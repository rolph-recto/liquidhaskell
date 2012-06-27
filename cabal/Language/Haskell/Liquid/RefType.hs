{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}

{- Refinement Types Mirroring the GHC Type definition -}

module Language.Haskell.Liquid.RefType (
    RTyVar (..), RType (..), RRType (..), BRType (..), RTyCon(..)
  , TyConable (..), Reftable(..), RefTypable (..), SubstP (..)
  , RefType, PrType, BareType, SpecType
  , PVar (..), Predicate (..), UReft(..), DataDecl (..)
  , pdAnd, pdVar, pdTrue, pvars
  , listConName, tupConName -- , bLst, bTup, bCon, isBoolBareType, boolConName
  , Bind (..), RBind
  , ppr_rtype, mapReft, mapRVar, mapBind
  , ofType, toType
  , rTyVar, rVar, rApp
  , typeUniqueSymbol
  , strengthen, strengthenRefType
  , mkArrow, normalizePds, rsplitVsPs, rsplitArgsRes
  , tvSubst, subsTyVarsP, subsTyVars, substSym 
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , stripRTypeBase, refTypePredSortedReft_,refTypeSortedReft, typeSortedReft, refTypePredSortedReft, rTypeSort
  -- , canonRefType
  , tidyRefType
  , mkSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalRefType, literalConst
  , REnv, deleteREnv, domREnv, insertREnv, lookupREnv, emptyREnv, memberREnv, fromListREnv
  , addTyConInfo
  , primOrderingSort
  ) where

import Text.Printf
import Control.Exception.Base
import Control.Exception (assert)
import GHC
import Outputable
import qualified TyCon as TC
import DataCon
import TypeRep 

import Var
import VarEnv
import PrelNames
import Name             (getSrcSpan, getOccString, mkInternalName)
import Unique           (getUnique)
import Literal
import Type             (isPredTy, mkTyConTy, liftedTypeKind, substTyWith, classifyPredType, PredTree(..), predTreePredType)
import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon, eqDataCon, ltDataCon, gtDataCon)


import Data.Maybe               (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S 
import Control.Applicative  hiding (empty)   
import Data.Bifunctor
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.DeepSeq
import qualified Data.Foldable as Fold

import Language.Haskell.Liquid.Tidy
import Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GhcMisc (tvId, stringTyVar, intersperse)
import Language.Haskell.Liquid.FileNames (boolConName)
import Data.List (sort, isPrefixOf, isSuffixOf, find, foldl')

--------------------------------------------------------------------
------------------ Predicate Variables -----------------------------
--------------------------------------------------------------------

data PVar t
  = PV { pname :: !Symbol
       , ptype :: !t
       , pargs :: ![(t, Symbol, Symbol)]
       }
	deriving (Data, Typeable, Show)

instance Eq (PVar t) where
  pv == pv' = (pname pv == pname pv') {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _)  (PV n' _ _) = compare n n'

instance Functor PVar where
  fmap f (PV x t txys) = PV x (f t) (mapFst3 f <$> txys)

instance (NFData a) => NFData (PVar a) where
  rnf (PV n t txys) = rnf n `seq` rnf t `seq` rnf txys

--instance Subable (PVar a) where
--  subst su (PV p t args) = PV p t $ [(t, x, subst su y) | (t, x, y) <- args]
--
--instance MapSymbol (PVar a) where 
--  mapSymbol f (PV p t args) = PV (f p) t [(t, x, f y) | (t, x, y) <- args]

--------------------------------------------------------------------
------------------ Predicates --------------------------------------
--------------------------------------------------------------------

newtype Predicate t = Pr [PVar t] deriving (Data, Typeable)

pdTrue         = Pr []
pdVar v        = Pr [v]
pvars (Pr pvs) = pvs
pdAnd ps       = Pr (concatMap pvars ps)

-- UNIFY: Why?!
instance Eq (Predicate a) where
  (==) = eqpd

eqpd (Pr vs) (Pr ws) 
  = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
    where vs' = sort vs
          ws' = sort ws

instance Functor Predicate where
  fmap f (Pr pvs) = Pr (fmap f <$> pvs)

instance Monoid (Predicate t) where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance Show (Predicate Type) where
  show = showSDoc . ppr

instance (Outputable (PVar t)) => Outputable (Predicate t) where
  ppr (Pr [])       = text "True"
  ppr (Pr pvs)      = hsep $ punctuate (text "&") (map ppr pvs)

instance Outputable (Predicate t) => Show (Predicate t) where
  show = showSDoc . ppr
  
instance Outputable (PVar t) => Reftable (Predicate t) where
  isTauto (Pr ps) 
    = null ps
  ppTy r d 
    | isTauto r = d 
    | otherwise = d <> (angleBrackets $ ppr r)
  

instance NFData (Predicate a) where
  rnf _ = ()

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()

--------------------------------------------------------------------
---- Unified Representation of Refinement Types --------------------
--------------------------------------------------------------------

data Bind tv pv = RB Symbol | RV tv | RP pv 
  deriving (Data, Typeable)

{- INVARIANTS:
 measure isTyVarBind :: Bind tv pv -> Bool
 isTyVarBind (RV _) = true 
 isTyVarBind (RP _) = false
 isTyVarBind (RB _) = false
-}

data RType p c tv pv r
  = RVar !(Bind tv pv) !r                                           -- INV: RVar {v | isTyVarBind v}
  | RFun !(Bind tv pv) !(RType p c tv pv r) !(RType p c tv pv r)    -- INV: RFun {v | isSymBind v} t1 t2
  | RAll !(Bind tv pv) !(RType p c tv pv r)                         -- INV: RAll {v | !(isSymBind v) }
  | RApp !c ![(RType p c tv pv r)] ![r] !r
  | RCls !p ![(RType p c tv pv r)]
  | ROth String
  deriving (Data, Typeable)

type BRType     = RType String String String   
type RRType     = RType Class  RTyCon RTyVar   

data UReft r t  = U {ureft :: !r, upred :: !(Predicate t)}
                  deriving (Data, Typeable)

type BareType   = BRType (PVar String) (UReft Reft String) 
type SpecType   = RRType (PVar Type)   (UReft Reft Type)
type PrType     = RRType (PVar Type)   (Predicate Type) 
type RefType    = RRType (PVar Type)   Reft

data DataDecl   = D String 
                    [String] 
                    [PVar String] 
                    [(String, [(String, BareType)])] 
                  deriving (Data, Typeable, Show)

class (Monoid r, Outputable r) => Reftable r where 
  isTauto :: r -> Bool
  ppTy    :: r -> SDoc -> SDoc
  
  top     :: r
  top     =  mempty
  
  meet    :: r -> r -> r
  meet    = mappend


class TyConable c where
  isList   :: c -> Bool
  isTuple  :: c -> Bool

class (Outputable p, Outputable c, Outputable tv, Outputable pv, Reftable r, TyConable c) => RefTypable p c tv pv r where
  ppCls    :: p -> [RType p c tv pv r] -> SDoc
  
  ppRType  :: Prec -> RType p c tv pv r -> SDoc 
  ppRType = ppr_rtype 



--------------------------------------------------------------------
---------------- Refinement Types: RefType -------------------------
--------------------------------------------------------------------

newtype RTyVar = RTV TyVar deriving (Data, Typeable)

instance Eq RTyVar where
  RTV α == RTV α' = tvId α == tvId α'

instance Ord RTyVar where
  compare (RTV α) (RTV α') = compare (tvId α) (tvId α')

type RBind = Bind RTyVar (PVar Type)

data RTyCon = RTyCon 
  { rTyCon     :: !TC.TyCon         -- GHC Type Constructor
  , rTyConPs   :: ![PVar Type]      -- Predicate Parameters
  }
  deriving (Eq, Data, Typeable)

instance Eq RBind where
  RB s == RB s' = s == s'
  RV α == RV α' = α == α'
  RP p == RP p' = pname p == pname p'
  _    == _     = False 

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rVar                = RVar . rTyVar 
rTyVar              = RV . RTV


normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

rPred p t = RAll (RP p) t
rApp c    = RApp (RTyCon c []) 


addPds ps (RAll v@(RV _) t) = RAll v $ addPds ps t
addPds ps t                 = foldl' (flip rPred) t ps

nlzP ps t@(RVar _ _ ) 
 = (t, ps)
nlzP ps (RFun b t1 t2) 
 = (RFun b t1' t2', ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAll (RV v) t )
 = (RAll (RV v) t', ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(RApp c ts rs r)
 = (t, ps)
nlzP ps t@(RCls c ts)
 = (t, ps)
nlzP ps (RAll (RP p) t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(ROth _)
 = (t, ps)

strengthenRefType :: RefType -> RefType -> RefType
strengthenRefType t1 t2 
  | eqt t1 t2 
  = strengthenRefType_ t1 t2
  | otherwise
  = errorstar $ "strengthen on differently shaped reftypes! " 
              ++ "t1 = " ++ showPpr t1 
              ++ "t2 = " ++ showPpr t2
  where eqt t1 t2 = showPpr (toType t1) == showPpr (toType t2)
  
strengthenRefType_ (RAll a@(RV _) t1) (RAll _ t2)
  = RAll a $ strengthenRefType_ t1 t2

strengthenRefType_ (RFun (RB x1) t1 t1') (RFun (RB x2) t2 t2') 
  = RFun (RB x1) t t'
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts = zipWith strengthenRefType_ t1s t2s
          rs = zipWith meet rs1 rs2

strengthenRefType_ t1 _ 
  = t1

strengthen (RApp c ts rs r) r' = RApp c ts rs (r `meet` r') 
strengthen (RVar a r) r'       = RVar a      (r `meet` r') 
strengthen t _                 = t 


replaceReft (RApp c ts rs _) r' = RApp c ts rs r' 
replaceReft (RVar a _) r'      = RVar a      r' 
replaceReft t _                = t 


addTyConInfo :: M.Map TC.TyCon RTyCon -> RRType pv Reft -> RRType pv Reft
addTyConInfo = mapBot . addTCI
addTCI tyi t@(RApp c ts rs r)
  = case (M.lookup (rTyCon c) tyi) of
     Just c' -> rConApp c' ts rs r
     Nothing -> rConApp c  ts rs r
addTCI _ t
  = t

showTy v = showSDoc $ ppr v <> ppr (varUnique v)
-- showTy t = showSDoc $ ppr t

rConApp (RTyCon c ps) ts rs r = RApp (RTyCon c ps') ts rs' r 
   where τs   = toType <$> ts
         ps'  = subsTyVarsP (zip cts τs) <$> ps
         cts  = RTV <$> TC.tyConTyVars c
         rs'  = if (null rs) then ((\_ -> F.trueReft) <$> ps) else rs

-- mkArrow ::  [TyVar] -> [(Symbol, RType a)] -> RType a -> RType a
mkArrow as xts t = mkUnivs as $ mkArrs xts t

mkUnivs αs t  = tr_foldr' RAll t $ RV `fmap` αs
mkArrs xts t = tr_foldr' (\(x,t) -> RFun (RB x) t) t xts

-- bkArrow :: RType a -> ([TyVar], [(Symbol, RType a)],  RType a)
bkArrow ty = (αs, xts, out)
  where (αs, t)    = bkUniv [] ty
        (xts, out) = bkArrs [] t
       

bkUniv αs (RAll (RV α) t) = bkUniv (α : αs) t
bkUniv αs t               = (reverse αs, t)

bkArrs xts (RFun (RB x) t t') = bkArrs ((x,t):xts) t'
bkArrs xts t                  = (reverse xts, t)

rsplitVsPs (RAll (RV v) t) = (v:vs, ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs (RAll (RP p) t) = (vs, p:ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs t = ([], [], t)

rsplitArgsRes (RFun (RB x) t1 t2) = (x:xs, t1:ts, r)
  where (xs, ts, r) = rsplitArgsRes t2
rsplitArgsRes t = ([], [], t)

----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance NFData REnv where
  rnf (REnv m) = () -- rnf m

instance NFData (Bind a b) where
  rnf (RB x) = rnf x
  rnf (RV a) = ()
  rnf (RP p) = () 

instance (NFData a, NFData b, NFData c, NFData d, NFData e) => NFData (RType a b c d e) where
  rnf (RVar α r)       = rnf α `seq` rnf r 
  rnf (RAll α t)       = rnf α `seq` rnf t
  rnf (RFun x t t')    = rnf x `seq` rnf t `seq` rnf t'
  rnf (RApp c ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RCls c ts)      = c `seq` rnf ts
  rnf (ROth _)         = ()

----------------------------------------------------------------
------------------ Printing Refinement Types -------------------
----------------------------------------------------------------

ppr_tyvar = text . tvId

instance Outputable RTyVar where
  ppr (RTV α) = ppr_tyvar α 

instance Show RTyVar where
  show = showPpr 

instance (Outputable tv, Outputable pv) => Outputable (Bind tv pv) where
  ppr (RB x) = ppr x
  ppr (RV a) = ppr a
  ppr (RP p) = ppr p

instance Show RBind where
  show = showPpr 

instance TyConable RTyCon where
  isList  = (listTyCon ==) . rTyCon
  isTuple = TC.isTupleTyCon   . rTyCon 
 
instance Reftable Reft where
  isTauto = isTautoReft
  ppTy    = ppr_reft

listConName = "List"
tupConName  = "Tuple"

instance TyConable String where
  isList  = (listConName ==) 
  isTuple = (tupConName ==)

instance (Outputable pv, Reftable r) => RefTypable String String String pv r where
  ppCls c ts = parens (text c <+> text "...")

instance (Reftable r, Reftable (Predicate t)) => Outputable (UReft r t) where
  ppr (U r p)
    | isTauto r  = ppr p
    | isTauto p  = ppr r
    | otherwise  = ppr p <> text " & " <> ppr r
 
instance (Reftable r, Reftable (Predicate t)) => Reftable (UReft r t) where
  isTauto (U r p) = isTauto r && isTauto p 
  ppTy (U r p) d  = ppTy r (ppTy p d) 

instance (Outputable pv, Reftable r) => RefTypable Class RTyCon RTyVar pv r where
  ppCls c ts  = parens $ pprClassPred c (toType <$> ts)

instance Outputable (PVar String) where
  ppr  = ppr_pvar text

instance Outputable (PVar Type) where
  ppr  = ppr_pvar ppr_pvar_type 

ppr_pvar_type (TyVarTy α) = ppr_tyvar α
ppr_pvar_type t           = ppr t

ppr_pvar pprv (PV s t xts) = ppr s <+> dcolon <+> intersperse arrow dargs 
  where dargs = [pprv t | (t,_,_) <- xts] ++ [pprv t, text boolConName]

--ppr_pvar pprv (PV s t []) = ppr s <> colon <> pprv t
--ppr_pvar pprv (PV s t xs) = ppr ((PV s t [])) <+> (parens $ hsep (punctuate comma (ppArg <$> xs)))
--                            where ppArg (t, _, x) = ppr x <+> colon <+> pprv t

instance (RefTypable p c tv pv r) => Outputable (RType p c tv pv r) where
  ppr = ppRType TopPrec

instance Outputable (RType p c tv pv r) => Show (RType p c tv pv r) where
  show = showSDoc . ppr

instance Outputable RTyCon where
  ppr (RTyCon c ts) = ppr c -- <+> text "\n<<" <+> hsep (map ppr ts) <+> text ">>\n"
  
instance Show RTyCon where
 show = showPpr

ppr_rtype :: (RefTypable p c tv pv r) => Prec -> RType p c tv pv r -> SDoc
ppr_rtype p (RAll pv@(RP _) t)
  = text "forall" <+> ppr pv <+> ppr_pred p t
ppr_rtype p t@(RAll (RV _) _)       
  = ppr_forall p t
ppr_rtype p (RVar a r)         
  = ppTy r $ ppr a
ppr_rtype p (RFun x t t')  
  = pprArrowChain p $ ppr_dbind x t : ppr_fun_tail t'
ppr_rtype p ty@(RApp c [t] rs r)
  | isList c 
  = ppTy r $ brackets (ppr_rtype p t) <> ppReftPs rs
ppr_rtype p (RApp c ts rs r)
  = ppTy r $ ppr c <> ppReftPs rs <+> hsep (ppr_rtype p <$> ts)
ppr_rtype _ ty@(RCls c ts)      
  = ppCls c ts
ppr_rtype _ (ROth s)
  = text "?" <> text s <> text "?"


ppReftPs rs 
  | all isTauto rs = empty -- text "" 
  | otherwise      = angleBrackets $ hsep $ punctuate comma $ ppr <$> rs

ppr_pred :: (RefTypable p c tv pv r) => Prec -> RType p c tv pv r -> SDoc
ppr_pred p (RAll pv@(RP _) t)
  = ppr pv <> ppr_pred p t
ppr_pred p t
  = dot <+> ppr_rtype p t

ppr_dbind :: (RefTypable p c tv pv r) => Bind tv pv -> RType p c tv pv r -> SDoc
ppr_dbind b@(RB x) t 
  | isNonSymbol x 
  = ppr_rtype FunPrec t
  | otherwise
  = {-braces-} (ppr b) <> colon <> ppr_rtype FunPrec t

ppr_fun_tail :: (RefTypable p c tv pv r) => RType p c tv pv r -> [SDoc]
ppr_fun_tail (RFun b t t')  
  = (ppr_dbind b t) : (ppr_fun_tail t')
ppr_fun_tail t
  = [ppr_rtype TopPrec t]

ppr_forall :: (RefTypable p c tv pv r) => Prec -> RType p c tv pv r -> SDoc
ppr_forall p t
  = maybeParen p FunPrec $ sep [ppr_foralls αs, ppr_rtype TopPrec t']
  where
    (αs,  t')           = split [] t
    split αs (RAll α t) = split (α:αs) t
    split αs t	        = (reverse αs, t)
   
ppr_foralls [] = empty
ppr_foralls bs = text "forall" <+> dαs [ α | RV α <- bs] <+> dπs [ π | RP π <- bs] <> dot
  where dαs αs = sep $ ppr <$> αs 
        dπs [] = empty 
        dπs πs = angleBrackets $ intersperse comma $ ppr <$> πs



-- UNIFY: Use Niki's code from PredType.hs (below) to improve Class Printing:
-- Instead of   : C1 t -> C2 d -> [t] -> [d] -> Int
-- Should print : (C1 t, C2 d) => [t] -> [d] -> Int

--instance Outputable PrType where
--  ppr t@(PrFun s t1 t2)   = ppr_fun t
--  ppr (PrAll a t)         = text "forall" <+> ppr a <+> ppr_forall t
--  ppr (PrAllPr p t)       = text "forall" <+> ppr p <+> ppr_forall t
--  ppr (PrLit l p)         = ppr l <+> ppr p
--  ppr (PrVar a p)         = ppr a <+>  ppr p
--  ppr (PrTyCon c ts ps p) = ppr c <+> braces (hsep (map ppr ts)) <+> braces (hsep (map ppr ps)) <+> ppr p
--  ppr (PrClass c ts)    = ppr c <+> (braces $ hsep (map ppr ts))
--
--ppr_forall (PrAll v t)   = ppr v <> ppr (varUnique v)<+> ppr_forall t
--ppr_forall (PrAllPr p t) = ppr p <+> ppr_forall t
--ppr_forall t             = dot  <> ppr t
--
--ppr_fun (PrFun s t1 t2)  = ppr_fun_l (s, t1) <+> ppr t2 
--ppr_fun t                = ppr t
--
----brance x = char '[' <> ppr x <> char ']'
--
--ppr_fun_l (_, PrClass c ts) 
--  = ppr c <+> (braces $ hsep (map ppr ts)) <+> text "=>"
--ppr_fun_l (s, PrFun s1 t1 t2) 
--  = ppr s <> char ':'
--          <> (parens (ppr_fun_l (s1, t1) <> ppr t2)) 
--		        <+> text "->"
--ppr_fun_l (s, t) 
--  = ppr s <> char ':' <> ppr t <+> text "->"


---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

--instance Functor (UReft r) where 
--  fmap = second 

instance Bifunctor UReft where
  first f (U r p)  = U (f r) p
  second f (U r p) = U r (fmap f p)


instance Functor (RType a b c d) where
  fmap f = mapReft f

  --fmap f (RVar α r)       = RVar α (f r)
  --fmap f (RAll a t)       = RAll a (fmap f t)
  --fmap f (RFun x t t')    = RFun x (fmap f t) (fmap f t')
  --fmap f (RApp c ts rs r) = RApp c (fmap (fmap f) ts) (f <$> rs) (f r)
  --fmap f (RCls c ts)      = RCls c (fmap (fmap f) ts)
  --fmap f (ROth a)         = ROth a 

subsTyVars_meet   = subsTyVars True
subsTyVars_nomeet = subsTyVars False
subsTyVar_nomeet  = subsTyVar False
subsTyVar_meet    = subsTyVar True

subsTyVars ::  Bool -> [(RTyVar, RefType)] -> RefType -> RefType 
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats

subsTyVar meet = subsFree meet S.empty

subsFree ::  Bool -> S.Set RTyVar -> (RTyVar, RefType) -> RefType -> RefType

subsFree m s z@(α, t') (RAll (RP p) t)         
  = RAll (RP p') t''
    where p'  = subsTyVarsP [(α, toType t')] p
          t'' = subsFree m s z t
          -- = errorstar $ "subsFree TBD: " ++ showPpr t
subsFree m s z (RAll (RV α) t)         
  = RAll (RV α) $ subsFree m (α `S.insert` s) z t
subsFree m s z (RFun x t t')       
  = RFun x (subsFree m s z t) (subsFree m s z t') 
subsFree m s z@(α, t') t@(RApp c ts rs r)     
  = RApp c' (subsFree m s z <$> ts) rs r  
    where c' = c {rTyConPs = (subsTyVarsP [(α, toType t')]) <$> (rTyConPs c)}
    -- UNIFY: why instantiating INSIDE parameters?
subsFree m s z (RCls c ts)     
  = RCls c (subsFree m s z <$> ts)
subsFree meet s (α', t') t@(RVar (RV α) r) 
  | α == α' && α `S.notMember` s 
  = if meet then t' `strengthen` r else t' 
  | otherwise
  = {- traceShow  msg $ -} t
  where msg = ("subsFree MISS: α = " ++ showPpr α ++ " α' = " ++ showPpr α' ++ " s = " ++ showPpr s)
subsFree _ _ _ t@(ROth _)        
  = t
subsFree _ _ _ t      
  = errorstar $ "subsFree fails on: " ++ showPpr t

---------------------------------------------------------------------
------------------- Type Substitutions ------------------------------
---------------------------------------------------------------------

class SubstP a where
  subp :: M.Map (PVar Type) (Predicate Type) -> a -> a
  subv :: (PVar Type -> PVar Type) -> a -> a
  subt :: (RTyVar -> Type) -> a -> a


lookupP s p@(PV _ _ s')
  = case M.lookup p s of 
      Nothing  -> Pr [p]
      Just q   -> subv (\pv -> pv { pargs = s'}) q

instance SubstP Type where
  subp _ = id
  subv _ = id
  subt f (TyVarTy tv) = f (RTV tv) -- UNIFY: Deep Subst

instance SubstP (PVar Type)

instance SubstP (Predicate Type) where
  subv f (Pr pvs) = Pr (f <$> pvs)
  subp s (Pr pvs) = pdAnd (lookupP s <$> pvs) -- RJ: UNIFY: not correct!
  subt t (Pr pvs) = error "TBD"

instance SubstP (UReft Reft Type) where
  subp f (U r p) = U r (subp f p)
  subv f (U r p) = U r (subv f p)

-- NOTE: This DOES NOT substitute at the binders
instance SubstP PrType where    
  subp f t = fmap (subp f) t
  subv f t = fmap (subv f) t 




--subsTyVarsP ::  Functor f => [(RTyVar, Type)] -> f Type -> f Type
--subsTyVarsP vts p = foldl' (flip subsTyVarP) p vts 
--  where subsTyVarP = fmap . tvSubst

subsTyVarsP :: (SubstP a) => [(RTyVar, Type)] -> a -> a 
subsTyVarsP vts x = foldl' (\x su -> subt (tvSubst su) x) vts

tvSubst (α, t) α'@(RTV tv') 
  | α == α'   = t
  | otherwise = TyVarTy tv'

--tvSubst ::  (RTyVar, Type) -> Type -> Type
--tvSubst (α, t) t'@(TyVarTy α') 
--  | α == (RTV α') = t
--  | otherwise     = t'
--tvSubst _ t'
--  = t'
----tvSubst _ t'
----  = errorstar $ "tvSubst fails on: " ++ showPpr t

HEREHEREHEREHERE
mapRVar (subsTyVar s) = subsFree True S.empty s 


subsTyVar (α, (RVar (RV a') p')) (RV a) p
  | α == a     = RVar (RV a') (meet p p')
  | otherwise  = RVar (RV a) p 
subsTyVar (α, (RApp c ts ps p')) (RV a) p
  | α == a     = RApp c ts ps (meet p p')
  | otherwise  = RVar (RV a) p 
subsTyVar (α, t) (RV a) p 
  | α == a     = t 
  | otherwise  = RVar (RV a) p 

subsTyVars_ (v, t, τ) = mapReft (subsTyVarsP [(v, τ)]) . mapRVar (subsTyVar (v, t))

HEREHEREHEREHEREHERE BUG
subsTyVars s = traceShow ("subsTyVars s = " ++ show s) . 
               mapReft (subv (subsTyVarP1_ s)) . mapRVar (subsTyVar s)
  where subsTyVarP1_ (α, (RVar (RV (RTV α')) _)) = fmap $ tvSubst (α, TyVarTy α')
        -- RJ: UNIFY: why no deep substitution? (just following subsTyVarAP_)

substSym (x, y) = mapReft fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == x) then y else s
        fp    = subv (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })


---------------------------------------------------------------

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RApp _ _ _ x)   
  = Just x
stripRTypeBase (RVar _ x)   
  = Just x
stripRTypeBase _                
  = Nothing

ofType :: Type -> RefType
ofType = ofType_ 

ofType_ :: Type -> RefType 
ofType_ (FunTy τ τ')    
  = RFun (RB dummySymbol) (ofType_ τ) (ofType_ τ')
ofType_ (ForAllTy α τ)  
  = RAll (rTyVar α) $ ofType_ τ  
ofType_ (TyVarTy α)     
  = RVar (rTyVar α) trueReft 
ofType_ τ
  | isPredTy τ
  = ofPredTree (classifyPredType τ)  
ofType_ τ@(TyConApp c _)
  | TC.isSynTyCon c
  = ofSynTyConApp τ
  | otherwise
  = ofTyConApp τ
ofType_ τ               
  = ROth (show τ)  

ofPredTree (ClassPred c τs)
  = RCls c (ofType_ <$> τs)
 

ofTyConApp  τ@(TyConApp c τs) 
  = rApp c (ofType_ <$> τs) [] trueReft

ofSynTyConApp (TyConApp c τs) 
  = ofType_ $ substTyWith αs τs τ
  where (αs, τ) = TC.synTyConDefn c

-----------------------------------------------------------------
---------------------- Scrap this using SYB? --------------------
-----------------------------------------------------------------

mapReft f (RVar α r)       = RVar α (f r)
mapReft f (RAll a t)       = RAll a (mapReft f t)
mapReft f (RFun x t t')    = RFun x (mapReft f t) (mapReft f t')
mapReft f (RApp c ts rs r) = RApp c (mapReft f <$> ts) (f <$> rs) (f r)
mapReft f (RCls c ts)      = RCls c (mapReft f <$> ts) 
mapReft f (ROth a)         = ROth a 

mapRVar :: (Bind tv pv -> r -> RType p c tv pv r)-> RType p c tv pv r -> RType p c tv pv r
mapRVar f (RVar b r)       = f b r 
mapRVar f (RFun b t1 t2)   = RFun b (mapRVar f t1) (mapRVar f t2)
mapRVar f (RAll b t)       = RAll b (mapRVar f t) 
mapRVar f (RApp c ts rs r) = RApp c (mapRVar f <$> ts) rs r
mapRVar f (RCls c ts)      = RCls c (mapRVar f <$> ts)
mapRVar f (ROth s)         = ROth s

mapBind f (RVar b r)       = RVar (f b) r
mapBind f (RFun b t1 t2)   = RFun (f b) (mapBind f t1) (mapBind f t2)
mapBind f (RAll b t)       = RAll (f b) (mapBind f t) 
mapBind f (RApp c ts rs r) = RApp c (mapBind f <$> ts) rs r
mapBind f (RCls c ts)      = RCls c (mapBind f <$> ts)
mapBind f (ROth s)         = ROth s



mapBot f (RAll a t)       = RAll a (mapBot f t)
mapBot f (RFun x t t')    = RFun x (mapBot f t) (mapBot f t')
mapBot f (RApp c ts rs r) = f $ RApp c (mapBot f <$> ts) rs r
mapBot f (RCls c ts)      = RCls c (mapBot f <$> ts)
mapBot f t'               = f t' 

--canonRefType = mapTop zz
--  where zz t@(RApp c ts rs r)  = RApp c ts (map canonReft rs) (canonReft r)
--        zz t                   = t
--mapTop f t = 
--  case f t of
--    (RAll a t')      -> RAll a (mapTop f t')
--    (RFun x t' t'')  -> RFun x (mapTop f t') (mapTop f t'')
--    (RApp c ts rs r) -> RApp c (mapTop f <$> ts) rs r
--    (RCls c ts)      -> RCls c (mapTop f <$> ts)
--    t'               -> t' 


-------------------------------------------------------------------
--------------------------- SYB Magic -----------------------------
-------------------------------------------------------------------

reftypeBindVars :: RefType -> S.Set Symbol
reftypeBindVars = everything S.union (S.empty `mkQ` grabBind)
  where grabBind ((RB x) :: RBind) = S.singleton x 

readSymbols :: (Data a) => a -> S.Set Symbol
readSymbols = everything S.union (S.empty `mkQ` grabRead)
  where grabRead (EVar x) = S.singleton x
        grabRead _        = S.empty

---------------------------------------------------------------------
---------- Cleaning Reftypes Up Before Rendering --------------------
---------------------------------------------------------------------

tidyRefType :: RefType -> RefType
tidyRefType = tidyDSymbols
            . tidySymbols 
            . tidyFunBinds
            . tidyLocalRefas 
            . tidyTyVars 

tidyFunBinds :: RefType -> RefType
tidyFunBinds t = everywhere (mkT $ dropBind xs) t 
  where xs = readSymbols t
        dropBind xs ((RB x) :: RBind) 
          | x `S.member` xs = RB x
          | otherwise       = RB nonSymbol
        dropBind _ z = z

tidyTyVars :: RefType -> RefType
tidyTyVars = tidy pool getS putS 
  where getS (α :: TyVar)   = Just (symbolString $ mkSymbol α)
        putS (α :: TyVar) x = stringTyVar x
        pool          = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]

tidyLocalRefas :: RefType -> RefType
tidyLocalRefas = everywhere (mkT dropLocals) 
  where dropLocals = filter (not . Fold.any isTmp . readSymbols) . flattenRefas
        isTmp x    = let str = symbolString x in 
                     (anfPrefix `isPrefixOf` str) || (tempPrefix `isPrefixOf` str) 

tidySymbols :: RefType -> RefType
tidySymbols = everywhere (mkT dropSuffix) 
  where dropSuffix = stringSymbol . takeWhile (/= symSep) . symbolString
        dropQualif = stringSymbol . dropModuleNames . symbolString 

tidyDSymbols :: RefType -> RefType
tidyDSymbols = tidy pool getS putS 
  where getS   sy  = let str = symbolString sy in 
                     if "ds_" `isPrefixOf` str then Just str else Nothing
        putS _ str = stringSymbol str 
        pool       = ["X" ++ show i | i <- [1..]]

----------------------------------------------------------------
------------------- Converting to Fixpoint ---------------------
----------------------------------------------------------------

symSep = '#'

mkSymbol ::  Var -> Symbol
--mkSymbol v = S $ vs ++ [symSep] ++ us
--  where us  = showPpr $ getUnique v 
--        vs  = pprShort v
--
--mkSymbol v = traceShow ("mkSymbol " ++ showPpr v ++ " = ") $ mkSymbol' v

mkSymbol v 
  | us `isSuffixOf` vs = stringSymbol vs  
  | otherwise          = stringSymbol $ vs ++ [symSep] ++ us
  where us  = showPpr $ getUnique v 
        vs  = pprShort v

dataConSymbol = mkSymbol . dataConWorkId

primOrderingSort = typeSort $ dataConRepType eqDataCon
ordCon s = EDat (S s) primOrderingSort

-- dataConReft   ::  DataCon -> Type -> Reft 
dataConReft c τ
  | c == trueDataCon
  = Reft (vv, [RConc $ (PBexp (EVar vv))]) 
  | c == falseDataCon
  = Reft (vv, [RConc $ PNot (PBexp (EVar vv))]) 
  | c == eqDataCon
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon "EQ"))]) 
  | c == gtDataCon
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon "GT"))]) 
  | c == ltDataCon
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon "LT"))]) 
  | otherwise
  = Reft (vv, [RConc PTrue]) 

dataConMsReft ty ys  = subst su r 
  where (_, xts, t)  = bkArrow ty 
        r            = fromMaybe trueReft $ stripRTypeBase t
        su           = mkSubst [(x, EVar y) | ((x,_), y) <- zip xts ys] 

pprShort    =  dropModuleNames . showPpr

dropModuleNames = last . words . (dotWhite <$>) 
  where dotWhite '.' = ' '
        dotWhite c   = c

---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------

toType ::  RRType a b -> Type

toType (RFun _ t t')   
  = FunTy (toType t) (toType t')
toType (RAll (RV (RTV α)) t)      
  = ForAllTy α (toType t)
toType (RVar (RV (RTV α)) _)        
  = TyVarTy α
toType (RApp (RTyCon {rTyCon = c}) ts _ _)   
  = TyConApp c (toType <$> ts)
toType (RCls c ts)   
  = predTreePredType $ ClassPred c (toType <$> ts)
  -- = PredTy (ClassP c (toType <$> ts))
toType (ROth t)      
  = errorstar $ "toType fails: " ++ t

typeSort :: Type -> Sort 
typeSort (TyConApp c []) 
  | k == intTyConKey     = FInt
  | k == intPrimTyConKey = FInt
  | k == integerTyConKey = FInt 
  | k == boolTyConKey    = FBool
  where k = TC.tyConUnique c
typeSort (ForAllTy _ τ) 
  = typeSort τ  -- JHALA: Yikes! Fix!!!
typeSort (FunTy τ1 τ2) 
  = typeSortFun τ1 τ2
typeSort τ
  = FPtr $ FLoc $ typeUniqueSymbol τ
typeSortFun τ1 τ2
  = FFunc n $ genArgSorts sos
  where sos  = typeSort <$> τs
        τs   = τ1  : grabArgs [] τ2
        n    = (length sos) - 1
     
typeUniqueSymbol :: Type -> Symbol 
typeUniqueSymbol = stringSymbol . ("sort_" ++) . showSDocDump . ppr

grabArgs τs (FunTy τ1 τ2 ) = grabArgs (τ1:τs) τ2
grabArgs τs τ              = reverse (τ:τs)

genArgSorts :: [Sort] -> [Sort]
genArgSorts xs = zipWith genIdx xs $ memoIndex genSort xs
  where genSort FInt        = Nothing
        genSort FBool       = Nothing 
        genSort so          = Just so
        genIdx  _ (Just i)  = FPtr (FLvar i) --FVar i
        genIdx  so  _       = so


---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

literalRefType l 
  = makeRTypeBase (literalType l) (literalReft l) 

-- makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α) x       
  = RVar (rTyVar α) x 
makeRTypeBase τ@(TyConApp c _) x 
  = rApp c [] [] x

literalReft l  = exprReft e 
  where (_, e) = literalConst l 

literalConst l                 = (sort, mkLit l)
  where sort                   = typeSort $ literalType l 
        sym                    = stringSymbol $ "$$" ++ showPpr l
        mkLit (MachInt    n)   = mkI n
        mkLit (MachInt64  n)   = mkI n
        mkLit (MachWord   n)   = mkI n
        mkLit (MachWord64 n)   = mkI n
        mkLit (LitInteger n _) = mkI n
        mkLit _                = ELit sym sort
        mkI                    = ECon . I

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

newtype REnv = REnv  (M.Map Symbol RefType)
               deriving (Data, Typeable)

fromListREnv              = REnv . M.fromList
deleteREnv x (REnv env)   = REnv (M.delete x env)
insertREnv x y (REnv env) = REnv (M.insert x y env)
lookupREnv x (REnv env)   = M.lookup x env
emptyREnv                 = REnv M.empty
memberREnv x (REnv env)   = M.member x env
domREnv (REnv env)        = M.keys env

instance Show Type where
  show  = showSDoc . ppr

instance Outputable REnv where
  ppr (REnv m)         = vcat $ map pprxt $ M.toAscList m
    where pprxt (x, t) = ppr x <> dcolon <> ppr t  

-- refTypePredSortedReft_   :: (Reft, Type) -> SortedReft
refTypePredSortedReft_ (r, τ) = RR so r
  where so = typeSort τ
refTypePredSortedReft r = RR so r
  where so = FObj -- typeSort τ

refTypeSortedReft   ::  RefType -> SortedReft
refTypeSortedReft t = RR so r
  where so = {- traceShow ("rTypeSort: t = " ++ showPpr t) $ -} rTypeSort t
        r  = fromMaybe trueReft $ stripRTypeBase t 

-- typeSortedReft ::  Type -> Refa -> SortedReft
typeSortedReft t r = RR so $ Reft(vv,[r])
  where so = typeSort t


-- rTypeSort ::  RType t -> Sort
rTypeSort = typeSort . toType

-------------------------------------------------------------------
-------------------------- Substitution ---------------------------
-------------------------------------------------------------------

instance Subable RefType  where
  subst = fmap . subst 

