-- | fault localization algorithm
module Language.Haskell.Liquid.FaultLocal (
  consWeight
) where

import CoreSyn
import Language.Haskell.Liquid.Constraint.Types as T

-- recursive weighting function for exprs
exprWeight :: Expr a -> Int
exprWeight (Var _) = 1

exprWeight (Lit _) = 1

exprWeight (App body arg) =
  (exprWeight body) + (exprWeight arg)

exprWeight (Lam _ body) =
  (exprWeight body) + 1

exprWeight (Let (NonRec _ arg) body) =
  (exprWeight arg) + (exprWeight body) + 1

exprWeight (Let (Rec args) body) =
  arg_weight + (exprWeight body)
  where arg_exprs   = map snd args
        arg_weight  = sum $ map exprWeight arg_exprs

exprWeight (Case e _ _ branches) =
  (exprWeight e) + branchWeight
  where bexprs       = map (\(_,_,e) -> e) branches
        branchWeight = sum $ map exprWeight bexprs

exprWeight (Cast e _) = exprWeight e

exprWeight (Tick _ e) = exprWeight e

exprWeight (Type _) = 0

exprWeight (Coercion _) = 0


-- weight of constraint is the sum of
-- the weights of the exprs mapped to it
consWeight :: T.SubC -> Int
consWeight (T.SubC _ _ _ locexprs) =
  sum $ map exprWeight exprs
  where exprs = map snd locexprs

consWeight (T.SubR _ _ _ locexprs) =
  sum $ map exprWeight exprs
  where exprs = map snd locexprs
  
