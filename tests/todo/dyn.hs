{-@ LIQUID "--no-termination" @-}
module Dyn (ok, bad) where

import Data.Dynamic
import Data.Maybe
import Data.Set

import GHC.Base

import Language.Haskell.Liquid.Prelude (proxy)

zero, one :: Int
{-@ zero :: {v:Int | v = 0} @-}
zero = undefined -- 0
{-@ one :: {v:Int | v = 1} @-}
one  = undefined -- 1

{-@ b0 :: {v:DBox a | (((defKeys v) = (Set_cup (Set_sng 0) (Set_sng 1)))
                  && ((fieldType v 0) = "String")
                  && ((fieldType v 1) = "Int"))}
  @-}
b0    = put zero ("cat" :: String)
      $ put one (12    :: Int)
      $ emp

ok    = 10 `plus` (get one b0)

bad   = 10 `plus` (get zero b0)

{-@ str :: String @-}
str :: String
str = undefined

{-@ int :: {v:Int | (typeRep v) = "Int"} @-}
int :: Int
int = undefined


{-@ foo :: d:DBox a -> {v:DBox a | ((fieldType v 0) = "String")} @-}
foo = put 0 ("cat" :: String)

-------------------------------------------------
plus :: Int -> Int -> Int
plus = (+)

-- concat :: String -> String -> String
-- concat = (++)

-------------------------------------------------

{-@ measure tag :: Dynamic -> Str @-}
{-@ class measure typeRep :: forall a. a -> Str @-}
{-@ invariant {v:String | (typeRep v) = "String"} @-}
{-@ invariant {v:Int | (typeRep v) = "Int"} @-}
{- instance measure typeRep :: String -> Str
    typeRep ([])       = "String"
    typeRep ((:) c cs) = "String"
  @-}
{- instance measure typeRep :: Int -> Str
    typeRep (I# i) = "Int"
  @-}
{-@ Data.Dynamic.toDyn :: (Typeable a) => x:a -> {v:Dynamic | (tag v) = (typeRep x)} @-}
{-@ qualif TypeTag(v:Dynamic): (tag v) = "String"  @-}
{-@ qualif TypeTag(v:Dynamic): (tag v) = "Int"  @-}
{-@ qualif TypeRep(v:Dynamic, x:a): (tag v) = (typeRep x) @-}

type Field   = Int

-- newtype DBox a = DB [(Field, Dynamic)]
data DBox a = Emp
          | Fld Field Dynamic (DBox a)
{-@ data DBox a <p :: Field -> Dynamic -> Prop>
      = Emp
      | Fld (k::Field) (v::Dynamic<p k>) (db::DBox <p> a)
  @-}
{-
data DBox where
  Emp :: {v:DBox | defKeys v = Set_emp }
  Fld :: k:Field -> v:Dynamic -> db:DBox
      -> {v:DBox | defKeys v = union (singleton k) (defKeys db)
                && fieldType k v = tag v }
-}
{-@ measure dsize :: DBox a -> Int
    dsize (Emp)        = 0
    dsize (Fld k v db) = 1 + (dsize db)
  @-}
{-@ invariant {v:DBox a | (dsize v) >= 0} @-}
{-@ measure getField :: Field -> DBox a -> Dynamic
  @-}
{-@ measure fieldType :: DBox a -> Field -> Str
  @-}

{- measure fieldTypes :: DBox a -> (Set (Field, Str))
    fieldTypes (Emp)       = {v | (? (Set_emp v))}
    fieldTypes (Fld k x d) = {v | v = (Set_cup (Set_sng (k, (tag x))) (fieldTypes d))}
  @-}
{-@ measure fieldTypes :: DBox a -> Prop
    fieldTypes (Emp) = true
    fieldTypes (Fld k x d) = (((fieldType d k) = (tag x)) && (fieldTypes d))
  @-}
-- fieldType d f = (tag (getField f d))

{-@ measure defKeys :: DBox a -> (Set Field)
    defKeys (Emp)       = {v | (? (Set_emp v))}
    defKeys (Fld k x d) = {v | v = (Set_cup (Set_sng k) (defKeys d))}
  @-}
{-@ type DBoxWithKey a F D = {v:DBox a | (defKeys v) = (Set_cup (Set_sng F) (defKeys D))} @-}

{-@ emp :: DBox <{\f v -> true}> a @-}
emp :: DBox a
emp = Emp -- DB []

{- put :: forall <p :: Field -> Dynamic -> Prop>. (Typeable a)
        => f:Field -> x:a -> d:DBox a
        -> {v:DBox aWithKey f d | (((fieldType v f) = (typeRep x)))}
  @-}
{-@ put :: forall <p :: Field -> Dynamic -> Prop>.
           (Typeable a)
        => f:Field -> x:a -> d:DBox <p> b
        -> {v:DBox <p> b | (tag (getField f v)) = (typeRep x) }
  @-}
-- (tag (getField f v)) = (typeRep x)

put :: (Typeable a) => Field -> a -> DBox b -> DBox b
-- put k v (DB b) = DB ((k, toD v) : b)
put k v = Fld k d
  where
    d = toD v

{- get :: forall <p :: Field -> Dynamic -> Prop>. (Typeable a)
        => x:a -> f:Field
        -> d:{DBox <p> a | ((Set_mem f (defKeys d)) && ((fieldType d f) = (typeRep x)))}
        -> a<p f> / [(dsize d)]
  @-}
{-@ get :: forall <p :: Field -> Dynamic -> Prop>. (Typeable a)
        => f:Field
        -> d:DBox <p> ()
        -> exists[x:Dynamic<p f>].
           {v:a | (typeRep v) = (tag x)} / [(dsize d)]
  @-}
get :: (Typeable a) => Field -> DBox () -> a
-- get k (DB kvs) = ofD (undefined :: a) $ fromMaybe err $ lookup k kvs
--   where 
--     err        = error $ "NOT FOUND" ++ show k
get k Emp = error $ "NOT FOUND " ++ show k
get k (Fld k' v db)
  | k == k'   = ofD x v
  | otherwise = get k db
  where
    {-@ x :: {v:a | true} @-}
    x = undefined


{-@ getDyn :: forall <p :: Field -> Dynamic -> Prop>.
              d:DBox <p> b
           -> f:Field
           -> Dynamic<p f>
  @-}
getDyn :: DBox a -> Field -> Dynamic
getDyn Emp          k  = error $ "NOT FOUND " ++ show k
getDyn (Fld f v db) k
  | f == k    = v
  | otherwise = getDyn db k

{-@ toD :: (Typeable a) => x:a -> {v:Dynamic | (tag v) = (typeRep x)} @-}
toD :: (Typeable a) => a -> Dynamic 
toD = toDyn 

{-@ ofD :: (Typeable a) => x:a -> {v:Dynamic | (tag v) = (typeRep x)} -> a @-}
ofD :: (Typeable a) => a -> Dynamic -> a
ofD _ = fromMaybe (error "DYNAMIC ERROR") . fromDynamic
