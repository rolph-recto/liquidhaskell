{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "-m4" @-}
module Dyn (ok, bad, bad2, bad3) where

import Data.Dynamic
import Data.Maybe
import Data.Set

import GHC.Base

import Language.Haskell.Liquid.Prelude (liquidError, proxy)


{- b0 :: {v:DBox () | (((defKeys v) = (Set_cup (Set_sng 0) (Set_sng 1)))
                     && ((fieldType v 0) = "String")
                     && ((fieldType v 1) = "Int"))}
  @-}
{-@ b0 :: DBox < {\k -> ((k = 0) || (k = 1))}
               , {\k v -> ((FieldType k 0 v "String") && (FieldType k 1 v "Int"))}> ()
  @-}
b0    = put 0 ("cat" :: String) b1
      -- $ put 1 (12    :: Int)
      -- $ emp

b1 = put 1 (12 :: Int) emp

b2 = put 0 ("cat" :: String) b1

{-@ ok :: {v:Int | (typeRep v) = "Int"} @-}
ok :: Int
ok    = get 1 b2

{-@ bad :: {v:Int | (typeRep v) = "Int"} @-}
bad :: Int
bad   = get 0 foo -- ofD (getDyn foo 0)

{-@ bad' :: {v:String | (typeRep v) = "String"} @-}
bad' :: String
bad'   = get 0 foo -- ofD (getDyn foo 0)

bad2  = undefined --10 `plus` ofD (getDyn b0 2)

bad3  = undefined --putDyn 1 (toD (10 :: Int)) b0



{-@ foo :: DBox <{\f -> f = 0},{\f v -> (FieldType f 0 v "String") }> () @-}
foo = put 0 ("cat" :: String) emp

-------------------------------------------------
plus :: Int -> Int -> Int
plus = (+)

-- concat :: String -> String -> String
-- concat = (++)

-------------------------------------------------

{-@ predicate FieldType F K V T = ((F = K) => ((tag V) = T)) @-}

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

-- FIXME: why doesn't this work with a newtype?
data DBox a = DB (Field -> Dynamic)
{-@ data DBox a <dom :: Field -> Prop, rng :: Field -> Dynamic -> Prop>
      = DB (x :: f:Field<dom> -> Dynamic<rng f>)
  @-}
-- newtype DBox a = DB [(Field, Dynamic)]
-- data DBox a = Emp
--           | Fld Field Dynamic (DBox a)
{- data DBox a <p :: Field -> Dynamic -> Prop>
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
{- measure dsize :: DBox a -> Int
    dsize (Emp)        = 0
    dsize (Fld k v db) = 1 + (dsize db)
  @-}
{- invariant {v:DBox a | (dsize v) >= 0} @-}
{-@ measure getField :: Field -> DBox a -> Dynamic
  @-}
{-@ measure fieldType :: DBox a -> Field -> Str
  @-}


{- measure defKeys :: DBox a -> (Set Field)
    defKeys (Emp)       = {v | (? (Set_emp v))}
    defKeys (Fld k x d) = {v | v = (Set_cup (Set_sng k) (defKeys d))}
  @-}
{- type DBoxWithKey a F D = {v:DBox a | (defKeys v) = (Set_cup (Set_sng F) (defKeys D))} @-}

{- emp :: forall <r :: Field -> Dynamic -> Prop>. DBox <{\f -> false}, r> () @-}
{-@ emp :: DBox <{\f -> false}, {\f v -> false}> () @-}
emp :: DBox ()
emp = DB $ \x -> liquidError $ "NOT FOUND " ++ show x -- Emp -- DB []

{- put :: forall <p :: Field -> Dynamic -> Prop>. (Typeable a)
        => f:Field -> x:a -> d:DBox a
        -> {v:DBox aWithKey f d | (((fieldType v f) = (typeRep x)))}
  @-}
{- put :: forall <d :: Field -> Prop, r :: Field -> Dynamic -> Prop>.
           (Typeable a)
        => f:Field -> x:a -> DBox <d, r> ()
        -> {v:DBox <{\k -> ((k = f) || (d k))}, r> () | (tag (getField f v)) = (typeRep x) }
  @-}
{-@ put :: forall <d :: Field -> Prop, r :: Field -> Dynamic -> Prop>.
           (Typeable a)
        => f:Field<d>
        -> x:a
        -> DBox <{v:Field<d> | v != f}, \k -> {v:Dynamic<r k> | k != f}> ()
        -> DBox <d, \k -> {v:Dynamic<r k> | (FieldType f k v (typeRep x))}> ()
  @-}
        -- -> DBox <{v:Field<d> | v != f}, r> ()
-- (tag (getField f v)) = (typeRep x)
{- putDyn :: forall <d :: Field -> Prop, r :: Field -> Dynamic -> Prop>.
              f:Field<d>
           -> x:Dynamic<r f>
           -> DBox <{v:Field<d> | v != f}, r> ()
           -> DBox <d, r> ()
  @-}

put :: (Typeable a) => Field -> a -> DBox () -> DBox ()
-- put k v (DB b) = DB ((k, toD v) : b)
-- put k v = Fld k d
--   where
--     d = toD v
put k v (DB db) = DB $ \x -> if x == k then d else db x
  where d = toD v

{- get :: forall <p :: Field -> Dynamic -> Prop>. (Typeable a)
        => x:a -> f:Field
        -> d:{DBox <p> a | ((Set_mem f (defKeys d)) && ((fieldType d f) = (typeRep x)))}
        -> a<p f> / [(dsize d)]
  @-}
{-@ get :: forall <d :: Field -> Prop, r :: Field -> Dynamic -> Prop>. (Typeable a)
        => f:Field<d>
        -> DBox <d, r> ()
        -> exists[x:Dynamic<(r f)>].
           {v:a | (typeRep v) = (tag x)}
  @-}
get :: (Typeable a) => Field -> DBox () -> a
-- get k (DB kvs) = ofD (undefined :: a) $ fromMaybe err $ lookup k kvs
--   where 
--     err        = error $ "NOT FOUND" ++ show k
-- get k Emp = error $ "NOT FOUND " ++ show k
-- get k (Fld k' v db)
--   | k == k'   = ofD v
--   | otherwise = get k db
  -- where
  --   {- x :: {v:a | true} @-}
  --   x = undefined
get k (DB db) = ofD' proxy d
  where d = db k


{-@ getDyn :: forall <d :: Int -> Prop, r :: Field -> Dynamic -> Prop>.
              DBox <d, r> ()
           -> f:Field<d>
           -> Dynamic<r f>
  @-}
getDyn :: DBox () -> Field -> Dynamic
getDyn (DB db) k = db k

--FIXME: the following is UNSAFE because d:DBox shadows d:Pred, shouldn't happen...
{- getDyn :: forall <d :: Int -> Prop, r :: Field -> Dynamic -> Prop>.
            -> d:DBox <d, r> ()
            -> Int<d>
            -> Dynamic<r f>
  @-}

{-@ putDyn :: forall <d :: Field -> Prop, r :: Field -> Dynamic -> Prop>.
              f:Field<d>
           -> x:Dynamic<r f>
           -> DBox <{v:Field<d> | v != f}, \k -> {v:Dynamic<r k> | k != f}> ()
           -> DBox <d, \k -> {v:Dynamic<r k> | (FieldType f k v (tag x))}> ()
  @-}
           -- -> {v:DBox <d, r> () | (tag (getField f v)) = (tag x) }
putDyn :: Field -> Dynamic -> DBox () -> DBox ()
putDyn k v (DB db) = DB $ \x -> if k == x then v else db x

{-@ toD :: (Typeable a) => x:a -> {v:Dynamic | (tag v) = (typeRep x)} @-}
toD :: (Typeable a) => a -> Dynamic 
toD = toDyn 

{- ofD :: (Typeable a) => x:a -> d:{Dynamic | (tag d) = (typeRep x)} -> {v:a | (tag d) = (typeRep v)} @-}
{-@ ofD :: (Typeable a)
        => d:Dynamic
        -> exists[m:Maybe {v:a | (typeRep v) = (tag d)}]. {v:a | v = (fromJust m)}
  @-}
ofD :: (Typeable a) => Dynamic -> a
-- ofD = fromMaybe (error "DYNAMIC ERROR") . fromDynamic
ofD = undefined -- fromJust . fromDynamic


{-@ ofD' :: (Typeable a) => x:a -> d:{Dynamic | (tag d) = (typeRep x)} -> {v:a | (tag d) = (typeRep v)} @-}
ofD' :: (Typeable a) => a -> Dynamic -> a
ofD' _ = undefined -- fromJust . fromDynamic

{-@ fromDynamic :: (Typeable a) => d:Dynamic -> {v:Maybe {x:a | (((tag d) = (typeRep x)) => (isJust v))} | true} @-}
{-@ fromJust :: x:{Maybe a | (isJust x)} -> {v:a | v = (fromJust x)} @-}









