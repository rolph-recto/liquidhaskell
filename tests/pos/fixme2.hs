
{-# LANGUAGE MultiParamTypeClasses #-}

module ZogBert where

import Control.Monad.Primitive ( PrimMonad, PrimState )

-- Adding this qualifier explicitly makes it safe, but why is it not auto-generated from the specs???

{- qualif Foo(v:a, x:a): 2 * (mvLen x) <= (mvLen v) @-}

{-@ enlarge :: (PrimMonad m, MVector v a) => x: (v (PrimState m) a) -> (m {v:(v (PrimState m) a) | (2 * (mvLen x)) <= (mvLen v)}) @-}
enlarge :: (PrimMonad m, MVector v a) => v (PrimState m) a -> m (v (PrimState m) a)
enlarge = undefined

{-@ bob :: (PrimMonad m, MVector v a) => x: (v (PrimState m) a) -> (m {v:(v (PrimState m) a) | (2 * (mvLen x)) <= (mvLen v)}) @-}
bob :: (PrimMonad m, MVector v a) => v (PrimState m) a -> m (v (PrimState m) a)
bob x = do y <- enlarge x
           return y

{-@ class measure mvLen :: forall a. a -> Int @-}

class MVector v a where
  length :: v s a -> Int
