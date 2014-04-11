module Test0 () where

import Language.Haskell.Liquid.Prelude

{-@ qualif Zog(v:FooBar, x:FooBar): v = x + 29 @-}

data FooBar = Foo Int

x = choose 0

prop_abs ::  Bool
prop_abs = if x > 0 then baz x else False

bob poo@(z,_) = z + 1

fac = go 1 where
  go accumulator numero 
    | numero <= 0 = accumulator
    | otherwise   = go (accumulator * numero) (numero - 1)  

baz gooberding = liquidAssertB (gooberding >= 0)
