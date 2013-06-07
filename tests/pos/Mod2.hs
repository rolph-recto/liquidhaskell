module Mod2 where

import qualified Mod1 as M

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ zinc :: x:M.Goo -> {v: M.Goo | (myg v) > (myg x)} @-}

zinc (M.G x) = M.G z'
  where 
    z        = x - 1
    z'       = liquidAssert (z > x) z
