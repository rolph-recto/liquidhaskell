module Mod1 where

data Goo = G Int

{-@ measure myg :: Goo -> Int 
    myg (G n) = n
  @-}
 
{-@ inc :: x:Goo -> {v: Goo | (myg v) > (myg x)} @-}
inc (M.G x) = M.G (x + 1)


