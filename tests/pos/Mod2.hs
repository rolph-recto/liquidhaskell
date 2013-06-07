module Mod2 where

import qualified Mod1 as M


{-@ zinc :: x:M.Goo -> {v: M.Goo | (myg v) > (myg x)} @-}

zinc (M.G x) = M.G (x + 1)

