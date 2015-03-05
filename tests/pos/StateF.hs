module State (
   returnST -- :: a -> ST a s
 , bindST   -- :: ST a s -> (a -> ST b s) -> ST b s
 , ST(..)
 ) where

import Prelude hiding (snd, fst)

data ST a s = S (s -> (a, s))
{-@ data ST a s <pre :: s -> Prop, post :: s -> a -> s -> Prop> 
       = S (ys::(x:s<pre> -> ((a, s)<\xx -> {v:s<post x xx> | true}>)))
  @-}

{-@ returnST :: forall <pre :: s -> Prop>.
               y:a
           -> ST <pre, {\xs xa v -> ((v = xs) && (xa = y))}> a s
  @-}
returnST :: a -> ST a s
returnST x = S $ \s -> (x, s)

{-@ bindST :: forall <p :: s -> Prop, q :: s -> a -> s -> Prop, r :: s -> b -> s -> Prop>.
            (xm:s<p> -> (a, s)<\xx -> {v:s<q xm xx> | true}>) 
         -> (xbind:a -> xk:s -> (b, s)<\xx -> {v:s<r xk xx> | true}>) 
         -> (xr:s<p> -> exists[xa:a].exists[xs:s<q xr xa>].(b, s)<\xx -> {v:s<r xs xx> | true}>)
 @-}
bindST :: (s -> (a, s)) -> (a -> (s -> (b, s))) -> (s ->  (b, s))
bindST m k = \s -> let (a, s') = m s in (k a) s'

{- bindST :: forall <p :: s -> Prop, q :: s -> a -> s -> Prop, r :: s -> b -> s -> Prop>.
            ST <p, q> a s 
         -> (xbind:a -> ST <{v:s<q xbind> | true}, r> b s) 
         -> ST <p, r> b s
 @-}
-- bindST :: ST a s -> (a -> ST b s) -> ST b s
-- bindST (S m) k = S $ \s -> let (a, s') = m s in apply (k a) s'

{- apply :: forall <p :: s -> Prop, q :: s -> a -> s -> Prop>.
             ST <p, q> a s -> x:s<p> -> (a, s)<q x>
  @-}
-- apply :: ST a s -> s -> (a, s)
-- apply (S f) s = f s
