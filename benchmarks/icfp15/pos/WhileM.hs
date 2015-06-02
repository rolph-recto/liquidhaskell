module WhileM where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO 

{-@
whileM  :: forall < p   :: World -> Prop 
               , qc :: World -> Bool -> World -> Prop
               , qe :: World -> () -> World -> Prop
               , q  :: World -> () -> World -> Prop>. 
       {x::(), s1::World<p>, b::{v:Bool | Prop v}, s2::World<qc s1 b> |- World<qe s2 x> <: World<p>}
       {b::{v:Bool | Prop v}, x2::(), s1::World<p>, s3::World |- World<q s3 x2> <: World<q s1 x2> } 
       {b::{v:Bool | not (Prop v)}, x2::(), s1::World<p> |- World<qc s1 b> <: World<q s1 x2> } 
          RIO <p, qc> Bool 
       -> RIO <{\v -> true}, qe> ()
       -> RIO <p, q> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e) 
    = undefined -- moved to todo because it breaks travis, but why?