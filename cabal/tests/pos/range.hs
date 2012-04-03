module Range where

import Language.Haskell.Liquid.Prelude

range :: Int -> Int -> [Int]
range i j  
  | i < j     = i : (range (i + 1) j)
  | otherwise = []  

sumTo = foldl (+) 0 . range 0

n = choose 0 
m = choose 1

mymap f [] = []
mymap f (x:xs) = (f x) : (mymap f xs)

prop_rng1 = mymap (assert . (0 <=)) $ range 0 n
prop_rng2 = mymap (assert . (n <=)) $ range n 100
prop_rng3 = mymap (assert . (n <=)) $ range n m
prop_rng4 = mymap (assert . (<= m)) $ range n m 
--prop_rng5 = assert (0 <= sumTo n)
