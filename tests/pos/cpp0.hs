{-# LANGUAGE CPP #-}

module Zog where

#include "cpp0.h"

{-@ foo :: x:Nat -> {v:Nat | v = x + 1} @-}
foo :: Int -> Int
foo x = INCREMENTALWHATSIT(x)
