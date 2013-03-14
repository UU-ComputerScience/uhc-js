{-# LANGUAGE NoImplicitPrelude #-}
module Fay where

import Functions

import Prelude


sumTest :: Int
sumTest = sum [1..100000]

primesTest :: Int
primesTest = primes 1700

fibTest :: Int
fibTest = fib 30