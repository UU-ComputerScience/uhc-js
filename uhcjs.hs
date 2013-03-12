module UHCJS where

import Functions

fib' x = case fib x of
            0 -> 0
            n -> n

foreign export js "fibUHCJS"
  fib' :: Int -> Int

foreign export js "sumUHCJS"
  sumStrict :: Int -> Int

foreign export js "primesUHCJS"
  primes :: Int -> Int

main = return ()