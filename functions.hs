module Functions (fib, primes) where

import           Data.List ( foldl' )
                
fib :: Int -> Int
fib 1 = 1
fib 2 = 2
fib n = fib (n-2) + fib (n-1)

primes :: Int -> [Int]
primes n = take n primesEU

sumNonStrict :: Int
sumNonStrict = foldl (+) 0 [1..1000000]

sumStrict :: Int
sumStrict = foldl' (+) 0 [1..1000000]

primesEU = 2 : eulers [3,5..] where
  eulers (p:xs) = p : eulers (xs `minus` map (p*) (p:xs))

-- ordered lists, difference and union
minus (x:xs) (y:ys) = case (compare x y) of 
           LT -> x : minus  xs  (y:ys)
           EQ ->     minus  xs     ys 
           GT ->     minus (x:xs)  ys
minus  xs     _     = xs
union (x:xs) (y:ys) = case (compare x y) of 
           LT -> x : union  xs  (y:ys)
           EQ -> x : union  xs     ys 
           GT -> y : union (x:xs)  ys
union  xs     []    = xs
union  []     ys    = ys