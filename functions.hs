module Functions (fib, primes, sumNonStrict, sumStrict) where

--import           Data.List ( foldl' )
import Prelude hiding (EQ, LT, GT, compare)
                
fib :: Int -> Int
fib 1 = 1
fib 2 = 2
fib n = fib (n-2) + fib (n-1)


sumNonStrict :: Int -> Int
sumNonStrict m = foldl (+) 0 [1..m]

sumStrict :: Int -> Int
sumStrict m = foldl (+) 0 [1..m]

primes :: Int -> Int
primes n = sum $ take n primesEU

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

data Ord' = LT | EQ | GT

compare :: Int -> Int -> Ord'
compare x y | x < y  = LT
						| x == y = EQ 
						| x > y  = GT