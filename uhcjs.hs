module UHCJS where

import Functions

fib30 = fib 30

foreign export js "fibUHCJS"
  fib30 :: Int

main = return ()