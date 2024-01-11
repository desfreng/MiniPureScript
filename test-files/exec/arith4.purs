module Main where

import Prelude
import Effect
import Effect.Console

arith_op :: Int -> Int -> Effect Unit
arith_op x y =
  let add = x + y
      sub = x - y
      mul = x * y
      div = x / y
      mo = mod x y in
  do
    log (show x <> " + " <> show y <> " = " <> show add)
    log (show x <> " - " <> show y <> " = " <> show sub)
    log (show x <> " * " <> show y <> " = " <> show mul)
    log (show x <> " / " <> show y <> " = " <> show div)
    log (show x <> " % " <> show y <> " = " <> show mo)

main::Effect Unit
main = do
  arith_op ( 17) ( 5)
  arith_op (-17) ( 5)
  arith_op ( 17) (-5)
  arith_op (-17) (-5)
  arith_op ( 17) ( 0)
  arith_op (  0) ( 4)
  arith_op (  0) ( 0)
