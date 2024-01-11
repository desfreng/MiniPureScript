module Main where

import Prelude
import Effect
import Effect.Console


bool_str :: Boolean -> String
bool_str true = "Yep"
bool_str false = "Nop..."

test :: Int -> Int -> Effect Unit
test a b =
  let gt = a > b
      ge = a >= b
      eq = a == b
      ne = a /= b
      le = a <= b
      lt = a < b in do
  log ("'" <> show a <> "' >  '" <> show b <> "'? : " <> bool_str gt)
  log ("'" <> show a <> "' >= '" <> show b <> "'? : " <> bool_str ge)
  log ("'" <> show a <> "' == '" <> show b <> "'? : " <> bool_str eq)
  log ("'" <> show a <> "' /= '" <> show b <> "'? : " <> bool_str ne)
  log ("'" <> show a <> "' <= '" <> show b <> "'? : " <> bool_str le)
  log ("'" <> show a <> "' <  '" <> show b <> "'? : " <> bool_str lt)

main :: Effect Unit
main = do
  test 50 50
  test 51 50
  test 49 50
  test (-50) (-50)
  test (-50) (-49)
  test (-50) (-51)
