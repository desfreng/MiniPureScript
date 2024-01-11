module Main where

import Prelude
import Effect
import Effect.Console


str_eq :: String -> String -> Boolean
str_eq x y = x == y

str_neq :: String -> String -> Boolean
str_neq x y = x /= y

test :: String -> String -> Effect Unit
test a b =
  let eq = str_eq a b
      neq = str_neq a b in do
  log ("'" <> a <> "' == '" <> b <> "'? : " <> show eq)
  log ("'" <> a <> "' /= '" <> b <> "'? : " <> show neq)

main :: Effect Unit
main = do
  test "Hello" "World"
  test "Hello" "hello"
  test "Hello" "Hello "
  test "Hello" "Hello"
