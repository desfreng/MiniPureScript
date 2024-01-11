module Main where

import Prelude
import Effect
import Effect.Console

data List a b = Nil a | Cons b (List a b)

instance (Show a, Show b) => Show (List a b) where
  show (Nil a) = "[" <> show a <> "]"
  show (Cons hd tl) = show hd <> "::" <> show tl

main::Effect Unit
main = let x = Nil 0 in do
    log (show x)
    (let y = Cons true x in log (show y))
