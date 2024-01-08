module Main where

import Prelude
import Effect
import Effect.Console

data Three a = A | B a | C a a
data Either a b = Left a | Right b

class Print a where
  print :: a -> Effect Unit

instance (Show a, Show b) => Print (Either a b) where
  print (Left a) = log ("Left : " <> show a)
  print (Right a) = log ("Right : " <> show a)

instance Print a => Print (Three a) where
  print A = log "A"
  print (B a) = do
    log "B with:"
    print a
  print (C a b) = do
    log "C with:"
    print a
    log "and"
    print b


main :: Effect Unit
main =
    let e = (C (Left 1) (Right true)) in
    print e
