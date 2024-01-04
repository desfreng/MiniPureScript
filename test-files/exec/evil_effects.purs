module Main where

import Prelude
import Effect
import Effect.Console


data List a = Nil | Cons a (List a)

iter_do :: List (Effect Unit) -> Effect Unit
iter_do Nil = pure unit
iter_do (Cons hd tl) = do
  hd
  iter_do tl

mdo :: List (Effect Unit) -> Effect Unit
mdo x = do
  log "Begin :"
  iter_do x
  log "Done !"

log_count :: Int -> List (Effect Unit)
log_count 0 = Nil
log_count x = Cons (log (show x)) (log_count (x - 1))


repeat :: Int -> Effect Unit -> List (Effect Unit)
repeat 0 _  = Nil
repeat x eff = Cons eff (repeat (x - 1) eff)

boxed :: Effect Unit -> Effect Unit
boxed eff = do
  log "Begin Boxed"
  eff
  log "End Boxed"

main :: Effect Unit
main =
  let n2 = repeat 2 (mdo (log_count 5)) in
  let n3 = repeat 3 (mdo (log_count 2)) in
  do
    boxed (mdo n2)
    boxed (mdo n3)