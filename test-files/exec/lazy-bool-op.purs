module Main where

import Prelude
import Effect
import Effect.Console

loop :: Unit -> Boolean
loop x = loop x

lazy_test :: Boolean -> Effect Unit
lazy_test x = do
  (if x && (loop unit) then log "Mmmm ?!" else log "Good !")
  (if (not x) || (loop unit) then log "Good !" else log "Mmmm ?!")

main :: Effect Unit
main = do
  lazy_test (1 > 2)
