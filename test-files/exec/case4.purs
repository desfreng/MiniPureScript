module Main where

import Prelude
import Effect
import Effect.Console


data List a = Nil | Cons a (List a)

string_to_int  ::  String -> Int
string_to_int "zero" = 0
string_to_int "un" = 1
string_to_int "deux" = 2
string_to_int "trois" = 3
string_to_int "quatre" = 4
string_to_int "cinq" = 5
string_to_int "six" = 6
string_to_int "sept" = 7
string_to_int "huit" = 8
string_to_int "neuf" = 9
string_to_int _ = -1

iter_print :: List String -> Effect Unit
iter_print Nil = pure unit
iter_print (Cons hd tl) =
  let i = string_to_int hd
      txt = show i <> " : " <> hd in do
    log txt
    iter_print tl

int_to_strlist :: Int -> List String
int_to_strlist n = if n >= 1 then
  let p = mod n 10
      q = n / 10 in
  let s = case p of
        0 -> "zero"
        1 -> "un"
        2 -> "deux"
        3 -> "trois"
        4 -> "quatre"
        5 -> "cinq"
        6 -> "six"
        7 -> "sept"
        8 -> "huit"
        9 -> "neuf"
        _ -> ""
  in Cons s (int_to_strlist q) else Nil

reverse :: forall a. List a -> List a -> List a
reverse Nil acc = acc
reverse (Cons hd tl) acc = reverse tl (Cons hd acc)

main :: Effect Unit
main = let x = int_to_strlist 314159265
           y = reverse x Nil in
  do
    iter_print y