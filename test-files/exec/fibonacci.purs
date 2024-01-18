module Main where

import Prelude
import Effect
import Effect.Console

data List a = Nil | Cons a (List a)

fibo :: Int -> List Int
fibo 0 = Cons 0 Nil
fibo 1 = Cons 1 (fibo 0)
fibo n =
    let l = fibo (n-1) in
    case l of
        Cons i (Cons j _) -> Cons (i + j) l
        _ -> Nil -- Impossible case


rev_list_acc :: forall a. List a -> List a -> List a
rev_list_acc acc Nil = acc
rev_list_acc acc (Cons hd tl) = rev_list_acc (Cons hd acc) tl

rev_list :: forall a. List a -> List a
rev_list l = rev_list_acc Nil l

print_list_acc :: forall a. Show a => Int -> List a -> Effect Unit
print_list_acc _ Nil = pure unit
print_list_acc pos (Cons hd tl) =
    do
        (let line1 = show pos <> ": "
             line2 = if pos < 10 then line1 <> " " else line1
             line3 = line2 <> show hd
         in log line3)
        print_list_acc (pos + 1) tl

print_list :: forall a. Show a => String -> List a -> Effect Unit
print_list title l = do
    log title
    print_list_acc 0 l

main :: Effect Unit
main = print_list "Fibonacci Sequence:" (rev_list (fibo 46))