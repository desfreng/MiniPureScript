module Main where

import Prelude
import Effect
import Effect.Console

data Q = Q Int Int
data Pair a b c d = P a b c d

instance Show Q where
  show (Q n d) = show n <> "/" <> show d


float_pres :: Int -> Q -> String -> String
float_pres i (Q a b) acc =
  if i == 0 then acc
  else  let dix_a = 10 * a
            d = dix_a / b
            new_a = mod dix_a b
        in float_pres (i - 1) (Q new_a b) (acc <> show d)


to_string :: Int -> Q -> String
to_string pres (Q a b) =
  let ent = a / b
      frac = mod a b
  in float_pres pres (Q frac b) (show ent <> ".")


pgcd :: Int -> Int -> Int
pgcd a 0 = a
pgcd a b = pgcd b (mod a b)

mk :: Int -> Int -> Q
mk a b = let p = pgcd a b
             na = a / p
             nb = b / p in Q na nb

add :: Q -> Q -> Q
add x y = case x of Q xn xd -> case y of Q yn yd -> mk (xn * yd + yn * xd) (xd * yd)

mul :: Q -> Q -> Q
mul x y = case x of Q xn xd -> case y of Q yn yd -> mk (xn * yn) (xd * yd)

-- This approximate the value of pi with the Bailey–Borwein–Plouffe formula
-- We return a pair of the approximation and 16^k
bbp :: Int -> Pair Q Int Q Q
bbp 0 = P (Q 47 15) 1 (Q 0 0) (Q 0 0)
bbp n =
  let tmp = let a = mk ( 4) (8 * n + 1)
                b = mk (-2) (8 * n + 4)
                c = mk (-1) (8 * n + 5)
                d = mk (-1) (8 * n + 6)
            in add (add a b) (add c d)
      prev = bbp (n - 1)
  in case prev of
    P prev_app prev_seize_n _ _ ->
      let seize_n = 16 * prev_seize_n
          curr_term = mul (Q 1 seize_n) tmp
          curr_app = add prev_app curr_term
      in P curr_app seize_n tmp curr_term


pi :: Int -> Q
pi k =  case bbp k of P app _ _ _ -> app


loop :: Int -> Effect Unit
loop (-1) = pure unit
loop i = do
  loop (i - 1)
  (let q = pi i in log ("bbp (" <> show i <> ") = " <> show q <> " ~ " <> to_string 15 q))


main :: Effect Unit
main =  loop 3  -- WARNING this only work because we use 64bit integers !
                -- Purescript is accurate up to rank 1...
                -- The output has been generated with the following Python code:

-- from sympy import *
--
-- prec = 15
-- pi = Rational(0)
-- for n in range(0, 4):
--     u = Rational(4, 8*n+1) - Rational(2, (8*n+4)) - \
--         Rational(1, (8*n+5)) - Rational(1, (8*n+6))
--     d = Rational(1, 16) ** n
--     pi += d * u
--     rep = int(pi.evalf(prec + 1) * (10 ** prec)) / \
--         (10 ** prec)  #  to truncate instead of round off
--     print(f"bbp ({n}) = {pi} ~ {rep}")
