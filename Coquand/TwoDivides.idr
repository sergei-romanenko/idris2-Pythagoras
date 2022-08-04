module Coquand.TwoDivides

import Data.Nat
import Data.Either
import Syntax.PreorderReasoning

import Coquand.Misc

%default total

mutual

  data Even : Nat -> Type where
    Even0  : Even Z
    Even1 : {n : Nat} -> Odd n -> Even (S n)

  data Odd : Nat -> Type where
    Odd1 : {n : Nat} -> Even n -> Odd (S n)

Uninhabited (Odd Z) where
  uninhabited (Odd _) impossible


even'odd : (n : Nat) -> Even n `Either` Odd n
even'odd 0 =
  Left Even0
even'odd (S k) =
  mirror $ bimap Odd1 Even1 $ even'odd k

export
m2_S : (n : Nat) -> 2 * S n = S (S (2 * n))
m2_S n = Calc $
  |~ 2 * S n
  ~~ S (n + S (n + Z))   ... Refl
  ~~ S (S (n + (n + Z))) ... (cong S (sym $ plusSuccRightSucc n (n + Z)))
  ~~ S (S (2 * n))       ... Refl


even_m2 : (n : Nat) -> Even (2 * n)
even_m2 Z =
  Even0
even_m2 (S Z) =
  Even1 (Odd1 Even0)
even_m2 (S (S n)) = even_m2 n |>
    |~~ Even (2 * n)
    ~~> Even (S (S (2 *  n)))   ... (Even1 . Odd1)
    ~~> Even (2 * S n)          ... (\h => rewrite m2_S n in h)
    ~~> Even (S (S (2 * S n)))  ... (Even1 . Odd1)
    ~~> Even (2 * S (S n))      ... (\h => rewrite m2_S (S n) in h)


even_even_plus : (m, n : Nat) -> Even m -> Even (m + n) -> Even n
even_even_plus 0 n Even0 = id
even_even_plus (S 0) n (Even1 odd_Z) = absurd odd_Z
even_even_plus (S (S m)) n (Even1 (Odd1 even_m)) =
  |~~ Even (S (S (m + n)))
  ~~> Odd (S (m + n))      ... (\case (Even1 h) => h)
  ~~> Even (m + n)         ... (\case (Odd1 h) => h)
  ~~> Even n               ... (even_even_plus m n even_m)


odd_even_mult : (m, n : Nat) -> Odd m -> Even (m * n) -> Even n
odd_even_mult (S 0) n (Odd1 Even0) = 
  |~~ Even (1 * n)
  ~~> Even (n + 0) ... id
  ~~> Even n       ... (\h => rewrite sym $ plusZeroRightNeutral n in h)
odd_even_mult (S (S m)) n (Odd1 (Even1 odd_m)) =
  |~~ Even (S (S m) * n)
  ~~> Even (n + (n + m * n))
    ... id
  ~~> Even ((n + n) + m * n)
    ... (\h => rewrite sym $ plusAssociative n n (m * n) in h)
  ~~> Even ((n + (n + 0)) + m * n)
    ... (\h => rewrite plusZeroRightNeutral n in h)
  ~~> Even (2 * n + m * n)
    ... id
  ~~> Even (m * n)
    ... (even_even_plus (2 * n) (m * n) (even_m2 n))
  ~~> Even n
    ... (odd_even_mult m n odd_m)


-- 2 divides n

public export
d2 : (n : Nat) -> Type
d2 n = (x ** 2 * x = n)

even_d2 : (n : Nat) -> Even n -> d2 n
even_d2 0 Even0 =
  (0 ** Refl)
even_d2 (S 0) (Even1 odd_Z) = absurd odd_Z
even_d2 (S (S n)) (Even1 (Odd1 even_n)) with (even_d2 n even_n)
  _ | (x ** eq_2x__n) = (S x ** eq_2sx__ssn)
    where
    eq_2sx__ssn : 2 * S x = S (S n)
    eq_2sx__ssn = Calc $
      |~ 2 * S x
      ~~ S (S (2 * x)) ... (m2_S x)
      ~~ S (S n) ... (cong (S . S) eq_2x__n)


d2_even : (n : Nat) -> d2 n -> Even n
d2_even n ((x ** eq_2x_n)) = even_m2 x |>
  |~~ Even (2 * x)
  ~~> Even n       ... (\h => rewrite sym $ eq_2x_n in h)


even_mult_even'even : (m, n : Nat) -> Even (m * n) ->
  Even m `Either` Even n
even_mult_even'even m n even_mn with (even'odd m)
  _ | Left even_m = Left even_m
  _ | Right odd_m = Right $ odd_even_mult m n odd_m even_mn


export
d2mn_d2m'd2n : (m, n : Nat) -> d2 (m * n) -> d2 m `Either` d2 n
d2mn_d2m'd2n m n =
  |~~ d2 (m * n)
  ~~> Even (m * n)             ... (d2_even (m * n))
  ~~> (Even m `Either` Even n) ... (even_mult_even'even m n)
  ~~> (d2 m `Either` d2 n)     ... (bimap (even_d2 m) (even_d2 n))
