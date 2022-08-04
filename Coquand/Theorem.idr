module Coquand.Theorem

import Syntax.PreorderReasoning
import Control.WellFounded

import Coquand.Cancellative

%default total

{-
The original proof was written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

public export
Multiple :  CAMonoid a => (p, x, y : a) -> Type
Multiple p x y = (p <.> x) = y

public export
divides : {a : Type} -> CAMonoid a => (x, y : a) -> Type
divides x y = (z ** x <.> z = y)

public export
Prime : {a : Type} -> CAMonoid a => (p : a) -> Type
Prime p = (x, y : a) -> p `divides` (x <.> y) ->
  (p `divides` x) `Either` (p `divides` y)

public export
NotSquare : {a : Type} -> CAMonoid a => (p : a) -> Type
NotSquare p = (x, y : a) -> Not (p <.> (x <.> x) = y <.> y)

p_sq : {a : Type} -> CAMonoid a =>
  (p, x : a) -> Prime p -> p `divides` (x <.> x) -> p `divides` x
p_sq p x prime_p p_xx with (prime_p x x p_xx)
  _ | Left  (z ** pz__x) = (z ** pz__x)
  _ | Right (z ** pz__x) = (z ** pz__x)

down : {a : Type} -> CAMonoid a =>
  (p : a) -> Prime p -> (x, y : a) ->  p <.> (x <.> x) = (y <.> y) ->
    (z ** (p <.> z = y, p <.> (z <.> z) = (x <.> x)))
down p prime_p x y pxx__yy with (p_sq p y prime_p ((x <.> x) ** pxx__yy))
  _ | ((w ** pw__y)) = (w ** (pw__y ,
    the (p <.> (w <.> w) = x <.> x) $
    cancelLeft p (p <.> (w <.> w)) (x <.> x) helper))
    where
    helper : p <.> (p <.> (w <.> w)) = p <.> (x <.> x)
    helper = Calc $
      |~ p <.> (p <.> (w <.> w))
      ~~ p <.> ((p <.> w) <.> w) ... (cong2 (<.>) Refl (opIsAssociative p w w))
      ~~ p <.> (w <.> (p <.> w)) ... (cong2 (<.>) Refl (opIsCommutative (p <.> w) w))
      ~~ (p <.> w) <.> (p <.> w) ... (opIsAssociative p w (p <.> w))
      ~~ y <.> y                 ... (cong2 (<.>) pw__y pw__y)
      ~~ p <.> (x <.> x)         ... (sym pxx__yy)


-- ======
-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be a square of rational in cancellative
-- abelian monoid.
-- ======

theorem' : {a : Type} -> CAMonoid a =>
  (p : a) -> Prime p ->
  (x, u : a) -> p <.> (x <.> x) = (u <.> u) ->
  Accessible (Multiple p) u -> Void
theorem' p prime_p x u pxx__uu (Access rec) =
  let
    (y ** (py__u, pyy_xx)) = down p prime_p x u pxx__uu
    (w ** (pw__x, pww__yy)) = down p prime_p y x pyy_xx
  in
  theorem' p prime_p w y pww__yy (rec y py__u)

export
theorem : {a : Type} -> CAMonoid a =>
  (p : a) -> WellFounded a (Multiple p) => Prime p -> NotSquare p
theorem p prime_p x u pxx__uu =
  theorem' p prime_p x u pxx__uu (wellFounded u)
