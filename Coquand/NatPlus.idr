module Coquand.NatPlus

import Data.Nat

import Coquand.Misc

%default total

infix 9 ##

public export
data NatP : Type where
  (##) : (x : Nat) -> (p : NonZero x) -> NatP

public export
fP : NatP -> Nat
fP (x ## p) = x

predP : NatP -> Nat
predP (0 ## SIsNonZero) impossible
predP (S x ## SIsNonZero) = x

public export
Nz1 : NatP
Nz1 = S Z ## SIsNonZero

public export
Nz2 : NatP
Nz2 = S (S Z) ## SIsNonZero

infix 6 =#

public export
(=#) : (m, n : NatP) -> Type
(x ## p) =# (y ## q) = x = y

public export
irrel_nz : (x : Nat) -> (p, q : NonZero x) -> p = q
irrel_nz (S x) SIsNonZero SIsNonZero = Refl

public export
eqp_eq : (m, n : _) -> m =# n -> m = n
eqp_eq ((S x) ## SIsNonZero) ((S y) ## SIsNonZero) sx__sy =
  rewrite cong pred sx__sy in
  Refl

public export
eq_eqp : (m, n : _) -> m = n -> m =# n
eq_eqp (x ## p) (x ## p) Refl = Refl

nz_plus : (m, n : NatP) -> NonZero (fP m + fP n)
nz_plus (S x ## SIsNonZero) (S y ## SIsNonZero) = SIsNonZero

public export
nz_mult : (m, n : NatP) -> NonZero (fP m * fP n)
nz_mult (S x ## SIsNonZero) (S y ## SIsNonZero) = SIsNonZero {x = y + x * S y}


infixl 8 +#
infixl 9 *#

(+#) : (m, n : NatP) -> NatP
m +# n = (fP m + fP n) ## nz_plus m n

public export
(*#) : (m, n : NatP) -> NatP
m *# n = (fP m * fP n) ## nz_mult m n

export
plusp_assoc : (l, c, r : NatP) -> l +# (c +# r) = (l +# c) +# r
plusp_assoc l c r =
  eqp_eq (l +# (c +# r)) ((l +# c) +# r) $
    plusAssociative (fP l) (fP c) (fP r)

export
multp_assoc : (l, c, r : NatP) -> l *# (c *# r) = (l *# c) *# r
multp_assoc l c r =
  eqp_eq (l *# (c *# r)) ((l *# c) *# r) $
    multAssociative (fP l) (fP c) (fP r)

export
multp_leftIdentity : (n : NatP) -> Nz1 *# n = n
multp_leftIdentity (x ## p) =
  eqp_eq (Nz1 *# (x ## p)) (x ## p) $ plusZeroRightNeutral x

export
multp_comm : (m, n : NatP) -> m *# n =  n *# m
multp_comm m n =
  eqp_eq (m *# n) (n *# m) $ multCommutative (fP m) (fP n)

mult_cancel_right : (x, y, k : Nat) -> x * S k = y * S k -> x = y
mult_cancel_right Z Z k Refl = Refl
mult_cancel_right Z (S y) k z__s = absurd z__s
mult_cancel_right (S x) Z k s__z = absurd s__z
mult_cancel_right (S x) (S y) k h = h |>
  |~~ (S x * S k = S y * S k)
  ~~> (S (k + x * S k) = S (k + y * S k)) ... id
  ~~> (k + x * S k = k + y * S k)         ... injective
  ~~> (x * S k = y * S k)                 ... (plusLeftCancel k (x * S k) (y * S k))
  ~~> (x = y)                             ... (mult_cancel_right x y k)
  ~~> (S x = S y)                         ... (cong S)

mult_cancel_left : (x, y, k : Nat) -> S k * x = S k * y -> x = y
mult_cancel_left x y k =
  |~~ (S k * x = S k * y)
  ~~> (x * S k = S k * y) ... (\h => rewrite multCommutative x (S k) in h)
  ~~> (x * S k = y * S k) ... (\h => rewrite multCommutative y (S k) in h)
  ~~> (x = y)             ... (mult_cancel_right x y k)

export
multp_cancel_left : (m, n, k : NatP) -> k *# m = k *# n -> m = n
multp_cancel_left (x ## p) (y ## q) (0 ## r) h = absurd r
multp_cancel_left (x ## p) (y ## q) ((S k) ## r) h
  with (eq_eqp ((S k ## r) *# (x ## p)) ((S k ## r) *# (y ## q)) h)
  _ | sk_x__sk_y with (mult_cancel_left x y k sk_x__sk_y)
    _ | x__y =
      rewrite x__y in
      cong (y ##) $ irrel_nz y (rewrite sym $ x__y in p) q
