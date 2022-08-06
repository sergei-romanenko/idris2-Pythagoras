module Coquand.Corollary

import Data.Nat
import Control.WellFounded

import Coquand.Misc
import Coquand.NatPlus
import Coquand.TwoDivides
import Coquand.Cancellative
import Coquand.Theorem

%default total

implementation CAMonoid NatP where

  (<.>) = (*#)
  neutral = Nz1

  opIsAssociative = multp_assoc
  opIsCommutative = multp_comm
  neutralLeft = multp_leftIdentity
  cancelLeft k x y = multp_cancel_left x y k

-- Prime Nz2

divides_d2 : (n : NatP) -> Nz2 `divides` n -> d2 (fromNatP n)
divides_d2 (x ## p) ((y ## q) ** h) =
  (y ** cong fromNatP h)

d2_divides : (n : NatP) -> d2 (fromNatP n) -> Nz2 `divides` n
d2_divides (0 ## nz_Z) (y ** h) = absurd nz_Z
d2_divides (S x ## p) (0 ** z__s) = absurd z__s
d2_divides (S x ## SIsNonZero) (S y ** h) =
  ((S y ## SIsNonZero) ** (
    eqp_eq (S (plus y (S (plus y 0))) ## SIsNonZero) (S x ## SIsNonZero) h
  ))

prime_Nz2 : Prime Nz2
prime_Nz2 (x ## p) (y ## q) h
  with (divides_d2 ((x ## p) *# (y ## q)) h)
  _ | d2_xy = bimap (d2_divides (x ## p)) (d2_divides (y ## q))
        $ d2mn_d2m'd2n x y d2_xy


-- RelMorph NatP & Nat

lt_m2 : (x : Nat) -> NonZero x -> x `LT` 2 * x
lt_m2 (S x) SIsNonZero = lteAddRight x |>
  |~~ (x `LTE` x + x)
  ~~> (x `LTE` x + (x + 0))
    ... (\h => rewrite plusZeroRightNeutral x in h)
  ~~> (x `LTE` 2 * x)
    ... id
  ~~> (2 + x `LTE` 2 + 2 * x)
    ... (LTESucc . LTESucc)
  ~~> (2 + x `LTE` 2 * (1 + x))
    ... (\h => rewrite multDistributesOverPlusRight 2 1 x in h)

LTP : (m, n : NatP) -> Type
m `LTP` n = fromNatP m `LT` fromNatP n

nz2eq_LTP : (m, n : NatP) -> Multiple Nz2 m n -> m `LTP` n
nz2eq_LTP (x ## p) (y ## q) eq_2m_n =
  rewrite sym $ (cong fromNatP eq_2m_n) in
  lt_m2 x p

nz2eq_LT : (m, n : NatP) -> Multiple Nz2 m n -> fromNatP m `LT` fromNatP n

-- Well-founded

RelMorphNatPNat : RelMorph NatP Nat (Multiple Nz2) LT
RelMorphNatPNat = MkRelMorph fromNatP nz2eq_LT

WellFounded NatP (Multiple Nz2) where
  wellFounded = relMorph_Wfb_acc RelMorphNatPNat

--
-- Nz2 is not rational.
--

corollary : NotSquare Nz2
corollary = theorem Nz2 prime_Nz2
