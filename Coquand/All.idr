module Coquand.All

-- Some general stuff
import Coquand.Misc

-- The definition of cancellative abelian monoid.
import Coquand.Cancellative

-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be a square of rational in cancellative
-- abelian monoid.
import Coquand.Theorem

-- Some properties of ℕ
import Coquand.TwoDivides

-- A set of natural numbers without zero.
import Coquand.NatPlus

-- The set of the natural numbers without zero and with multiplication
-- forms a cancellative abelian modoid.
-- Thus, the square root of two is irrational.
import Coquand.Corollary

----
---- Miscellanea
----

-- There is no m and n such that
--   n ≢ 0 and m * m ≡ 2 * (n * n)
-- Hence, sqrt 2 is irrational.

-- The proof in Coq has been originally written by Pierre Corbineau
-- http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v

-- import Corbineau.Sqrt2

-- 2 is prime.
-- Originally written by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

-- import Danielsson.2IsPrime
