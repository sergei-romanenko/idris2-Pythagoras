module Coquand.Cancellative

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

%default total

infixl 7 <.>

-- Cancellative Abelian Monoid

public export
interface CAMonoid ty where
  constructor MkCancellativeAbelianMonoid

  (<.>) : ty -> ty -> ty
  neutral : ty

  opIsAssociative : (l, c, r : ty) ->
    l <.> (c <.> r) = (l <.> c) <.> r

  opIsCommutative : (l, r : ty) ->
    l <.> r = r <.> l

  neutralLeft : (x : ty) ->
    neutral <.> x = x

  cancelLeft : (z, x, y : ty) ->
    z <.> x = z <.> y -> x = y
