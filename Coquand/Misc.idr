module Coquand.Misc

import Control.Relation
import Control.WellFounded

%default total

--
-- Implication reasoning
--

prefix 1  |~~
infixl 0  ~~>
infix  1  ...
infixr 0 |>

-- Implication is a preorder relation...

public export
(|~~) : (0 a : Type) -> (a -> a)
(|~~) a = id

public export
(~~>) : (p : a -> b) -> (q : b -> c) -> (a -> c)
(~~>) p q = q . p

public export
(...) : (0 b : Type) -> (a -> b) -> (a -> b)
(...) b xy = xy

public export
(|>) : forall a, b. (x : a) -> (f : a -> b) -> b
(|>) x f = f x

--
-- RelMorph & Well-founded
--

public export
record RelMorph a b (relA : Rel a) (relB : Rel b) where
  constructor MkRelMorph
  toB : a -> b
  relMorph : (x, y : _) -> relA x y -> relB (toB x) (toB y)

relMorph_acc : (rm : RelMorph a b relA relB) ->
  (x : a) -> Accessible relB (toB rm x) -> Accessible relA x
relMorph_acc rm x (Access rec) =
  Access $ \y, ra_yx => relMorph_acc rm y (rec (toB rm y) (relMorph rm y x ra_yx))

public export
relMorph_Wfb_acc : (rm : RelMorph a b relA relB) -> WellFounded b relB =>
  (x : a) -> Accessible relA x
relMorph_Wfb_acc rm x = relMorph_acc rm x (wellFounded (toB rm x))
