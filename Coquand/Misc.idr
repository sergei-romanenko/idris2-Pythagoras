module Coquand.Misc

%default total

-- Implication reasoning

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
