module Discrete.ConstantFunctor

import CFunctor
import Category

%access public export
%default total

-- constant functor in haskell
-- fmap _ (Const r) = Const r

Delta : (cat1, cat2 : Category) -> (n : object cat2) -> CFunctor cat1 cat2
Delta cat1 cat2 n = MkCFunctor
  (\a => n)
  (\a, b, f => identity cat2 n)
  (\a => Refl)
  (\a, b, c, f, g => sym (leftIdentity cat2 n n (identity cat2 n)))
