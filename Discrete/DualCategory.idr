module DualCategory

import Category
import CFunctor


dualMorphism : (cat : Category) -> (a, b : object cat) -> Type
dualMorphism cat a b = morphism cat b a


dualCompose : (cat : Category) -> (a, b, c : object cat) -> (f : dualMorphism cat a b) -> (g : dualMorphism cat b c)
  -> dualMorphism cat a c
dualCompose cat a b c f g = (compose cat) c b a g f


dualLeftIdentity : (cat : Category) -> (a, b : object cat) -> (f : dualMorphism cat a b) -> dualCompose cat a a b (identity cat a) f = f
dualLeftIdentity cat a b f = rightIdentity cat b a f


dualRightIdentity : (cat : Category) -> (a, b : object cat) -> (f : dualMorphism cat a b) -> dualCompose cat a b b f (identity cat b) = f
dualRightIdentity cat a b f = leftIdentity cat b a f


dualAssociativity : (cat : Category) -> (a, b, c, d : object cat) -> (f : dualMorphism cat a b) -> (g : dualMorphism cat b c) -> (h : dualMorphism cat c d)
  -> dualCompose cat a b d f (dualCompose cat b c d g h) = dualCompose cat a c d (dualCompose cat a b c f g) h
dualAssociativity cat a b c d f g h = sym (associativity cat d c b a h g f)


dualCategory : (cat : Category) -> Category
dualCategory cat = MkCategory
  (object cat)
  (dualMorphism cat)
  (identity cat)
  (dualCompose cat)
  (dualLeftIdentity cat)
  (dualRightIdentity cat)
  (dualAssociativity cat)


doubleDualTo : (cat : Category) -> CFunctor (dualCategory (dualCategory cat)) cat
doubleDualTo cat = MkCFunctor
  id
  (\_, _ => id)
  (\_ => Refl)
  (\_, _, _, _, _ => Refl)


doubleDualFrom : (cat : Category) -> CFunctor cat (dualCategory (dualCategory cat))
doubleDualFrom cat = MkCFunctor
  id
  (\_, _ => id)
  (\_ => Refl)
  (\_, _, _, _, _ => Refl)
