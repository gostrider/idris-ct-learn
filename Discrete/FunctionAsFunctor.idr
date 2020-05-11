module Discrete.FunctionAsFunctor

import CFunctor
import DiscreteCategory


public export
functionMapMorphism : (f : a -> b) -> (x, y : a) -> DiscreteMorphism x y -> DiscreteMorphism (f x) (f y)
functionMapMorphism f x x Refl = Refl


public export
functionPreserveCompose : (f : a -> b)
  -> (x, y, z : a)
  -> (g : DiscreteMorphism x y) -> (h : DiscreteMorphism y z)
  -> functionMapMorphism f x z (discreteCompose x y z g h)
    = discreteCompose (f x) (f y) (f z) (functionMapMorphism f x y g) (functionMapMorphism f y z h)
functionPreserveCompose f x x x Refl Refl = Refl


public export
functionAsFunctor : (f : a -> b) -> CFunctor (discreteCategory a) (discreteCategory b)
functionAsFunctor f =
  MkCFunctor f (functionMapMorphism f) (\_ => Refl) (functionPreserveCompose f)
