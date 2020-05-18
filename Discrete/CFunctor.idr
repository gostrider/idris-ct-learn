module Discrete.CFunctor

import Category


public export
record CFunctor (cat1 : Category) (cat2 : Category) where

  constructor MkCFunctor

  mapObject : object cat1 -> object cat2

  mapMorphism : (a, b : object cat1) -> morphism cat1 a b -> morphism cat2 (mapObject a) (mapObject b)

  preserveIdentity : (a : object cat1)
    -> mapMorphism a a (identity cat1 a) = identity cat2 (mapObject a)

  preserveCompose : (a, b, c : object cat1) -> (f : morphism cat1 a b) -> (g : morphism cat1 b c)
    -> mapMorphism a c (compose cat1 a b c f g)
      = compose cat2 (mapObject a) (mapObject b) (mapObject c) (mapMorphism a b f) (mapMorphism b c g)

  -- preserveLeftIdentity : (a, b : object cat1)
  --   -> (f : morphism cat1 a b)
  --   -> mapMorphism a b (compose cat1 a a b (identity cat1 a) f) = mapMorphism a b f
  --
  -- preserveRightIdentity : (a, b: object cat1)
  --   -> (f : morphism cat1 a b)
  --   -> mapMorphism a b (compose cat1 a b b f (identity cat1 b)) = mapMorphism a b f
  --
  -- preserveAssociativity : (a, b, c, d : object cat1)
  --   -> (f : morphism cat1 a b) -> (g : morphism cat1 b c) -> (h : morphism cat1 c d)
  --   -> mapMorphism a d (compose cat1 a b d f (compose cat1 b c d g h))
  --     = mapMorphism a d (compose cat1 a c d (compose cat1 a b c f g) h)
