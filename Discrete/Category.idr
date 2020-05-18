module Discrete.Category


public export
record Category where

  constructor MkCategory

  object : Type

  morphism : object -> object -> Type

  identity : (a : object) -> morphism a a

  compose : (a, b, c : object) -> (f : morphism a b) -> (g : morphism b c) -> morphism a c
  --- compose Int Int Int (Int -> Int) (Int -> Int)

  leftIdentity : (a, b : object) -> (f : morphism a b) -> compose a a b (identity a) f = f
  -- (return 1 >>= (\x => Just $ x + 1)) == f x
  -- id . g = g

  rightIdentity : (a, b : object) -> (f : morphism a b) -> compose a b b f (identity b) = f
  -- (Just 1 >>= return) == x
  -- f . id = f

  associativity : (a, b, c, d : object) -> (f : morphism a b) -> (g : morphism b c) -> (h : morphism c d)
    -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h


TypeMorphism : Type -> Type -> Type
TypeMorphism x y = x -> y


identity : (a : Type) -> TypeMorphism a a
identity a = id


compose : (a, b, c : Type) -> (f : TypeMorphism a b) -> (g : TypeMorphism b c) -> TypeMorphism a c
compose a b c f g = g . f


leftIdentity : (a, b : Type) -> (f : TypeMorphism a b) -> f . (identity a) = f
leftIdentity a b f = Refl


rightIdentity : (a, b : Type) -> (g : TypeMorphism a b) -> (identity b) . g = g
rightIdentity a b g = Refl


associativity : (a, b, c, d : Type) -> (f : TypeMorphism a b) -> (g : TypeMorphism b c) -> (h : TypeMorphism c d)
  -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
associativity a b c d f g h = Refl


typeAsCategory : Category
typeAsCategory = MkCategory
  Type
  TypeMorphism
  identity
  compose
  leftIdentity
  rightIdentity
  associativity
