module Discrete.ExtensionalCategory


record ExtensionalTypeMorphism (a : Type) (b : Type) where
  constructor MkExtensionalTypeMorphism
  func : a -> b


postulate
funExt : {f, g : ExtensionalTypeMorphism a b} -> ((x : a) -> func f x = func g x) -> f = g
