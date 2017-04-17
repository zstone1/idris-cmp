module Lens

Lens: Functor f => (s,t,a,b : Type) -> Type 
Lens {f} s t a b = (s -> f t) -> (a -> f b)

Lens': Functor f => (a, b: Type) -> Type 
Lens' {f} a b = Lens {f} a a b b


