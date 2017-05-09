module Quotient
import Decidable.Order
import Util.PreorderReasoningExt
import Util.NatExt

data EqClass : {eq : t->t->Type} -> t -> Type where
  MkEqClass : Equivalence t eq => u `eq` v -> EqClass {eq} v

eqClassLemma1 : Equivalence t eq => x`eq`y -> EqClass {eq} x -> EqClass {eq} y
eqClassLemma1 xEQy (MkEqClass {u} uEQx) = MkEqClass {u} $ transitive u _ _ uEQx xEQy

data Quotient : (t:Type) -> (t -> t -> Type) -> Type where
  MkCl : Equivalence t eq => {x:t} -> EqClass {eq} x -> Quotient t eq

--data PickRepresentative : Quotient t eq -> Type where
--  Pick : x `eq` y -> 

{-
        f
      t -> u
      |    ^
MkCl  |   /
      |  / qinduce . f
      V /
      q
-}
--parameters (q:Quotient t eq)

--  respectsEq : (t -> u) -> Type 
--  respectsEq f = (x,y:t) ->  x `eq` y -> f x = f y



--  qinduce : (f: t -> u) -> {auto pf : respectsEq f} -> (Quotient t eq -> u)

 -- prf : {f:t -> u} -> f x = (qinduce . f) (MkCl x)

