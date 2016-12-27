module Projective
import Decidable.Order
import Prelude.Basics
import Data.So
%access export

public export
interface Preorder t po => TotalPreorder t (po : t -> t -> Type) where
  porder : (a : t) -> (b : t) -> Either (po a b) (po b a)

public export
[inht] Ordered t to => TotalPreorder t to where
  porder = order

public export
interface Functor f => Projective (f:Type ->Type) where
  proj : {a:Type} -> f a -> a
  commutative : (x:f a) -> (g: a -> b) -> (proj . map g) x = (g . proj) x

{-     map g
    f A --> f B
    |        |
proj|        | proj
    v        v
    A -----> B
        g
---}

public export
Functor (Pair a) where
  map f (x,y) = (x,f y)

public export
Projective (Pair a) where
  proj = snd
  commutative (x,y) g = Refl

public export
data ProjLifted : (f: Type -> Type) -> (po: t->t->Type) -> f t -> f t -> Type where
  LiftToProj : Projective f => (po: t -> t -> Type) -> po (proj x) (proj y) -> ProjLifted f po x y

(Preorder t po, Projective f) => Preorder (f t) (ProjLifted f po)  where
  reflexive a = LiftToProj {f} po (reflexive $ proj a) 
  transitive a b c (LiftToProj _ x) (LiftToProj _ y) = 
        LiftToProj {f} po (transitive (proj a) (proj b) (proj c ) x y)


[pj] (TotalPreorder t po, Projective f) => TotalPreorder (f t) (ProjLifted f po) where
  porder x y  with (porder {t} {po} (proj x) (proj y))
    | Left xy = Left $ LiftToProj {f} po xy
    | Right yx = Right $ LiftToProj {f} po yx




