module MinimumExt
import PreorderReasoningExt
import Data.So
import MaybeExt
import Projective
import VectExt
import Decidable.Order  
%access export 

public export
minimum : (TotalPreorder t po) => t -> t -> t
minimum {po} x y with (porder {po} x y)
    | Left _ = x
    | Right _ = y

minimumLemma1 : Ordered t po => (f . Prelude.Basics.fst) (minimum @{pj} {po=ProjLifted (Pair u) po} (a, f a) (b, f b)) = minimum @{inht} {po} (f a) (f b)
minimumLemma1 {u} {f} {a} {b} {po} with (porder {po=ProjLifted (Pair u) po} (a, f a) (b, f b))
  | (Left (LiftToProj po p1)) with (porder {po} (f a) (f b))
    |Left p2 = Refl
    |Right p2= antisymmetric (f a) (f b) p1 p2
  | (Right (LiftToProj po p1)) with (porder {po} (f a) (f b))
    |Left p2 = antisymmetric (f b) (f a) p1 p2
    |Right p2 = Refl

public export
minElem : TotalPreorder t po => Vect (S k) t -> t
minElem (x :: []) = x
minElem {po} (x :: x'::xs)  = minimum {po} x (minElem {po} (x'::xs)) 

minElemLemma1 : TotalPreorder t po => (x:t) -> (xs : Vect k t) -> (po (minElem {po} (x::xs)) x)
minElemLemma1 x [] = reflexive x
minElemLemma1 {po} x (y :: xs) with (porder {po} x (minElem {po} (y::xs))) 
  |Left p = reflexive x
  |Right p2 = p2


minElemLemma2 : TotalPreorder t po =>  (x:t) -> (xs: Vect (S k) t) -> po (minElem {po}(x::xs)) (minElem {po} xs)
minElemLemma2 {po} {k=Z} x (x' :: []) with (porder {po} x x') 
  |Left p = p
  |Right p = reflexive x'
minElemLemma2 {po} {k=S j} x (x' :: xs) with (porder {po} x (minElem {po} (x'::xs)))
  |Left p = p 
  |Right p = reflexive (minElem {po} (x'::xs))

minElemPrf : TotalPreorder t po => (l: Vect (S k) t) -> ( Elem x l ) -> po (minElem {po} l) x
minElemPrf {x = y} (y :: []) Here = reflexive y
minElemPrf {x = x} (y :: []) (There later) = absurd later
minElemPrf {x = y} {po} (y :: y' :: ys) Here with (porder {po} y (minElem {po} (y'::ys))) 
  |Left _ = reflexive y
  |Right p = p
minElemPrf {x} {po} (y :: y' :: ys) (There later) with (porder {po} y (minElem {po} (y'::ys)))
  |Left p = let rec = minElemPrf {x} {po} (y'::ys) later in 
               transitive y (minElem {po} (y'::ys)) x p rec 
  |Right p = minElemPrf {x}{po} (y'::ys) later

mapPair : (f:u-> t) -> (x:u) -> (u,t)
mapPair f x = (x,f x)

minElemBy : TotalPreorder t po => (u -> t) -> Vect (S k) u -> u
minElemBy {u} {t} {po} f xs = Basics.fst $ minElem @{pj} {po=ProjLifted (Pair u) po} (map (mapPair f) xs)

minElemByLemma1 : TotalPreorder t po => (f: u -> t) -> (l:Vect (S k) u) -> (Elem x l) -> po ( minElem {po} (map f l)) (f x) 
minElemByLemma1 {po} f xs elem = minElemPrf {po} (map f xs) (mapElem elem)

private
minElemBySwap : TotalPreorder t po => (f : u -> t) -> 
                                        (Basics.snd $ minElem @{pj} {po = ProjLifted (Pair u) po} (map (mapPair f) l)) = (f$Basics.fst$minElem {po = ProjLifted (Pair u) po} (map (mapPair f) l))

minElemBySwap {po} {l=x::[]} f = Refl
minElemBySwap {po} {l=x::x'::xs} f with (porder {po=ProjLifted (Pair u) po}(x, f x) (minElem {po = ProjLifted (Pair u) po} (map (mapPair f) (x'::xs))))
  | Left l = Refl
  | Right r = minElemBySwap {po} {l=x'::xs} f 

minElemByLemma2 : Ordered t po => (f:u -> t) -> (l: Vect (S k) u) -> (minElem @{inht} {po} (map f l)) = f (minElemBy {po} f l)
minElemByLemma2 f (x :: [])= Refl
minElemByLemma2 {inht} {u} {po} {t} f (x :: x' :: xs) with (porder {po} @{inht} (f x) (minElem {po} (map f (x'::xs))))
  |Left l1 with (porder @{pj} {po=ProjLifted(Pair u) po} (x, f x) (minElem {po = ProjLifted (Pair u) po}@{pj} (map (mapPair f) (x'::xs))))
    |Left l2 = Refl
    |Right (LiftToProj po l2) with (minElemByLemma2 {inht} f (x'::xs) {po})
      | rec = let p1 = replace rec l1 in
              let p2 = minElemBySwap {po} {l=(x'::xs)} f in
              let p3 = replace {P = flip po (f x)} (p2) l2 in
                  antisymmetric (f x) (f $ fst $ minElem{po = ProjLifted (Pair u) po} @{pj} (map (mapPair f) (x'::xs))) p1 p3
  |Right r1 with (porder @{pj} {po=ProjLifted(Pair u) po} (x, f x) (minElem {po = ProjLifted (Pair u) po}@{pj} (map (mapPair f) (x'::xs))))
    |Right r2 = minElemByLemma2 {inht} f (x'::xs) {po}
    |Left (LiftToProj po r2) with (minElemByLemma2 {inht} f (x'::xs) {po})
      |rec = let p1 = minElemBySwap {po} {l=(x'::xs)} f in
             let p2 = replace p1 {P = po (f x)} r2 in
             let p3 = replace {P=po (f x)} (sym rec) p2 in
                 antisymmetric {po} (minElem {po} (map f (x'::xs))) (f x) r1 p3

