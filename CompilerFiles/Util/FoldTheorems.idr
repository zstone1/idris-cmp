module FoldTheorems
import Syntax.PreorderReasoning
import Data.So
import Prelude.Maybe
import Projective
import Data.Vect
import Decidable.Order  
%default total
%access export
|||A proof that given three element, f associates over them.
Associates: (f : t -> t -> t) -> Type 
Associates {t} f = (t1:t) -> (t2:t) -> (t3:t) -> (f ( f t1 t2) t3 = f t1 (f t2 t3))

|||Lifts to a proof that partial application of f associates. 
AssociatesExtend : Associates f -> (a:t) -> (x:t) -> ((\e => f (f a x) e) = (\e => f a (f x e)))
--Idris does not know about "extentionality" of functions. So we use must use beieve_me.
AssociatesExtend _ = believe_me () 

|||A proof for that all x, f x = x
IdenQ : (f : t -> t) -> Type
IdenQ {t} f = (tn: t) -> (f tn = tn)

|||Lifts to a proof that f is the identity.
IdenExtend : IdenQ f -> (f = Basics.id)
--Idris does not know about "extentionality" of functions. So we must use believe_me.
IdenExtend _ = believe_me ()

public export
qed : (x : Nat) -> LTE x x
qed x = lteRefl

public export
step : (x:Nat) -> (LTE x y) -> (LTE y z) -> (LTE x z)
step x p1 p2 = lteTransitive p1 p2


|||Given an associate folding function, this proves that 
|||we can pull of the first element in the obvious way.
FoldAssocCons: Associates f ->
               (a:t) -> 
               (as:Vect n t) -> 
               f a (foldr f s as) = foldr f s (a :: as)  
FoldAssocCons _ _ [] = Refl
FoldAssocCons {f} {s} prf a (x :: xs) =
    let rec = sym $ FoldAssocCons {f}{s} prf x xs in
    let axsAssoc = sym$ prf a x (foldr f s xs) in
  (f a (foldr f s (x::xs)))   ={ rewrite rec in axsAssoc  }=
  (f (f a x) (foldr f s xs))  ={ FoldAssocCons {f}{s} prf (f a x) xs }=
    let extends = (AssociatesExtend prf a x) in 
  (foldr f s ((f a x) :: xs)) ={ cong {f=\e => foldrImpl f s e xs} extends }=
  (foldr f s (a :: x :: xs)) QED

|||Given an associative function, folding that function
|||distributes over concatonation.
FoldAssocConcat : Associates f ->
                  IdenQ (f s) -> 
                  (as : Vect n t) ->
                  (bs : Vect m t) ->
                  f (foldr f s as) (foldr f s bs) = foldr f s (as ++ bs) 
FoldAssocConcat {f} {s} prf idprf [] bs = 
  rewrite idprf (foldr f s bs) in Refl
FoldAssocConcat {f} {s} prf idprf (a :: as) bs = 
    let consAAs = sym$ FoldAssocCons{f}{s} prf a as in
    let assocAAsBs = prf a (foldr f s as) (foldr f s bs) in
  (f (foldr f s (a::as)) (foldr f s bs))  ={ rewrite consAAs in assocAAsBs }=
  (f a (f (foldr f s as) (foldr f s bs))) ={ cong $ FoldAssocConcat {f}{s} prf idprf as bs }=
  (f a (foldr f s (as ++ bs)))            ={ FoldAssocCons {f}{s} prf a (as++bs) }=
  (foldr f s (a :: (as++bs)))             QED


SumAssociates : (as : Vect n Nat) -> (bs: Vect m Nat) -> (sum as + sum bs = sum (as ++ bs))
SumAssociates as bs = 
  let assoc = \a,b,c => sym $ plusAssociative a b c in
      FoldAssocConcat {f=\a,b => plus a b} assoc plusZeroLeftNeutral as bs

MapAppendDistributes : (f: t->u) -> (as : Vect n t) -> (bs : Vect m t) -> (map f as) ++ (map f bs) = map f (as ++ bs)
MapAppendDistributes f [] bs = Refl
MapAppendDistributes f (x :: xs) bs =  rewrite MapAppendDistributes f xs bs in Refl


syntax [from] "=[" [prf] "]=" [to] = (from) ={ (|
                    rewrite prf in  Refl,
                    rewrite prf in lteRefl,
                    replace prf from
                 |) }= (to)

MergeEqualities : {x,y,a,b:t} -> (f: t->t->u) -> (x = y) -> (a = b) -> (f x a) = (f y b)
MergeEqualities {x}{y}{a}{b} f xy ab =
  (f x a) =[ ab ]=
  (f x b) =[ xy ]=
  (f y b) QED


elemSingleton : Elem x [y] ->x=y
elemSingleton Here = Refl
elemSingleton (There later) = absurd later

NotElemLemma1 : Elem inList as -> Not $ Elem outList as -> (inList = outList) -> Void
NotElemLemma1 isIn isOut contra = isOut $ rewrite sym contra in isIn 

NotElemLemma2 : Not $ Elem a (x::xs) -> Elem a xs -> Void
NotElemLemma2 {a} {xs = a :: xs'} contr Here = contr $ There Here
NotElemLemma2 {xs = y :: xs'} contr (There later) = contr $ There( There( later))


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


minusPlusCancel : (k : Nat) -> (n : Nat) -> {auto q: LTE n k} ->(k = (n +(k - n)))
minusPlusCancel k Z = rewrite minusZeroRight k in Refl
minusPlusCancel Z (S j) {q} = absurd q
minusPlusCancel (S k) (S j) {q} = cong $ minusPlusCancel k j {q = fromLteSucc q}

lteMinus : (m:Nat) ->(n :Nat) -> {auto q1 : LTE 1 n} -> {auto q2 : LTE n m} -> LT (m - n) m
lteMinus _ Z {q1} = absurd q1
lteMinus Z (S k) {q2} = absurd q2
lteMinus (S j) (S Z) = rewrite minusZeroRight j in (LTESucc lteRefl )
lteMinus (S k) (S(S j)) {q2} = let LTESucc f = q2 in
                                   LTESucc $ lteSuccLeft $ (lteMinus k (S j))

Uninhabited (IsJust Nothing) where
  uninhabited ItIsJust impossible

getVal : (x : Maybe t) -> {auto prf : IsJust x} -> t
getVal {prf} Nothing = absurd prf
getVal {prf} (Just x) = x

justMapMaybe : (f :t -> Maybe u) -> 
               (l : Vect k t) ->
               Elem x l ->
               IsJust (f x) -> 
               Elem (getVal $ f x) (snd $ mapMaybe f l)
justMapMaybe f [] elem p = absurd elem
justMapMaybe f (a :: as) Here isJust with (mapMaybe f as)
  | (len ** list) with (f a) 
    | Nothing = absurd isJust
    | Just y = Here
justMapMaybe {x} f (a :: as) (There later) isJust with ( justMapMaybe f as later isJust)
 | rec with (mapMaybe f as) proof p1
   | (len ** list) with ( f a )
      | Nothing = rec
      | Just y = There rec
  
filterForward : (Elem x l) -> (So (f x)) -> Elem x (snd $ filter f l)
filterForward {l=[]} elem _ = absurd elem 
filterForward {x=w} {l= w :: ws} {f} Here success with (filter f ws)
  | (l ** rest) with (f w)
    | False = absurd success 
    | True = Here
filterForward {x} {l=w :: ws} {f} (There later) success with (filterForward {x} {l=ws} {f} later success)
  | rec with (filter f ws)
    | (l ** rest) with (f w)
       | False = rec
       | True = There rec

filterBackwards : (l: Vect k t) -> Elem x (snd $ filter f l) -> (So (f x), Elem x l)
filterBackwards [] elem = absurd elem 
filterBackwards {x} {f} (w :: ws) elem with (filter f ws) proof p1
  |( _ ** rest) with (f w) proof p2
    filterBackwards {x}{f} (w::ws) elem | (_ ** rest) | False = 
      let (o, elemRec) = filterBackwards {x}{f} ws (rewrite sym p1 in elem) in
          (o, There elemRec)
 -- This line is the magic where idris has deduced out that the heads of both lists agree 
    filterBackwards {x} {f} (x :: ws) Here | (_ ** rest) | True = 
      (rewrite sym p2 in Oh, Here)
    filterBackwards {x} {f} (w :: ws) (There later) | (_ ** rest) | True =
      let (o, elemRec) = filterBackwards {x} {f} ws (rewrite sym p1 in later) in 
          (o, There elemRec)

implementation Uninhabited (False = True) where
  uninhabited Refl impossible






















