module FoldTheorems
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

|||Given an associate folding function, this proves that 
|||we can pull of the first element in the obvious way.
FoldAssocCons: Associates f ->
               (a:t) -> 
               (as:Vect n t) -> 
               f a (foldr f s as) = foldr f s (a :: as)  
FoldAssocCons _ _ [] = Refl
FoldAssocCons {f} {s} prf a (x :: xs) =
  let foldxs = foldr f s xs in 
  let foldxxs = foldr f s (x::xs) in 
  let l1 = prf a x foldxs in
  let rec = FoldAssocCons {f=f}{s=s} prf x xs in
  let l2 : (f a foldxxs = _ ) = rewrite sym rec in sym l1 in
  let rec2 = FoldAssocCons {f=f} {s=s} prf (f a x) xs in
  let l3 : ( f a foldxxs = foldr f s ((f a x) :: xs)) = rewrite sym rec2 in l2 in
  -- I know if is associative
  let fassoc : ((\x1 => f (f a x) x1) = (\x1 => f a (f x x1))) = AssociatesExtend prf a x in
  let l4 : ( _ = foldr f s (a :: x :: xs)) = rewrite sym fassoc in Refl in
    rewrite sym l4 in l3

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
  let foldas = (foldr f s as) in
  let foldaas = (foldr f s (a::as)) in
  let foldbs = (foldr f s bs) in
  let l1 = FoldAssocCons {s=s} {f=f} prf a as in
  let l2 = prf a foldas foldbs in
  let t3 : (f foldaas foldbs = f a (f foldas foldbs)) = (rewrite sym l1 in l2) in
  let rec = FoldAssocConcat {f=f} {s=s} prf idprf as bs in
  let t4 : (f foldaas foldbs = f a (foldr f s (as ++ bs))) = rewrite sym rec in t3 in
  let l5 = FoldAssocCons {s=s} {f=f} prf a (as ++ bs) in
  let t5 : (f foldaas foldbs = foldr f s (a :: (as ++ bs))) = rewrite sym l5 in t4 in
    t5 

SumAssociates : (as : Vect n Nat) -> (bs: Vect m Nat) -> (sum as + sum bs = sum (as ++ bs))
SumAssociates as bs = 
  let assoc = \a,b,c => sym $ plusAssociative a b c in
      FoldAssocConcat {f=\a,b => plus a b}{s=Z} assoc plusZeroLeftNeutral as bs

MapAppendDistributes : (f: t->u) -> (as : Vect n t) -> (bs : Vect m t) -> (map f as) ++ (map f bs) = map f (as ++ bs)
MapAppendDistributes f [] bs = Refl
MapAppendDistributes f (x :: xs) bs = 
  let induct = MapAppendDistributes f xs bs in
    rewrite induct in Refl 

MergeEqualities : {x,y,a,b:t} -> {f: t->t->u} -> (x = y) -> (a = b) -> (f x a) = (f y b)
MergeEqualities xy ab = rewrite xy in rewrite ab in Refl


NotElemLemma1 : Elem inList as -> Not $ Elem outList as -> (inList = outList) -> Void
NotElemLemma1 isIn isOut contra = isOut $ rewrite sym contra in isIn 

NotElemLemma2 : Not $ Elem a (x::xs) -> Elem a xs -> Void
NotElemLemma2 {a} {xs = a :: xs'} contr Here = contr $ There Here
NotElemLemma2 {xs = y :: xs'} contr (There later) = contr $ There( There( later))


minimum : (TotalPreorder t po) => t -> t -> t
minimum {po} x y with (porder {po} x y)
    | Left _ = x
    | Right _ = y


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
--
--
minElemBy : TotalPreorder t po => (u -> t) -> Vect (S k) u -> u
minElemBy {u} {t} {po} f xs = let pairs = map (\e => (e, f e)) xs in 
                                 fst $ minElem {po=ProjLifted (Pair u) po} pairs

minElemByLemma1 : TotalPreorder t po => (f: u -> t) -> (l:Vect (S k) u) -> (Elem x l) -> po ( minElem {po} (map f l)) (f x) 
minElemByLemma1 {po} f xs elem = minElemPrf {po} (map f xs) (mapElem elem)


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













