module FoldExt
import Util.PreorderReasoningExt
import Util.VectExt
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

elemSingleton : Elem x [y] ->x=y
elemSingleton Here = Refl
elemSingleton (There later) = absurd later

NotElemLemma1 : Elem inList as -> Not $ Elem outList as -> (inList = outList) -> Void
NotElemLemma1 isIn isOut contra = isOut $ rewrite sym contra in isIn 

NotElemLemma2 : Not $ Elem a (x::xs) -> Elem a xs -> Void
NotElemLemma2 {a} {xs = a :: xs'} contr Here = contr $ There Here
NotElemLemma2 {xs = y :: xs'} contr (There later) = contr $ There( There( later))

implementation Uninhabited (False = True) where
  uninhabited Refl impossible






















