module Hierarchy
import Effects
import Util.DepUnion
%access public export

Hierarchy : Type
Hierarchy = Nat -> List Type

level : Hierarchy -> Nat -> List Type
level h Z = h Z
level h (S n) =  h (S n) ++ level h n

infixr 10 #.
(#.): Hierarchy -> Nat -> Type
(#.) h c = DepUnion (level h c)

Member : Hierarchy -> Type
Member h = (n : Nat ** h#.n)

using ( h : Hierarchy)
  cumulative1: (level h n) `SubList` (level h (S n))
  cumulative1 = dropPrefix (subListId _ ) 

  cumulative2 : (h#.n) -> (h#.(m+n))
  cumulative2 {m = Z} a = a
  cumulative2 {m = S k} a = Shuffle {left = cumulative1}  (cumulative2 a)

  lteHelper : a+x `LTE` a+y -> x `LTE` y
  lteHelper {a=Z} = id
  lteHelper {a = S i} = lteHelper . fromLteSucc

  cumulative3 : (n,m:Nat) -> .(n `LTE` m) -> h#.n -> h#.m
  cumulative3 n m a t with (cmp n m)
    cumulative3 x x a t | CmpEQ = t
    cumulative3 n (n+S i) a t | CmpLT i = rewrite plusCommutative n (S i) in cumulative2 {n=n}{m=S i} t
    cumulative3 (m+S i) m a t | CmpGT i =
      let a' :(m + S i `LTE` m + 0) = (rewrite plusZeroRightNeutral m in a) in
        absurd $ lteHelper a'

  liftComplexity : (Functor f, Foldable f) => (f (Member h)) -> (n : Nat ** f (h#.n))
  liftComplexity l = 
    let complexity = foldr maximum 0 (map fst l) in
    ( _ ** map (liftTerm complexity) l) where
       liftTerm : (c : Nat) -> Member h -> h#.c
       liftTerm c (n ** term) = 
         let lte : (n `LTE` c) = believe_me () in
         cumulative3 n c lte term

