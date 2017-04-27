module NatExt
import Util.PreorderReasoningExt
import Data.Vect
%access export

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

data NonZero : Nat -> Type where
  IsNotZero : NonZero (S k)

data GTE2 : Nat -> Type where
  MkGTE2 : GTE2 (S(S k))


hint1 : {n:Nat} -> n*0+k = k
hint1 {n} = rewrite multZeroRightZero n in Refl

lteOrGte : (a:Nat) -> (b:Nat) -> Either (a `LTE` b) (b `LTE` a)
lteOrGte Z b = Left LTEZero
lteOrGte a Z = Right LTEZero
lteOrGte (S a') (S b') with (lteOrGte a' b')
  | Left p = Left $ LTESucc p
  | Right p = Right $ LTESucc p

natToFin' : (x:Nat) -> (n:Nat) -> .(S x `LTE` n) -> Fin n
natToFin' _ Z p = absurd p
natToFin' Z (S k) p = FZ
natToFin' (S x) (S n) p = FS (natToFin' x n (fromLteSucc p))

natToFinToNat : finToNat (natToFin' x n l) = x
natToFinToNat {x = Z} {n=S k} = Refl
natToFinToNat {x = S x} {n = S n} {l = LTESucc l} with (natToFinToNat {x}{n}{l})
 | p = cong p

data CmpNat2 : Nat -> Nat -> Type where
  CmpGT2 : (x : _) -> CmpNat2 (y + S x) y
  CmpLTE2 : (x: _) -> CmpNat2 y (y + x )

cmp2 : (n:Nat) -> (m:Nat) -> CmpNat2 n m
cmp2 n m with (cmp n m)
  cmp2 n (n + S i) | CmpLT i = CmpLTE2 (S i)
  cmp2 (m + S i) m | CmpGT i = CmpGT2 i
  cmp2 n n | CmpEQ = replace (plusZeroRightNeutral n) (CmpLTE2 Z)

data Divide : Nat -> Nat -> Type where
  Quotient : (q:Nat) -> (r:Fin d) -> Divide d (d*q + finToNat r)

divideBy : (d:Nat) -> {auto prf : NonZero d} -> (n:Nat) -> Divide d n
divideBy {prf} d n with (cmp2 d n)
  divideBy (n+(S i)) n | CmpGT2 i = 
    let lte : (S n `LTE` n+S i) = rewrite sym $ plusSuccRightSucc n i in lteAddRight {m=i} (S n) in
    let quo1 = Quotient 0 (natToFin' n (n+S i) lte) in 
    let quo2 = replace hint1 quo1 in
    let quo3 = replace natToFinToNat quo2 in
        quo3
        
  --Assert total because d is non zero, so  i < (d+i) 
  divideBy d (d+i) | (CmpLTE2 i) with (assert_total (divideBy d i))
   divideBy d (d + (d*q + finToNat r)) | _ | (Quotient q r) =
     let quo1 : (Divide d (d*(S q) + finToNat r)) = Quotient (S q) r in  
     let quo2 : (Divide d ((d + d*q) + finToNat r )) = rewrite sym ( multRightSuccPlus d q) in quo1 in
     let quo3 : (Divide d (d + (d*q + finToNat r))) =  replace {P = Divide d} (sym (plusAssociative d (d*q) (finToNat r))) quo2 in 
         quo3
{-
fromCoefficients : Foldable f => (base: Nat) -> f (Fin base) -> Nat
fromCoefficients b l = fst $ foldr agg (Z,S Z) l where
  agg nextCoef (val, mult) = (val + (b * finToNat nextCoef), mult * b)


data BaseNView : (b:Nat) -> (n:Nat) -> Type where
  Coeffs : (l: List (Fin b)) -> BaseNView b (fromCoefficients b l)


toBase : (b:Nat) -> (n:Nat) -> BaseNView b n
toBase 

|||given the coefficents of the base n expansion, produces the value of the number
|||along with a helpful helpful statement about well-foundedness
fromBase : (Vect k (Fin base)) -> (n:Nat ** LTE n (power base (S k)))
fromBase {k=Z} [] = (0 ** LTEZero)
fromBase {k=S k'} (x::xs) {base} = 
  let (n' ** q') = fromBase xs in
  let asNat = finToNat x in
  let new = asNat * (pow base k') in
  let prf : (LTE (n'+new) (power base (2+k'))) = ?base_lte in
      (n'+new ** prf)

data Base : Nat -> Nat -> Type where
  AsBase : (coefs: Vect k (Fin n)) -> Base n (fst $ fromBase coefs)


toBaseN : {auto q: GTE2 b} -> (x:Nat) -> Base b x
toBaseN Z = AsBase []
toBaseN {b = S(S b')} {q=MkGTE2} (S k) with (toBaseN {b=S(S b')} k)
  toBaseN _ | AsBase [] = AsBase [FS FZ]
  toBaseN _ | AsBase (c::cs) = ?l1
  

--toHex : (x:Nat) -> (Base 16 x)

-}






