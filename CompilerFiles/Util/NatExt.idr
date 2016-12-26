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
{-
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
  -}  

--toHex : (x:Nat) -> (Base 16 x)








