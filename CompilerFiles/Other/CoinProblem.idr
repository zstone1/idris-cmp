module CoinProblem
import Data.Vect
import Util.VectTheorems

data Denoms : {k:Nat} -> Type where
  MkDenoms : (d:Vect n Nat) -> {auto e: Elem 1 d} -> Denoms {k=n}

getDenoms : {k:Nat} -> Denoms {k=k}-> Vect k Nat
getDenoms (MkDenoms v) = v

data Coin : Denoms -> Type where
  MkCoin : (a:Nat) -> {p : Denoms} -> {auto q : Elem a (getDenoms p)} -> Coin p

CSum: Vect n (Coin d) -> Nat
CSum coins = sum (map getVal coins) where getVal (MkCoin a) = a


--  let q1:(CSum [a] + CSum as + CSum bs = _) = cong{f = \e => e+CSum bs} p1 in
-- let l1 = plusAssociative (CSum [a]) (CSum as) (CSum bs) in 
-- let q2:(CSum [a] + (CSum as + CSum bs) = _ ) = rewrite l1 in q1 in
-- let l2:(CSum [a] + (CSum as + CSum bs) = CSum [a] + CSum (as ++ bs)) =  cong {f = \e => CSum [a] + e} p2 in
--   ?asdf 

data Change : {d : Denoms} -> (amt: Nat) -> Type where
  MkChng : (cs : Vect n (Coin d) ** amt = CSum cs) -> Change {d=d} amt
--  
--

MergeChange : (c1 : Change n) -> (c2 : Change m) -> Change (n + m)

GiveChange : (d : Denoms) -> (amt: Nat) -> Change {d=d} amt
GiveChange _ Z = MkChng ([] ** Refl)
GiveChange (MkDenoms d) (S k) with (isElem (S k) d) 
  | Yes prf = let c = MkCoin (S k) {p = MkDenoms d} {q = prf} in 
              let p1 : (plus (S k) 0 = CSum [c]) = Refl in
              let p2 : ((S k) = CSum [c]) = (rewrite sym $ plusZeroRightNeutral (S k) in p1) in 
                MkChng ([c] ** p2)
  | No contr = ?foo

SumDist : (a: Vect n Nat) -> (b: Vect m Nat) -> 
          (sum a) + (sum b) = sum (a ++ b)
SumDist [] b = Refl
SumDist (x :: xs) b = 
  let sumCons:(sum [x] + sum[xs] = sum (x Data.Vect.:: xs)) = ?lem_1 in
      ?SumDist_rhs_2
 

--CSumDist : (as:Vect n (Coin d)) -> (bs : Vect m (Coin d)) ->
--              (CSum as) + (CSum bs) = CSum ( as ++ bs)
--CSumDist [] bs = Refl
--CSumDist (a :: as) bs = 
--  let p1 = CSumDist [a] as in 
--  let p2 = CSumDist as bs in
--  let p3 = CSumDist [a] (as++bs)in
--  let q1 = cong{f = \e => e+CSum bs} p1 in
--  let l1 = plusAssociative (CSum [a]) (CSum as) (CSum bs) in 
--  let q2 = rewrite l1 in q1 in
--  let q3:(CSum [a] + CSum(as ++ bs) = CSum (a::as) + CSum bs) = rewrite p2 in q1 in  
--    ?a_12
