module CoinProblem
import Data.Vect
import FoldTheorems
%default total
record CurrencyConstraints (d : Vect k Nat) where
  constructor ValidateCurrency
  hasOne : Elem 1 d

Currency : {k:Nat} -> Type
Currency {k}= (d : Vect k Nat ** CurrencyConstraints {k=k} d) 

MkCurrency : (d : Vect k Nat) -> {auto q : Elem 1 d} -> Currency {k=k}
MkCurrency d {q} = (d ** ValidateCurrency q)

getDenoms : Currency {k=k} -> Vect k Nat
getDenoms x = fst x

getConstraints : (cur : Currency {k=k}) -> CurrencyConstraints (getDenoms cur)
getConstraints = snd

record CoinConstraints (n:Nat) (cur:Currency {k=k}) where
  constructor ValidateCoin
  isDenom : Elem n (getDenoms cur) 

Coin : Currency -> Type
Coin cur = (n : Nat ** CoinConstraints n cur)

getVal : Coin d -> Nat
getVal = fst

MkCoin : (n:Nat) -> (cur : Currency) -> {auto q : Elem n (getDenoms cur)} -> Coin cur
MkCoin {q} n cur = (n ** ValidateCoin q)

cSum : Vect n (Coin d) -> Nat
cSum coins = sum (map getVal coins) 

|||Proof that cSum distributes like sum.
CSumDistr : (as : Vect n (Coin d)) -> (bs : Vect m (Coin d)) -> cSum as + cSum bs = cSum (as ++ bs)
CSumDistr as bs = 
    let as' = map getVal as in
    let bs' = map getVal bs in
    let asbs' = map getVal (as ++ bs) in 
    let l1 : (sum as' + sum bs' = sum (as' ++ bs')) = SumAssociates as' bs' in
    let p2 : (as' ++ bs' = asbs') = MapAppendDistributes getVal as bs in
    let l4 : (sum as' + sum bs' = sum (asbs')) = rewrite sym p2 in l1 in
        l4

record ChangeConstraints (cur : Currency{k=k}) (amt :Nat) (a: Vect n (Coin cur)) where
  constructor ValidateChange
  amtCheck : amt = cSum a

data Change : (cur : Currency) -> (amt: Nat) -> Type where
  MkChange : (n:Nat) -> (a : Vect n (Coin cur)) -> ChangeConstraints cur amt a -> Change cur amt

implementation Show (Change cur amt) where
  show (MkChange n a _) = (show n) ++ " coins totaling " ++(show (cSum a)) ++". " 
      ++ (show (map getVal a))

|||Given change for n and change for m, I can combine and make change for n+m
MergeChange : (c1 : Change cur n) -> (c2 : Change cur m) -> Change cur (n + m)
MergeChange (MkChange {amt = amt1} _ a1 const1) (MkChange {amt = amt2} _ a2 const2) = 
  let (amt1Check, amt2Check) = (amtCheck const1, amtCheck const2) in
  let sumCheckA : (amt1 + amt2 = cSum a1 + cSum a2) = 
    rewrite amt1Check in
    rewrite amt2Check in Refl in
  let sumCheckB : (amt1 + amt2 = cSum (a1 ++ a2)) = rewrite sym $ CSumDistr a1 a2 in sumCheckA in
    MkChange _ (a1 ++ a2) (ValidateChange sumCheckB) 

GiveChange : (cur : Currency) -> (amt: Nat) -> Change cur amt
GiveChange _ Z = MkChange Z [] (ValidateChange Refl)
GiveChange cur (S k) with (isElem (S k) (getDenoms cur))
  | Yes prf = let c = MkCoin (S k) cur in 
              let p1 : (plus (S k) 0 = cSum [c]) = Refl in
              let p2 : ((S k) = cSum [c]) = (rewrite sym $ plusZeroRightNeutral (S k) in p1) in 
                MkChange 1 [c] (ValidateChange p2)
  | No contr = let one = hasOne $ getConstraints cur in 
               let c = MkCoin 1 cur {q=one} in
               let one =  MkChange (S Z) [c] (ValidateChange Refl) in
               let rec = GiveChange cur k in
                 MergeChange one rec

USCurrency : Currency {k=4}
USCurrency = MkCurrency [1,5,10,25]

Foo : String 
Foo = show $ (GiveChange USCurrency 12)
 

