module CoinProblem
import Data.So
import Projective
import Data.Vect
import FoldTheorems
%default total


record CurrencyConstraints (d : Vect k Nat) where
  constructor ValidateCurrency
  hasOne : Elem 1 d
  --TODO: include claim that Not $ Elem 0 d
  
Currency : {k:Nat} -> Type
Currency {k}= (d : Vect k Nat ** CurrencyConstraints {k=k} d) 

MkCurrency : (d : Vect k Nat) -> {auto q : Elem 1 d} -> Currency {k=k}
MkCurrency d {q} = (d ** ValidateCurrency q)

getDenoms : Currency {k=k} -> Vect k Nat
getDenoms = fst

getConstraints : (cur : Currency {k=k}) -> CurrencyConstraints (getDenoms cur)
getConstraints = snd

record CoinConstraints (n:Nat) (cur:Currency {k=k}) where
  constructor ValidateCoin
  isDenom : Elem n (getDenoms cur) 

Coin : Currency -> Type
Coin cur = (n : Nat ** CoinConstraints n cur)

getValue : Coin d -> Nat
getValue = fst

MkCoin : (n:Nat) -> (cur : Currency) -> {auto q : Elem n (getDenoms cur)} -> Coin cur
MkCoin {q} n cur = (n ** ValidateCoin q)

cSum : Vect n (Coin d) -> Nat
cSum coins = sum (map getValue coins) 

|||Proof that cSum distributes like sum.
CSumDistr : (as : Vect n (Coin d)) -> (bs : Vect m (Coin d)) -> cSum as + cSum bs = cSum (as ++ bs)
CSumDistr as bs = 
    let l1 = SumAssociates (map getValue as) (map getValue bs) in
    let p2 = sym $ MapAppendDistributes getValue as bs in
    let l4 : ( _ = sum (map getValue (as ++ bs))) = rewrite p2 in l1 in l4

record ChangeConstraints (cur : Currency{k=k}) (amt :Nat) (a: Vect n (Coin cur)) where
  constructor ValidateChange
  amtCheck : amt = cSum a

data Change : (cur : Currency) -> (amt: Nat) -> Type where
  MkChange : (n:Nat) -> (a : Vect n (Coin cur)) -> ChangeConstraints cur amt a -> Change cur amt

implementation Show (Change cur amt) where
  show (MkChange n a _) = (show n) ++ " coins totaling " ++(show (cSum a)) ++". " 
      ++ (show (map getValue a))

|||Given change for n and change for m, I can combine and make change for n+m
MergeChange : (c1 : Change cur n) -> (c2 : Change cur m) -> Change cur (n + m)
MergeChange (MkChange {amt = amt1} _ a1 const1) (MkChange {amt = amt2} _ a2 const2) = 
  let (amt1Check, amt2Check) = (amtCheck const1, amtCheck const2) in
  let sumCheckA = MergeEqualities amt1Check amt2Check in
  let sumCheckB : (amt1 + amt2 = cSum (a1 ++ a2)) = rewrite sym $ CSumDistr a1 a2 in sumCheckA in
    MkChange _ (a1 ++ a2) (ValidateChange sumCheckB) 

|||Does the obvious then when the amount of change is a value for a coin.
total
GiveChangeElem : (cur : Currency) -> (amt : Nat) -> (Elem amt (getDenoms cur)) -> Change cur amt
GiveChangeElem cur amt prf = 
  let c = MkCoin amt cur in 
    MkChange _ [c] (ValidateChange (rewrite plusZeroRightNeutral amt in Refl))

getCoins: Change cur amt -> Nat
getCoins (MkChange n1 _ _) = n1 

candDenom : Nat -> Type
candDenom amt = (n:Nat ** (LT 0 n, LT n amt)) 


filterCand : (amt: Nat) -> (cand: Nat) -> Maybe $ candDenom amt
filterCand amt cand with ((isLTE 1 cand, isLTE (S cand) amt))
  |( No _, _ )= Nothing
  |( _, No _ )= Nothing
  |( Yes prf1, Yes prf2 ) =  Just (cand ** (prf1, prf2))

                                 
filterCandidates : {j:Nat} -> (cur : Currency {k=j}) -> 
                   (amt : Nat) -> 
                   {auto q1 : (LTE 1 amt)} ->
                   {auto q2 : (Not$ Elem amt (getDenoms cur))} ->
                   (p:Nat ** Vect (S p) (candDenom amt))
filterCandidates cur Z {q1} = absurd q1
filterCandidates (_**constr) (S Z) {q2} = void $ NotElemLemma1 (hasOne constr) q2 Refl
filterCandidates {q2} (xss ** constr) (S(S k)) {j} with (hasOne constr) 
  filterCandidates {q2} (((S Z)::xs) ** _) (S(S k)) | Here = 
    let c : (candDenom (S(S k))) = (S Z ** (LTESucc LTEZero, LTESucc $ LTESucc $ LTEZero)) in
    let (l ** rest) = mapMaybe (filterCand (S(S k))) xs in
      ( _ ** c::rest) 
  filterCandidates {q2} (x::xs ** _ ) (S(S k)) | There next = 
    let prf1 = NotElemLemma2 q2 in
    let (l ** next) = filterCandidates (xs ** ValidateCurrency next) (S(S k)) {q2 = prf1} in
      case filterCand (S(S k)) x of
           Nothing => (_ ** next)
           Just x => (_ ** x :: next)

isCand : (amt: Nat) -> (cand: Nat) -> Bool
isCand amt cand with ((isLTE 1 cand, isLTE (S cand) amt))
  |( No _, _ )= False
  |( _, No _ )= False
  |( Yes prf1, Yes prf2 ) = True

oneIsCand : LTE 2 amt -> (So (isCand amt 1))
oneIsCand {amt} x with (( isLTE 1 1, isLTE 2 amt))
  | (_, No bad) = void $ bad x
  | (No bad ,_) = void $ bad (lteRefl)
  | (Yes prf1, Yes prf2) = Oh

filterCands : (cur : Currency) -> (amt : Nat) -> (j : Nat ** Vect j Nat)
filterCands cur amt = filter (isCand amt) (getDenoms cur)

filterCandsHasOne : (cur :Currency) -> (amt :Nat) -> LTE 2 amt -> Elem 1 (snd $ filterCands cur amt)
filterCandsHasOne (denoms ** constr) amt prf = filterPass (S Z) (denoms) (isCand amt) (hasOne constr) (oneIsCand {amt} prf)

candsAreValid : Elem x (snd $ filterCands cur amt) -> ((LTE 1 amt, LTE (S x) amt))
candsAreValid {cur} {amt} elem = ?candsAreValid_rhs


GiveChange : (cur : Currency) -> (amt: Nat) -> (welf : Nat) ->{auto q : LTE amt welf} -> Change cur amt
GiveChange cur Z _ = MkChange Z [] (ValidateChange Refl) 
GiveChange cur (S k) Z {q} = absurd q
GiveChange cur (S k) (S welf) {q = LTESucc q'} with (isElem (S k) (getDenoms cur))
  | Yes prf = GiveChangeElem cur (S k) prf 
  | No contr = 
    let (l ** cands) = filterCandidates {q2= contr} cur (S k) in
    let changeChoices = map handleDenom cands in 
        minElemBy {po = LTE} getCoins changeChoices where 
          handleDenom : candDenom (S k) -> Change cur (S k)
          handleDenom (n ** (zLtn, LTESucc nLtek)) =
            let q1 : (n `LTE` S k) = lteSuccRight nLtek in
            let q2 : (n `LTE` welf) = lteTransitive nLtek q' in
            let q3 : ((S k)-n `LTE` welf) = let LTESucc f = lteMinus (S k) n in lteTransitive f q' in
            let c1 = GiveChange cur n welf in
            let c2 = GiveChange cur ((S k) -n) welf in
                rewrite minusPlusCancel (S k) n in MergeChange c1 c2 
                        
  
USCurrency : Currency {k=4}
USCurrency = MkCurrency [1,5,10,25]

Foo : Nat -> String 
Foo e= show $ (GiveChange USCurrency e e {q = lteRefl})
 

