module CoinProblem
import Syntax.PreorderReasoning
import Data.So
import Projective
import Data.Vect
import FoldTheorems
import Decidable.Order
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
  (cSum as + cSum bs)                            ={ SumAssociates (map getValue as) (map getValue bs) }= 
  (sum ((map getValue as) ++ (map getValue bs))) ={ cong $ MapAppendDistributes getValue as bs }=
  (cSum (as ++ bs))                              QED

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
  let amtValid = 
    (amt1 + amt2)       ={ MergeEqualities (amtCheck const1) (amtCheck const2) }=
    (cSum a1 + cSum a2) ={ CSumDistr a1 a2 }= 
    (cSum (a1 ++ a2))   QED in
  MkChange _ (a1 ++ a2) (ValidateChange amtValid) 

|||Does the obvious then when the amount of change is a value for a coin.
total
GiveChangeElem : (cur : Currency) -> (amt : Nat) -> (Elem amt (getDenoms cur)) -> Change cur amt
GiveChangeElem cur amt prf = 
  let c = MkCoin amt cur in 
    MkChange _ [c] (ValidateChange (rewrite plusZeroRightNeutral amt in Refl))

getCoins: Change cur amt -> Nat
getCoins (MkChange n1 _ _) = n1 

isCand : (amt: Nat) -> (cand: Nat) -> Bool
isCand amt cand with ((isLTE 1 cand, isLTE (S cand) amt))
  |( No _, _ )= False
  |( _, No _ )= False
  |( Yes _, Yes _ ) = True

oneIsCand : LTE 2 amt -> (So (isCand amt 1))
oneIsCand {amt} x with (( isLTE 1 1, isLTE 2 amt))
  | (_, No bad) = void $ bad x
  | (No bad ,_) = void $ bad (lteRefl)
  | (Yes prf1, Yes prf2) = Oh

filterCands : (cur : Currency) -> (amt : Nat) -> (j : Nat ** (Vect j Nat))
filterCands cur amt = filter (isCand amt) (getDenoms cur)

filterCandsHasOne : (cur :Currency) -> (amt :Nat) -> LTE 2 amt -> Elem 1 (snd $ filterCands cur amt)
filterCandsHasOne (denoms ** constr) amt prf = filterForward (hasOne constr) (oneIsCand {amt} prf)

candsAreValid : So (isCand amt x) -> ((LTE 1 x, LTE (S x) amt))
candsAreValid {x} {amt} o with (isCand amt x) proof oPrf
  candsAreValid {x} {amt} Oh | True with (isLTE 1 x, isLTE (S x) amt) proof prf2
    | (No _, _ ) = absurd oPrf
    | (Yes a, No b) = absurd oPrf
    | (Yes a, Yes b) = (a, b)

candsLemma1 : Elem x (snd $ filterCands cur amt) -> (Elem x (getDenoms cur), LTE 1 x, LTE (S x) amt)
candsLemma1 {cur} elem = let (o, e) = filterBackwards (getDenoms cur) elem  in 
                        let (p1,p2) = candsAreValid o in
                            (e, p1,p2) 

filterCandsWithPrf : (cur : Currency) -> (amt: Nat) -> {auto p:LTE 2 amt} -> (j: Nat ** (Vect (S j) Nat))
filterCandsWithPrf cur amt {p} with (filterCandsHasOne cur amt p)
  | hasOne with (filterCands cur amt)
    | (_**[]) = absurd hasOne
    | (S j ** (c::cs)) = (j ** (c::cs))


candsLemma2 : Elem x (snd $ filterCandsWithPrf cur amt {p=p}) -> (Elem x (snd $ filterCands cur amt))
candsLemma2 {cur}{amt}{p} elem with (filterCandsHasOne cur amt p)
  | foo with (filterCands cur amt)
    | (_** []) = absurd foo 
    | (_ ** (c::cs)) = elem



restrictFunc : (f: {x:u} -> Elem x (a::as) -> t) -> {y:u} -> Elem y as -> t
restrictFunc f elem = f (There elem) 

mapElemPrf : {l: Vect k u} -> (f: {x:u} -> Elem x l -> t) -> Vect k t
mapElemPrf {l = []} _ = []
mapElemPrf {l = (x :: xs)} f =  (f Here) :: (mapElemPrf {l=xs} (restrictFunc f))

mutual
  GiveChangeI : (cur : Currency) -> (amt: Nat) -> (welf : Nat) ->{auto q : LTE amt welf} -> Change cur amt
  handleCand : {auto q : LTE (S k) welf} -> (Elem c (getDenoms cur), LTE 1 c, LTE (S c) (S(S k))) -> Change cur (S(S k))
  mapThrough : {auto q : LTE (S k) welf} -> Elem x (snd $ filterCandsWithPrf cur (S(S k))) -> Change cur (S(S k))

  GiveChangeI cur Z _ = MkChange Z [] (ValidateChange Refl) 
  GiveChangeI cur (S k) Z {q} = absurd q
  GiveChangeI cur (S Z) _ = GiveChangeElem cur (S Z) (hasOne $ getConstraints cur)
  GiveChangeI cur (S(S k)) (S welf) {q = LTESucc q'} with (isElem (S(S k)) (getDenoms cur))
    | (Yes prf) = GiveChangeElem cur (S(S k)) prf
    | (No contr) = minElemBy @{inht} {po=LTE} getCoins (mapElemPrf mapThrough)

  handleCand {c} {k} {welf} {cur} {q} (p1, p2, LTESucc p3) = 
    let q1 : (c `LTE` S(S k)) = lteSuccRight p3 in
    let q2 : (c `LTE` welf) = lteTransitive p3 q in
    let q3 : ((S(S k))-c `LTE` welf) = let LTESucc f = lteMinus (S(S k)) c in lteTransitive f q in
    let c1 = GiveChangeElem cur c p1 in
    let c2 = GiveChangeI cur ((S(S k)) - c) welf in
        rewrite minusPlusCancel (S(S k)) c in MergeChange c1 c2 

  mapThrough = handleCand . candsLemma1 . candsLemma2 
 
GiveChange : (cur : Currency) -> (amt: Nat) -> Change cur amt
GiveChange cur amt = GiveChangeI cur amt amt {q=lteRefl}

AtLeastOneCoin : (s: Change cur (S amt)) -> LTE 1 (getCoins s)
AtLeastOneCoin {amt = amt} (MkChange _ [] x) = absurd$ sym$ amtCheck x
AtLeastOneCoin {amt = amt} (MkChange _ (a::as) x) = LTESucc LTEZero

mutual 
  GiveChangeMinimizes : {auto q: LTE amt welf} -> (s: Change cur amt) -> LTE (getCoins$ GiveChange cur amt) (getCoins s)
  mapThroughMinimizes : {auto q: LTE (S k) welf} -> {q' : Not $ Elem (S(S k)) (getDenoms cur)} -> (s: Change cur (S(S k))) -> 
                                     LTE (getCoins (minElemBy @{inht} {po=LTE} getCoins (mapElemPrf (mapThrough {k}{cur})))) (getCoins s)
  
  smallChangeCands : {c:Coin cur} -> (S (S k) = cSum (c :: c' :: cs)) -> Elem (getValue c) (snd $ filterCandsWithPrf cur (S (S k)))

--  mapThroughCoin : (wit : Elem x (snd $ filterCandsWithPrf cur (S(S k)))) -> (mapThrough {k} {cur} wit)

  mapThroughMinimizes {cur} {k} (MkChange _ [] constr) = absurd $ sym $ amtCheck constr
  mapThroughMinimizes {cur} {k} {q'} (MkChange _ (c :: []) constr) = 
    let (v ** w) = c in
    let amtprf = amtCheck constr in
    let lem = plusZeroRightNeutral v in 
    let elemprf : (Elem v (getDenoms cur)) = isDenom w in
        void $ q' $ rewrite trans amtprf lem in elemprf

  mapThroughMinimizes {cur} {k} {q'} (MkChange _ (c::c'::cs) constr) =
--    let lem1 = smallChangeCands (amtCheck constr) in
--    let mapped = mapThrough lem1 {k} {cur} in 
        ?foo 


  GiveChangeMinimizes {amt = Z} {cur}s = LTEZero
  GiveChangeMinimizes {amt = (S Z)} {cur} s = AtLeastOneCoin s
  GiveChangeMinimizes {amt = (S k)} {welf = Z} {q} s = absurd q
  GiveChangeMinimizes {amt = (S(S k))} {welf = S j} {cur} {q = LTESucc q'} s with(isElem (S(S k)) (getDenoms cur))
    | (Yes prf) = AtLeastOneCoin s
    | (No contr) =  mapThroughMinimizes {k} {cur} {q'=contr} s

USCurrency : Currency {k=4}
USCurrency = MkCurrency [1,5,10,25]

Foo : Nat -> String 
Foo e= show $ GiveChange USCurrency e
 

