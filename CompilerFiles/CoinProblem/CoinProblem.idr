module CoinProblem
import Util.UtilRoot
import CoinProblem.CoinModels
import CoinProblem.CoinHelpers
import Decidable.Order
import Data.So
%default total

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
    | (No _, _ ) = absurd $ sym oPrf
    | (Yes a, No b) = absurd $ sym oPrf
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
  GiveChangeI cur (S (S k)) Z {q} = absurd q
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
AtLeastOneCoin {amt} (MkChange _ [] x) = absurd$ sym$ amtCheck x
AtLeastOneCoin {amt} (MkChange _ (a::as) x) = LTESucc LTEZero

lteMinusOne : {auto q:LTE m (S n)} -> LTE 1 m -> LTE ((S n) - m) n
mutual 
  GiveChangeMinimizes : {auto q: LTE amt welf} -> (s: Change cur amt) -> LTE (getCoins$ GiveChangeI cur amt welf {q}) (getCoins s)
  mapThroughMinimizes : {q: LTE (S k) welf} -> {q' : Not $ Elem (S(S k)) (getDenoms cur)} -> (s: Change cur (S(S k))) -> 
                                     LTE (getCoins (minElemBy @{inht} {po=LTE} getCoins (mapElemPrf (mapThrough {k}{cur})))) (getCoins s)
  
 -- this signature is wrong: I need to reconcile k and S(k) in the definition of mapThrough. 
  addCoinToMin : (amt : Nat) -> (c:Coin cur) -> LTE 
                 (getCoins $ minElemBy @{inht} {po=LTE} getCoins (mapElemPrf (mapThrough {k=(getValue c) + amt}{cur}{q=q1}))) 
                 (S(getCoins $ GiveChangeI cur amt welf {q=q2}))

  smallChangeCands : {c:Coin cur} -> (S (S k) = cSum (c :: c' :: cs)) -> Elem (getValue c) (snd $ filterCandsWithPrf cur (S (S k)))

  mapThroughMinimizes {cur} {k} (MkChange _ [] constr) = absurd $ sym $ amtCheck constr
  mapThroughMinimizes {cur} {k} {q'} (MkChange _ (c :: []) constr) = 
    let (v ** w) = c in
    let lem = (S(S k))   ={ amtCheck constr }=
              (plus v 0) ={ plusZeroRightNeutral v }=
              (v)        QED in
    let elemprf : (Elem v (getDenoms cur)) = isDenom w in
        void $ q' $ rewrite lem in elemprf

  mapThroughMinimizes {cur} {welf} {k} {q} {q'} (MkChange _ (c::c'::cs) constr) =
    let chng = (MkChange _ (c::c'::cs) constr) in
    let cval = (getValue c) in
    let csumval = cSum (c'::cs) in
    let p1 : (_ = _) = (S(S k))        =[ amtCheck constr ]=
             (cSum (c::c'::cs))        =[ CSumDistr [c] (c'::cs) ]=
             ((cval + 0) + csumval)    =[ plusZeroRightNeutral cval ]= 
             (cval + csumval)          QED in

    let p2 : (LTE _ _ ) = (cval)       ={ lteAddRight cval }=
             (cval + csumval)          QED in

    let p2': (LTE _ _) = (cval +0)     =[ plusZeroRightNeutral cval ]=
             (cval)                    ={ p2 }=
             (cval + csumval)          QED in

    let p3 : (LTE _ _) = (cval)        ={ p2 }=
             (cval + csumval)          =[ sym p1 ]=
             (S(S k))                  QED in

    let p5 : (_=_) = (S(S k) - cval)          ={ cong {f=\e=>minus e cval} p1 }= 
             ((cval + csumval) - cval)        ={ cong {f = minus (cval + csumval)} $ sym $ plusZeroRightNeutral cval }=
             ((cval + csumval) - (cval +0))   ={ plusMinusLeftCancel cval csumval Z }=
             (csumval - 0)                    ={ minusZeroRight csumval }= 
             (csumval)                        QED in
    let p6 : (S(S k) - cval `LTE` welf) = 
             (S(S k) - cval) ={ lteMinusOne (notZero (snd c)) }= 
             (S k)           ={ q }=
             (welf)          QED in
    let p6' : (csumval `LTE` welf) = rewrite sym p5 in p6 in 
    let p7 : (csumval = sum (map getValue (c'::cs))) = Refl in
    let recMin = GiveChangeMinimizes {amt=csumval} {q=p6'}( MkChange _ (c'::cs) (ValidateChange p7)) in
    
    let p9 : (LTE _ _ ) = 
      ( getCoins $ minElemBy {po=LTE} getCoins (mapElemPrf (mapThrough {k}{cur}{q})))
        ={ ?l1 }=
      ( S $ getCoins $ GiveChangeI cur csumval welf {q=p6'} )                            
        ={LTESucc recMin}=
      ( S $ getCoins ( MkChange _ (c'::cs) (ValidateChange p7)))                                                        
        ={lteRefl}=
      ( getCoins $ MkChange _ (c::c'::cs) constr)
        QED in

--    let lem1 = smallChangeCands (amtCheck constr) in
--    let mapped = mapThrough lem1 {k} {cur} in 
        p9

  GiveChangeMinimizes {amt = Z} {cur}s = LTEZero
  GiveChangeMinimizes {amt = (S(S k))} {welf = Z} {q} s = absurd q
  GiveChangeMinimizes {amt = (S Z)} {welf = _ } {cur} s = AtLeastOneCoin s
  GiveChangeMinimizes {amt = (S(S k))} {welf = S j} {cur} {q = LTESucc q2} s with(isElem (S(S k)) (getDenoms cur))
    | (Yes prf) = AtLeastOneCoin s
    | (No contr) =  mapThroughMinimizes {k} {cur} {q'=contr} s

USCurrency : Currency {k=4}
USCurrency = MkCurrency [1,5,10,25]

Foo : Nat -> String 
Foo e= show $ GiveChange USCurrency e
 

