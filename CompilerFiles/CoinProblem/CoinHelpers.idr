module CoinHelpers
import Util.UtilRoot
import CoinProblem.CoinModels
%access export

|||Given change for n and change for m, I can combine and make change for n+m
MergeChange : (c1 : Change cur n) -> (c2 : Change cur m) -> Change cur (n + m)
MergeChange (MkChange {amt = amt1} _ a1 const1) (MkChange {amt = amt2} _ a2 const2) = 
    let amtValid = 
    (amt1 + amt2)       ={ MergeEqualities (+) (amtCheck const1) (amtCheck const2) }=
    (cSum a1 + cSum a2) ={ CSumDistr a1 a2 }= 
    (cSum (a1 ++ a2))   QED in
      MkChange _ (a1 ++ a2) (ValidateChange amtValid)

|||Does the obvious then when the amount of change is a value for a coin.
public export
GiveChangeElem : (cur : Currency) -> (amt : Nat)  -> {auto q : LTE 1 amt} -> (Elem amt (getDenoms cur)) -> Change cur amt
GiveChangeElem cur amt prf = 
  let c = MkCoin amt cur in 
    MkChange _ [c] (ValidateChange (rewrite plusZeroRightNeutral amt in Refl))

