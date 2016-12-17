module CoinModels
import Util.UtilRoot
%access public export
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
  notZero : LTE (S Z) n

Coin : Currency -> Type
Coin cur = (n : Nat ** CoinConstraints n cur)

getValue : Coin d -> Nat
getValue = fst

MkCoin : (n:Nat) -> (cur : Currency) -> {auto q : Elem n (getDenoms cur)} -> {auto q' : LTE (S Z) n} -> Coin cur
MkCoin {q} {q'} n cur = (n ** ValidateCoin q q')

cSum : Vect n (Coin d) -> Nat
cSum coins = sum (map getValue coins) 


|||Proof that cSum distributes like sum.
export
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

