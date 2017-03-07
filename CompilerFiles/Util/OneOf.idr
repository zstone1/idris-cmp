module OneOf
import Effects
import Data.List
import Data.Vect

data OneOf : List Type -> Type where
  MkOneOf : {l : List Type} -> {auto p : SubElem t l} -> (v : t) -> OneOf l
  
Uninhabited (OneOf []) where
  uninhabited (MkOneOf {p} v )= absurd p

writeExample : (String, String) -> OneOf [(String, String), Bool]
writeExample s = MkOneOf s

readExample : OneOf [String, Integer] -> Either String Integer
readExample (MkOneOf {p = S (S later)} v) = absurd later
readExample (MkOneOf {p = S Z} v) = Right v
readExample (MkOneOf {p = (Z)} v) = Left v

Convert : OneOf l -> (f : {x:Type} ->  SubElem x l -> x -> OneOf r) -> OneOf r 
Convert (MkOneOf {p} v) f = f p v

partial
PadWithId : (l,r:List Type)-> (overrides : List (x:Type ** (SubElem x l, x-> OneOf r))) -> {auto totalprf : SubList l r} -> {t:Type} -> SubElem t ((map DPair.fst overrides)++l) -> t -> OneOf r

PadWithId [] _ [] a _ = absurd a
PadWithId (l::ls) r {totalprf = InList p n} [] a v with(a)
  | Z = MkOneOf v
  | S later = ?case2
--PadWithId l r {totalprf = InList} ((o ** f) :: os) a v = ?case2

