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

Convert : OneOf l -> (f : (x:Type) ->  SubElem x l -> x -> OneOf r) -> OneOf r 
Convert (MkOneOf {p} {t} v) f = f t  p v

PadWithId : (l,r:List Type)-> (overrides : List (x:Type ** x-> OneOf r)) -> {auto totalprf : SubList l r} -> {t:Type} -> SubElem t ((map DPair.fst overrides)++l) -> t -> OneOf r

PadWithId [] _ [] a _ = absurd a
PadWithId (l::ls) r {totalprf = InList p n} [] a v with(a)
  | Z = MkOneOf v
  | S later =  PadWithId ls r {totalprf = n} [] later v
PadWithId l r {totalprf = InList} ((o ** f) :: os) a v with (a)
  | Z = f v
  | S later = PadWithId l r os later v

T : List Type
T = [String,Char]

--PadWithIdTest : OneOf [String, Char]
--PadWithIdTest = 
--  let a = MkOneOf {l = [Bool, String]} True  in
--  let conv = PadWithId [String] [String, Char] [(Bool ** (\b => if b then (MkOneOf {l=T} {t=Char} 'b') else (MkOneOf {l=T} {t=Char} 'c')))] in 
--    Convert {l=[Bool, String]} {r = [String, Char] } a conv 

