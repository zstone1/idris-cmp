module DepUnion
import Effects
import Data.List
import Data.Vect

data DepUnion : List Type -> Type where
  MkDepUnion : {l : List Type} -> {auto p : SubElem t l} -> (v : t) -> DepUnion l
  
Uninhabited (DepUnion []) where
  uninhabited (MkDepUnion {p} v )= absurd p

writeExample : (String, String) -> DepUnion [(String, String), Bool]
writeExample s = MkDepUnion s

readExample : DepUnion [String, Integer] -> Either String Integer
readExample (MkDepUnion {p = S (S later)} v) = absurd later
readExample (MkDepUnion {p = S Z} v) = Right v
readExample (MkDepUnion {p = (Z)} v) = Left v

Convert : DepUnion l -> (f : (x:Type) ->  SubElem x l -> x -> DepUnion r) -> DepUnion r 
Convert (MkDepUnion {p} {t} v) f = f t  p v

PadWithId : (l,r:List Type)-> (overrides : List (x:Type ** x-> DepUnion r)) -> {auto totalprf : SubList l r} -> {t:Type} -> SubElem t ((map DPair.fst overrides)++l) -> t -> DepUnion r

PadWithId [] _ [] a _ = absurd a
PadWithId (l::ls) r {totalprf = InList p n} [] a v with(a)
  | Z = MkDepUnion v
  | S later =  PadWithId ls r {totalprf = n} [] later v
PadWithId l r {totalprf = InList} ((o ** f) :: os) a v with (a)
  | Z = f v
  | S later = PadWithId l r os later v

T : List Type
T = [String,Char]

--PadWithIdTest : DepUnion [String, Char]
--PadWithIdTest = 
--  let a = MkDepUnion {l = [Bool, String]} True  in
--  let conv = PadWithId [String] [String, Char] [(Bool ** (\b => if b then (MkDepUnion {l=T} {t=Char} 'b') else (MkDepUnion {l=T} {t=Char} 'c')))] in 
--    Convert {l=[Bool, String]} {r = [String, Char] } a conv 

