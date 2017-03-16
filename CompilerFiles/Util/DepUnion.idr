module DepUnion
import Effects
import Data.List
import Data.Vect

data DepUnion : List Type -> Type where
  MkDepUnion : {l : List Type} -> {auto p : SubElem t l} -> (v : t) -> DepUnion l
  
Uninhabited (DepUnion []) where
  uninhabited (MkDepUnion {p} v )= absurd p

depMatch : DepUnion l -> (f: (x:Type) -> SubElem x l -> x -> t) -> t
depMatch (MkDepUnion {l=[]} {p} _) _ = absurd p
depMatch (MkDepUnion {l = t::us} {t} {p = Z} v) f = f t Z v
depMatch (MkDepUnion {l = u::us} {t} {p = S later} v) f = 
  depMatch (MkDepUnion {l=us} v) (\a,b,c => f a (S b) c)

ElemTrans : SubElem x ys -> SubList ys zs -> SubElem x zs
ElemTrans x SubNil = absurd x
ElemTrans Z (InList e _) = e
ElemTrans {ys = y::ys'} (S later) (InList e l) = ElemTrans later l

%hint
implicit
Shuffle : DepUnion l -> {auto left: SubList l r} -> DepUnion r
Shuffle (MkDepUnion {p} _) {left = SubNil} = absurd p
Shuffle (MkDepUnion {p = Z} v) {left = InList e rest}  = MkDepUnion v
Shuffle (MkDepUnion {p = S later} v) {left = InList e rest} = MkDepUnion {p = ElemTrans later rest} v

Show (DepUnion []) where
  show t = absurd t

Show a => Show (DepUnion [a]) where
  show d = depMatch d showf where
    showf : Show a => (x:Type) -> (SubElem x [a])  -> x -> String
    showf _ Z v = show v
    showf _ (S later) _ = absurd later

(Show a, Show b) => Show (DepUnion [a,b]) where
  show d = depMatch d showf where
    showf : (Show a, Show b) => (x:Type) -> (SubElem x [a,b])  -> x -> String
    showf _ Z v = show v
    showf _ (S Z) v = show v
    showf _ (S (S later)) _ = absurd later

(Show a, Show b, Show c) => Show (DepUnion [a,b,c]) where
  show d = depMatch d showf where
    showf : (Show a, Show b, Show c) => (x:Type) -> (SubElem x [a,b,c])  -> x -> String
    showf _ Z v = show v
    showf _ (S Z) v = show v
    showf _ (S (S Z)) v = show v
    showf _ (S (S (S later))) _ = absurd later

writeExample : (String, String) -> DepUnion [(String, String), Bool]
writeExample s = MkDepUnion s

readExample : DepUnion [String, Integer] -> Either String Integer
readExample (MkDepUnion {p = S (S later)} v) = absurd later
readExample (MkDepUnion {p = S Z} v) = Right v
readExample (MkDepUnion {p = (Z)} v) = Left v


Convert : DepUnion l -> (f : (x:Type) ->  SubElem x l -> x -> DepUnion r) -> DepUnion r 
Convert (MkDepUnion {p} {t} v) f = f t  p v

PadWithId : (l,r:List Type)-> (overrides : List (x:Type ** x-> DepUnion r)) -> {auto totalprf : SubList l r} -> {t:Type} -> {auto a : SubElem t ((map DPair.fst overrides)++l)} -> t -> DepUnion r

PadWithId [] _ [] {a} _ = absurd a
PadWithId (l::ls) r {totalprf = InList p n} [] {a} v with(a)
  | Z = MkDepUnion v
  | S later =  PadWithId ls r {totalprf = n} [] {a=later} v
PadWithId l r {totalprf = InList} ((o ** f) :: os) {a} v with (a)
  | Z = f v
  | S later = PadWithId l r os {a=later} v

T : List Type
T = [String,Char]

PadWithIdTrivial : DepUnion [String, Bool]
PadWithIdTrivial = 
  PadWithId [String, Bool] [String, Bool] [] {t=Bool} True

PadWithIdTest : String 
PadWithIdTest = show $ PadWithId [String] T [(_ ** (\b => if b then (MkDepUnion {l=T} {t=Char} 't') else (MkDepUnion {l=T} {t=Char} 'f')))] {t=String} "hi" 

Push : DepUnion (x::xs) -> (x -> DepUnion (ys ++ xs)) -> DepUnion (ys ++ xs)
Push d f {xs}{ys} = Convert d (\t,a => PadWithId xs (ys ++ xs) [(_**f)] {t=t}{a=a})









