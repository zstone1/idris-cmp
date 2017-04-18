module DepUnion
import Effects
import Data.List
import Data.Vect
%access public export

data DepUnion : List Type -> Type where
  MkDepUnion : {l : List Type} ->{t:Type} -> (v : t) -> {auto p : SubElem t l} -> DepUnion l
  
Uninhabited (DepUnion []) where
  uninhabited (MkDepUnion {p} v )= absurd p

extract: DepUnion [x] -> x
extract (MkDepUnion v {p = Z}) = v
extract (MkDepUnion _ {p = S l}) = absurd l

depMatch : DepUnion l -> (f: (x:Type) -> SubElem x l -> x -> t) -> t
depMatch (MkDepUnion {l=[]} {p} _) _ = absurd p
depMatch (MkDepUnion {l = t::us} {t} {p = Z} v) f = f t Z v
depMatch (MkDepUnion {l = u::us} {t} {p = S later} v) f = 
  depMatch (MkDepUnion {l=us} v) (\a,b,c => f a (S b) c)

%hint
elemTrans : SubElem x ys -> SubList ys zs -> SubElem x zs
elemTrans x SubNil = absurd x
elemTrans Z (InList e _) = e
elemTrans {ys = y::ys'} (S later) (InList e l) = elemTrans later l

%hint
implicit
Shuffle : DepUnion l -> {auto left: SubList l r} -> DepUnion r
Shuffle (MkDepUnion {p} _) {left = SubNil} = absurd p
Shuffle (MkDepUnion {p = Z} v) {left = InList e rest}  = MkDepUnion v
Shuffle (MkDepUnion {p = S later} v) {left = InList e rest} = MkDepUnion {p = elemTrans later rest} v

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


convert : DepUnion l -> (f : (x:Type) ->  x -> SubElem x l -> DepUnion r) -> DepUnion r 
convert (MkDepUnion {p} {t} v) f = f t v p

padWithId : (l,r:List Type)-> (overrides : List (x:Type ** x-> DepUnion r)) -> {auto totalprf : SubList l r} -> {t:Type} -> t ->  {auto a : SubElem t ((map DPair.fst overrides)++l)} -> DepUnion r
padWithId [] _ [] {a} _ = absurd a
padWithId (l::ls) r {totalprf = InList p n} [] {a} v with(a)
  | Z = MkDepUnion v
  | S later =  padWithId ls r {totalprf = n} [] {a=later} v
padWithId l r {totalprf = InList} ((o ** f) :: os) {a} v with (a)
  | Z = f v
  | S later = padWithId l r os {a=later} v


private
T : List Type
T = [String,Char]

private
padWithIdTrivial : (MkDepUnion {l=[String, Bool]}{t=Bool} True) = padWithId [String, Bool] [String, Bool] [] True
padWithIdTrivial = Refl

private
padWithIdTest1 : "\"hi\"" = show $ padWithId [String] T [(_ ** (\b => if b then (MkDepUnion 't') else (MkDepUnion 'f')))] "hi" 
padWithIdTest1 = Refl

private
padWithIdTest2 : "'f'" = show $ padWithId [String] T [(_ ** (\b => if b then (MkDepUnion 't') else (MkDepUnion 'f')))] False
padWithIdTest2 = Refl

|||Applies @f to the head of @d if it's a match. Otherwise it's a no-op, modulo type changes.
push : (d:DepUnion (x::xs)) -> (f: x -> DepUnion (ys ++ xs)) -> DepUnion (ys ++ xs)
push d f {xs}{ys} = convert d (\t,v,a => padWithId xs (ys ++ xs) [(_**f)] v {t=t}{a=a})

private
pushTest : "False" = show $ push {ys = []} (MkDepUnion {l=[String, Bool, Char]} False) (\s => MkDepUnion True)
pushTest = Refl

|||Applies a simple map to the head of @d, if it's a match.
pushOne : (d: DepUnion (x::xs)) -> (f: x -> y) -> DepUnion(y::xs)
pushOne d f {y} = push {ys = [y]} d (\x => MkDepUnion(f x)) 

|||If @d is a match for @x, the type is collapsed into the other types of the union.
collapse : (d: DepUnion (x :: xs)) -> (f: x -> DepUnion xs) -> DepUnion xs
collapse d f = push {ys = []} d f


private
collapseHelper : DepUnion [Nat, String]
collapseHelper = 
  let base = MkDepUnion {l = [String, Nat, Bool]} False in --This tests that shuffle is working implicitly.
      collapse base (\i => if i then MkDepUnion "it was true"  else MkDepUnion "it was false" )

private
collapseTest : "\"it was false\"" = show DepUnion.collapseHelper
collapseTest = Refl


syntax dcase [d] "of" [f] = 
  extract $ convert (Shuffle d) (\t,x,p => MkDepUnion ((toFuncForm f t x p )))

syntax "|" [t] end [after] = t :: after
syntax "|" [t] term = | t end []
syntax [t] ":=" {i} "=>" [f] = ( t ** \i : t => f )

total   
toFuncForm : (l: List (t:Type ** (t-> u))) -> (t:Type) -> (v:t) -> (SubElem t (Functor.map DPair.fst l)) -> u
toFuncForm ((t1 ** f1) :: fs) t1 v (Z) = f1 v
toFuncForm ((t1 ** f1) :: fs) t v (S later) = toFuncForm fs t v later

test2 : List (t:Type ** (t-> Bool))
test2 = | String := i  => True end 
        | Nat := s => False end []


private
SynTestVal : Bool 
SynTestVal = 
  let base = MkDepUnion {l=[Char, String, Bool]} True in
  dcase base of 
  | Char := i => False end
  | Bool := b => b end
  | String := s => True term

private 
synTest : True = SynTestVal
synTest = Refl


 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
