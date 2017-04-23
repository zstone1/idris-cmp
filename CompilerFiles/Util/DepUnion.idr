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

toFuncForm : (l: List (t:Type ** (t-> u))) -> (t:Type) -> (v:t) -> (SubElem t (Functor.map DPair.fst l)) -> u
toFuncForm ((t1 ** f1) :: fs) t1 v (Z) = f1 v
toFuncForm ((t1 ** f1) :: fs) t v (S later) = toFuncForm fs t v later

dep: {t:Type} -> {l : List Type} -> {auto p : SubElem t l} -> (v:t) -> DepUnion l
dep {t} {l} {p} v = MkDepUnion v

depMatch : DepUnion l -> (f : (x:Type) ->  x -> SubElem x l -> u) -> u
depMatch (MkDepUnion {p} {t} v) f = f t v p

depMatch' : (f : (x:Type) ->  x -> SubElem x l -> u) -> DepUnion l -> u
depMatch' = flip depMatch


%hint
elemTrans : SubElem x ys -> SubList ys zs -> SubElem x zs
elemTrans x SubNil = absurd x
elemTrans Z (InList e _) = e
elemTrans {ys = y::ys'} (S later) (InList e l) = elemTrans later l

addSubElem : SubElem x (y::y::ys) -> SubElem x (y::ys)
addSubElem Z = Z
addSubElem (S l) = l

%hint
implicit
shuffle : DepUnion l -> {auto left: SubList l r} -> DepUnion r
shuffle (MkDepUnion {p} _) {left = SubNil} = absurd p
shuffle (MkDepUnion {p = Z} v) {left = InList e rest}  = MkDepUnion v
shuffle (MkDepUnion {p = S later} v) {left = InList e rest} = MkDepUnion {p = elemTrans later rest} v

shuffle' : {auto left: SubList l r} -> DepUnion l -> DepUnion r
shuffle' {left} d= shuffle {left} d



padWithId : (l,r:List Type)-> (overrides : List (x:Type ** x-> DepUnion r)) -> {auto totalprf : SubList l r} -> {t:Type} -> t ->  {auto a : SubElem t ((map DPair.fst overrides)++l)} -> DepUnion r
padWithId [] _ [] {a} _ = absurd a
padWithId (l::ls) r {totalprf = InList p n} [] {a} v with(a)
  | Z = MkDepUnion v
  | S later =  padWithId ls r {totalprf = n} [] {a=later} v
padWithId l r {totalprf = InList} ((o ** f) :: os) {a} v with (a)
  | Z = f v
  | S later = padWithId l r os {a=later} v


|||Applies @f to the head of @d if it's a match. Otherwise it's a no-op, modulo type changes.
push : (d:DepUnion (x::xs)) -> (f: x -> DepUnion (ys ++ xs)) -> DepUnion (ys ++ xs)
push d f {xs}{ys} = depMatch d (\t,v,a => padWithId xs (ys ++ xs) [(_**f)] v {t=t}{a=a})


|||Applies a simple map to the head of @d, if it's a match.
pushOne : (d: DepUnion (x::xs)) -> (f: x -> y) -> DepUnion(y::xs)
pushOne d f {y} = push {ys = [y]} d (\x => MkDepUnion(f x)) 

|||If @d is a match for @x, the type is collapsed into the other types of the union.
collapse : (d: DepUnion (x :: xs)) -> (f: x -> DepUnion xs) -> DepUnion xs
collapse d f = push {ys = []} d f

subElemConcat : SubElem x (ys ++ zs) -> Either (SubElem x ys) (SubElem x zs)
subElemConcat {ys = []} p = Right p
subElemConcat {ys = y::ys} Z = Left Z
subElemConcat {ys = y::ys} (S n) with(subElemConcat n)
  |Left q = Left$ S q
  |Right q = Right q

split : DepUnion (xs ++ ys) -> Either (DepUnion xs) (DepUnion ys)
split (MkDepUnion {t} v {p}) = case subElemConcat p of
                                    Left q => Left$ MkDepUnion {p=q} v
                                    Right q => Right$ MkDepUnion {p=q} v

mapToMatcher : Applicative m => 
              (f : {t:Type} -> pre t -> m (post t)) -> 
              (x:Type) -> 
              x -> 
              SubElem x (map pre l) -> 
              m ( DepUnion (map post l))
mapToMatcher {l = []} _ _ _ p  = absurd p
mapToMatcher {l = t::ts} f _ v Z = [| dep (f v) |]
mapToMatcher {l = t'::ts} f t v (S n) = 
  let sub = dropPrefix (subListId _) {zs = [_]} in 
      [| (shuffle' {left = sub}) (mapToMatcher f t v n) |]


syntax dcase [d] "of" [f] = 
  extract $ depMatch (shuffle d) (\t,x,p => MkDepUnion ((toFuncForm f t x p ))) --composition doesn't play nice with implicit params
syntax [t] ":" {i} "=>" [f] "%|" = (t ** \i : t => f)

infixl 0 |%

(|%) : List (t:Type ** (t -> u)) -> (t:Type ** (t -> u)) -> List (t:Type ** (t -> u))
(|%) l a = a :: l

Show (DepUnion []) where
  show t = absurd t

Show a => Show (DepUnion [a]) where
  show d = depMatch d showf where
    showf : Show a => (x:Type) -> x -> (SubElem x [a]) -> String
    showf _ v Z = show v
    showf _ _ (S later) = absurd later

(Show a, Show b) => Show (DepUnion [a,b]) where
  show d = depMatch d showf where
    showf : (Show a, Show b) => (x:Type) -> x -> (SubElem x [a,b]) -> String
    showf _ v Z = show v
    showf _ v (S Z) = show v
    showf _ _ (S (S later)) = absurd later

(Show a, Show b, Show c) => Show (DepUnion [a,b,c]) where
  show d = depMatch d showf where
    showf : (Show a, Show b, Show c) => (x:Type) -> x -> (SubElem x [a,b,c]) -> String
    showf _ v Z = show v
    showf _ v (S Z) = show v
    showf _ v (S (S Z)) = show v
    showf _ _ (S (S (S later))) = absurd later

Show (DepUnion (a :: b :: c :: d :: xs)) where
  show d = "too deep"

--Tests 
private
writeExample : (String, String) -> DepUnion [(String, String), Bool]
writeExample s = MkDepUnion s

private
readExample : DepUnion [String, Integer] -> Either String Integer
readExample (MkDepUnion {p = S (S later)} v) = absurd later
readExample (MkDepUnion {p = S Z} v) = Right v
readExample (MkDepUnion {p = (Z)} v) = Left v

private
pushTest : "False" = show $ push {ys = []} (MkDepUnion {l=[String, Bool, Char]} False) (\s => MkDepUnion True)
pushTest = Refl

private
SynTestVal : Bool 
SynTestVal = 
  let base = MkDepUnion {l=[Char, String, Bool]} True in
  dcase base of []
  |% Char : i => False %|
  |% Bool : b => b %|
  |% String : s => False %|

private 
synTest : True = SynTestVal
synTest = Refl

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
 
private
collapseHelper : DepUnion [Nat, String]
collapseHelper = 
  let base = MkDepUnion {l = [String, Nat, Bool]} False in --This tests that shuffle is working implicitly.
      collapse base (\i => if i then MkDepUnion "it was true"  else MkDepUnion "it was false" )

private
collapseTest : "\"it was false\"" = show DepUnion.collapseHelper
collapseTest = Refl

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
