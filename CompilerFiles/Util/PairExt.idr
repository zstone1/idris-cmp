module PairExt
import Data.Vect
%access public export

syntax "[(" [x]"$*"[map]")]" = pure (\e => (x ** e)) <*> map x
syntax "[(" [x]"**"[val]")]" = pure (\e => (x ** e)) <*> val

syntax "[(" [l] "," [r] ")]" = (| 
     (pure (\e => (l,e)) <*> r),
     (pure (\e => (e,r)) <*> l),
     [|MkPair l r |] |)
                              
private
t1Help : (x : Nat) -> Maybe (Z=x)
t1Help x with( decEq Z x)
  | Yes t = Just t
  | No _ = Nothing

private
t2Help : Nat -> Maybe(x:Nat ** Z=x) 
t2Help x = [( x $* t1Help )]

private
t2 : Maybe (Nat, String)
t2 = [( Z , Just "a" )]

private 
t3 : Maybe (Nat, String)
t3 = [( Nothing, "a")]

