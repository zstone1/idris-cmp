module PairExt
import Data.Vect
%access public export

liftDPair : Applicative t => {dep : a -> Type} -> 
                             (map : (a':a) -> t (dep a')) ->
                             a -> 
                             t (a' : a ** dep a')
liftDPair {dep} map x = pure (\e => (x ** e)) <*> map x

syntax "[(" [left]"$*"[right] ")]" = liftDPair right left



liftlPair : Applicative t => a -> t b -> t(a, b)
liftlPair l r = pure (\e => (l, e)) <*> r

liftrPair : Applicative t => t a -> b -> t(a, b)
liftrPair l r = pure (\e => (e, r)) <*> l

syntax "[(" [left] "," [right] ")]" = (|liftlPair left right, 
                                        liftrPair left right|)
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

