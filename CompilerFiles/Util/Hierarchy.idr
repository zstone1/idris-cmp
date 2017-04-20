module Hierarchy

interface Hierarchy (a: Nat -> Type) where
  cumulativity : {complexity:Nat} -> a complexity -> a (S complexity)

private
upTo : Hierarchy a => (n,m : Nat) -> a n -> a (m + n)
upTo n Z a = a
upTo n (S m) a = cumulativity (upTo n m a)
    
