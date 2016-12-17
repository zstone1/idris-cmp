module PreorderReasoningExt
import public Syntax.PreorderReasoning
%access public export

toLteRefl : (x=y) -> (LTE x y)
toLteRefl o = rewrite o in lteRefl

syntax [from] "=[" [prf] "]=" [to] = (from) ={ (|
                    prf,
                    sym prf,
                    rewrite prf in Refl,
                    rewrite prf in lteRefl 
                    |) }= (to)
qed : (x : Nat) -> LTE x x
qed x = lteRefl

step : (x:Nat) -> (LTE x y) -> (LTE y z) -> (LTE x z)
step x p1 p2 = lteTransitive p1 p2


