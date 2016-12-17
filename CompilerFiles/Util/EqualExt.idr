module EqualExt
import Util.PreorderReasoningExt
%access export

|||Merges two equalities by applying the left and right sides to the given 2-ary function.
MergeEqualities : {x,y,a,b:t} -> (f: t->t->u) -> (x = y) -> (a = b) -> (f x a) = (f y b)
MergeEqualities {x}{y}{a}{b} f xy ab =
  (f x a) =[ ab ]=
  (f x b) =[ xy ]=
  (f y b) QED

