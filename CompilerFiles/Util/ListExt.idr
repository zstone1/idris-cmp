module ListExt
import Data.List

data ElemZipped : t -> List t -> Type where
  ZippedBy : (a: List t) -> (x: t) -> (b: List t) -> ElemZipped x (a ++ (x::b))
 
asZipped : {t:Type} -> {l:List t} -> Elem x l  -> ElemZipped x l
asZipped {x} {l=x::xs} Here = ZippedBy [] x xs
asZipped {x} {l=y::xs} (There p) with (asZipped p)
  asZipped {x} {l=y::(a ++ (x::b))} (There p) | ZippedBy a x b = ZippedBy (y::a) x b
