module SyntaxExt
%access public export

infix 0 //
(//) : a -> (a -> b) -> b
(//) = flip apply
