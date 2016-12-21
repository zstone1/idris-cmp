module EitherExt
%access public export

mapl : (f: a -> c) -> Either a b -> Either c b
mapl f e with (e)
  | Left x = Left $ f x
  | Right x = Right x

mapr : (f: b -> c) -> Either a b -> Either a c
mapr f e with (e)
  | Left x = Left x
  | Right x = Right $ f x

