module Error

import Data.Fin
%access public export
data ErrorM : (errType:Type) -> (ty:Type) -> Type where 
  Success: ty -> ErrorM errType ty 
  Fail: errType -> ErrorM errType ty
implementation Functor (ErrorM e) where
  map fn (Fail s) = (Fail s)
  map fn (Success t) = Success(fn t)

implementation Applicative (ErrorM e) where
  pure a = Success a
  (Fail s) <*> _ = Fail s
  _ <*> (Fail s) = Fail s
  (Success x) <*> (Success y) = Success (x y)
  
implementation Monad (ErrorM e) where
  (Fail s) >>= f = Fail s
  (Success x) >>= f =  f x

