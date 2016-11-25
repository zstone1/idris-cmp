module Error

import Data.Fin
import Prelude.Either
import Control.Monad.Except
%access public export
interface Monad m => ExceptionT expTy (m:Type ->Type)|m where 
  Success: t -> ErrorM t 
  Fail: e -> 
--implementation Functor (ErrorM e) where
--  map fn (Fail s) = (Fail s)
--  map fn (Success t) = Success(fn t)
--
--implementation Applicative (ErrorM {e=e}) where
--  pure a = Success a
--  (Fail s) <*> _ = Fail s
--  _ <*> (Fail s) = Fail s
--  (Success x) <*> (Success y) = Success (x y)
--  
--implementation Monad (ErrorM {e=e}) where
--  (Fail s) >>= f = Fail s
--  (Success x) >>= f =  f x
--
