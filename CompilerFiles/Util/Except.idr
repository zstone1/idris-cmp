module Error

import Control.Monad.Trans
import Data.Fin
%access public export

eitherLift : (f:y -> z) -> Either x y -> Either x z
eitherLift f e = case e of 
                      Left a => Left a
                      Right b => Right (f b)
eitherLiftFunc : Either x (y -> z) -> Either x y -> Either x z
eitherLiftFunc f e = case (f,e) of 
                      (Left a, _) => Left a
                      (_, Left a) => Left a
                      (Right f, Right b) => Right (f b)

||| A computation which short circuits on thrown errors.
interface Monad m => MonadExcept errType (m:Type -> Type)| m where 
  |||throw an error causing the operation to short circuit.
  throw : errType -> m ()
  |||determine the current state of the operation.
  read : m a -> Either errType a

data ExceptT : (errType : Type) ->  (m : Type -> Type) -> (a : Type) -> Type where
  MkExcept : m (Either errType a) -> ExceptT errType m a

implementation Functor f => Functor (ExceptT errType f) where
  map fn (MkExcept ex) =
    let lifted = eitherLift fn in 
      MkExcept (map lifted ex)

implementation Applicative f => Applicative (ExceptT e f) where
  pure a = MkExcept $ pure $ Right a
  (MkExcept a) <*> (MkExcept b) = MkExcept (pure eitherLiftFunc <*> a <*> b) 
  
implementation Monad m => Monad (ExceptT errType m) where
  (MkExcept x) >>= f = MkExcept $ do y <- x
                                     case y of 
                                          Left a => pure (Left a)
                                          Right b => let (MkExcept c) = f b in c
---- 
--implementation Monad m => MonadExcept errType (ExceptT errType m) where
--  throw e = Fail e 
--  read (Fail errVal) = Left errVal
--  read (Success sVal) = Right sVal
--
--
--
--
--
