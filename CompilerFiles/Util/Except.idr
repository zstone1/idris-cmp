module Error

import Control.Monad.Identity
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

data ExceptT : (errType : Type) ->  (m : Type -> Type) -> (a : Type) -> Type where
  MkExcept : m (Either errType a) -> ExceptT errType m a

throw : Applicative m => e -> ExceptT e m a 
throw e = MkExcept( pure ( Left e))

run : ExceptT e f a -> f (Either e a)
run x = let (MkExcept y) = x in y

catch : Monad m => ExceptT e m a -> (e -> ExceptT e m a ) -> ExceptT e m a
catch x f = MkExcept( do y <- run x
                         case y of
                              Left a => run $ f a
                              Right b => pure $ Right b)

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
                                          Right b => run $ f b 

implementation MonadTrans (ExceptT e) where
  lift x = MkExcept ( do y <- x
                         pure $ Right y)

Except : Type -> Type -> Type 
Except e a = ExceptT e Identity a
