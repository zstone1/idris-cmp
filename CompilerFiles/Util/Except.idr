module Error

import Control.Monad.Identity
import Control.Monad.Trans
import Data.Fin
%access public export

%access private
eitherLift : (f:y -> z) -> Either x y -> Either x z
eitherLift f e = case e of 
                      Left a => Left a
                      Right b => Right (f b)
%access private
eitherLiftFunc : Either x (y -> z) -> Either x y -> Either x z
eitherLiftFunc f e = case (f,e) of 
                      (Left a, _) => Left a
                      (_, Left a) => Left a
                      (Right f, Right b) => Right (f b)
|||Adds short circuiting behavior to a monad.
data ExceptT : (errType : Type) ->  (m : Type -> Type) -> (a : Type) -> Type where
  MkExcept : m (Either errType a) -> ExceptT errType m a

|||Short circuit with the given error.
throw : Applicative m => e -> ExceptT e m a 
throw e = MkExcept( pure ( Left e))

|||Get the result of the monad operation. The left contains the
|||error and the right contains the success.
run : ExceptT e f a -> f (Either e a)
run x = let (MkExcept y) = x in y

|||Runs the catch clause if the first operation threw.
catch : Monad m => ExceptT e m a -> (e -> ExceptT e m a ) -> ExceptT e m a
catch x f = MkExcept $ do Left a <- run x | Right b => pure (Right b)
                          run (f a)

implementation Functor f => Functor (ExceptT errType f) where
  map fn (MkExcept ex) =
    let lifted = eitherLift fn in 
      MkExcept (map lifted ex)

implementation Applicative f => Applicative (ExceptT e f) where
  pure a = MkExcept $ pure $ Right a
  (MkExcept a) <*> (MkExcept b) = MkExcept (pure eitherLiftFunc <*> a <*> b) 
  
implementation Monad m => Monad (ExceptT errType m) where
  (MkExcept x) >>= f = MkExcept $ do Right b <- x | Left a => pure (Left a)
                                     run (f b)

implementation MonadTrans (ExceptT e) where
  lift x = MkExcept ( do y <- x
                         pure $ Right y)

|||A monad that short circuits on exception.
Except : Type -> Type -> Type 
Except e a = ExceptT e Identity a
