module EffectExt
import public Effects
import public Effect.Monad
%access public export

implicit
getEff : MonadEffT xs m a -> EffM m a xs (\v => xs)
getEff (MkMonadEffT x) = x
