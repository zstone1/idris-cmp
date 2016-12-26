module EffectExt
import public Effects
import public Effect.Monad
import public Effect.Exception
import public Effect.StdIO
%access public export

implicit
getEff : MonadEffT xs m a  -> EffM m a xs (\v => xs)
getEff (MkMonadEffT x) = x


CompErr : EFFECT 
CompErr = EXCEPTION String

CompEffs : List EFFECT
CompEffs = [CompErr]

Comp : {ty : Type -> Type} -> {default CompEffs l:List EFFECT}  -> Type -> Type
Comp {ty} {l} t = EffM ty t l (\v => l)
