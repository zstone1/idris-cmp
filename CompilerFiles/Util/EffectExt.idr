module EffectExt
import public Effects
import public Effect.Monad
import public Effect.Exception
import public Effect.StdIO
import public Effect.State
%access public export

implicit
getEff : MonadEffT xs m a  -> EffM m a xs (\v => xs)
getEff (MkMonadEffT x) = x


CompErr : EFFECT 
CompErr = EXCEPTION String

--CompNamer : EFFECT
--CompNamer = STATE Nat

CompEffs : List EFFECT
CompEffs = [CompErr,'Namer ::: STATE Nat]

nextName : EffM ty String ['Namer ::: STATE Nat] (\v=> ['Namer :::STATE Nat])
nextName = do
  next <- 'Namer :- get
  'Namer :- put (S next)
  pure  ("_"++show next)

Comp : {ty : Type -> Type} -> {default CompEffs l:List EFFECT}  -> Type -> Type
Comp {ty} {l} t = EffM ty t l (\v => l)






