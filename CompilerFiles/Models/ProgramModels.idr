module ProgramModels
import Data.Vect

interface Traversable coll => FuncSig (a : Type)
  (pty : Type)
  (accessTy: Type) 
  (rtnDecor : Type -> Type)  
  (argDecor : Type -> Type) 
  (coll : Type -> Type) where
  getAccess : a -> accessTy
  getRtn : a -> rtnDecor pty
  getName : a -> String
  getArgs : a -> coll (argDecor pty)

record PFuncSig (pty : Type) (accessTy: Type) (rtnDecor : Type -> Type)  (argDecor : Type -> Type) (coll : Type -> Type) where
  constructor MkPFuncSig
  access : accessTy
  rtn : rtnDecor pty
  name : String
  args : coll (argDecor pty)

NaryFuncSig : Show t => t -> Type 
NaryFuncSig {t} = ?foo

-- Forall t (ForAll a b c d coll ( t a b c d coll `implements` FuncSig) => (n : Nat ** a b c d (Vect n)) ` implements FuncSig)

--implementation (Traversable coll => FuncSig t a b c d coll) => FuncSig (n:Nat ** (t a b c d (Vect n))) a b c d (Vect n) where

--implementation FuncSig (NaryFuncSig pty accessTy rtnDecor argDecor) pty accessTy rtnDecor argDecor (Vect n) where
--  getAccess = access . snd

--data Prgm : (funcTy, constTy: Type) ->  (meta : (List funcTy) -> (List constTy) -> Type) -> Type  where
--   MkPrgm : {funcTy,constTy  : Type} ->
--            {meta : (List funcTy) -> (List constTy) -> Type} ->
--            (funcs : List funcTy) -> 
--            (consts : List constTy) -> 
--            (facts : meta funcs consts) ->
--            Program funcTy constTy meta

