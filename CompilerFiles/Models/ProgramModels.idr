module ProgramModels
import Data.Vect
import Util.RootUtil
%access public export

--Function types

record FuncSigTypes where
  constructor MkFunSigTypes
  nameTy : Type
  pty : Type
  accessTy : Type
  rtnDecor : Type -> Type
  argDecor : Type -> Type

record FuncSig (tys : FuncSigTypes) where
  constructor MkFuncSig
  access : accessTy tys
  rtn : (rtnDecor tys)  (pty tys)
  name : nameTy tys
  args : Vect n ((argDecor tys) (pty tys)) 

arity : FuncSig t -> Nat
arity (MkFuncSig {n} _ _ _ _ ) = n

record StatementTypes where
  constructor MkStagementTypes
  valTypes : List Type
  contextTy : Type

record Statement (tys : StatementTypes) where  
  constructor MkStatement
  val : DepUnion (valTypes tys)

-- terms

data IntLiteral : Type  where
  MkIntLit : Nat -> IntLiteral

data StringLiteral : Type where
  MkStringLit : String -> StringLiteral

record FuncApplication (argTy : Type) where
  constructor MkFuncApplication
  name : String
  args : List argTy

Term : List Type -> Type
Term l = DepUnion l 

--constants

--modules
record Mod (statTy: Type) (funcTy : FuncSigTypes)where
   constructor  MkMod
   name : String
   funcs : List (FuncSig funcTy, List (statTys))
--   constants : List constTy
--   customTypes : List customTy

record Program (statTy: Type) (funcTy : FuncSigTypes) where
  constructor MkProgram 
  modules : List (Mod statTy funcTy)




