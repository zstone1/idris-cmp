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

record IntLiteral where
  constructor MkIntLit 
  intVal : Int

record StringLiteral where
  constructor MkStringLit 
  strVal : String 

record FuncApplication (argTy : Type) where
  constructor MkFuncApplication
  name : String
  args : List argTy

Term : List Type -> Type
Term l = DepUnion l 

--constants

--modules
record Mod (statTy: Type) (funcTy : FuncSigTypes) (constTy : Type) where
   constructor  MkMod
   name : String
   funcs : List (FuncSig funcTy, List (statTy))
   constants : List constTy
--   customTypes : List customTy

record Program (statTy: Type) (funcTy : FuncSigTypes) (constTy : Type) where
  constructor MkProgram 
  modules : List (Mod statTy funcTy constTy)

--lenses

traverseProgram : Applicative f => (Mod a b c -> f (Mod x y z)) -> Program a b c -> f(Program x y z)
traverseProgram m p = [| MkProgram (traverse m (modules p)) |]

traverseModule : Applicative f => 
                     ((FuncSig b, List a) -> f (FuncSig y, List x)) ->
                     (String -> f String) ->
                     (c -> f z) ->
                     Mod a b c -> f(Mod x y z)
traverseModule fUpdate nUpdate cUpdate  p = 
  [| MkMod (nUpdate (name p)) (traverse fUpdate (funcs p)) (traverse cUpdate (constants p))|]

traverseModuleFunc : Applicative f => (FuncSig b -> f (FuncSig y)) -> Mod a b c -> f (Mod a y c)
traverseModuleFunc m = traverseModule (_1 m) pure pure 

traverseModuleConsts : Applicative f => (c -> f z) -> Mod a b c -> f (Mod a b z)
traverseModuleConsts m = traverseModule pure pure m

traverseModuleStats : Applicative f => (a -> f x) -> Mod a b c -> f (Mod x b c)
traverseModuleStats m = traverseModule (_2 (traverse m)) pure pure

traverseModuleName : Applicative f => (String -> f String) -> Mod a b c -> f(Mod a b c)
traverseModuleName m = traverseModule pure m pure











