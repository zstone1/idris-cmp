module FuncSigTypes
import Util.RootUtil
import Models.RootModels

public export
data ReturnTy : Type -> Type where
  VoidRtn : ReturnTy t 
  SomeRtn : t -> ReturnTy t

public export
InitPassSigTys : FuncSigTypes
InitPassSigTys = MkFunSigTypes 
  String
  BuiltInType
  AccessMod
  ReturnTy
  (Pair String)

public export
InitPassSig : Type
InitPassSig = FuncSig InitPassSigTys

parseReturnTy : String -> Comp (ReturnTy BuiltInType)
parseReturnTy "void" = [| VoidRtn |]
parseReturnTy s = [| SomeRtn (parseBuiltInType s) |]

parseArg : (String, String) -> Comp (String, BuiltInType)
parseArg = _2 parseBuiltInType

firstPassSig : ParsedFuncSig -> Comp {env} InitPassSig
firstPassSig (MkFuncSig a rtn name args) = 
  [| MkFuncSig (parseAccess a) (parseReturnTy rtn) (pure name) (traverse parseArg args)|]

export
typeFuncSigs : Program a ParsedFuncSigTys c -> Comp (Program a InitPassSigTys c)
typeFuncSigs = traverseProgram $ traverseModuleFunc $ firstPassSig




