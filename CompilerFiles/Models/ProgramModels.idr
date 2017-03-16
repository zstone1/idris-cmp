module ProgramModels

interface Traversable coll => FuncSig (a : (pty, accessTy : Type) -> (rtnDecor, argDecor, coll : Type -> Type) -> Type) 
  (pty : Type)
  (accessTy: Type) 
  (rtnDecor : Type -> Type)  
  (argDecor : Type -> Type) 
  (coll : Type -> Type) where
  getAccess : a pty accessTy rtnDecor argDecor coll -> accessTy
  getRtn :  a pty accessTy rtnDecor argDecor coll -> rtnDecor pty
  getName :  a pty accessTy rtnDecor argDecor coll -> String
  getArgs : a pty accessTy rtnDecor argDecor coll -> coll (argDecor pty)

record PFuncSig (pty : Type) (accessTy: Type) (rtnDecor : Type -> Type)  (argDecor : Type -> Type) (coll : Type -> Type) where
  constructor MkPFuncSig
  access : accessTy
  rtn : rtnDecor pty
  name : String
  args : coll (argDecor pty)

Traversable coll => FuncSig PFuncSig pty accessTy rtnDecor argDecor coll where
  getAccess = access
  getRtn = rtn
  getName = name
  getArgs = args


--data Prgm : (funcTy, constTy: Type) ->  (meta : (List funcTy) -> (List constTy) -> Type) -> Type  where
--   MkPrgm : {funcTy,constTy  : Type} ->
--            {meta : (List funcTy) -> (List constTy) -> Type} ->
--            (funcs : List funcTy) -> 
--            (consts : List constTy) -> 
--            (facts : meta funcs consts) ->
--            Program funcTy constTy meta

