module ProgramModels

data PFuncSig : {pty, accessTy: Type} -> {rtnDecor, argDecor, coll : Type -> Type} -> Type where
  MkFuncSig :   Traversable coll =>
                {pty, accessTy: Type} ->
                {rtnDecor, argDecor, coll : Type -> Type} ->
                (access : accessTy) ->
                (rtn : rtnDecor pty) ->
                (name : String) ->
                (args : coll (argDecor pty)) ->
                PFuncSig 




--data Prgm : (funcTy, constTy: Type) ->  (meta : (List funcTy) -> (List constTy) -> Type) -> Type  where
--   MkPrgm : {funcTy,constTy  : Type} ->
--            {meta : (List funcTy) -> (List constTy) -> Type} ->
--            (funcs : List funcTy) -> 
--            (consts : List constTy) -> 
--            (facts : meta funcs consts) ->
--            Program funcTy constTy meta

