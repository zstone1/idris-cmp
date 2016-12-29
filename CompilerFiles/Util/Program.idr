module Program
%access public export

data Program : (funcTy, constTy: Type) ->  (meta : (List funcTy) -> (List constTy) -> Type) -> Type  where
  MkProgram : {funcTy,constTy  : Type} ->
              {meta : (List funcTy) -> (List constTy) -> Type} ->
              (funcs : List funcTy) -> 
              (consts : List constTy) -> 
              (facts : meta funcs consts) ->
              Program funcTy constTy meta
funcs : Program f c m -> List f
funcs (MkProgram fs _ _ ) = fs

consts : Program f c m -> List c 
consts (MkProgram _ cs _) = cs

(Show funcTy, Show constTy) => Show (Program funcTy constTy meta) where
  show (MkProgram fs cs _) = "funcs : "++ show fs ++ "\n" ++ "consts : " ++show cs

Show Void where
  show x impossible

data NoFacts : a -> b -> Type where
  Nothing : NoFacts a b

