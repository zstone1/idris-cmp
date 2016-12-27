module ExprPrim
import Data.Fin
import Data.Vect
%access public export

|||An untyped representation of the contents of a function
data ExprPrim : Type where
  MkIntLit : Int -> ExprPrim
  MkStrLit : String -> ExprPrim

|||An untyped represetnation of the metadata of a function
record FuncPrim where 
  constructor MkFuncPrim
  access : String
  rtnTy : String
  name : String
  params : Vect n (String, String)
  body : List ExprPrim


record ProgramPrim where
  constructor MkProgramPrim
  funcs : List FuncPrim


Show ExprPrim where
  show (MkIntLit x) = "intLit: " ++ show x
  show (MkStrLit x) = "strLit: " ++ show x

Show FuncPrim where
  show x = "access : " ++ (show $ access x) ++ "\n" ++
           "rtnTy : " ++ (show $ rtnTy x) ++   "\n" ++
           "name : " ++ (show $ name x) ++     "\n" ++
           "params: " ++ (show $ params x) ++  "\n" ++
           "body: " ++ (show $ body x) 
 
Show ProgramPrim where
  show x = "funcs : " ++ (show $ funcs x)









