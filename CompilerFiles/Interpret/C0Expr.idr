module C0Expr
import Data.Fin
import Data.Vect
%access public export

data C0Type = C0Int 
            | C0Bool 
            | C0Str 
            | C0Char

data Access = Public | Private

Show C0Type where
  show C0Int = "C0Int"
  show C0Bool = "C0Bool"
  show C0Str = "C0Str"
  show C0Char = "C0Char"

|||An untyped representation of the contents of a function
data ExprPrim : Type where
  MkIntLit : Int -> ExprPrim
  MkStrLit : String -> ExprPrim

data ExprTyped : Type where

Show ExprPrim where
  show (MkIntLit x) = "intLit: " ++ show x
  show (MkStrLit x) = "strLit: " ++ show x

|||An untyped represetnation of the metadata of a function
record FuncPrim where 
  constructor MkFuncPrim
  access : String
  rtnTy : String
  name : String
  params : Vect n (String, String)
  defn : ExprPrim

record FuncTyped where
  constructor MkFuncTyped
  access : Access
  rtnTy : C0Type
  name : String
  params : Vect n (C0Type, String)
  defn : ExprTyped

Show FuncPrim where
  show x = "access : " ++ (show $ access x) ++
           "rtnTy : " ++ (show $ rtnTy x) ++
           "name : " ++ (show $ name x) ++
           "params: " ++ (show $ params x) ++
           "defn: " ++ (show $ defn x) 

record ProgramPrim where
  constructor MkProgramPrim
  funcs : List FuncPrim
  
Show ProgramPrim where
  show x = "funcs : " ++ (show $ funcs x)









