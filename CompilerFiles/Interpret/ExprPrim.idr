module ExprPrim
import Util.RootUtil
import Data.Fin
import Data.Vect
%access public export

data TermPrim : Type where
  MkIntLit : Int -> TermPrim
  MkStrLit : String -> TermPrim
  ApplyFunc : (fname: String) -> Vect n TermPrim -> TermPrim

|||An untyped representation of the contents of a function
data StatPrim : Type where
  Return : TermPrim -> StatPrim
  ExecTerm : TermPrim ->  StatPrim
  Condition : TermPrim -> List StatPrim -> StatPrim
  --Asign
  --While

|||An untyped represetnation of the metadata of a function
record FuncPrim where 
  constructor MkFuncPrim
  access : String
  rtnTy : String
  name : String
  params : Vect n (String, String)
  body : List StatPrim

ProgramPrim : Type
ProgramPrim = Program FuncPrim Void NoFacts 
 
Show TermPrim where
  show (MkIntLit x) = "intLit: " ++ show x
  show (MkStrLit x) = "strLit: " ++ show x
  show (ApplyFunc n args) = assert_total (n ++ show args)

Show StatPrim where
  show (Return t) = "return "++ show t
  show (ExecTerm t) = show t
  show (Condition guard bod) = assert_total$ "if (" ++show guard++") then " ++ show bod

Show FuncPrim where
  show x = "access : " ++ (show $ access x) ++ "\n" ++
           "rtnTy : " ++ (show $ rtnTy x) ++   "\n" ++
           "name : " ++ (show $ name x) ++     "\n" ++
           "params: " ++ (show $ params x) ++  "\n" ++
           "body: " ++ (show $ body x) 
 






