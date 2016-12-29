module Typed
import Data.Vect
import Data.List
import Data.HVect
import TypeCheck.CorePrgm
import Util.RootUtil
%access public export

data StatGen : (termT : C0Type -> Type) -> Type where
  Return : (t:C0Type) -> termT t -> StatGen termT

data TermTyped : C0Type -> Type where
  MkIntLit : Int -> TermTyped C0Int
  MkStrLit : String -> TermTyped C0Str
  ApplyFunc : (name: String) -> (rtn : C0Type)-> Vect n (t:C0Type ** TermTyped t) -> TermTyped rtn

StatTyped : Type
StatTyped = StatGen TermTyped

FuncTyped : Type
FuncTyped = QFunc StatTyped

ProgramTyped : Type
ProgramTyped = Program FuncTyped Void NoFacts

Show (TermTyped t) where
  show (MkIntLit x) = "IntLit: " ++ show x
  show (MkStrLit x) = "StrLit: " ++ show x
  show (ApplyFunc n r vals) =  assert_total $
    n ++ "(" ++ foldl 
          (\a,x => a ++ "," ++ show (snd x))
          "" vals ++ ")"

Show StatTyped where
  show (Return _ s) = "return " ++ show s
