module C0Expr
import Data.Fin
import Data.Vect
%access public export

data C0Type = C0Int 
            | C0Bool 
            | C0Str 
            | C0Char
            | C0Func C0Type C0Type

Show C0Type where
  show C0Int = "C0Int"
  show C0Bool = "C0Bool"
  show C0Str = "C0Str"
  show C0Char = "C0Char"
  show (C0Func a b) = (show a) ++ " -> " ++ (show b)

using(C: Vect n C0Type)

  data HasType : (i : Fin n) -> Vect n C0Type -> C0Type -> Type where
    Stop : HasType FZ (t :: C)  t
    Pop : HasType k C t -> HasType (FS k) (u::C) t

  data C0Expr : Vect n C0Type -> C0Type -> Type where
--    Var : HasType i C t -> C0Expr C t
    IntLit : Integer -> C0Expr C C0Int
--    StrLit : String -> C0Expr C C0Str
--    CharLit: Char -> C0Expr C C0Char
--    BoolLit: Bool -> C0Expr C C0Bool
    Func : C0Expr C (C0Func a b) -> C0Expr C a -> C0Expr C b
    
  dsl C0
      variable = Var
      index_first = Stop
      index_next = Pop
  

  Show (C0Expr c t) where
    show (IntLit i) = show i
    show (Func f a) = show f ++ " ( " ++ show a ++ " ) "



