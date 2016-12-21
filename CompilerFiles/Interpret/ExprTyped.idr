module ExprTyped
import Data.Vect
%access public export

data C0Type = C0Int 
            | C0Str 

data AccessMod = Public

data ExprTyped : C0Type -> Type where
  MkIntLit : Int -> ExprTyped C0Int
  MkStrLit : String -> ExprTyped C0Str

record FuncTyped where
  constructor MkFuncTyped
  access : AccessMod
  name : String
  params : Vect n (C0Type, String)
  defn : (rtnTy : C0Type ** ExprTyped rtnTy)

record ProgramTyped where
  constructor MkProgram
  funcs : List FuncTyped

Uninhabited (C0Int = C0Str) where
  uninhabited Refl impossible

DecEq C0Type where
  decEq C0Int C0Int = Yes Refl
  decEq C0Str C0Str = Yes Refl
  decEq C0Int C0Str = No absurd
  decEq C0Str C0Int = No (absurd . sym)

Show C0Type where
  show C0Int = "C0Int"
  show C0Str = "C0Str"

Show AccessMod where
  show Public = "Public"

Show (ExprTyped t) where
  show (MkIntLit x) = "IntLit: " ++ show x
  show (MkStrLit x) = "StrLit: " ++ show x

Show FuncTyped where
  show x = "access : " ++ (show $ access x) ++    "\n" ++
           "rtnTy : " ++ (show $ fst $ defn x) ++ "\n" ++
           "name : " ++ (show $ name x) ++        "\n" ++
           "params: " ++ (show $ params x) ++     "\n" ++
           "defn: " ++ (show $ snd $ defn x) 

Show ProgramTyped where
  show x = "funcs : " ++ (show $ funcs x)

