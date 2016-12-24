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

arity : FuncTyped -> Nat
arity f = length $ params f

MainName : String
MainName = "main"

data IsMain : FuncTyped -> Type where
  EmptyMain : IsMain (MkFuncTyped Public MainName [] (C0Int ** _))

getMainFunc : IsMain f -> FuncTyped
getMainFunc {f} = const f

record ProgramTyped where
  constructor MkProgram
  funcs : List FuncTyped
  main : IsMain f

DecEq C0Type where
  decEq C0Int C0Int = Yes Refl
  decEq C0Int _ = No (believe_me()) --Find a better way to build these trivial DecEq types
  decEq C0Str C0Str = Yes Refl
  decEq C0Str _ = No (believe_me())

DecEq AccessMod where
  decEq Public Public = Yes Refl

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

