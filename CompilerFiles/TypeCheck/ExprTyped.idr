module ExprTyped
import Data.Vect
import Data.List
import Data.HVect
%access public export

data C0Type = C0Int 
            | C0Str 
            | Void

data AccessMod = Public



data TermTyped : C0Type -> Type where
  MkIntLit : Int -> TermTyped C0Int
  MkStrLit : String -> TermTyped C0Str
  ApplyFunc : (name: String) -> (rtn : C0Type)-> Vect n (t:C0Type ** TermTyped t) -> TermTyped rtn

data ExprTyped : C0Type -> Type where
  Return : TermTyped t -> ExprTyped t

record FuncTyped (rtn:C0Type) (args: Vect n C0Type) where
  constructor MkFuncTyped
  access : AccessMod
  name : String
  paramNames : Vect n String
  body : List (t : C0Type ** ExprTyped t)

arity : FuncTyped {n=n} _ _ -> Nat
arity {n} = const n

data SigFunc : Type where
  SFunc : (t:C0Type) -> (args : Vect n C0Type) -> (FuncTyped t args) -> SigFunc

rtnTy : SigFunc -> C0Type
rtnTy (SFunc t _ _) = t

argTy : SigFunc -> (n:Nat ** Vect n C0Type)
argTy (SFunc _ s _) = ( _ ** s)

data IsMain : SigFunc -> List SigFunc -> Type where
  EmptyMain : Elem (SFunc C0Int a (MkFuncTyped Public "main" [] b )) fs -> 
              IsMain (SFunc C0Int a (MkFuncTyped Public "main" [] b )) fs

mainFunc : IsMain f fs -> SigFunc
mainFunc {f} = const f

mainElem : IsMain f fs -> Elem f fs
mainElem (EmptyMain el) = el


data ProgramTyped : Type where
  MkProgram : (fs : List SigFunc) -> IsMain f fs -> ProgramTyped 

DecEq C0Type where
  decEq C0Int C0Int = Yes Refl
  decEq C0Int _ = No (believe_me()) --Find a better way to build these trivial DecEq types
  decEq C0Str C0Str = Yes Refl
  decEq C0Str _ = No (believe_me())
  decEq Void Void = Yes Refl
  decEq Void _ = No (believe_me())

DecEq AccessMod where
  decEq Public Public = Yes Refl

Show C0Type where
  show C0Int = "C0Int"
  show C0Str = "C0Str"
  show Void = "void type"

Show AccessMod where
  show Public = "Public"


Show (TermTyped t) where
  show (MkIntLit x) = "IntLit: " ++ show x
  show (MkStrLit x) = "StrLit: " ++ show x
  show (ApplyFunc n r vals) =  assert_total $
    n ++ "(" ++ foldl 
          (\a,x => a ++ "," ++ show (snd x))
          "" vals ++ ")"

Show (ExprTyped t) where
  show (Return s) = "return " ++ show s

Show (FuncTyped r a)  where
  show x = "access : " ++ (show $ access x) ++    "\n" ++
           "rtnTy : " ++ (show r)              ++ "\n" ++
           "name : " ++ (show $ name x) ++        "\n" ++
           "params: " ++ (show a)          ++     "\n" ++
           "body: " ++ (show $ body x) 
Show SigFunc where
  show (SFunc _ _ f) = show f

Show ProgramTyped where
  show (MkProgram funcs _) = "funcs : " ++ (show funcs) 
  
