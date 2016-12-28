module ExprTyped
import Data.Vect
import Data.List
%access public export

data C0Type = C0Int 
            | C0Str 

data AccessMod = Public

mutual 
  data TermTyped : C0Type -> Type where
    MkIntLit : Int -> TermTyped C0Int
    MkStrLit : String -> TermTyped C0Str
    ApplyFunc : FuncTyped rtn arTy -> MatchArgTy arTy arVal -> TermTyped rtn

  data MatchArgTy : (Vect n C0Type) -> (Vect n (t:C0Type ** TermTyped t)) -> Type where
    Vacuous : MatchArgTy [] []
    Next : (t:C0Type) -> (v:TermTyped t) -> MatchArgTy {n=k} ts vs ->  
           MatchArgTy {n=S k} (t::ts) ((t**v) :: vs)

  record FuncTyped (rtn:C0Type) (args: Vect n C0Type) where
    constructor MkFuncTyped
    access : AccessMod
    name : String
    paramNames : Vect n String
    body : List (t : C0Type ** ExprTyped t)

  data ExprTyped : C0Type -> Type where
    Return : TermTyped t -> ExprTyped t

arity : FuncTyped {n=n} _ _ -> Nat
arity {n} = const n

getArgs : MatchArgTy ts vs -> (n ** Vect n (t:C0Type ** TermTyped t))
getArgs {vs} = const (_ ** vs)

data SigFunc : Type where
  SFunc : (t:C0Type) -> (args : Vect n C0Type) -> (FuncTyped t args) -> SigFunc

rtnTy : SigFunc -> C0Type
rtnTy (SFunc t _ _) = t

argTy : SigFunc -> (n:Nat ** Vect n C0Type)
argTy (SFunc _ s _) = ( _ ** s)

data IsMain : SigFunc -> List SigFunc -> Type where
  EmptyMain : Elem (SFunc r a (MkFuncTyped Public "main" [] b )) fs -> 
              IsMain (SFunc r a (MkFuncTyped Public "main" [] b )) fs

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

DecEq AccessMod where
  decEq Public Public = Yes Refl

Show C0Type where
  show C0Int = "C0Int"
  show C0Str = "C0Str"

Show AccessMod where
  show Public = "Public"

Show (TermTyped t) where
  show (MkIntLit x) = "IntLit: " ++ show x
  show (MkStrLit x) = "StrLit: " ++ show x
  --Mutually recursive type as dependent parameter of list. Idris is not that clever
  show (ApplyFunc (MkFuncTyped _ n _ _) val) = assert_total
    (show n ++ " " ++  show (getArgs val))

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
  
