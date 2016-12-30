module CorePrgm
import Util.RootUtil
%access public export

data C0Type = C0Int 
            | C0Str 
--            | Void

data AccessMod = Public

data StatGen : (termT : ty -> Type) -> Type where
  Return : (t: ty) -> termT t -> StatGen termT
  Execute : (name : String) -> (Vect n (t: (ty) ** termT t)) -> StatGen termT

record FuncGen (statT : Type) (rtn:C0Type) (args: Vect n C0Type) where
  constructor MkFuncGen
  access : AccessMod
  name : String
  paramNames : Vect n String
  body : List statT

arity : FuncGen {n=n} _ _ _ -> Nat
arity {n} = const n

data QFunc : (statTy : Type) -> Type where
  MkFunc : {statTy : Type} -> 
          {rtnTy : C0Type} -> 
          {args : Vect n C0Type} -> 
          (FuncGen statTy rtnTy args) -> 
          QFunc statTy

rtnTy : QFunc _ -> C0Type
rtnTy (MkFunc {rtnTy} _) = rtnTy

argTy : QFunc _ -> (n:Nat ** Vect n C0Type)
argTy (MkFunc {args} _) = ( _ ** args)

data IsMain : QFunc statTy -> List (QFunc statTy) -> Type where
  EmptyMain : Elem (MkFunc {rtnTy=C0Int} (MkFuncGen Public "main" [] b )) fs -> 
              IsMain (MkFunc {rtnTy= C0Int} (MkFuncGen Public "main" [] b )) fs

DecEq C0Type where
  decEq C0Int C0Int = Yes Refl
  decEq C0Int _ = No (believe_me()) --Find a better way to build these trivial DecEq types
  decEq C0Str C0Str = Yes Refl
  decEq C0Str _ = No (believe_me())
--  decEq Void Void = Yes Refl
--  decEq Void _ = No (believe_me())

DecEq AccessMod where
  decEq Public Public = Yes Refl

Show C0Type where
  show C0Int = "C0Int"
  show C0Str = "C0Str"
--  show Void = "void type"

Show AccessMod where
  show Public = "Public"


(Show statT) => Show (FuncGen statT r a)  where
  show x = "access : " ++ (show $ access x) ++    "\n" ++
           "rtnTy : " ++ (show r)              ++ "\n" ++
           "name : " ++ (show $ name x) ++        "\n" ++
           "params: " ++ (show a)          ++     "\n" ++
           "body: " ++ (show $ body x) 
(Show statT) => Show (QFunc statT) where
  show (MkFunc f) = show f
