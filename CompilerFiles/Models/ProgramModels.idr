module ProgramModels
import Data.Vect
import Util.RootUtil

record Class where
  constructor MkClass 
  students : Vect n String

Foo : Class -> String
Foo (MkClass {n} x) = show x

record FuncSig where
  constructor MkFuncSig
  {pty : Type}
  {rtnDecor : Type -> Type}
  {argDecor : Type -> Type}
  access : accessTy
  rtn : rtnDecor pty
  name : nameTy
  args : Vect n (argDecor pty) 

arity : FuncSig -> Nat
arity (MkFuncSig {n} _ _ _ _ ) = n

record Statement where
  constructor MkStatement
  {l : List Type}
  val : DepUnion l
  scope : scopeTy  

record Func where
  constructor MkFunc
  sig : FuncSig
  stat : Vect n Statement

record Mod where
   constructor  MkMod
   name : String
   funcs : List Func
   constants : List constTy
   customTypes : List customTy

record Program where
  constructor MkProgram 
  modules : List Mod
