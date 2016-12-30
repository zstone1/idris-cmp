module Link
import Util.RootUtil
import TypeCheck.CorePrgm
import TypeCheck.Typed
import TypeCheck.FactorConst
%access public export

SeedFuncs : List (String, C0Type, (n:Nat ** Vect n C0Type))
SeedFuncs = [("printf", C0Int, (_**[C0Str])), 
             ("plus", C0Str, (_**[C0Str, C0Str])),
             ("plus", C0Int, (_**[C0Int, C0Int]))]


data TermLink : C0Type -> Type where
  FromConst : ConstTyped t -> TermLink t
  ApplyFunc : (name :String) ->
              (rtn : C0Type) ->
              Vect n (t:C0Type ** TermLink t) ->
              TermLink rtn

StatLink : Type
StatLink = StatGen TermLink

FuncLink : Type
FuncLink = QFunc StatLink 

ProgramLink : Type 
ProgramLink = Program FuncLink (t:C0Type ** ConstTyped t) NoFacts

%access private

findFunc : {default (SeedFuncs) l : List (String, C0Type, (n:Nat ** Vect n C0Type))} -> 
           (name:String) -> (args:Vect n C0Type) -> Comp C0Type
findFunc name args {l=[]} = raise ("No function "++name++" with args "++show args++" could be found.")
findFunc {n} {l=(cname,t,(cn**cargs))::xs} name args with (decEq n cn)
  | (Yes p) with (decEq name cname, decEq args (rewrite p in cargs))
    | (Yes _, Yes _) = pure t
    | ( _, _) = findFunc {l=xs} name args
  | (No _) =    findFunc {l=xs} name args
 
linkTerm : (t: Maybe C0Type ** TermFactorConst t) -> Comp (t:C0Type ** TermLink t)
linkTerm (Just t ** ApplyFunc n args) impossible --Func return values are never known before linking
linkTerm (Nothing ** FromConst c) impossible --all const types discovered in the previous phase
linkTerm (Just t ** FromConst c) = pure (t ** FromConst c)
linkTerm (Nothing ** ApplyFunc n args) = do
  rec <- assert_total $ traverseM linkTerm args
  rtnTy <- findFunc n (map fst rec)
  pure $ (_ ** ApplyFunc n rtnTy rec)
  
linkStat : StatFactorConst -> Comp StatLink
linkStat (Return t val) = do 
  (rtnTy**linkedVal) <- linkTerm (_**val)
  pure $ Return rtnTy linkedVal
linkStat (Execute n ts) = do 
  terms <- traverseM linkTerm ts
  pure $ Execute n terms


linkFunc : FuncFactorConst -> Comp FuncLink
linkFunc (MkFunc {rtnTy} {args} (MkFuncGen a n ns b)) = do
  stats <- traverseM linkStat b 
  pure (MkFunc {rtnTy} {args} (MkFuncGen a n ns stats ))

export 
linkPrgm : ProgramFactorConst -> Comp ProgramLink
linkPrgm (MkProgram fs cs prfs) = pure $ MkProgram !(traverseM linkFunc fs) cs Nothing
  










