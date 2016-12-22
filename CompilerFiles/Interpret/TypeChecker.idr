module TypeChecker
import Interpret.ExprTyped
import Interpret.ExprPrim
import Util.EffectExt
import Util.PairExt
import Effect.Exception
import Util.EitherExt
import Data.Vect
import Util.SyntaxExt

data TypeErr = MkTypeErr String

Show TypeErr where
  show (MkTypeErr s) = s

TypeErrEff : {ty: Type -> Type} -> Type -> Type
TypeErrEff {ty}= MonadEffT [EXCEPTION TypeErr] ty

convertAccess : String -> TypeErrEff AccessMod
convertAccess s with (s)
  | "public" = pure Public
  | _ = raise (MkTypeErr (s ++ " is not a valid access modifier"))

convertExpr : ExprPrim -> TypeErrEff (t:C0Type ** ExprTyped t) 
convertExpr e with (e)
  | (MkIntLit x) = pure (C0Int ** MkIntLit x)
  | (MkStrLit x) = pure (C0Str ** MkStrLit x)

convertType : String -> TypeErrEff C0Type 
convertType s with (s)
  | "int" = pure C0Int
  | "string" = pure C0Str

validateTypeMatch : (a:C0Type) -> (b:C0Type) -> TypeErrEff (a=b) 
validateTypeMatch x y with (decEq x y)
  | Yes p = pure p
  | No _ = raise (MkTypeErr $ 
            " expected type " ++ show x ++ 
            " but computed type " ++ show y)

convertParam : (String, String) -> TypeErrEff (C0Type, String)
convertParam (a,b) = [(convertType a, b)]

convertFunc : FuncPrim -> TypeErrEff FuncTyped 
convertFunc x = do
  access <- convertAccess $ access x
  let name = name x
  (t ** defn) <- convertExpr $ defn x
  expectedt <- convertType $ rtnTy x 
  validateTypeMatch t expectedt --This returns a proof. Use it somewhere?
  params <- traverse convertParam $ params x
  pure $ MkFuncTyped access name params (t ** defn)

private 
q : DecEq a => (f : FuncTyped) -> (g: FuncTyped -> a) -> (a2:a) -> Dec (g f = a2)
q f g a2 = decEq (g f) a2

checkMain : (f: FuncTyped) -> Maybe (IsMain f)
checkMain f with (q f name MainName, q f (fst . defn) C0Int, q f access Public, q f arity Z)
  | (Yes p1, Yes p2, Yes p3, Yes p4) = Just (MainWit p1 p2 p3 p4)
  | _ = Nothing


getMain : List FuncTyped -> TypeErrEff {ty} (t ** IsMain t)
getMain fs with (mapMaybe (\f => [(f $* checkMain)]) fs) 
  | [] = raise (MkTypeErr "Main method is required")
  | (x :: xs) = pure x 

convertProgram' : ProgramPrim -> TypeErrEff ProgramTyped
convertProgram' x = do
  allfuncs <- traverse convertFunc $ funcs x 
  (_ ** main) <- getMain allfuncs
  pure $ MkProgram allfuncs main

export
convertProgram : ProgramPrim -> Either String ProgramTyped
convertProgram x = run (convertProgram' x) // mapl show
                       





