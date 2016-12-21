module TypeChecker
import Interpret.ExprTyped
import Interpret.ExprPrim
import Util.EffectExt
import Effect.Exception
import Util.EitherExt
import Data.Vect
import Util.SyntaxExt

export
data TypeErr = MkTypeErr String

Show TypeErr where
  show (MkTypeErr s) = s

TypeErrEff : {ty: Type -> Type} -> Type -> Type
TypeErrEff {ty}= MonadEffT [EXCEPTION TypeErr] ty

convertAccess : String -> TypeErrEff AccessMod
convertAccess s with (s)
  | "public" = [| Public |]
  | _ = raise (MkTypeErr (s ++ " is not a valid access modifier"))

convertExpr : ExprPrim -> TypeErrEff (t:C0Type ** ExprTyped t) 
convertExpr e with (e)
  | (MkIntLit x) = [| (C0Int ** MkIntLit x) |]
  | (MkStrLit x) = [| (C0Str ** MkStrLit x) |]

convertType : String -> TypeErrEff C0Type 
convertType s with (s)
  | "int" = [| C0Int |]
  | "string" = [| C0Str |]

validateTypeMatch : (a:C0Type) -> (b:C0Type) -> TypeErrEff (a=b) 
validateTypeMatch x y with (decEq x y)
  | Yes p = [| p |]
  | No _ = raise (MkTypeErr $ 
            " expected type " ++ show x ++ 
            " but computed type " ++ show y)

convertParam : (String, String) -> TypeErrEff (C0Type, String)
convertParam (a,b) = [| MkPair (convertType a) (pure b) |]

convertFunc : FuncPrim -> TypeErrEff FuncTyped 
convertFunc x = do
  access <- convertAccess $ access x
  let name = name x
  (t ** defn) <- convertExpr $ defn x
  expectedt <- convertType $ rtnTy x 
  validateTypeMatch t expectedt --This returns a proof. Use it somewhere?
  params <- traverse convertParam $ params x
  pure $ MkFuncTyped access name params (t ** defn)


convertProgram' : ProgramPrim -> TypeErrEff ProgramTyped
convertProgram' x = 
  let programs = traverse convertFunc $ funcs x in 
      [| MkProgram programs |]

export
convertProgram : ProgramPrim -> Either String ProgramTyped
convertProgram x = run (convertProgram' x) // mapl show
                       





