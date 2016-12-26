module TypeChecker
import Interpret.ExprTyped
import Interpret.ExprPrim
import Effect.Exception
import Util.UtilRoot
import Data.List

convertAccess : String -> Comp AccessMod
convertAccess s with (s)
  | "public" = pure Public
  | _ = raise (s ++ " is not a valid access modifier")

convertExpr : ExprPrim -> Comp (t:C0Type ** ExprTyped t) 
convertExpr e with (e)
  | (MkIntLit x) = pure (C0Int ** MkIntLit x)
  | (MkStrLit x) = pure (C0Str ** MkStrLit x)

convertType : String -> Comp C0Type 
convertType s with (s)
  | "int" = pure C0Int
  | "string" = pure C0Str
  | _ = raise ( s ++ " is not a valid type")

validateTypeMatch : (a:C0Type) -> (b:C0Type) -> Comp (a=b) 
validateTypeMatch x y with (decEq x y)
  | Yes p = pure p
  | No _ = raise ( 
            " expected type " ++ show x ++ 
            " but computed type " ++ show y)

convertParam : (String, String) -> Comp (C0Type, String)
convertParam (a,b) = [(convertType a, b)]

convertFunc : FuncPrim -> Comp FuncTyped 
convertFunc x = do
  access <- convertAccess $ access x
  let name = name x
  (t ** defn) <- convertExpr $ defn x
  expectedt <- convertType $ rtnTy x 
  validateTypeMatch t expectedt --This returns a proof. Use it somewhere?
  params <-getEff $ traverse (monadEffT . convertParam)  $ params x
  pure $ MkFuncTyped access name params (t ** defn)


getMain : (l: List FuncTyped) -> Comp (t ** IsMain t l)
getMain [] = raise "Main method is required"
getMain ((MkFuncTyped Public "main" [] (C0Int ** _)):: xs) = pure $  (_** EmptyMain Here)
getMain (x ::xs) = do (_**(EmptyMain elem)) <- getMain xs
                      pure $ (_** EmptyMain (There elem))

export
convertProgram : ProgramPrim -> Comp ProgramTyped
convertProgram x = do
  allfuncs <- getEff $ traverse (monadEffT . convertFunc) $ funcs x 
  (_ ** main) <- getMain allfuncs
  pure $ MkProgram allfuncs main
                       





