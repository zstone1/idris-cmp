module TypeChecker
import Interpret.RootInterpret
import TypeCheck.ExprTyped
import Effect.Exception
import Util.RootUtil
import Data.List


convertAccess : String -> Comp AccessMod
convertAccess s with (s)
  | "public" = pure Public
  | _ = raise (s ++ " is not a valid access modifier")

convertType : String -> Comp C0Type 
convertType s with (s)
  | "int" = pure C0Int
  | "string" = pure C0Str
  | _ = raise ( s ++ " is not a valid type")


--matchFromArgs : (args: Vect n (t:C0Type ** TermTyped t)) -> MatchArgTy (map fst args) args
--matchFromArgs [] = Vacuous
--matchFromArgs (x::xs) = ?l2

mutual 
  convertTerm : TermPrim -> Comp (t:C0Type ** TermTyped t)
  convertExpr : ExprPrim -> Comp (t:C0Type ** ExprTyped t)
  convertFunc : FuncPrim -> Comp SigFunc
 
  convertTerm (MkIntLit i) = pure (_ ** MkIntLit i) 
  convertTerm (MkStrLit s) = pure (_ ** MkStrLit s)
  convertTerm (ApplyFunc n argsPrim) = do 
    --assert total due to args nested in list
    args <- assert_total $ getEff $ traverse (monadEffT . convertTerm) argsPrim 
    ?l1

{-  
convertBody : List ExprPrim -> Comp (List (t:C0Type ** ExprTyped t))
convertBody e with (e)
  | [(MkIntLit x)] = pure [(C0Int ** MkIntLit x)]
  | [(MkStrLit x)] = pure [(C0Str ** MkStrLit x)]
  | _ = raise "bad funcs"


convertParam : (String, String) -> Comp (C0Type, String)
convertParam (a,b) = [(convertType a, b)]

convertFunc x = do
  access <- convertAccess $ access x
  let name = name x
  body <- convertBody $ body x
  expectedt <- convertType $ rtnTy x 
  params <-getEff $ traverse (monadEffT . convertParam)  $ params x
  pure $ MkFuncTyped access name params expectedt body


getMain : (l: List FuncTyped) -> Comp (t ** IsMain t l)
getMain [] = raise "Main method is required"
getMain ((MkFuncTyped Public "main" [] C0Int _ ):: xs) = pure $  (_** EmptyMain Here)
getMain (x ::xs) = do (_**(EmptyMain elem)) <- getMain xs
                      pure $ (_** EmptyMain (There elem))

export
convertProgram : ProgramPrim -> Comp ProgramTyped
convertProgram x = do
  allfuncs <- getEff $ traverse (monadEffT . convertFunc) $ funcs x 
  (_ ** main) <- getMain allfuncs
  pure $ MkProgram allfuncs main
  -}                       





