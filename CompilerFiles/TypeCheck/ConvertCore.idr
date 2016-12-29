module ConvertCore
import Interpret.RootInterpret
import TypeCheck.CorePrgm
import Util.RootUtil
import Data.List
%access export


{-
--convertExpr : ExprPrim -> Comp (t:C0Type ** ExprTyped t)
convertTerm : TermPrim -> Comp (t:C0Type ** TermTyped t)
convertTerm (MkIntLit i) = pure (_ ** MkIntLit i) 
convertTerm (MkStrLit s) = pure (_ ** MkStrLit s)
convertTerm (ApplyFunc n rtnPrim argsPrim) = do 
  --assert total due to args nested in list
  args <- assert_total $ getEff $ traverse (monadEffT . convertTerm) argsPrim 
  rtn <- convertMType rtnPrim
  pure ( _ ** ApplyFunc n rtn args)
  
convertExpr : ExprPrim -> Comp (t:C0Type ** ExprTyped t)
convertExpr (Return t) = do (t ** trm) <- convertTerm t
                            pure (t ** Return trm)
convertExpr (ExecTerm t) = raise "only return is supported"

convertBody : List ExprPrim -> Comp (List (t:C0Type ** ExprTyped t))
convertBody ePrims = getEff $ traverse (monadEffT . convertExpr) ePrims

convertParam : (String, String) -> Comp (C0Type, String)
convertParam (a,b) = [(convertType a, b)]

convertFunc : FuncPrim -> Comp SigFunc
convertFunc x = do
  access <- convertAccess $ access x
  let name = name x
  body <- convertBody $ body x
  expectedt <- convertType $ rtnTy x 
  params <-getEff $ traverse (monadEffT . convertParam)  $ params x
  let func = MkFuncTyped access name (map snd params) body
  pure (SFunc expectedt (map fst params) func )


getMain : (l: List SigFunc) -> Comp (t ** IsMain t l)
getMain [] = raise "Main method is required"
getMain ((SFunc C0Int _ (MkFuncTyped Public "main" [] b))::fs) = pure $  (_** EmptyMain Here)
getMain (x ::xs) = do (_**(EmptyMain elem)) <- getMain xs
                      pure $ (_** EmptyMain (There elem))
                      
export
convertProgram : ProgramPrim -> Comp ProgramTyped
convertProgram x = do
  allfuncs <- getEff $ traverse (monadEffT . convertFunc) $ funcs x 
  (_ ** main) <- getMain allfuncs
  pure $ MkProgram allfuncs main


-}
