module TypeParser
import Interpret.RootInterpret
import Util.RootUtil
import TypeCheck.CorePrgm
import TypeCheck.Typed

convertAccess : String -> Comp AccessMod
convertAccess s with (s)
  | "public" = pure Public
  | _ = raise (s ++ " is not a valid access modifier")


convertType : String -> Comp C0Type 
convertType s with (s)
  | "int" = pure C0Int
  | "string" = pure C0Str
  | _ = raise ( s ++ " is not a valid type")

convertMType : Maybe String -> Comp C0Type
convertMType Nothing = pure Void
convertMType (Just x) = convertType x

convertTerm : TermPrim -> Comp (t:C0Type ** TermTyped t)
convertTerm (MkIntLit i) = pure (_ ** MkIntLit i) 
convertTerm (MkStrLit s) = pure (_ ** MkStrLit s)
convertTerm (ApplyFunc n rtnPrim argsPrim) = do 
  --assert total due to args nested in list
  args <- assert_total $  traverseM  convertTerm argsPrim 
  rtn <- convertMType rtnPrim
  pure ( _ ** ApplyFunc n rtn args)
  
convertStat : StatPrim -> Comp StatTyped 
convertStat (Return t) = do (t ** trm) <- convertTerm t
                            pure (Return t trm)
convertStat (ExecTerm t) = raise "only return is supported"

convertBody : List StatPrim -> Comp (List StatTyped)
convertBody ePrims = getEff $ traverse (monadEffT . convertStat) ePrims


convertParam : (String, String) -> Comp (C0Type, String)
convertParam (a,b) = [(convertType a, b)]

convertFunc : FuncPrim -> Comp FuncTyped
convertFunc x = do
  access <- convertAccess $ access x
  let name = name x
  body <- convertBody $ body x
  expectedt <- convertType $ rtnTy x 
  params <-getEff $ traverse (monadEffT . convertParam)  $ params x
  let func = MkFuncGen access name (map snd params) body
  pure (MkFunc {rtnTy=expectedt} {args=(map fst params)} func )

                      
export
convertProgramTyped : ProgramPrim -> Comp ProgramTyped
convertProgramTyped x = do
  allfuncs <- getEff $ traverse (monadEffT . convertFunc) $ funcs x 
  pure $ MkProgram allfuncs [] Nothing
