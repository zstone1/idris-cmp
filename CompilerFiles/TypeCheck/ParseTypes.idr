module ParseTypes
import Interpret.RootInterpret
import Util.RootUtil
import TypeCheck.CorePrgm
%access public export

data TermTyped : Maybe C0Type -> Type where
  MkIntLit : Int -> TermTyped (Just C0Int)
  MkStrLit : String -> TermTyped (Just C0Str)
  ApplyFunc : (name: String) -> Vect n (t:Maybe C0Type ** TermTyped t) -> TermTyped Nothing

StatTyped : Type
StatTyped = StatGen TermTyped

FuncTyped : Type
FuncTyped = QFunc StatTyped

ProgramTyped : Type
ProgramTyped = Program FuncTyped Void NoFacts

Show (TermTyped t) where
  show (MkIntLit x) = "IntLit: " ++ show x
  show (MkStrLit x) = "StrLit: " ++ show x
  show (ApplyFunc n vals) =  assert_total $
    n ++ "(" ++ foldl 
          (\a,x => a ++ "," ++ show (snd x))
          "" vals ++ ")"

Show StatTyped where
  show (Return _ s) = "return " ++ show s
  show (Execute n vs) = n ++ "(" ++ show vs ++ ")"
  show (Condition gu bo) = "if " ++ show gu ++ " then " ++ assert_total(show bo)

%access private
convertAccess : String -> Comp AccessMod
convertAccess s with (s)
  | "public" = pure Public
  | _ = raise (s ++ " is not a valid access modifier")


convertType : String -> Comp C0Type 
convertType s with (s)
  | "int" = pure C0Int
  | "string" = pure C0Str
  | _ = raise ( s ++ " is not a valid type")

convertTerm : TermPrim -> Comp (t:Maybe C0Type ** TermTyped t)
convertTerm (MkIntLit i) = pure (_ ** MkIntLit i) 
convertTerm (MkStrLit s) = pure (_ ** MkStrLit s)
convertTerm (ApplyFunc n argsPrim) = do 
  --assert total due to args nested in list
  args <- assert_total $  traverseM  convertTerm argsPrim 
  pure ( _ ** ApplyFunc n args)
  
convertStat : StatPrim -> Comp StatTyped 
convertStat (Return t) = do (t ** trm) <- convertTerm t
                            pure (Return t trm)

convertStat (ExecTerm (ApplyFunc n args)) = pure $ Execute n !(traverseM convertTerm args)
convertStat (ExecTerm (MkIntLit i)) = raise ("Cannot execute int  "++ show i)
convertStat (ExecTerm (MkStrLit s)) = raise ("Cannot execute string " ++ s)

convertStat (Condition gu bo) = do
  (_**gu') <- (convertTerm gu) 
  bo' <- assert_total (traverseM convertStat bo)
  pure$ Condition gu' bo'



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
