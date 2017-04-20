module Parser
import Util.RootUtil
import Models.RootModels
import Lightyear
import Lightyear.Char
import Lightyear.Strings
%access private
%default partial

total
public export
ParsedTermTys : Nat -> List Type 
ParsedTermTys Z = [IntLiteral, StringLiteral]
ParsedTermTys (S c) = FuncApplication (DepUnion (ParsedTermTys c)) :: ParsedTermTys c

total
public export
ParsedTermC : Nat -> Type
ParsedTermC n = DepUnion (ParsedTermTys n)

total
public export
ParsedTerm : Type
ParsedTerm = (n : Nat ** ParsedTermC n)

private total
cumulativity1 : (ParsedTermTys n) `SubList` (ParsedTermTys (S n))
cumulativity1 {n} = dropPrefix (subListId _ ) {zs = [_]}

private total 
maxLemma : x `LTE` maximum x y
maxLemma {x = Z} {y} = LTEZero
maxLemma {x = S n} {y = Z} = lteRefl
maxLemma {x = S a} {y = S b} = LTESucc $ maxLemma

private total
cumulativity2 : (ParsedTermC n) -> (ParsedTermC (m+n))
cumulativity2 {m = Z} a = a
cumulativity2 {m = S k} a = Shuffle {left = cumulativity1} (cumulativity2 a)

private total
lteHelper : a+x `LTE` a+y -> x `LTE` y
lteHelper {a=Z} = id
lteHelper {a = S i} = lteHelper . fromLteSucc

private total
cumulativity3 : (n,m:Nat) -> .(n `LTE` m) -> ParsedTermC n -> ParsedTermC m
cumulativity3 n m a t with (cmp n m)
  cumulativity3 x x a t | CmpEQ = t
  cumulativity3 n (n+S i) a t | CmpLT i = rewrite plusCommutative n (S i) in cumulativity2 {n=n}{m=S i} t
  cumulativity3 (m+S i) m a t | CmpGT i =
    let a' :(m + S i `LTE` m + 0) = (rewrite plusZeroRightNeutral m in a) in
      absurd $ lteHelper a'



liftComplexity : (List ParsedTerm) -> (n : Nat ** List (ParsedTermC n))
liftComplexity = ?lift_complexity_parsed_term

rtn : Parser ()
rtn = token "return"
 
parseIntLit : Parser ParsedTerm
parseIntLit = pure (0 **  MkDepUnion $  MkIntLit !integer)

parseStrLit : Parser ParsedTerm
parseStrLit = pure (0 ** MkDepUnion $ MkStringLit !(quoted '"'))

mutual
  parseFuncApp : Parser ParsedTerm
  parseTerm : Parser ParsedTerm

  parseFuncApp = do name <- some letter <* spaces
                    args <- between (token "(") (token ")") (parseTerm `sepBy` token ",") 
                    let (n ** lifted) = liftComplexity args
                    let val = MkFuncApplication (pack name) lifted
                    pure $ ( _ ** MkDepUnion {l=ParsedTermTys (S n)} val)

  parseTerm =  parseIntLit
           <|> parseStrLit
           <|> parseFuncApp
           <?> "Failed to parse literal"

public export
record ParsedReturn where
  constructor MkParsedReturn
  rtnVal : ParsedTerm

public export
record ParsedExec where
  constructor MkParsedExec
  execVal : ParsedTerm


public export
record ParsedCondition (ty:Type) where
  constructor MkParsedCondition
  guard : ParsedTerm
  body : List ty

public export
ParsedStatTys : Nat -> List Type
ParsedStatTys Z = [ParsedReturn, ParsedExec]
ParsedStatTys (S n) = [ParsedCondition (DepUnion (ParsedStatTys n))] ++ ParsedStatTys n

public export
ParsedStatC : Nat -> Type
ParsedStatC = DepUnion . ParsedStatTys

public export
ParsedStat : Type
ParsedStat = (n : Nat ** ParsedStatC n)

liftComplexityStat : (List ParsedStat) -> (n : Nat ** List (ParsedStatC n))
liftComplexityStat = ?lift_complexity_parsed_stat

mutual 
  parseStat : Parser ParsedStat
  parseRtn : Parser ParsedStat
  parseExecTerm : Parser ParsedStat
  parseCondition : Parser ParsedStat
  parseBody : Parser (List ParsedStat)

  parseRtn = rtn *> pure ( Z ** MkDepUnion $ MkParsedReturn !parseTerm)

  parseExecTerm = pure ( Z **  MkDepUnion $ MkParsedExec !parseTerm)
         
  parseCondition = do token "if" 
                      token "(" 
                      gu <- parseTerm
                      token ")"
                      bo <- parseBody
                      let (n ** lifted) = liftComplexityStat bo
                      pure ( _ ** MkDepUnion {l = ParsedStatTys (S n)} $ MkParsedCondition gu lifted)

  parseStat = (parseRtn <* semi)
           <|> parseCondition
           <|> (parseExecTerm <* semi)
           <?> "cannot determine expression"

  parseBody = between (token "{") (token "}") (many parseStat)


parsePair : Parser (String, String)
parsePair = do 
  a <- some letter
  token " "
  b <- some letter
  pure (pack a, pack b)

total
public export
ParsedFuncSigTys : FuncSigTypes
ParsedFuncSigTys = MkFunSigTypes String String String id (Pair String)

total
public export
ParsedFuncSig : Type
ParsedFuncSig = FuncSig ParsedFuncSigTys

total
public export
ParsedFunc : Type 
ParsedFunc = (ParsedFuncSig, List ParsedStat)

parseFunc : Parser (ParsedFuncSig, List ParsedStat)
parseFunc = do 
  access <- some letter <* token " "
  ty <- some letter <* token " "
  name <- some letter <* spaces
  params <- between (token "(") (token ")") (parsePair `sepBy` (token ","))
  defn <- parseBody
  let access' = pack access
  let ty' = pack ty
  let name' = pack name
  let params' = fromList params
  let sig = MkFuncSig access' ty' name' params'
  pure $ (sig, defn)

total
public export
ParsedMod : Type
ParsedMod = Mod (ParsedStat) (ParsedFuncSigTys)

parseMod : Parser ParsedMod
parseMod = do 
  funcs <- (parseFunc `sepBy` endOfLine)
  eof
  pure $ MkMod "default_mod" funcs

--export
total --assert total because strings have finite length.
parseProgram : String -> Comp (Program ParsedStat ParsedFuncSigTys)
parseProgram s = assert_total $ case parse parseMod s of
                                   Left e => raise e
                                   Right p => pure (MkProgram [p])

test : String -> String
test s = case parse parseMod s of
              Left e => e
              Right e => show e













