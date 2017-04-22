module Parser
import Util.RootUtil
import Models.RootModels
import Lightyear
import Lightyear.Char
import Lightyear.Strings
%access private
%default partial

rtn : Parser ()
rtn = token "return"
 
parseIntLit : Parser ParsedTerm
parseIntLit = pure (0 **  MkDepUnion $ MkIntLit !integer)

parseStrLit : Parser ParsedTerm
parseStrLit = pure (0 ** MkDepUnion $ MkStringLit !(quoted '"'))

mutual
  parseFuncApp : Parser ParsedTerm
  parseTerm : Parser ParsedTerm

  parseFuncApp = do name <- some letter <* spaces
                    args <- between (token "(") (token ")") (parseTerm `sepBy` token ",") 
                    let (n ** lifted) = liftComplexity args
                    let val = MkFuncApplication (pack name) lifted
                    pure $ ( _ ** MkDepUnion {l= level ParsedTermHierarchy (S n)} val)

  parseTerm =  parseIntLit
           <|> parseStrLit
           <|> parseFuncApp
           <?> "Failed to parse literal"

mutual 
  parseStat : Parser ParsedStat
  parseRtn : Parser ParsedStat
  parseExecTerm : Parser ParsedStat
  parseCondition : Parser ParsedStat
  parseBody : Parser (List ParsedStat)

  parseRtn = do rtn
                t <- parseTerm 
                pure ( Z ** MkDepUnion ( MkParsedReturn t))

  parseExecTerm = do t <- parseTerm 
                     pure ( Z **  MkDepUnion (MkParsedExec t))


         
  parseCondition = do token "if" 
                      token "(" 
                      gu <- parseTerm
                      token ")"
                      bo <- parseBody
                      let (n ** lifted) = liftComplexity bo
                      pure ( _ ** MkDepUnion {l = level ParsedStatHierarchy (S n)} $ MkParsedCondition gu lifted)

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

parseMod : Parser ParsedMod
parseMod = do 
  funcs <- (parseFunc `sepBy` endOfLine)
  eof
  pure $ MkMod "default_mod" funcs []

total export
parseProgram : String -> Comp (Program ParsedStat ParsedFuncSigTys ParsedConstant)
parseProgram s = assert_total $ case parse parseMod s of
                                   Left e => raise e
                                   Right p => pure (MkProgram [p])










