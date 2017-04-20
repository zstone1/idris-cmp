module Parser
import Util.RootUtil
import Models.RootModels
import Lightyear
import Lightyear.Char
import Lightyear.Strings
%access private
%default partial

total
ParsedTermTys : Nat -> List Type 
ParsedTermTys Z = [IntLiteral, StringLiteral]
ParsedTermTys (S c) = FuncApplication (DepUnion (ParsedTermTys c)) :: ParsedTermTys c

private
cumulativity1 : (ParsedTermTys n) `SubList` (ParsedTermTys (S n))
cumulativity1 {n} = dropPrefix (subListId _ ) {zs = [_]}

ParsedTerm : Nat -> Type
ParsedTerm n = DepUnion (ParsedTermTys n)

--got bored proving this.
cumulativity2 : ParsedTerm n -> ParsedTerm m 
cumulativity2 p a = Shuffle 

rtn : Parser ()
rtn = token "return"
 
parseIntLit : Parser (ParsedTerm 0)
parseIntLit = pure $ MkDepUnion $  MkIntLit !integer

parseStrLit : Parser (ParsedTerm 0)
parseStrLit = pure $ MkDepUnion $ MkStringLit !(quoted '"')

mutual
  parseFuncApp : Parser (n:Nat ** ParsedTerm n)
  parseTerm : Parser (n: Nat ** ParsedTerm n)

  parseFuncApp = do name <- some letter <* spaces
                    args <- between (token "(") (token ")") (parseTerm `sepBy` token ",") 
                    let complexity = foldr max 0 (map DPair.fst args)
--                    let x = MkFuncApplication {argTy = ParsedTerm complexity} (pack name) (map DPair.snd)
                    ?foo

  parseTerm =  ?parseTerm 
   -- parseIntLit
    --       <|> parseStrLit
    --       <|> parseFuncApp
    --       <?> "Failed to parse literal"

{-
mutual 
  parseStat : Parser StatPrim
  parseRtn : Parser StatPrim
  parseExecTerm : Parser StatPrim
  parseCondition : Parser StatPrim
  parseBody : Parser (List StatPrim)

  parseRtn = rtn *> [| Return parseTerm |]

  parseExecTerm = [|ExecTerm parseFuncApp |] 
         
  parseCondition = do token "if" 
                      token "(" 
                      gu <- parseTerm
                      token ")"
                      bo <- parseBody
                      pure (Condition gu bo)

  parseStat =  (parseRtn <* semi)
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


parseFunc : Parser FuncPrim
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
  pure $ MkFuncPrim access' ty' name' params' defn

parseProgram' : Parser (ProgramPrim)
parseProgram' = do 
  funcs <- (parseFunc `sepBy` endOfLine)
  eof
  pure $ MkProgram funcs [] Nothing

export
total --assert total because strings have finite length.
parseProgram : String -> Comp ProgramPrim
parseProgram s = assert_total $ case parse parseProgram' s of
                                   Left e => raise e
                                   Right p => pure p

test : String -> String
test s = case parse parseProgram' s of
              Left e => e
              Right e => show e



-}









