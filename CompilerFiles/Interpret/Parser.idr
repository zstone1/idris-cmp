module Parser
import Interpret.ExprPrim
import Lightyear
import Lightyear.Char
import Lightyear.Strings
%access private
%default partial

rtn : Parser ()
rtn = token "return"

parseIntLit : Parser ExprPrim
parseIntLit = [| MkIntLit integer |]

parseStrLit : Parser ExprPrim
parseStrLit = [| MkStrLit $ quoted '"' |]

parseLit : Parser ExprPrim
parseLit =   parseIntLit
         <|> parseStrLit
         <?> "Failed to parse literal"
          
parseExpr : Parser ExprPrim
parseExpr = rtn *> parseLit <* semi

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
  defn <- between (token "{") (token "}") parseExpr
  let access' = pack access
  let ty' = pack ty
  let name' = pack name
  let params' = fromList params
  pure $ MkFuncPrim access' ty' name' params' defn

parseProgram' : Parser (ProgramPrim)
parseProgram' = do 
  funcs <- (parseFunc `sepBy` endOfLine)
  eof
  pure $ MkProgramPrim funcs

export
total --assert total because strings have finite length.
parseProgram : String -> Either String ProgramPrim
parseProgram = assert_total $ parse parseProgram' 

Test1 : String
Test1 = case [|show $ parse parseExpr "return 123;" |] of
             Left s => s
             Right s => s

Test3 : String 
Test3 = case [|show $ parse parseFunc "public \n int Foo(t a, tt b) { return 5;}"|] of
             Left s => s
             Right s => s

