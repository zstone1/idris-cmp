module Conductor
import Util.UtilRoot
import Asm.AsmRoot
import Interpret.RootInterpret

compile : String -> Either String String
compile s = do
  parsed <- parseProgram s
  typed <- convertProgram parsed
  let toasm = toAsm typed
  pure $ show toasm


