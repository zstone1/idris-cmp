module Conductor
import Util.RootUtil
import Asm.RootAsm
import Interpret.RootInterpret
import TypeCheck.RootTypeCheck
import Effect.File
import Effect.StdIO
import Control.IOExcept

compile : String -> Comp AsmProgram
compile s = do
  parsed <- parseProgram s
  typed <- convertProgram parsed
  let assembled = toAsm typed
  pure $ assembled


export
compileToFile' : String -> String -> Comp {l=[EXCEPTION String, STDIO, FILE ()]} ()
compileToFile' prgmFile name = do 
  (Result prgm) <- readFile prgmFile | FError e => raise (show e)
  asm <- compile prgm
  let gen = show asm
  writeFile name gen 
  pure ()


export
compileToFile : String -> String -> IOExcept String ()
compileToFile a b= run (compileToFile' a b)


















