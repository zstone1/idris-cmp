module AsmBuilder
import TypeCheck.RootTypeCheck
import Asm.Asm
import Util.RootUtil
import Data.List

writeStd : Opr -> Int -> List Instr
writeStd o i = [
      Mov (Reg RAX) @1@,
      Mov (Reg RDI) @1@,
      Mov (Reg RSI) o,
      Mov (Reg RDX) @i@,
      Syscall]

exit : Int -> List Instr
exit i =
  [Mov (Reg EAX) @60@,
   Xor (Reg RDI) (Reg RDI),
   Syscall]

buildMain : IsMain f fs -> AsmProgram
buildMain {f = MkFuncTyped Public _ [] C0Int [(C0Int ** (MkIntLit i))]} (EmptyMain _) = 
  let reserve = MkReserve "rtn" DB (Num i) in
  let instrs = (writeStd (Res reserve) 1) ++ (exit i) in
     MkAsm (MkDirectives (Just "_start")) 
           [reserve] 
           [MkAsmFunc instrs "_start"]
buildMain _ = assert_unreachable()

export
toAsm : ProgramTyped -> AsmProgram
toAsm (MkProgram funcs main) = buildMain main

