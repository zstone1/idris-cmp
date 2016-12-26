module AsmBuilder
import Interpret.ExprTyped
import Asm.Asm
import Util.UtilRoot

buildMain : IsMain f fs -> AsmProgram
buildMain {f = MkFuncTyped Public _ [] (C0Int ** (MkIntLit i))} (EmptyMain _) = 
  let reserve = MkReserve "rtn" DB (Num i) in
  let instrs = [
      Mov (Reg RAX) @1@,
      Mov (Reg RDI) @1@,
      Mov (Reg RSI) (Res reserve),
      Mov (Reg RDX) @2@,
      Syscall,
      Mov (Reg EAX) @60@,
      Xor (Reg RDI) (Reg RDI),
      Syscall
  ] in
     MkAsm (MkDirectives (Just "_start")) 
           [reserve] 
           [MkAsmFunc instrs "_start"]

export
toAsm : ProgramTyped -> AsmProgram
toAsm (MkProgram funcs main) = buildMain main
