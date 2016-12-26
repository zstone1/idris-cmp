module AsmBuilder
import Interpret.ExprTyped
import Asm.Asm
import Util.UtilRoot

--buildReserves : ProgramTyped -> Reserves
--buildReserves (MkProgram fs main)
--  | [] = -- TODO: IsMain ought to include a proof that this is true
--  | (x::xs) = ?reserves

{-
buildMain : IsMain f -> List Instr 
buildMain {f = MkFuncTyped Public _ [] (C0Int ** (MkIntLit i))} EmptyMain = 
  [   Mov (Reg RAX) @1@,
      Mov (Reg RDI) @1@,
      Mov (Reg RSI) @i@,
      Mov (Reg RDX) @2@,
      Syscall,
      Mov (Reg EAX) @60@,
      Xor (Reg RDI) (Reg RDI),
      Syscall
  ]

-}
export
toAsm : ProgramTyped -> AsmProgram
--toAsm (MkProgram funcs main) =  MkAsm "_start" (buildMain main)
