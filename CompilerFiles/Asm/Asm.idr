module Asm
import Util.UtilRoot

data RegId = RAX
           | RCX
           | RDX
           | RBX
           | RSP
           | RBP
           | RSI
           | RDI
           | EAX

data Prefix = Dec
            | Hex
            | Oct
            | Bin

record ImmVal where
  constructor MkImm
  val : Nat
  pre : Prefix


data Opr: Type where
  Reg : RegId -> Opr
  Imm : ImmVal -> Opr
  MemReg : RegId -> Opr
  MemImm : ImmVal -> Opr

data Instr : Type where
  Mov : Opr -> Opr -> Instr
  Syscall : Instr
  Xor : Opr -> Opr -> Instr


record AsmProgram where
  constructor MkAsm
  global : String
  instructs : List Instr
  
