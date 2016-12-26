module Asm
import Util.UtilRoot
%access public export


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
--            | Hex
--            | Oct
--            | Bin

record ImmVal where
  constructor MkImm
  val : Int
  pre : Prefix


data Opr: Type where
  Reg : RegId -> Opr
  Imm : ImmVal -> Opr
  MemReg : RegId -> Opr

syntax "@"[v]"@" = Imm $ MkImm v Dec

data Instr : Type where
  Mov : Opr -> Opr -> Instr
  Syscall : Instr
  Xor : Opr -> Opr -> Instr


record AsmProgram where
  constructor MkAsm
  global : String
  instructs : List Instr
  
Show RegId where
 show RAX = "rax"
 show RCX = "rcx"
 show RDX = "rdx"
 show RBX = "rbx"
 show RSP = "rsp"
 show RBP = "rbp"
 show RSI = "rsi"
 show RDI = "rdi"
 show EAX = "eax" 

Show ImmVal where
  show (MkImm v p) = show v --TODO: use hex for everything.

Show Opr where
  show (Reg r) = show r
  show (Imm i) = show i
  show (MemReg m) = "[" ++ show m ++ "]"

pad10 : String -> String
pad10 = padSpace 10

pad5 : String -> String
pad5 = padSpace 5

Show Instr where
  show (Mov o1 o2) = pad5 "" ++ pad10 "mov" ++ (pad5 (show o1)) ++ "," ++ (show o2)
  show Syscall = pad5 "" ++ "syscall"
  show (Xor o1 o2) = pad5 "" ++ pad10 "xor" ++ (pad5 (show o1)) ++ "," ++ (show o2)

Show AsmProgram where
  show (MkAsm glob instructs) = 
    "global " ++ glob ++ "\n" ++ 
    "\n" ++
    "section .text \n" ++
    glob ++ ": \n" ++
    unlines (map show instructs)







