module Asm
import Util.UtilRoot
%access public export

 --------names for things:
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

data MemSize = DB
             | DW

---------- reserved values
data ReserveVal = Chars String (Maybe Int) | Num Int

record Reservation where
  constructor MkReserve
  name : String 
  size : MemSize
  val : ReserveVal

record Reserves where
  constructor MkConsts
  reserves : List Reservation

--------- Instruction
record ImmVal where
  constructor MkImm
  val : Int
  pre : Prefix

data Opr : Reserves -> Type where
  Reg : RegId -> Opr rs
  Imm : ImmVal -> Opr rs
  Res : {rs: Reserves} -> (r:Reservation) -> {auto q:List.Elem r (reserves rs)} -> Opr rs

syntax "@"[v]"@" = Imm $ MkImm v Dec

data Instr : Reserves -> Type where
  Mov : Opr rs -> Opr rs -> Instr rs
  Syscall : Instr rs
  Xor : Opr rs -> Opr rs -> Instr rs


data AsmProgram : Type where
  MkAsm : (start: String) -> (rs: Reserves) -> List (Instr rs) -> AsmProgram
  
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

Show MemSize where
  show DB = "db"
  show DW = "dw"

Show Reservation where
  show (MkReserve n s (Num i)) = n ++ ":  " ++ show s ++ " " ++ show i
  show (MkReserve n s (Chars v Nothing)) = n ++ ":  " ++show s++ "  \"" ++ v ++ "\""
  show (MkReserve n s (Chars v (Just i))) = n ++ ":  " ++ show s++ "  \"" ++ v ++ "\"," ++ show i

Show ImmVal where
  show (MkImm v p) = show v --TODO: use hex for everything.

Show (Opr rs) where
  show (Reg r) = show r
  show (Imm i) = show i
  show (Res m) = name m

pad10 : String -> String
pad10 = padSpace 10

pad5 : String -> String
pad5 = padSpace 5

Show (Instr rs) where
  show (Mov o1 o2) = pad5 "" ++ pad10 "mov" ++ (pad5 (show o1)) ++ "," ++ (show o2)
  show Syscall = pad5 "" ++ "syscall"
  show (Xor o1 o2) = pad5 "" ++ pad10 "xor" ++ (pad5 (show o1)) ++ "," ++ (show o2)

Show AsmProgram where
  show (MkAsm start rs instructs) = 
    "global " ++ start ++ "\n" ++ 
    "\n" ++
    "section .text \n" ++
    start ++ ": \n" ++
    unlines (map show instructs) ++ "\n" ++
    "\n" ++
    unlines (map show (reserves rs))







