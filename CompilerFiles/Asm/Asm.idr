module Asm
import Util.RootUtil
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

-------- Directives
record Directives where
  constructor MkDirectives
  global : Maybe String

--------- Instruction
record ImmVal where
  constructor MkImm
  val : Int
  pre : Prefix

data Opr : Type where
  Reg : RegId -> Opr
  Imm : ImmVal -> Opr 
  Res : (r:Reservation) -> Opr

syntax "@"[v]"@" = Imm $ MkImm v Dec

data Instr :Type where
  Mov : Opr -> Opr-> Instr
  Syscall : Instr 
  Xor : Opr -> Opr -> Instr 

-------- Functions
record AsmFunc where
  constructor MkAsmFunc
  instrs : List Instr
  name : String

-------- Programs
data AsmProgram : Type where
  MkAsm : Directives -> List Reservation -> List AsmFunc -> AsmProgram

InitPrgm : AsmProgram
InitPrgm = MkAsm (MkDirectives Nothing) [] []
  


data AsmState : AsmProgram -> Type where
  Init : AsmState InitPrgm
  AddReserve : (r : Reservation) -> AsmState (MkAsm d rs fs) -> AsmState (MkAsm d (r::rs) fs)
  AddFunc : (f : AsmFunc) -> AsmState (MkAsm d rs fs) -> AsmState (MkAsm d rs (f ::fs))
   

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

Show (Opr) where
  show (Reg r) = show r
  show (Imm i) = show i
  show (Res m) = name m


Show Directives where
  show (MkDirectives Nothing) = ""
  show (MkDirectives (Just x)) = "global " ++ x

pad10 : String -> String
pad10 = padSpace 10

pad5 : String -> String
pad5 = padSpace 5

Show (Instr) where
  show (Mov o1 o2) = pad5 "" ++ pad10 "mov" ++ (pad5 (show o1)) ++ "," ++ (show o2)
  show Syscall = pad5 "" ++ "syscall"
  show (Xor o1 o2) = pad5 "" ++ pad10 "xor" ++ (pad5 (show o1)) ++ "," ++ (show o2)

Show AsmFunc where
  show (MkAsmFunc instrs name) = 
    "section .text \n" ++
    name ++ ": \n" ++
    unlines (map show instrs)

Show AsmProgram where
  show (MkAsm directives rs fs) = 
    show directives ++
    "\n" ++
    unlines (map show fs) ++
    "\n" ++
    unlines (map show rs)







