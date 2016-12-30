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

data MemSize = B
             | W
             | DW
             | QW

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
  global : String

--------- Instruction
record ImmVal where
  constructor MkImm
  val : Int
  pre : Prefix

data Opr : Type where
  Reg : RegId -> Opr
  Imm : ImmVal -> Opr 
  Res : (r:Reservation) -> Opr
  Mem : Maybe MemSize -> Opr -> Opr

syntax "@"[v]"@" = Imm $ MkImm v Dec

data Instr :Type where
  Mov : Opr -> Opr-> Instr
  Syscall : Instr 
  Xor : Opr -> Opr -> Instr 
  Je : String -> Instr
  Jnz : String -> Instr
  Jne : String -> Instr
  Jmp : String -> Instr
  Cmp : Opr -> Opr -> Instr
  Label : String -> Instr

-------- Functions
record AsmFunc where
  constructor MkAsmFunc
  instrs : List Instr
  name : String

-------- Programs
data AsmProgram : Type where
  MkAsm : Directives -> List Reservation -> List AsmFunc -> AsmProgram


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

[dataSec] Show MemSize where
  show B = "db"
  show W = "dw"
  show DW = "dd"
  show QW = "dq"

[memRead] Show MemSize where
  show B = "byte"
  show W = "word"
  show DW = "dword"
  show QW = "qword"

Show Reservation where
  show (MkReserve n s (Num i)) = n ++ ":  " ++ show @{dataSec} s ++ " " ++ show i
  show (MkReserve n s (Chars v Nothing)) = n ++ ":  " ++show @{dataSec} s++ "  \"" ++ v ++ "\""
  show (MkReserve n s (Chars v (Just i))) = n ++ ":  " ++show @{dataSec} s++ "  \"" ++ v ++ "\"," ++ show i

Show ImmVal where
  show (MkImm v p) = show v --TODO: use hex for everything.

Show (Opr) where
  show (Reg r) = show r
  show (Imm i) = show i
  show (Res m) = name m
  show (Mem Nothing opr) = "["++show opr++"]"
  show (Mem (Just s) opr) = show @{memRead} s ++" ["++show opr++"]"


Show Directives where
  show (MkDirectives x) = "global " ++ x

pad10 : String -> String
pad10 = padSpace 10

pad5 : String -> String
pad5 = padSpace 5

Show (Instr) where
  show (Jnz l) = pad5 "" ++ pad10 "jnz" ++ l
  show (Je l) = pad5 "" ++ pad10 "je" ++ l
  show (Jne l) = pad5 "" ++ pad10 "jne" ++ l
  show (Jmp l) = pad5 "" ++ pad10 "jmp" ++ l
  show (Cmp o1 o2) = pad5 "" ++ pad10 "cmp" ++ (pad5 (show o1)) ++ "," ++ (show o2)
  show (Mov o1 o2) = pad5 "" ++ pad10 "mov" ++ (pad5 (show o1)) ++ "," ++ (show o2)
  show Syscall = pad5 "" ++ "syscall"
  show (Xor o1 o2) = pad5 "" ++ pad10 "xor" ++ (pad5 (show o1)) ++ "," ++ (show o2)
  show (Label s) = s ++ ":"

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







