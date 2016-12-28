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

exit : List Instr
exit =
  [Mov (Reg EAX) @60@,
   Xor (Reg RDI) (Reg RDI),
   Syscall]

buildTerm : TermTyped t -> Comp Reservation
buildTerm (MkIntLit i) = pure $ MkReserve "rtn" DB (Num i)
buildTerm (MkStrLit s) = pure $ MkReserve "rtn" DB (Chars s (Just 10))
buildTerm _ = raise "wtf to do with this?"

buildExpr : ExprTyped t -> Comp (List Instr, List Reservation)
buildExpr (Return i) = do
  reserve <- buildTerm i
  pure ((writeStd (Res reserve) 1) ++ exit, [reserve])

buildMain : IsMain f fs -> Comp AsmProgram
buildMain {f = SFunc _ _ (MkFuncTyped Public "main" [] b)} (EmptyMain _) with (b)
  | ((_** x)::[]) = do
      (instrs, reservs) <- buildExpr x
      pure$ MkAsm (MkDirectives (Just "_start"))
            reservs
            [MkAsmFunc instrs "_start"]
  | _ = raise "only one method supported"
buildMain _ = raise "main function missing?"

export
toAsm : ProgramTyped -> Comp AsmProgram
toAsm (MkProgram funcs main) = buildMain main

