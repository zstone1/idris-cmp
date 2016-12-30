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

exit : Opr -> List Instr
exit o =
  [Mov (Reg EAX) @60@,
   Mov (Reg RDI) o,
   Syscall]

{-
buildMain 
buildMain {f = SFunc _ _ (MkFuncTyped Public "main" [] b)} (EmptyMain _) with (b)
  | ((_** x)::[]) = do
      (instrs, reservs) <- buildExpr x
      pure$ MkAsm (MkDirectives (Just "_start"))
            reservs
            [MkAsmFunc instrs "_start"]
  | _ = raise "only one method supported"
buildMain _ = raise "main function missing?"
-}

buildReserve : (t:C0Type ** ConstTyped t) -> (Reservation, Int)
buildReserve (_**(StringConst n s)) = (MkReserve n DB (Chars s (Just 10)), cast (length s))
buildReserve (_**(NumConst n i)) = (MkReserve n DB (Num i), 1)



buildExpr : StatLink-> Comp (List Instr)
buildExpr (Return _ (FromConst c)) =
  let (reserve, _) = buildReserve (_ ** c) in 
      pure (exit (Res reserve))
buildExpr (Execute "printf" [ (C0Str ** FromConst c) ]) = do
  let (reserve, len) = buildReserve (_ **c)
  pure (writeStd (Res reserve) len) 
buildExpr (Condition (FromConst {t=C0Int} c) bo) = do
  let (reserve, _) = buildReserve (C0Int ** c)
  ifTrue <- assert_total (traverseM buildExpr bo)
  doneLabel <- nextName
  pure([
    Cmp (Res reserve) @0@,
    Jnz doneLabel ]++
    concat ifTrue ++[
    Label doneLabel])

buildExpr (Execute _ _ ) = raise "asm still doesn't support functions"
buildExpr (Return _ _ ) = raise "return doesn't support functions"
buildExpr (Condition  _ _) = raise "unsupported if statement"


buildMain : QFunc StatLink -> Comp AsmFunc
buildMain (MkFunc (MkFuncGen Public "main" [] b)) = do
  exprs <- traverseM buildExpr b
  pure $ MkAsmFunc (concat exprs) "_start"
buildMain _ = raise "Not a main function"

export
toAsm : ProgramLink -> Comp AsmProgram
toAsm (MkProgram (x::[]) cs _) = pure $ MkAsm
      (MkDirectives (Just "_start"))
      (map (fst . buildReserve) cs)
      [!( buildMain x)]
toAsm _ = raise "Only one function supported"











