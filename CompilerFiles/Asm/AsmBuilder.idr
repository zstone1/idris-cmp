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

buildExpr : StatFactorConst -> Comp (List Instr)
buildExpr (Return  _ (FromConst c)) = do
  let (reserve, len) = buildReserve (_ ** c)
  pure ((writeStd (Res reserve) len) ++ exit)
buildExpr (Return _ (ApplyFunc _ _)) = raise "asm doesn't support funcs yet"
buildExpr (Execute _ _ ) = raise "asm still doesn't support functions"

buildMain : QFunc StatFactorConst -> Comp AsmFunc
buildMain (MkFunc (MkFuncGen Public "main" [] b)) = do
  exprs <- traverseM buildExpr b
  pure $ MkAsmFunc (concat exprs) "_start"
buildMain _ = raise "Not a main function"

export
toAsm : ProgramFactorConst -> Comp AsmProgram
toAsm (MkProgram (x::[]) cs _) = pure $ MkAsm
      (MkDirectives (Just "_start"))
      (map (fst . buildReserve) cs)
      [!( buildMain x)]
toAsm _ = raise "Only one function supported"











