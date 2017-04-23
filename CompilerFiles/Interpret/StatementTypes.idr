module StatementTypes
import Util.RootUtil
import Models.RootModels
import Interpret.ConstTypes

Pass1TermHierarchy : Hierarchy
Pass1TermHierarchy Z = TypedConstantTys
Pass1TermHierarchy (S c) = [FuncApplication (assert_total $ Pass1TermHierarchy #. c)]

Pass1Term : Type
Pass1Term = Member Pass1TermHierarchy

termMap : (c : Nat) -> ParsedTermHierarchy#.c -> Comp' {env} {l=['Namer ::: STATE Nat]} (Pass1TermHierarchy#.c)
termMap (S n) t with (split{xs = [_]} t)
  | Left a = do let a = extract a
                newArgs <- getEff (traverse(monadEffT . termMap n) (args a))
                pure $ MkDepUnion $ MkFuncApplication (name a) newArgs
  |Right b = [| (cumulative2 {n=n} {m=S Z}) (termMap n b) |]
termMap Z t = dcase t of []
  |% _ : i => (toTypedConst (intVal i)) %|
  |% _ : i => (toTypedConst (strVal i)) %| where
    toTypedConst : {t:Type} -> t -> {auto p : SubElem (TypedConstant' t) TypedConstantTys} -> 
                        Comp' {l=['Namer ::: STATE Nat]} (Pass1TermHierarchy#.Z)
    toTypedConst v = pure (MkDepUnion $ MkTypedConstant (!nextName) Private v)
  
