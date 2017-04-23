module StatementTypes
import Util.RootUtil
import Models.RootModels
import Interpret.ConstTypes

record ConstantTerm where
  constructor MkConstTerm 
  val : TypedConstant 
  name : String
  

Pass1TermHierarchy : Hierarchy
Pass1TermHierarchy Z = [ConstantTerm]
Pass1TermHierarchy (S c) = [FuncApplication (assert_total $ Pass1TermHierarchy #. c)]

Pass1Term : Type
Pass1term : Member Pass1TermHierarchy

{-
termMap : ParsedTerm -> Comp' {l=['Namer ::: STATE Nat]} TypedConstant
termMap (Z ** t) = dcase t of []
  |% IntLiteral : i => (pure $ MkDepUnion $ MkTypedConstant (!nextName) Private (intVal i)) %|
  |% StringLiteral : i => (pure $ MkDepUnion $ MkTypedConstant (!nextName) Private (strVal i)) %|
termMap (S n ** t) = ?b
-}

