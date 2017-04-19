module ValueModels
import Util.RootUtil

data IntLiteral : Type  where
  MkIntLit : Nat -> IntLiteral

data StringLiteral : Type where
  MkStringLit : String -> StringLiteral

record Term where
  constructor MkTerm 
  val : DepUnion l


