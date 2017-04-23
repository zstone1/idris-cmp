module FactorConst
import Util.RootUtil
import Models.RootModels

export
record TypedConstant' (t:Type) where
  constructor MkTypedConstant
  name : String
  access : AccessMod
  val : t

public export
TypedConstant : Type
TypedConstant = DepUnion (map TypedConstant' ConstantBaseTypes)

typeConst' : {t:Type} -> ParsedConstant' t -> Comp (TypedConstant' t)
typeConst' (MkParsedConstant n a t) = pure $ MkTypedConstant n !(parseAccess a) t

export
typeConst : Program a b ParsedConstant -> Comp (Program a b TypedConstant)
typeConst = let f = depMatch' $ mapToMatcher {l = ConstantBaseTypes} $ typeConst' in
                traverseProgram $ traverseModuleConsts $ f

