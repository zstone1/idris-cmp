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

typeConstants' : {t:Type} -> ParsedConstant' t -> Comp (TypedConstant' t)
typeConstants' (MkParsedConstant n a t) = pure $ MkTypedConstant n !(parseAccess a) t

export
typeConstants : Program a b ParsedConstant -> Comp (Program a b TypedConstant)
typeConstants = let f = depMatch' $ mapToMatcher {l = ConstantBaseTypes} $ typeConstants' in
                traverseProgram $ traverseModuleConsts $ f

