module FactorConst
import Util.RootUtil
import Models.RootModels

record TypedConstant' (t:Type) where
  constructor MkTypedConstant
  name : String
  access : AccessMod
  val : t
ConstantBaseTypes :List Type
ConstantBaseTypes = [Int, String]

typeConst' : {t:Type} -> ParsedConstant' t -> Comp (TypedConstant' t)
typeConst' (MkParsedConstant n a t) = pure $ MkTypedConstant n !(parseAccess a) t

typeConvert : Applicative m => 
              {l : List Type} ->
              {pre, post :Type -> Type} -> 
              (f : {t:Type} -> pre t -> m (post t)) -> 
              (x:Type) -> 
              x -> 
              SubElem x (map pre l) -> 
              m ( DepUnion (map post l))
typeConvert {l = []} _ _ _ p  = absurd p
typeConvert {l = t::ts} f _ v Z = [| dep (f v) |]
typeConvert {l = t'::ts} f t v (S n) = 
  let sub = dropPrefix (subListId _) {zs = [_]} in 
      [| (\r => shuffle r {left = sub}) (typeConvert f t v n) |]

computeTypedConstants : {l : List Type} -> DepUnion (map ParsedConstant' l) -> Comp {env} ( DepUnion (map TypedConstant' l))
computeTypedConstants = getEff . (depMatch' $ typeConvert $ monadEffT . typeConst')
    
--typeConst : Program a b ParsedConstant -> Comp (Program a b TypedConstant)
--typeConst = traverseProgram (traverseModuleConsts

