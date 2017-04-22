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

typeConst' : ParsedConstant' t -> Comp (TypedConstant' t)
typeConst' (MkParsedConstant n a t) = pure $ MkTypedConstant n !(parseAccess a) t

typeConvert : Applicative m => 
              {l : List Type} ->
              {pre, post :Type -> Type} -> 
              (f : {t:Type} -> pre t -> m (post t)) -> 
              (x:Type) -> 
              x -> 
              SubElem x (map pre l) -> 
              m ( DepUnion (map post l))
typeConvert {m} {post} {l = []} _ _ _ p  = absurd p
typeConvert {m} {post} {l = t::ts} f _ v Z = [| dep (f v) |]
typeConvert {m} {post} {l = t'::ts} f t v (S n) = 
  let sub = dropPrefix (subListId _) {zs = [_] } in 
      [| (\r => Shuffle r {left = sub}) (typeConvert f t v n) |]

--computeTypedConstants : {l : List Type} -> DepUnion (map ParsedConstant' l) ->
--                 Comp ( DepUnion (map TypedConstant' l))
--computeTypedConstants = flip depMatch (typeConvert (typeConst'))


--typeConst : ParsedConstant -> Comp TypedConstant
--typeConst m = dcase m of []
--              |% ( _ ** \i:(ParsedConstant' String ) => [| MkDepUnion (typeConst' i)|])
--              |% ( _ ** \i:(ParsedConstant' Int) => [| MkDepUnion (typeConst' i)|])


--typeConst : Program a b ParsedConstant -> Comp (Program a b TypedConstant)
--typeConst = traverseProgram (traverseModuleConsts 

