module ParserModels
import Util.RootUtil
import Models.ProgramModels
import Models.Core
%access public export

--term
ParsedTermHierarchy : Hierarchy
ParsedTermHierarchy Z = [IntLiteral, StringLiteral]
ParsedTermHierarchy (S c) = [FuncApplication (assert_total $ ParsedTermHierarchy #. c)]

ParsedTerm : Type
ParsedTerm = Member ParsedTermHierarchy

record ParsedConstant' (t:Type) where
  constructor MkParsedConstant
  name : String
  access : String
  val : t

public export
ParsedConstant : Type
ParsedConstant = DepUnion (map ParsedConstant' ConstantBaseTypes)

--statement
record ParsedReturn where
  constructor MkParsedReturn
  rtnVal : ParsedTerm

record ParsedExec where
  constructor MkParsedExec
  execVal : ParsedTerm

record ParsedCondition (ty:Type) where
  constructor MkParsedCondition
  guard : ParsedTerm
  body : List ty

ParsedStatHierarchy : Hierarchy
ParsedStatHierarchy Z = [ParsedReturn, ParsedExec]
ParsedStatHierarchy (S n) = [ParsedCondition (assert_total $ ParsedStatHierarchy #. n)]

ParsedStat : Type
ParsedStat = Member ParsedStatHierarchy

--function
ParsedFuncSigTys : FuncSigTypes
ParsedFuncSigTys = MkFunSigTypes String String String id (Pair String)

ParsedFuncSig : Type
ParsedFuncSig = FuncSig ParsedFuncSigTys

ParsedFunc : Type 
ParsedFunc = (ParsedFuncSig, List ParsedStat)

--module

ParsedMod : Type
ParsedMod = Mod (ParsedStat) (ParsedFuncSigTys) ParsedConstant

