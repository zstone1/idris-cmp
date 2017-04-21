module FactorConst
import Util.RootUtil
import Models.RootModels


factorConst : (Program ParsedStat ParsedFuncSigTys) -> Comp (Program FactorConstStat ParsedFuncSigTys)
factorConst p = record {p -> 

