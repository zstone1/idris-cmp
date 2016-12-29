module Link
import Util.RootUtil
import TypeCheck.CorePrgm
import TypeCheck.Typed
import TypeCheck.FactorConst
%access public export

SeedFuncs : List (String, C0Type, (n:Nat ** Vect n C0Type))
SeedFuncs = [("printf", Void, (_**[C0Str]))]


