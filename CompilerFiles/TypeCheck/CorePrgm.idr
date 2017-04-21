module CorePrgm
import Util.RootUtil
%access public export

DecEq AccessMod where
  decEq Public Public = Yes Refl

Show C0Type where
  show C0Int = "C0Int"
  show C0Str = "C0Str"
--  show Void = "void type"

Show AccessMod where
  show Public = "Public"


(Show statT) => Show (FuncGen statT r a)  where
  show x = "access : " ++ (show $ access x) ++    "\n" ++
           "rtnTy : " ++ (show r)              ++ "\n" ++
           "name : " ++ (show $ name x) ++        "\n" ++
           "params: " ++ (show a)          ++     "\n" ++
           "body: " ++ (show $ body x) 
(Show statT) => Show (QFunc statT) where
  show (MkFunc f) = show f


