module Core
import Util.RootUtil
%access public export

data BuiltInType = C0Int 
                 | C0Str 

data AccessMod = Public

parseAccess :  String -> Comp AccessMod
parseAccess s = case s of 
                     "public" => pure Public
                     _ => monadEffT $raise ("cannot parse " ++ s ++ " as an access modifier")

ConstantBaseTypes :List Type
ConstantBaseTypes = [Int, String]

DecEq BuiltInType where
  decEq C0Int C0Int = Yes Refl
  decEq C0Int _ = No (believe_me()) --Find a better way to build these trivial DecEq types
  decEq C0Str C0Str = Yes Refl
  decEq C0Str _ = No (believe_me())




