module Core
import Util.RootUtil
%access public export

data BuiltInType = C0Int 
                 | C0Str 

parseBuiltInType : String -> Comp BuiltInType
parseBuiltInType s = case s of 
                          "int" => pure C0Int
                          "string" => pure C0Str
                          _ => monadEffT $ raise (" cannot parse " ++ s ++ " into a built int type")

data AccessMod = Public | Private

parseAccess :  String -> Comp AccessMod
parseAccess s = case s of 
                     "public" => pure Public
                     "private" => pure Private
                     _ => monadEffT $raise ("cannot parse " ++ s ++ " as an access modifier")

ConstantBaseTypes :List Type
ConstantBaseTypes = [Int, String]

DecEq BuiltInType where
  decEq C0Int C0Int = Yes Refl
  decEq C0Str C0Str = Yes Refl
  decEq _ _ = No (believe_me()) --Find a better way to build these trivial DecEq types




