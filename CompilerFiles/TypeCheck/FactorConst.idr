module FactorConst
import TypeCheck.CorePrgm
import TypeCheck.Typed
import Util.RootUtil
%access public export

data ConstTyped : C0Type -> Type where
  StringConst : (name:String) -> (val :String) -> ConstTyped C0Str
  NumConst : (name : String) -> (val : Int) -> ConstTyped C0Int

constName : ConstTyped t -> String
constName (StringConst n _)= n
constName (NumConst n _) =  n

data TermFactorConst : C0Type -> Type where
  FromConst : ConstTyped t -> TermFactorConst t
  ApplyFunc : (name: String) -> (rtn : C0Type)-> 
              Vect n (t:C0Type ** TermFactorConst t) -> 
              TermFactorConst rtn

StatFactorConst : Type
StatFactorConst = StatGen TermFactorConst

FuncFactorConst : Type
FuncFactorConst = QFunc StatFactorConst

ProgramFactorConst : Type
ProgramFactorConst = Program FuncFactorConst (t:C0Type ** ConstTyped t) NoFacts

%access private
Consts : Type
Consts = List (t:C0Type ** ConstTyped t)

FactorConstEff : {ty:Type -> Type} -> Type -> Type
FactorConstEff {ty} = Comp{ty} {l= (STATE Consts) :: CompEffs}

--This is just a stub for when the parser can generate constants
seed : ProgramTyped -> Comp Consts 
seed (MkProgram _ [] _) = pure []
seed (MkProgram _ (x::xs) _) = absurd x


factorTerm : TermTyped t -> FactorConstEff (TermFactorConst t)
factorTerm (MkIntLit i) = do let const = NumConst !nextName i
                             update ((_**const) ::)
                             pure (FromConst const)
factorTerm (MkStrLit s) = do let const = StringConst !nextName s
                             update ((_**const) ::)
                             pure (FromConst const)
factorTerm (ApplyFunc n r x) = do 
  let map = (\(_**e)=> assert_total [(_**factorTerm e)])
  args <- traverseM map x 
  pure (ApplyFunc n r args) 


factorStat : StatTyped -> FactorConstEff StatFactorConst
factorStat (Return t val) = pure$ Return _ !(factorTerm val)


factorFunc : FuncTyped -> FactorConstEff FuncFactorConst
factorFunc (MkFunc {rtnTy} {args} (MkFuncGen a n ns b)) = do
  stats <- traverseM factorStat b 
  pure (MkFunc {rtnTy} {args} (MkFuncGen a n ns stats ))


factorFuncs : ProgramTyped -> FactorConstEff (List FuncFactorConst, Consts)
factorFuncs (MkProgram fs cs _) = [(traverseM factorFunc fs, get)]

export 
factorConstsPrgm : ProgramTyped -> Comp{ty=ty} ProgramFactorConst
factorConstsPrgm p {ty} = do
  (fs, cs) <- new (STATE Consts) !(seed p) (factorFuncs p)
  pure $ MkProgram fs cs Nothing --It would be nice to include a proof that every const is accounted for
  


                   


   
