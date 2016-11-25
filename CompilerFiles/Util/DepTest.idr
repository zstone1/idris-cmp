module TestHarness
import Error
import Control.Monad.State
import Data.Vect

%access public export
data FailureReason = FailByAssertion 
                   | Timeout
 
record TestFailure where
  constructor TestFail
  Reason: FailureReason
  FailString : String 

TestM: Type -> Type
TestM = ErrorM {e=TestFailure}

AssertFail: String -> TestM a
AssertFail s = Fail (TestFail FailByAssertion s)

Assert: (f:a->Bool) -> a -> String -> TestM a
Assert pred x err =
  if pred x 
  then Success x 
  else AssertFail err

AssertTrue: Bool -> String -> TestM()
AssertTrue b err = Assert (\e=>b) () err

AssertFalse: Bool -> String -> TestM()
AssertFalse b err = AssertTrue (not b) err

record TestRunState where
  constructor StartRun
  passCount:Int
  failures: (n:Nat ** Vect n (string, string))

TestState:Type -> Type
TestState a = State TestRunState a

WTFTestM : TestM a -> TestFailure 
WTFTestM (Success x) = ?WTFTestM_rhs_1
WTFTestM (Fail x) = x

RunTest: (String,TestM a) -> TestState ()
RunTest (name, test) = 
  do y <- get
     let newState:TestRunState = 
       case test of
            Success succ => record {passCount $= (+1)} y
            Fail fl => y
     put $ newState
   

    
