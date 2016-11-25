module TestHarness
import Error
import Control.Monad.State
import Data.Vect

%access export
data FailureReason = FailByAssertion 
                   | Timeout
 
record TestFailure where
  constructor TestFail
  reason: FailureReason
  failStr : String 

TestM: Type -> Type
TestM = ErrorM TestFailure

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
  passCount: Nat
  failures: (n:Nat ** Vect n (String, String))

InitRun:TestRunState
InitRun= StartRun Z (Z ** [])

TestState:Type -> Type
TestState a = State TestRunState a

private
TestSuccess: TestRunState -> TestRunState
TestSuccess r = record {passCount $= S} r   

private
TestFailed: (name:String) -> (failstr:String) -> TestRunState -> TestRunState
TestFailed name failstr state = 
  let (_ ** fails) = failures state in
  let nextFail = (name, failstr) in
      record {failures = (_ ** nextFail :: fails)} state 

RunTest: String -> TestM a -> TestState ()
RunTest name (Success _) = put $ TestSuccess !get
RunTest name (Fail f) = put $ TestFailed name (failStr f) !get

TotalTests: TestState Nat
TotalTests =  do s <- get
                 let passes = passCount s
                 let fails = fst $ failures s
                 pure $ passes + fails

NoTestRunZ: evalState TotalTests InitRun = Z
NoTestRunZ = ?NoTestRunZ_rhs












