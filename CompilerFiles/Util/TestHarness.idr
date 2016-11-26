module TestHarness
import Except 
import Control.Monad.State
import Data.Vect
import Data.So

%access export
data FailureReason = FailByAssertion 
                   | Timeout
 
record TestFailure where
  constructor TestFail
  reason : FailureReason
  failStr : String 

record TestState where
  constructor Tr
  tr : List String  
 
testStart : TestState
testStart = Tr []

TestM : Type -> Type
TestM = ExceptT TestFailure (State TestState)

trace : String -> TestM ()
trace s = lift $ modify $ record { tr $= \e => s :: e }

AssertFail : {default () a : Type} -> String -> TestM a
AssertFail s = throw (TestFail FailByAssertion s )

Assert: (f:a->Bool) -> (x:a) -> String -> TestM (So (f x))
Assert pred x err with (pred x)
  | True = pure Oh 
  | False = AssertFail {a=(So False)} err 

AssertTrue: (b:Bool) -> String -> TestM(So b)
AssertTrue b err = Assert (\e=>b) () err

AssertFalse: (b:Bool) -> String -> TestM(So (not b))
AssertFalse b err = AssertTrue (not b) err

Finalize : String -> TestM () -> IO Bool
Finalize name t =
  let (result, state) = runState (run t) testStart in
    case result of
         Left a => do putStrLn (name 
                               ++ " Failed: " ++ (failStr a)
                               ++ " Trace: " ++ (show (tr state))) 
                      pure False
         Right b => do putStrLn (name ++ " Succeeded.")
                       pure True
                
ExecuteAll : Vect n (String, TestM ()) -> IO ()
ExecuteAll all = putStrLn $ show $ !(foldl agg (pure (0,0)) all) where
       agg a (name, t) = do (succ, fail) <- a
                            isSuccess <- Finalize name t
                            if isSuccess 
                               then pure (succ + 1, fail)
                               else pure (succ, fail + 1) 

test1 : TestM ()
test1 = do trace "first"
           trace "second"
           AssertFail "failing here"
           trace " third"

test2 : TestM ()
test2 = do trace "one"
           AssertTrue True "nope"
           pure ()

Try1 : IO ()
Try1 = ExecuteAll [("t1", test1), ("t2", test2)]
--
--
--
--
--
--
--
