module TestH

import Effects
import Effect.Exception
import Effect.State
import Effect.Random
import Data.Vect

data FailReason = FailByAssertion
                | Timeout

record TestFailure where
  constructor FailTest
  failRsn : FailReason
  failStr : String

Test1 : Eff Integer [EXCEPTION String, RND]
Test1 = do if True
              then raise "oh boy"
              else (rndInt  0 100) 

Test2 : Eff Integer [EXCEPTION String, RND]
Test2 = do x <- Test1
           y <- Test1
           pure (x+y)
           
Test3 : Eff Int [STATE Int]
Test3 = do update (+ 1)
           get

Handle1 : Eff a [EXCEPTION String, EXCEPTION Bool, RND ] -> String
Handle1 {a} x with (the (Either String,Bool|) a) $ run x)
  | Left p = "foo"
  | Right p = "bar"


Bar1 : Int
Bar1 =  runPure Test3







