module Main
import Util.RootUtil
--import Interpret.RootInterpret
--import TypeCheck.RootTypeCheck
--import Asm.RootAsm
--import Conduct.RootConduct
--import Models.RootModels
--import Effects
--import Effect.System
--import Effect.StdIO
--import Effect.File
--import Control.IOExcept
--import CoinProblem.RootCoinProblem


--main' : SimpleEff.Eff () ([SYSTEM, STDIO, FILE ()] ++ CompEffs)
--main' = do [_, p, o] <- getArgs | [] => putStrLn "Can't happen"
--                                | [_] => putStrLn "neither in nor out arg"
--                                | [_,_]=> putStrLn "only one of in or out arg"
--                                | _ => putStrLn "Too many args"
--           compileToFile' p o

--partial -- apparently System's handler of IOExcpet is partial.
--main : IO ()
--main = do Right () <- runIOExcept (run main') | Left e => putStrLn ("Failure : " ++ e)
--          pure ()
          

