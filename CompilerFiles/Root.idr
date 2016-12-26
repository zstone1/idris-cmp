module Main
import Util.UtilRoot
import Interpret.RootInterpret
import Asm.AsmRoot
import Conduct.ConductRoot
import Effects
import Effect.System
import Effect.StdIO
import Effect.File
import Control.IOExcept
--import CoinProblem.RootCoinProblem


main' : SimpleEff.Eff () [SYSTEM, STDIO, FILE (), EXCEPTION String]
main' = do [_, p, o] <- getArgs | [] => putStrLn "Can't happen"
                                | [_] => putStrLn "neither program or out"
                                | [_,_]=> putStrLn "only one of program or out"
                                | _ => putStrLn "Too many args"
           compileToFile' p o

partial -- apparently System's handler of IOExcpet is partial.
main : IO ()
main = do Right () <- runIOExcept (run main') | Left e => putStrLn ("Failure : " ++ e)
          pure ()
          

