import CoreSyntax
import Parser
import Desugar
import LinearSequentCheck

import Data.Either
import Control.Monad.Reader

import Control.Monad.Trans 
import System.Console.Haskeline 


process :: String -> IO ()
process line =
  let res = parseExpr line in
  case res of
    Left err -> print err
    Right ex -> print ex

main :: IO ()
main = runInputT defaultSettings loop 
    where 
    loop = do 
        minput <- getInputLine "> "
        case minput of 
            Nothing -> outputStrLn "Bye."
            Just input -> liftIO (process input) >> loop


-- run as module

pdesugar :: String -> CoreExpr
pdesugar s = runReader (desugar $ rightParseExpr s) []

pcheck :: String -> Type
pcheck s = typecheck $ pdesugar s
