import CoreSyntax
import Parser
import Desugar
import LinearCheck
import Evaluate

import Data.Either
import Control.Monad.Reader

import Control.Monad.Trans 
import System.Console.Haskeline 

import System.Environment
import System.IO


process :: String -> IO ()
process line =
  let res = parseExpr line in
  case res of
    Left err -> print err
    Right ex -> print ex

interpret :: IO ()
interpret = runInputT defaultSettings loop 
    where 
    loop = do 
        minput <- getInputLine "> "
        case minput of 
            Nothing -> outputStrLn "Bye."
            Just input -> liftIO (process input) >> loop

-- interpretfile :: IO ()
-- interpretfile = do
--     (fileName:args) <- getArgs
--     contents <- readFile fileName

main :: IO ()
main = interpret



-- run as module

pdesugar :: String -> CoreExpr
pdesugar s = runReader (desugar $ rightParseExpr s) []

pcheck :: String -> Type
pcheck s = typecheck $ pdesugar s

pevaluate :: String -> CoreExpr
pevaluate s =
    let tree = pdesugar s in
    let ty   = typecheck tree in -- make sure is well typed
    eval ([], []) tree
