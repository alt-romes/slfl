module Main where

import CoreSyntax
import Syntax
import Parser
import Desugar
import LinearCheck
import Evaluate
import Synth

import Data.Either
import Control.Monad.Reader

import Control.Monad.Trans 
import System.Console.Haskeline

import System.Environment
import System.IO

import Text.Parsec

-- process :: String -> IO ()
-- process line = print $ parseExpr line

-- interpret :: IO ()
-- interpret = runInputT defaultSettings loop 
--     where 
--     loop = do 
--         minput <- getInputLine "> "
--         case minput of 
--             Nothing -> outputStrLn "Bye."
--             Just input -> liftIO (process input) >> loop


---- Single Expressions

mainparse :: String -> Expr
mainparse = parseExpr

maindesugar :: String -> CoreExpr
maindesugar = desugarExpr . mainparse

maintypecheck :: String -> Type
maintypecheck = typecheckExpr . maindesugar

maineval :: String -> CoreExpr
maineval = evalExpr . maindesugar

mainsynth :: String -> Expr
mainsynth t =
    let surroundtype = '(':t ++ ")" in
        synthType (parseType surroundtype)

-- TODO: Se eu chamasse _ <- maintypecheck s; e depois e <- maineval s; ele apenas ia correr (desugarExpr . parseExpr) uma vez por causa de memoization certo?



---- Modules

mainparseModule :: String -> IO [Binding]
mainparseModule fname = do
    input <- readFile fname
    return $ parseModule fname input

maindesugarModule :: String -> IO [CoreBinding]
maindesugarModule fname = do
   bindings <- mainparseModule fname
   return $ desugarModule bindings

-- when defining a function you can only use the ones defined above

maintypecheckModule :: String -> IO [TypeBinding]
maintypecheckModule fname = do
    cbindings <- maindesugarModule fname
    return $ typecheckModule cbindings

mainevalModule :: String -> IO CoreExpr
mainevalModule fname = do
    cbindings <- maindesugarModule fname
    let _ = typecheckModule cbindings in -- make sure module is well typed
        return $ evalModule cbindings

mainsynthMarksModule :: String -> IO [Binding]
mainsynthMarksModule fname = do
    targets <- mainparseModule fname
    return $ synthMarksModule targets



---- Main

main :: IO ()
main = do
    (action:args) <- getArgs
    let arg =
            (case args of
               [] -> if null action
                        then "(A -o A)"
                        else "llcprogs/main.llc"
               (arg:oargs) -> arg)
    case action of
      "synth" -> print $ mainsynth arg
      "complete" -> mainsynthMarksModule arg >>= mapM_ print 
      "desugar" -> maindesugarModule arg >>= mapM_ print
      "type" -> maintypecheckModule arg >>= mapM_ print
      "eval" -> mainevalModule arg >>= print
      _ -> print $ mainsynth action
