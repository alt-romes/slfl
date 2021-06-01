module Main where

import CoreSyntax
import Syntax
import Parser
import Desugar
import Typechecker
import Evaluate
import Synth
import Util

import Data.Either
import Control.Monad.Reader

import Control.Monad.Trans 
import System.Console.Haskeline

import System.Environment
import System.IO

-- import Text.Parsec
import Debug.Trace

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

maintypecheck :: String -> Scheme
maintypecheck = typecheckExpr . maindesugar

maineval :: String -> CoreExpr
maineval = evalExpr . maindesugar

mainsynth :: String -> Expr
mainsynth t =
    let surroundtype = '(':t ++ ")" in
        synthType (parseType surroundtype)

-- TODO: Se eu chamasse _ <- maintypecheck s; e depois e <- maineval s; ele apenas ia correr (desugarExpr . parseExpr) uma vez por causa de memoization certo?

mainsynthAll :: String -> [Expr]
mainsynthAll t =
    let surroundtype = '(':t ++ ")" in
        synthAllType (parseType surroundtype)


---- Modules

mainparseModule :: String -> IO [Binding]
mainparseModule fname = do
    input <- readFile fname
    return $ parseModule fname input

maindesugarModule :: String -> IO [CoreBinding]
maindesugarModule fname = do
   bindings <- mainparseModule fname
   let cbindings = desugarModule bindings -- Desugaring is automatically followed by typechecking+inference
   return $ typeinferModule cbindings

-- when defining a function you can only use the ones defined above

maintypecheckModule :: String -> IO [TypeBinding]
maintypecheckModule fname = do
    cbindings <- maindesugarModule fname
    return $ typecheckModule cbindings

mainevalModule :: String -> IO CoreExpr
mainevalModule fname = do
    cbindings <- maindesugarModule fname
    return $ evalModule cbindings

mainsynthMarksModule :: String -> IO [Binding]
mainsynthMarksModule fname = do
    bindings <- mainparseModule fname
    ctbindings <- maindesugarModule fname -- TODO: por causa tb de memoization aqui não faz mal chamar tudo de novo em vez de aproveitar os resultados do primeiro parse right
    let nbindings = copyMarksTypesModule bindings ctbindings -- copy marks types to the non-desugared expression from the desugared+inferred expression 
    return $ synthMarksModule nbindings



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
      "all" -> print $ mainsynthAll arg
      "complete" -> mainsynthMarksModule arg >>= mapM_ print 
      "fdesugar" -> print $ maindesugar arg
      "desugar" -> maindesugarModule arg >>= mapM_ print
      "ftype" -> print $ maintypecheck arg
      "type" -> maintypecheckModule arg >>= mapM_ print
      "feval" -> print $ maineval arg
      "eval" -> mainevalModule arg >>= print
      "fparse" -> print $ mainparse arg
      "parse" -> mainparseModule arg >>= print
      _ -> print $ mainsynth action
