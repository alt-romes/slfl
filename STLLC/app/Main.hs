module Main (main) where

import System.Environment


import CoreSyntax
import Syntax
import Program
import Parser
import Desugar
import Typechecker
import Evaluate
import Synth
import Util

-- import Text.Parsec

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



-------------------------------------------------------------------------------
-- Inline Programs
-------------------------------------------------------------------------------

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


mainsynthAll :: String -> [Expr]
mainsynthAll t =
    let surroundtype = '(':t ++ ")" in
        synthAllType (parseType surroundtype)





-------------------------------------------------------------------------------
-- Full Programs
-------------------------------------------------------------------------------

mainparseModule :: String -> IO Program
mainparseModule fname = do
    input <- readFile fname
    return $ parseModule fname input


maindesugarModule :: String -> IO CoreProgram
maindesugarModule fname = do
   bindings <- mainparseModule fname
   let cbindings = desugarModule bindings -- Desugaring is automatically followed by typechecking+inference
   return $ typeinferModule cbindings


maintypecheckModule :: String -> IO [TypeBinding]
maintypecheckModule fname = do
    cbindings <- maindesugarModule fname
    return $ typecheckModule cbindings


mainevalModule :: String -> IO CoreExpr
mainevalModule fname = do
    cbindings <- maindesugarModule fname
    return $ evalModule cbindings


mainsynthMarksModule :: String -> IO Program
mainsynthMarksModule fname = do
    bindings <- mainparseModule fname
    ctbindings <- maindesugarModule fname -- TODO: por causa tb de memoization aqui não faz mal chamar tudo de novo em vez de aproveitar os resultados do primeiro parse right
    let nbindings = copyMarksTypesModule bindings ctbindings -- copy marks types to the non-desugared expression from the desugared+inferred expression 
    return $ synthMarksModule nbindings





-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = do
    (action:args) <- getArgs
    let arg =
            (case args of
               [] -> if null action
                        then "(A -o A)"
                        else "llcprogs/main.llc"
               (argx:_) -> argx)
    case action of
      "synth" -> print $ mainsynth arg
      "all" -> print $ mainsynthAll arg
      "complete" -> mainsynthMarksModule arg >>= print 
      "fdesugar" -> print $ maindesugar arg
      "desugar" -> maindesugarModule arg >>= print
      "ftype" -> print $ maintypecheck arg
      "type" -> maintypecheckModule arg >>= mapM_ print
      "feval" -> print $ maineval arg
      "eval" -> mainevalModule arg >>= print
      "fparse" -> print $ mainparse arg
      "parse" -> mainparseModule arg >>= print
      _ -> print $ mainsynth action

