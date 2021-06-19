module Main (main) where

import System.Environment
import Debug.Trace


import CoreSyntax
import Syntax
import Program
import Parser
import Desugar
import Typechecker
import Evaluate
import Synth
import Util



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


maindesugarModule :: String -> IO Program
maindesugarModule fname = do
   bindings <- mainparseModule fname
   let cbindings = desugarModule bindings -- desugaring is automatically followed by typechecking+inference
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
    return $ synthMarksModule ctbindings 





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
      "complete" -> mainsynthMarksModule arg >>= print . frontend
      "fdesugar" -> print $ maindesugar arg
      "desugar" -> maindesugarModule arg >>= print . _cbinds
      "ftype" -> print $ maintypecheck arg
      "type" -> maintypecheckModule arg >>= mapM_ print
      "feval" -> print $ maineval arg
      "eval" -> mainevalModule arg >>= print
      "fparse" -> print $ mainparse arg
      "parse" -> mainparseModule arg >>= print
      _ -> print $ mainsynth action

