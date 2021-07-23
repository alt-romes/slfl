module Main (main) where

import System.Environment
import Debug.Trace
import Control.Monad


import CoreSyntax
import Criterion.Main
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


mainsynth :: String -> IO Expr
mainsynth t =
    let surroundtype = '(':t ++ ")" in
        synthType (parseType surroundtype)


mainsynthAll :: String -> IO [Expr]
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
   typeinferModule cbindings


maintypecheckModule :: String -> IO Program
maintypecheckModule = maindesugarModule


mainevalModule :: String -> IO CoreExpr
mainevalModule fname = do
    synthedp <- mainsynthMarksModule fname
    let cbindings = desugarModule synthedp -- Desugar already synthetised program
    return $ evalModule cbindings


mainsynthMarksModule :: String -> IO Program
mainsynthMarksModule fname = do
    ctbindings <- maindesugarModule fname -- TODO: por causa tb de memoization aqui não faz mal chamar tudo de novo em vez de aproveitar os resultados do primeiro parse right
    synthMarksModule ctbindings





-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = do
    (action:args) <- getArgs
    if action == "bench"
    then do
        -- let benchmarks = map (\x -> "bench/final-" ++ x ++ ".hs") ["1-1", "1-2", "1-3", "1-4", "2-1", "2-2", "2-3", "2-4", "2-5", "2-6", "2-7", "3-1", "3-2", "4-1", "4-2", "4-4", "4-5", "4-6", "4-7", "5-1", "6-1"]
        let benchmarks = map (\x -> "bench/final-" ++ x ++ ".hs") ["7-1"]
        defaultMain [bgroup "synth" (map (\n -> bench n $ nfIO $ (mainsynthMarksModule >=> \(Program _ bs _ _) -> return bs) n) benchmarks)]
    else
        let arg =
                (case args of
                   [] -> error "No second arg"
                   (argx:_) -> argx) in
        case action of
          "synth" -> print . Binding "main" =<< mainsynth arg
          "all" -> print =<< mainsynthAll arg
          "complete" -> mainsynthMarksModule arg >>= print
          "fdesugar" -> print $ maindesugar arg
          "desugar" -> maindesugarModule arg >>= print . _cbinds
          "ftype" -> print $ maintypecheck arg
          "type" -> maintypecheckModule arg >>= print
          "feval" -> print $ maineval arg
          "eval" -> mainevalModule arg >>= print
          "fparse" -> print $ mainparse arg
          "parse" -> mainparseModule arg >>= print
          _ -> print . Binding "main" =<< mainsynth action

