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
    bindings <- mainparseModule fname
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
        let benchmarks = map (\x -> "bench/" ++ x ++ ".hs") ["llt1", "llt2", "llt3", "llt4", "list1", "list2", "list3", "list4", "list5", "list6", "list7", "list8", "maybe1", "maybe2", "maybe3", "tree1", "tree2", "tree3", "tree4", "tree5", "map2", "map3", "map5", "map6", "map8", "map9"]
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

