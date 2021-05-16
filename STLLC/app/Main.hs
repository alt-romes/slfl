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

rparse :: String -> Expr
rparse s = case parseExpr s of
             Left x -> error $ "[Expr Parse] Failed: " ++ show x
             Right x -> x

pdesugar :: String -> CoreExpr
pdesugar s = runReader (desugar $ rparse s) []

pcheck :: String -> Type
pcheck s = typecheck $ pdesugar s

pevaluate :: String -> CoreExpr
pevaluate s =
    let tree = pdesugar s in
    let ty   = typecheck tree in -- make sure is well typed
    evalExpr tree

ptype :: String -> Type
ptype s = case parseType s of
             Left x -> error $ "[Expr Parse] Failed: " ++ show x
             Right x -> x

-- modules

mparse :: String -> IO [Binding] -- module parse
mparse fname = do
    input <- readFile fname
    let pmod = parseModule fname input in
        case pmod of
          Left x -> do { print x; error "[Module Parse] Failed" }
          Right x -> return x

mdesugar :: String -> IO [CoreBinding]
mdesugar fname = do
   pbindings  <- mparse fname
   return $ desugarModule pbindings

-- when defining a function you can only use the ones defined above

mcheck :: String -> IO [TypeBinding]
mcheck fname = do
    cbindings <- mdesugar fname
    return $ typecheckModule cbindings

mevaluate :: String -> IO CoreExpr
mevaluate fname = do
    cbindings <- mdesugar fname
    let _ = typecheckModule cbindings in -- make sure module is well typed
        return $ evaluateModule cbindings

-- main :: IO ()
-- main = do
--     (fname:args) <- getArgs
--     p <- mparse fname
--     print p
--     d <- mdesugar fname
--     print d
--     t <- mcheck fname
--     print t
--     e <- mevaluate fname
--     print e

main = do
    (t:args) <- getArgs
    let surroundtype = '(':t ++ ")"
    print $ synthType (ptype surroundtype)
