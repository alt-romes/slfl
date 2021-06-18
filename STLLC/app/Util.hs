{-# LANGUAGE LambdaCase #-}
module Util where

import Text.PrettyPrint
import qualified Data.Map as Map
import Control.Monad
import qualified Data.Either as Either
import qualified Data.Set as Set
import Data.Maybe



-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)


letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']


getName :: Int -> String
getName i = if i < 0 then '-' : letters !! (-i) else letters !! i


getNumCode :: String -> Int
getNumCode n = fromJust $ lookup n [("a", 0), ("b", 1), ("c", 2), ("d", 3), ("e", 4), ("f", 5), ("g", 6), ("h", 7), ("i", 8), ("j", 9), ("k", 10)] -- TODO: find way to parse type vars and to get their value


mparens :: String -> String
mparens s = "(" ++ s ++ ")"

count :: Eq a => a -> [a] -> Int
count x = length . filter (== x)





-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

class Pretty p where
    ppr :: Int -> p -> Doc

    pp :: p -> Doc
    pp = ppr 0


parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

