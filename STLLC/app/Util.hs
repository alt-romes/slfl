{-# LANGUAGE LambdaCase #-}
module Util where

import qualified Data.Map as Map
import Control.Monad



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
getName i = letters !! i
