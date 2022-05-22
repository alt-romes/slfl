{-# LANGUAGE LinearTypes #-}
module Main where

id :: a %1 -> a
id = _

g :: (a, b) %1 -> (a, b)
g = _

main :: IO ()
main = print $ 1
