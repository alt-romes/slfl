{-# LANGUAGE LinearTypes #-}
module Main where

id :: a %1 -> a
id = _

g :: (a, b) %1 -> (a, b)
g = _

l :: (a, c, b) %1 -> (c, b, a)
l = _

m :: (a, c, b, a) %1 -> (c, b, a, a)
m = _

main :: IO ()
main = print $ 1
