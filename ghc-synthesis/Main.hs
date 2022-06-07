{-# LANGUAGE LinearTypes #-}
module Main where

-- x :: Bool
-- x = _

-- unit :: a -> ()
-- unit = _

-- l :: (a, c, b) %1 -> (c, b, a)
-- l = _

-- f :: (a -> b) -> a -> b
-- f = _

map' :: (a -> b) -> [a] -> [b]
map' = _


data Test a = Test a

t :: Test a %1 -> a
t = _

-- return :: a %1 -> [a]
-- return = _

-- return :: a %1 -> Maybe a
-- return = _

-- fromMaybe :: a %1 -> Maybe a %1 -> a
-- fromMaybe = _

main :: IO ()
main = print $ 1

