{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
module Main where

data Ur a where
    Ur :: a -> Ur a

-- f :: (a %1 -> b) %1 -> a %1 -> b
-- f = _

-- return :: a %1 -> Maybe a
-- return = _

-- empty :: Maybe a
-- empty = _

-- map' :: (a %1 -> b) -> [a] %1 -> [b]
-- map' = _

map' :: Ur (Int %1 -> Char) %1 -> [Int] %1 -> [Char]
map' = _

-- bind :: Maybe a %1 -> (a %1 -> Maybe b) -> Maybe b
-- bind = _

main :: IO ()
main = print $ 1

