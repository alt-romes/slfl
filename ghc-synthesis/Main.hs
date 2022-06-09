{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE LinearTypes #-}
module Main where

data Ur a where
    Ur :: a -> Ur a

data A
data B
data C
data R

data State b a = State (b -> (a, Ur b))

-- f :: (a %1 -> b) %1 -> a %1 -> b
-- f = _

-- return :: A %1 -> Maybe A
-- return = _

-- empty :: Maybe A
-- empty = _

-- map' :: (a %1 -> b) -> [a] %1 -> [b]
-- map' = _

-- t :: Ur a
-- t = _

map' :: (A %1 -> B) -> [A] %1 -> [B]
map' = _

-- m :: a
-- m = _

-- (>>=) :: Maybe A %1 -> (A %1 -> Maybe B) -> Maybe B
-- (>>=) = _

-- return :: A %1 -> State B A
-- return = _

-- (>>=) :: State B A %1 -> (A %1 -> Maybe B) -> Maybe B
-- (>>=) = _

-- runState :: State B A %1 -> (B -> (A, Ur B))
-- runState = _


-- bind :: State C A %1 -> (A %1 -> State C B) %1 -> State C B
-- bind = _

main :: IO ()
main = print $ 1

