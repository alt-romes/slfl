{-# LANGUAGE LinearTypes, NoImplicitPrelude #-}
module Linear where

f :: (a, a) %1 -> (a, a)
f = \a -> case a of
            (b, c) -> (b, c)



