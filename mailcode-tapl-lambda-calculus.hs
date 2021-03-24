{-# LANGUAGE RankNTypes #-}

import Prelude hiding (succ, pred)

type ChurchBool = forall a. a -> a -> a
true :: ChurchBool
true = \t -> \f -> t

false :: ChurchBool
false = \t -> \f -> f

type ChurchNum = forall a. (a -> a) -> a -> a
newtype Church = Church { unChurch :: ChurchNum }

zero :: Church
zero = Church $ \f -> \x -> x

succ :: Church -> Church
succ = \n -> Church $ \f -> \x -> f (unChurch n f x)

pair :: a1 -> a2 -> (a1 -> a2 -> a) -> a
pair = \x -> \y -> \z -> z x y

first :: ((a2 -> a1 -> a2) -> a) -> a
first = \p -> p (\x -> \y -> x)

second :: ((a1 -> a2 -> a2) -> a) -> a
second = \p -> p (\x -> \y -> y)

pair_zero = pair zero zero
pair_succ = \p -> pair (second p) (succ (second p))

pred :: Church -> Church
pred = \m -> Church $ unChurch (first ((unChurch m) pair_succ pair_zero))

unchurch_num :: Church -> Integer
unchurch_num = \a -> unChurch a (\b -> b + 1) (0)

sub :: Church -> Church -> Church
sub = \m -> \n -> unChurch n pred m
