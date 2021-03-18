tru = \t -> (\f -> t)
fls = \t -> (\f -> f)

ltest = \l -> (\m -> (\n -> l m n))

land = \b -> (\c -> b c fls)

-- 5.2.1
lor = \a -> (\b -> a tru b)
lnot = \a -> (a fls tru)

lpair = \f -> (\s -> (\b -> b f s))
lfst = \p -> p tru
lsnd = \p -> p fls

-- Church numerals -> to get a value in haskell apply: lcn succ 0
lc0 = \s -> (\z -> z)
lc1 = \s -> (\z -> s z)
lc2 = \s -> (\z -> s (s z))
lc3 = \s -> (\z -> s (s (s z)))
lc4 = \s -> (\z -> s (s (s (s z))))
lc5 = \s -> (\z -> s (s (s (s (s z)))))

lscc = \n -> (\s -> (\z -> s (n s z)))

lplus = \m -> (\n -> (\s -> (\z -> m s (n s z))))

ltimes = \m -> (\n -> m (lplus n) lc0) -- ltimes lc2 lc3 succ 0 = 6 :)

-- 5.2.4
lpow = \m -> (\n -> n (ltimes m) lc1) -- lpow lc2 lc5 succ 0 = 32 :)

liszro = \m -> m (\x -> fls) tru;

lzz = lpair lc0 lc0
lss = \p -> lpair (lsnd p) (lplus lc1 (lsnd p))
lprd = \m -> lfst (m lss lzz)

-- 5.2.5
lsub = \m -> (\n -> n lprd m)
