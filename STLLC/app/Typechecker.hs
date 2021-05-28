module Typechecker where

import Control.Applicative
import Data.Maybe
import Data.List (sortBy)
import Control.Monad.State
import Control.Monad.Writer (WriterT, writer, runWriterT) 
import Data.Bifunctor
import qualified Data.Map as Map
import Debug.Trace
import qualified Data.Set as Set

import CoreSyntax

data TypeBinding = TypeBinding String Scheme
instance (Show TypeBinding) where
    show (TypeBinding s (Forall ns t)) = s ++ ":\n    " ++ (if null ns then "" else foldl (\p n -> p ++ " " ++ (letters !! n)) "forall" ns ++ ". ") ++ show t ++ "\n"


type BoundCtxt = [Maybe Scheme]
type FreeCtxt = [(String, Scheme)]
type Ctxt = (BoundCtxt, FreeCtxt)

data Constraint = Constraint Type Type -- e.g. [X => Y]
instance Show Constraint where
    show (Constraint t t') = "[" ++ show t ++ " => " ++ show t' ++ "]"

type Substitution = (Type, CoreExpr) -> (Type, CoreExpr) -- F to replace all type variables with interpreted types

type Infer = WriterT [Constraint] (StateT Ctxt (StateT Int Maybe))

-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: CoreExpr -> Infer (Type, CoreExpr)

-- a -o a  ===> forall a . a -o a
-- forall a . a -o a ===> a' -o a'

--  foco : ?b |-    a'     (?b := a') [OK]
--  foco : a' |-    ?b     (?b := a') [OK]
--  foco : ?b |-    ?c     [NOK] (*)   ?b = ?c    ?c = a'
--                                     ?b -o ?c [b := c,c := a]  => ?c -o ?c [NOK]
--  foco : a' |-    b'    [NOK!]


--  x: ?b -o ?b     , y:a' |-   b'     Existencial |-> Universal    Universal |-/-> Existencial
-- ....



-- x: (forall b c . b -o c)  , y:a'|-       b'
-- x: (forall b . b -o b)  |-       a' -o a'
-- x: (forall b . b -o b)  |-       : forall a . a -o a

-- data Bool = True | False 

-- (x:Bool) -o {y:Bool :  x=y}  ~ \x:Bool . case x of  True  ->  x=True | False ->  x=False 

--- |- forall a b . a -o b 

{- 
    let id x = x     
        in
        (id true, id 0)
 -}



--- hyp --------------------

typeconstraint ce@(BLVar x) = do
    ctx <- get
    let (pre, maybesch:end) = splitAt x $ fst ctx
    sch <- lift $ lift $ lift maybesch
    put (pre ++ Nothing:end, snd ctx)
    t <- instantiate sch
    return (t, ce)

typeconstraint ce@(FLVar x) = do
    (bctx, fctx) <- get
    let (maybesch, fctx') = findDelete x fctx []
    sch <- lift $ lift $ lift maybesch
    put (bctx, fctx')
    t <- instantiate sch
    return (t, ce)

typeconstraint ce@(BUVar x) = do
    ctx <- get
    sch <- lift $ lift $ lift $ fst ctx !! x
    t <- instantiate sch
    return (t, ce)

typeconstraint ce@(FUVar x) = do
    ctx <- get
    sch <- lift $ lift $ lift $ lookup x $ snd ctx
    t <- instantiate sch
    return (t, ce)

--- -o ---------------------

--  -oI
typeconstraint (Abs t1 e) = do
    tv <- fresh
    let t1' = fromMaybe tv t1
    (bctx, fctx) <- get
    put (Just (trivialScheme t1'):bctx, fctx)
    (t2, ce) <- typeconstraint e
    return (Fun t1' t2, Abs (Just t1') ce)

--  -oE
typeconstraint (App e1 e2) = do
    tv <- fresh 
    (t1, ce1) <- typeconstraint e1
    (t2, ce2) <- typeconstraint e2
    writer ((tv, App ce1 ce2), [Constraint t1 (Fun t2 tv)])

--- * ----------------------

--  *I
typeconstraint (TensorValue e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    (t2, ce2) <- typeconstraint e2
    return (Tensor t1 t2, TensorValue ce1 ce2)

--  *E
typeconstraint (LetTensor e1 e2) = do
    tv1 <- fresh
    tv2 <- fresh
    (t, ce1) <- typeconstraint e1
    (bctx, fctx) <- get
    put (Just (trivialScheme tv2):Just (trivialScheme tv1):bctx, fctx)
    (t3, ce2) <- typeconstraint e2
    writer ((t3, LetTensor ce1 ce2), [Constraint t (Tensor tv1 tv2)])

--- 1 ----------------------

--  1I
typeconstraint UnitValue = return (Unit, UnitValue)

--  1E
typeconstraint (LetUnit e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    (t2, ce2) <- typeconstraint e2
    writer ((t2, LetUnit ce1 ce2), [Constraint t1 Unit])

--- & ----------------------

--  &I
typeconstraint (WithValue e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    ctx2 <- get
    (t2, ce2) <- typeconstraint e2
    ctx3 <- get
    if equalCtxts ctx2 ctx3
        then return (With t1 t2, WithValue ce1 ce2)
        else empty

--  &E
typeconstraint (Fst e) = do
    vari <- lift $ lift get
    let tv1 = TypeVar vari
    let tv2 = TypeVar $ vari+1
    lift $ lift $ put $ vari+2
    (t, ce) <- typeconstraint e
    writer ((tv1, Fst ce), [Constraint t (With tv1 tv2)])

--  &E
typeconstraint (Snd e) = do
    tv1 <- fresh
    tv2 <- fresh
    (t, ce) <- typeconstraint e
    writer ((tv2, Snd ce), [Constraint t (With tv1 tv2)])

--- + ----------------------

--  +I
typeconstraint (InjL t1 e) = do 
    tv <- fresh
    let t1' = fromMaybe tv t1
    (t2, ce) <- typeconstraint e
    return (Plus t2 t1', InjL (Just t1') ce)

--  +I
typeconstraint (InjR t1 e) = do
    tv <- fresh
    let t1' = fromMaybe tv t1
    (t2, ce) <- typeconstraint e
    return (Plus t1' t2, InjR (Just t1') ce)

--  +E
typeconstraint (CaseOfPlus e1 e2 e3) = do
    (pt, ce1) <- typeconstraint e1
    tv1 <- fresh
    tv2 <- fresh
    (bctx, fctx) <- get
    put (Just (trivialScheme tv1):bctx, fctx)
    (t3, ce2) <- typeconstraint  e2
    ctx3 <- get
    put (Just (trivialScheme tv2):bctx, fctx)
    (t4, ce3) <- typeconstraint  e3
    ctx4 <- get
    if equalCtxts ctx3 ctx4
       then writer ((t4, CaseOfPlus ce1 ce2 ce3), [Constraint t3 t4, Constraint pt (Plus tv1 tv2)])
       else empty

--- ! ----------------------

--  !I
typeconstraint (BangValue e) = do
    ctx <- get
    (t2, ce) <- typeconstraint e
    ctx2 <- get
    if equalCtxts ctx2 ctx
        then return (Bang t2, BangValue ce)
        else empty -- TODO: Assim (\x -o !x) não é sintetisado, mas se calhar o tipo inferido de x devia ser !a

--  !E
typeconstraint (LetBang e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    tv1 <- fresh
    (bctx, fctx) <- get
    put (Just (trivialScheme tv1):bctx, fctx)
    (t2, ce2) <- typeconstraint e2
    writer ((t2, LetBang ce1 ce2), [Constraint t1 (Bang tv1)])

--- LetIn ------------------

typeconstraint (LetIn e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    (bctx, fctx) <- get 
    let t1' = generalize (bctx, fctx) t1 
    put (Just t1':bctx, fctx)
    (t2, ce2) <- typeconstraint e2
    return (t2, LetIn ce1 ce2)

--- Synth marker ---

typeconstraint (Mark i t) = do
    tv <- fresh
    let t' = fromMaybe tv t
    return (t', Mark i (Just t'))

--- Bool -------------------

typeconstraint Tru = return (Bool, Tru)
typeconstraint Fls = return (Bool, Fls)

-- TODO: if true then { ... } else false should synthetize a bool, but doesn't...
typeconstraint (IfThenElse e1 e2 e3) = do
    (t1, ce1) <- typeconstraint e1
    ctx1 <- get
    (t2, ce2) <- typeconstraint e2
    ctx2 <- get
    put ctx1
    (t3, ce3) <- typeconstraint e3
    ctx3 <- get
    if equalCtxts ctx2 ctx3
       then writer ((t3, IfThenElse ce1 ce2 ce3), [Constraint t2 t3, Constraint t1 Bool])
       else empty

typeconstraint (SumValue mts (t, e)) = do
    types <- mapM (\(s, mt) -> do
        tv <- fresh
        let t' = fromMaybe tv mt
        return (s, t')) mts
    (t2, ce) <- typeconstraint e
    return (Sum ((t, t2):types), SumValue (map (second Just) types) (t, ce))

typeconstraint (CaseOfSum e exps) = do
    (st, ce) <- typeconstraint e
    (bctx, fctx) <- get
    inferredexps <- mapM (\(s, ex) -> do
        tv <- fresh
        put (Just (trivialScheme tv):bctx, fctx)
        (t', ce) <- typeconstraint ex
        ctx' <- get
        return (t', s, ce, ctx')
        ) exps
    -- TODO: Probably doable in a more idiomatic way
    let (t1', s1, ce1, ctx1') = head inferredexps
    if all ((== ctx1') . (\(_,_,_,c) -> c)) (tail inferredexps)
       then writer ((t1', CaseOfSum ce (map (\(_,s,c,_) -> (s,c)) inferredexps)), Constraint st (Sum (map (\(t,s,_,_) -> (s, t)) inferredexps)):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps))
       else empty

--- end typeconstraint ----------

---------------------------------
-- type Infer = WriterT [Constraint] (StateT Ctxt (StateT Int Maybe))

fresh :: Infer Type 
fresh = do 
    n <- lift $ lift get 
    lift $ lift $ put (n+1)
    return $ TypeVar n 

instantiate :: Scheme -> Infer Type 
instantiate (Forall ns t) = do
    fs <- mapM (const fresh) ns 
    let s = Map.fromList $ zip ns fs 
    return $ apply s t

-- pre: No free tvars in t
trivialScheme :: Type -> Scheme 
trivialScheme = Forall []

generalize :: Ctxt -> Type -> Scheme
generalize ctxt t = Forall as t 
    where as = Set.toList $ Set.difference (ftv t) (ftvctx ctxt)

---------------------------------

type Subst = Map.Map Int Type

class Substitutable a where
    apply :: Subst -> a -> a

instance Substitutable Scheme where
    apply s (Forall ns t) = Forall ns $ apply s' t 
                            where s' = foldr Map.delete s ns 

instance Substitutable Type where
    apply s (Fun t1 t2) = Fun (apply s t1) (apply s t2)
    apply s (Tensor t1 t2) = Tensor (apply s t1) (apply s t2)
    apply s (With t1 t2) = With (apply s t1) (apply s t2)
    apply s (Plus t1 t2) = Plus (apply s t1) (apply s t2)
    apply s (Bang t) = Bang (apply s t)
    apply s t@(TypeVar i) = Map.findWithDefault t i s
    apply s (Sum tl) = Sum $ map (second $ apply s) tl
    apply s t = t

instance Substitutable CoreExpr where
    apply s (Abs (Just t) e) = Abs (return $ apply s t) (apply s e)
    apply s (App e1 e2) = App (apply s e1) (apply s e2)
    apply s (TensorValue e1 e2) = TensorValue (apply s e1) (apply s e2)
    apply s (LetTensor e1 e2) = LetTensor (apply s e1) (apply s e2)
    apply s (LetUnit e1 e2) = LetUnit (apply s e1) (apply s e2)
    apply s (WithValue e1 e2) = WithValue (apply s e1) (apply s e2)
    apply s (Fst e) = Fst (apply s e)
    apply s (Snd e) = Snd (apply s e)
    apply s (InjL (Just t) e) = InjL (return $ apply s t) (apply s e)
    apply s (InjR (Just t) e) = InjR (return $ apply s t) (apply s e)
    apply s (CaseOfPlus e1 e2 e3) = CaseOfPlus (apply s e1) (apply s e2) (apply s e3)
    apply s (Mark i (Just t)) = Mark i (return $ apply s t)
    apply s (SumValue tl (i, e)) = SumValue (map (second $ apply s) tl) (i, apply s e)
    apply s (CaseOfSum e el) = CaseOfSum (apply s e) (map (second $ apply s) el)
    apply s e = e

instance Substitutable CoreBinding where
    apply s (CoreBinding n e') = CoreBinding n (apply s e')

instance Substitutable a => Substitutable (Maybe a) where
    apply s Nothing = Nothing
    apply s (Just t) = Just (apply s t)

instance Substitutable a => Substitutable [a] where
    apply s l = map (apply s) l

instance (Substitutable a, Substitutable b) => Substitutable ((,) a b) where
    apply s (x, y) = (apply s x, apply s y)


ftv :: Type -> Set.Set Int
ftv = ftv' Set.empty
    where
        ftv' :: Set.Set Int -> Type -> Set.Set Int
        ftv' acc (Fun t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (Tensor t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (With t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (Plus t t') = ftv' acc t `mappend` ftv' acc t'
        ftv' acc (Bang t) = ftv' acc t
        ftv' acc (TypeVar x) = Set.insert x acc
        ftv' acc (Sum []) = acc
        ftv' acc (Sum ((i, t):ts)) = ftv' acc t `mappend` ftv' acc (Sum ts)
        ftv' acc t = acc

ftvctx :: Ctxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> Ctxt -> Set.Set Int
        ftvctx' acc (bc, fc) = Set.unions (map ftvsch (catMaybes bc)) `Set.union` Set.unions (map (ftvsch . snd) fc)
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t

unify :: Type -> Type -> Maybe Subst 
unify Bool Bool = Just Map.empty
unify (Atom x) (Atom y) = if x == y then Just Map.empty else Nothing
unify Unit Unit = Just Map.empty
unify (TypeVar x) (TypeVar y) = if x == y then Just Map.empty else Just $ Map.singleton x (TypeVar y)
unify (TypeVar x) y = if x `notElem` ftv y then Just $ Map.singleton x y else Nothing
unify x (TypeVar y) = if y `notElem` ftv x then Just $ Map.singleton y x else Nothing
unify (Fun t1 t2) (Fun t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (Tensor t1 t2) (Tensor t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (With t1 t2) (With t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (Plus t1 t2) (Plus t1' t2') = do
    s  <- unify t1 t1'
    s' <- unify (apply s t2) (apply s t2')
    return $ compose s' s
unify (Bang x) (Bang y) = unify x y
unify (Sum xtl) (Sum ytl) = do
    let xtl' = sortBy (\(a,_) (b,_) -> compare a b) xtl
    let ytl' = sortBy (\(a,_) (b,_) -> compare a b) ytl
    let maybesubs = zipWith (\x y -> snd x `unify` snd y) xtl' ytl'
    foldM (\p n -> compose p <$> n) Map.empty maybesubs
unify _ _ = Nothing

compose :: Subst -> Subst -> Subst
s' `compose` s = Map.map (apply s') s `Map.union` s'

solveconstraints :: Subst -> [Constraint] -> Maybe Subst -- w/ substitution accumulator and list of constraints generate a substitution
solveconstraints subs constr =
    case constr of
      [] -> return subs
      Constraint t1 t2:cs -> do
          s <- unify t1 t2
          solveconstraints (compose s subs) $ map (\(Constraint t1 t2) -> Constraint (apply s t1) (apply s t2)) cs


typeinfer :: FreeCtxt -> CoreExpr -> Maybe (Type, CoreExpr, Subst)
typeinfer fc e = do
    ((ctype, cexp), constraints) <- evalStateT (evalStateT (runWriterT $ typeconstraint e) ([], fc)) (length fc)
    s <- solveconstraints Map.empty constraints
    let (ctype', cexp') = apply s (ctype, cexp)
    -- TODO: Maybe factor into another function? it's done in infer module?
    -- let sch = generalize ([],[]) ctype'
    return (ctype', cexp', s)
        
 -- typeinfer ........ Abs 0 ~~~~ Forall a . a -o a       

--- util -------------------

findDelete :: (Eq a) => a -> [(a, b)] -> [(a, b)] -> (Maybe b, [(a, b)])
findDelete _ [] _ = (Nothing, [])
findDelete x ((y,t):xs) acc =
    if x==y then (Just t, reverse acc ++ xs)
    else findDelete x xs ((y,t):acc)

equalCtxts :: Ctxt -> Ctxt -> Bool
equalCtxts (ba, fa) (bb, fb) = (catMaybes ba, fa) == (catMaybes bb, fb) || trace "[Typecheck] Failed resource management." False


---- TOP LEVEL ------------

typeinferExpr :: CoreExpr -> CoreExpr
typeinferExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(_, ce, _) -> ce) (typeinfer [] e)

typeinferModule :: [CoreBinding] -> [CoreBinding] -- typecheck and use inferred types
typeinferModule cbs = let (finalcbs, finalsubst) = typeinferModule' cbs [] Map.empty in -- Infer and typecheck iteratively every expression, and in the end apply the final substitution (unified constraints) to all expressions
                          apply finalsubst finalcbs
    where
        typeinferModule' :: [CoreBinding] -> [TypeBinding] -> Subst -> ([CoreBinding], Subst)
        typeinferModule' corebindings acc subst =
            case corebindings of
              [] -> ([], subst)
              b@(CoreBinding n ce):corebindings' -> do
                 let (btype, bexpr, subst') =
                         fromMaybe (errorWithoutStackTrace ("[Typecheck Module] Failed checking: " ++ show b)) $
                             typeinfer (map (\(TypeBinding n t) -> (n, t)) acc) ce
                 first (CoreBinding n bexpr :) $ typeinferModule' corebindings' (TypeBinding n (generalize ([], []) btype):acc) subst'

typecheckExpr :: CoreExpr -> Type
typecheckExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(t, _, _) -> t) (typeinfer [] e)

typecheckModule :: [CoreBinding] -> [TypeBinding]
typecheckModule cbs = typecheckModule' cbs []
    where typecheckModule' cbs acc = 
            if null cbs then []
            else let b@(CoreBinding n ce):xs = cbs in
                 let tb = TypeBinding n $ generalize ([],[]) $ maybe (errorWithoutStackTrace ("[Typecheck Module] Failed checking: " ++ show b)) (\(t, _, _) -> t) $ typeinfer (map (\(TypeBinding n t) -> (n, t)) acc) ce in
                     tb:typecheckModule' xs (tb:acc)

