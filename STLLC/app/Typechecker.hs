module Typechecker where

import Debug.Trace
import Data.Bifunctor (first, second)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer (WriterT, writer, runWriterT) 

import CoreSyntax
import Constraints hiding (Ctxt)
import Util (findDelete)

data TypeBinding = TypeBinding String Scheme
instance (Show TypeBinding) where
    show (TypeBinding s (Forall ns t)) = s ++ ":\n    " ++ (if null ns then "" else foldl (\p n -> p ++ " " ++ (letters !! n)) "forall" ns ++ ". ") ++ show t ++ "\n"


type BoundCtxt = [Maybe Scheme]
type FreeCtxt = [(String, Scheme)]
type Ctxt = (BoundCtxt, FreeCtxt)

type Substitution = (Type, CoreExpr) -> (Type, CoreExpr) -- F to replace all type variables with interpreted types

type Infer = WriterT [Constraint] (StateT Ctxt (StateT Int Maybe))

runinfer :: FreeCtxt -> CoreExpr -> Maybe ((Type, CoreExpr), [Constraint])
runinfer fc e = evalStateT (evalStateT (runWriterT $ typeconstraint e) ([], fc)) (length fc)

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
    ctx1 <- get
    (t1, ce1) <- typeconstraint e1
    ctx2 <- get
    put ctx1
    (t2, ce2) <- typeconstraint e2
    ctx3 <- get
    if equalCtxts ctx2 ctx3
        then return (With t1 t2, WithValue ce1 ce2)
        else empty

--  &E
typeconstraint (Fst e) = do
    tv1 <- fresh
    tv2 <- fresh
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
    (bctx, fctx) <- get
    tv1 <- fresh
    tv2 <- fresh
    put (Just (trivialScheme tv1):bctx, fctx)
    (t3, ce2) <- typeconstraint e2
    ctx3 <- get
    put (Just (trivialScheme tv2):bctx, fctx)
    (t4, ce3) <- typeconstraint e3
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
    (bctx, fctx) <- get
    tv1 <- fresh
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
    guard $ all ((== ctx1') . (\(_,_,_,c) -> c)) (tail inferredexps)
    writer ((t1', CaseOfSum ce (map (\(_,s,c,_) -> (s,c)) inferredexps)), Constraint st (Sum (map (\(t,s,_,_) -> (s, t)) inferredexps)):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps))

--- end typeconstraint ----------

---------------------------------

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

typeinfer :: FreeCtxt -> CoreExpr -> Maybe (Type, CoreExpr, Subst)
typeinfer fc e = do
    ((ctype, cexp), constraints) <- runinfer fc e
    s <- solveconstraints Map.empty constraints
    let (ctype', cexp') = apply s (ctype, cexp)
    -- TODO: Maybe factor into another function?
    -- TODO: Typeinfer should return a scheme?
    -- TODO: Generalize and instantiate to get free vars starting from a, b ...
    -- let sch = generalize ([],[]) ctype'
    return (ctype', cexp', s)
        
--- util -------------------

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
