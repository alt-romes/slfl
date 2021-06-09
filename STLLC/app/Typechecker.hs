module Typechecker (typeinferExpr, typeinferModule, typecheckExpr, typecheckModule, TypeBinding(..)) where

import Debug.Trace
import Data.Bifunctor (first, second)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer (WriterT, writer, runWriterT) 


import CoreSyntax
import Program
import Constraints
import Util (findDelete)


type BoundCtxt = [Maybe Scheme]
type FreeCtxt = [(String, Scheme)]
type Ctxt = (BoundCtxt, FreeCtxt)

-------------------------------------------------------------------------------
-- Datatypes
-------------------------------------------------------------------------------

data TypeBinding = TypeBinding String Scheme





-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Show TypeBinding) where
    show (TypeBinding s sch) = s ++ ":\n    " ++ show sch ++ "\n"





-------------------------------------------------------------------------------
-- Infer "Monad"
-------------------------------------------------------------------------------

type Infer = WriterT [Constraint] (StateT Ctxt (StateT Int Maybe))


runinfer :: FreeCtxt -> CoreExpr -> Maybe (((Type, CoreExpr), [Constraint]), Ctxt)
runinfer fc e = evalStateT (runStateT (runWriterT $ typeconstraint e) ([], fc)) (length fc)


-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

addtoboundctx :: Scheme -> Infer ()
addtoboundctx c = modify (first (Just c :))


wasBLVConsumed :: Int -> Infer Bool
wasBLVConsumed i = do
    (bc, _) <- get
    return $ isNothing $ bc !! (length bc - 1 - i) -- Appends are done to the head of the list, so check the index counting from the end


getlastvarindex :: Infer Int
getlastvarindex = gets (\(bc, _) -> length bc - 1)


equalDeltas :: Ctxt -> Ctxt -> Bool
equalDeltas (ba, _) (bb, _) = catMaybes ba == catMaybes bb || trace "[Typecheck] Failed resource management." False


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


-- TODO: Generalize for tuple of sets and place in util? kind of hard bc of the maybes or not maybes ;) maybe i should unify all contexts
ftvctx :: Ctxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> Ctxt -> Set.Set Int
        ftvctx' acc (bc, fc) = Set.unions (map ftvsch (catMaybes bc)) `Set.union` Set.unions (map (ftvsch . snd) fc)
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t




-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: CoreExpr -> Infer (Type, CoreExpr)

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
    addtoboundctx $ trivialScheme t1'
    newvari <- getlastvarindex
    (t2, ce) <- typeconstraint e
    wasBLVConsumed newvari >>= guard
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
    addtoboundctx $ trivialScheme tv1
    addtoboundctx $ trivialScheme tv2
    lastvari <- getlastvarindex
    (t3, ce2) <- typeconstraint e2
    wasBLVConsumed (lastvari - 1) >>= guard -- make sure linear variables were used and don't exit the binder
    wasBLVConsumed lastvari >>= guard
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
    guard $ equalDeltas ctx2 ctx3
    return (With t1 t2, WithValue ce1 ce2)

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
    currentctx <- get
    tv1 <- fresh
    tv2 <- fresh
    addtoboundctx $ trivialScheme tv1
    lastvi1 <- getlastvarindex
    (t3, ce2) <- typeconstraint e2
    wasBLVConsumed lastvi1 >>= guard -- make sure branch bound var doesn't escape
    ctx3 <- get
    put currentctx -- reset context to synth with the same context as the one used above
    addtoboundctx $ trivialScheme tv2
    lastvi2 <- getlastvarindex
    (t4, ce3) <- typeconstraint e3
    wasBLVConsumed lastvi2 >>= guard -- make sure branch bound var doesn't escape
    ctx4 <- get
    guard $ equalDeltas ctx3 ctx4
    writer ((t4, CaseOfPlus ce1 ce2 ce3), [Constraint t3 t4, Constraint pt (Plus tv1 tv2)])

--- ! ----------------------

--  !I
typeconstraint (BangValue e) = do
    ctx <- get
    (t2, ce) <- typeconstraint e
    ctx2 <- get
    guard $ equalDeltas ctx2 ctx
    return (Bang t2, BangValue ce)

--  !E
typeconstraint (LetBang e1 e2) = do
    (t1, ce1) <- typeconstraint e1
    tv1 <- fresh
    addtoboundctx $ trivialScheme tv1 -- this var can, and will, escape because it'll be used unrestrictedly
    (t2, ce2) <- typeconstraint e2
    writer ((t2, LetBang ce1 ce2), [Constraint t1 (Bang tv1)])

--- LetIn ------------------

typeconstraint (LetIn e1 e2) = do
    c <- get
    (t1, ce1) <- typeconstraint e1
    c'@(bctx, fctx) <- get 
    guard $ equalDeltas c c' -- LetIn makes first variable unrestricted, so e1 should typecheck on an empty delta
    addtoboundctx $ generalize c' t1
    (t2, ce2) <- typeconstraint e2
    return (t2, LetIn ce1 ce2)

--- Synth marker ---

typeconstraint (Mark i _ t) = do
    tv <- fresh
    (bc, fc) <- get
    let t' = fromMaybe tv t
    return (t', Mark i (nontrivialschemes fc []) (Just t')) -- TODO: Apenas contexto quantificado universalmente no free context vai poder ser utilizado na mark porque tenho a certeza que é unrestricted e porque não tenho de inventar um nome novo que não pensei ainda como fazer, se quisessemos utilizar coisas do contexto linear tenho de modificar as variáveis para elas terem informação sobre se são lineares ou não para poder guardar na Mark o contexto linear e o unrestricted para o saber passar para o sintetisador
        where
            nontrivialschemes [] acc = acc
            nontrivialschemes ((n, Forall ns t):xs) acc =
                if null ns
                   then nontrivialschemes xs acc
                   else nontrivialschemes xs ((n, Forall ns t):acc)

--- Bool -------------------

typeconstraint Tru = return (Bool, Tru)
typeconstraint Fls = return (Bool, Fls)

-- TODO: if true then { ... } else false should synthetize a bool, but doesn't...
typeconstraint (IfThenElse e1 e2 e3) = do -- !TODO: Remove bools, make ifthenelse part of desugaring
    (t1, ce1) <- typeconstraint e1
    ctx1 <- get
    (t2, ce2) <- typeconstraint e2
    ctx2 <- get
    put ctx1
    (t3, ce3) <- typeconstraint e3
    ctx3 <- get
    guard $ equalDeltas ctx2 ctx3
    writer ((t3, IfThenElse ce1 ce2 ce3), [Constraint t2 t3, Constraint t1 Bool])

--- Sum --------------------

-- sumI
typeconstraint (SumValue mts (t, e)) = do
    types <- mapM (\(s, mt) -> do
        tv <- fresh
        let t' = fromMaybe tv mt
        return (s, t')) mts
    (t2, ce) <- typeconstraint e
    return (Sum ((t, t2):types), SumValue (map (second Just) types) (t, ce))

-- sumE
typeconstraint (CaseOfSum e exps) = do
    (st, ce) <- typeconstraint e
    (bctx, fctx) <- get
    inferredexps <- mapM (\(s, ex) -> do
        tv <- fresh
        addtoboundctx $ trivialScheme tv
        (t', ce) <- typeconstraint ex
        ctx' <- get
        return (t', s, ce, ctx')
        ) exps
    -- TODO: Probably doable in a more idiomatic way
    let (t1', s1, ce1, ctx1') = head inferredexps
    guard $ all ((== ctx1') . (\(_,_,_,c) -> c)) (tail inferredexps)
    writer ((t1', CaseOfSum ce (map (\(_,s,c,_) -> (s,c)) inferredexps)), Constraint st (Sum (map (\(t,s,_,_) -> (s, t)) inferredexps)):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps))

--- ADT --------------------

-- adtI is done by checking the free context for the constructors

-- adtE
typeconstraint (CaseOf e exps) = do
    (st, ce) <- typeconstraint e
    currentctx@(bctx, fctx) <- get
    inferredexps <- mapM (\(s, ex) -> do
        put currentctx -- reset ctx for every branch
        case lookup s fctx of
            Just (Forall [] (Fun argtype (ADT _))) -> do -- Constructor takes an argument
                addtoboundctx $ trivialScheme argtype
                lastvi <- getlastvarindex
                (t', ce) <- typeconstraint ex
                wasBLVConsumed lastvi >>= guard -- Variable bound in branch must be linearly
                ctx' <- get
                return $ Just (t', s, ce, ctx')
            Just (Forall [] (ADT _)) -> do -- Constructor does not take an argument
                (t', ce) <- typeconstraint ex
                ctx' <- get
                return $ Just (t', s, ce, ctx')
            _ -> return Nothing
        ) exps
    -- TODO: Probably doable in a more idiomatic way
    let inferredexps' = catMaybes inferredexps
    let (t1', s1, ce1, ctx1') = head inferredexps'
    guard $ all ((== first catMaybes ctx1') . (\(_,_,_,c) -> first catMaybes c)) (tail inferredexps')
    let adtname = getadtname fctx s1
    guard $ all ((== adtname) . (\(_,constr,_,_) -> getadtname fctx constr)) (tail inferredexps')
    writer ((t1', CaseOf ce (map (\(_,s,c,_) -> (s,c)) inferredexps')), Constraint st (ADT adtname):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps'))
        where
            getadtname fctx s = case lookup s fctx of
                        Just (Forall [] (Fun _ (ADT adtname))) -> adtname -- Constructor takes an argument
                        Just (Forall [] (ADT adtname)) -> adtname -- Constructor does not take an argument


typeinfer :: FreeCtxt -> CoreExpr -> Maybe (Type, CoreExpr, Subst)
typeinfer fc e = do
    (((ctype, cexp), constraints), (bc, _)) <- runinfer fc e
    -- guard (...) -- TODO: No linear variables in the exit context -- todo: annotate variables with linearity
    s <- solveconstraints Map.empty constraints
    let (ctype', cexp') = apply s (ctype, cexp)
    return (ctype', cexp', s)
    -- TODO: Maybe factor into another function?
    -- TODO: Typeinfer should return a scheme? let sch = generalize ([],[]) ctype'
    -- TODO: Generalize and instantiate from the beginning to get free vars starting from a, b ... ?





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

processadts :: [ADTD] -> [TypeBinding]
processadts = concatMap processadt
    where
        processadt :: ADTD -> [TypeBinding]
        processadt (ADTD tn cns) = map processcns cns
            where
                processcns (cn, Unit) = TypeBinding cn (trivialScheme (ADT tn))
                processcns (cn, ty) = TypeBinding cn (trivialScheme (Fun ty (ADT tn)))





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

typeinferExpr :: CoreExpr -> CoreExpr
typeinferExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(_, ce, _) -> ce) (typeinfer [] e)


typeinferModule :: CoreProgram -> CoreProgram -- typecheck and use inferred types
typeinferModule (CoreProgram adts cbs) =
    let (finalcbs, finalsubst) = typeinferModule' cbs (processadts adts) Map.empty in -- Infer and typecheck iteratively every expression, and in the end apply the final substitution (unified constraints) to all expressions
        CoreProgram adts $ apply finalsubst finalcbs
    where
        typeinferModule' :: [CoreBinding] -> [TypeBinding] -> Subst -> ([CoreBinding], Subst)
        typeinferModule' corebindings acc subst =
            case corebindings of
              [] -> ([], subst)
              b@(CoreBinding n ce):corebindings' -> do
                 let (btype, bexpr, subst') =
                         fromMaybe (errorWithoutStackTrace ("[Typeinfer Module] Failed checking: " ++ show b ++ " with context " ++ show acc)) $
                             typeinfer (map (\(TypeBinding n t) -> (n, t)) acc) ce
                 first (CoreBinding n bexpr :) $ typeinferModule' corebindings' (TypeBinding n (generalize ([], []) btype):acc) subst'


typecheckExpr :: CoreExpr -> Scheme
typecheckExpr e = generalize ([],[]) $ maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(t, _, _) -> t) (typeinfer [] e) -- TODO: porque é que o prof não queria que isto devolvêsse Scheme?


typecheckModule :: CoreProgram -> [TypeBinding]
typecheckModule (CoreProgram adts cbs) = typecheckModule' cbs $ processadts adts
    where
        typecheckModule' cbs acc = 
            if null cbs then []
            else let b@(CoreBinding n ce):xs = cbs in
                 let tb = TypeBinding n $ generalize ([],[]) $ maybe (errorWithoutStackTrace ("[Typecheck Module] Failed checking: " ++ show b ++ " with context " ++ show acc)) (\(t, _, _) -> t) $ typeinfer (map (\(TypeBinding n t) -> (n, t)) acc) ce in
                     tb:typecheckModule' xs (tb:acc)

