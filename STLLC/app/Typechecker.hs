module Typechecker (typeinferExpr, typeinferModule, typecheckExpr, typecheckModule, TypeBinding(..)) where

import Debug.Trace
import Data.List
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



type BoundCtxt = [Maybe Var] -- Left is unrestricted hypothesis, right is linear and might have been consumed
type FreeCtxt = [(String, Scheme)] -- TODO: i'm assuming all free ctx variables are unrestricted, since we can't really do free ctx linear vars
type Ctxt = (BoundCtxt, FreeCtxt)

-------------------------------------------------------------------------------
-- Infer "Monad"
-------------------------------------------------------------------------------

type Infer = WriterT [Constraint] (StateT Ctxt (StateT Int Maybe))


runinfer :: FreeCtxt -> Int -> CoreExpr -> Maybe ((((Type, CoreExpr), [Constraint]), Ctxt), Int)
runinfer fc i e = runStateT (runStateT (runWriterT $ typeconstraint e) ([], fc)) i





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

addtoblinctx :: Scheme -> Infer ()
addtoblinctx c = modify (first (Just (Var Lin c) :))


addtobunrctx :: Scheme -> Infer ()
addtobunrctx c = modify (first (Just (Var Unr c) :))


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


generalize :: Ctxt -> Type -> Scheme
generalize ctxt t = Forall as t 
    where as = Set.toList $ Set.difference (ftv t) (ftvctx ctxt)


-- TODO: Generalize for tuple of sets and place in util? kind of hard bc of the maybes or not maybes ;) maybe i should unify all contexts
ftvctx :: Ctxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> Ctxt -> Set.Set Int
        ftvctx' acc (bc, fc) = Set.unions (map (ftvsch . unVar) (catMaybes bc)) `Set.union` Set.unions (map (ftvsch . snd) fc)
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t





-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: CoreExpr -> Infer (Type, CoreExpr)

--- lit --------------------

typeconstraint ce@(Lit x) = return (getLitType x, ce)

--- hyp --------------------

typeconstraint ce@(BLVar x) = do
    ctx <- get
    let (pre, maybeschv:end) = splitAt x $ fst ctx
    schv <- lift $ lift $ lift maybeschv
    put (pre ++ Nothing:end, snd ctx)
    t <- instantiate $ unVar schv
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
    t <- instantiate $ unVar sch
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
    addtoblinctx $ trivialScheme t1'
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
    addtoblinctx $ trivialScheme tv1
    addtoblinctx $ trivialScheme tv2
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
    addtoblinctx $ trivialScheme tv1
    lastvi1 <- getlastvarindex
    (t3, ce2) <- typeconstraint e2
    wasBLVConsumed lastvi1 >>= guard -- make sure branch bound var doesn't escape
    ctx3 <- get
    put currentctx -- reset context to synth with the same context as the one used above
    addtoblinctx $ trivialScheme tv2
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
    addtobunrctx $ trivialScheme tv1 -- this var can, and will, escape because it'll be used unrestrictedly
    (t2, ce2) <- typeconstraint e2
    writer ((t2, LetBang ce1 ce2), [Constraint t1 (Bang tv1)])

--- LetIn ------------------

typeconstraint (LetIn e1 e2) = do
    c <- get
    (t1, ce1) <- typeconstraint e1
    c'@(bctx, fctx) <- get 
    guard $ equalDeltas c c' -- LetIn makes first variable unrestricted, so e1 should typecheck on an empty delta
    addtobunrctx $ generalize c' t1
    (t2, ce2) <- typeconstraint e2
    return (t2, LetIn ce1 ce2)

--- Synth marker -----------

typeconstraint (Mark i _ t) = do
    tv <- fresh
    c@(bc, fc) <- get
    let t' = fromMaybe tv t
    return (t', Mark i (bc, fc) (Just t'))

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
        addtoblinctx $ trivialScheme tv
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
                addtoblinctx $ trivialScheme argtype
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


typeinfer :: FreeCtxt -> Int -> CoreExpr -> Maybe (Type, CoreExpr, Subst, Int)
typeinfer fc i e = do
    ((((ctype, cexp), constraints), (bc, _)), i') <- runinfer fc i e
    -- guard (...) -- TODO: No linear variables in the exit context -- todo: annotate variables with linearity
    s <- solveconstraints Map.empty constraints
    let (ctype', cexp') = apply s (ctype, cexp)
    -- TODO: generate new constraint with the inferred type, and apply a new substitution over the core expression to resolve the marks "recursive" context
    return (ctype', cexp', s, i')
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


instantiateFrom :: Int -> Scheme -> Type
instantiateFrom i (Forall ns t) = do
    let fs = take (length ns) $ map TypeVar [i..]
    let s = Map.fromList $ zip ns fs 
    apply s t





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

typeinferExpr :: CoreExpr -> CoreExpr
typeinferExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(_, ce, _, _) -> ce) (typeinfer [] 0 e)


-- TODO: Refactor this function
-- !TODO: Rever como estou a fazer as type annotations com o prof
typeinferModule :: Program -> Program -- typecheck and use inferred types
typeinferModule (Program adts bs ts cbs) =
    let (finalcbs, finalts, finalsubst) = typeinferModule' cbs (processadts adts ++ ts) 0 Map.empty in -- Infer and typecheck iteratively every expression, and in the end apply the final substitution (unified constraints) to all expressions
        let finalcbs' = apply finalsubst finalcbs in
            Program adts bs finalts finalcbs'
    where
        typeinferModule' :: [CoreBinding] -> [TypeBinding] -> Int -> Subst -> ([CoreBinding], [TypeBinding], Subst)
        typeinferModule' corebindings knownts i subst = -- Corebindings to process, knownts = known type bindings, i = next var nº to use in inference, subst = substitution to compose with when solving next constraints
            case corebindings of
              [] -> ([], knownts, subst)
              b@(CoreBinding n ce):corebindings' ->
                  let tbs_pairs = map (\(TypeBinding n t) -> (n, t)) knownts in
                  case lookup n tbs_pairs of                                    -- Check if we already have a type definition for this function name
                    Nothing ->                                                  -- We don't have a type for this name yet, add it as a general function so recursion can be type checked
                        case typeinfer ((n, Forall [] (TypeVar i)):tbs_pairs) (i+1) ce of -- TODO: Queremos assim com a' ou queremos Fun a' b' ? É que se for o segundo depois não podiamos ter coisas como variáveis
                          Nothing -> errorWithoutStackTrace ("[Typeinfer Module] Failed checking: " ++ show b ++ " with context " ++ show tbs_pairs) -- Failed to solve constraints
                          Just (btype, bexpr, subst', i') ->
                              case solveconstraints subst' [Constraint (TypeVar i) btype] of -- Solve type annotation with actual type
                                Nothing -> errorWithoutStackTrace ("[Typeinfer Module] Failed to solve annotation with actual type when typing: " ++ show b ++ " with context " ++ show tbs_pairs) -- Failed to solve constraints
                                Just subst'' ->
                                  let (btype', bexpr') = apply subst'' (btype, bexpr) in -- Use new substitution that solves annotation with actual type
                                  (\(c', tb', s') -> (CoreBinding n bexpr' :c', tb', s')) $
                                      typeinferModule' corebindings' (TypeBinding n (generalize ([], []) $ cleanLetters btype'):knownts) i' subst''
                    Just (Forall schnames schty) ->                             -- Function name is already typed, and already in the context, so no need to add again
                        case typeinfer tbs_pairs i ce of
                          Nothing -> errorWithoutStackTrace ("[Typeinfer Module] Failed checking: " ++ show b ++ " with context " ++ show tbs_pairs) -- Failed to solve constraints
                          Just (btype, bexpr, subst', i') -> 
                              (\(c', tb', s') -> (CoreBinding n bexpr :c', tb', s')) $ -- Add this corebinding to the result
                                  typeinferModule' corebindings' (TypeBinding n (generalize ([], []) $ cleanLetters btype):knownts) i' subst' -- Recursive call and add new typebinding to known type bindings


        cleanLetters :: Type -> Type
        cleanLetters t = instantiateFrom 0 $ generalize ([], []) t


typecheckExpr :: CoreExpr -> Scheme
typecheckExpr e = generalize ([],[]) $ maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(t, _, _, _) -> t) (typeinfer [] 0 e) -- TODO: porque é que o prof não queria que isto devolvesse Scheme?


-- pre : Program must have been previously type inferred
typecheckModule :: Program -> [TypeBinding]
typecheckModule = reverse . _tbinds
    -- if and $ zipWith (\ (CoreBinding n1 _) (TypeBinding n2 _) -> n1 == n2) (_cbinds p) (_tbinds p)
    --    then -- all core bindings already have type bindings
    --         reverse $ _tbinds p
    --    else -- not all core bindings have type bindings yet
    --         reverse $ _tbinds $ typeinferModule p

