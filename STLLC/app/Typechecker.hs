{-# LANGUAGE LambdaCase #-}
module Typechecker (typeinferExpr, typeinferModule, typecheckExpr, TypeBinding(..), instantiateFrom) where

import Debug.Trace
import Data.List
import Data.Bifunctor (first, second)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer (WriterT, writer, runWriterT) 
import Refinements


import CoreSyntax
import Program
import Constraints
import Util



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
addtoblinctx c = do
    (bc, _) <- get
    modify (first (Just (Var Lin c) :))


addtobunrctx :: Scheme -> Infer ()
addtobunrctx c = modify (first (Just (Var Unr c) :))


wasBLVConsumed :: Int -> Infer Bool
wasBLVConsumed i = do
    (bc, _) <- get
    case bc !! (length bc - 1 - i) of -- Appends are done to the head of the list, so check the index counting from the end
      Nothing -> return True
      Just x -> error $ "BLV " ++ show x ++ " wasn't consumed!"


getlastvarindex :: Infer Int
getlastvarindex = gets (\(bc, _) -> length bc - 1)


equalDeltas :: Ctxt -> Ctxt -> Bool
equalDeltas (ba, _) (bb, _) = filterD ba == filterD bb || trace ("[Typecheck] Failed resource management comparing " ++ show (filterD ba) ++ " with " ++ show (filterD bb)) False
    where
        filterD = filter (\v -> varMult v == Lin) . catMaybes


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

-- !TODO: Typecheck predicates

-- Generate a list of constraints, a type that may have type varibales, and a modified expression with type variables instead of nothing for untyped types
typeconstraint :: CoreExpr -> Infer (Type, CoreExpr)

--- lit --------------------

typeconstraint ce@(Lit (LitInt x)) = do
    i <- lift $ lift get
    lift $ lift $ put (i+1)
    let name = getName i
    return (RefinementType name (TyLit TyInt) [] (Just $ BinaryOp "==" (PVar name) (PNum x)), ce)

--- hyp --------------------

typeconstraint ce@(BLVar x) = do
    (bc, fc) <- get
    let (pre, maybeschv:end) = splitAt x bc
    schv <- lift $ lift $ lift maybeschv
    put (pre ++ Nothing:end, fc)
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
    lastvari1 <- getlastvarindex
    addtoblinctx $ trivialScheme tv2
    lastvari2 <- getlastvarindex
    (t3, ce2) <- typeconstraint e2
    wasBLVConsumed lastvari1 >>= guard -- make sure linear variables were used and don't exit the binder
    (bc, _) <- get
    wasBLVConsumed lastvari2 >>= guard
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

typeconstraint (Mark i n _ t ed) = do
    tv <- fresh
    c@(bc, fc) <- get
    let t' = fromMaybe (trivialScheme tv) t
    case t' of
      Forall [] t'' -> do
        vari <- lift $ lift get
        lift $ lift $ put (vari + length (ftv t''))
        return (t'', Mark i n (bc, fc) (Just $ Forall (Set.toList $ ftv t'') t'') ed)
      _ -> error "Type inference shouldn't have marks with bound polimorfic variables"

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
            Just (Forall ns (Fun argtype (ADT _ _))) -> do -- Constructor takes an argument
                addtoblinctx $ Forall ns argtype
                lastvi <- getlastvarindex
                (t', ce) <- typeconstraint ex
                wasBLVConsumed lastvi >>= guard -- Variable bound in branch must be linearly
                ctx' <- get
                return $ Just (t', s, ce, ctx')
            Just (Forall ns (ADT _ _)) -> do -- Constructor does not take an argument
                addtobunrctx $ Forall [] Unit
                (t', ce) <- typeconstraint ex
                ctx' <- get
                return $ Just (t', s, ce, ctx')
            _ -> return Nothing
        ) exps
    -- TODO: Probably doable in a more idiomatic way
    let inferredexps' = catMaybes inferredexps
    let (t1', s1, ce1, ctx1') = head inferredexps'
    guard $ all (equalDeltas ctx1' . (\(_,_,_,c) -> c)) (tail inferredexps')
    (adtname, adttypes) <- getadt fctx s1
    guard $ all ((== adtname) . (\(_,constr,_,_) -> getadtname fctx constr)) (tail inferredexps')
    writer ((t1', CaseOf ce (map (\(_,s,c,_) -> (s,c)) inferredexps')), Constraint st (ADT adtname adttypes):map (\(t'',_,_,_) -> Constraint t1' t'') (tail inferredexps'))
        where
            getadt fctx s = case lookup s fctx of
                        Just (Forall ns (Fun _ (ADT adtname adttypes))) -> do
                            adttypes' <- mapM (instantiate . Forall ns) adttypes
                            return (adtname, adttypes') -- Constructor takes an argument
                        Just (Forall ns (ADT adtname adttypes)) -> do
                            adttypes' <- mapM (instantiate . Forall ns) adttypes
                            return (adtname, adttypes') -- Constructor does not take an argument

            getadtname fctx s = case lookup s fctx of
                        Just (Forall _ (Fun _ (ADT adtname _))) -> adtname -- Constructor takes an argument
                        Just (Forall _ (ADT adtname _)) -> adtname -- Constructor does not take an argument



typeinfer :: FreeCtxt -> CoreExpr -> Maybe (Type, CoreExpr, Subst, Int)
typeinfer fc e = do
    ((((ctype, cexp), constraints), (bc, _)), i') <- runinfer fc 0 e
    -- guard (...) -- TODO: No linear variables in the exit context -- todo: annotate variables with linearity?
    case solveconstraints Map.empty constraints of
      Nothing -> error ("[TypeInfer] Failed solving constraints " ++ show constraints)
      Just s -> do
        let (ctype', cexp') = apply s (ctype, cexp)
        let refinementctxt = makeRefinementCtxt s constraints -- Look at substitutions from function of refined types to function of refined types, e.g. [x {Int} -o y {Int | y == x + 1} => a {Int | a == 1} -o y { Int | y == x + 1 }] and replace a with name x to context of y
        let ctype'' = updateRefinements refinementctxt ctype'
        return (ctype'', cexp', s, i')

    where
        updateRefinements :: Map.Map Name [Type] -> Type -> Type
        updateRefinements c r@(RefinementType n t ls p) =
            case Map.lookup n c of
              Nothing -> r
              Just rs -> RefinementType n t (ls ++ rs) p
        updateRefinements c (Fun t1 t2) = Fun (updateRefinements c t1) (updateRefinements c t2)
        updateRefinements c t = t

        makeRefinementCtxt :: Map.Map Int Type -> [Constraint] -> Map.Map Name [Type]
        makeRefinementCtxt m cns = makeRefinementCtxt' $ filter (\ (a,_) -> case a of                            -- e.g. [x {Int} -o y {Int | y == x + 1} => a {Int | a == 1} -o y { Int | y == x + 1 }] and replace a with name x to context of y
                                                             Fun _ (Fun _ _) -> True                -- choose only types in which the value's refinement might have been altered by the argument
                                                             Fun _ RefinementType {} -> True
                                                             _ -> False
                                                 ) $ map (\(Constraint t1 t2) -> (t1, t2)) $ apply m cns
                                                 
        makeRefinementCtxt' :: [(Type, Type)] -> Map.Map Name [Type]
        makeRefinementCtxt' l@((Fun (RefinementType n1 _ _ _) RefinementType {}, Fun a@(RefinementType n2 t ls p) (RefinementType n3 _ _ _)):xs) =
            Map.insertWith (++) n3 [RefinementType n1 t ls (replaceName (Map.singleton n2 n1) <$> p)] $ makeRefinementCtxt' xs
        makeRefinementCtxt' ((Fun (RefinementType n1 _ _ _) _, Fun (RefinementType n2 t ls p) innert):xs) = foldr (\name rs -> Map.insertWith (++) name [RefinementType n1 t ls (replaceName (Map.singleton n2 n1) <$> p)] rs) (makeRefinementCtxt' xs) (getRefinementNames innert)
        makeRefinementCtxt' (_:xs) = makeRefinementCtxt' xs
        makeRefinementCtxt' [] = Map.empty

        getRefinementNames :: Type -> [Name]
        getRefinementNames (Fun t1 t2) = getRefinementNames t1 ++ getRefinementNames t2
        getRefinementNames (RefinementType n _ _ _) = [n]
        getRefinementNames _ = []





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

processadts :: [ADTD] -> [TypeBinding]
processadts = concatMap processadt
    where
        processadt :: ADTD -> [TypeBinding]
        processadt (ADTD tn tps cns) = map processcns cns
            where
                processcns (cn, Unit) = TypeBinding cn (Forall tps (ADT tn $ map TypeVar tps))
                processcns (cn, ty) = TypeBinding cn (Forall tps (Fun ty (ADT tn $ map TypeVar tps)))


instantiateFrom :: Int -> Scheme -> Type
instantiateFrom i (Forall ns t) = do
    let fs = take (length ns) $ map TypeVar [i..]
    let s = Map.fromList $ zip ns fs 
    apply s t


generalizetbs :: [TypeBinding] -> [TypeBinding]
generalizetbs [] = []
generalizetbs ((TypeBinding n (Forall [] ty)):xs) = TypeBinding n (generalize ([],[]) ty):generalizetbs xs  -- TypeBindings from the parser come generalized with trivial schemes
                                                                                                            -- TODO: Should probably be done in the parser instead of this
generalizetbs (tb@(TypeBinding n sch):xs) = tb:generalizetbs xs


deletetb :: Name -> [TypeBinding] -> [TypeBinding]
deletetb _ [] = []
deletetb n (t@(TypeBinding z ty):ls)
  | n == z = deletetb n ls
  | otherwise = t:deletetb n ls





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

typeinferExpr :: CoreExpr -> CoreExpr
typeinferExpr e = maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(_, ce, _, _) -> ce) (typeinfer [] e)


typeinferModule :: Program -> IO Program -- typecheck and use inferred types
typeinferModule (Program adts bs ts cbs) = do

    (finalcbs, finalts) <- typeinferModule' cbs (processadts adts ++ generalizetbs ts)  -- Infer and typecheck iteratively every expression, and in the end apply the final substitution (unified constraints) to all expressions
    return $ completeFrontendMarksCtx $ Program adts bs finalts finalcbs

    where
        typeinferModule' :: [CoreBinding] -> [TypeBinding] -> IO ([CoreBinding], [TypeBinding])
        typeinferModule' corebindings knownts = -- Corebindings to process, knownts = known type bindings, i = next var nº to use in inference, subst = substitution to compose with when solving next constraints
            case corebindings of
              [] -> return ([], knownts)
              (CoreBinding n ce):corebindings' ->
                  let tbs_pairs = map (\(TypeBinding n t) -> (n, t)) knownts in
                  case lookup n tbs_pairs of                                    -- Check if we already have a type definition (annotation) for this function name
                    Nothing ->                                                  -- We don't have a type for this name yet, add it as a general function so recursion can be type checked
                        let selftype = Forall [0] (TypeVar 0) in 
                        inferWithRecName corebindings' knownts n ((n, selftype):tbs_pairs) ce selftype
                    Just sch ->                                                 -- Function name is already typed, and already in the context, so no need to add it again
                        inferWithRecName corebindings' (deletetb n knownts) n tbs_pairs ce sch -- delete from knownts (accumulator for typebindings) the type because it will be inferred, solved with the annotation, and re-added after


        inferWithRecName :: [CoreBinding]
                         -> [TypeBinding]
                         -> Name
                         -> FreeCtxt
                         -> CoreExpr
                         -> Scheme
                         -> IO ([CoreBinding], [TypeBinding])
        inferWithRecName corebindings' knownts n tbs_pairs ce selftype@(Forall stvs selftypet) = 
            case typeinfer tbs_pairs ce of -- Use type annotation in inference, and solve it after by adding a constraint manually
              Nothing -> error ("[Typeinfer Module] Failed checking: " ++ show ce ++ " with context " ++ show tbs_pairs) -- Failed to solve constraints
              Just (btype, bexpr, subst', i') ->
                  case solveconstraints subst' [Constraint btype $ instantiateFrom i' selftype] of  -- Solve type annotation with actual type
                    Nothing -> error ("[Typeinfer Module] Failed to solve annotation \"" ++ show (instantiateFrom i' selftype) ++ "\" with actual type \"" ++ show btype ++ "\" when typing: " ++ show ce ++ " with context " ++ show tbs_pairs) -- Failed to solve constraints
                    Just subst'' -> do
                      let (btype', bexpr') = apply subst'' (btype, bexpr)        -- Use new substitution that solves annotation with actual type
                      let bsch = if selftypet == TypeVar 0 then generalize ([], []) $ cleanLetters btype' else selftype     -- Use the type annotation if one was given, else use the inferred type
                      let bexpr'' = substSelfTypeMarks n bsch bexpr'
                      satunify <- satunifyrefinements (cleanLetters btype') (instantiateFrom 0 selftype)
                      if True || satunify     -- Satisfy the refinements of the inferred type with the annotation together
                        then
                          first (CoreBinding n bexpr'':) <$>
                            typeinferModule' corebindings' (TypeBinding n bsch:knownts) -- Re-add self-type to type bindings
                        else error $ "[Infer] Failed to satisfy refinements of type with possible annotation " ++ show bsch ++ " with verification condition " ++ show (getvc (renameR $ cleanLetters btype') `composeVC` getvc (renameR $ instantiateFrom 0 selftype))


        cleanLetters :: Type -> Type
        cleanLetters t = instantiateFrom 0 $ generalize ([], []) t

        substSelfTypeMarks :: Name -> Scheme -> CoreExpr -> CoreExpr
        substSelfTypeMarks n btype bexpr' =
            transform (\case
                (Mark i mn (bc, fc) t ed) ->
                    let fc' = (n, btype):deleteBy (\ (s, _) (s', _) -> s == s') (n, undefined) fc in -- Remove possibly incorrect self type from mark context and re-add one correctly
                        Mark i mn (bc, fc') t ed;
                 x -> x) bexpr'



typecheckExpr :: CoreExpr -> Scheme
typecheckExpr e = generalize ([],[]) $ maybe (errorWithoutStackTrace "[Typecheck] Failed") (\(t, _, _, _) -> t) (typeinfer [] e) -- TODO: porque é que o prof não queria que isto devolvesse Scheme?

