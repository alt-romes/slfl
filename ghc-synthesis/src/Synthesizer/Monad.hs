{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Synthesizer.Monad
    ( module Language.Haskell.Syntax.Expr
    , module Language.Haskell.Syntax.Pat
    , module GHC
    , runState, runReaderT, observeT, observeManyT, asks, get, put
    , SDoc, ppr
    , module Synthesizer.Monad
    ) where

import Debug.Trace
import Data.Tree
import Data.List
import Data.Either
import Data.Bifunctor
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.RWS.Lazy hiding (ask, asks, local, get, put, modify, writer, tell, listen)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer.Class
import Control.Monad.RWS.Class
import Data.Foldable (toList)

import Language.Haskell.Syntax.Pat
import Language.Haskell.Syntax.Expr
import Language.Haskell.Syntax.Extension
import GHC.Core.Predicate
import GHC.Utils.Outputable hiding ((<>), empty, Depth(..))
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Tc.Types.Constraint
import GHC.Types.Basic
import GHC.Tc.Utils.TcMType (newCoercionHole, newEvVar)
import GHC.Tc.Solver
import GHC.Parser.Annotation
import GHC.Core.Multiplicity
import GHC.Types.Var
import GHC.Core.TyCo.Rep
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
import GHC.Types.Name
import GHC.Types.Basic
import GHC.Data.FastString
import GHC.Core.Map.Type
import GHC.Core.TyCon
import GHC.Hs.Pat
import GHC.Tc.Types
import GHC.Core.Coercion
import GHC.Tc.Solver.Interact
import GHC.Tc.Solver.Monad (runTcS)
import GHC.Tc.Utils.Monad
import GHC.Tc.Types.Origin
import GHC.Types.Id
import GHC.Data.Bag
import GHC

import GHC.SourceGen hiding (guard)

import Control.Monad.Logic

import Synthesizer.AST

-----------------------------------------
-- * Synth
-----------------------------------------

-- | Synthesis monad
--
-- Handles threading of state, propagation of reading state, backtracking,
-- constraint solving, and friends
newtype Synth a = Synth { unSynth :: LogicT (RWST (Depth, [RestrictTag], Gamma, Omega) () (Past, Int, Delta, [Ct]) TcM) a }
    deriving ( Functor
             , MonadFail
             , MonadLogic
             , MonadIO)

instance Applicative Synth where
    pure = Synth . pure
    (Synth f) <*> (Synth v) = Synth (f <*> v)

instance Alternative Synth where
    (<|>) (Synth a) (Synth b) = Synth (a <|> b)
    empty = do
        (d, _, _, _) <- ask
        liftIO $ putStrLn (take (d*2) (repeat ' ') <> "[X] Fail")
        Synth empty

instance Monad Synth where
    (Synth a) >>= f = Synth $ do
        (p, i, d, ct) <- get
        (_, rs, g, o) <- ask
        when (p /= Past d rs g o) $ do
            -- liftIO $ print d >> print (rs, g, o)
            put (Past d rs g o, i, d, ct)
        a >>= unSynth . f

instance MonadReader (Depth, [RestrictTag], Gamma, Omega) Synth where
    ask = Synth (lift ask)
    local f (Synth (LogicT m)) = Synth $ LogicT $ \sk fk -> do
        env <- ask
        local f $ m ((local (const env) .) . sk) (local (const env) fk)

instance MonadState (Past, Int, Delta, [Ct]) Synth where
    get = Synth $ lift get
    put = Synth . lift . put

-- | Run a synthesis computation.
--
-- Receives the amount of results to observe,
-- the type of the recursive call (small hack while I don't have the module info),
-- and the synthesis computation
runSynth :: Int -> Type -> Synth a -> TcM [a]
runSynth i t sy = do
    (exps, _) <- evalRWST (observeManyT i $ unSynth sy) (0, mempty, Gamma [("rec", trace (show $ ppr t) t)], Omega mempty) (NoPast, 0, Delta mempty, mempty)
    return exps


-----------------------------------------
-- * Rules
-----------------------------------------

-- | A Rule is a string e.g. "-oR", but could also be a custom datatype
type Rule = String

-- | Run computation where the current rule is being applied to the given type
--
-- This is used to track the depth of the proof, and for logging
rule :: Rule -> Type -> Synth a -> Synth a
rule s t act = do
    (d, _, _, _) <- ask
    liftIO $ putStrLn (take (d*2) (repeat ' ') <> "[" <> s <> "] " <> show t)
    local (\(d,a,b,c) -> (d+1,a,b,c)) act

-- | From two types (a,b) create a new type (a => b) for usage with 'rule'
-- 
-- Used for representing e.g. left focus => synth goal
(=>>) :: Type -> Type -> Type
(=>>) a b = FunTy InvisArg Many a b


-----------------------------------------
-- * Gamma
-----------------------------------------

-- | Unrestricted hypothesis (Γ)
newtype Gamma = Gamma { gamma :: [Prop] }

-- | Run a computation with additional proposition in gamma
inGamma :: Prop -> Synth a -> Synth a
inGamma nt = local (first (Gamma . (nt:) . gamma))

-- | Get the unrestricted context
getGamma :: Synth [Prop]
getGamma = do
    (_, _, g, _) <- ask
    return $ gamma g


-----------------------------------------
-- * Delta
-----------------------------------------

-- | Linear hypothesis (not left asynchronous) (Δ)
newtype Delta = Delta { delta :: [Prop] }

-- | Add a proposition to the linear context
pushDelta :: Prop -> Synth ()
pushDelta p = modify (first (Delta . (p:) . delta))

-- | Remove a proposition from the linear context
delDelta :: Prop -> Synth ()
delDelta p = modify (first (Delta . delete p . delta))

-- | Get the linear context
getDelta :: Synth [Prop]
getDelta = do
    (_, _, d, _) <- get
    return $ delta d

-- | Set the linear context
setDelta :: [Prop] -> Synth ()
setDelta = modify . first . const . Delta

-- | This computation succeeds when 
guardUsed :: SName -> Synth ()
guardUsed name = do
    d <- getDelta
    guardWith "Not used" (name `notElem` map fst d)


-----------------------------------------
-- * Omega
-----------------------------------------

-- | Ordered (linear?) hypothesis (Ω)
newtype Omega = Omega { omega :: [Prop] }

-- | Take a proposition from the omega context:
--   * If one exists, pass it to the 2nd argument (computation using proposition)
--   * If none does, run the 1st argument (computation without proposition from omega)
--
--   In case a proposition is taken from omega, the computation run won't have it in the omega context anymore
takeOmegaOr :: Synth a -> (Prop -> Synth a) -> Synth a
takeOmegaOr c f = asks (\case (_,_,_,Omega o) -> o) >>= \case
    (h:o) -> local (second (const (Omega o))) (f h)
    [] -> c

-- | Run a computation with an additional proposition in omega
inOmega :: Prop -> Synth a -> Synth a
inOmega nt = local (second (Omega . (<> [nt]) . omega))

-- | Extend a computation with additional propositions in omega
extendOmega :: [Prop] -> Synth a -> Synth a
extendOmega o' = local (second (Omega . (<> o') . omega))


-----------------------------------------
-- * Restrictions
-----------------------------------------

-- | Restrictions to conduct synthesis
data RestrictTag
    = ConstructTy Type          -- ^ Restriction on Constructing Type
    | DeconstructTy Type        -- ^ Restriction on Deonstructing Type
    | DecideLeftBangR Type Type -- ^ Restriction on "Deciding-Left-Bang" on X to synthesize Y
    deriving Eq

-- | Run a computation with an additional restriction
addRestriction :: RestrictTag -> Synth a -> Synth a
addRestriction tag = local (\(d,r,g,o) -> (d, tag:r, g, o))

-- | Guard that a certain restriction exists
--
-- i.e. if the given restriction is already in place, the computation suceeds,
-- otherwise, the given restriction isn't in place, and the computation fails
-- with `empty`
guardRestricted :: RestrictTag -> Synth ()
guardRestricted tag = do
    (_, rs, _, _) <- ask
    guardWith "Expected restricted" (tag `elem` rs)
-- guardRestricted (DecideLeftBangR _ _) = undefined

-- | Guard that a certain restriction hasn't been applied
--
-- i.e. if the given restriction doesn't exist, the computation suceeds,
-- otherwise, the given restriction is already in place, and the computation fails
-- with `empty`
guardNotRestricted :: RestrictTag -> Synth ()
guardNotRestricted tag = do
    (_, rs, _, _) <- ask
    guardWith "Restricted" (tag `notElem` rs)
-- guardRestricted tag@(DecideLeftBangR _ _) = do -- TODO
--     (rs, _, _) <- ask
--     existentialdepth <- getExistentialDepth
--     return $ tag `notElem` rs &&
--         -- isExistential => Poly-Exist pairs are less than the existential depth
--         (not (isExistentialType $ snd typair) || existentialdepth > count True (map (\x -> isExistentialType (snd x) && isLeft (fst x)) reslist)) -- no repeated use of unr functions or use of unr func when one was used focused on an existential


-----------------------------------------
-- * Constraints (WIP)
-----------------------------------------

getConstraints :: Synth [Ct]
getConstraints = do
    (_, _, _, cts) <- get
    return cts

setConstraints :: [Ct] -> Synth ()
setConstraints = modify . second . const

newWantedWithLoc :: CtLoc -> PredType -> TcM CtEvidence
newWantedWithLoc loc pty
  = do dst <- case classifyPredType pty of
                EqPred {} -> HoleDest  <$> newCoercionHole pty
                _         -> EvVarDest <$> newEvVar pty
       return $ CtWanted { ctev_dest      = dst
                         , ctev_pred      = pty
                         , ctev_loc       = loc
                         , ctev_nosh      = WOnly }

-- | Add a constraint to the list of constraints and solve it
-- Failing if the constraints can't be solved with this addition
solveConstraintsWithEq :: Type -> Type -> Synth ()
solveConstraintsWithEq t1 t2 = do
    cts <- getConstraints
    -- Solve the existing constraints with the added equality, failing when unsolvable
    (ct, solved) <- liftTcM $ do
        let predTy = mkPrimEqPred t1 t2
        liftIO $ putStrLn ("Predicate: " <> show predTy)
        -- name <- newName (mkEqPredCoOcc (mkVarOcc "magic"))
        -- let var = mkVanillaGlobal name predTy
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
        -- let ct = mkNonCanonical $ CtGiven predTy var loc
        ct <- mkNonCanonical <$> newWantedWithLoc loc predTy
        evBinds <- evBindMapBinds . snd <$> runTcS (solveSimpleWanteds (listToBag $ ct:cts))
        liftIO $ putStrLn ("Result: " <> show (ppr evBinds))
        return (ct, not (null $ toList evBinds) && (t1 /= t2)) -- when t1 == t2, evBinds = [] ?
    guardWith "Unification failure (ALWAYS FALSE)" False -- TODO: The above doesn't work, always fail for now
    guard solved
    setConstraints (ct:cts)


-----------------------------------------
-- * Names
-----------------------------------------

-- | Generate a fresh name
--
-- Example:
--      a <- fresh
--      return (var a)
fresh :: Synth SName
fresh = do
    (p, n, d, cts) <- get
    put (p, n + 1, d, cts)
    return . occNameToStr . mkVarOcc . getName $ n

    where letters :: [String]
          letters = [1..] >>= flip replicateM ['a'..'z']

          getName :: Int -> String
          getName i = if i < 0 then '-' : letters !! (-i) else letters !! i


-----------------------------------------
-- * Utilities
-----------------------------------------

-- | Like 'guard' but emit given string as failure message upon failure
guardWith :: String -> Bool -> Synth ()
guardWith s b = do
    unless b $ do
        (d, _, _, _) <- ask
        liftIO $ putStrLn (take (d*2) (repeat ' ') <> "[X] " <> s)
        empty

-- | 'forM' but instead of '(>>=)' use '(>>-)' for fair conjunction
--
-- See '(>>-)' in 'LogicT'
forMFairConj :: MonadLogic m => [t] -> (t -> m a) -> m [a]
forMFairConj [] _ = return [] 
forMFairConj (x:xs) f =
  f x >>- \x' -> do
      xs' <- forMFairConj xs f
      return $ x':xs'

-- | Lift a 'TcM' computation into a 'Synth' one
liftTcM :: TcM a -> Synth a
liftTcM = Synth . lift . lift

-- | Get 4th value of tuple of size 4
t4 :: (a,b,c,d) -> d
t4 (_,_,_,d) = d


-----------------------------------------
-- * Pretty Printing
-----------------------------------------

instance {-# OVERLAPPING #-} Show Prop where
    show (n, t) = occNameStrToString n <> ": " <> show t

instance Show Gamma where
    show (Gamma l) = "Gamma: " <> show l

instance Show Delta where
    show (Delta l) = "Delta: " <> show l <> "\n"

instance Show Omega where
    show (Omega l) = "Omega: " <> show l

instance Show RestrictTag where
    show (ConstructTy l) = "PC: " <> show l
    show (DeconstructTy l) = "PD: " <> show l
    show (DecideLeftBangR l r) = "PL!: " <> show l <> " :=> " <> show r

instance {-# OVERLAPPING #-} Show ([RestrictTag], Gamma, Omega) where
    show (a,b,c) = "Restrictions: " <> show a <> "\n\n" <> show b <> "\n\n" <> show c <> "\n\n"

instance Show Type where
    -- hack for showing types
    show = show . ppr

instance Eq Type where
    -- hack for comparing types using debruijn....
    a == b = deBruijnize a == deBruijnize b


-----------------------------------------
-- * Other Types
-----------------------------------------

type Depth = Int
type SName = OccNameStr
type Prop = (SName, Type)

deriving instance Eq Gamma
deriving instance Eq Delta
deriving instance Eq Omega

data Past = Past Delta [RestrictTag] Gamma Omega
          | NoPast
          deriving (Eq)

