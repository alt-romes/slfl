{-# LANGUAGE LambdaCase #-}
module Synth where

import Data.List
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Data.Maybe
import Data.Bifunctor

import Debug.Trace

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool, Atom, TypeVar, Sum), Scheme (Forall))
import Syntax
import Util
import Constraints

type Gamma = [(String, Either Scheme Type)] -- Unrestricted hypothesis
type Delta = [(String, Type)] -- Linear hypothesis (not left asynchronous)
type Omega = [(String, Type)] -- Ordered (linear?) hypothesis
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value

type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

type SynthState = Int  -- variable number to be used, note: should we also use the state monad for the delta context???


letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

getName :: Int -> String
getName i = letters !! i

fresh :: LogicT (State SynthState) String
fresh = do 
    n <- lift get 
    lift $ put (n+1)
    return $ getName n

isAtomic :: Type -> Bool
isAtomic t = case t of
               Atom _ -> True
               _ -> False

---- subsitute var n with expn in expf
substitute :: String -> Expr -> Expr -> Expr
-- Propositions tend to appear only once due to linearity
substitute n expn = editexp (\case {Var _ -> True; _ -> False}) (\v@(Var x) -> if x == n then expn else v)

---- Synthetizer -----------------------------

synth :: Ctxt -> Type -> LogicT (State SynthState) (Expr, Delta)

---- Right asynchronous rules -----------------

---- forall a . T (async)  =>   instantiate T   (a' ...) -- TODO: Estou a assumir que se houverem type variables no tipo é como se já tivessem sido "instanciadas", e então começo a síntese sempre com um tipo simples, por isso este passo já não existe correto?

---- -oR
synth (г, d, o) (Fun a b) = do
    name <- fresh
    (exp, d') <- synth (г, d, (name, a):o) b
    guard (name `notElem` map fst d')
    return (Abs name (Just a) exp, d')

---- &R
synth c (With a b) = do
    (expa, d') <- synth c a
    (expb, d'') <- synth c b
    guard (d' == d'')
    return (WithValue expa expb, d')

-- no more synchronous right propositions, start inverting the ordered context (omega)


---- Left asynchronous rules ------------------

---- *L
synth (g, d, (n, Tensor a b):o) t = do
    n1 <- fresh
    n2 <- fresh
    (expt, d') <- synth (g, d, (n2, b):(n1, a):o) t
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (LetTensor n1 n2 (Var n) expt, d')

---- 1L
synth (g, d, (n, Unit):o) t = do
    (expt, d') <- synth (g, d, o) t
    return (LetUnit (Var n) expt, d')

---- +L
synth (g, d, (n, Plus a b):o) t = do
    n1 <- fresh
    n2 <- fresh
    (expa, d') <- synth (g, d, (n1, a):o) t
    (expb, d'')  <- synth (g, d, (n2, b):o) t
    guard (d' == d'')
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (CaseOfPlus (Var n) n1 expa n2 expb, d')

---- sumL
synth (g, d, (n, Sum tys):o) t = do
    ls <- mapM (\(name, ct) -> do
        varid <- fresh
        (exp, d') <- synth (g, d, (varid, ct):o) t
        return (name, varid, exp, d')
        ) tys
    let (n1, varid1, e1, d1') = head ls
    guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls)
    guard $ all ((`notElem` map fst d1') . (\(n,_,_,_) -> n)) ls
    return (CaseOfSum (Var n) (map (\(n,i,e,_) -> (n,i,e)) ls), d1')

---- !L
synth (g, d, (n, Bang a):o) t = do
    nname <- fresh
    (exp, d') <- synth ((nname, Right a):g, d, o) t
    guard (nname `notElem` map fst d')
    return (LetBang nname (Var n) exp, d')


----- Non-canonical right sync rules ---------

synth (g, d, (n, Bool):o) t = do
    (expa, d') <- synth (g, d, o) t
    (expb, d'') <- synth (g, d, o) t
    guard (d' == d'')
    return (IfThenElse (Var n) expa expb, d')

---- Synchronous left propositions to Delta ----

synth (g, d, p:o) t =
    synth (g, p:d, o) t

---- Synchronous rules -------------------------

-- no more asynchronous propositions, focus
synth (g, d, []) t = focus (g, d) t

focus :: FocusCtxt -> Type -> LogicT (State SynthState) (Expr, Delta)
-- because of laziness it'll only run until the first succeeds (bc of observe)
focus c goal =
    decideRight c goal <|> decideLeft c goal <|> decideLeftBang c goal

    where

        decideRight c goal =
            if isAtomic goal            -- to decide right, goal cannot be atomic
                then empty
                else focus' Nothing c goal

        decideLeft (g, din) goal = do
            case din of
              []     -> empty
              _ -> foldr ((<|>) . (\x -> focus' (Just x) (g, delete x din) goal)) empty din

        decideLeftBang (g, din) goal = do
            case g of
              []   -> empty
              _ -> foldr ((<|>) . (\x -> focus' (Just x) (g, din) goal)) empty g
        
        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> LogicT (State SynthState) (Expr, Delta)

        ---- Right synchronous rules ------------------

        ---- *R
        focus' Nothing c@(g, d) (Tensor a b) = do
            (expa, d') <- focus' Nothing c a
            (expb, d'') <- focus' Nothing (g, d') b
            return (TensorValue expa expb, d'')

        ---- 1R
        focus' Nothing c@(g, d) Unit = do
            return (UnitValue, d)
            
        ---- +R
        focus' Nothing c (Plus a b) = do
            (il, d') <- focus' Nothing c a
            return (InjL (Just b) il, d')
            <|> do
            (ir, d') <- focus' Nothing c b
            return (InjR (Just a) ir, d')

        ---- sumR
        focus' Nothing c (Sum sts) =
            foldr ((<|>) . (\(tag, goalt) ->
                do {
                   (e, d') <- focus' Nothing c goalt;
                   let smts = map (second Just) $ delete (tag, goalt) sts in
                   return (SumValue smts (tag, e), d')
                })) empty sts

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = do
            (expa, d') <- synth (g, d, []) a
            guard (d == d')
            return (BangValue expa, d')

        -- all right propositions focused on are synchronous; this pattern matching should be extensive

        ----- Non-canonical right sync rules ---------

        focus' Nothing (g, d) Bool = return (Tru, d) <|> return (Fls, d)


        ---- Left synchronous rules -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = do
            nname <- fresh
            (expb, d')  <- focus' (Just (nname, b)) c goal
            (expa, d'') <- synth (g, d', []) a
            return (substitute nname (App (Var n) expa) expb, d'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal = do
            nname <- fresh
            do
                (lf, d') <- focus' (Just (nname, a)) c goal
                return (substitute nname (Fst (Var n)) lf, d')
                -- note: whitespace is sensitive and I can't make it prettier ;) 
                <|> do
                (rt, d') <- focus' (Just (nname, b)) c goal
                return (substitute nname (Snd (Var n)) rt, d')

        ---- VL

        -- focusScheme (Just (n, Forall [] t)) c@(g,d) goal = 
        --     focus' (Just (n,t)) c@(g,d) goal 

        -- focusScheme (Just (n, Forall ids t)) c@(g,d) goal = 
            -- 1o "instanciar" ids em t com vars existenciais
            -- focar no t instanciado (saiem constraints tambem)
            -- tentar resolver constraints 
            -- Se all good ... :)
            -- Se nao ... :(

        ---- Proposition no longer synchronous --------

        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus
        focus' (Just nh@(n, h)) (g, d) goal =
            if isAtomic h
               then do
                   -- left focus is atomic
                   guard (h == goal) -- if is atomic and not the goal, fail
                   return (Var n, d)
               else
                   ---- left focus is not atomic and not left synchronous, unfocus
                   synth (g, d, [nh]) goal

        ---- right focus is not synchronous, unfocus. if it is atomic we fail
        focus' Nothing (g, d) goal = do
            (e, d') <- synth (g, d, []) goal
            return (e, d')


---- util

ftvctx :: FocusCtxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> FocusCtxt -> Set.Set Int
        ftvctx' acc (gc, dc) = Set.unions (map (ftvctx'' . snd) gc) `Set.union` Set.unions (map (ftv . snd) dc)
        ftvctx'' = \case {Right t -> ftv t; Left sch -> ftvsch sch}
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t

generalize :: FocusCtxt -> Type -> Scheme
generalize ctxt t = Forall ns t 
    where ns = Set.toList $ Set.difference (ftv t) (ftvctx ctxt)

---- top level

synthCtxAllType :: (Gamma, Delta) -> Type -> [Expr]
-- TODO : Print error se snd != [] ? Já não deve acontecer porque estamos a usar a LogicT
synthCtxAllType (g, d) t = let res = evalState (observeAllT $ synth (g, d, []) t) 0 in
                  if null res
                     then errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t
                     else map fst res

synthCtxType :: (Gamma, Delta) -> Type -> Expr
synthCtxType c t = head $ synthCtxAllType c t

synthAllType :: Type -> [Expr]
synthAllType = synthCtxAllType ([], [])

-- TODO: i'm assuming this type might contain type variables, and those will be used in the synth process as universal
synthType :: Type -> Expr
synthType t = head $ synthAllType t -- TODO: instanciate $ generalize t?

synthMarks :: Expr -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks = editexp
                (\case {Mark {} -> True; _ -> False})
                    (\(Mark _ c t) ->
                        synthCtxType (map (second Left) c, []) (fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t))

synthMarksModule :: [Binding] -> [Binding]
synthMarksModule = map (\(Binding n e) -> Binding n $ synthMarks e)
