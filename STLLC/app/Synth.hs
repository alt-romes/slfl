{-# LANGUAGE LambdaCase #-}
module Synth where

import Data.List
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Data.Maybe

import Debug.Trace

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool, Atom))
import Syntax
import Util

type Gamma = [(String, Type)] -- Unrestricted hypothesis
type Delta = [(String, Type)] -- Linear hypothesis (not left asynchronous)
type Omega = [(String, Type)] -- Ordered (linear?) hypothesis
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value

type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

type SynthState = Int  -- variable number to be used, note: should we also use the state monad for the delta context???


variableNames :: [String]
variableNames = ["x", "y", "z", "u", "v", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]

getName :: Int -> String
getName i = variableNames !! i

isAtomic :: Type -> Bool
isAtomic t = case t of
               Bool -> True
               Atom _ -> True
               _ -> False

---- subsitute var n with expn in expf
substitute :: String -> Expr -> Expr -> Expr
-- substitute'''''' n expn expf =
--     case expf of
--       (Var x) -> if x == n then expn else LetIn n expn expf
--       _ -> LetIn n expn expf
--
-- Propositions tend to appear only once due to linearity
substitute n expn = editexp (\case {Var _ -> True; _ -> False}) (\v@(Var x) -> if x == n then expn else v)

---- Synthetizer -----------------------------

synth :: Ctxt -> Type -> StateT SynthState Maybe (Expr, Delta)

---- Right asynchronous rules -----------------

---- -oR
synth (г, d, o) (Fun a b) = do
    vari <- get
    let name = getName vari
    put $ vari + 1
    (exp, d') <- synth (г, d, (name, a):o) b
    guard (name `notElem` map fst d')
    return (Abs name a exp, d')

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
    vari <- get
    let n1 = getName vari
    let n2 = getName (vari+1)
    put $ vari + 2
    (expt, d') <- synth (g, d, (n2, b):(n1, a):o) t
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (LetTensor n1 n2 (Var n) expt, d')

---- 1L
synth (g, d, (n, Unit):o) t = do
    (expt, d') <- synth (g, d, o) t
    return (LetUnit (Var n) expt, d')

---- +L
synth (g, d, (n, Plus a b):o) t = do
    vari <- get
    let n1 = getName vari
    let n2 = getName (vari+1)
    put $ vari + 2
    (expa, d') <- synth (g, d, (n1, a):o) t
    (expb, d'')  <- synth (g, d, (n2, b):o) t
    guard (d' == d'')
    guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    return (CaseOfPlus (Var n) n1 expa n2 expb, d')

---- !L
synth (g, d, (n, Bang a):o) t = do
    vari <- get
    let nname = getName vari
    put $ vari + 1
    (exp, d') <- synth ((nname, a):g, d, o) t
    guard (nname `notElem` map fst d')
    return (LetBang nname (Var n) exp, d')


----- Non-canonical right sync rules ---------

-- synth (g, d, (n, Bool):o) t = do
--     (expa, d') <- synth (g, d, (n1, a):o) t

---- Synchronous left propositions to Delta ----

synth (g, d, p:o) t = synth (g, p:d, o) t

-- eventually the ordered context will be empty, then start focusing


---- Synchronous rules -------------------------

-- no more asynchronous propositions, focus
synth (g, d, []) t = do
    vari <- get
    let (explist, vari') = runState (observeManyT 1 $ focus (g, d) t) vari
    put vari'
    if null explist
       then empty
       else return $ head explist -- TODO: Não é preciso garantir que o contexto aqui de entrada tmb é igual ao de saída?
                                  -- Ou alguma vez sai algo a mais do focus do que aquilo que lá metemos? Que exemplo? :)


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
              -- a:b:c:[]
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
            return (InjL b il, d')
            <|> do
            (ir, d') <- focus' Nothing c b
            return (InjR a ir, d')

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = do
            vari <- lift get
            let maybeSynthResult = runStateT (synth (g, d, []) a) vari -- if asynch continuation of synthesis failed, fail to backtrack
           -- TODO: Podemos ver alguns exemplos disto? vvvvv (context ter de ser vazio e quando não é etc)
            maybe empty (\((expa, d'), vari') -> do {lift $ put vari'; guard (d == d'); return (BangValue expa, d')}) maybeSynthResult

        -- all right propositions focused on are synchronous; this pattern matching should be extensive

        ----- Non-canonical right sync rules ---------

        focus' Nothing (g, d) Bool = do
            return (Tru, d) <|> return (Fls, d)
        

        ---- Left synchronous rules -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = do
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            (expb, d') <- focus' (Just (nname, b)) c goal
            vari' <- get
            let maybeSynthResult = runStateT (synth (g, d', []) a) vari'
            maybe empty (\((expa, d''), vari'') -> lift $ put vari'' >> return (substitute nname (App (Var n) expa) expb, d'')) maybeSynthResult
            
        ---- &L
        focus' (Just (n, With a b)) c goal = do
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            do
                (lf, d') <- focus' (Just (nname, a)) c goal
                return (substitute nname (Fst (Var n)) lf, d')
                <|> do
                (rt, d') <- focus' (Just (nname, b)) c goal
                return (substitute nname (Snd (Var n)) rt, d')


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
               else do
                   ---- left focus is not atomic and not left synchronous, unfocus
                   vari <- lift get
                   let maybeSynthResult = runStateT (synth (g, d, [nh]) goal) vari
                   maybe empty (\((exp, d'), vari') -> lift $ put vari' >> return (exp, d')) maybeSynthResult

        ---- right focus is not synchronous, unfocus. if it is atomic we fail
        focus' Nothing (g, d) goal = do
            vari <- lift get
            let maybeSynthResult = runStateT (synth (g, d, []) goal) vari
            maybe empty (\((e,d'), vari') -> lift $ put vari' >> return (e, d')) maybeSynthResult




---- top level

synthType :: Type -> Expr
-- TODO : Print error se snd != []
synthType t = fst $ fromMaybe (errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t) (evalStateT (synth ([], [], []) t) 0)

synthMarks :: Expr -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks = editexp (\case {Mark _ -> True; _ -> False}) (\(Mark t) -> synthType $ fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t)

synthMarksModule :: [Binding] -> [Binding]
synthMarksModule = map (\(Binding n e) -> Binding n $ synthMarks e)
