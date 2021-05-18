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
-- substitute n expn expf =
--     case expf of
--       (Var x) -> if x == n then expn else LetIn n expn expf -- TODO: Aqui devia tmb dizer Let n expn expf ou se não utilizamos a variável podemos discartá-la? Parece me difícil esta situação sequer acontecer, porque se os recursos são lineares... ?
--       _ -> LetIn n expn expf
-- TODO: Queremos mesmo substituir a expressão em todo o lado?
-- Estava a pensar que fazia mais sentido apenas substituir expressões que sejam
-- diretamente "(Var n)", porque se não vamos estar a tornar a expressão mais complicada
-- ao substituir Var n possivelmente várias vezes em toda a expressão
--
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
    return (Abs name a exp, d')

---- &R
synth c (With a b) = do
    (expa, d') <- synth c a
    (expb, d'') <- synth c b
    guard (d' == d'') -- TODO: ?? DeltaOut from synth a and DeltaOut from synth b should be the same ??
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
    (expb, _)  <- synth (g, d, (n2, b):o) t    -- ?? como é que garanto que ambos estes synth vão usar os mesmos recursos?
                                                -- ? tenho de ter LogicT até nas invertíveis e andar para trás quando estas coisas correm mal? parece-me estranho,,
    return (CaseOfPlus (Var n) n1 expa n2 expb, d')

---- !L
synth (g, d, (n, Bang a):o) t = do
    vari <- get
    let nname = getName vari
    put $ vari + 1
    (exp, d') <- synth ((nname, a):g, d, o) t
    return (LetBang nname (Var n) exp, d')


---- Synchronous left propositions to Delta ----

-- synth (g, d, (n, Fun a b):o) t = synth (g, (n, Fun a b):d, o) t
-- synth (g, d, (n, With a b):o) t = synth (g, (n, With a b):d, o) t
synth (g, d, p:o) t = synth (g, p:d, o) t -- generalization of above

-- eventually the ordered context will be empty, then start focusing


---- Synchronous rules -------------------------

-- no more asynchronous propositions, focus
synth (g, d, []) t = do
    vari <- get
    let (explist, vari') = runState (observeManyT 1 $ focus (g, d) t) vari -- todo better?
    put vari'
    if null explist
       then empty   -- TODO: Isto está a por Nothing na "monad interior?" (ainda é um pouco difícil pensar nisso:) ), suponho que os outros return estão a por Just
       else return $ head explist


focus :: FocusCtxt -> Type -> LogicT (State SynthState) (Expr, Delta)
-- because of laziness it'll only run until the first succeeds (bc of observe), right?
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
            (expa, d') <- focus' Nothing c a  -- important todo: estou a assumir que aqui um possivel empty na chamada se propague e "termine a monad" ali, espero não estar a dizer nada demasiado ao lado. Eu tentei perceber o combinador com o que o prof enviou mas não consegui muito bemm
            (expb, d'') <- focus' Nothing (g, d') b
            return (TensorValue expa expb, d'')

        ---- 1R
        focus' Nothing c@(g, d) Unit = do
            guard (null d)
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
            guard (null d)
            vari <- lift get
            -- TODO: Factorizar isto? :)
            let maybeSynthResult = runStateT (synth (g, d, []) a) vari -- if asynch continuation of synthesis failed, fail to backtrack
            if isNothing maybeSynthResult
               then empty
               else do
                   let ((expa, d'), vari') = fromJust maybeSynthResult
                   lift $ put vari'
                   return (BangValue expa, d')

        -- all right propositions focused on are synchronous; this pattern matching should be extensive

        -- nota: estou a ter alguma dificuldade em visualizar que tipo de proposições vamos ter no lado direito quando focusing na esquerda...
        -- tentei inventar um tipo que me desse focusing com decideLeft mas não estou a conseguir, preciso de ajuda :)


        ---- Left synchronous rules -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = do
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            (expb, d') <- focus' (Just (nname, b)) c goal
            vari' <- get
            -- TODO: Factorizar isto? :)
            let maybeSynthResult = runStateT (synth (g, d', []) a) vari'
            if isNothing maybeSynthResult
               then empty
               else do
                   let ((expa, d''), vari'') = fromJust maybeSynthResult
                   lift $ put vari''
                   return (substitute nname (App (Var n) expa) expb, d'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal = do -- como factorizar este código ? 
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            (lf, d') <- focus' (Just (nname, a)) c goal
            return (substitute nname (Fst (Var n)) lf, d') -- ainda me faz um bocadinho confusão pensar nas regras assim, parece mesmo que estamos a complicar mesmo não estando, podemos rever a motivação?
            <|> do
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            (rt, d') <- focus' (Just (nname, b)) c goal
            return (substitute nname (Snd (Var n)) rt, d')


        ---- Proposition no longer synchronous --------

        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus
        focus' (Just nh@(n, h)) (g, d) goal =
            if isAtomic h       -- TODO: estou a criar alguma confusão em relação ao 1 ser ou não atómico
               then do
                   -- left focus is atomic
                   guard (h == goal) -- if is atomic and not the goal, fail
                   return (Var n, d)
               else do
                   ---- left focus is not atomic and not left synchronous, unfocus
                   vari <- lift get
                   -- TODO: Factorizar isto? :)
                   let maybeSynthResult = runStateT (synth (g, d, [nh]) goal) vari
                   if isNothing maybeSynthResult
                       then empty
                       else do
                           let ((exp, d'), vari') = fromJust maybeSynthResult
                           lift $ put vari'
                           return (exp, d')

        ---- right focus is not synchronous, unfocus. if it is atomic we fail
        -- ?? estou a ter tmb alguma difficuldade a visualizar esta situação :)
        focus' Nothing (g, d) goal = do
            vari <- lift get
            -- TODO: Factorizar isto? :)
            let maybeSynthResult = runStateT (synth (g, d, []) goal) vari
            if isNothing maybeSynthResult
               then empty
               else do
                   let ((e,d'), vari') = fromJust maybeSynthResult
                   lift $ put vari'
                   return (e, d')


-- TODO: Como definimos regras para bool? (IfThenElse)


---- top level

synthType :: Type -> Expr
synthType t = fst $ fromMaybe (errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t) (evalStateT (synth ([], [], []) t) 0)

synthMarks :: Expr -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks = editexp (\case {TypedMark _ -> True; _ -> False}) (\(TypedMark t) -> synthType t)

synthMarksModule :: [Binding] -> [Binding]
synthMarksModule = map (\(Binding n e) -> Binding n $ synthMarks e)
