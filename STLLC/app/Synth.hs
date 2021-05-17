module Synth where

import Control.Applicative
import Control.Monad.Logic

import Control.Monad.State

import Debug.Trace

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool))
import Syntax

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
               Unit -> True
               _ -> False

synth :: Ctxt -> Type -> State SynthState (Expr, Delta)

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
    (expb, _) <- synth c a -- ?? DeltaOut from synth a and DeltaOut from synth b should be the same ??
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
    (exp, d') <- synth ((nname, a):g, d, o) t
    put $ vari + 1
    return (LetBang nname (Var n) exp, d')


---- Synchronous left propositions to Delta ----

-- synth (g, d, (n, Fun a b):o) t = synth (g, (n, Fun a b):d, o) t
-- synth (g, d, (n, With a b):o) t = synth (g, (n, With a b):d, o) t
synth (g, d, p:o) t = synth (g, p:d, o) t -- generalization of above

-- eventually the ordered context will be empty, then start focusing


---- Synchronous rules -------------------------

-- no more asynchronous propositions, focus
synth (g, d, []) t = 
    fmap head $ observeManyT 1 $ focus (g, d) t -- todo better?


focus :: FocusCtxt -> Type -> LogicT (State SynthState) (Expr, Delta)
-- because of laziness it'll only run until the first succeeds (bc of observe), right?
focus c goal =
    decideRight c goal <|> decideLeft c goal <|> decideLeftBang c goal

    where
        decideRight c goal =
            case goal of               -- to decide right, goal cannot be atomic
              Bool -> empty
              _ -> focus' Nothing c goal

        decideLeft (g, din) goal = do
            case din of
              []     -> empty
              a:din' -> trace ("DLeft + " ++ show a) $ focus' (Just a) (g, din') goal

        decideLeftBang (g, din) goal = do
            case g of
              []   -> empty
              a:g' -> focus' (Just a) (g, din) goal
        
        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> LogicT (State SynthState) (Expr, Delta)

        ---- Right synchronous rules ------------------

        ---- *R
        focus' Nothing c@(g, d) (Tensor a b) = do
            (expa, d') <- focus' Nothing c a  -- important todo: estou a assumir que aqui um possivel empty na chamada se propague e "termine a monad" ali, espero não estar a dizer nada demasiado ao lado. Eu tentei perceber o combinador com o que o prof enviou mas não consegui muito bemm
            (expb, d'') <- focus' Nothing (g, d') a
            return (TensorValue expa expb, d'')

        ---- 1R
        focus' Nothing c@(g, d) Unit = do
            guard (null d)
            return (UnitValue, d)
            
        ---- +R
        focus' Nothing c (Plus a b) = do
            (il, d') <- trace "try injl" $ focus' Nothing c a
            return (InjL b il, d')
            <|> do
            (ir, d') <- trace "try injr" $ focus' Nothing c b
            return (InjR a ir, d')

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = do
            guard (null d)
            vari <- lift get
            let ((expa, d'), vari') = runState (synth (g, d, []) a) vari
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
            let ((expa, d''), vari') = runState (synth (g, d', []) a) (vari+1)
            lift $ put vari'
            return (LetIn nname (App (Var n) expa) expb, d'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal = do -- como factorizar este código ? 
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            (lf, d') <- trace "try first" $ focus' (Just (nname, a)) c goal
            trace ("returned first + " ++ show lf ++ " " ++ show d') $ return (LetIn nname (Fst (Var n)) lf, d') -- ainda me faz um bocadinho confusão pensar nas regras assim, parece mesmo que estamos a complicar mesmo não estando, podemos rever a motivação?
            <|> do
            vari <- lift get
            let nname = getName vari
            lift $ put $ vari + 1
            (rt, d') <- trace "try snd" $ focus' (Just (nname, b)) c goal
            return (LetIn nname (Snd (Var n)) rt, d')


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
                   let ((e,d'), vari') = runState (synth (g, d, [nh]) goal) vari
                   lift $ put vari'
                   return (e, d')

        ---- left focus is not atomic and not left synchronous, unfocus
        -- focus' (Just a) (g, d) goal = do
        --     vari <- lift get
        --     let ((e,d'), vari') = runState (synth (g, d, [a]) goal) vari
        --     lift $ put vari'
        --     return (e, d')
        
        ---- right focus is not atomic and not synchronous, unfocus. if it is atomic we fail
        -- ?? estou a ter tmb alguma difficuldade a visualizar esta situação :)
        focus' Nothing (g, d) goal = do
            if isAtomic goal
               then empty
               else do
                   vari <- lift get
                   let ((e,d'), vari') = runState (synth (g, d, []) goal) vari
                   lift $ put vari'
                   return (e, d')



---- top level

synthType t = fst $ evalState (synth ([], [], []) t) 0
