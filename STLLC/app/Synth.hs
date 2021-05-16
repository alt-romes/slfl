module Synth where

import Control.Applicative
import Control.Monad.Logic

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool))
import Syntax

type Gamma = [(String, Type)] -- Unrestricted hypothesis
type Delta = [(String, Type)] -- Linear hypothesis (not left asynchronous)
type Omega = [(String, Type)] -- Ordered (linear?) hypothesis
type Ctxt = (Gamma, Delta, Omega) -- Delta out is a return value

type FocusCtxt = (Gamma, Delta) -- Gamma, DeltaIn and DeltaOut in the return value

synth :: Ctxt -> Type -> (Expr, Delta)

---- Right asynchronous rules -----------------

---- -oR
synth (г, d, o) (Fun a b) = let (exp, d') = synth (г, d, ("x", a):o) b in
                                 (Abs "x" a exp , d')

---- &R
synth c (With a b) = let (expa, d') = synth c a in
                         let (expb, _) = synth c a in -- ?? DeltaOut from synth a and DeltaOut from synth b should be the same ??
                             (WithValue expa expb, d')

-- no more synchronous right propositions, start inverting the ordered context (omega)


---- Left asynchronous rules ------------------

---- *L
synth (g, d, (n, Tensor a b):o) t = let (expt, d') = synth (g, d, ("y", b):("x", a):o) t in
                                        (LetTensor "x" "y" (Var n) expt, d')

---- 1L
synth (g, d, (n, Unit):o) t = let (expt, d') = synth (g, d, o) t in
                                  (LetUnit (Var n) expt, d')

---- +L
synth (g, d, (n, Plus a b):o) t = let (expa, d') = synth (g, d, ("l", a):o) t in
                                      let (expb, _) = synth (g, d, ("r", b):o) t in -- ?? como é que garanto que ambos estes synth vão usar os mesmos recursos?
                                                                                    -- ? tenho de ter LogicT até nas invertíveis e andar para trás quando estas coisas correm mal? parece-me estranho,,
                                          (CaseOfPlus (Var n) "l" expa "r" expb, d')

---- !L
synth (g, d, (n, Bang a):o) t = synth ((n, a):g, d, o) t


---- Synchronous left propositions to Delta ----

-- synth (g, d, (n, Fun a b):o) t = synth (g, (n, Fun a b):d, o) t
-- synth (g, d, (n, With a b):o) t = synth (g, (n, With a b):d, o) t
synth (g, d, p:o) t = synth (g, p:d, o) t -- generalization of above

-- eventually the ordered context will be empty, then start focusing


---- Synchronous rules -------------------------

synth (g, d, []) t = -- no more asynchronous propositions, focus
       observe $ focus (g, d) t


focus :: FocusCtxt -> Type -> Logic (Expr, Delta)
focus c goal =  decideRight c goal     -- because of laziness it'll only run until the first succeeds (bc of observe), right?
            <|> decideLeft c goal
            <|> decideLeftBang c goal
    where
        decideRight c goal = focus' Nothing c goal

        decideLeft (g, din) goal = do
            case din of
              []     -> empty
              a:din' -> focus' (Just a) (g, din') goal

        decideLeftBang (g, din) goal = do
            case g of
              []   -> empty
              a:g' -> focus' (Just a) (g, din) goal
        
        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Logic (Expr, Delta)

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
            (il, d') <- focus' Nothing c a
            pure (InjL b il, d')
            <|> do
            (ir, d') <- focus' Nothing c b
            return (InjR a ir, d')

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = do
            guard (null d)
            let (expa, d') = synth (g, d, []) a
            return (BangValue expa, d')

        -- all right propositions focused on are synchronous; this pattern matching is extensive

        -- nota: estou a ter alguma dificuldade em visualizar que tipo de proposições vamos ter no lado direito quando focusing na esquerda...
        -- tentei inventar um tipo que me desse focusing com decideLeft mas não estou a conseguir, preciso de ajuda :)


        ---- Left synchronous rules -------------------

        focus' (Just (n, Fun a b)) c@(g, d) goal = do
            (expb, d') <- focus' (Just ("g", b)) c goal
            let (expa, d'') = synth (g, d', []) a
            return (App expb expa, d'')
            


---- top level

synthType t = fst $ synth ([], [], []) t
