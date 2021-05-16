module Synth where

import Control.Applicative
import Control.Monad.Logic

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool))
import Syntax

type Gamma = [(String, Type)] -- Unrestricted hypothesis
type Delta = [(String, Type)] -- Linear hypothesis (not left asynchronous)
type Omega = [(String, Type)] -- Ordered (linear?) hypothesis
type Ctxt = (Gamma, Delta, Omega)

type FocusCtxt = (Gamma, Delta) -- Gamma, DeltaIn and DeltaOut in the return value

synth :: Ctxt -> Type -> Expr

---- Right asynchronous rules -----------------

---- -oR
synth (г, d, o) (Fun a b) = Abs "x" a $ synth (г, d, ("x", a):o) b

---- &R
synth c (With a b) = WithValue (synth c a) (synth c b)

synth c (Bool) = Tru

-- no more synchronous right propositions, start inverting the ordered context (omega)


---- Left asynchronous rules ------------------

---- *L
synth (g, d, (n, Tensor a b):o) t = LetTensor "x" "y" (Var n) $ synth (g, d, ("y", b):("x", a):o) t

---- 1L
synth (g, d, (n, Unit):o) t = LetUnit (Var n) $ synth (g, d, o) t

---- +L
synth (g, d, (n, Plus a b):o) t = CaseOfPlus (Var n) "l" (synth (g, d, ("l", a):o) t) "r" (synth (g, d, ("r", b):o) t)

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


focus :: FocusCtxt -> Type -> Logic Expr
focus c t =  decideRight c t     -- because of laziness it'll only run until the first succeeds (bc of observe), right?
         <|> decideLeft c t
         <|> decideLeftBang c t    
    where
        decideRight c t = do
            (e, _) <- focus' Nothing c t
            pure e

        decideLeft (g, din) t = do
            case din of
              []     -> empty
              a:din' -> do
                  (e, _) <- focus' (Just a) (g, din') t
                  pure e

        decideLeftBang (g, din) t = do
            case g of
              []   -> empty
              a:g' -> do
                  (e, _) <- focus' (Just a) (g, din) t
                  pure e
        
        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Logic (Expr, Delta)

        ---- Right synchronous rules ------------------

        ---- *R
        focus' Nothing c@(g, d) (Tensor a b) = do
            (expa, d') <- focus' Nothing c a
            (expb, d'') <- focus' Nothing (g, d') a
            pure (TensorValue expa expb, d'')

        ---- 1R
        focus' Nothing c@(g, d) Unit = do
            guard (null d)
            pure (UnitValue, d)
            
        ---- +R
        focus' Nothing c (Plus a b) = do
            (il, d') <- focus' Nothing c a
            pure (InjL b il, d')
            <|> do
            (ir, d') <- focus' Nothing c b
            pure (InjR a ir, d')

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = do
            guard (null d)
            pure (BangValue $ synth (g, d, []) a, d)

        -- all right propositions focused on are synchronous; this pattern matching is extensive

        -- nota: estou a ter alguma dificuldade em visualizar que tipo de proposições vamos ter no lado direito quando focusing na esquerda...
        -- tentei inventar um tipo que me desse focusing com decideLeft mas não estou a conseguir, preciso de ajuda :)


        ---- Left synchronous rules -------------------

        -- focus' (Just a) c t = 


---- top level

synthType t = synth ([], [], []) t
