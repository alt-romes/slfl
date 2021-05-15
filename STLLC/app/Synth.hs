module Synth where

import Control.Applicative
import Control.Monad.Logic

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool))
import Syntax

type Gamma = [(String, Type)] -- Unrestricted hypothesis
type Delta = [(String, Type)] -- Linear hypothesis (not left asynchronous)
type Omega = [(String, Type)] -- Ordered (linear?) hypothesis
type Ctxt = (Gamma, Delta, Omega)

type FocusCtxt = (Gamma, Delta, Delta) -- Gamma, DeltaIn and DeltaOut

synth :: Ctxt -> Type -> Expr

---- Right asynchronous rules -----------------

---- -oR
synth (г, d, o) (Fun a b) = Abs "x" a $ synth (г, d, ("x", a):o) b

---- &R
synth c (With a b) = WithValue (synth c a) (synth c b)


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

synth (g, d, (n, Fun a b):o) t = synth (g, (n, Fun a b):d, o) t

synth (g, d, (n, With a b):o) t = synth (g, (n, With a b):d, o) t


---- Right synchronous rules ------------------

synth (g, d, []) t = -- no more asynchronous propositions, focus
       observe $ focus (g, d, []) t


focus :: FocusCtxt -> Type -> Logic Expr
focus c t = decideRight c t <|> decideLeft c t <|> decideLeftBang c t -- because of laziness it'll only run until the first succeeds (bc of observe), right?
    where
        decideRight = focus' Nothing

        decideLeft (g, din, dout) t = do
            case din of
              []     -> empty
              a:din' -> focus' (Just a) (g, din', dout) t

        decideLeftBang c t = focus' Nothing c t
        
        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Logic Expr
        focus' a c t = return Tru

