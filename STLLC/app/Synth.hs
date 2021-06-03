{-# LANGUAGE LambdaCase #-}
module Synth where

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Data.Maybe
import Data.Bifunctor

import Debug.Trace

import CoreSyntax (Type (Fun, Tensor, Unit, With, Plus, Bang, Bool, Atom, TypeVar, ExistentialTypeVar, Sum), Scheme (Forall))
import Syntax
import Program
import Util
import Constraints

type Gamma = [(String, Either Scheme Type)] -- Unrestricted hypothesis
type Delta = [(String, Type)] -- Linear hypothesis (not left asynchronous)
type Omega = [(String, Type)] -- Ordered (linear?) hypothesis
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value

type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

type SynthState = Int  -- variable number to be used, note: should we also use the state monad for the delta context???

type Synth a = LogicT (StateT [Constraint] (State SynthState)) a

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

getName :: Int -> String
getName i = letters !! i

fresh :: Synth String
fresh = do 
    n <- lift $ lift get 
    lift $ lift $ put (n+1)
    return $ getName n

isAtomic :: Type -> Bool
isAtomic t = case t of
               Bool -> True
               TypeVar _ -> True
               Atom _ -> True
               _ -> False

---- subsitute var n with expn in expf
substitute :: String -> Expr -> Expr -> Expr
-- Propositions tend to appear only once due to linearity
substitute n expn = editexp (\case {Var _ -> True; _ -> False}) (\v@(Var x) -> if x == n then expn else v)

---- Synthetizer -----------------------------

synth :: Ctxt -> Type -> Synth (Expr, Delta)

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

-- synth (g, d, (n, Bool):o) t = do
--     (expa, d') <- synth (g, d, o) t
--     (expb, d'') <- synth (g, d, o) t
--     guard (d' == d'')
--     return (IfThenElse (Var n) expa expb, d')

---- Synchronous left propositions to Delta ----

synth (g, d, p:o) t =
    synth (g, p:d, o) t

---- Synchronous rules -------------------------

-- no more asynchronous propositions, focus
synth (g, d, []) t = focus (g, d) t

focus :: FocusCtxt -> Type -> Synth (Expr, Delta)
-- because of laziness it'll only run until the first succeeds (bc of observe)
focus c goal =
    decideRight c goal <|> decideLeft c goal <|> decideLeftBang c goal

    where
        decideRight :: FocusCtxt -> Type -> Synth (Expr, Delta)

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
              _ -> foldr ((<|>) . (\case {
                                        (n, Right x) -> focus' (Just (n, x)) (g, din) goal;
                                        (n, Left sch) -> focusSch (n, sch) (g, din) goal})) empty g
        
            
        ---- Eliminating Schemes
        focusSch :: (String, Scheme) -> FocusCtxt -> Type -> Synth (Expr, Delta)

        ---- VL
        focusSch (n, sch@(Forall ns t)) ctxt goal = do
            -- can only try scheme if current constraints are still safe
            -- before trying to synth Unit to use as the instanciation of an existential ?x, make sure this new constraint doesn't violate previous constraints,
            -- or else we might try to synth Unit assuming ?x again, which will fail solving the constraints, which in turn will make the Unit try to be synthed again using the other choice which is to assume ?x again...
            -- TODO: Verify and explain resoning to make sure it's correct (e.g. let id = (\x -o x); let main = {{ ... }} loops infintely without this)
            -- TODO: Do i need this verification everytime I add a constraint? Kind of makes sense, to detect issues right away
            -- TODO: Será que posso ter em vez disto uma substituição "solved" à qual sempre que quero adicionar uma constraint a resolve logo com as outras, falhando logo em vez de capturar constraints e juntar depois?
            constrs <- lift get
            let unify = solveconstraintsExistential Map.empty constrs                                      -- resolve ou falha -- por conflito ou falta informação
            guard (isJust unify)                                                                -- por conflicto
            let et = existencialInstantiate sch                                                 -- tipo com existenciais
            (se, d') <- focus' (Just (n, et)) ctxt goal   -- fail ou success c restrições
            constrs <- lift get
            let unify = solveconstraintsExistential Map.empty constrs                                      -- resolve ou falha -- por conflito ou falta informação
            guard (isJust unify)                                                                -- por conflicto
            guard (Set.disjoint (Set.fromList ns) (ftv $ apply (fromJust unify) et))            -- por falta de informação (não pode haver variáveis existenciais bound que fiquem por instanciar, i.e. não pode haver bound vars nas ftvs do tipo substituido) -- TODO: Não produz coisas erradas mas podemos estar a esconder resultados válidos
            return (se, d')                                                                     -- if constraints are "total" and satisfiable, the synth using a polymorphic type was successful
                where                                                                           -- TODO: É isto certo?
                    existencialInstantiate (Forall ns t) =
                        apply (Map.fromList $ zip ns (map ExistentialTypeVar ns)) t


        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta)

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

        -- focus' Nothing (g, d) Bool = return (Tru, d) <|> return (Fls, d)

        focus' Nothing (g, d) (ExistentialTypeVar x) =  -- TODO: Factor (Bool, Unit, etc) into "Literal?"
            -- (do
            -- (e, d') <- focus (g, d) Bool                -- focus will try all decides
            -- lift $ Writer.tell [Constraint (ExistentialTypeVar x) Bool]
            -- return (e, d'))
            -- <|>
            do
            lift $ modify (Constraint (ExistentialTypeVar x) Unit :)
            (e, d') <- focus (g, d) Unit
            return (e, d')
            -- TODO: Não é possível gerar type constraints de ?a => a' a focando-nos à direita certo? aqui apenas posso tentar instanciar literais, e falhar, para nos podermos focar no contexto e eventualmente instanciar de TypeVar para ExistencialVar e gerar o tal constraint ?a => a'

        ---- Left synchronous rules -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = do
            nname <- fresh
            (expb, d')  <- focus' (Just (nname, b)) c goal
            (expa, d'') <- synth (g, d', []) a
            css <- lift get
            return (substitute nname (App (Var n) expa) expb, d'')
            
        ---- &L
        focus' (Just (n, With a b)) c goal =
            do
                nname <- fresh
                (lf, d') <- focus' (Just (nname, a)) c goal
                return (substitute nname (Fst (Var n)) lf, d')
            <|>
            do
                nname <- fresh
                (rt, d') <- focus' (Just (nname, b)) c goal
                return (substitute nname (Snd (Var n)) rt, d')

        focus' (Just (n, ExistentialTypeVar x)) (g, d) goal = do -- TODO: Refactor
                lift $ modify (Constraint (ExistentialTypeVar x) goal :) -- TODO: Correct
                return (Var n, d)

        ---- Proposition no longer synchronous --------

        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus
        focus' (Just nh@(n, h)) (g, d) goal =
            if isAtomic h
               then do
                   -- left focus is atomic
                   case goal of
                     (ExistentialTypeVar x) -> do   -- goal is an existential proposition generate a constraint and succeed -- TODO: Fiz isto em vez de ter uma regra para left focus on TypeVar para Existencial porque parece-me que Bool |- ?a tmb deve gerar um constraint ?a => Bool, certo?
                         lift $ modify (Constraint (ExistentialTypeVar x) h :)
                         return (Var n, d)
                     _ -> do
                         guard (h == goal)          -- if is atomic and not the goal, fail
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
synthCtxAllType (g, d) t = let res = fst $ evalState (runStateT (observeAllT $ synth (g, d, []) t) []) 0 in
                  if null res
                     then errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t
                     else map fst res

synthCtxType :: (Gamma, Delta) -> Type -> Expr
synthCtxType c t = head $ synthCtxAllType c t

synthAllType :: Type -> [Expr]
synthAllType = synthCtxAllType ([], [])

synthScheme :: Scheme -> Expr
synthScheme = undefined

-- TODO: i'm assuming this type might contain type variables, and those will be used in the synth process as universal
synthType :: Type -> Expr
synthType t = head $ synthAllType t -- TODO: instanciate $ generalize t?

synthMarks :: Expr -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks = editexp
                (\case {Mark {} -> True; _ -> False})
                    (\(Mark _ c t) ->
                        trace ("CONTEXT OF MARK : " ++ show c ++ " TYPE OF MARK : " ++ show t) $ synthCtxType (map (second Left) c, []) (fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t))

synthMarksModule :: Program -> Program
synthMarksModule (Program adts bs) = Program adts $ map (\(Binding n e) -> Binding n $ synthMarks e) bs
