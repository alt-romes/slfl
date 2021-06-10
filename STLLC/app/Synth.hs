{-# LANGUAGE LambdaCase #-}
module Synth (synthAllType, synthType, synthScheme, synthMarks, synthMarksModule) where

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe
import Data.Bifunctor
import Debug.Trace


import CoreSyntax (Name, Type(..), Scheme(..))
import Syntax
import Program
import Util
import Constraints



-- TODO: refactor the Delta_Out into the state monad???

type Gamma = [(String, Either Scheme Type)] -- Unrestricted hypothesis              (Γ)
type Delta = [(String, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(String, Type)]       -- Ordered (linear?) hypothesis                 (Ω)
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

-------------------------------------------------------------------------------
-- Synth "Monad"
-------------------------------------------------------------------------------

type Synth a = LogicT (StateT SynthState (Reader [ADTD])) a 


type SynthState = ([Constraint], Int)  -- (list of constraints added by the process, next index to instance a variable)


runSynth :: (Gamma, Delta) -> Type -> SynthState -> [ADTD] -> [(Expr, Delta)]
runSynth (g, d) t st = runReader (evalStateT (observeAllT $ synth (g, d, []) t) st)


initSynthState :: SynthState
initSynthState = ([], 0)





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

addconstraint :: Constraint -> Synth ()
addconstraint c = lift $ modify (first (c :))


getadtcons :: Name -> Synth [(Name, Type)]
getadtcons tyn = do
    adtds <- lift $ lift ask
    return $ concatMap (\(ADTD _ cs) -> cs) $ filter (\(ADTD name cs) -> tyn == name) adtds


fresh :: Synth String
fresh = do 
    (cs, n) <- lift get
    lift $ put (cs, n+1)
    return $ getName n


freshIndex :: Synth Int
freshIndex = do 
    (cs, n) <- lift get
    lift $ put (cs, n+1)
    return n


assertADTHasCons :: Type -> Synth Bool
assertADTHasCons t =
    case t of
       ADT name -> do
           cons <- getadtcons name
           return $ not $ null cons
       _        ->
           return True


isAtomic :: Type -> Bool
isAtomic t =
    case t of
       TypeVar _            -> True
       ExistentialTypeVar _ -> True
       _                    -> False


---- subsitute var n with expn in expf
substitute :: String -> Expr -> Expr -> Expr
substitute n expn = transform (\case
                                v@(Var x) -> if x == n then expn else v
                                x -> x)
-- descendM

-- TODO: Make Generic and move to constraints?
ftvctx :: FocusCtxt -> Set.Set Int
ftvctx = ftvctx' Set.empty
    where
        ftvctx' :: Set.Set Int -> FocusCtxt -> Set.Set Int
        ftvctx' acc (gc, dc) = Set.unions (map (ftvctx'' . snd) gc) `Set.union` Set.unions (map (ftv . snd) dc)
        ftvctx'' = \case {Right t -> ftv t; Left sch -> ftvsch sch}
        ftvsch (Forall ns t) = Set.difference (Set.fromList ns) $ ftv t


-- TODO: Make Generic and move to constraints?
generalize :: FocusCtxt -> Type -> Scheme
generalize ctxt t = Forall ns t 
    where ns = Set.toList $ Set.difference (ftv t) (ftvctx ctxt)


-- TODO: Move to util
letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']


getName :: Int -> String
getName i = letters !! i





-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

synth :: Ctxt -> Type -> Synth (Expr, Delta)

---- * Right asynchronous rules * -----------------

---- -oR
synth (г, d, o) (Fun a b) = do
    name <- fresh
    (exp, d') <- trace ("put " ++ show a ++ " in context to get " ++ show b) $ synth (г, d, (name, a):o) b
    trace "out" $ guard (name `notElem` map fst d')
    return (Abs name (Just a) exp, d')

---- &R
synth c (With a b) = do
    (expa, d') <- synth c a
    (expb, d'') <- synth c b
    guard (d' == d'')
    return (WithValue expa expb, d')

-- no more synchronous right propositions, start inverting the ordered context (Ω)



---- * Left asynchronous rules * ------------------

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

---- adtL
synth (g, d, (n, ADT tyn):o) t =
    do
    adtds <- getadtcons tyn
    ls <- mapM (\(name, vtype) ->
        case vtype of
          Unit -> do
            (exp, d') <- synth (g, d, o) t
            return (name, "", exp, d')
          argty -> do
            varid <- fresh
            (exp, d') <- synth (g, d, (varid, argty):o) t
            return (name, varid, exp, d')
          -- TODO: polymorphic ADT
        ) adtds
    guard (not $ null ls) -- make sure constructors were found for this adtype
    let (n1, varid1, e1, d1') = head ls
    guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls)
    guard $ all ((`notElem` map fst d1') . (\(n,_,_,_) -> n)) ls
    return (CaseOf (Var n) (map (\(n, vari, exp, _) -> (n, vari, exp)) ls), d1')
    <|>
    do
    guard $ ADT tyn == t            -- !TODO: Assim deixamos de ter aquela propriedade de que não recordo o nome de desconstruirmos sempre tudo para voltar a construir, mas à partida não está errada certo?, simplesmente damos logo a variável mais cedo
    focus (g, (n, ADT tyn):d) t  -- TODO: A instanciação de Vars costuma ser quando se está focado no contexto ... posso fazer isto assim preemptivamente aqui? foi um bocado por intuição mas não sei se posso estragar as regras assim... :)


---- !L
synth (g, d, (n, Bang a):o) t = do
    nname <- fresh
    (exp, d') <- synth ((nname, Right a):g, d, o) t
    guard (nname `notElem` map fst d')
    return (LetBang nname (Var n) exp, d')



---- * Synchronous left propositions to Δ * -------

synth (g, d, p:o) t =
    synth (g, p:d, o) t



---- * Synchronous rules * -------------------------

-- no more asynchronous propositions, focus

synth (g, d, []) t = focus (g, d) t


focus :: FocusCtxt -> Type -> Synth (Expr, Delta)
focus c goal = trace ("Focus on " ++ show goal ++ " with ctx: " ++ show c)
    (decideRight c goal <|> decideLeft c goal <|> decideLeftBang c goal)

    where
        decideRight, decideLeft, decideLeftBang :: FocusCtxt -> Type -> Synth (Expr, Delta)

        decideRight c goal = do
            if isAtomic goal                            -- to decide right, goal cannot be atomic
                then empty
                else do
                    assertADTHasCons goal >>= guard     -- to decide right, goal cannot be an ADT that has no constructors
                    focus' Nothing c goal


        decideLeft (g, din) goal = do
            case din of
              []     -> empty
              _ -> foldr ((<|>) . (\x -> trace ("decide left " ++ show x ++ " to prove goal " ++ show goal) focus' (Just x) (g, delete x din) goal)) empty din


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
            (et, etvars) <- existencialInstantiate sch                                     -- tipo com existenciais
            (se, d') <- focus' (Just (n, et)) ctxt goal   -- fail ou success c restrições
            (constrs, _) <- lift get
            let unify = solveconstraintsExistential Map.empty constrs                                      -- resolve ou falha -- por conflito ou falta informação
            guard (isJust unify)                                                                -- por conflicto
            guard (Set.disjoint (Set.fromList etvars) (ftv $ apply (fromJust unify) et))        -- por falta de informação (não pode haver variáveis existenciais bound que fiquem por instanciar, i.e. não pode haver bound vars nas ftvs do tipo substituido) -- TODO: Não produz coisas erradas mas podemos estar a esconder resultados válidos
            return (se, d')                                                                     -- if constraints are "total" and satisfiable, the synth using a polymorphic type was successful
                where
                    existencialInstantiate (Forall ns t) = do
                        netvs <- mapM (const $ do {i <- freshIndex; return (ExistentialTypeVar i, i)}) ns
                        return (apply (Map.fromList $ zip ns $ map fst netvs) t, map snd netvs)



        focus' :: Maybe (String, Type) -> FocusCtxt -> Type -> Synth (Expr, Delta)

        ---- * Right synchronous rules * ------------------

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

        ---- adtR
        focus' Nothing (g, d) (ADT tyn) = do
            cons <- getadtcons tyn
            foldr ((<|>) . (\(tag, argty) -> --- (Green, Unit), (Red, Unit), (Yellow, Bool)
                   case argty of
                     Unit -> return (Var tag, d)        -- The branch where this constructor is used might fail later e.g. if an hypothesis isn't consumed from delta when it should have
                     argtype -> do
                       (arge, d') <- synth (g, d, []) argtype;
                       return (App (Var tag) arge, d')
                )) empty cons

        ---- !R
        focus' Nothing c@(g, d) (Bang a) = do
            (expa, d') <- synth (g, d, []) a
            guard (d == d')
            return (BangValue expa, d')



        ---- * Left synchronous rules * -------------------

        ---- -oL
        focus' (Just (n, Fun a b)) c@(g, d) goal = do
            nname <- fresh
            (expb, d')  <- focus' (Just (nname, b)) c goal
            (expa, d'') <- synth (g, d', []) a
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

        ---- ∃L (?)
        focus' (Just (n, ExistentialTypeVar x)) (g, d) goal =
            case goal of
              (ExistentialTypeVar y) ->
                  if x == y then return (Var n, d)          -- ?a |- ?a succeeds
                            else empty                      -- ?a |- ?b fails
              _ -> do                                       -- ?a |-  t succeeds with constraint
                  addconstraint $ Constraint (ExistentialTypeVar x) goal
                  return (Var n, d)



        ---- * Proposition no longer synchronous * --------

        ---- left focus is either atomic or not.
        ---- if it is atomic, it'll either be the goal and instanciate it, or fail
        ---- if it's not atomic, and it's not left synchronous, unfocus

        focus' (Just nh@(n, h)) (g, d) goal
          | isAtomic h                      -- left focus is atomic
          = do case goal of
                 (ExistentialTypeVar x)     -- goal is an existential proposition generate a constraint and succeed -- TODO: Fiz isto em vez de ter uma regra para left focus on TypeVar para Existencial porque parece-me que Bool |- ?a tmb deve gerar um constraint ?a => Bool, certo?
                   -> do addconstraint $ Constraint (ExistentialTypeVar x) h
                         return (Var n, d)
                 _ -> do guard (h == goal)  -- if is atomic and not the goal, fail
                         return (Var n, d)  -- else, instantiate it

          | case goal of
              (ADT tyn) -> h == ADT tyn     -- !TODO: Assim deixamos de ter aquela propriedade de que não recordo o nome de desconstruirmos sempre tudo para voltar a construir, mas à partida não está errada certo?
              _ -> False
          = return (Var n, d)               -- left focus is not atomic and not left synchronous, but we can stop deconstructing and instanciate the ADT right away.

          | otherwise
          = synth (g, d, [nh]) goal         -- left focus is not atomic and not left synchronous, unfocus



        ---- right focus is not synchronous, unfocus. if it is atomic we fail

        focus' Nothing (g, d) goal = do
            (e, d') <- synth (g, d, []) goal
            return (e, d')





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

synthCtxAllType :: (Gamma, Delta) -> [ADTD] -> Type -> [Expr]
synthCtxAllType c adts t = -- TODO : Print error se snd != [] ? Já não deve acontecer porque estamos a usar a LogicT
    let res = runSynth c t initSynthState adts in
                  if null res
                     then errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t
                     else map fst res


synthCtxType :: (Gamma, Delta) -> [ADTD] -> Type -> Expr
synthCtxType c adts t = head $ synthCtxAllType c adts t





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

synthAllType :: Type -> [Expr]
synthAllType = synthCtxAllType ([], []) []


synthType :: Type -> Expr
synthType t = head $ synthAllType t -- TODO: instanciate $ generalize t? TODO: i'm assuming this type might contain type variables, and those will be used in the synth process as universal 


synthScheme :: Scheme -> Expr
synthScheme = undefined -- forall a . T (async)  =>   instantiate T   (a' ...) -- TODO: Estou a assumir que se houverem type variables no tipo é como se já tivessem sido "instanciadas", e então começo a síntese sempre com um tipo simples, por isso este passo já não existe correto?


synthMarks :: Expr -> [ADTD] -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks ex adts = transform (\case
                                (Mark _ c t) -> trace ("CONTEXT OF MARK : " ++ show c ++ " TYPE OF MARK : " ++ show t) $ synthCtxType (map (second Left) c, []) adts (fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t)
                                x -> x
                               ) ex


synthMarksModule :: Program -> Program
synthMarksModule (Program adts bs) = Program adts $ map (\(Binding n e) -> Binding n $ synthMarks e adts) bs

