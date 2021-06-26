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


import CoreSyntax (Name, Type(..), Scheme(..), isInType)
import Syntax
import Program
import Util
import Constraints



type Gamma = [(String, Either Scheme Type)] -- Unrestricted hypothesis              (Γ)
type Delta = [(String, Type)]       -- Linear hypothesis (not left asynchronous)    (Δ)
type Omega = [(String, Type)]       -- Ordered (linear?) hypothesis                 (Ω)
type Ctxt = (Gamma, Delta, Omega)   -- Delta out is a return value
type FocusCtxt = (Gamma, Delta)     -- Gamma, DeltaIn

-------------------------------------------------------------------------------
-- Synth "Monad"
-------------------------------------------------------------------------------

type Synth a = LogicT (StateT SynthState (Reader SynthReaderState)) a 


type SynthState = ([Constraint], Int)  -- (list of constraints added by the process to solve when instantiating a scheme, next index to instance a variable)


type SynthReaderState = (Restrictions, [ADTD]) -- (list of restrictions applied on types in specific places, list of ADTDs to be always present)
type Restriction = Type -> Bool
type Restrictions = ([Restriction], [Restriction], [Restriction], [Restriction])


data TypeTag = SynthGoal | RightFocus | LeftFocus | LeftInvert


runSynth :: (Gamma, Delta) -> Type -> SynthState -> [ADTD] -> [(Expr, Delta)]
runSynth (g, d) t st adtds = runReader (evalStateT (observeAllT $ synthComplete (g, d, []) t) st) $ initSynthReaderState adtds
    where
        synthComplete (g, d, o) t = do
            (e, d') <- synth (g, d, o) t
            guard $ null d'
            return (e, d')


initSynthState :: Int -> SynthState
initSynthState i = ([], i)


initSynthReaderState :: [ADTD] -> SynthReaderState
initSynthReaderState a = (([], [], [], []), a)




-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

addconstraint :: Constraint -> Synth ()
addconstraint c = lift $ modify (first (c :))


addrestriction :: TypeTag -> Restriction -> Synth a -> Synth a
addrestriction tag r = local (\ ((a, b, c, d), adtds) ->
    case tag of
      SynthGoal -> ((r:a, b, c, d), adtds)
      RightFocus -> ((a, r:b, c, d), adtds)
      LeftFocus -> ((a, b, r:c, d), adtds)
      LeftInvert -> ((a, b, c, r:d), adtds)
    )


getrestrictions :: TypeTag -> Synth [Restriction]
getrestrictions tag = do
    (sgoal, rfocus, lfocus, linvert) <- fst <$> lift (lift ask)
    case tag of
      SynthGoal -> return sgoal
      RightFocus -> return rfocus
      LeftFocus -> return lfocus
      LeftInvert -> return linvert


removeRestrictions :: TypeTag -> Synth a -> Synth a
removeRestrictions tt = local (\((a,b,c,d),e) ->
    case tt of
      SynthGoal -> (([],b,c,d), e)
      RightFocus -> ((a,[],c,d), e)
      LeftFocus -> ((a,b,[],d), e)
      LeftInvert -> ((a,b,c,[]), e)
      )



getadtcons :: Name -> Synth [(Name, Type)]
getadtcons tyn = do
    adtds <- snd <$> lift (lift ask)
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


findType :: Type -> Delta -> Bool
findType t d = t `elem` map snd d


isAtomic :: Type -> Bool
isAtomic t =
    case t of
       TyLit _              -> True
       TypeVar _            -> True
       ExistentialTypeVar _ -> True
       _                    -> False


---- subsitute var n with expn in expf
substitute :: String -> Expr -> Expr -> Expr
substitute n expn = transform (\case
                                v@(Var x) -> if x == n then expn else v
                                x -> x)


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







-------------------------------------------------------------------------------
-- Main Logic
-------------------------------------------------------------------------------

synth :: Ctxt -> Type -> Synth (Expr, Delta)

---- * Right asynchronous rules * -----------------

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

-- no more synchronous right propositions, start inverting the ordered context (Ω)



---- * Left asynchronous rules * ------------------

---- *L
synth (g, d, (n, Tensor a b):o) t = do
    n1 <- fresh
    n2 <- fresh
    (expt, d') <- trace ("show me 5 after this bc im trying to synth " ++ show t ++ " with " ++ show ((n2,b):[(n1,a)])) synth (g, d, (n2, b):(n1, a):o) t
    trace ("5 guard " ++ show b ++ " and " ++ show a ++ " are not in context") $ guard ((n1 `notElem` map fst d') && (n2 `notElem` map fst d'))
    trace "6 passed" $ return (LetTensor n1 n2 (Var n) expt, d')

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
synth (g, d, p@(n, ADT tyn):o) t = trace ("1 deconstruct ADT " ++ tyn ++ " to synth " ++ show t ++ " with context " ++ show (g, d, o))$ do
    res <- getrestrictions LeftInvert
    trace "14 Testing constraints" $ guard $ all (\f -> f (ADT tyn)) res
    adtds <- trace "14 passed" $ getadtcons tyn
    ls <- mapM (\(name, vtype) ->
        case vtype of
          Unit -> do
            (exp, d') <- synth (g, d, o) t
            return (name, "", exp, d')
          argty -> do
            varid <- fresh
            (exp, d') <- trace ("2 Synth from branch " ++ show (name, argty) ++ " with new contxt " ++ show (g, (varid, argty):d, o)) $
                (if trace ("Is " ++ show (ADT tyn) ++ " inside " ++ show argty ++ " ? : " ++ show (ADT tyn `isInType` argty))$ ADT tyn `isInType` argty
                                        -- !TODO PROF: Validar este raciocínio. A ideia é:
                                        -- Se estivermos a sintetizar uma função por exemplo Expr -> Nat, mas em que Expr tem um constructor recursivo (ou seja, o tipo final aparece como argumento (debaixo de um número arbitrario de camadas) no construtor),
                                        -- para esse garantimos que nao nos focamos à esquerda e tentamos descontruir Expr outra vez para ter Nat,
                                        -- e para garantir que nunca tentamos construir Expr para usar como param da função Expr -> Nat que esperames usar (e.g. um construtor que possivelmente precise de Nat causará um loop infinito)
                                        -- (basicamente, para forçar a utilização de uma função Expr -> Nat com o argumento Expr que veio do tipo recursivo)
                                        -- A restrição LeftInvert apenas é verificada diretamente antes da tentativa de desconstrução (async) de um ADT
                                        -- A restrição RightFocus é verificada diretamente antes da tentativa de construção (sync) de um ADT
                   then addrestriction LeftInvert (/= ADT tyn)
                        -- . addrestriction RightFocus (/= ADT tyn)
                   else id) $ 
                    synth (g, (varid, argty):d, o) t
            trace ("successful synth of type " ++ show t ++ " with " ++ show argty ++ ": " ++ show exp) $ return (name, varid, exp, d')
          -- TODO: polymorphic ADT
        ) adtds
    guard (length ls == length adtds) -- make sure all constructors were decomposed
    let (n1, varid1, e1, d1') = head ls
    guard $ all ((== d1') . (\(_,_,_,c) -> c)) (tail ls)
    guard $ all ((`notElem` map fst d1') . (\(n,_,_,_) -> n)) ls
    return (CaseOf (Var n) (map (\(n, vari, exp, _) -> (n, vari, exp)) ls), d1')
    -- <|>
    -- do
    -- res <- getrestrictions LeftInvert
    -- trace "checking a second time" $ guard $ not $ all (\f -> f (ADT tyn)) res  -- If we failed above because a restriction didn't allow us to invert this ADT
    -- trace "passed cseond time" synth (g, p:d, o) t                                                         -- try using it the proposition in the linear context

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
focus c goal =
    decideRight c goal <|> decideLeft c goal <|> decideLeftBang c goal

    where
        decideRight, decideLeft, decideLeftBang :: FocusCtxt -> Type -> Synth (Expr, Delta)

        decideRight c goal = trace ("Focus right on " ++ show goal) $ do
            if isAtomic goal                            -- to decide right, goal cannot be atomic
                then empty
                else do
                    assertADTHasCons goal >>= guard     -- to decide right, goal cannot be an ADT that has no constructors
                    focus' Nothing c goal


        decideLeft (g, din) goal = do
            case din of
              []     -> empty
              _ -> foldr ((<|>) . (\x -> trace ("Focus left on " ++ show x ++ " to " ++ show goal) $ focus' (Just x) (g, delete x din) goal)) empty din


        decideLeftBang (g, din) goal = do
            case g of
              []   -> empty
              _ -> foldr ((<|>) . (\case {
                                        (n, Right x) -> trace ("Focus left bang on " ++ show x ++ " to " ++ show goal) $ focus' (Just (n, x)) (g, din) goal;
                                        (n, Left sch) -> trace ("Focus left bang scheme on " ++ show sch ++ " to " ++ show goal) $ focusSch (n, sch) (g, din) goal})) empty g

        
            
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
            `interleave` do
            (ir, d') <- focus' Nothing c b
            return (InjR (Just a) ir, d')

        ---- sumR
        focus' Nothing c (Sum sts) =
            foldr (interleave . (\(tag, goalt) ->
                do {
                   (e, d') <- focus' Nothing c goalt;
                   let smts = map (second Just) $ delete (tag, goalt) sts in
                   return (SumValue smts (tag, e), d')
                })) empty sts

        ---- adtR
        focus' Nothing (g, d) (ADT tyn) =
            if findType (ADT tyn) d then empty -- Preemptively check for this ADT type in the linear context, and fail the right focus to try instanciating it as a variable first --- TODO : very wrong ?
            else do
                -- res <- getrestrictions RightFocus
                -- guard $ all (\f -> f (ADT tyn)) res -- TODO: Ver explicação na destrução do ADT
                cons <- getadtcons tyn
                foldr (interleave . (\(tag, argty) -> --- (Green, Unit), (Red, Unit), (Yellow, Bool)
                       case argty of
                         Unit -> return (Var tag, d)        -- The branch where this constructor is used might fail later e.g. if an hypothesis isn't consumed from delta when it should have
                         argtype ->
                           if case argtype of
                                 ADT tyn' -> tyn == tyn' -- If the constructor for an ADT takes itself as a parameter, focus right should fail and instead focus left.
                                 _ -> False
                              then empty
                              else do
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

        -- adtLFocus
        -- if we're focusing left on an ADT X while trying to synth ADT X, instead of decomposing the ADT as we do when inverting rules, we'll instance the var right away -- else recursive types would loop infinitely
        focus' (Just nh@(n, ADT tyn)) (g, d) goal =
            if case goal of
              ADT tyn' -> tyn' == tyn
              _ -> False
              then return (Var n, d)
              else synth (g, d, [nh]) goal



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
          | otherwise
          = synth (g, d, [nh]) goal         -- left focus is not atomic and not left synchronous, unfocus



        ---- right focus is not synchronous, unfocus. if it is atomic we fail

        focus' Nothing (g, d) goal = do
            (e, d') <- synth (g, d, []) goal
            return (e, d')





-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

synthCtxAllType :: (Gamma, Delta) -> Int -> [ADTD] -> Type -> [Expr]
synthCtxAllType c i adts t =
    let res = runSynth c t (initSynthState i) adts in
                  if null res
                     then errorWithoutStackTrace $ "[Synth] Failed synthesis of: " ++ show t
                     else map fst res


synthCtxType :: (Gamma, Delta) -> Int -> [ADTD] -> Type -> Expr
synthCtxType c i adts t = head $ synthCtxAllType c i adts t





-------------------------------------------------------------------------------
-- Exported Functions
-------------------------------------------------------------------------------

synthAllType :: Type -> [Expr]
synthAllType = synthCtxAllType ([], []) 0 []


synthType :: Type -> Expr
synthType t = head $ synthAllType t -- TODO: instanciate $ generalize t? TODO: i'm assuming this type might contain type variables, and those will be used in the synth process as universal 


synthScheme :: Scheme -> Expr
synthScheme = undefined -- forall a . T (async)  =>   instantiate T   (a' ...) -- TODO: Estou a assumir que se houverem type variables no tipo é como se já tivessem sido "instanciadas", e então começo a síntese sempre com um tipo simples, por isso este passo já não existe correto?


synthMarks :: Expr -> [ADTD] -> Expr -- replace all placeholders in an expression with a synthetized expr
synthMarks ex adts = transform transformfunc ex
    where
        transformfunc =
            \case
                (Mark _ name c@(fc, bc) t) -> 
                    let t' = fromMaybe (error "[Synth] Failed: Marks can't be synthetized without a type.") t in
                    case name of
                      Nothing    -> -- Non-recursive Mark
                        synthCtxType c 0 adts t'
                      Just name' -> -- Recursive Mark
                        case t' of
                          Fun (ADT tyn) t2 ->
                              let adtcons = concatMap (\(ADTD _ cs) -> cs) $ filter (\(ADTD name cs) -> tyn == name) adts in
                              let i = 0 in
                              Abs (getName i) (Just (ADT tyn)) $ CaseOf (Var (getName i)) (synthBranches adtcons (i+1))
                              where
                                  synthBranches :: [(Name, Type)] -> Int -> [(String, String, Expr)]
                                  synthBranches adtcons i = map (\(name, vtype) ->
                                        case vtype of
                                          Unit -> do
                                            (name, "", synthCtxType c i adts t2)
                                          argty -> do
                                            (name, getName i, synthCtxType ((name', Left $ generalize ([], []) t'):fc, (getName i, argty):(name', t'):bc) (i+1) adts t2) -- TODO: Inverter ordem fun - hyp ou hyp - fun em delta? vai definir qual é tentado primeiro
                                      ) adtcons
                          _ ->
                              error "[Synth Mark] Recursive mark must be of type a -> b"
                x -> x
                           


-- pre: program has been type inferred
synthMarksModule :: Program -> Program
synthMarksModule (Program adts bs ts cs) = Program adts (map (\(Binding n e) -> Binding n $ synthMarks e adts) bs) ts cs

