{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where
import qualified Debug.Trace as Trace
import qualified Data.Map.Strict as M
import qualified OrderedMap as OM
import qualified Data.Map.Merge.Strict as M
import qualified Data.Set as S
import Data.List (intercalate, nub)
import Data.Semigroup
import qualified Control.Monad.State as ST
import qualified Control.Monad.Reader as MR
import Data.Foldable 
import Data.Traversable (sequenceA, for)
import Control.Applicative
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import Control.Exception (assert)
import Data.Maybe (catMaybes, fromJust)
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..), 
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import qualified ISL.Native.Types as ISLTy (Id)
import Foreign.Ptr
import Control.Monad (foldM)
import qualified Control.Monad (join)
import IR
import Opsem
import Lattice
import Util
import Collectingsem
import Absdomain


-- each location has an associated abstract domain.
-- each location's abstract domain is the value that is held
-- right after that location.
-- Data at a location is the value that is present *before* the isntruction
-- is executed
newtype Loc2AbsDomain = Loc2AbsDomain (M.Map Loc AbsDomain) deriving (Show)

instance Pretty Loc2AbsDomain where
    pretty (Loc2AbsDomain l2d) = pretty l2d

-- | Initial loc2d
loc2dinit :: Loc -- ^ location of the entry block
    -> AbsDomain -- ^ initial abstract domain
    -> IO (Loc2AbsDomain)
loc2dinit l d = do
    d <- absdomainCopy d
    return $ Loc2AbsDomain $ M.insert l d mempty

-- | Union at a key in l2d
loc2dUnion :: Loc -> AbsDomain -> Loc2AbsDomain -> IO Loc2AbsDomain
loc2dUnion l dcur (Loc2AbsDomain l2d) = 
    case M.lookup l l2d of
        Just dprev -> do
            dprev <- absdomainCopy dprev
            dcur <- absdomainCopy dcur
            d' <- absdomUnion dcur dprev
            return $ Loc2AbsDomain $ M.insert l d' l2d
        Nothing -> return $ Loc2AbsDomain $ M.insert l dcur l2d

-- | Get the absdomain at a located value
loc2dget :: Located a => Loc2AbsDomain -> a -> AbsDomain
loc2dget (Loc2AbsDomain l2d) a = l2d !!# (location a)
-- | Abstract domain model
data AbsDomain = AbsDomain {
    absdomval :: M.Map Id (Ptr Pwaff),
    absdomedge :: (M.Map (BBId, BBId) (Ptr Set)),
    absdombb :: M.Map BBId (Ptr Set)
} deriving(Show)

absdomainCopy :: AbsDomain -> IO AbsDomain
absdomainCopy d = do
    vals <- traverse pwaffCopy (absdomval d) 
    bbs <- traverse setCopy (absdombb d) 
    edges <- traverse setCopy (absdomedge d) 
    return $ AbsDomain vals edges bbs

-- | Take a union of two maps under a monadic context
-- | Assumes key space of 1 and 2 are equal
mapsunionM :: (Ord k, Pretty k, Pretty v, Monad m) 
    => (v -> v -> m v) 
    -> M.Map k v 
    -> M.Map k v 
    -> m (M.Map k v)
mapsunionM f m m' = do
    let ks = M.keys m
    foldM  (\mcur k -> do
            let v = m !!# k
            let v' = m' !!# k
            vunion <- f v v'
            return $ M.insert k vunion mcur
        ) M.empty ks


-- | Performs a pointwise union of pwaff over two maps.
-- | Assumes key space of 1 and 2 are equal
id2pwunion :: (Ord k, Pretty k)
    => M.Map k (Ptr Pwaff) 
    -> M.Map k (Ptr Pwaff) 
    -> IO (M.Map k (Ptr Pwaff))
id2pwunion = mapsunionM pwaffUnion

-- | perform a pointwise union of sets over two maps.
-- | Assumes key space of 1 and 2 are equal
id2setunion :: (Ord k, Pretty k)
    => M.Map k (Ptr Set)
    -> M.Map k (Ptr Set)
    -> IO (M.Map k (Ptr Set))
id2setunion = mapsunionM setUnion

-- | Union two values of the abstract domain
absdomUnion :: AbsDomain -> AbsDomain -> IO AbsDomain
absdomUnion d d' = do
    domnew <- id2pwunion (absdomval d) (absdomval d')
    edgenew <- id2setunion (absdomedge d) (absdomedge d')
    bbnew <- id2setunion (absdombb d) (absdombb d')
    return $ AbsDomain domnew edgenew bbnew


-- | dom[id]
absdomGetVal :: AbsDomain -> Id -> (Ptr Pwaff)
absdomGetVal d id = absdomval d !!# id

-- | dom[id <- v]
absdomSetVal :: Id -> Ptr Pwaff -> AbsDomain -> AbsDomain
absdomSetVal id pwaff d = 
    d { absdomval =  M.insert id pwaff (absdomval d) }


absdomSetEdge_ :: BBId -> BBId -> Ptr Set -> AbsDomain -> AbsDomain
absdomSetEdge_ bb bb' set d = 
    d { absdomedge = M.insert (bb, bb') set (absdomedge d) }


-- | dom[bb, bb']
absdomGetEdge :: BBId -> BBId -> AbsDomain -> Ptr Set
absdomGetEdge bb bb' d = absdomedge d !!# (bb, bb')

-- | dom[bb, bb'] = dom[bb, bb'] U s
absdomUnionEdge :: BBId -> BBId -> Ptr Set -> AbsDomain -> IO AbsDomain
absdomUnionEdge bb bb' s d = do
    let scur = absdomGetEdge bb bb' d
    s' <- setUnion s scur
    return $ absdomSetEdge_ bb bb' s' d

-- | dom[bb]
absdomGetBB :: BBId -> AbsDomain -> Ptr Set
absdomGetBB bb d = absdombb d !!# bb

-- | dom[bb] = dom[bb] U s
absdomUnionBB :: BBId -> Ptr Set -> AbsDomain -> IO AbsDomain
absdomUnionBB bb s d = do
    let scur = absdomGetBB bb d
    s' <- setUnion s scur
    return $ d { absdombb = M.insert bb s' (absdombb d) }


-- restrict the domain of all values
absdomRestrictValDomains :: Ptr Set -> AbsDomain  -> IO AbsDomain
absdomRestrictValDomains s d = do
    absdomval' <- traverse 
        (\pw -> do
            s <- setCopy s 
            pw <- pwaffCopy pw
            pwaffIntersectDomain pw s)
        (absdomval d)
    return $ d { absdomval = absdomval'}


instance Pretty AbsDomain where
    pretty d = 
        vcat [pretty "Val:", indent 1 $ pretty (absdomval d),
              pretty "BB:", indent 1 $ pretty (absdombb d),
              pretty "Edge:", indent 1 $ pretty (absdomedge d)]


-- | Create the set space common to all functions in the abstract domain
absSetSpace :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> IO (Ptr Space)
absSetSpace ctx id2isl = do
    s <- spaceSetAlloc ctx 0 (length id2isl)
    s <- OM.foldMWithIx s id2isl 
        (\s ix _ islid -> idCopy islid >>= setDimId s IslDimSet ix)
    return s


-- return the ISL state that is used in common across the absint
newISLState :: Program -> IO (Ptr Ctx, OM.OrderedMap Id (Ptr ISLTy.Id))
newISLState p = do
    ctx <- ctxAlloc
    islAbortOnError ctx
    let ids = S.toList (progids p) ++ S.toList (progvivs p)
    islids <- OM.fromList  <$> for ids (\id -> (id, ) <$> idAlloc ctx (show id))

    return $ (ctx, islids)

-- | Create a pwaff that takes on the value of the variable
pwVar :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Id -> IO (Ptr Pwaff)
pwVar ctx id2isl id = do
  ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace
  Just ix <- findDimById ls IslDimSet (id2isl OM.! id)
  affVarOnDomain ls IslDimSet ix >>= pwaffFromAff


-- | Create a constant pwaff
pwConst :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Int -> IO (Ptr Pwaff)
pwConst ctx id2isl i = do
    ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace 
    pwaffInt ctx ls i

-- Initial abstract domain
absDomainStart :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    ->  Program 
    -> IO AbsDomain
absDomainStart ctx id2isl p = do
    dval <- M.fromList <$> 
        for (S.toList (progids p))
            (\id -> (pwVar ctx id2isl id) >>= \pw -> return (id, pw))

    let edges = progedges p
    dedge <- M.fromList <$> for edges
        (\e -> (e,) <$> (absSetSpace ctx id2isl >>= setEmpty))

    dbb <- M.fromList <$> for (zip [0..] (progbbs p))
        (\(ix, bb) ->
            if ix == 0
            then do
                s <- absSetSpace ctx id2isl >>= setUniverse
                return (bbid bb, s)
            else do 
                s <- absSetSpace ctx id2isl >>= setEmpty
                return (bbid bb, s))
    return $ AbsDomain dval dedge dbb

-- Abstract interpret expressions
abstransexpr :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id
    -> Expr
    -> AbsDomain
    -> IO (Ptr Pwaff)
abstransexpr ctx id2isl id (EId id') absdom = 
    pwaffCopy (absdomGetVal absdom id')

abstransexpr ctx id2isl _ (EInt i) _ = pwConst ctx id2isl i

abstransexpr ctx id2isl _ (EBinop Add id1 id2) absdom = do
    pw1 <- pwaffCopy $ absdomGetVal absdom id1
    pw2 <- pwaffCopy $ absdomGetVal absdom id2
    pwaffAdd pw1 pw2


abstransexpr ctx id2isl _ (EBinop Lt id1 id2) absdom = do
    pw1 <- pwaffCopy $ absdomGetVal absdom id1
    pw2  <- pwaffCopy $ absdomGetVal absdom id2
    lt <- pwaffLtSet pw1 pw2

    pwt <- (pwConst ctx id2isl (-1))
    pwt <- setCopy lt >>= pwaffIntersectDomain pwt

    pwf <- (pwConst ctx id2isl 0)
    pwf <- setComplement lt >>= pwaffIntersectDomain pwf
    pwaffUnionAdd pwt pwf
    

-- | Abstract interpret assignment expressions
-- | TODO: code repetition of forwarding to BB. This should most likely
-- | be the responsibility of the BB code.
abstransassign :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> Ptr Set -- ^ Take, Conditions under which this assignment is active
    -> Assign
    -> AbsDomain
    -> IO AbsDomain
abstransassign ctx id2isl p dom a d = do
    let e = assignexpr a
    let id = assignid a

    dom <- setCopy dom
    pwaff <- abstransexpr ctx id2isl id e d 
    pwaff <- pwaffIntersectDomain pwaff dom
    return $ absdomSetVal id pwaff d



-- | If edge enters a loop, constrain it to set (loopvar = 0)
edgeConstrainOnLoopEnter :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> BBId -- ^ entering bbid
    -> Ptr Set -- ^ current conditions
    -> IO (Ptr Set)
edgeConstrainOnLoopEnter ctx id2isl p bbid s = do
    let bbid2nl = progbbid2nl p
    case bbid2nl M.!? bbid of
        Nothing -> return s
        Just nl -> do
            putDocW 80 (pretty "#NATURAL LOOP: " <> 
                pretty nl <> pretty "\n")
            putDocW 80 (pretty "#SET" <> pretty s <> pretty "\n")
            -- dim of the loop
            let lid = id2isl OM.! (nl2loopid nl)
            Just ldim <- findDimById s IslDimSet lid
            -- set dim of loop = 0
            c <- getSpace s >>= localSpaceFromSpace >>= 
                constraintAllocEquality 
            c <- constraintSetCoefficient c IslDimSet ldim 1
            s <- setCopy s >>= \s -> setAddConstraint s c
            putDocW 80 (pretty "#SET" <> pretty s <> pretty "\n")
            return s



-- | Abstract interpret terminators
abstransterm :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> BBId -- ^ Current BBId
    -> Term
    -> AbsDomain
    -> IO [(BBId, AbsDomain)] -- ^ List of basic blocks and updated abstract domains
abstransterm ctx id2isl p _ (Done _) d = return []
abstransterm ctx id2isl p bb (Br _ bb') d = do
    let s = absdomGetBB bb d
    s <- edgeConstrainOnLoopEnter ctx id2isl p bb' s
    d <- absdomainCopy d
    d <- setCopy s >>= \s -> absdomUnionEdge bb bb' s d
    d <- setCopy s >>= \s -> absdomUnionBB bb' s d
    return [(bb', d)]

abstransterm ctx id2isl p bb (BrCond _ c bbl bbr) d = do
    vc <- pwaffCopy $ absdomGetVal d c
    let dbb  = absdomGetBB bb d
    d <- absdomainCopy d

    -- true = -1
    vcTrue <- (pwConst ctx id2isl (-1)) >>= pwaffEqSet vc 
    vcTrue <- setCopy dbb >>= \dbb -> vcTrue `setIntersect` dbb
    vcTrue <- edgeConstrainOnLoopEnter ctx id2isl p bbl vcTrue
    d <- setCopy vcTrue >>= \s -> absdomUnionEdge bb bbl s d
    d <- absdomUnionBB bbl vcTrue d


    vcFalse <- setCopy vcTrue >>= setComplement
    vcFalse <- setCopy dbb >>= \dbb -> vcFalse `setIntersect` dbb
    vcFalse <- edgeConstrainOnLoopEnter ctx id2isl p bbl vcFalse
    d <- setCopy vcFalse >>= \s -> absdomUnionEdge bb bbr s d
    d <- absdomUnionBB bbr vcFalse d
    putStrLn "#### term: doml before###"

    doml <- setCopy $ absdomGetBB bbl d 
    dl <- absdomainCopy d >>= absdomRestrictValDomains doml


    domr <- setCopy $ absdomGetBB bbr d
    dr <- absdomainCopy d >>= absdomRestrictValDomains domr

    return $ [(bbl, dl), (bbr, dr)]

-- | take a disjoin union of two pwaffs
-- | Take, Take -> Give
pwaffUnion :: Ptr Pwaff -> Ptr Pwaff -> IO (Ptr Pwaff)
pwaffUnion pl pr = do
    dl <- pwaffCopy pl >>= pwaffDomain 
    dr <- pwaffCopy pr >>= pwaffDomain 
    dintersect <- setIntersect dl dr
    deq <- pwaffCopy pl >>= \pl -> pwaffCopy pr >>= \pr -> pwaffEqSet pl pr

    Just isEqOnCommon <- setIsSubset dintersect deq
    if isEqOnCommon
    then  do
        pl <- pwaffCopy pl
        pr <- pwaffCopy pr
        pwaffUnionAdd pl pr
    else do 
        putDocW 80 $ vcat $ 
            [pretty "---"
            , pretty "pl: " <> pretty pl <> pretty "| dl: " <> pretty dl
            , pretty "pr: " <> pretty pr <> pretty "| dr: " <> pretty dr
            , pretty "dintersect: " <> pretty dintersect
            , pretty "deq: " <> pretty deq
            , pretty "---\n"]
        error $ "pwaffs are not equal on common domain"


-- | update abstact domain if we are entering into a loop phi node
absintEntryIntoLoopPhi :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> BBId
    -> AbsDomain
    -> IO AbsDomain
absintEntryIntoLoopPhi ctx id2isl p bbid d = return d
    
-- | Abstract interpret phi nodes
abstransphis :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    -> Program 
    -> Phi 
    -> AbsDomain 
    -> IO AbsDomain
abstransphis cx id2isl p phi d = do
    putDocW 80 (pretty d)
    pl <-  pwaffCopy $ absdomGetVal d (snd . phil $ phi)
    pr <-  pwaffCopy $ absdomGetVal d (snd . phir $ phi)
    pwaff <- pwaffUnion pl pr
    return $ absdomSetVal (phiid phi) pwaff d


foldM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldM1 f (a:as) = foldM f a as

-- | Abstract interpret basic blocks
absintbb :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    -> Program 
    -> AbsDomain -- ^ identity abstract domain
    -> BB 
    -> Loc2AbsDomain 
    -> IO Loc2AbsDomain
absintbb ctx id2isl p dmempty bb l2d = do
    putStrLn $ "\n########0:" ++ show (bbid bb) ++ "#######"
    -- putDocW 80 (pretty (progbbid2preds p))
    let preds = (progbbid2preds p) !!# (bbid bb)
    let pred_ds = map (\bb -> loc2dget l2d  bb) preds

    putDocW 80 (vcat (map (\d -> vcat [pretty "vvv",pretty d, pretty "^^^"]) pred_ds))
    -- create a union.
    -- HACK: special case for entry BB
    d <- if null pred_ds
        then return dmempty
        else foldM1 absdomUnion pred_ds 
    putStrLn $ "\n########01:" ++ show (bbid bb) ++ "#######"
    -- forward this to the first instruction in the bb
    l2d <- loc2dUnion (bbFirstInstLoc bb) d l2d
    putStrLn $ "\n########02:" ++ show (bbid bb) ++ "#######"

    -- now abstract interpret each instruction, forwarding the
    -- data as expected
    l2d <- foldM 
        (\l2d a -> do
            let d = loc2dget l2d a
            let dom = absdomGetBB (bbid bb) d
            d' <- abstransassign ctx id2isl p dom a d
            -- set the value at the next location
            l2d <- loc2dUnion (locincr (location a)) d' l2d
            return l2d
        ) l2d (bbinsts bb)

    putStrLn "\n########1#######"
    -- | now abstract interpret the terminator, updating
    -- | the states of everyone after us.
    let t = bbterm bb
    bbid2d <- abstransterm ctx id2isl p (bbid bb) t (loc2dget l2d t)
    putStrLn "\n########2#######"
    l2d <- foldM (\l2d (bbid', d) -> do
        let bbid2bb = progbbid2bb p
        let bb' = bbid2bb !!# bbid'
        -- update at the location of the next bb
        putStrLn $ 
            ("\n########2:" ++ show (bbid bb) ++ "->>>" 
            ++ show (bbid bb') ++ "#######")
        loc2dUnion (bbloc bb') d l2d 
        ) l2d bbid2d
        
    putStrLn "\n########4#######"
    return l2d


    
-- perform the abstract interpretation for one iteration
absint_ :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program 
    -> AbsDomain -- ^ Identity abstract domain
    -> Loc2AbsDomain 
    -> IO Loc2AbsDomain
absint_ ctx id2isl p dmempty l2d = do
    foldM (\l2d bb -> absintbb ctx id2isl p dmempty bb l2d) l2d (progbbs p)
    

absint :: Program -> IO Loc2AbsDomain
absint p = do
     (ctx, id2isl) <- newISLState p
     dmempty <- absDomainStart ctx id2isl p
     l2d <- loc2dinit (Loc (-1)) dmempty
     absint_ ctx id2isl p dmempty l2d


gamma :: AbsDomain -> ConcreteDomain
gamma = undefined




-- Example programs
-- ================

{-



pNestedLoop :: Program
pNestedLoop = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing 
  loop1 <- buildNewBB "loop" (Just $ BBLoop [])
  loop2 <- buildNewBB "loop2" (Just $ BBLoop [])
  exit <- buildNewBB "exit" Nothing

  focusBB entry
  assign "x_entry" (EInt 1)
  br loop1


  focusBB loop1
  phi Philoop "x_loop" (entry, "x_entry") (loop1, "x_next")
  assign "y_entry" (EInt 0)

  assign "x_loop_lt_5" ("x_loop" <. (EInt 5))
  assign "x_next" ("x_loop" +. (EInt 1))

  condbr "x_loop_lt_5" loop2 exit

  focusBB loop2
  phi Philoop "y_loop" (loop1, "y_entry") (loop2, "y_next")
  assign "x_loop_lt_2" ("y_loop" <. (EInt 2))
  assign "y_loop_next" ("y_loop" +. (EInt 1))
  condbr "y_loop_lt_2" loop2 loop1


  focusBB exit
  done

pAdjacentLoop :: Program
pAdjacentLoop = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing 
  loop1 <- buildNewBB "loop" (Just $ BBLoop [])
  loop1_to_loop2 <- buildNewBB "loop1_to_loop2" (Just $ BBLoop [])
  loop2 <- buildNewBB "loop2" (Just $ BBLoop [])
  exit <- buildNewBB "exit" Nothing

  focusBB entry
  assign "x_entry" (EInt 1)
  br loop1


  focusBB loop1
  phi Philoop "x_loop" (entry, "x_entry") (loop1, "x_next")

  assign "x_loop_lt_5" ("x_loop" <. (EInt 5))
  assign "x_next" ("x_loop" +. (EInt 1))

  condbr "x_loop_lt_5" loop1 loop1_to_loop2

  focusBB loop1_to_loop2
  assign "y_entry" (EInt 0)
  br loop2

  focusBB loop2
  phi Philoop "y_loop" (loop1_to_loop2, "y_entry") (loop2, "y_next")
  assign "x_loop_lt_2" ("y_loop" <. (EInt 2))
  assign "y_loop_next" ("y_loop" +. (EInt 1))
  condbr "y_loop_lt_2" loop2 loop1


  focusBB exit
  done
-}

passign :: Program
passign = runProgramBuilder $ do
    param "p"
    entry <- buildNewBB "entry" Nothing
    focusBB entry
    assign "one" $ EInt 1
    assign "minus_one" $ EInt (-1)
    assign "p_plus_p" $ "p" +. "p"
    assign "p_plus_one" $ "p" +. "one"
    assign "p2" $ "p_plus_one" +. "minus_one"
    done


pif :: Program
pif = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing
  true <- buildNewBB "true" Nothing
  false <- buildNewBB "false" Nothing
  merge <- buildNewBB "merge" Nothing
  p <- param "p"
  

  focusBB entry
  assign "two" $ EInt 2
  assign "p_lt_2" $ "p" <. "two"
  condbr "p_lt_2" true false

  focusBB true
  assign "yt" (EInt 1)
  assign "xt" (EInt 1)
  br merge

  focusBB false
  assign "yf" (EInt (-1))
  assign "xf" (EInt (1))
  br merge

  focusBB merge
  m <- phi Phicond "m" (true, "yt") (false, "yf")
  m2 <- phi Phicond "m2" (true, "xt") (false, "xf")
  done

ploop :: Program
ploop = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing 
  loop <- buildNewBB "loop" (Just . BBLoop . S.fromList $ [])
  exit <- buildNewBB "exit" Nothing

  focusBB entry
  assign "one" $ (EInt 1)
  assign "five" $ (EInt 5)
  assign "x_entry" $ EId (Id "one")

  br loop

  focusBB exit
  done

  focusBB loop
  phi Philoop "x_loop" (entry, "x_entry") (loop, "x_next")

  assign "x_loop_lt_5" ("x_loop" <. "five")
  assign "x_next" ("x_loop" +. "one")
  condbr "x_loop_lt_5" loop exit

-- 
-- -- ========================
-- -- CHOOSE YOUR PROGRAM HERE
-- -- ========================


runProgram :: Program -> Env Int -> IO ()
runProgram p e = do
    putStrLn "***program***"
    putDocW 80 (pretty p)
    putStrLn ""

    putStrLn "***program output***"
    let outenv = (programExec semConcrete p) e
    print outenv

    --putStrLn "***collecting semantics (concrete x symbol):***"
    --let cbegin = (collectingBegin pcur e) :: Collecting Int
    --let csem = programFixCollecting semConcrete pcur cbegin
    --putDocW 80 (pretty csem)

    putStrLn "***absint output***"
    absenv <- absint p
    putDocW 80 (pretty absenv)

-- | Default environment we start with
edefault :: Env Int
edefault = envFromParamList [(Id "p", 1)]

programs :: [(Program, Env Int)]
programs = [(passign, edefault)
            , (pif, edefault)
            -- , (ploop, edefault)
           ] 

-- | Main entry point that executes all programs
main :: IO ()
main = for_ programs (\(p, e) -> do
    runProgram  p e
    putStrLn "\n=========================")

