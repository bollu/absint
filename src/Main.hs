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


-- | each location has an associated abstract domain.
-- | each location's abstract domain is the value that is held
-- | right after that location.
-- | Data at a location is the value that is present *after* the isntruction
-- | is executed
newtype Loc2AbsDomain = Loc2AbsDomain (M.Map Loc AbsDomain) deriving (Show, Eq)

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
loc2dUnion :: Located a => a -> AbsDomain -> Loc2AbsDomain -> IO Loc2AbsDomain
loc2dUnion a d (Loc2AbsDomain l2d) = 
    let l = location a in
    case M.lookup l l2d of
        Just dprev -> do
            --- putStrLn "before loc2dunion"
            --- putStrLn "vvvvvvvvvvv"
            --- putDocW 80 $ pretty dprev
            --- putStrLn "\n============"
            --- putDocW 80 $ pretty d
            --- putStrLn "\n^^^^^^^^^^^"
            dprev <- absdomainCopy dprev
            d <- absdomainCopy d

            -- putDocW 80 $ pretty "\n===location:" <> pretty l <> 
            --     pretty "\n1.\n" <> pretty dprev <> 
            --     pretty "\n2.\n" <> pretty d <> 
            --     pretty "\n===\n"
            d' <- absdomUnion d dprev
            putStrLn "after loc2dunion"
            return $ Loc2AbsDomain $ M.insert l d' l2d
        Nothing -> return $ Loc2AbsDomain $ M.insert l d l2d

-- | Get the absdomain at a located value, and nothing if unable to
-- | find anything
loc2dgetmaybe :: Located a => Loc2AbsDomain -> a -> Maybe AbsDomain
loc2dgetmaybe(Loc2AbsDomain l2d) a = l2d M.!? (location a) 

-- | Get the absdomain at a located value
loc2dget :: Located a => Loc2AbsDomain -> a -> AbsDomain
loc2dget (Loc2AbsDomain l2d) a = l2d !!# (location a)
-- | Abstract domain model
data AbsDomain = AbsDomain {
    absdomval :: M.Map Id (Ptr Pwaff),
    absdomedge :: (M.Map (BBId, BBId) (Ptr Set)),
    absdombb :: M.Map BBId (Ptr Set)
} deriving(Show, Eq)

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
    putStrLn "before absdomunion"
    domnew <- id2pwunion (absdomval d) (absdomval d')
    putStrLn "after absdomunion"
    edgenew <- id2setunion (absdomedge d) (absdomedge d')
    bbnew <- id2setunion (absdombb d) (absdombb d')
    return $ AbsDomain domnew edgenew bbnew


-- | dom[id]
absdomGetVal :: AbsDomain -> Id -> (Ptr Pwaff)
absdomGetVal d id = absdomval d !!# id

-- | dom[id <- v]
absdomSetVal_ :: Id -> Ptr Pwaff -> AbsDomain -> AbsDomain
absdomSetVal_ id pwaff d = 
    d { absdomval =  M.insert id pwaff (absdomval d) }

absdomUnionVal :: Id -> Ptr Pwaff -> AbsDomain -> IO AbsDomain
absdomUnionVal id pwaff d = do
    let pwcur = absdomGetVal d id
    putStrLn "before absdom union val"
    pw' <- pwaffUnion pwaff pwcur
    putStrLn "after absdom union val"
    return $ absdomSetVal_ id pw' d
    


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


-- | dom[bb] = dom[bb] U s
absdomIntersectBB :: BBId -> Ptr Set -> AbsDomain -> IO AbsDomain
absdomIntersectBB bb s d = do
    let scur = absdomGetBB bb d
    s' <- setIntersect s scur
    return $ d { absdombb = M.insert bb s' (absdombb d) }



-- restrict the domain of all values. Keep set
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
    let ids = S.toList $ (progparams p) `S.union` (progvarids p) `S.union`  (progvivs p)
    islids <- OM.fromList  <$> for ids (\id -> (id, ) <$> idAlloc ctx (show id))

    return $ (ctx, islids)

-- | Create a pwaff that takes on the value of the variable
pwVar :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Id -> IO (Ptr Pwaff)
pwVar ctx id2isl id = do
  ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace
  Just ix <- findDimById ls IslDimSet (id2isl OM.! id)
  affVarOnDomain ls IslDimSet ix >>= pwaffFromAff


-- | Create a pwaff that takes on the value of the variable


-- | Create a constant pwaff
pwConst :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Int -> IO (Ptr Pwaff)
pwConst ctx id2isl i = do
    ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace 
    pwaffInt ctx ls i


-- construct a pwnan on the n-dimensional space
pwnan :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id)  -> IO (Ptr Pwaff)
pwnan ctx id2isl = do
    ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace
    emptyset <- absSetSpace ctx id2isl >>= setEmpty

    pwaff <- pwaffInt ctx ls 0
    pwaff <- pwaffIntersectDomain pwaff emptyset
    return pwaff

-- Initial abstract domain
absDomainStart :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    ->  Program 
    -> IO AbsDomain
absDomainStart ctx id2isl p = do
    dparams <- M.fromList <$> 
        for (S.toList (progparams p))
            (\id -> (pwVar ctx id2isl id) >>= \pw -> return (id, pw))

    dvars <- M.fromList <$>
        for (S.toList (progvarids p))
            (\id -> (pwnan ctx id2isl) >>= \pw -> return (id, pw))

    let dvals = dvars `M.union` dparams


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
    return $ AbsDomain dvals dedge dbb

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
    absdomUnionVal id pwaff d


-- | The to basic block is the header of the natural loop and the
-- | from basic block is in th eloop
isEdgeBackedge :: Program -> (BBId, BBId) -> Bool
isEdgeBackedge p (bbidfrom, bbidto) = do
    case progbbid2nl p M.!? bbidto of
        Nothing -> False
        Just nl -> 
            (bbidfrom `S.member` nlbody nl || bbidfrom == nlheader nl)

-- | the to basic block is the header of a natural loop, and the from
-- | basic block is *outside* the natural loop
isEdgeEnteringLoop :: Program -> (BBId, BBId) -> Bool
isEdgeEnteringLoop p (bbidfrom, bbidto) = do
    case progbbid2nl p M.!? bbidto of
        Nothing -> False
        Just nl -> 
            not $ bbidfrom `S.member` nlbody nl || bbidfrom == nlheader nl

-- | Increment the given *parameter* dimension by 1
-- | TODO: use this function
pwaffIncrParamDimension :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id -- ^ dimension to be incremented
    -> Ptr Pwaff
    -> IO (Ptr Pwaff)
pwaffIncrParamDimension ctx id2isl id pw = do
    let islid = id2isl OM.! id
    -- ID of the parametric dimension to be incremented
    n <- ndim pw IslDimParam
    Just ixid <- findDimById pw IslDimIn islid 

    -- [v1, v2, ... vloop = N] -> [VAL]
    pwmap <- pwaffCopy pw >>= mapFromPwaff

    domain <- pwaffGetDomainSpace pw >>= setUniverse

    -- [v1, v2, ... vloop] -> [v1', v2', ... vloop']
    incrmap <- setCopy domain >>= 
        \d -> setCopy domain >>= 
            \d' -> mapFromDomainAndRange d d'

    -- [vloop' = vloop + 1]
    c <- getSpace incrmap >>= localSpaceFromSpace >>= 
        constraintAllocEquality 
    c <- constraintSetCoefficient c IslDimIn ixid (1)
    c <- constraintSetCoefficient c IslDimOut ixid (-1)
    c <- constraintSetConstant c (1)
    incrmap <- mapAddConstraint incrmap c

    pwmap <- mapApplyDomain  pwmap incrmap

    pw <- pwaffFromMap pwmap
    return pw
    -- pws <- MR.forM [0..n] (\i -> do
    --     let id = (OM.keys id2isl) !! i
    --     if i == ixid
    --     then do
    --         pwcur <- pwVar ctx id2isl id
    --         pwone <- pwConst ctx id2isl 1
    --         pwaffAdd pwcur pwone
    --     else pwVar ctx id2isl id)

    -- sp <- pwaffGetSpace pw
    -- -- TODO: work on fixing this function
    -- pw_multi <- toListPwaff ctx pws >>= multipwaffFromPwaffList sp
    -- pw <- pwaffPullbackMultipwaff pw pw_multi
    -- return pw

setIncrParamDimension :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id -- ^ dimension to be incremented
    -> Ptr Set
    -> IO (Ptr Set)
setIncrParamDimension ctx id2isl id s = do
    let islid = id2isl OM.! id
    -- ID of the parametric dimension to be incremented
    n <- ndim s IslDimSet
    Just ixid <- findDimById s IslDimSet islid 


    domain <- setCopy s >>= setGetSpace  >>= setUniverse

    -- [v1, v2, ... vloop] -> [v1', v2', ... vloop']
    incrmap <- setCopy domain >>= 
        \d -> setCopy domain >>= 
            \d' -> mapFromDomainAndRange d d'

    -- [vloop' = vloop + 1]
    c <- getSpace incrmap >>= localSpaceFromSpace >>= 
        constraintAllocEquality 
    c <- constraintSetCoefficient c IslDimIn ixid (1)
    c <- constraintSetCoefficient c IslDimOut ixid (-1)
    c <- constraintSetConstant c (1)
    incrmap <- mapAddConstraint incrmap c

    setApply s incrmap




-- | Transfer values from the right to the phi on a backedge
absdomTransferOnLoopBackedge :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> (BBId, BBId) -- ^ Edge
    -> AbsDomain -- ^ current conditions
    -> IO AbsDomain
absdomTransferOnLoopBackedge ctx id2isl p (bbidfrom, bbidto) d = do
    if isEdgeBackedge p (bbidfrom, bbidto)
    then do
        let nl = progbbid2nl p !!# bbidto
        let lid = id2isl OM.! (nl2loopid nl)
        foldM (\d phi -> do
                let vidr = snd . phir  $ phi
                pw <- pwaffCopy $ absdomGetVal d vidr
                -- Increment the dimension of the loop, so we get the effect
                -- at the next loop iteration
                pw <- pwaffIncrParamDimension ctx id2isl (nl2loopid nl) pw
                -- NOTE: this is *destructive* and overwrites the previous values
                d <- absdomUnionVal (phiid phi) pw d


                s <- setCopy $ absdomGetBB bbidto d
                putDocW 80 $ pretty "setIncrParamDimension(before):" <> pretty s  <> pretty "\n"
                s <-  setIncrParamDimension ctx id2isl (nl2loopid nl) s
                putDocW 80 $ pretty "setIncrParamDimension(after):" <> pretty s  <> pretty "\n"
                d <- absdomUnionBB bbidto s d 
                return d
              ) d (bbphis $ (progbbid2bb p) !!# bbidto)
    else return d


setSetParamDimension :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id -- ^ dimension to be restricted
    -> Int -- ^ value to restrict to
    -> Ptr Set
    -> IO (Ptr Set)
setSetParamDimension ctx id2isl id val s = do
    let islid = id2isl OM.! id
    putDocW 80 $ pretty "---\n"
    putDocW 80  $ pretty "id: " <> pretty id <> pretty "\n"
    putDocW 80  $ pretty "islid: " <> pretty islid <> pretty "\n"
    putDocW 80  $ pretty "s: " <> pretty s <> pretty "\n"
    putDocW 80 $ pretty "---\n"
    Just ix <- findDimById s IslDimSet islid

    c <- getSpace s >>= localSpaceFromSpace >>= 
        constraintAllocEquality 
    c <- constraintSetCoefficient c IslDimSet ix 1
    c <- constraintSetConstant c val
    s <-  setAddConstraint s c
    return s

pwaffSetParamDimension :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id -- ^ dimension to be restricted
    -> Int -- ^ value to restrict to
    -> Ptr Pwaff
    -> IO (Ptr Pwaff)
pwaffSetParamDimension ctx id2isl id val pw = do
    s <- pwaffCopy pw >>= 
        pwaffGetDomainSpace >>= 
        setUniverse >>= 
        setSetParamDimension ctx id2isl id val

    pw <- pwaffIntersectDomain pw s
    return pw
    

-- | Restrict values from the left to a phi on a forward edge
absdomTransferOnLoopEnter :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> (BBId, BBId) -- ^ Edge
    -> AbsDomain -- ^ current conditions
    -> IO AbsDomain
absdomTransferOnLoopEnter ctx id2isl p (bbidfrom, bbidto) d = do
    if isEdgeEnteringLoop p (bbidfrom, bbidto)
    then do
        let nl = progbbid2nl p !!# bbidto
        let lid = id2isl OM.! (nl2loopid nl)
        d <- foldM (\d phi -> do
                let vidl = snd . phil  $ phi
                pw <- pwaffCopy $ absdomGetVal d vidl
                pw <- pwaffSetParamDimension ctx id2isl (nl2loopid nl) 0 pw
                d <- absdomUnionVal (phiid phi) pw d

                s <-  setSetParamDimension ctx id2isl (nl2loopid nl) 0 (absdomGetBB bbidto d)
                d <- absdomIntersectBB bbidto s d 
                return d

              ) d (bbphis $ (progbbid2bb p) !!# bbidto)
        -- putDocW 80 $ pretty "===\ntransfer on loop enter (" <> 
        --     pretty bbidfrom <> pretty "->" <> pretty bbidto <> pretty ")\n"  <> 
        --     pretty d <> pretty "\n===\n"
        return d
    else return d

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
    d <- absdomainCopy d >>= absdomRestrictValDomains s
    d <- absdomUnionBB bb' s d
    d <- absdomTransferOnLoopEnter ctx id2isl p (bb, bb') d
    d <- absdomTransferOnLoopBackedge ctx id2isl p (bb, bb') d
    return [(bb', d)]

abstransterm ctx id2isl p bb (BrCond _ c bbl bbr) d = do
    let dbb  = absdomGetBB bb d
    d <- absdomainCopy d

    -- true = -1
    vc <- pwaffCopy $ absdomGetVal d c
    setcTrue <- (pwConst ctx id2isl (-1)) >>= pwaffEqSet vc 
    setcTrue <- setCopy dbb >>= \dbb -> setcTrue `setIntersect` dbb
    -- setcTrue <- edgeConstrainOnLoopEnter  ctx id2isl p (bb, bbl) setcTrue

    vc <- pwaffCopy $ absdomGetVal d c
    setcFalse <- (pwConst ctx id2isl (0)) >>= pwaffEqSet vc 
    setcFalse <- setCopy dbb >>= \dbb -> setcFalse `setIntersect` dbb
    -- setcFalse <- edgeConstrainOnLoopEnter  ctx id2isl p (bb, bbr) setcFalse

    -- domr <- setCopy $ absdomGetBB bbr d
    dtrue <- absdomainCopy d >>= absdomRestrictValDomains setcTrue
    dtrue <- absdomUnionBB  bbl setcTrue dtrue
    dtrue <- absdomTransferOnLoopEnter ctx id2isl p (bb, bbl) dtrue
    dtrue <- absdomTransferOnLoopBackedge ctx id2isl p (bb, bbl) dtrue

    dfalse <- absdomainCopy d >>= absdomRestrictValDomains setcFalse
    dfalse <- absdomUnionBB  bbr setcFalse dfalse
    dfalse <- absdomTransferOnLoopEnter ctx id2isl p (bb, bbr) dfalse
    dfalse <- absdomTransferOnLoopBackedge ctx id2isl p (bb, bbr) dfalse

    -- putDocW 80 $ pretty "\n====\nAbstransterm" <> 
    --     pretty (bb, bbl, bbr) <> pretty "\n" <>
    --     pretty "true:\n" <> pretty dtrue <> pretty "\n----\n" <>
    --     pretty "false:\n" <> pretty dfalse <> 
    --     pretty "\ndbb: " <> pretty dbb <> pretty "\n" <>
    --     pretty "\n=====\n"

    return $ [(bbl, dtrue), (bbr, dfalse)]

-- | take a disjoin union of two pwaffs
-- | Take, Take -> Give
pwaffUnion :: Ptr Pwaff -> Ptr Pwaff -> IO (Ptr Pwaff)
pwaffUnion pl pr = do
    dl <- pwaffCopy pl >>= pwaffDomain 
    dr <- pwaffCopy pr >>= pwaffDomain 
    dcommon <- setCopy dl >>= \dl -> setCopy dr >>= \dr -> setIntersect dl dr
    deq <- pwaffCopy pl >>= \pl -> pwaffCopy pr >>= \pr -> pwaffEqSet pl pr

    Just commonSubsetEq <- setIsSubset dcommon deq
    Just commonEqualEq <- setIsEqual dcommon deq

    
    if commonSubsetEq
    then  do
        pl <- pwaffCopy pl
        pr <- pwaffCopy pr
        pwaffUnionMax pl pr
    else do 
        dneq <- setCopy deq >>= setComplement 
        putDocW 80 $ vcat $ 
            [pretty "\n---"
            , pretty "pl: " <> pretty pl
            , pretty "dl: " <> pretty dl
            , pretty "pr: " <> pretty pr
            , pretty "-----"
            , pretty "dr: " <> pretty dr
            , pretty "dcommon: " <> pretty dcommon
            , pretty "deq: " <> pretty deq
            , pretty "dNEQ: " <> pretty dneq
            , pretty "commonEqualEq: " <> pretty commonEqualEq
            , pretty "commonSubsetEq: " <> pretty commonSubsetEq
            , pretty "---\n"]
        error $ "pwaffs are not equal on common domain"


    
-- | Abstract interpret phi nodes
abstransphi :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    -> Program 
    -> Phi 
    -> AbsDomain
    -> IO AbsDomain
abstransphi cx id2isl p phi d = do
    case (phity phi) of
        Philoop -> return d
        Phicond -> do
            let idl =  snd . phil $ phi
            let idr =  snd . phir $ phi
            -- domain from the left hand
            vl <- pwaffCopy $ absdomGetVal d idl 
            vr <- pwaffCopy $ absdomGetVal d idr 

            v <- (pwaffUnion vl vr)
            absdomUnionVal (phiid phi) v d


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

    -- first abstract interpret each phi, forwarding the data
    -- as expected
    -- TODO: remove redundancy in code between phi and assign
    l2d <- foldM 
        (\l2d phi -> do
            -- state is the state that is on top
            let d = loc2dget l2d (bbGetPrevLoc bb phi)
            d' <- abstransphi ctx id2isl p phi d
            putStrLn "before phi fold"
            l2d <- loc2dUnion phi d' l2d
            putStrLn "after phi fold"
            return l2d
        ) l2d (bbphis bb)

    -- now abstract interpret each instruction, forwarding the
    -- data as expected
    l2d <- foldM 
        (\l2d a -> do
            let d = loc2dget l2d (bbGetPrevLoc bb a)
            let bbdom = absdomGetBB (bbid bb) d
            let dAtAssign = loc2dgetmaybe l2d a
            d' <- abstransassign ctx id2isl p bbdom a d
            -- set the value at the next location
            putStrLn "before assign fold"
            putDocW 80 $ pretty "----\n"
            putDocW 80 $ pretty d <> pretty "\n"
            putDocW 80 $ pretty "\n********" <> pretty a <> pretty "*******\n"
            putDocW 80 $ pretty d' <> pretty "\n"
            putDocW 80 $ pretty "*** Old: ***\n"
            putDocW 80 $ pretty dAtAssign
            putDocW 80 $ pretty "\n----"
            l2d <- loc2dUnion a d' l2d
            putStrLn "after assign fold"
            return l2d
        ) l2d (bbinsts bb)


    -- | now abstract interpret the terminator, updating
    -- | the states of everyone after us.
    let t = bbterm bb
    bbid2d <- abstransterm ctx id2isl p (bbid bb) t (loc2dget l2d (bbGetPrevLoc bb t))
    l2d <- foldM (\l2d (bbid', d) -> do
        let bbid2bb = progbbid2bb p
        let bb' = bbid2bb !!# bbid'
        -- update at the location of the next bb
        putStrLn "before term fold"
        l2d <- loc2dUnion (bbloc bb') d l2d 
        putStrLn "after term fold"
        return l2d
        ) l2d bbid2d
        
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
     putDocW 80 (pretty dmempty)

     l2d <- loc2dinit (Loc (-1)) dmempty
     l2ds <- repeatTillFixDebugTraceM 2 (==) (absint_ ctx id2isl p dmempty) l2d
     -- forM_ l2ds (\l2d -> putDocW 80 $  pretty "\n==\n" <> pretty l2d <> pretty "==\n")
     return $ last l2ds


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

    putStrLn "***program***"
    putDocW 80 (pretty p)
    putStrLn ""

-- | Default environment we start with
edefault :: Env Int
edefault = envFromParamList [(Id "p", 1)]

programs :: [(Program, Env Int)]
programs = [-- (passign, edefault)
            -- (pif, edefault)
            (ploop, edefault)
           ] 

-- | Main entry point that executes all programs
main :: IO ()
main = for_ programs (\(p, e) -> do
    runProgram  p e
    putStrLn "\n=========================")

