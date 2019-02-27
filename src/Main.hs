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
newtype Absint = Absint (M.Map Loc AbsDomain)

-- | Abstract domain model
data AbsDomain = AbsDomain {
    absdomval :: M.Map Id (Ptr Pwaff),
    absdomedge :: (M.Map (BBId, BBId) (Ptr Set)),
    absdombb :: M.Map BBId (Ptr Set)
} deriving(Show)

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
absintexpr :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id
    -> Expr
    -> AbsDomain
    -> IO (Ptr Pwaff)
absintexpr ctx id2isl id (EId id') absdom = pwaffCopy (absdomGetVal absdom id')

absintexpr ctx id2isl _ (EInt i) _ = pwConst ctx id2isl i

absintexpr ctx id2isl _ (EBinop Add id1 id2) absdom = do
    pw1 <- pwaffCopy $ absdomGetVal absdom id1
    pw2 <- pwaffCopy $ absdomGetVal absdom id2
    pwaffAdd pw1 pw2


absintexpr ctx id2isl _ (EBinop Lt id1 id2) absdom = do
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
absintassign :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> Ptr Set -- ^ Take, Conditions under which this assignment is active
    -> Assign
    -> AbsDomain
    -> IO AbsDomain
absintassign ctx id2isl p dom a d = do
    let e = assignexpr a
    let id = assignid a

    dom <- setCopy dom
    pwaff <- absintexpr ctx id2isl id e d 
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
            putDocW 80 (pretty "#NATURAL LOOP: " <> pretty nl <> pretty "\n")
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
absintterm :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> BBId -- ^ Current BBId
    -> Term
    -> AbsDomain
    -> IO AbsDomain
absintterm ctx id2isl p _ (Done _) d = return d
absintterm ctx id2isl p bb (Br _ bb') d = do
    let s = absdomGetBB bb d
    s <- edgeConstrainOnLoopEnter ctx id2isl p bb' s
    d <- setCopy s >>= \s -> absdomUnionEdge bb bb' s d
    d <- setCopy s >>= \s -> absdomUnionBB bb' s d
    putDocW 80 (pretty "\n\n" <> pretty d <> pretty "\n\n")
    return d

absintterm ctx id2isl p bb (BrCond _ c bbl bbr) d = do
    vc <- pwaffCopy $ absdomGetVal d c
    let dbb  = absdomGetBB bb d

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

    return d

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
            [pretty "pl: " <> pretty pl <> pretty "| dl: " <> pretty dl
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
absintphi :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    -> Program 
    -> Phi 
    -> AbsDomain 
    -> IO AbsDomain
absintphi cx id2isl p phi d = do
    pl <-  pwaffCopy $ absdomGetVal d (snd . phil $ phi)
    pr <-  pwaffCopy $ absdomGetVal d (snd . phir $ phi)
    pwaff <- pwaffUnion pl pr
    return $ absdomSetVal (phiid phi) pwaff d


-- | Abstract interpret basic blocks
absintbb :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    -> Program 
    -> BB 
    -> AbsDomain 
    -> IO AbsDomain
absintbb ctx id2isl p bb d = do
    -- let dphi = d
    d <- foldM 
        (\d phi -> absintphi ctx id2isl p phi d) d (bbphis bb)
    d <- foldM 
        (\d a -> let dom = absdomGetBB (bbid bb) d in
            absintassign ctx id2isl p dom a d) d (bbinsts bb)
    d <- absintterm ctx id2isl p (bbid bb) (bbterm bb) d
    return d


    
-- perform the abstract interpretation for one iteration
absint_ :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program 
    -> AbsDomain 
    -> IO AbsDomain
absint_ ctx id2isl p d = do
    foldM (\d bb -> absintbb ctx id2isl p bb d) d (progbbs p)
    

absint :: Program -> IO AbsDomain
absint p = do
     (ctx, id2isl) <- newISLState p
     d <- absDomainStart ctx id2isl p
     absint_ ctx id2isl p d


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
            , (ploop, edefault)] 

-- | Main entry point that executes all programs
main :: IO ()
main = for_ programs (\(p, e) -> do
    runProgram  p e
    putStrLn "\n=========================")

