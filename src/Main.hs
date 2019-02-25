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


data AbsDomain = 
    AbsDomain (M.Map Id (Ptr Pwaff)) (LatticeMap (BBId, BBId) (Ptr Set))
    deriving(Show)

getAbsdomAtVid :: AbsDomain -> Id -> (Ptr Pwaff)
getAbsdomAtVid (AbsDomain id2pwaff _) id = id2pwaff !!# id

absdomSetVid :: Id -> Ptr Pwaff -> AbsDomain -> AbsDomain
absdomSetVid id pwaff (AbsDomain id2pwaff edge2bb) = 
    AbsDomain (M.insert id pwaff id2pwaff) edge2bb


instance Pretty AbsDomain where
    pretty (AbsDomain id2pwaff edge2set) = 
        vcat [pretty id2pwaff, pretty edge2set]


-- Create the set space common to all functions in the abstract domain
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
    let ids = S.toList (progids p)
    islids <- OM.fromList  <$> for ids (\id -> (id, ) <$> idAlloc ctx (show id))

    return $ (ctx, islids)

pwVar :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Id -> IO (Ptr Pwaff)
pwVar ctx id2isl id = do
  ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace
  Just ix <- findDimById ls IslDimSet (id2isl OM.! id)
  affVarOnDomain ls IslDimSet ix >>= pwaffFromAff

-- Initial abstract domain
absDomainStart :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    ->  Program 
    -> IO AbsDomain
absDomainStart ctx id2isl p = do
    id2pwnan <- M.fromList <$> 
        for (S.toList (progids p))
            (\id -> (pwVar ctx id2isl id) >>= \pw -> return (id, pw))
    let absdom = AbsDomain id2pwnan lmempty
    return $ absdom

-- Abstract interpret expressions
absintexpr :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Id
    -> Expr
    -> AbsDomain
    -> IO (Ptr Pwaff)
absintexpr ctx id2isl id (EId id') absdom = pwaffCopy (getAbsdomAtVid absdom id')

absintexpr ctx id2isl _ (EInt i) _ = do
    ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace 
    pwaffInt ctx ls i

absintexpr ctx id2isl _ (EBinop Add id1 id2) absdom = do
    pw1 <- pwaffCopy $ getAbsdomAtVid absdom id1
    pw2 <- pwaffCopy $ getAbsdomAtVid absdom id2
    pwaffAdd pw1 pw2


absintexpr ctx id2isl _ (EBinop Lt id1 id2) absdom = do
    pw1 <- pwaffCopy $ getAbsdomAtVid absdom id1
    pw2  <- pwaffCopy $ getAbsdomAtVid absdom id2
    pwaffLtSet pw1 pw2 >>= setIndicatorFunction
    

-- | Abstract interpret assignment expressions
absintassign :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> Assign
    -> AbsDomain
    -> IO AbsDomain
absintassign ctx id2isl p a d = do
    let e = assignexpr a
    let id = assignid a

    pwaff <- absintexpr ctx id2isl id e d
    return $ absdomSetVid id pwaff d

-- | Abstract interpret terminators
absintterm :: Ptr Ctx
    -> OM.OrderedMap Id (Ptr ISLTy.Id)
    -> Program
    -> Term
    -> AbsDomain
    -> IO AbsDomain
absintterm ctx id2isl p (Done _) dom = return dom



-- | Abstract interpret basic blocks
absintbb :: Ptr Ctx 
    -> OM.OrderedMap Id (Ptr ISLTy.Id) 
    -> Program 
    -> BB 
    -> AbsDomain 
    -> IO AbsDomain
absintbb ctx id2isl p bb d = do
    dassign <- foldM 
        (\d a -> absintassign ctx id2isl p a d) d (bbinsts bb) 
    dterm <- absintterm ctx id2isl p (bbterm bb) dassign
    return dterm


    
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

pLoop :: Program
pLoop = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing 
  loop <- buildNewBB "loop" (Just $ BBLoop [])
  exit <- buildNewBB "exit" Nothing

  focusBB entry
  assign "x_entry" (EInt 1)

  br loop

  focusBB exit
  done

  focusBB loop
  phi Philoop "x_loop" (entry, "x_entry") (loop, "x_next")

  assign "x_loop_lt_5" ("x_loop" <. (EInt 5))
  assign "x_next" ("x_loop" +. (EInt 1))

  condbr "x_loop_lt_5" loop exit


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

pIf :: Program
pIf = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing
  true <- buildNewBB "true" Nothing
  false <- buildNewBB "false" Nothing
  merge <- buildNewBB "merge" Nothing
  p <- param "p"

  focusBB entry
  assign "p_lt_2" $ p <. EInt 2
  condbr "p_lt_2" true false

  focusBB true
  assign "yt" (EInt 1)
  br merge

  focusBB false
  assign "yf" (EInt (-1))
  br merge

  focusBB merge
  m <- phi Phicond "m" (true, "yt") (false, "yf")
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

-- 
-- -- ========================
-- -- CHOOSE YOUR PROGRAM HERE
-- -- ========================
pcur :: Program
pcur = passign

envcur :: Env Int
envcur = envFromParamList [(Id "p", 1)]

main :: IO ()
main = do
    putStrLn "***program***"
    putDocW 80 (pretty pcur)
    putStrLn ""
    
    putStrLn "***program output***"
    let outenv =  (programExec semConcrete pcur) envcur
    print outenv

    putStrLn "***absint output***"
    absenv <- absint pcur
    putDocW 80 (pretty absenv)



mainCSem :: IO ()
mainCSem = do
    putStrLn "***collecting semantics (concrete x symbol):***"
    let cbegin = (collectingBegin pcur envcur) :: Collecting Int
    let csem = programFixCollecting semConcrete pcur cbegin
    putDocW 80 (pretty csem)

