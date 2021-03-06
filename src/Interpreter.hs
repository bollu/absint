{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE KindSignatures #-}
-- This module contains an implementation of a general abstract interpret
-- which works for any abstract domain
-- INVARIANTS:
-- if we have instructions:
-- l0: i0
-- l1: i1
-- l2: ...


-- l0 -> i0 -> l1
-- l1 -> i1 -> l2

-- that is, THE LOCATION FOR AN INSTRUCTION IS WHERE IT WILL
-- WRITE DATA TO!

module Interpreter where
import Lattice
import IR
import Control.Monad(guard, forM, foldM)
import qualified Data.Map as M


-- | An abstract state maps each location to abstract
-- domains
-- at each location, identifiers to values.
type AbsState d = LatticeMap Loc d

-- | Data needed to perform abstract interpretation
-- a: abstract value
-- d: abstract domain
data AI (m :: * -> *) d  = AI {
  -- | interpret an assignment
 aiA :: Assign -> d -> m d
  -- | interpret a terminator node
  , aiT :: Term -- ^ terminator instruction
      -> BBId  -- ^  bbid of successor
      -> d -- ^ abstract domain to use
      -> m d
  , aiPhiCond :: Phi -> d -> m d
   -- | Transform a loop phi node.
  , aiPhiLoop :: Phi -> d  -> m d
  , aiStartState :: m d -- ^ Starting state of the AI
}

    {-
-- | Given an update using the abstract domain
-- at a given point, update the full abstract state
-- TODO, BUG: we should use the *previous* location here
updateLoc :: Monad m => Lattice m a => Lattice m (d a) =>
    Loc -- ^ previous location
    -> Loc -- ^ current location
    -> Id -- ^ identifier to update
    -> AbsState d a -- ^ previous abstract state
    -> (d a -> m a) -- ^ update value
    -> m  (Loc, AbsState d a)
updateLoc lprev lcur i s f = do
  d <- s #! lprev
  v <- f d
  d' <- lmInsert i v d
  s' <- lmInsert lcur d' s
  return $ (lcur, s')
  -}

runTransferFunction :: Lattice m d
                    => Monad m
                    => Loc  -- ^ previous location to read
                    -> Loc  -- ^ current location to write
                    -> (d -> m d) -- ^ transfer function
                    -> AbsState d -- ^ abstract state to update
                    -> m (Loc, AbsState d) -- ^ (current loc, new abstract state)
runTransferFunction lprev lcur f s = do
    d <- s #! lprev
    d' <- f d
    s' <- lmInsert lcur d' s
    return (lcur, s')

-- | Abstract interpret an assignment. Return current location
-- and new state
aiAssign :: Monad m => Lattice m d => AI m d
         -> Loc -- ^ previous location
         -> Assign -> AbsState d -> m (Loc, AbsState d)
aiAssign AI{..} lprev a s = runTransferFunction lprev (location a) (aiA a) s


aiPhi :: (Monad m, Lattice m d) => AI m d
  -> Loc -- ^ previous location
  -> Phi -- ^ phinode
  -> M.Map BBId BB
  -> AbsState d
  -> m (Loc, AbsState d)
aiPhi AI{..} lprev phi bbid2bb s =
    let f = case phity phi of
                     Phicond -> aiPhiCond phi
                     Philoop -> aiPhiLoop phi
    in runTransferFunction lprev (location phi) f s

-- | Get the predecessors of a given BB
preds :: M.Map BBId BB -> BB -> [BB]
preds bbid2bb bbcur = do
    bbpred <- (M.elems bbid2bb)
    guard $ (bbid bbcur) `elem`  (termnextbbs . bbterm $ bbpred)
    return $ bbpred

aiTerm :: Monad m => Lattice m d => AI m d
       -> Loc
       -> Term
       -> AbsState d
       -> m (AbsState d)
aiTerm AI{..} lprev term s = do
   dinit <- s #! lprev
   -- | AbsDom a -> BBId -> AbsDom a
   -- Update the state of the successor BBId
   let runT d bbid =  (aiT term bbid d)

  -- | run the terminator on each of the successors and union them all.
   d' <- foldM runT dinit (termnextbbs term)

   -- lmInsert lbb d' s
   lmInsert (location term) d' s

-- | for a basic block, get the final abstract domain value
bbFinalAbsdom :: Monad m => Lattice m d => AbsState d
  -> BB -> m d
bbFinalAbsdom s bb = s #! (bbFinalLoc bb)

-- | Merge the state from predecrssors into a BB
aiMergeBB :: Monad m => Lattice m d =>
    BB -> M.Map BBId BB -> AbsState d -> m (AbsState d)
aiMergeBB bb bbid2bb s = do
    -- | gather predecessors
    -- bbps :: [BB]
    let bbps = preds bbid2bb bb
    -- | Gather abstract domains at the end of the predecessors
    -- ds :: [AbsDom a]
    ds <- forM bbps (bbFinalAbsdom s)
    -- | Union all previous abstract domains
    d' <- unLUnion . mconcat $ (map (LUnion . return) ds)

    s' <- lmInsert (location bb) d' s
    return $ s'

-- | Abstract interpret a basic block
-- Note that special handling is needed for the entry block.
aiBB :: Monad m => Lattice m d => AI m d
    -> BBId -- ^ bbid of entry
    -> BB -- ^ BB to interpret
    -> M.Map BBId BB -> AbsState d -> m (AbsState d)
aiBB ai entryid bb bbid2bb sinit = do
    sbb <-  if bbid bb == entryid
            then return sinit
            else aiMergeBB bb bbid2bb sinit

    (lprev, sphi) <- foldM (\(lprev, s) phi ->
                     (aiPhi ai lprev phi bbid2bb s))
                   (location bb, sbb) (bbphis bb)

    (lprev, si) <- foldM (\(lprev, s) a ->
                     (aiAssign ai lprev a s))
                   (lprev, sphi) (bbinsts bb)
    let bbid2loc = M.map location bbid2bb
    st <- aiTerm ai lprev (bbterm bb)  si
    return $ st


-- | Create the abstract state with the initial abstract domain at the
-- program entry location and bottom everywhere else
mkEntryAbsState :: Program -> d -> AbsState d
mkEntryAbsState p d = lmsingleton (progEntryLoc p) d

-- | Abstract interpret the whole program once.
aiProgramOnce :: Monad m => Lattice m d => AI m d
  -> Program -> AbsState d -> m (AbsState d)
aiProgramOnce ai p sinit = do
  let bbs = progbbs p
  let entryid = progEntryId p
  let bbid2bb = progbbid2bb p
  foldM (\s bb -> aiBB ai entryid bb bbid2bb s) sinit bbs

-- | Run AI N times, or till fixpoint is reached, whichever is earlier
aiProgramN :: (Monad m, Eq d, Lattice m d) => Int  -- ^ times to run
           -> AI m d
           -> Program
           -> AbsState d
           -> m (AbsState d)
aiProgramN 0 _ _ s = return s
aiProgramN n ai p s = do
  s' <-  aiProgramOnce ai p s
  if s == s'
  then return s'
  else aiProgramN (n-1) ai p s'

-- | perform AI till fixpoint
aiProgramFix :: (Monad m, Lattice m d, Eq d) => AI m d ->
    Program -> AbsState d -> m (AbsState d)
aiProgramFix ai p s = do
   s' <- aiProgramOnce ai p s
   if s == s' then return s' else aiProgramOnce ai p s'


-- | Run AI N times, or till fixpoint is reached, and return
-- the entire trace. Returns iterations in ascending order.
-- head = 0th iteration
-- last = nth iteration
-- Usually invoked as (aiProgramTraceN 100 ai p (aiStartState ai))
aiProgramNTrace :: (Monad m, Eq d, Lattice m d)
                => Int  -- ^ times to run
                -> AI m d
                -> Program
                -> AbsState d
                -> m [AbsState d]
aiProgramNTrace 0 _ _ s = return [s]
aiProgramNTrace n ai p s = do
  s' <-  aiProgramOnce ai p s
  if s == s'
  then return [s']
  else do
      ss <- aiProgramNTrace (n-1) ai p s'
      return $ ss ++ [s']

