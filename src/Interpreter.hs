{-# LANGUAGE RecordWildCards #-}
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

-- | An abstract domain is a lattice map which maps
-- identifiers to abstract values
type AbsDom a = LatticeMap Id a

-- | An abstract state maps each location to abstract
-- domains
-- at each location, identifiers to values.
type AbsState a = LatticeMap Loc (AbsDom a)

-- | Data needed to perform abstract interpretation
-- a: abstract value
data AI m a = AI {
  -- | interpret an expression node
 aiE :: Expr -> AbsDom a -> m a
  -- | interpret a terminator node
  , aiT :: Term -- ^ terminator instruction
      -> BBId  -- ^  bbid of successor
      -> AbsDom a -- ^ abstract domain to use
      -> m a
  , aiStartState :: m (AbsState a) -- ^ Starting state of the AI
}


-- | Given an update using the abstract domain
-- at a given point, update the full abstract state
-- TODO, BUG: we should use the *previous* location here
updateLoc :: Monad m => Lattice m a =>
    (AbsDom a -> m a)
    -> Loc -- ^ previous location
    -> Loc -- ^ current location
    -> Id -- ^ identifier to update
    -> AbsState a -> m (Loc, AbsState a)
updateLoc f lprev lcur i s = do
  d <- s #! lprev
  v <- f d
  d' <- lmInsert i v d
  s' <- lmInsert lcur d' s
  return $ (lcur, s')

-- | Abstract interpret an assignment. Return current location
-- and new state
aiAssign :: Monad m => Lattice m a => AI m a
         -> Loc -- ^ previous location
         -> Assign -> AbsState a -> m (Loc, AbsState a)
aiAssign AI{..} lprev (Assign lcur id e) =
    updateLoc (aiE e) lprev lcur id


-- | Abstract intepret  a phi node
-- TODO, BUG: Phi should probably just project out data
-- from the BB and copy it. Actually, phi can also just
-- be identity.
aiPhi :: (Monad m, Lattice m a) => Phi -> M.Map BBId BB -> AbsState a -> m (AbsState a)
aiPhi _ _ s = return s
{-
aiPhi phi bbid2bb s =
    let (bbidl, idl) = phil phi
        (bbidr, idr) = phir phi
        dl = s #! (bbFinalLoc (bbid2bb M.! bbidl))
        dr = s #! (bbFinalLoc (bbid2bb M.! bbidr))
    in updateLoc
         (const ((dl #! idl) `ljoin` (dr #! idr)))
         (philoc phi)
         (phiid phi)
         s
-}

-- | Get the predecessors of a given BB
preds :: M.Map BBId BB -> BB -> [BB]
preds bbid2bb bb = do
    bb' <- (M.elems bbid2bb)
    guard $ (bbid bb') `elem`  (termnextbbs . bbterm $ bb')
    return $ bb'

aiTerm :: Monad m => Lattice m a => AI m a
       -> Loc
       -> Term
       -> AbsState a
       -> m (AbsState a)
aiTerm AI{..} lprev term s = do
   dinit <- s #! lprev
   -- | AbsDom a -> BBId -> AbsDom a
   -- Update the state of the successor BBId
   let aiSucc d bbid = do
            v <- (aiT term bbid d)
            lmInsert bbid v d


   d' <- foldM aiSucc dinit (termnextbbs term)
   -- lmInsert lbb d' s
   lmInsert (location term) d' s

-- | for a basic block, get the final abstract domain value
bbFinalAbsdom :: Monad m =>Lattice m a => AbsState a -> BB -> m (AbsDom a)
bbFinalAbsdom s bb  = s #! (bbFinalLoc bb)

-- | Merge the state from predecrssors into a BB
aiMergeBB :: Monad m => Lattice m a =>
    BB -> M.Map BBId BB -> AbsState a -> m (AbsState a)
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
aiBB :: Monad m => Lattice m a => AI m a
    -> BBId -- ^ bbid of entry
    -> BB -- ^ BB to interpret
    -> M.Map BBId BB -> AbsState a -> m (AbsState a)
aiBB ai entryid bb bbid2bb s = do
    sbb <-  if bbid bb == entryid
            then aiStartState ai
            else aiMergeBB bb bbid2bb s
    (lprev, si) <- foldM (\(lprev, s) a ->
                     (aiAssign ai lprev a s))
                   (location bb, sbb) (bbinsts bb)
    let bbid2loc = M.map location bbid2bb
    st <- aiTerm ai lprev (bbterm bb)  si
    return $ st

-- | Abstract interpret the whole program once.
aiProgramOnce :: Monad m => Lattice m a => AI m a -> Program -> AbsState a -> m (AbsState a)
aiProgramOnce ai p s = do
  let bbs = progbbs p
  let entryid = progEntryId p
  let bbid2bb = progbbid2bb p
  foldM (\s bb -> aiBB ai entryid bb bbid2bb s) s bbs

-- | Run AI N times, or till fixpoint is reached, whichever is earlier
aiProgramN :: (Monad m, Eq a, Lattice m a) => Int  -- ^ times to run
           -> AI m a
           -> Program
           -> AbsState a
           -> m (AbsState a)
aiProgramN 0 _ _ s = return s
aiProgramN n ai p s = do
  s' <-  aiProgramOnce ai p s
  if s == s'
  then return s'
  else aiProgramN (n-1) ai p s'

-- | perform AI till fixpoint
aiProgramFix :: (Monad m, Lattice m a, Eq a) => AI m a ->
    Program -> AbsState a -> m (AbsState a)
aiProgramFix ai p s = do
   s' <- aiProgramOnce ai p s
   if s == s' then return s' else aiProgramOnce ai p s'


-- | Run AI N times, or till fixpoint is reached, and return
-- the entire trace. Returns iterations in ascending order.
-- head = 0th iteration
-- last = nth iteration
-- Usually invoked as (aiProgramTraceN 100 ai p (aiStartState ai))
aiProgramNTrace :: (Monad m, Eq a, Lattice m a) => Int  -- ^ times to run
           -> AI m a
           -> Program
           -> AbsState a
           -> m [AbsState a]
aiProgramNTrace 0 _ _ s = return [s]
aiProgramNTrace n ai p s = do
  s' <-  aiProgramOnce ai p s
  if s == s'
  then return [s']
  else do
      ss <- aiProgramNTrace (n-1) ai p s'
      return $ ss ++ [s']

