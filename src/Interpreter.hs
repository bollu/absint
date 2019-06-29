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
-- READ DATA FROM!

module Interpreter where
import Lattice
import IR
import Control.Monad(guard)
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
data AI a = AI {
  -- | interpret an expression node
  aiE :: Expr -> AbsDom a -> a
  -- | interpret a terminator node
  , aiT :: Term -- ^ terminator instruction
      -> BBId  -- ^  bbid of successor
      -> AbsDom a -- ^ abstract domain to use
      -> a
}


-- | Given an update using the abstract domain
-- at a given point, update the full abstract state
-- TODO, BUG: we should use the *previous* location here
updateLoc :: Lattice a => (AbsDom a -> a) -> Loc -> Id -> AbsState a -> AbsState a
updateLoc f l i s =
  let d = s #! l
      v = f d
      d' = lmInsert i v d
  in lmInsert (locincr l) d' s

-- | Abstract interpret an assignment
aiAssign :: Lattice a => AI a ->  Assign -> AbsState a -> AbsState a
aiAssign AI{..} (Assign l id e) = updateLoc (aiE e) l id


-- | Abstract intepret  a phi node
-- TODO, BUG: Phi should probably just project out data
-- from the BB and copy it. Actually, phi can also just
-- be identity.
aiPhi :: Lattice a => Phi -> M.Map BBId BB -> AbsState a -> AbsState a
aiPhi _ _ s = s
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

aiTerm :: Lattice a => AI a -> Term -> M.Map BBId BB ->
    AbsState a -> AbsState a
aiTerm AI{..} term bbid2bb s =
    let d = s #! (location term)
        -- | M.Map BBId Loc
        bbid2loc = M.map location bbid2bb
        -- | AbsState a -> BBId -> AbsState a
        -- Update the state of the successor BBId
        aiSucc s bbid =
            let -- | current state
                d = s #! (location term)
                d' = lmInsert bbid (aiT term bbid d) d
                lbb = bbid2loc M.! bbid
            in lmInsert lbb d' s

    in foldl aiSucc s (termnextbbs term)

-- | for a basic block, get the final abstract domain value
bbFinalAbsdom :: Lattice a => AbsState a -> BB -> AbsDom a
bbFinalAbsdom s bb  = s #! (bbFinalLoc bb)

-- | Merge the state from predecrssors into a BB
aiMergeBB :: Lattice a => BB -> M.Map BBId BB -> AbsState a -> AbsState a
aiMergeBB bb bbid2bb s =
    -- | gather predecessors
    -- bbps :: [BB]
    let bbps = preds bbid2bb bb
        -- | Gather abstract domains at the end of the predecessors
        -- ds :: [AbsDom a]
        ds = map (bbFinalAbsdom s) bbps
        -- | Union all previous abstract domains
        d' = unLUnion . mconcat $ (map LUnion ds)
    in lmInsert (location bb) d' s

-- | Abstract interpret a basic block
aiBB :: Lattice a => AI a
    -> BB
    -> M.Map BBId BB -> AbsState a -> AbsState a
aiBB ai bb bbid2bb s =
    let sbb = aiMergeBB bb bbid2bb s
        si = foldl (\s a -> aiAssign ai a s) sbb (bbinsts bb)
        st = aiTerm ai (bbterm bb) bbid2bb  si
    in st

-- | Abstract interpret the whole program once.
aiProgramOnce :: Lattice a => AI a -> Program -> AbsState a -> AbsState a
aiProgramOnce ai p s =
 let bbs = progbbs p
     bbid2bb = progbbid2bb p
 in foldl (\s bb -> aiBB ai bb bbid2bb s) s bbs

-- | Run AI N times, or till fixpoint is reached, whichever is earlier
aiProgramN :: (Eq a, Lattice a) => Int  -- ^ times to run
           -> AI a
           -> Program
           -> AbsState a
           -> AbsState a
aiProgramN 0 _ _ s = s
aiProgramN n ai p s =
  let s' =  aiProgramOnce ai p s
  in if s == s' then s' else aiProgramN (n-1) ai p s'

-- | perform AI till fixpoint
aiProgramFix :: (Lattice a, Eq a) => AI a ->
    Program -> AbsState a -> AbsState a
aiProgramFix ai p s =
    let s' = aiProgramOnce ai p s
     in if s == s' then s' else aiProgramOnce ai p s'

