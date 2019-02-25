module Collectingsem where
import IR
import Util
import Lattice
import Opsem
import Data.Text.Prettyprint.Doc
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromJust)

-- Collecting semantics
-- ====================

mapVenvEnv :: (VEnv a -> VEnv a) -> Env a -> Env a
mapVenvEnv f (Env ve le pc) = Env (f ve) le pc

mapLEnvEnv :: (LEnv -> LEnv) -> Env a -> Env a
mapLEnvEnv f (Env ve le pc) = Env ve (f le) pc

-- update the environment at the location
updateEnvCollecting :: Ord a => Pretty a => 
  Loc 
  -> (Env a -> Env a) 
  -> Collecting a -> Collecting a
updateEnvCollecting loc f csem = 
  let envs = csem !!# loc 
      envs' = S.map f envs in
      M.insert loc envs' csem

-- This unions the collection of environments at a point
mapEnvCollecting :: Ord a => Pretty a =>
                    Loc 
                 -> Loc 
                 -> (Env a -> Env a) 
                 -> Collecting a -> Collecting a
mapEnvCollecting loc loc' f csem = 
  let envs = csem !!# loc 
      envs' = S.map f envs in
      M.adjust (`S.union` envs') loc' csem



instExecCollecting :: Ord a => Pretty a =>
                     (Expr -> VEnv a -> a) 
                   -> Assign 
                   -> Loc -- loc to pull from
                   -> Collecting a -> Collecting a
instExecCollecting exprsem inst loc csem = 
  mapEnvCollecting loc (location inst)
    (mapVenvEnv (mkSemInst exprsem inst)) csem

termExecCollecting :: Ord a => Pretty a => (a -> Maybe Bool) 
                   -> Term 
                   -> Loc
                   -> BBId  -- current BBId
                   -> Collecting a -> Collecting a
termExecCollecting sempred term loc curbbid csem = let
  -- envMap :: Env a -> Env a
  envMap (Env venv lenv pc) = 
    (Env venv lenv (mkSemTerm sempred term curbbid venv))
 in mapEnvCollecting loc (location term) envMap csem

setCatMaybes :: Ord a => S.Set (Maybe a) -> S.Set a
setCatMaybes s = S.map fromJust $ S.filter (/= Nothing) s


-- update the loop environment given the terminator PC status in the next basic block:w
lenvUpdate :: M.Map BBId NaturalLoop 
           -> PC -- pc of the terminator instruction
           -> LEnv -> LEnv
lenvUpdate bbid2nl (PCNext prevbbid nextbbid) lenv = 
  case fmap (nlContainsBB prevbbid) (bbid2nl M.!? nextbbid) of
    Just True -> M.adjust (+1) nextbbid lenv
    Just False -> M.insert nextbbid 0 lenv
    Nothing -> lenv

-- at term: [PCNext loop loop, PCNext loop exit]
-- copy data from term into  loop and exit
-- copy data from loop into loop, copy data from entry into loop
-- TODO: refactor this, this is ugly as sin.
flowIntoBBExecCollecting :: Ord a => Pretty a => 
  Loc  --  location of terminator to pull from
  -> M.Map BBId NaturalLoop
  -> M.Map BBId Loc  -- map from BB ids to locations
  -> Collecting a 
  -> Collecting a
flowIntoBBExecCollecting loc bbid2nl bbid2loc csem = 
  let -- tocopy :: S.Set (Env a)
      tocopy = csem !!# loc

      -- targets :: S.Set (Maybe (Env a, Loc))
      targets = S.map (\env@(Env venv lenv pc) -> case pc of
                                            PCNext _ nextbbid -> Just (Env venv (lenvUpdate bbid2nl pc lenv) pc, bbid2loc !!# nextbbid)
                                            _ -> Nothing) tocopy

      -- targets' :: S.Set (Env a, Loc)
      targets' = setCatMaybes targets

      -- updateEnv :: Collecting a -> (Env a, Loc) -> Collecting a
      updateEnv csem (env, loc) = M.adjust (`S.union` (S.singleton env)) loc csem

  in foldl updateEnv csem targets'




phiExecCollecting :: Ord a => Pretty a => 
                     Phi 
                  -> Loc 
                  -> Collecting a 
                  -> Collecting a 
phiExecCollecting phi loc csem = 
  let
    -- f :: Env a -> Env a
    f env@(Env venv lenv (PCNext prevbbid _)) = mapVenvEnv (mkSemPhi phi prevbbid) env
    f env@(Env venv lenv PCDone) = env
  in 
   mapEnvCollecting loc (location phi) f  csem



bbExecCollecting :: Ord a => Pretty a => Semantics a 
                 -> M.Map BBId NaturalLoop
                 -> M.Map BBId Loc
                 -> BB 
                 -> Collecting a -> Collecting a
bbExecCollecting sem bbid2nl bbid2loc bb csem = let
  -- bb -> phis
  (locphis, csemphis) = 
    foldl (\(loc, csem) phi -> (location phi, phiExecCollecting phi loc csem)) 
      (location bb, csem) (bbphis bb)

  -- prev inst -> inst
  (locinsts, cseminsts) = 
    foldl (\(loc, csem) inst -> (location inst, instExecCollecting (semExpr sem) inst loc csem)) 
      (locphis, csemphis) (bbinsts bb)

  -- last inst -> term
  csemterm = termExecCollecting (semPredicate sem) (bbterm bb) locinsts (bbid bb) cseminsts

  -- term -> next bb
  csemflow = flowIntoBBExecCollecting (location (bbterm bb)) bbid2nl bbid2loc csemterm

  -- next bb -> next bb lenv counter
  -- csemupdatenext = bbUpdateLenvCollecting bbid2nl bbid2loc bb csemflow

  in csemflow
  


programExecCollecting :: Ord a => Pretty a => Semantics a -> Program -> Collecting a -> Collecting a
programExecCollecting sem p@(Program _ bbs) csem = 
  let bbid2loc = M.map bbloc (programBBId2BB p) 
      bbid2nl = programBBId2nl p
   in foldl (\csem bb -> bbExecCollecting sem bbid2nl bbid2loc bb csem) csem bbs


programFixCollecting :: (Eq a, Ord a, Pretty a, Pretty a) => 
  Semantics a -> Program -> Collecting a -> Collecting a
programFixCollecting sem p csem = 
  repeatTillFix (programExecCollecting sem p) csem

