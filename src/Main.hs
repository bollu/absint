{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
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
import Data.Foldable 
import Data.Traversable (sequenceA)
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
import PrettyUtils (prettyableToString, docToString)
import Foreign.Ptr
import Control.Monad (foldM)
import qualified Control.Monad (join)
import qualified System.IO.Unsafe as Unsafe (unsafePerformIO)


(!!#) :: Ord k => Pretty k => Pretty v => M.Map k v -> k -> v
(!!#) m k = 
  case M.lookup k m of
    Just v -> v
    Nothing -> error . docToString $  
                pretty "missing key: " <+> pretty k <+> 
                  pretty "in map: " <+> pretty m

-- Pretty Utils
-- ============
instance Pretty a => Pretty (S.Set a) where
  pretty s = case S.toList s of
               [] -> pretty "emptyset"
               xs -> indent 1 $ vcat $ [pretty "{"] ++ (map pretty xs)  ++ [pretty "}"]

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
  pretty m = 
    if M.null m 
       then pretty "emptymap" 
       else (indent 1 (vcat $ [pretty "(" <> pretty k <+> pretty "->" <+> (pretty v) <> pretty ")" | (k, v) <- M.toList m]))

-- Lattice theory
-- ==============
-- top = join of all elements
class SemiJoin a where
  join :: a -> a -> a
  top :: a

-- bottom = meet of all elements 
class SemiMeet a where
  meet :: a -> a -> a
  bottom :: a

class (SemiJoin a, SemiMeet a) => Lattice a

instance SemiJoin a => SemiJoin (Maybe a) where
  top = Just top

  join Nothing a = a
  join a Nothing = a
  join (Just a) (Just b) = Just (join a b)

instance SemiMeet a => SemiMeet (Maybe a) where
  bottom = Nothing

  meet Nothing _ = Nothing
  meet _ Nothing = Nothing
  meet (Just a) (Just b) = Just (meet a b)

instance (SemiJoin a, SemiJoin b) => SemiJoin (a, b) where
  top = (top, top)
  join (a, b) (a', b') = (a `join` a', b `join` b')

instance (SemiMeet a, SemiMeet b) => SemiMeet (a, b) where
  bottom = (bottom, bottom)
  meet (a, b) (a', b') = (a `meet` a', b `meet` b')

instance (Lattice a, Lattice b) => Lattice (a, b)

data LiftedLattice a = LL !a | LLBot | LLTop deriving(Eq, Ord, Functor)

instance Pretty a => Pretty (LiftedLattice a) where
  pretty (LL a) = pretty a
  pretty LLBot = pretty "_|_"
  pretty LLTop = pretty "T"

instance Eq a => SemiJoin (LiftedLattice a) where
  top = LLTop

  join LLBot a = a
  join a LLBot = a
  join LLTop _ = LLTop
  join _ LLTop = LLTop
  join (LL a) (LL b) = if a == b then LL a else LLTop

instance Eq a => SemiMeet (LiftedLattice a) where
  bottom = LLBot

  meet LLBot _ = LLBot
  meet _ LLBot = LLBot
  meet a LLTop = a
  meet LLTop a = a
  meet (LL a) (LL b) = if a == b then LL a else LLBot

instance Eq a => Lattice (LiftedLattice a)



liftLL2 :: (a -> b -> c) -> LiftedLattice a -> LiftedLattice b -> LiftedLattice c
liftLL2 f LLTop _ = LLTop
liftLL2 f _ LLTop = LLTop
liftLL2 f LLBot _ = LLBot
liftLL2 f _ LLBot  = LLBot
liftLL2 f (LL a) (LL b) = LL (f a b)

instance Show a => Show (LiftedLattice a) where
  show LLBot = "_|_"
  show LLTop = "T"
  show (LL a) = show a


class Lattice a => BooleanAlgebra a where
  complement :: a -> a

-- implication in the boolean algebra
imply :: BooleanAlgebra a => a -> a -> a
imply a b = (complement a) `join` b

-- symbol
(===>) :: BooleanAlgebra a => a -> a -> a
(===>) = imply


-- Adjoin a top element 
data ToppedLattice a = TLTop | TL !a deriving (Eq, Ord, Functor)

instance Show a => Show (ToppedLattice a) where
  show TLTop = "T"
  show (TL a) = show a

data BottomedLattice a = TLBot | TB !a deriving(Eq, Ord, Functor)

instance Show a => Show (BottomedLattice a) where
  show TLBot = "_|_"
  show (TB a) = show a


-- A map based representation of a function (a -> b), which on partial
-- missing keys returns _|_
data SemiMeetMap k v = LM !(M.Map k v)  deriving (Eq, Ord, Functor)

-- Insert a regular value into a lattice map
lminsert :: Ord k => k -> v -> SemiMeetMap k v -> SemiMeetMap k v
lminsert k v (LM m) = LM $ M.insert k v m

-- pointwise produce of two lattice maps
-- If a value is missing in either lattice, put a bottom in its place
lmproduct :: (SemiMeet v, SemiMeet w, Ord k) => SemiMeetMap k v -> SemiMeetMap k w -> SemiMeetMap k (v, w)
lmproduct (LM m) (LM m') = let
  missingm' = M.mapMissing (\k w -> bottom)
  missingm =  M.mapMissing (\k v -> bottom)
  merger = M.zipWithMatched (\k tx ty -> (tx, ty))
  in LM $ M.merge missingm' missingm merger m m'

adjust :: Ord k => k -> (v -> v) -> SemiMeetMap k v -> SemiMeetMap k v
adjust k f (LM m) = LM $ M.adjust f k m

(!!#!) :: (Ord k, SemiMeet v) => SemiMeetMap k v -> k -> v
(!!#!) (LM m) k = case m M.!? k of
                   Just v -> v
                   Nothing -> bottom


(!!#?) :: Ord k => SemiMeetMap k v -> k -> Maybe v
(!!#?) (LM m) k = m M.!? k 

lmfromlist :: Ord k => [(k, v)] -> SemiMeetMap k v
lmfromlist kvs = LM $ M.fromList [(k, v) | (k, v) <- kvs]

lmempty :: SemiMeetMap k v 
lmempty = LM $ M.empty

lmtolist :: Ord k => SemiMeetMap k v -> [(k, v)]
lmtolist (LM m) = M.toList m

instance (Ord k, Show k, Show v) => Show (SemiMeetMap k v) where
  show (LM m) = show $ [(k, m M.! k) | k <- M.keys m]


instance (Ord k, Pretty k, Pretty v) => Pretty (SemiMeetMap k v) where
  pretty (LM m) =  pretty m -- vcat $ [pretty k <+> pretty "->" <+> pretty (m !!# k) | k <- M.keys m]

instance SemiMeet v => SemiMeet (SemiMeetMap k v) where
  bottom = LM M.empty
  meet _ _ = error "TODO: define meet"

-- Helper to repeat till fixpoint
-- ===============================


repeatTillFix :: (Eq a) =>  (a -> a) -> a -> a
repeatTillFix f a =
  let a' = f a in
  if a == a' then a else repeatTillFix f a'


-- repeat till fixpoint, or the max count
repeatTillFixDebug :: Eq a => Int -> (a -> a) -> a -> a
repeatTillFixDebug 0 f a = a
repeatTillFixDebug n f a = 
  let a' = f a in if a' == a then a else repeatTillFixDebug (n - 1) f a'


repeatTillFixDebugTrace :: Eq a => Int -> (a -> a) -> a -> [a]
repeatTillFixDebugTrace 0 f a = [a]
repeatTillFixDebugTrace n f a = 
  let a' = f a in if a' == a then [a] else a:repeatTillFixDebugTrace (n - 1) f a'

repeatTillFixDebugTraceM :: (Eq a, Monad m) => Int -> (a -> m a) -> a -> m [a]
repeatTillFixDebugTraceM 0 f a = return [a]
repeatTillFixDebugTraceM n f a = do
  a' <- f a
  if a == a' 
  then return [a]
  else do
    as <- repeatTillFixDebugTraceM (n - 1) f a'
    return (a' : as)


-- Program syntax
-- ==============

-- Identifiers
newtype Id = Id String deriving(Eq, Ord)
instance Show Id where
  show (Id s) = "id:" ++ s

instance Pretty Id where
  pretty (Id s) =  pretty s

-- Concrete Syntax
data Binop = Add | Lt deriving(Eq, Ord)
instance Show Binop where
  show Add = "op:+"
  show Lt = "op:<"

instance Pretty Binop where
  pretty Add = pretty "+."
  pretty Lt = pretty "<."

data Expr = EInt !Int | EBool !Bool  | EBinop !Binop !Expr !Expr | EId Id
  deriving(Eq, Ord)

instance Show Expr where
    show (EInt i) = show i
    show (EBool b) = show b
    show (EId id) = show id
    show (EBinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Pretty Expr where
  pretty (EInt i) = pretty i
  pretty (EBool b) = pretty b
  pretty (EId id) = pretty id
  pretty (EBinop op e1 e2) = parens $  pretty e1 <+> pretty op <+> pretty e2


-- Program counter
data Loc = Loc { unLoc :: !Int } deriving(Eq, Ord)

instance Show Loc where
  show (Loc pc) = "loc:" ++ show pc

instance Pretty Loc where
  pretty = pretty . show

locincr :: Loc -> Loc
locincr (Loc i) = Loc (i + 1)

pcinit :: Loc
pcinit = Loc 0

class Located a where
  location :: a -> Loc

data BBId = BBId String deriving(Eq, Ord, Show)
instance Pretty BBId where
  pretty (BBId id) = pretty id

-- Instructions
data Inst = Assign !Loc !Id !Expr  deriving(Eq, Ord, Show)
instance Pretty Inst where
  pretty (Assign pc id expr) =
    pretty pc <+> pretty id <+> equals <+> pretty expr

instance Located Inst where
  location (Assign loc _ _) = loc

-- Phi nodes
data Phi = Phi !Loc Id (BBId, Id) (BBId, Id) deriving(Eq, Ord, Show)

instance Located Phi where
  location (Phi loc _ _ _) = loc

instance Pretty Phi where
  pretty (Phi pc id l r) =
    pretty pc <+> pretty "phi" <+> 
      pretty id <+> equals <+> pretty l <+> pretty r

-- Terminator instruction
data Term = Br !Loc BBId 
          | BrCond !Loc Id BBId BBId 
          | Done !Loc deriving(Eq, Ord, Show)

instance Located Term where
  location (Br loc _) = loc
  location (BrCond loc _ _ _) = loc
  location (Done loc) = loc

instance Pretty Term where
  pretty (Br pc bbid) = pretty pc <+> pretty "br" <+> pretty bbid
  pretty (BrCond pc cid bbidl bbidr) = 
    pretty pc <+> pretty "brcond" <+> 
      pretty cid <+> pretty bbidl <+> pretty bbidr
  pretty (Done loc) = pretty loc <+> pretty "done"

data BBTy = 
  BBLoop [BBId] -- if it's a loop, the list of basic blocks that are bodies of this loop
  deriving(Eq, Ord, Show)

instance Pretty BBTy where
  pretty (BBLoop bs) = pretty "bbloop"  <+> pretty bs

data BB = BB {
 bbid :: BBId,
 bbty :: Maybe BBTy,
 bbloc :: Loc,
 bbphis :: [Phi],
 bbinsts :: [Inst],
 bbterm :: Term 
}deriving(Eq, Ord, Show)

instance Pretty BB where
  pretty (BB bbid bbty bbloc phis is term) = 
    pretty bbloc <+> pretty bbid <+> pretty bbty <> line <>
      indent 4 (vcat $ (map pretty phis) ++  (map pretty is) ++ [pretty term])

instance Located BB where
  location (BB _ _ loc _ _ _) = loc


bbModifyInsts :: ([Inst] -> [Inst]) -> BB -> BB
bbModifyInsts f (BB id ty loc phis insts term) = 
  BB id ty loc phis (f insts) term 

bbModifyPhis :: ([Phi] -> [Phi]) -> BB -> BB
bbModifyPhis f (BB id ty loc phis insts term) = 
  BB id ty loc (f phis) insts term

bbModifyTerm :: (Term -> Term) -> BB -> BB
bbModifyTerm f (BB id ty loc phis insts term) = 
  BB id ty loc phis insts (f term)

-- return locations of everything in the BB
bbGetLocs :: BB -> [Loc]
bbGetLocs (BB _ _ loc phis insts term) = 
  [loc] ++ (map location phis) ++ (map location insts) ++ [location term]


-- Program is a collection of basic blocks. First basic block is the
-- entry block (block that gets executed on startup
newtype Program = Program [BB] deriving(Eq)


programMaxLoc :: Program -> Loc
programMaxLoc (Program bbs) = 
  let locs = bbs >>= bbGetLocs 
   in maximum locs

instance Pretty Program where
  pretty (Program bbs) = vcat $ map pretty bbs

-- Setup for the semantics
-- =======================

-- current basic block and location within the basic block being executed
data PC = PCEntry | PCNext BBId BBId | PCDone deriving(Eq, Ord, Show)

instance Pretty PC where
  pretty (PCEntry) = pretty "pcentry"
  pretty (PCNext bbid bbid') = 
    pretty "pcnext" <+> pretty bbid <+> pretty bbid'
  pretty (PCDone) = pretty "pcdone"

type VEnv v = M.Map Id v
-- trip count
type LEnv = M.Map BBId Int

data Env v = Env (VEnv v) LEnv PC deriving(Eq, Ord, Show)

instance Pretty v => Pretty (Env v) where
  pretty (Env venv lenv pc) = 
    pretty "Env:" <> indent 1 (vcat [pretty pc, pretty "venv: " <+> pretty venv, pretty "lenv:" <+> pretty lenv ])


envBegin :: Env v
envBegin = Env mempty mempty PCEntry

-- map variables to functions of loop trip counts
type TripCount = M.Map Id Int
type AbsVal = Ptr Pwaff
-- abstract environments
type AbsEnv = Env AbsVal
type AbsDomain = M.Map Loc AbsEnv 


-- collecting semantics in general. Map PC to a set of environments
type Collecting a = M.Map Loc (S.Set (Env a))

collectingBegin :: Ord a => Program -> Collecting a
collectingBegin p@(Program (entry:_)) = 
  let locs = map Loc [-1..(unLoc (programMaxLoc p))]
      allempty = M.fromList $ zip locs (repeat mempty)
   in M.insert (location entry) (S.singleton envBegin) allempty

-- concrete environments
type ConcreteEnv = Env Int

-- The concrete domain is the collecting semantics of the concrete environment
type ConcreteDomain  = Collecting ConcreteEnv


-- type SemExpr = Expr -> Env a -> a
-- type SemPhi = Phi -> BBId -> Env a -> Env a
-- type SemInst = Inst -> Env a -> Env a
-- type SemTerm = Term -> BBId -> Env a -> PC
-- 
-- definitino of semantics
data Semantics a = Semantics {
 semExpr :: Expr -> VEnv a -> a,
 semPredicate :: a -> Maybe Bool
}

mkSemInst :: (Expr -> VEnv a -> a) -> Inst -> VEnv a -> VEnv a
mkSemInst sem (Assign _ id e) env  = 
  M.insert id (sem e env) env

mkSemTerm :: Pretty a => (a -> Maybe Bool) -- concrete value to truth value
          -> Term
          -> BBId -- current bb id
          -> VEnv a 
          -> PC
mkSemTerm _ (Br _ bbid') bbid env = PCNext bbid bbid'

mkSemTerm judgement (BrCond _ condid bbidl bbidr) bbid env = 
  let (Just bcond) = judgement (env !!# condid) 
      bbid' =  (if bcond then  bbidl else bbidr)
   in PCNext bbid bbid'
mkSemTerm _ (Done _) _ _ = PCDone

mkSemPhi :: Pretty a => Phi 
         -> BBId  -- prevbbid
         -> VEnv a 
         -> VEnv a
mkSemPhi  p@(Phi _ id (bbidl, idl) (bbidr, idr)) prevbbid env = 
  if prevbbid == bbidl 
     then M.insert id (env !!# idl) env
     else if prevbbid == bbidr 
     then M.insert id (env !!# idr) env
     else error $ "incorrect phi: " ++ show p


envInsertOrUpdate :: Ord k => v -> (v -> v) -> k -> M.Map k v -> M.Map k v
envInsertOrUpdate v f k m = 
  case m M.!? k  of
    Just v' -> M.insert k (f v') m
    Nothing -> M.insert k v m

-- update the lenv with respect to the bb type
bbLenvUpdate :: BBId -> Maybe BBTy -> LEnv -> LEnv
bbLenvUpdate _ Nothing lenv = lenv
bbLenvUpdate bbid (Just (BBLoop _)) lenv = envInsertOrUpdate 0 (+1) bbid lenv

-- Execute a basic block
bbExec :: Pretty a => Semantics a -> BB -> Env a -> Env a
bbExec sem (BB bbid bbty _ phis insts term) (Env venv lenv pcprev) = 
  let lenvbb = bbLenvUpdate bbid bbty lenv
      venvphi = case pcprev of
                      PCNext prevbbid _ -> foldl (\venv phi -> mkSemPhi phi prevbbid venv) venv phis
                      PCEntry -> venv
                      PCDone -> error "canot have PC done and then execute a BB"
      venvinst = foldl (\venv inst -> mkSemInst (semExpr sem) inst venv) venvphi insts
      pc' = mkSemTerm (semPredicate sem) term bbid venvinst 
   in Env venvinst lenvbb pc'

-- Create a map, mapping basic block IDs to basic blocks
-- for the given program
programBBId2BB :: Program -> M.Map BBId BB
programBBId2BB (Program bbs) = 
  foldl (\m bb -> M.insert (bbid bb) bb m) M.empty bbs

programBBId2nl :: Program -> M.Map BBId NaturalLoop
programBBId2nl (Program bbs) = M.fromList $ do
  bb <- bbs
  let ty = bbty bb
  case ty of
    Just (BBLoop bodies) -> return (bbid bb, NaturalLoop (bbid bb) (S.fromList bodies))
    Nothing -> []



programExec :: Pretty a => Semantics a -> Program -> Env a -> Env a
programExec sem p@(Program bbs) env@(Env _ _ pc) = 
  let bbid2bb :: M.Map BBId BB
      bbid2bb = programBBId2BB p
  in
    case pc of
      PCDone -> env
      PCEntry -> programExec sem p $ bbExec sem (head bbs) env
      PCNext _ curbbid -> programExec sem p $ bbExec sem (bbid2bb !!# curbbid) env

-- Concrete semantics
-- ===================


-- Expression evaluation
semExprConcrete :: Expr -> VEnv Int -> Int
semExprConcrete (EInt i) _ =  i
semExprConcrete (EBool b) _ =  if b then 1 else 0
semExprConcrete (EId id) env = env !!# id
semExprConcrete (EBinop op e1 e2) env = semExprConcrete e1 env `opimpl` semExprConcrete e2 env where
  opimpl = case op of
             Add -> (+)
             Lt -> (\a b -> if a < b then 1 else 0)

semPredicateConcrete :: Int -> Maybe Bool
semPredicateConcrete 0 = Just False
semPredicateConcrete 1 = Just True
semPredicateConcrete _ = Nothing

semConcrete :: Semantics Int
semConcrete = Semantics {
  semExpr = semExprConcrete,
  semPredicate = semPredicateConcrete
}

-- Loop definitions
-- ================

data NaturalLoop = 
  NaturalLoop { nlHeader :: BBId, nlbody :: S.Set BBId } deriving(Eq, Ord, Show)

instance Pretty NaturalLoop where
  pretty (NaturalLoop header body) = 
    pretty "natural loop" <+> pretty header <+> pretty body
  
-- Return if the natural loop contains the basic block
nlContainsBB :: BBId -> NaturalLoop ->  Bool
nlContainsBB id (NaturalLoop headerid bodyids) = 
  id == headerid || id `S.member` bodyids

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
                   -> Inst 
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
programExecCollecting sem p@(Program bbs) csem = 
  let bbid2loc = M.map bbloc (programBBId2BB p) 
      bbid2nl = programBBId2nl p
   in foldl (\csem bb -> bbExecCollecting sem bbid2nl bbid2loc bb csem) csem bbs


programFixCollecting :: (Eq a, Ord a, Pretty a, Pretty a) => 
  Semantics a -> Program -> Collecting a -> Collecting a
programFixCollecting sem p csem = 
  repeatTillFix (programExecCollecting sem p) csem

-- Symbolic values
-- ===============


-- Symbolic polynomial with constant term and coefficients for the other terms
data Symaff = Symaff !(Int, M.Map Id Int) deriving (Eq, Ord)

-- return a list of IDs that occur in this sym aff
symAffOccurs :: Symaff -> S.Set Id
symAffOccurs (Symaff (_, coeffs)) = S.fromList $ M.keys $ M.filter (> 0) coeffs

instance Show Symaff where
  show (Symaff (c, coeffs)) = 
    let 
        showTerm :: Int -> Id -> Maybe String
        showTerm 0 x = Nothing
        showTerm 1 x = Just $ show x
        showTerm c x = Just $ show c ++ show x

        coeffs' :: [String]
        coeffs' = catMaybes [showTerm c id | (id, c) <- M.toList coeffs]
        
        c' :: String
        c' = if c == 0
                then "" 
                else if length coeffs' == 0 then show c else " + " ++ show c
     in (intercalate " + " $ coeffs') ++ c'

-- lift an identifier to a polynomial
symAffId :: Id -> Symaff
symAffId id = Symaff (0, M.fromList [(id, 1)])

-- extract an ID from a symaff, if the symaff represents an Id
symAffExtractId :: Symaff -> Maybe Id
symAffExtractId sa@(Symaff (_, id2coeffs)) = 
  case M.toList id2coeffs of
    [(id, _)] -> Just id
    _ -> Nothing

-- Lift a constant to a polynomial
symAffConst :: Int -> Symaff
symAffConst c = Symaff (c, M.empty)

-- remove IDs that have value 0 in the Symaff
-- Call internally after peforming operations
_symAffRemoveZeroIds :: Symaff -> Symaff
_symAffRemoveZeroIds (Symaff (c, cs)) = 
  (Symaff (c, M.filter (/= 0) cs))

-- Add two symbolic polynomials
symAffAdd :: Symaff -> Symaff -> Symaff
symAffAdd (Symaff (c1, p1)) (Symaff (c2, p2)) = 
  let pres = 
        M.merge 
          M.preserveMissing
          M.preserveMissing
          (M.zipWithMatched (\k x y -> x + y)) p1 p2 
       in _symAffRemoveZeroIds $ Symaff (c1 + c2, pres)

-- If a Symaff is constant, return the constant value, otherwise
-- return Nothing
symAffAsConst :: Symaff -> Maybe Int
symAffAsConst (Symaff (c, cs)) = if cs == M.empty then Just c else Nothing

-- negate a Symbolic affine value
symAffNegate :: Symaff -> Symaff
symAffNegate (Symaff (c, cs)) = Symaff (-c, M.map (\x -> (-x)) cs)

-- Check if one Symaff is defnitely less than the other
-- Use the fact that x < y <-> x - y < 0
symAffIsLt :: Symaff -> Symaff -> Maybe Bool
symAffIsLt a1 a2 = 
  let sub = symAffAdd a1 (symAffNegate a2)
      msubc = symAffAsConst sub
   in fmap (< 0)  msubc


instance Pretty Symaff where
  pretty (Symaff (c, coeffs)) = 
    let 
    prettyTerm :: Int -> Id -> Maybe (Doc a)
    prettyTerm 0 x = Nothing
    prettyTerm 1 x = Just $ pretty x
    prettyTerm c x = Just $ pretty c <> pretty x 

    c' :: Doc a
    c' = if c == 0 then mempty 
         else if null coeffs then pretty c else pretty "+" <+> pretty c

    coeffs' :: [Doc a]
    coeffs' = catMaybes [prettyTerm c id | (id, c) <- M.toList coeffs]
     in hcat (punctuate (pretty "+") coeffs') <+> c'

-- Symbolic value that is either a symbolic polynomial or a binop of two such
-- polynomials
data SymVal = SymValAff !Symaff 
            | SymValBinop !Binop !SymVal !SymVal 
            | SymValPhi !Id !Id !SymVal !Id !SymVal deriving(Eq, Ord)

-- return a list of IDs that occur in this symbolic value
symValOccurs :: SymVal -> S.Set Id
symValOccurs (SymValAff aff) = symAffOccurs aff
symValOccurs (SymValBinop _ l r) = symValOccurs l `S.union` symValOccurs r
symValOccurs (SymValPhi _ _ l _ r) = symValOccurs l `S.union` symValOccurs r

symValId :: Id -> SymVal
symValId = SymValAff . symAffId


symValConst :: Int -> SymVal
symValConst = SymValAff . symAffConst

instance Show SymVal where
  show (SymValAff p) = show p
  show (SymValBinop op sym sym') = 
   "(" ++ show op ++ " " ++ show sym ++ " " ++ show sym' ++ ")"

instance Pretty SymVal where
  pretty (SymValAff p) = pretty p
  pretty (SymValBinop op sym sym') =
    parens $  pretty sym <+> pretty op <+> pretty sym'
  pretty (SymValPhi idphi idl syml idr symr) 
    = parens $ pretty "phi" <+> pretty idphi <+> pretty (idl, syml)<+> pretty (idr, symr)

-- constant folding for symbols
symConstantFold :: SymVal -> SymVal
symConstantFold (SymValBinop op s1 s2) = 
  let 
    s1' = symConstantFold s1
    s2' = symConstantFold s2
 in case (op, s1', s2') of
      (Add, SymValAff p1, SymValAff p2) -> SymValAff $ symAffAdd p1 p2
      (Lt, SymValAff p1, SymValAff p2) -> 
        case symAffIsLt p1 p2 of
          Just True -> symValConst 1
          Just False -> symValConst 0
          Nothing -> (SymValBinop op s1' s2')
      _ -> SymValBinop  op s1' s2'
      
-- if it's a polynomial, leave it unchanged
symConstantFold p = p


-- Values to make opaque at a given PC
data OpaqueVals = OpaqueVals !(M.Map PC [Id])


-- Symbolic interpretation
-- =======================
-- check if sym occurs in itself. ie, you're trying to construct an infinite type
symInfiniteType :: Id -> SymVal -> Bool
symInfiniteType id val = id `S.member` symValOccurs val


-- if the val is infinite, block it. Otherwise, let it be constructed
symBlockInfiniteType :: Id -- id to block
                     -> SymVal -- symval to use as backup
                     -> SymVal -- symval to check
                     -> SymVal
symBlockInfiniteType id backup val = 
  if symInfiniteType id val then backup else val

-- get the symbolic value of an expression
exprGetSymbolic :: Id  -- identifier to avoid occurs check with
                ->  Expr 
                -> M.Map Id SymVal -> Maybe SymVal
exprGetSymbolic _ (EInt i) _ =  Just $ symValConst i
exprGetSymbolic _ (EBool b) _ =  Just $ if b then (symValConst 1) else (symValConst 0)
exprGetSymbolic idinf (EId id) env = (symBlockInfiniteType idinf (symValId id)) <$> (env M.!? id)
exprGetSymbolic idinf (EBinop op e1 e2) env = 
  let ml = exprGetSymbolic idinf e1 env
      mr = exprGetSymbolic idinf e2 env
   in liftA2 opimpl ml mr where
    opimpl v1 v2 = symConstantFold $ SymValBinop op v1 v2

mapInsertMaybe :: Ord k => k -> Maybe v -> M.Map k v -> M.Map k v
mapInsertMaybe k (Just v) m = M.insert k v m
mapInsertMaybe _ Nothing m = m

-- If the phi does not create an infinite type, then allow it.
-- Otherwise, disallow
-- TODO: clean this up, too many cases
phiGetSymbolic :: Phi -> M.Map Id SymVal -> M.Map Id SymVal
phiGetSymbolic (Phi _ idphi (bbidl, idl) (bbidr, idr)) env = 
  let
    ml = exprGetSymbolic idphi (EId idl) env
    mr = exprGetSymbolic idphi (EId idr) env
    mphi = liftA2 (\ml mr -> SymValPhi idphi idl ml idr mr) ml mr
 in case mphi of
      Just sym -> M.insert idphi sym env
      Nothing -> M.insert idphi (symValId idphi) env


instGetSymbolic :: Inst -> M.Map Id SymVal -> M.Map Id SymVal
instGetSymbolic (Assign _ id expr) env = 
  case exprGetSymbolic id expr env of
    Just v -> M.insert id v env
    Nothing -> M.insert id (symValId id) env

  -- mapInsertMaybe id (exprGetSymbolic expr env) env

bbGetSymbolic :: BB -> M.Map Id SymVal -> M.Map Id SymVal
bbGetSymbolic bb env = 
  let envphis = foldl (flip phiGetSymbolic) env (bbphis bb)
      envinsts = foldl (flip instGetSymbolic) envphis (bbinsts bb)
   in envinsts

bbInitSymbolic :: BB -> M.Map Id SymVal 
bbInitSymbolic bb = 
  let envphis = M.fromList $ map (\(Phi _ id _ _) -> (id, symValId id)) (bbphis bb)
      envinsts = M.fromList $ map (\(Assign _ id _ ) -> (id, symValId id)) (bbinsts bb)
   in envphis <> envinsts

programGetSymbolic :: Program -> M.Map Id SymVal
programGetSymbolic (Program bbs) = 
  let 
    runbbs :: M.Map Id SymVal -> M.Map Id SymVal
    runbbs env = foldl (flip bbGetSymbolic) env bbs

    initenv :: M.Map Id SymVal
    initenv = mconcat $ map bbInitSymbolic bbs
 in (repeatTillFix runbbs) initenv



-- Symbolic expression to Pwaff
-- ============================
localSpaceIds :: Ptr Ctx -> M.Map Id  (Ptr ISLTy.Id) -> IO (Ptr LocalSpace)
localSpaceIds ctx id2islid = do
  ls <- localSpaceSetAlloc ctx 0 (length id2islid)
  putStrLn "local space created."
  let islidcounters = zip (M.elems id2islid) [0, 1..]
  islidcounters <- traverse (\(id, c) -> (, c) <$> idCopy id) islidcounters

  putStrLn "local space adding dimensions."
  ls <- foldM 
          (\ls (islid, ix) -> 
              localSpaceSetDimId ls IslDimSet ix islid) ls
                islidcounters
  putStrLn "local space added dimensions"
  localSpaceDump ls
  return ls


idToAff :: Ptr Ctx
  -> M.Map Id (Ptr ISLTy.Id)
  -> Id
  -> IO (Ptr Aff)
idToAff ctx id2islid curid = do
  ls <- localSpaceIds ctx id2islid
  -- TODO: we are assuming that IDs are found in the parameter dimension
  (Just varix) <- findDimById ls IslDimSet (id2islid M.! curid)
  var <- affVarOnDomain ls IslDimSet varix
  return var

termToPwaff :: Ptr Ctx 
            -> M.Map Id (Ptr ISLTy.Id) 
            -> M.Map Id SymVal 
            -> Id 
            -> Int 
            -> IO (Ptr Pwaff)
termToPwaff ctx id2islid id2sym id coeff = do
  -- TODO: refactor this
  var <- idToAff ctx id2islid id
  coeff <- localSpaceIds ctx id2islid >>= \ls -> affInt ctx ls coeff
  term <- affMul var coeff >>= pwaffFromAff
  return term


  

symaffToPwaff :: Ptr Ctx -> M.Map Id (Ptr ISLTy.Id) -> M.Map Id SymVal -> Symaff -> IO (Ptr Pwaff)
symaffToPwaff ctx id2islid id2sym(Symaff (c, terms)) = do
    ls <- localSpaceIds ctx id2islid 
    pwconst <- pwaffInt ctx ls c
    pwaffToStr pwconst >>= \s -> putStrLn $ "pwconst:" ++ s
    if M.null terms
       then return pwconst
       else do
         pwterms <- traverse (\(id, coeff) -> termToPwaff ctx id2islid id2sym id coeff) (M.toList terms)
         foldM pwaffAdd pwconst pwterms 

-- add a new dimension to the map and return its index
mapAddUnnamedDim :: Ptr Map -> DimType -> Maybe (Ptr ISLTy.Id) -> IO (Ptr Map, Int)
mapAddUnnamedDim m dt mislid = do
    ndim <- mapDim m dt
    m <- mapAddDims m dt 1
    m <- case mislid of 
          Nothing -> return m
          Just islid -> mapSetDimId m dt ndim islid
    return (m, fromIntegral ndim)
      
pwaffFromMap :: Ptr Map -> IO (Ptr Pwaff)
pwaffFromMap m = do
    pwma <- (pwmultiaffFromMap m)
    pwa <- pwmultiaffGetPwaff pwma 0
    return pwa

-- returns the position of the first occurence of id if exists, otherwise returns Nothing
mapGetIxOfId :: Ptr Map -> DimType -> Ptr ISLTy.Id  -> IO (Maybe Int)
mapGetIxOfId m dt islid = do
  ndim <- mapDim m dt
  id2ix <- M.fromList <$> traverse (\ix ->  (,ix) <$> (mapGetDimId m dt ix)) [0..ndim-1]
  return $ fromIntegral <$> (id2ix M.!? islid)


mapConditionallyMoveDims :: Ptr Map 
                         -> (Ptr ISLTy.Id -> Bool) -- filter for dimension ID
                         -> DimType  -- input dimension
                         -> DimType -- output dimension
                         -> IO (Ptr Map)
mapConditionallyMoveDims m idfilter din dout = 
  let move :: Ptr Map -> Int -> IO (Ptr Map)
      move m ixin = do
        nin <- mapDim m din
        nout <- mapDim m dout
        
        if fromIntegral ixin >= nin
           then return m
           else do
                 idin <- mapGetDimId m din (fromIntegral ixin)
                 let shouldmove = idfilter idin
                 --mapToStr m >>= 
                 --  (\s -> putStrLn $ "nin: " ++ show nin ++ 
                 --           "|ixin: " ++ show ixin ++ 
                 --           "|shouldmove: " ++ show shouldmove ++ 
                 --           "|nout: " ++ show nout ++ 
                 --           " " ++ s)
                 if shouldmove
                    then do
                        m <- mapMoveDims m dout nout din (fromIntegral ixin) (fromIntegral 1)
                        move m ixin
                    else move m (ixin + 1)
  in move m 0 


class Spaced a where
  getSpace :: a -> IO (Ptr Space)
  -- get the number of dimensions for the given dimtype
  ndim :: a -> DimType -> IO Int
  ndim a dt = getSpace a >>= \s -> spaceDim s dt 

  -- get the dimension ID
  getDimId :: a -> DimType -> Int -> IO (Ptr ISLTy.Id)
  getDimId a dt ix = getSpace a >>= \s -> spaceGetDimId s dt ix

  -- set the dimension ID
  setDimId :: a -> DimType -> Int -> Ptr ISLTy.Id ->  IO a

  -- add dimensions
  addDims :: a -> DimType -> Int -> IO a

  findDimById :: a -> DimType -> Ptr ISLTy.Id -> IO (Maybe Int)
  findDimById a dt id = 
    getSpace a >>= \s -> do
      n <- ndim s dt
      mixs <- traverse (\ix -> do 
        ixid <- spaceGetDimId s dt ix
        if ixid == id 
           then return (Just ix)
           else return Nothing) [0..(n-1)]
      return $ foldl (<|>) Nothing mixs

-- add dimensions with the given IDs. 
-- NOTE, TODO: I am abusing "name" to mean "id'd". Hopefully, this will
-- not get confusing.
addNamedDims :: Spaced a => a -> DimType -> [Ptr ISLTy.Id] -> IO a
addNamedDims x dt ids = do
  n <- ndim x dt
  -- tuples of new IDs and their locations
  let newidixs = zip ids [n..]
  x <- addDims x dt (length ids)
  foldM (\x (id, ix) -> setDimId x dt ix id) x newidixs

instance Spaced (Ptr Space) where
  getSpace = return
  setDimId x dt i id = spaceSetDimId x dt (fromIntegral i) id
  addDims x dt i = spaceAddDims x dt (fromIntegral i)


instance Spaced (Ptr LocalSpace) where
  getSpace = localSpaceGetSpace
  setDimId x dt i id = localSpaceSetDimId x dt i id
  addDims x dt i = localSpaceAddDims x dt (fromIntegral i)


instance Spaced (Ptr Set) where
  getSpace = setGetSpace
  setDimId x dt i id = setSetDimId x dt (fromIntegral i) id
  addDims x dt i = setAddDims x dt (fromIntegral i)

instance Spaced (Ptr Map) where
  getSpace = mapGetSpace
  setDimId x dt i id = mapSetDimId x dt (fromIntegral i) id
  addDims x dt i = mapAddDims x dt (fromIntegral i)

instance Spaced (Ptr Pwaff) where
  getSpace = pwaffGetSpace
  setDimId x dt i id = pwaffSetDimId x dt (fromIntegral i) id
  addDims x dt i = pwaffAddDims x dt (fromIntegral i)

-- align a to b's space
class Spaced b => Alignable a b where
  alignParams :: a -> b -> IO a

instance Spaced b => Alignable (Ptr Pwaff) b where
  alignParams pwaff b = getSpace b >>= \s -> pwaffAlignParams pwaff s



constraintEqualityForSpaced :: Spaced  a => a -> IO (Ptr Constraint)
constraintEqualityForSpaced set = do
  getSpace set >>= localSpaceFromSpace >>= constraintAllocEquality


-- assume two pwaffs:
-- pw1: [x_entry, params] -> { [viv] -> [x_entry + viv] : viv >= 0 }
-- pw2: [params] -> { [1] }
-- We would like to add the inputs of pw1 to pw2, and lift it to the constant function
-- In general, we want to check that the dimensions match till where they match,
-- and align the rest
-- aligns the *first* parameter *to* second param
-- if first has more dimensions, returns the second unchanged
pwaffAlignLoopViv :: Ptr Pwaff -> Ptr Pwaff -> IO (Ptr Pwaff)
pwaffAlignLoopViv pw pw' = do
    ninpw <- ndim pw IslDimIn
    ninpw' <- ndim pw' IslDimIn

    if ninpw > ninpw' 
       then return pw
       else do 
          -- indeces to check are equal
          let tocheck = [0..ninpw-1]
          forM_ tocheck (\ix -> do
            id <- getDimId pw IslDimIn ix
            id' <- getDimId pw' IslDimIn ix
            return $ assert  (id == id') ())

          -- indeces to be aligned
          let tofix = [ninpw..ninpw'-1]
          newids <- traverse (getDimId pw' IslDimIn) tofix
          pw <- addNamedDims pw IslDimIn newids
          -- we need to ensure domain constraints are the same
          pw'domain <- pwaffCopy pw' >>= mapFromPwaff >>= mapDomain
          pw <- pwaffIntersectDomain pw pw'domain
          return pw

-- On calling functions such as set indicator, we will get pwaffs
-- with negative viv. For example, consider:
-- set: { [x] : 0 <= x <= 4 }
-- indicator: { [x] -> [1] : 0 <= x <= 4 , [x] -> [0]: x < 0 or x > 4 }
-- We dont' want the part where x < 0, since viv can't be less than 0.
pwaffMkVivNonNegative :: Ptr Pwaff -> IO (Ptr Pwaff)
pwaffMkVivNonNegative pwaff = do
  map <- mapFromPwaff pwaff
  nin <- ndim map IslDimIn

  map <- foldM (\map ix -> do
          idgt0 <- getSpace map >>= localSpaceFromSpace >>= constraintAllocInequality
          idgt0 <- constraintSetCoefficientSi idgt0 IslDimIn ix (1)
          map <- mapAddConstraint map idgt0
          return map
        ) map [0..(fromIntegral nin-1)]


  pwaffFromMap map >>= pwaffCoalesce




-- Given the symbolic representation of all other expressions, maximal
-- upto occurs check, create the symbolic value for this expression
symValToPwaff :: Ptr Ctx 
              -> M.Map Id (Ptr ISLTy.Id) -- id to ISL ids of that variable
              -> M.Map Id SymVal  -- values of each ID
              -> SymVal  -- symval to convert
              -> IO (Ptr Pwaff)
symValToPwaff ctx id2islid id2sym (SymValAff aff) = 
  symaffToPwaff ctx id2islid id2sym aff
symValToPwaff ctx id2islid id2sym (SymValBinop bop l r) = do
  pwl <- symValToPwaff ctx id2islid id2sym l
  pwr <- symValToPwaff ctx id2islid id2sym r
  pwl <- pwaffAlignLoopViv pwl pwr
  pwr <- pwaffAlignLoopViv pwr pwl

  case bop of
    Add -> pwaffAdd pwl pwr
    Lt ->  do
            ltset <- pwaffLtSet pwl pwr 
            pwlt <- return ltset >>= setIndicatorFunction >>= pwaffCoalesce 
            return pwlt >>= pwaffMkVivNonNegative

-- symValToPwaff ctx id2islid id2sym (SymValPhi idphi idl syml idr symr) = idToAff ctx id2islid idphi >>= pwaffFromAff
-- TODO: actually attach the loop header name here

symValToPwaff ctx id2islid id2sym (SymValPhi idphi idl syml idr symr) = do
  -- { [x_loop, rest] -> [x_loop] }
  mapid <- symValToPwaff ctx id2islid id2sym (symValId idphi) >>= mapFromPwaff
  -- [x_loop] -> { [rest] -> [x_loop] }
  mapid <- mapConditionallyMoveDims mapid (const True) IslDimIn IslDimParam
  setid <- mapWrap mapid
  setToStr setid >>= \s -> putStrLn $ "setid: " ++ s

  --  { [x_loop, rest] -> [xloop + delta] }
  mapbackedge <- symValToPwaff ctx id2islid id2sym (id2sym M.! idr) >>= mapFromPwaff
  --  [x_loop] -> { [rest] -> [xloop + delta] }
  mapbackedge <- mapConditionallyMoveDims mapbackedge (const True) IslDimIn IslDimParam
  mapToStr mapbackedge >>= \s -> putStrLn $ "mapbackedge: " ++ s
  setbackedge <- mapWrap mapbackedge
  setToStr setbackedge >>= \s -> putStrLn $ "setbackege: " ++ s


  -- [x_loop] -> { [[] -> [xloop]] -> [[] -> [xloop + delta]] }
  mapbackedgeff <- mapFromDomainAndRange setid setbackedge
  mapToStr mapbackedgeff >>= \s -> putStrLn $ "mapbackedgeff: " ++ s
  (Just phiix)  <- mapGetIxOfId mapbackedgeff IslDimParam (id2islid M.! idphi) 
  mapbackedgeff <- mapProjectOut mapbackedgeff IslDimParam (fromIntegral phiix) 1
  mapToStr mapbackedgeff >>= \s -> putStrLn $ "mapbackedgeff (after project): " ++ s



  -- [params] -> { [k] -> [[[] -> [o0]] -> [[] -> [k + o0]]] : k > 0 }
  (pow, _) <- mapPower mapbackedgeff
  idviv <- idAlloc ctx "viv"
  pow <- mapSetDimId pow IslDimIn 0 idviv
  mapToStr pow >>= \s -> putStrLn $ "power: " ++ s

  -- [params, k] -> { [] -> [[[] -> [o0]] -> [[] -> [k + o0]]] : k > 0 }
  pow <- mapConditionallyMoveDims pow (const True) IslDimIn IslDimParam
  -- [params, k] -> { [[] -> [o0]] -> [[] -> [k + o0]] : k > 0 }
  pow <- mapRange pow >>= setUnwrap

  -- { [params] -> [entryval] }
  entry <- symValToPwaff ctx id2islid id2sym (symValId idl) >>= mapFromPwaff
  -- [params] -> { [] -> [entryval] }
  entry <- mapConditionallyMoveDims entry (const True) IslDimIn IslDimParam
  mapToStr entry >>= \s -> putStrLn  $ "entry: " ++ s

  -- [params] -> { [[] -> [entryval]] }
  entryset <- mapCopy entry >>= mapWrap

  -- [params, k] -> { [] -> [k+ o0] }
  final <- setApply entryset pow >>= setUnwrap


  -- [params] -> { [k] -> [k+ o0] }
  final <- mapConditionallyMoveDims  final (== idviv) IslDimParam IslDimIn
  mapToStr final >>= \s -> putStrLn  $ "final: " ++ s

  -- Now, align final with the entry data
  -- final: [params] -> { [k] -> [k + o0] }
  -- entry: [params] -> { [o0] }
  -- need to make entry:
  -- entry: [params] -> { [k] -> [o0] : k = 0 }
  (final_iter_0, _) <- mapCopy entry >>= \entry -> mapAddUnnamedDim entry IslDimIn  (Just idviv)

  k0 <- constraintEqualityForSpaced final_iter_0
  -- TODO: verify that dim 0 is `idviv`
  let idvivix = 0
  k0 <- constraintSetCoefficientSi k0 IslDimIn idvivix (-1)
  final_iter_0 <- mapAddConstraint final_iter_0 k0

  -- final: [params] -> { [k] -> [k + o0] : k > 0 and [0] -> [entry] }
  final <- mapUnion final final_iter_0
  mapToStr final >>= \s -> putStrLn $ "final map with entry: " ++ s

  -- final, move parameters in:
  ifnal <- mapConditionallyMoveDims final (const True) IslDimParam IslDimIn


  pwaff <- pwaffFromMap final >>= pwaffCoalesce
  pwaffToStr pwaff >>= \s -> putStrLn $ "final pwaff:" ++ s
  return pwaff

traverseMap :: (Ord k, Monad m) => (k -> v -> m o) 
            -> M.Map k v 
            -> m (M.Map k o)
traverseMap f k2v = 
  M.fromList <$> traverse (\(k, v) -> (k,) <$> f k v) (M.toList k2v)

-- { [a] -> [b] }
-- { [c] -> [a] }
-- iterate the representation of values as pwaffs
iteratePwaffRepresentation :: Ptr Ctx
            -> M.Map Id SymVal
            -> M.Map Id (Ptr ISLTy.Id) -- id to ISL ids of that variable
            -> M.Map Id (Ptr Pwaff)
            -> IO (M.Map Id (Ptr Pwaff))
iteratePwaffRepresentation ctx id2sym id2islid id2pwaff = 
  let helper :: Id -> Ptr Pwaff -> IO (Ptr Pwaff)
      helper curid curpwaff = do
        let cursym = id2sym M.! curid
        let curislid = id2islid M.! curid 
        let islid2pwaff = M.fromList [(islid, id2pwaff M.! id) | (id, islid) <- (M.toList id2islid)]

        -- ids to replace this pwaff's representation with
        -- pwaffs to pullback with
        nin <- ndim curpwaff IslDimIn
        islidstopullback <- traverse (getDimId curpwaff IslDimIn) [0..(nin-1)]
        -- if we have the ID, then pullback. If not, produce the function
        -- that evaluates to the given value
        pwaffstopullback <- traverse 
          (\islid ->
            case islid2pwaff M.!? islid of 
              Just pwaff -> return pwaff
              Nothing -> do
                space <- pwaffGetDomainSpace curpwaff >>= localSpaceFromSpace
                -- find the given ISL id in the space
                Just ix <- findDimById space IslDimSet islid
                pw <- affVarOnDomain space IslDimSet ix >>= pwaffFromAff
                pwaffGetSpace curpwaff >>= pwaffAlignParams pw 
              ) islidstopullback

        pwaffToStr curpwaff >>= \s -> putStrLn $ "bundle for: " ++ s
        traverse (\pwaff -> pwaffToStr pwaff >>= \s -> putStrLn $ "  --" ++ s ) pwaffstopullback

        domain <-pwaffGetDomainSpace curpwaff
        domain' <- pwaffGetDomainSpace curpwaff

        multipwspace <- spaceMapFromDomainAndRange domain domain'
        multipwspace <- pwaffGetSpace curpwaff >>= \s -> 
          spaceAlignParams multipwspace s

        putStrLn "2"
        listpws <- toListPwaff ctx pwaffstopullback 
        putStrLn "3"
        multipw <-  multipwaffFromPwaffList multipwspace listpws
        putStrLn "4"

        return curpwaff
   in traverseMap helper id2pwaff

initId2Pwaff :: Ptr Ctx 
             -> M.Map Id (Ptr ISLTy.Id) -- ID to the ISL id of the variable
             -> [Id] 
             -> IO (M.Map Id (Ptr Pwaff)) 
initId2Pwaff ctx id2islids ids = 
  M.fromList <$> traverse 
    (\id -> (id,) <$>  (idToAff ctx id2islids id >>= pwaffFromAff)) ids

-- Abstract interpretation
-- =======================

absint :: Program -> AbsDomain
absint = undefined

gamma :: AbsDomain -> ConcreteDomain
gamma = undefined



-- Program builder
-- ===============

class ToExpr a where
  toexpr :: a -> Expr

instance ToExpr Id where
  toexpr a = EId a


instance ToExpr String where
  toexpr a = EId (Id a)

instance ToExpr Bool where
  toexpr True = EInt 1
  toexpr False = EInt 0

instance ToExpr Expr where
  toexpr = id

(+.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(+.) a b = EBinop Add (toexpr a) (toexpr b)


(<.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(<.) a b = EBinop Lt (toexpr a) (toexpr b)

-- Builder of program state
data ProgramBuilder = ProgramBuilder { 
  builderpc :: Loc, 
  curbbid :: Maybe BBId,
  bbid2bb :: OM.OrderedMap BBId BB
}


runProgramBuilder :: ST.State ProgramBuilder () -> Program
runProgramBuilder pbst = 
  let pbinit :: ProgramBuilder
      pbinit = ProgramBuilder (Loc (-1)) Nothing OM.empty

      pbout :: ProgramBuilder
      pbout = ST.execState pbst pbinit
   in Program $ map snd (OM.toList (bbid2bb pbout))


builderLocIncr :: ST.State ProgramBuilder Loc
builderLocIncr = do
  loc <- ST.gets builderpc
  ST.modify (\s -> s { builderpc = locincr (builderpc s) })
  return loc

-- builds a new basic block, but *does not focus on it*
buildNewBB :: String -> Maybe BBTy -> ST.State ProgramBuilder BBId 
buildNewBB name ty = do
  loc <- builderLocIncr
  locret <- builderLocIncr
  let bbid = BBId name
  let bb = BB bbid ty loc [] [] (Done locret)
  ST.modify (\s -> s { bbid2bb = OM.insert bbid bb (bbid2bb s) } )

  return bbid

focusBB :: BBId -> ST.State ProgramBuilder ()
focusBB bbid = ST.modify (\s -> s { curbbid = Just bbid })

builderCurBBModify :: (BB -> BB) -> ST.State ProgramBuilder ()
builderCurBBModify f = 
  ST.modify (\s -> let m = bbid2bb s
                       (Just bbid) = curbbid s
                       m' = OM.adjust f bbid m
                 in s { bbid2bb = m' })


appendInst :: Inst -> ST.State ProgramBuilder ()
appendInst i = builderCurBBModify (bbModifyInsts (++ [i]))

appendPhi :: Phi -> ST.State ProgramBuilder ()
appendPhi ph = builderCurBBModify (bbModifyPhis (++ [ph]))

setTerm :: Term -> ST.State ProgramBuilder ()
setTerm term = builderCurBBModify (bbModifyTerm (const term))

assign :: String -> Expr -> ST.State ProgramBuilder ()
assign id e = do
  loc <- builderLocIncr
  appendInst (Assign loc (Id id) e)

done :: ST.State ProgramBuilder ()
done = do
  loc <- builderLocIncr
  setTerm (Done loc)

phi :: String -> (BBId, String) -> (BBId, String) -> ST.State ProgramBuilder ()
phi id (bbidl, idl) (bbidr, idr) = do
  loc <- builderLocIncr
  appendPhi (Phi loc (Id id) (bbidl, Id idl) (bbidr, Id idr))

condbr :: String -> BBId -> BBId -> ST.State ProgramBuilder ()
condbr id bbidt bbidf = do
  loc <- builderLocIncr
  setTerm (BrCond loc (Id id) bbidt bbidf)


br :: BBId -> ST.State ProgramBuilder ()
br bbid = do
  loc <- builderLocIncr
  setTerm (Br loc bbid)

-- Example programs
-- ================

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
  phi "x_loop" (entry, "x_entry") (loop, "x_next")

  assign "x_loop_lt_5" ("x_loop" <. (EInt 5))
  assign "x_next" ("x_loop" +. (EInt 1))

  condbr "x_loop_lt_5" loop exit
-- 
-- -- ========================
-- -- CHOOSE YOUR PROGRAM HERE
-- -- ========================
pcur :: Program
pcur = pLoop


main :: IO ()
main = do
    islctx <- ctxAlloc


    putStrLn "***program***"
    putDocW 80 (pretty pcur)
    putStrLn ""
    
    putStrLn "***program output***"
    let outenv =  (programExec semConcrete pcur) envBegin
    print outenv


    putStrLn "***collecting semantics (concrete x symbol):***"
    let cbegin = (collectingBegin pcur) :: Collecting Int
    let csem = programFixCollecting semConcrete pcur cbegin
    putDocW 80 (pretty csem)
    -- forM_  (S.toList curCSemIntSym) (\m -> (putDocW 80 . pretty $ m) >> putStrLn "---")

  
    putStrLn ""
    putStrLn "***symbolic values***"
    let id2sym = programGetSymbolic pcur
    putDocW 80 (pretty id2sym)


    putStrLn ""
    putStrLn "***pwaff values***"
    id2islid <- traverseMap (\(Id idstr) _ -> idAlloc islctx idstr) id2sym
    id2pwaff  <- traverse (symValToPwaff islctx id2islid id2sym) id2sym
    traverse pwaffToStr id2pwaff >>= (putDocW 80) . pretty 


    putStrLn ""
    putStrLn "***iterated pwaff values***"
    id2pwaffs <- repeatTillFixDebugTraceM 5 (iteratePwaffRepresentation  islctx id2sym id2islid) id2pwaff

    forM_ id2pwaffs (\id2pwaff -> do
      putStrLn "" 
      traverse pwaffToStr id2pwaff >>= (putDocW 80) . pretty)

