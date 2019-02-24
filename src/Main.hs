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
import PrettyUtils (prettyableToString, docToString)
import Foreign.Ptr
import Control.Monad (foldM)
import qualified Control.Monad (join)
import qualified System.IO.Unsafe as Unsafe (unsafePerformIO)
import GHC.Stack


(!!#) :: HasCallStack => Ord k => Pretty k => Pretty v => M.Map k v -> k -> v
(!!#) m k = 
  case M.lookup k m of
    Just v -> v
    Nothing -> error . docToString $  
                pretty "missing key: " <+> pretty k <+> 
                  pretty "in map: " <+> pretty m
{-# Inline (!!#) #-}
instance {-# OVERLAPPABLE #-} Pretty (Ptr a) where
  pretty pa = pretty $ show pa

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
data LatticeMap k v = LM !(M.Map k v)  deriving (Eq, Ord, Functor)

-- Insert a regular value into a lattice map
lminsert :: Ord k => k -> v -> LatticeMap k v -> LatticeMap k v
lminsert k v (LM m) = LM $ M.insert k v m

-- pointwise produce of two lattice maps
-- If a value is missing in either lattice, put a bottom in its place
lmproduct :: (SemiMeet v, SemiMeet w, Ord k) => LatticeMap k v -> LatticeMap k w -> LatticeMap k (v, w)
lmproduct (LM m) (LM m') = let
  missingm' = M.mapMissing (\k w -> bottom)
  missingm =  M.mapMissing (\k v -> bottom)
  merger = M.zipWithMatched (\k tx ty -> (tx, ty))
  in LM $ M.merge missingm' missingm merger m m'

adjust :: Ord k => k -> (v -> v) -> LatticeMap k v -> LatticeMap k v
adjust k f (LM m) = LM $ M.adjust f k m

(!!#!) :: (Ord k, SemiMeet v) => LatticeMap k v -> k -> v
(!!#!) (LM m) k = case m M.!? k of
                   Just v -> v
                   Nothing -> bottom


(!!#?) :: Ord k => LatticeMap k v -> k -> Maybe v
(!!#?) (LM m) k = m M.!? k 

lmfromlist :: Ord k => [(k, v)] -> LatticeMap k v
lmfromlist kvs = LM $ M.fromList [(k, v) | (k, v) <- kvs]

lmempty :: LatticeMap k v 
lmempty = LM $ M.empty

lmtolist :: Ord k => LatticeMap k v -> [(k, v)]
lmtolist (LM m) = M.toList m

instance (Ord k, Show k, Show v, Pretty k, Pretty v) => Show (LatticeMap k v) where
  show (LM m) = show $ [(k, m !!# k) | k <- M.keys m]


instance (Ord k, Pretty k, Pretty v) => Pretty (LatticeMap k v) where
  pretty (LM m) =  pretty m -- vcat $ [pretty k <+> pretty "->" <+> pretty (m !!# k) | k <- M.keys m]

instance SemiMeet v => SemiMeet (LatticeMap k v) where
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

repeatTillFixDebugTraceM :: (Monad m) => Int -> (a -> a -> Bool) -> (a -> m a) -> a -> m [a]
repeatTillFixDebugTraceM 0 eqf f a = return [a]
repeatTillFixDebugTraceM n eqf f a = do
  a' <- f a
  if eqf a a' 
  then return [a]
  else do
    as <- repeatTillFixDebugTraceM (n - 1) eqf f a'
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

data Paramid = Paramid String deriving(Eq, Ord)
instance Show Paramid where
  show (Paramid p) = "param:" ++ p

instance Pretty Paramid where
  pretty p = pretty . show $ p

data Expr = EInt !Int | EBool !Bool  | EBinop !Binop !Expr !Expr | EId Id | EParam Paramid
  deriving(Eq, Ord)

instance Show Expr where
    show (EInt i) = show i
    show (EBool b) = show b
    show (EId id) = show id
    show (EParam id) = show id
    show (EBinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Pretty Expr where
  pretty (EInt i) = pretty i
  pretty (EBool b) = pretty b
  pretty (EId id) = pretty id
  pretty (EParam id) = pretty id
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
data Assign = Assign {
    assignloc :: !Loc,
    assignid :: !Id,
    assignexpr :: !Expr
}deriving(Eq, Ord, Show)

instance Pretty Assign where
  pretty (Assign pc id expr) =
    pretty pc <+> pretty id <+> equals <+> pretty expr

instance Located Assign where
  location (Assign loc _ _) = loc

-- Phi nodes
data Phity = Philoop | Phicond deriving(Eq, Ord, Show)
instance Pretty Phity where
  pretty (Philoop) = pretty "loop"
  pretty (Phicond) = pretty "cond"

data Phi = Phi {
    philoc :: !Loc,
    phity :: Phity,
    phiid :: Id,
    phil :: (BBId, Id),
    phir :: (BBId, Id) 
} deriving(Eq, Ord, Show)

instance Located Phi where
  location (Phi loc ty _ _ _) = loc

instance Pretty Phi where
  pretty (Phi loc ty id l r) =
    pretty loc <+> pretty "phi" <+> pretty ty <+>
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
 bbinsts :: [Assign],
 bbterm :: Term 
}deriving(Eq, Ord, Show)

instance Pretty BB where
  pretty (BB bbid bbty bbloc phis is term) = 
    pretty bbloc <+> pretty bbid <+> pretty bbty <> line <>
      indent 4 (vcat $ (map pretty phis) ++  (map pretty is) ++ [pretty term])

instance Located BB where
  location (BB _ _ loc _ _ _) = loc


bbModifyInsts :: ([Assign] -> [Assign]) -> BB -> BB
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

bbGetIds :: BB -> [Id]
bbGetIds (BB _ _ _ phis assigns _) = 
    map phiid phis ++ map assignid assigns


-- Program is a collection of basic blocks, and list of input parameter names.
-- First basic block is the entry block (block that gets executed on startup)
data Program = Program { progparams :: S.Set Paramid, progbbs :: [BB]  } deriving(Eq)

-- get the entry basic block ID
programEntryId :: Program -> BBId
programEntryId (Program _ (entry:_)) = bbid entry


-- get the largest location
programMaxLoc :: Program -> Loc
programMaxLoc (Program _ bbs) = 
  let locs = bbs >>= bbGetLocs 
   in maximum locs

instance Pretty Program where
  pretty (Program params bbs) = vcat $ 
    [pretty "prog" <> parens (pretty (S.toList params))] ++ map pretty bbs

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


envFromParamList :: [(Id, v)] -> Env v
envFromParamList id2v = Env (M.fromList id2v) mempty PCEntry

-- map variables to functions of loop trip counts
type TripCount = M.Map Id Int


-- collecting semantics in general. Map PC to a set of environments
type Collecting a = M.Map Loc (S.Set (Env a))

-- Setup the initial environment for the collecting semantics
collectingBegin :: Ord a => Program -> Env a -> Collecting a
collectingBegin p@(Program _ (entry:_)) initenv = 
  let locs = map Loc [-1..(unLoc (programMaxLoc p))]
      allempty = M.fromList $ zip locs (repeat mempty)
   in M.insert (location entry) (S.singleton initenv) allempty

-- concrete environments
type ConcreteEnv = Env Int

-- The concrete domain is the collecting semantics of the concrete environment
type ConcreteDomain  = Collecting ConcreteEnv


-- type SemExpr = Expr -> Env a -> a
-- type SemPhi = Phi -> BBId -> Env a -> Env a
-- type SemInst = Assign -> Env a -> Env a
-- type SemTerm = Term -> BBId -> Env a -> PC
-- 
-- definitino of semantics
data Semantics a = Semantics {
 semExpr :: Expr -> VEnv a -> a,
 semPredicate :: a -> Maybe Bool
}

mkSemInst :: (Expr -> VEnv a -> a) -> Assign -> VEnv a -> VEnv a
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
mkSemPhi  p@(Phi _ _ id (bbidl, idl) (bbidr, idr)) prevbbid env = 
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
programBBId2BB (Program _ bbs) = 
  foldl (\m bb -> M.insert (bbid bb) bb m) M.empty bbs

programBBId2nl :: Program -> M.Map BBId NaturalLoop
programBBId2nl (Program _ bbs) = M.fromList $ do
  bb <- bbs
  let ty = bbty bb
  case ty of
    Just (BBLoop bodies) -> return (bbid bb, NaturalLoop (bbid bb) (S.fromList bodies))
    Nothing -> []



programExec :: Pretty a => Semantics a -> Program -> Env a -> Env a
programExec sem p@(Program _ bbs) env@(Env _ _ pc) = 
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
semExprConcrete (EParam (Paramid id)) env = env !!# Id id
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


-- Abstract interpretation
-- =======================
localSpaceIds :: Ptr Ctx -> M.Map Id  (Ptr ISLTy.Id) -> IO (Ptr LocalSpace)
localSpaceIds ctx id2isl = do
  ls <- localSpaceSetAlloc ctx 0 (length id2isl)
  putStrLn "local space created."
  let islidcounters = zip (M.elems id2isl) [0, 1..]
  islidcounters <- traverse (\(id, c) -> (, c) <$> idCopy id) islidcounters

  putStrLn "local space adding dimensions."
  ls <- foldM 
          (\ls (islid, ix) -> 
              localSpaceSetDimId ls IslDimSet ix islid) ls
                islidcounters
  putStrLn "local space added dimensions"
  localSpaceDump ls
  return ls



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


-- Abstract interpretation
-- =======================
instance Pretty (Ptr Pwaff) where
    pretty pw = pretty $ (Unsafe.unsafePerformIO (pwaffToStr pw))
-- abstract environments
type AbsVEnv = LatticeMap Id (Ptr Pwaff)
data AbsDomain = 
    AbsDomain (LatticeMap Id (Ptr Pwaff)) (LatticeMap (BBId, BBId) (Ptr Set))
    deriving(Show)

instance Pretty AbsDomain where
    pretty (AbsDomain id2pwaff edge2set) = vcat [pretty id2pwaff, pretty edge2set]

-- construct a pwnan on the n-dimensional space
pwnan :: Ptr Ctx -> Ptr Space -> IO (Ptr Pwaff)
pwnan ctx s = do
    ls <- spaceCopy s >>= localSpaceFromSpace
    emptyset <- setEmpty s

    pwaff <- pwaffInt ctx ls 0 -- affValOnDomain ls 0 >>= pwaffFromAff
    pwaff <- pwaffIntersectDomain pwaff emptyset
    return pwaff

-- Create the set space common to all functions in the abstract domain
absSetSpace :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> IO (Ptr Space)
absSetSpace ctx id2isl = do
    s <- MR.liftIO $ spaceSetAlloc ctx 0 (length id2isl)
    s <- OM.foldMWithIx s id2isl (\s ix _ islid -> setDimId s IslDimSet ix islid)
    return s


-- return the ISL state that is used in common across the absint
newISLState :: Program -> IO (Ptr Ctx, OM.OrderedMap Id (Ptr ISLTy.Id))
newISLState p = do
    ctx <- ctxAlloc
    let ps = map (\(Paramid p) -> Id p) (S.toList . progparams $ p)
    islids <- OM.fromList <$> for ps (\id -> (id, ) <$> idAlloc ctx (show id))

    return $ (ctx, islids)

-- Initial abstract domain
absDomainStart :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) ->  Program -> IO AbsDomain
absDomainStart ctx id2isl p = do
    id2pwnan <- lmfromlist <$> 
        for (progbbs p >>= bbGetIds)
            (\id -> (id, ) <$> (absSetSpace ctx id2isl >>= pwnan ctx))
    let absdom = AbsDomain id2pwnan lmempty
    return $ absdom

absintbb :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Program -> BBId -> AbsDomain -> IO AbsDomain
absintbb ctx id2isl p bbid dom = return dom
    

absint :: Program -> IO AbsDomain
absint p = do
     (ctx, id2isl) <- newISLState p
     absDomainStart ctx id2isl p >>= absintbb ctx id2isl p (programEntryId p)


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
  builderparams ::  S.Set Paramid,
  builderpc :: Loc, 
  curbbid :: Maybe BBId,
  bbid2bb :: OM.OrderedMap BBId BB
}


runProgramBuilder :: ST.State ProgramBuilder () -> Program
runProgramBuilder pbst = 
  let pbinit :: ProgramBuilder
      pbinit = ProgramBuilder mempty (Loc (-1)) Nothing OM.empty

      pbout :: ProgramBuilder
      pbout = ST.execState pbst pbinit

      progbbs :: [BB]
      progbbs = map snd (OM.toList (bbid2bb pbout))

      progparams = builderparams pbout
   in Program progparams progbbs

param :: String -> ST.State ProgramBuilder Expr
param pname = do 
  ST.modify (\s -> s { 
    builderparams = (Paramid pname) `S.insert` (builderparams s) })
  return (EParam (Paramid pname))

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


appendInst :: Assign -> ST.State ProgramBuilder ()
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

phi :: Phity -> String -> (BBId, String) -> (BBId, String) -> ST.State ProgramBuilder ()
phi ty id (bbidl, idl) (bbidr, idr) = do
  loc <- builderLocIncr
  appendPhi (Phi loc ty (Id id) (bbidl, Id idl) (bbidr, Id idr))

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
-- 
-- -- ========================
-- -- CHOOSE YOUR PROGRAM HERE
-- -- ========================
pcur :: Program
pcur = pIf

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

