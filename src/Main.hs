{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M
import qualified Data.Set as S
import Data.List (intercalate, nub)
import Data.Semigroup
import qualified Control.Monad.State as ST
import Data.Foldable
import Control.Applicative
import Data.Void
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import Control.Exception (assert)

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

data LiftedLattice a = LL a | LLBot | LLTop deriving(Eq, Ord, Functor)

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
data ToppedLattice a = TLTop | TL a deriving (Eq, Ord, Functor)

instance Show a => Show (ToppedLattice a) where
  show TLTop = "T"
  show (TL a) = show a

data BottomedLattice a = TLBot | TB a deriving(Eq, Ord, Functor)

instance Show a => Show (BottomedLattice a) where
  show TLBot = "_|_"
  show (TB a) = show a


-- A map based representation of a function (a -> b), which on partial
-- missing keys returns _|_
data SemiMeetMap k v = LM (M.Map k v)  deriving (Eq, Ord, Functor)

-- Insert a regular value into a lattice map
insert :: Ord k => k -> v -> SemiMeetMap k v -> SemiMeetMap k v
insert k v (LM m) = LM $ M.insert k v m

-- pointwise produce of two lattice maps
-- *NOTE: only contains a value if both the first and second map have a value
-- for it.
-- *TODO: this is currently borked, in that if EITHER v or w are Top, the full
-- thing becomes top. Fix this next.
lmproduct :: Ord k => SemiMeetMap k v -> SemiMeetMap k w -> SemiMeetMap k (v, w)
lmproduct (LM m) (LM m') = undefined
--  let
--    missingm' = M.dropMissing
--    missingm =  M.dropMissing
--    merger = M.zipWithMatched (\k tx ty -> case (tx, ty) of
--                                                (TL x, TL y) -> TL (x, y)
--                                                _ -> TLTop)
-- in LM $ M.merge missingm' missingm merger m m'
lmproduct _ _ = error "undefined so far"

adjust :: Ord k => k -> (v -> v) -> SemiMeetMap k v -> SemiMeetMap k v
adjust k f (LM m) = LM $ M.adjust f k m

(!!!) :: (Ord k, SemiMeet v) => SemiMeetMap k v -> k -> v
(!!!) (LM m) k = case m M.!? k of
                   Just v -> v
                   Nothing -> bottom


(!!?) :: Ord k => SemiMeetMap k v -> k -> Maybe v
(!!?) (LM m) k = m M.!? k 

lmfromlist :: Ord k => [(k, v)] -> SemiMeetMap k v
lmfromlist kvs = LM $ M.fromList [(k, v) | (k, v) <- kvs]

lmempty :: SemiMeetMap k v 
lmempty = LM $ M.empty

lmtolist :: Ord k => SemiMeetMap k v -> [(k, v)]
lmtolist (LM m) = M.toList m

instance (Ord k, Show k, Show v) => Show (SemiMeetMap k v) where
  show (LM m) = show $ [(k, m M.! k) | k <- M.keys m]


instance (Ord k, Pretty k, Pretty v) => Pretty (SemiMeetMap k v) where
  pretty (LM m) =  vcat $ [pretty k <+> pretty "->" <+> pretty (m M.! k) | k <- M.keys m]

instance SemiMeet v => SemiMeet (SemiMeetMap k v) where
  bottom = LM M.empty
  meet _ _ = error "TODO: define meet"

-- Helper to repeat till fixpoint
-- ===============================


repeatTillFix :: (Eq a) =>  (a -> a) -> a -> [a]
repeatTillFix f a =
  let a' = f a in
  if a == a' then [a] else a:repeatTillFix f a'


-- repeat till fixpoint, or the max count
repeatTillFixDebug :: Eq a => Int -> (a -> a) -> a -> [a]
repeatTillFixDebug 0 f a = [a]
repeatTillFixDebug n f a = 
  let a' = f a in if a' == a then [a] else a': repeatTillFixDebug (n - 1) f a'

-- Program syntax
-- ==============

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

data Expr = EInt Int | EBool Bool  | EBinop Binop Expr Expr | EId Id
  deriving(Eq)

instance Show Expr where
    show (EInt i) = show i
    show (EBool b) = show b
    show (EId id) = show id
    show (EBinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Pretty Expr where
  pretty (EInt i) = pretty i
  pretty (EBool b) = pretty b
  pretty (EId id) = pretty id
  pretty (EBinop op e1 e2) = parens $ pretty op <+> pretty e1 <+> pretty e2


-- program counter, positioned *after* the ith instruction.
data PC = PC { unPC :: Int } deriving(Eq, Ord)
instance Show PC where
  show (PC pc) = "pc:" ++ show pc

instance Pretty PC where
  pretty = pretty . show

pcincr :: PC -> PC
pcincr (PC i) = PC (i + 1)

pcinit :: PC
pcinit = PC 0

-- Statements of the language
data Stmt = Assign PC Id Expr
            | If PC Id Stmt Stmt -- branch value id, true branch, false branch
            | While PC Id Stmt  PC -- while cond stmt, pc of entry, pc of exit
            | Seq Stmt Stmt
            | Skip PC deriving(Eq)

-- Return the PC of the first statement in the block
stmtPCStart :: Stmt -> PC
stmtPCStart (Assign pc _ _)  = pc
stmtPCStart (If pc _ _ _) = pc
stmtPCStart (While pc _ _ _) = pc
stmtPCStart (Seq s1 _) = stmtPCStart s1
stmtPCStart (Skip pc) = pc


-- Return the PC of the last statement in the block
stmtPCEnd :: Stmt -> PC
stmtPCEnd (Assign pc _ _)  = pc
stmtPCEnd (If pc _ _ _) = pc
stmtPCEnd (While _ _ _ pc) = pc
stmtPCEnd (Seq _ s2) = stmtPCEnd s2
stmtPCEnd (Skip pc) = pc

instance Show Stmt where
  show (Assign pc id e) = show pc ++ ":" ++ "(= " ++  show id ++ " " ++ show e ++  ")"
  show (If pc cond t e) = show pc ++ ":" ++ "(if " ++ show cond ++ " " ++ show t ++ " " ++ show e ++ ")"
  show (While pc cond s pc') = show pc ++ ":" ++ "(while " ++ show cond ++ " " ++ show s ++ ")" ++ show pc' ++ ":END WHILE"
  show (Seq s1 s2) =  show s1 ++ ";;" ++ show s2
  show (Skip pc) = show pc ++ ":" ++ "done"

instance Pretty Stmt where
  pretty s@(Assign pc id e) = pretty pc <+> (parens $ pretty "=" <+> pretty id <+> pretty e)
  pretty s@(If pc cond t e) = pretty pc <+> (parens $ pretty "if" <+> pretty cond <+> indent 1 (line <> pretty t <> line <> pretty e))
  pretty (Seq s1 s2) =  pretty s1 <> line <> pretty s2
  pretty (While pc cond s pc') = 
    pretty pc <+> 
      (parens $ 
        pretty "(while" <+> 
          pretty cond <+> 
            indent 1 (line <> pretty s <> line <> pretty pc' <+> pretty "ENDWHILE"))
  pretty (Skip pc) = pretty pc <+> pretty "Skip"

-- A Program is a top level statement
type Program = Stmt 




-- Language semantics
-- ==================

-- Environments of the language
type Env = (M.Map Id Int)

-- Initial env
envBegin :: Env
envBegin = M.empty

-- Expression evaluation
exprEval :: Expr -> Env -> Int
exprEval (EInt i) _ =  i
exprEval (EBool b) _ =  if b then 1 else 0
exprEval (EId id) env = env M.! id
exprEval (EBinop op e1 e2) env = exprEval e1 env `opimpl` exprEval e2 env where
  opimpl = case op of
             Add -> (+)
             Lt -> (\a b -> if a < b then 1 else 0)


-- Semantics of a Stmt, taking a single step through the execution.
stmtSingleStep :: Stmt -> Env -> Env
stmtSingleStep (Assign _ id e) env = M.insert id (exprEval e env) env
stmtSingleStep (If _ cid s s') env = 
  if (env M.! cid) == 1
  then stmtSingleStep s env
  else stmtSingleStep s' env
stmtSingleStep w@(While _ cid s _) env =
  if (env M.! cid == 1)
  then stmtSingleStep s env
  else env
       
stmtSingleStep (Seq s1 s2) env = stmtSingleStep s2 (stmtSingleStep s1 env)
stmtSingleStep (Skip _) env = env

  -- Execute the statement with respect to the semantics
stmtExec :: Stmt -> Env -> Env
stmtExec (Assign _ id e) env = M.insert id (exprEval e env) env
stmtExec (If _ cid s s') env = 
  if (env M.! cid) == 1
  then stmtExec s env
  else stmtExec s' env
stmtExec w@(While _ cid s _) env =
  if (env M.! cid == 1)
  then stmtExec w (stmtExec s env)
  else env

stmtExec (Seq s1 s2) env = stmtExec s2 (stmtExec s1 env)
stmtExec (Skip _) env = env

--  Collecting semantics Framework
-- ===============================

type CSemEnv v = SemiMeetMap Id v

data CSemDefn v = CSemDefn {
  -- the value of `true` that is used for conditionals in the environment
  csemDefnValIsTrue :: v -> Bool,
  csemDefnStmtSingleStep :: Stmt -> CSemEnv v -> CSemEnv v 
}

csemenvbegin :: CSemEnv v
csemenvbegin = lmempty


type PC2CSemEnv v = M.Map PC (CSemEnv v)
type CSem v = S.Set (PC2CSemEnv v)

pc2csemenvShow :: Show v => PC2CSemEnv v -> String
pc2csemenvShow m = fold $ map (\(k, v) -> show k ++ " -> " ++ show v ++ "\n") (M.toList m)


-- Propogate the value of the environment at the first PC to the second PC.
-- Needed to implicitly simulate the flow graph.
statePropogate :: PC -> PC -> (CSemEnv v -> CSemEnv v) -> PC2CSemEnv v -> PC2CSemEnv v
statePropogate pc pc' f st = let e = st M.! pc  in
  M.insert pc' (f e) st


-- Initial collecting semantics, which contains one PC2Env.
-- This initial PC2Env maps every PC to the empty environment
initCollectingSem :: Program -> CSem v
initCollectingSem p = let 
  finalpc = unPC (stmtPCEnd p) + 1
  st = M.fromList (zip (map PC [-1..finalpc]) (repeat csemenvbegin)) 
  in S.singleton $ st

-- propogate the value of an environment at the first PC to the second
-- PC across all states.
collectingSemPropogate :: Ord v => PC -> PC -> (CSemEnv v -> CSemEnv v) -> CSem v -> CSem v
collectingSemPropogate pc pc' f = S.map (statePropogate pc pc' f)

-- affect the statement, by borrowing the PC2Env from the given PC
stmtCollect :: (SemiMeet v, Ord v) => CSemDefn v -> PC -> Stmt -> CSem v -> CSem v

-- flow order:
-- 1. pre -> entry,  backedge -> entry
-- 3. entry ---loop-> loop final PC
-- 4. loop final PC -> exit block
stmtCollect csemDefn pcold (While pc condid loop pc') csem =
  let -- filter_allowed_iter :: CSem v -> CSem v
      filter_allowed_iter csem = S.filter (\s -> csemDefnValIsTrue csemDefn ((s M.! pc) !!! condid)) csem
  
      -- pre_to_entry :: CSem v -> CSem v
      pre_to_entry = filter_allowed_iter . collectingSemPropogate pcold pc id


      -- exit block to entry 
      -- exit_to_entry :: CSem v -> CSem v
      exit_to_entry = filter_allowed_iter . collectingSemPropogate pc' pc id


      -- everything entering the entry block 
      -- all_to_entry :: CSem v -> CSem v
      all_to_entry csem = (pre_to_entry csem) `S.union` exit_to_entry csem 

      -- loop execution
      -- entry_to_exit :: CSem v -> CSem v
      entry_to_exit csem =  stmtCollect csemDefn pc loop (all_to_entry csem)

      -- final statement in while to exit block
      -- final_to_exit :: CSem v -> CSem v
      final_to_exit csem = collectingSemPropogate (stmtPCEnd loop) pc' id (entry_to_exit csem)

      -- f :: CSem v -> CSem v
      f csem = final_to_exit csem

   in (fold (repeatTillFix f csem))

stmtCollect csemDefn pc (Seq s1 s2) csem =
  let csem' = stmtCollect csemDefn pc s1 csem
      pc' = stmtPCEnd s1 in
    stmtCollect csemDefn pc' s2 csem'

-- TODO: merge code of Assign, Skip?
stmtCollect csemDefn pcold s@(Assign _ _ _) csem =
  (collectingSemPropogate pcold (stmtPCStart s) (csemDefnStmtSingleStep csemDefn s)) $ csem


stmtCollect csemDefn pcold s@(Skip _) csem = 
  (collectingSemPropogate pcold (stmtPCStart s) (csemDefnStmtSingleStep csemDefn s)) $ csem

-- Fixpoint of stmtCollect
stmtCollectFix :: (SemiMeet v, Ord v) => CSemDefn v -> PC -> Stmt -> CSem v -> CSem v
stmtCollectFix csemDefn pc s csem = fold $ repeatTillFix (stmtCollect csemDefn pc s) csem


-- Abstract domain 1 - concrete functions
-- ======================================

-- type representing loop backedge taken counts
type LoopBTC v = M.Map Id v 

-- maps identifiers to functions from loop trip counts to values
data Id2LoopFn v = Id2LoopFn
  { 
    runId2LoopFn :: Id -> LoopBTC v -> v
    -- runId2Limits :: M.Map Id (Interval v) 
  }



-- push a tuple into the second element
pushTupleInList :: (a, [b]) -> [(a, b)]
pushTupleInList abs = map ((fst abs), ) (snd abs)

listTuplesCollect :: (Eq a, Ord a) => [(a, b)] -> M.Map a [b]
listTuplesCollect abs = 
  let abs' = map (\(a, b) -> (a, [b])) abs 
  in M.fromListWith (++) abs'


-- Explode the collecting semantics object to a gargantuan list so we can
-- then rearrange it
-- Collectingsem :: S.Set (M.Map PC (M.Map Id ToppedLattice Int))
collectingSemExplode :: CSem v -> [(Id, (PC, v))]
collectingSemExplode csem = 
  let -- set2list :: [PC2CSemEnv v]
      set2list = S.toList csem
      
      -- pc2aenvlist :: [[(PC, CSemEnv v)]]
      pc2aenvlist = map M.toList set2list

      -- aenvlist :: [[(PC, [(Id, ToppedLattice v)])]]
      aenvlist = (map . map) ((\(pc, aenv) -> (pc, lmtolist aenv))) pc2aenvlist 

      -- flatten1 :: [(PC, [(Id, ToppedLattice v)])]
      flatten1 = concat aenvlist

      -- tuples :: [(PC, (Id, ToppedLattice v))]
      tuples = concat $ map pushTupleInList flatten1

      -- tuples' :: [(Id, (PC, ToppedLattice v))]
      tuples' = map (\(pc, (id, val)) -> (id, (pc, val))) tuples
  in tuples'


-- Find the assignment statement that first assigns to the ID.
-- TODO: make sure our language is SSA. For now, it returns the *first* assignment
-- to a variable.
idFindAssign :: Id -> Program -> Maybe Stmt
idFindAssign id s@(Assign _ aid _) = 
  if id == aid 
     then Just s
     else Nothing

idFindAssign id (Seq s1 s2) = idFindAssign id s1 <|> idFindAssign id s2
idFindAssign id while@(While _ condid sinner _)  = 
  idFindAssign id sinner
idFindAssign id (If _ _ s1 s2) = idFindAssign id s1 <|> idFindAssign id s2

-- check if the given AEnv has loop variables at these values
aenvHasLoopValues :: (Eq v) => LoopBTC v -> CSemEnv v -> Bool
aenvHasLoopValues btcs aenv = 
  all (\(id, val) -> aenv !!? id == Just val) (M.toList btcs)

-- check if the given pc2env has loop variables at these values at some PC
pc2envHasLoopValues :: (Eq v) => PC -> LoopBTC v -> PC2CSemEnv v -> Bool
pc2envHasLoopValues pc btcs pc2env = 
  let aenv = (pc2env M.! pc) in
      aenvHasLoopValues btcs aenv

-- Provide the instance in the collecting sematics that has these 
-- values of backedge taken counts at the given PC
csemAtLoopValues :: (Lattice v, Ord v, Eq v) => CSem v -> PC -> LoopBTC v -> Id -> v
csemAtLoopValues csem pc btcs id = 
  let 
  -- pick all valid pc2envs
  -- candidates :: S.Set (PC2CSemEnv v)
  candidates =  S.filter (pc2envHasLoopValues pc btcs) csem 

  -- out of these, pick anll AEnvs that work
  -- vals :: S.Set (LiftedLattice v)
  vals = S.map (\candidate -> (candidate M.! pc) !!! id) candidates
  in
    foldl join bottom vals


-- Abstraction function to Id2LoopFn from the collecting semantics
alphacsem :: (Lattice v, Ord v) => Program -> CSem v -> Id2LoopFn v
alphacsem p csem = 
  let fn id btcs = let Just (assign) = idFindAssign id p in csemAtLoopValues csem (stmtPCStart assign) btcs id
      -- limits :: M.Map Id (Interval v)
      -- limits = M.fromListWith (<>) (map (\(id, (pc, TL val)) -> (id, intervalClosed val)) (collectingSemExplode csem))
  in Id2LoopFn fn

gammacsem :: Program -> Id2LoopFn v -> CSem v
gammacsem p id2loop = undefined



-- Concrete domain 1 - concrete collecting semantics of Int
-- ========================================================

concreteCSem :: CSemDefn (LiftedLattice Int)
concreteCSem = CSemDefn valTrueA stmtSingleStepA
    where
      valTrueA :: LiftedLattice Int -> Bool
      valTrueA (LL 1) = True
      valTrueA _ = False
  
      exprEvalA :: Expr -> CSemEnv (LiftedLattice Int) -> LiftedLattice Int
      exprEvalA (EInt i) _ =  LL i
      exprEvalA (EBool b) _ =  if b then LL 1 else LL 0
      exprEvalA (EId id) env = env !!! id
      exprEvalA (EBinop op e1 e2) env = 
        liftLL2 opimpl (exprEvalA e1 env) (exprEvalA e2 env) where
          opimpl = case op of
                     Add -> (+)
                     Lt -> (\a b -> if a < b then 1 else 0)
      
      stmtSingleStepA :: Stmt -> CSemEnv (LiftedLattice Int) -> CSemEnv (LiftedLattice Int)
      stmtSingleStepA (Assign _ id e) env = insert id (exprEvalA e env) env
      stmtSingleStepA (If _ cid s s') env = if (env !!! cid) == LL 1
                                       then stmtSingleStepA s env
                                       else stmtSingleStepA s' env
      stmtSingleStepA w@(While _ cid s _) env =
        if (env !!! cid == LL 1)
          then stmtSingleStepA s env
          else env
         
      stmtSingleStepA (Seq s1 s2) env = stmtSingleStepA s2 (stmtSingleStepA s1 env)
      stmtSingleStepA (Skip _) env = env
  

-- Concrete domain 2 - concrete collecting semantics of Symbol
-- ================================================
-- Note the problem with abstract domain 1: We are unable to extract out
-- relations between variables. However, for us to perform loop acceleration,
-- what we actually care about is the ability to infer relations between
-- variables. So, we create a symbolic domain, so that we may derive equations
-- of the form [x = 1, x = x + 1] which we can then accelerate.

data Sym = SymVal Int | SymSym Id | SymBinop Binop Sym Sym deriving(Eq, Ord)

-- constant folding for symbols
symConstantFold :: Sym -> Sym
symConstantFold (SymBinop op s1 s2) = 
  let 
    s1' = symConstantFold s1
    s2' = symConstantFold s2
    in case (s1', s2') of
        (SymVal i1, SymVal i2) -> 
          case op of
            Add -> SymVal (i1 + i2)
            Lt -> SymVal (if i1 < i2 then 1 else 0)
        _ -> SymBinop op s1' s2'
symConstantFold s = s


-- Values to make opaque at a given PC
data OpaqueVals = OpaqueVals (M.Map PC [Id])

-- Make the environment opaque for the given values in OpaqueVals at the 
-- current PC
envOpaqify :: PC -> OpaqueVals -> CSemEnv (LiftedLattice Sym) -> CSemEnv (LiftedLattice Sym)
envOpaqify pc (OpaqueVals ovs) env =
  case ovs M.!? pc of
    Just ids -> foldl (\env id -> insert id (LL (SymSym id)) env) env ids
    Nothing -> env


-- Collecting semantics of symbolic execution
symbolCSem :: OpaqueVals -> CSemDefn (LiftedLattice Sym)
symbolCSem ovs = CSemDefn valTrueA stmtSingleStepOpaqify
  where
    valTrueA :: LiftedLattice Sym -> Bool
    valTrueA (LL (SymVal 1)) = True
    valTrueA _ = False

    exprEvalA :: Expr -> CSemEnv (LiftedLattice Sym) -> LiftedLattice Sym
    exprEvalA (EInt i) _ =  LL (SymVal i)
    exprEvalA (EBool b) _ =  if b then LL (SymVal 1) else LL (SymVal 0)
    exprEvalA (EId id) env = env !!! id
    exprEvalA (EBinop op e1 e2) env = 
      liftLL2 opimpl (exprEvalA e1 env) (exprEvalA e2 env) where
        opimpl v1 v2 = symConstantFold $ SymBinop op v1 v2

    -- abstract semantics that respects opacity
    stmtSingleStepOpaqify :: Stmt -> CSemEnv (LiftedLattice Sym) -> CSemEnv (LiftedLattice Sym)
    stmtSingleStepOpaqify s env = 
      stmtSingleStepA s (envOpaqify (stmtPCStart s) ovs env)

    -- raw abstract semantics
    stmtSingleStepA :: Stmt -> CSemEnv (LiftedLattice Sym) -> CSemEnv (LiftedLattice Sym)
    stmtSingleStepA (Assign _ id e) env = insert id (exprEvalA e env) env
    stmtSingleStepA (If _ cid s s') env = if (env !!! cid) == LL (SymVal 1)
                                     then stmtSingleStepA s env
                                     else stmtSingleStepA s' env
    stmtSingleStepA w@(While pc cid s _) env = error "undefined, never executed"
    stmtSingleStepA (Seq s1 s2) env = stmtSingleStepA s2 (stmtSingleStepA s1 env)
    stmtSingleStepA (Skip _) env = env


instance Show Sym where
  show (SymVal val) = show val
  show (SymSym id) = show id
  show (SymBinop op sym sym') = 
   "(" ++ show op ++ " " ++ show sym ++ " " ++ show sym' ++ ")"

instance Pretty Sym where
  pretty (SymBinop op sym sym') =
    parens $ pretty op <+> pretty sym <+> pretty sym'
  pretty sym = pretty (show sym)


-- Concrete Domain 3 - product domain of symbols and concrete values
-- =================================================================
-- We construct a product domain, so that we are able to perform loop iterations
-- which the symbolic domain gets stuck on, while still being able to collect
-- symbolic information, which the concrete domain cannot do.

-- stmtSingleStepProduct :: 
--   (Stmt -> CSemEnv v -> CSemEnv v) 
--   -> (Stmt -> CSemEnv w -> CSemEnv w)
--   -> Stmt -> CSemEnv (v, w) -> CSemEnv (v, w)
-- stmtSingleStepProduct f1 f2 s env = 
--   lmproduct (f1 s (fmap fst env)) (f2 s (fmap snd env))

-- Abstract domain 3 - presburger functions
-- ========================================

-- Our abstract value is an affine function of loop trip counts.
-- type representing affine function of identifiers
-- contains a constant value, and a mapping from identifiers to their
-- respective coefficients in the affine function.
-- terms in the affine function
data AFFTerm = AFNConst | AFNVar Id
-- affine function maps terms to their respective coefficients.
data AFF = AFN (AFFTerm -> LiftedLattice Int)

-- NOTE: this is *not enough*. Our abstract domain should contain *piecewise*
-- affine functions, so that we can build up loops in stages. Our acceleration
-- then finds an equivalent formulation of this affine function

-- lifted integers for the interval domain
data IInt = IInt Int | IInfty | IMinusInfty deriving (Eq, Show)
instance Ord IInt where
  IMinusInfty <= IMinusInfty = True
  IMinusInfty <= _ = True
  _ <= IMinusInfty = False

  IInfty <= IInfty = True
  _ <= IInfty = True
  IInfty <= _ = False

  (IInt x) <= (IInt y) = x <= y

-- interval domain
data Interval a = Interval a a | IEmpty deriving(Eq)

-- lift a value to a closed interval
intervalClosed :: a -> Interval a
intervalClosed a = Interval a a

instance Show a => Show (Interval a) where
  show IEmpty = "]["
  show (Interval a b) = "[" ++ show a ++ ", " ++ show b ++ "]"

-- Interval joining
instance Ord a => Semigroup (Interval a) where
  x <> IEmpty = x
  IEmpty <> x = x
  (Interval x x') <> (Interval y y') = 
    let minlist is = foldl1 min is
        maxlist is = foldl1 max is
     in Interval (minlist [x, x', y, y']) (maxlist [x, x', y, y'])

        
-- Monoid instance
instance Ord a => Monoid (Interval a) where
  mempty = IEmpty
  mappend = (<>)


data PWAFF = PWAFF

-- abstracter
alpha2 :: Id2LoopFn v -> PWAFF
alpha2 = undefined

-- concretizer
gamma2 :: PWAFF -> Id2LoopFn v
gamma2= undefined

-- concrete semantic transformer, that takes a semantics and incrementally
-- builds up on it. The final semantics is the least fixpoint of this function.
csem2 :: Program -> Id2LoopFn v -> Id2LoopFn v
csem2 = undefined

-- abstract semantics in terms of concrete semantics
asem2 :: Program -> PWAFF -> PWAFF
asem2 p = alpha2 . csem2 p . gamma2

-- Example
-- =======

data StmtBuilder = StmtBuilder { sbpc :: PC }

sbPCIncr :: ST.State StmtBuilder ()
sbPCIncr = ST.modify  (\s -> s { sbpc = (pcincr (sbpc s)) })

  

stmtBuild :: ST.State StmtBuilder Stmt -> Stmt
stmtBuild st = let begin = StmtBuilder (pcincr pcinit) in 
             ST.evalState st begin

stmtSequence :: [ST.State StmtBuilder Stmt] -> ST.State StmtBuilder Stmt
stmtSequence [x] = x
stmtSequence (x:xs) = do
  x' <- x
  xs' <- stmtSequence xs
  return $ Seq x' xs'

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

assign :: ToExpr a => String -> a -> ST.State StmtBuilder Stmt
assign id a =
  do
    pc <- ST.gets sbpc
    let s = Assign pc (Id id) (toexpr a)
    sbPCIncr
    return s

skip :: ST.State StmtBuilder Stmt
skip = do
  pc <- ST.gets sbpc
  let s = Skip pc
  sbPCIncr
  return s


while :: String -> ST.State StmtBuilder Stmt -> ST.State StmtBuilder Stmt
while idcond loopbuilder = do
  pc <- ST.gets sbpc
  sbPCIncr
  loop <- loopbuilder
  pc' <- ST.gets sbpc
  sbPCIncr

  let l = While pc (Id idcond) loop pc'
  return l

  
(+.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(+.) a b = EBinop Add (toexpr a) (toexpr b)


(<.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(<.) a b = EBinop Lt (toexpr a) (toexpr b)


program :: (Stmt, OpaqueVals)
program = (stmtBuild . stmtSequence $ [
  assign "x" (EInt 1),
  assign "x_lt_5" ("x" <. EInt 5),
  while "x_lt_5" $ stmtSequence $ [
      skip,
      assign "x" ("x" +.  EInt 1),
      assign "x_lt_5" ("x" <. EInt 5)
  ],
  assign "beta" ("x" +. EInt (-5))],
 OpaqueVals (M.fromList $ [(PC 4, [Id "x"])]))

program2 :: (Stmt, OpaqueVals)
program2 = (stmtBuild . stmtSequence $ [
  assign "x" (EInt 1),
  assign "x_lt_5" ("x" <. EInt 5),
  while "x_lt_5" $ stmtSequence $ [
      skip,
      assign "x" ("x" +.  EInt 1),
      assign "x_lt_5" ("x" <. EInt 5),

      assign "y" (EInt 2),
      assign "y_lt_10" ("y" <. EInt 10),
      while "y_lt_10" $ stmtSequence $ [
        assign "y" ("y" +.  EInt 5),
        assign "y_lt_10" ("y" <. EInt 10)
    ],
    assign "alpha" ("y" +. EInt (-12))
  ],
  assign "beta" ("x" +. EInt (-5))],
 OpaqueVals (M.fromList $ [(PC 4, [Id "x"])]))

-- Program on which main runs
pcur :: Stmt
pcur = fst program


curToOpaqify :: OpaqueVals
curToOpaqify = snd program

curCSemInt :: CSem (LiftedLattice Int)
curCSemInt = stmtCollectFix concreteCSem (PC (-1)) pcur (initCollectingSem pcur)


curCSemSym :: CSem (LiftedLattice Sym)
curCSemSym = stmtCollectFix (symbolCSem curToOpaqify) (PC (-1)) pcur (initCollectingSem pcur)

curAbs1 :: Id2LoopFn (LiftedLattice Int)
curAbs1 = alphacsem pcur curCSemInt

main :: IO ()
main = do
    putStrLn "***program***"
    putDocW 80 (pretty pcur)
    putStrLn ""
    
    putStrLn "***program output***"
    let outenv =  (stmtExec pcur) envBegin
    print outenv


    putStrLn "***collecting semantics (concrete):***"
    forM_  (S.toList curCSemInt) (\m -> (putStr . pc2csemenvShow $ m) >> putStrLn "---")


    putStrLn "***collecting semantics (symbol):***"
    forM_  (S.toList curCSemSym) (\m -> (putStr . pc2csemenvShow $ m) >> putStrLn "---")

    putStrLn "***Abstract semantics 1: concrete loop functions***"
