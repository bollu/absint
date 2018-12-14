{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where
import qualified Data.Map.Strict as M
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
class Lattice a where
  bottom :: a
  top :: a
  join :: a -> a -> a
  meet :: a -> a -> a

instance Lattice a => Lattice (Maybe a) where
  bottom = Nothing
  top = Just top
  join Nothing a = a
  join a Nothing = a
  join (Just a) (Just b) = Just (join a b)

  meet Nothing _ = Nothing
  meet _ Nothing = Nothing
  meet (Just a) (Just b) = Just (meet a b)

instance (Lattice a , Lattice b) => Lattice (a, b) where
  bottom = (bottom, bottom)
  top = (top, top)
  join (a, b) (a', b') = (a `join` a', b `join` b')
  meet (a, b) (a', b') = (a `meet` a', b `meet` b')

data LiftedLattice a = LL a | LLBot | LLTop deriving(Eq, Ord, Functor)

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


data ToppedLattice a = TLTop | TL a deriving (Eq, Ord, Functor)

instance Show a => Show (ToppedLattice a) where
  show TLTop = "T"
  show (TL a) = show a


-- Lift any element pointwise onto a lattice
instance Eq a => Lattice (LiftedLattice a) where
  bottom = LLBot
  top = LLTop

  join LLBot a = a
  join a LLBot = a
  join LLTop _ = LLTop
  join _ LLTop = LLTop
  join (LL a) (LL b) = if a == b then LL a else LLTop

  meet LLBot _ = LLBot
  meet _ LLBot = LLBot
  meet a LLTop = a
  meet LLTop a = a
  meet (LL a) (LL b) = if a == b then LL a else LLBot


instance Lattice o => Lattice (i -> o) where
  bottom = const bottom
  top = const top
  join f g = \i -> f i `join` g i
  meet f g = \i -> f i `meet` g i


class Lattice a => BooleanAlgebra a where
  complement :: a -> a


-- implication in the boolean algebra
imply :: BooleanAlgebra a => a -> a -> a
imply a b = (complement a) `join` b

-- symbol
(===>) :: BooleanAlgebra a => a -> a -> a
(===>) = imply

data LatticeMap k v = LM (M.Map k (ToppedLattice v)) | LMTop deriving (Eq, Ord)

-- Insert a regular value into a lattice map
insert :: Ord k => k -> v -> LatticeMap k v -> LatticeMap k v
insert k v LMTop = LMTop
insert k v (LM m) = LM $ M.insert k (TL v) m

-- insert a lattice value into a LatticeMap
insert' :: Ord k => k -> LiftedLattice v -> LatticeMap k v -> LatticeMap k v
insert' _ _ LMTop = LMTop
insert' _ LLBot m = m
insert' k LLTop (LM m) = LM $ M.insert k TLTop m
insert' k (LL v) (LM m) = LM $ M.insert k (TL v) m

adjust :: Ord k => k -> (v -> v) -> LatticeMap k v -> LatticeMap k v
adjust _ _ LMTop = LMTop
adjust k f (LM m) = LM $ M.adjust (fmap f) k m

(!!!) :: Ord k => LatticeMap k v -> k -> LiftedLattice v
(!!!) (LM m) k = case m M.!? k of
                  Just (TL v) -> LL v
                  Just TLTop -> LLTop
                  Nothing -> LLBot
(!!!) LMTop k = LLTop

lmfromlist :: Ord k => [(k, v)] -> LatticeMap k v
lmfromlist kvs = LM $ M.fromList [(k, TL v) | (k, v) <- kvs]

lmempty :: LatticeMap k v 
lmempty = LM $ M.empty

lmtolist :: Ord k => LatticeMap k v -> [(k, ToppedLattice v)]
lmtolist LMTop = error "unable to convert LMTop to a list"
lmtolist (LM m) = M.toList m

instance (Ord k, Show k, Show v) => Show (LatticeMap k v) where
  show (LM m) = show $ [(k, m M.! k) | k <- M.keys m]
  show LMTop = "_ -> T"

instance Ord k => Lattice (LatticeMap k v) where
  bottom = LM M.empty
  top = LMTop

  -- if they're both defined, give up
  join _ LMTop = LMTop
  join LMTop _ = LMTop
  join (LM m) (LM m') = LM $ M.unionWith (\_ _ -> TLTop) m m'

  meet a LMTop = a
  meet LMTop a = a
  meet _ _ = error "trying to meet two maps defined at the same point"

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
data Binop = Add | Lt deriving(Eq)
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
data PC = PC Int deriving(Eq, Ord)
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
-- Fixpoint of these semantics are the actual bigstep semantics
stmtSingleStep :: Stmt -> Env -> Env
stmtSingleStep (Assign _ id e) env = M.insert id (exprEval e env) env
stmtSingleStep (If _ cid s s') env = if (env M.! cid) == 1
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
stmtExec (s@(Assign _ _ _)) env = stmtSingleStep s env
stmtExec (s@(If _ _ _ _)) env = stmtSingleStep s env
stmtExec (s@(Seq _ _)) env = stmtSingleStep s env
stmtExec (s@(Skip _)) env = stmtSingleStep s env
stmtExec (s@(While _ cid loop _)) env = last $
  repeatTillFix (stmtSingleStep loop) env


-- Concrete domain - Collecting semantics
-- ======================================
type AEnv = LatticeMap Id Int

aenvbegin :: AEnv
aenvbegin = lmempty

-- Abstract version of expression evaluation
exprEvalA :: Expr -> AEnv -> LiftedLattice Int
exprEvalA (EInt i) _ =  LL i
exprEvalA (EBool b) _ =  if b then LL 1 else LL 0
exprEvalA (EId id) env = env !!! id
exprEvalA (EBinop op e1 e2) env = 
  liftLL2 opimpl (exprEvalA e1 env) (exprEvalA e2 env) where
    opimpl = case op of
               Add -> (+)
               Lt -> (\a b -> if a < b then 1 else 0)

-- Abstract version of statement single step
stmtSingleStepA :: Stmt -> AEnv -> AEnv
stmtSingleStepA (Assign _ id e) env = insert' id (exprEvalA e env) env
stmtSingleStepA (If _ cid s s') env = if (env !!! cid) == LL 1
                                 then stmtSingleStepA s env
                                 else stmtSingleStepA s' env
stmtSingleStepA w@(While _ cid s _) env =
  if (env !!! cid == LL 1)
    then stmtSingleStepA s env
    else env
       
stmtSingleStepA (Seq s1 s2) env = stmtSingleStepA s2 (stmtSingleStepA s1 env)
stmtSingleStepA (Skip _) env = env

type PC2Env = M.Map PC AEnv

pc2envshow :: PC2Env -> String
pc2envshow m = fold $ map (\(k, v) -> show k ++ " -> " ++ show v ++ "\n") (M.toList m)

-- Propogate the value of the environment at the first PC to the second PC.
-- Needed to implicitly simulate the flow graph.
statePropogate :: PC -> PC -> (AEnv -> AEnv) -> PC2Env -> PC2Env
statePropogate pc pc' f st = let e = st M.! pc  in
  M.insert pc' (f e) st

-- a set of maps from program counters to environments
type CollectingSem = S.Set PC2Env

-- Initial collecting semantics, which contains one PC2Env.
-- This initial PC2Env maps every PC to the empty environment
initCollectingSem :: CollectingSem
initCollectingSem = let st = M.fromList (zip (map PC [-1..10]) (repeat aenvbegin)) in
  S.singleton $ st

-- propogate the value of an environment at the first PC to the second
-- PC across all states.
collectingSemPropogate :: PC -> PC -> (AEnv -> AEnv) -> CollectingSem -> CollectingSem
collectingSemPropogate pc pc' f = S.map (statePropogate pc pc' f)

-- affect the statement, by borrowing the PC2Env from the given PC
stmtCollect :: PC -> Stmt -> CollectingSem -> CollectingSem
stmtCollect pcold s@(Assign _ _ _) csem =
  (collectingSemPropogate pcold (stmtPCStart s) (stmtSingleStepA s)) $ csem

-- flow order:
-- 1. pre -> entry,  backedge -> entry
-- 3. entry ---loop-> loop final PC
-- 4. loop final PC -> exit block
stmtCollect pcold (While pc condid loop pc') csem =
  let filter_allowed_iter :: CollectingSem -> CollectingSem
      filter_allowed_iter csem = S.filter (\s -> (s M.! pc) !!! condid == LL 1) csem
  
      pre_to_entry :: CollectingSem -> CollectingSem
      pre_to_entry = filter_allowed_iter . collectingSemPropogate pcold pc id


      -- exit block to entry 
      exit_to_entry :: CollectingSem -> CollectingSem
      exit_to_entry = filter_allowed_iter . collectingSemPropogate pc' pc id


      -- everything entering the entry block 
      all_to_entry :: CollectingSem -> CollectingSem
      all_to_entry csem = (pre_to_entry csem) `S.union` exit_to_entry csem 

      -- loop execution
      entry_to_exit :: CollectingSem -> CollectingSem
      entry_to_exit csem =  stmtCollect pc loop (all_to_entry csem)

      -- final statement in while to exit block
      final_to_exit :: CollectingSem -> CollectingSem
      final_to_exit csem = collectingSemPropogate (stmtPCEnd loop) pc' id (entry_to_exit csem)

      f :: CollectingSem -> CollectingSem
      f csem = final_to_exit csem

   in f csem -- (fold (repeatTillFix f csem))

stmtCollect pc (Seq s1 s2) csem =
  let csem' = stmtCollect pc s1 csem
      pc' = stmtPCEnd s1 in
    stmtCollect pc' s2 csem'
stmtCollect pc (Skip _) csem = csem

-- Fixpoint of stmtCollect
stmtCollectFix :: PC -> Stmt -> CollectingSem -> CollectingSem
stmtCollectFix pc s csem = fold $ repeatTillFix (stmtCollect pc s) csem



-- Abstract domain 1 - concrete functions
-- ======================================

-- type representing loop backedge taken counts
type LoopBTC = M.Map Id Int 

-- maps identifiers to functions from loop trip counts to values
data Id2LoopFn = Id2LoopFn { runId2LoopFn :: Id -> LoopBTC -> (LiftedLattice Int), idLimits :: M.Map Id (Interval Int) }

-- A loop nest is identified by a trail of loop identifiers, from outermost
-- to innermost
newtype Loopnest = Loopnest [(Id, Stmt)] deriving(Eq, Show)

loopnestEmpty :: Loopnest
loopnestEmpty = Loopnest []

loopnestAddOuterLoop :: Id -> Stmt -> Loopnest -> Loopnest
loopnestAddOuterLoop id s (Loopnest nest) = Loopnest ((id, s):nest)

-- A loop nest of a single loop
loopnestInnermost :: Id -> Stmt -> Loopnest
loopnestInnermost id s = Loopnest [(id, s)]

-- collect loop nests in a statement
getLoopnests :: Stmt -> [Loopnest]
getLoopnests (Seq  s1 s2) = getLoopnests s1 ++ getLoopnests s2
getLoopnests s@(While pc condid body _) = 
  let lns = getLoopnests body
   in if null lns
         then [loopnestInnermost condid s]
         else map (loopnestAddOuterLoop condid s) lns
getLoopnests _ = []


type ID2PC2Vals = M.Map Id (M.Map PC (S.Set Int))


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
collectingSemExplode :: CollectingSem -> [(Id, (PC, ToppedLattice Int))]
collectingSemExplode csem = 
  let set2list :: [PC2Env]
      set2list = S.toList csem
      
      pc2aenvlist :: [[(PC, AEnv)]]
      pc2aenvlist = map M.toList set2list

      aenvlist :: [[(PC, [(Id, ToppedLattice Int)])]]
      aenvlist = (map . map) ((\(pc, aenv) -> (pc, lmtolist aenv))) pc2aenvlist 

      flatten1 :: [(PC, [(Id, ToppedLattice Int)])]
      flatten1 = concat aenvlist

      tuples :: [(PC, (Id, ToppedLattice Int))]
      tuples = concat $ map pushTupleInList flatten1

      tuples' :: [(Id, (PC, ToppedLattice Int))]
      tuples' = map (\(pc, (id, val)) -> (id, (pc, val))) tuples
  in tuples'


-- Find the assignment statement that first assigns to the ID.
-- TODO: make sure our language is SSA. For now, it returns the *first* assignment
-- to a variable.
idFindAssign :: Id -> Program -> Maybe (Stmt, Loopnest)
idFindAssign id s@(Assign _ aid _) = 
  if id == aid 
     then Just (s, loopnestEmpty) 
     else Nothing

idFindAssign id (Seq s1 s2) = idFindAssign id s1 <|> idFindAssign id s2

idFindAssign id while@(While _ condid sinner _)  = 
  fmap (\(s, ln) -> (s, loopnestAddOuterLoop condid while ln)) (idFindAssign id sinner)

idFindAssign id (If _ _ s1 s2) = idFindAssign id s1 <|> idFindAssign id s2

-- check if the given AEnv has loop variables at these values
aenvHasLoopValues :: LoopBTC -> AEnv -> Bool
aenvHasLoopValues btcs aenv = 
  all (\(id, val) -> aenv !!! id == LL val) (M.toList btcs)

-- check if the given pc2env has loop variables at these values at some PC
pc2envHasLoopValues :: PC -> LoopBTC -> PC2Env -> Bool
pc2envHasLoopValues pc btcs pc2env = 
  let aenv = (pc2env M.! pc) in
      aenvHasLoopValues btcs aenv

-- Provide the instance in the collecting sematics that has these 
-- values of backedge taken counts at the given PC
csemAtLoopValues :: CollectingSem -> PC -> LoopBTC -> Id -> LiftedLattice Int
csemAtLoopValues csem pc btcs id = 
  let 
  -- pick all valid pc2envs
  candidates :: S.Set PC2Env
  candidates =  S.filter (pc2envHasLoopValues pc btcs) csem 

  -- out of these, pick anll AEnvs that work
  vals :: S.Set (LiftedLattice Int)
  vals = S.map (\candidate -> (candidate M.! pc) !!! id) candidates
  in
    foldl join bottom vals


-- Abstraction function to Id2LoopFn from the collecting semantics
alpha1 :: Program -> CollectingSem -> Id2LoopFn
alpha1 p csem = 
  let loops = getLoopnests p 
      fn id btcs = let (Just (assign, nest)) = idFindAssign id p in csemAtLoopValues csem (stmtPCStart assign) btcs id
      limits :: M.Map Id (Interval Int)
      limits = M.fromListWith (<>) (map (\(id, (pc, TL val)) -> (id, intervalClosed val)) (collectingSemExplode csem))
  in Id2LoopFn fn limits



gamma1 :: Id2LoopFn -> CollectingSem
gamma1 = undefined


-- Abstract domain 2 - presburger functions
-- ========================================

-- -- our abstract value is an affine function of loop trip counts.
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
  IMinusInfty <= _ = True
  IMinusInfty <= IMinusInfty = True
  _ <= IMinusInfty = False

  _ <= IInfty = True
  IInfty <= IInfty = True
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
alpha2 :: Id2LoopFn -> PWAFF
alpha2 = undefined

-- concretizer
gamma2 :: PWAFF -> Id2LoopFn
gamma2= undefined

-- concrete semantic transformer, that takes a semantics and incrementally
-- builds up on it. The final semantics is the least fixpoint of this function.
csem2 :: Program -> Id2LoopFn -> Id2LoopFn
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


program :: Stmt
program = stmtBuild . stmtSequence $ [
  assign "x" (EInt 1),
  assign "y" (EInt 2),
  assign "x_lt_5" ("x" <. EInt 5),
  assign "x_lt_5_btc" (EInt (-1)),
  while "x_lt_5" $ stmtSequence $ [
      assign "x_lt_5_btc" ("x_lt_5_btc" +. (EInt 1)),
      assign "x_in_loop" "x",
      assign "x" ("x" +.  EInt 1),
      assign "x_lt_5" ("x" <. EInt 5)
  ],
  assign "z" ("x" +. EInt (-5))]

p :: Stmt
p = program

pcsem :: CollectingSem
pcsem = stmtCollectFix (PC (-1)) p initCollectingSem

pabs1 :: Id2LoopFn
pabs1 = alpha1 p pcsem

main :: IO ()
main = do
    putStrLn "***program***"
    putDocW 80 (pretty p)
    putStrLn ""
    
    putStrLn "***program output***"
    let outenv =  (stmtExec p) envBegin
    print outenv


    putStrLn "***collecting semantics:***"
    forM_  (S.toList pcsem) (\m -> (putStr . pc2envshow $ m) >> putStrLn "---")

    putStrLn "***Abstract semantics 1: concrete loop functions***"
    let loopnests = getLoopnests p
    putStrLn "loop nests:"
    print loopnests
