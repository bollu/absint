{-# LANGUAGE FlexibleInstances #-}
module Main where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate)
import qualified Control.Monad.State as ST
import Data.Foldable
import Data.Void

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

data LiftedLattice a = LL a | LLBot | LLTop deriving(Eq, Ord)

instance Show a => Show (LiftedLattice a) where
  show LLBot = "_|_"
  show LLTop = "T"
  show (LL a) = show a


data ToppedLattice a = TLTop | TL a deriving (Eq, Ord)

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

data LatticeMap k v = LM (M.Map k (ToppedLattice v)) | LMTop

insert :: Ord k => k -> v -> LatticeMap k v -> LatticeMap k v
insert k v LMTop = LMTop
insert k v (LM m) = LM $ M.insert k (TL v) m

(!!!) :: Ord k => LatticeMap k v -> k -> LiftedLattice v
(!!!) (LM m) k = case m M.!? k of
                  Just (TL v) -> LL v
                  Just TLTop -> LLTop
                  Nothing -> LLBot
(!!!) LMTop k = LLTop

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
repeatTillFix f seed = let cur = f seed in
                           if cur == seed then [seed] else seed:repeatTillFix f cur

-- Program syntax
-- ==============

newtype Id = Id String deriving(Eq, Ord)
instance Show Id where
  show (Id s) = "id-" ++ s

-- Concrete Syntax
data Binop = Add | Lt deriving(Eq)
instance Show Binop where
  show Add = "op-+"
  show Lt = "op-<"

data Expr = EInt Int | EBool Bool  | EBinop Binop Expr Expr | EId Id
  deriving(Eq)
instance Show Expr where
    show (EInt i) = show i
    show (EBool b) = show b
    show (EId id) = show id
    show (EBinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e1 ++ ")"

-- program counter, positioned *after* the ith instruction.
data PC = PC Int deriving(Eq, Ord)
instance Show PC where
  show (PC pc) = "pc-" ++ show pc

pcincr :: PC -> PC
pcincr (PC i) = PC (i + 1)

pcinit :: PC
pcinit = PC 0

-- Statements of the language
data Stmt = Assign PC Id Expr
            | If PC Id Stmt Stmt -- branch value id, true branch, false branch
            | While PC Id Stmt  -- while cond stmt
            | Seq Stmt Stmt
            | Skip PC

-- Return the PC of the first statement in the block
stmtPCStart :: Stmt -> PC
stmtPCStart (Assign pc _ _)  = pc
stmtPCStart (If pc _ _ _) = pc
stmtPCStart (While pc _ _) = pc
stmtPCStart (Seq s1 _) = stmtPCStart s1
stmtPCStart (Skip pc) = pc


-- Return the PC of the last statement in the block
stmtPCEnd :: Stmt -> PC
stmtPCEnd (Assign pc _ _)  = pc
stmtPCEnd (If pc _ _ _) = pc
stmtPCEnd (While pc _ _) = pc
stmtPCEnd (Seq _ s2) = stmtPCEnd s2
stmtPCEnd (Skip pc) = pc

instance Show Stmt where
  show (Assign pc id e) = show pc ++ ":" ++ "(= " ++  show id ++ " " ++ show e ++  ")"
  show (If pc cond t e) = show pc ++ ":" ++ "(if " ++ show cond ++ " " ++ show t ++ " " ++ show e ++ ")"
  show (While pc cond s) = show pc ++ ":" ++ "(while " ++ show cond ++ " " ++ show s ++ ")"
  show (Seq s1 s2) =  show s1 ++ "\n" ++ show s2
  show (Skip pc) = show pc ++ ":" ++ "done"




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
stmtSingleStep w@(While _ cid s) env =
  if (env M.! cid == 1)
 then let env' = (stmtSingleStep s env) in env'
  else env
stmtSingleStep (Seq s1 s2) env = stmtSingleStep s2 (stmtSingleStep s1 env)
stmtSingleStep (Skip _) env= env

  -- Execute the statement with respect to the semantics
stmtExec :: Stmt -> Env -> Env
stmtExec (s@(Assign _ _ _)) env = stmtSingleStep s env
stmtExec (s@(If _ _ _ _)) env = stmtSingleStep s env
stmtExec (s@(Seq _ _)) env = stmtSingleStep s env
stmtExec (s@(Skip _)) env = stmtSingleStep s env
stmtExec (s@(While _ cid loop)) env = last $ repeatTillFix
  (\env -> if env M.! cid == 1 then stmtSingleStep loop env else env) env


-- Concrete domain - Collecting semantics
-- ======================================
type State = M.Map PC Env

-- Propogate the value of the environment at the first PC to the second PC.
-- Needed to implicitly simulate the flow graph.
statePropogate :: PC -> PC -> (Env -> Env) -> State -> State
statePropogate pc pc' f st = let e = st M.! pc  in
  M.insert pc' (f e) st

-- a set of maps from program counters to environments
type CollectingSem =  (S.Set State)

-- Initial collecting semantics, which contains one state.
-- This initial state maps every PC to the empty environment
initCollectingSem :: CollectingSem
initCollectingSem = let st = M.fromList (zip (map PC [-1..7]) (repeat envBegin)) in
  S.singleton $ st

-- propogate the value of an environment at the first PC to the second
-- PC across all states.
collectingSemPropogate :: PC -> PC -> (Env -> Env) -> CollectingSem -> CollectingSem
collectingSemPropogate pc pc' f = S.map (statePropogate pc pc' f)

-- affect the statement, by borrowing the state from the given PC
stmtCollectFix :: PC -> Stmt -> CollectingSem -> CollectingSem
stmtCollectFix pcold s@(Assign _ _ _) csem =
  collectingSemPropogate pcold (stmtPCStart s) (stmtSingleStep s) csem

stmtCollectFix pcold (While pc condid loop) csem =
  let collectfix :: CollectingSem -> CollectingSem
      collectfix = collectingSemPropogate pc pc (stmtSingleStep loop)
      collect_in :: CollectingSem -> CollectingSem
      collect_in = collectingSemPropogate pcold pc (stmtSingleStep loop)
  in  collect_in csem `S.union` (fold (repeatTillFix collectfix csem))

stmtCollectFix pc (Seq s1 s2) csem =
  let csem' = stmtCollectFix pc s1 csem
      pc' = stmtPCEnd s1 in
    stmtCollectFix pc' s2 csem'
stmtCollectFix pc (Skip _) csem = csem



-- Abstract domain 1 - concrete functions
-- ======================================

-- type representing loop trip counts
newtype LoopTripCounts = LoopTripCounts (M.Map Id Int)

-- concrete value is a function from loop trip conts to values
newtype CVal = CVal (LoopTripCounts -> LiftedLattice Int)

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

-- lifted integers
data LInt = LILift Int | LIInfty | LIMinusInfty
-- interval domain
data Interval = Interval [(LInt, LInt)]

data PWAFF = PWAFF

-- abstracter
alpha :: CVal -> PWAFF
alpha = undefined

-- concretizer
gamma :: PWAFF -> CVal
gamma = undefined

-- concrete semantic transformer, that takes a semantics and incrementally
-- builds up on it. The final semantics is the least fixpoint of this function.
csem :: Program -> CVal -> CVal
csem = undefined

-- abstract semantics in terms of concrete semantics
asem :: Program -> PWAFF -> PWAFF
asem p = alpha . csem p . gamma

-- Example
-- =======

data StmtBuilder = StmtBuilder { sbpc :: PC, stmts :: Stmt }

assign :: String -> Expr -> ST.State StmtBuilder ()
assign id e =
  do
    pc <- ST.gets sbpc
    let a = Assign pc (Id id) e
    ST.modify  (\s -> s { sbpc = (pcincr (sbpc s)) })
    ST.modify (\s -> s { stmts = Seq (stmts s) a})
    return ()

build :: ST.State StmtBuilder () -> Stmt
build st = let begin = StmtBuilder (pcincr pcinit) (Skip (PC 0)) in 
             stmts $ ST.execState st  begin

program :: Stmt
program = build $  do
  assign "x" (EInt 1)
  assign "y" (EInt 2)

p :: Stmt
p = program


main :: IO ()
main = do
    print p
    putStrLn "***program output***"
    let outenv =  (stmtSingleStep p) envBegin
    print outenv

    putStrLn "***collecting semantics:***"

    let states' = stmtCollectFix (PC (-1)) p initCollectingSem

    putStrLn "***collecting semantics:***"
    forM_  (S.toList (fst states')) (\m -> forM_ ((map (\(k, v) -> show k ++ " -> " ++ show v)) (M.toList m)) print)
