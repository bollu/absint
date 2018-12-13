{-# LANGUAGE FlexibleInstances #-}
module Main where
import qualified Data.Map.Strict as M
import Data.List (intercalate)

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

-- Program syntax
-- ==============

newtype Id = Id String deriving(Eq, Ord)
instance Show Id where
  show (Id s) = "id-" ++ s

-- newtype Loopid = Loopid String deriving(Eq)
-- instance Show Loopid where
--   show (Loopid s) = "loopid-" ++ s

-- Concrete Syntax
data Binop = Add | Lt deriving(Eq)
instance Show Binop where
  show Add = "op-+"
  show Lt = "op-<"

data Expr = EInt Int | EBool Bool  | EBinop Binop Id Id | EId Id
  deriving(Eq)
instance Show Expr where
    show (EInt i) = show i
    show (EBool b) = show b
    show (EId id) = show id
    show (EBinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e1 ++ ")"


data Command = Assign Id Expr 
             | If Id Stmt Stmt  -- branch value id, true branch, false branch
             | While Id Stmt -- while cond stmt

instance Show Command where
  show (Assign id e) = "(= " ++  show id ++ " " ++ show e ++  ")"
  show (If cond t e) = "(if " ++ show cond ++ " " ++ show t ++ " " ++ show e ++ ")"
  show (While cond s) = "(while " ++ show cond ++ " " ++ show s ++ ")"

newtype Stmt = Stmt [Command]
instance Show Stmt where
  show (Stmt cs) = intercalate ";" (map show cs)

-- A Program is a top level statement
type Program = Stmt

-- Language semantics
-- ==================

-- Environments of the language
type Env = (M.Map Id Int) 

exprEval :: Expr -> Env -> Int
exprEval (EInt i) _ =  i
exprEval (EBool b) _ =  if b then 1 else 0
exprEval (EId id) env = env M.! id
exprEval (EBinop Add id1 id2) env = (env M.! id1) + (env M.! id2)

-- Semantics of a command
commandStep :: Command -> Env -> Env
commandStep (Assign id e) env = M.insert id (exprEval e env) env
commandStep (If cid s s') env = if (env M.! cid) == 1 
                                 then stmtStep s env 
                                 else stmtStep s' env
commandStep (While cid s) env = if (env M.! cid == 1) then stmtStep s env else env

stmtStep :: Stmt -> Env -> Env
stmtStep (Stmt cs) env = foldl (flip commandStep) env cs


-- Concrete domain - Collecting semantics
-- ======================================


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


assign :: String -> Expr -> Command
assign id e = Assign (Id id) e

program :: Stmt 
program = Stmt $ 
  [assign "x" (EInt 1),
  assign "y" (EInt 2),
  assign "z" (EBinop Add (Id "x") (Id "y"))]

main :: IO ()
main = print program
