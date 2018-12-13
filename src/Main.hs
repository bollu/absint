module Main where
import qualified Data.Map.Strict as M
import Data.List (intercalate)

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

data LiftedLattice a = LL a | LLBot | LLTop
instance Show a => Show (LiftedLattice a) where
  show LLBot = "_|_"
  show LLTop = "T"
  show (LL a) = show a

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


newtype Id = Id String deriving(Eq)
instance Show Id where
  show (Id s) = "id-" ++ s

-- Concrete Syntax
data Binop = Add | Lt deriving(Eq)
instance Show Binop where
  show Add = "op-+"
  show Lt = "op-<"

data Expr = Eint Int | Ebool Bool  | Ebinop Binop Id Id
  deriving(Eq)
instance Show Expr where
    show (Eint i) = show i
    show (Ebool b) = show b
    show (Ebinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e1 ++ ")"


data Command = Assign Id Expr 
             | If Id Stmt Stmt  -- branch value id, true branch, false branch
             | Loop Id Id Id Stmt -- loop phi id, entry value id, backedge value id

instance Show Command where
  show (Assign id e) = "(= " ++  show id ++ " " ++ show e ++  ")"
  show (If cond t e) = "(if " ++ show cond ++ " " ++ show t ++ " " ++ show e ++ ")"

newtype Stmt = Stmt [Command]
instance Show Stmt where
  show (Stmt cs) = intercalate ";" (map show cs)

-- A Program is a top level statement
type Program = Stmt


-- type representing loop trip counts
newtype LoopTripCounts = LoopTripCounts (M.Map Id Int)

-- concrete value is a function from loop trip conts to values
newtype CVal = CVal (LoopTripCounts -> LiftedLattice Int)

-- our abstract value is an affine function of loop trip counts.
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
  [assign "x" (Eint 1),
  assign "y" (Eint 2),
  assign "z" (Ebinop Add (Id "x") (Id "y"))]

main :: IO ()
main = print program
