module Main where
import qualified Data.Map.Strict as M
import Data.List (intercalate)

class Lattice a where
  bottom :: a
  top :: a
  join :: a -> a -> a
  meet :: a -> a -> a

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

-- lifted integers
data LInt = LILift Int | LIInfty | LIMinusInfty
-- interval domain
data Interval = Interval [(LInt, LInt)]


-- Concrete Syntax
data Binop = Add deriving(Eq, Show)
data Expr = Eint Int | Ebool Bool  | Ebinop Binop Expr Expr
  deriving(Eq)
instance Show Expr where
    show (Eint i) = show i
    show (Ebool b) = show b
    show (Ebinop Add e1 e2) = "(+" ++ show e1 ++ " " ++ show e1 ++ ")"

newtype Id = Id String deriving(Eq, Show)
data Command = Assign Id Expr | Skip | If Expr Stmt Stmt | While Expr Stmt
instance Show Command where
  show (Assign (Id id) e) = id ++ " := " ++ show e
  show Skip = "skip"
  show (If cond t e) = show "if" ++ show cond ++ show t ++ show e

newtype Stmt = Stmt [Command]
instance Show Stmt where
  show (Stmt cs) = intercalate ";" (map show cs)
newtype Nodeid = Nodeid Int deriving(Show)


assign :: String -> Expr -> Command
assign id e = Assign (Id id) e

program :: Stmt 
program = Stmt $ 
  [assign "x" (Eint 1),
  assign "y" (Eint 2)]

main :: IO ()
main = print program
