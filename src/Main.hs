module Main where
import qualified Data.Map.Strict as M
import Data.List (intercalate)

-- A join semilattice with bottom
class JoinSemilattice a where
  bottom :: a
  join :: a -> a -> a




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

-- Abstract semantics
-- Ix = n -> *before* the nth basic block
newtype Ix = Ix Int deriving(Eq, Show)
data Interval = Interval (Int, Int) | Infty | Empty
data `



assign :: String -> Expr -> Command
assign id e = Assign (Id id) e

program :: Stmt 
program = Stmt $ 
  [assign "x" (Eint 1),
  assign "y" (Eint 2)]

main :: IO ()
main = print program
