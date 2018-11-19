module Main where
import qualified Data.Map.Strict as M


data Binop = Add deriving(Eq, Show)
data Expr = Eint Int | Ebool Bool  | Ebinop Binop Expr Expr
  deriving(Eq)
instance Show Expr where
    show (Eint i) = show i
    show (Ebool b) = show b
    show (Ebinop Add e1 e2) = "(+" ++ show e1 ++ " " ++ show e1 ++ ")"

newtype Id = Id String deriving(Eq, Show)
data Stmt = Assign Id Expr
instance Show Stmt where
  show (Assign id e) = show id ++ " := " ++ show e
newtype Nodeid = Nodeid Int deriving(Show)


-- map from a nodeID to the node and its list of
-- successors.
newtype Graph = Graph (M.Map Nodeid (Stmt, [Nodeid]))

main :: IO ()
main = putStrLn "Hello, Haskell!"
