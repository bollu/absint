{-# LANGUAGE DeriveFunctor #-}
module Lattice where
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import Test.QuickCheck
import Util

class Lattice a where
  lbot :: a
  ltop :: a
  ljoin :: a -> a -> a
  lmeet :: a -> a -> a

-- | quickCheck properties of union.
qcLatticeJoinCommutes :: (Eq a, Lattice a) => a -> a -> Bool
qcLatticeJoinCommutes a b = a `ljoin` b == b `ljoin` a


qcLatticeJoinAssoc :: (Eq a, Lattice a) => a -> a -> a -> Bool
qcLatticeJoinAssoc a b c =
    (a `ljoin` b) `ljoin` c == a `ljoin` (b `ljoin` c)

qcLatticeJoinIdempotent :: (Eq a, Lattice a) => a -> Bool
qcLatticeJoinIdempotent a = a `ljoin` a == a

qcLatticeJoinUnit :: (Eq a, Lattice a) => a -> Bool
qcLatticeJoinUnit a  = a `ljoin` lbot == a

-- A map based representation of a function (a -> b), which on partial
-- missing keys returns _|_
data LatticeMap k v = LM !(M.Map k v)  deriving (Eq, Ord, Functor)

instance (Ord k, Arbitrary k, Arbitrary v) =>
    Arbitrary (LatticeMap k v) where
        arbitrary = lmfromlist <$> arbitrary


lmInsert :: (Ord k, Lattice v) => k -> v ->  LatticeMap k v ->  LatticeMap k v
lmInsert k v (LM lm) =
  let vold = case lm M.!? k of
                Nothing -> lbot
                Just v' -> v'
  in LM $ M.insert k (ljoin v vold) lm


(#!) :: (Ord k, Lattice v) => LatticeMap k v -> k -> v
(#!) (LM m) k = case m M.!? k of
                   Just v -> v
                   Nothing -> lbot

lmfromlist :: Ord k => [(k, v)] -> LatticeMap k v
lmfromlist kvs = LM $ M.fromList [(k, v) | (k, v) <- kvs]

lmempty :: LatticeMap k v
lmempty = LM $ M.empty

lmtolist :: Ord k => LatticeMap k v -> [(k, v)]
lmtolist (LM m) = M.toList m

instance (Ord k, Lattice v) => Lattice (LatticeMap k v) where
  lbot = LM $ M.empty
  ltop =  error "hard to define top for latticemap without knowing universe"
  ljoin (LM kv) kv' =
     foldl (\kv' (k, v)  -> lmInsert k v kv')  kv' (M.toList kv)
  lmeet =  error "hard to define meet"

instance (Ord k, Show k, Show v, Pretty k, Pretty v) => Show (LatticeMap k v) where
  show (LM m) = show $ [(k, m M.! k) | k <- M.keys m]


instance (Ord k, Pretty k, Pretty v) => Pretty (LatticeMap k v) where
  pretty (LM m) =  pretty m -- vcat $ [pretty k <+> pretty "->" <+> pretty (m !!# k) | k <- M.keys m]

-- | a union combinator  for monoid on lattice
newtype LUnion a = LUnion { unLUnion :: a } deriving(Eq, Ord, Show)

instance Lattice a => Semigroup (LUnion a) where
    (LUnion a) <> (LUnion a') = LUnion $ ljoin a a'

instance Lattice a => Monoid (LUnion a) where
    mempty = LUnion $ lbot
