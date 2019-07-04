{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Lattice where
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import Test.QuickCheck
import Util
import Control.Monad
{-
class Lattice a where
  lbot :: a
  ltop :: a
  ljoin :: a -> a -> a
  lmeet :: a -> a -> a
-}

class Lattice m a where
  lbot :: m a
  ljoin :: a -> a -> m a


-- | quickCheck properties of union.
-- qcLatticeJoinCommutes :: (Eq a, Lattice m a) => a -> a -> m Bool
-- qcLatticeJoinCommutes a b = a `ljoin` b == b `ljoin` a

-- qcLatticeJoinAssoc :: (Eq a, Lattice m a) => a -> a -> a -> m Bool
-- qcLatticeJoinAssoc a b c =
--     (a `ljoin` b) `ljoin` c == a `ljoin` (b `ljoin` c)

-- qcLatticeJoinIdempotent :: (Eq a, Lattice m a) => a -> m Bool
-- qcLatticeJoinIdempotent a = a `ljoin` a == a

-- qcLatticeJoinUnit :: (Eq a, Lattice m a) => a ->m  Bool
-- qcLatticeJoinUnit a  = a `ljoin` lbot == a

-- qcLatticeJoinOrd :: (Ord a, Lattice m a) => a -> a -> m Bool
-- qcLatticeJoinOrd a b = (a <= ljoin a b) && (b <= ljoin a b)

data LatticeMap k v = LM !(M.Map k v) deriving(Eq, Ord, Functor)

-- instance (Ord k, Arbitrary k, Arbitrary v) =>
--     Arbitrary (LatticeMap k v) where
--         arbitrary = lmfromlist <$> arbitrary


lmInsert :: (Monad m, Ord k, Lattice m v) => k -> v ->
  LatticeMap k v ->  m (LatticeMap k v)
lmInsert k v (LM lm) = do
  vold <- case lm M.!? k of
                Nothing -> lbot
                Just v' -> return v'
  vnew <- ljoin v vold
  return $ LM $ M.insert k vnew lm


(#!) :: (Ord k, Monad m, Lattice m v) => LatticeMap k v -> k -> m v
(#!) (LM m) k = case m M.!? k of
                   Just v -> return v
                   Nothing -> lbot


-- | A hack to avoid having to get `m v`. Used for debugging.
lmmaybelookup :: (Ord k) => LatticeMap k v -> k -> Maybe v
lmmaybelookup (LM m) k = m M.!? k

instance (Ord k, Show k, Show v, Pretty k, Pretty v) => Show (LatticeMap k v) where
  show (LM m) = show $ [(k, m M.! k) | k <- M.keys m]


instance (Ord k, Pretty k, Pretty v) => Pretty (LatticeMap k v) where
  pretty (LM m) =  pretty m -- vcat $ [pretty k <+> pretty "->" <+> pretty (m !!# k) | k <- M.keys m]

instance (Monad m, Ord k, Lattice m v) => Lattice m (LatticeMap k v) where
  lbot = return $ LM $ M.empty
  ljoin (LM kv) kv' =
     foldM (\kv' (k, v)  -> lmInsert k v kv')  kv' (M.toList kv)

-- | a union combinator  for monoid on lattice
newtype LUnion m a = LUnion { unLUnion :: m a } deriving(Eq, Ord, Show)

instance (Monad m, Lattice m a) => Semigroup (LUnion m a) where
    (LUnion ma) <> (LUnion ma') = LUnion $ do
      a <- ma
      a' <- ma'
      a `ljoin` a'

instance (Monad m, Lattice m a) => Monoid (LUnion m a) where
    mempty = LUnion $ lbot

lmfromlist :: Ord k => [(k, v)] -> LatticeMap k v
lmfromlist kvs = LM $ M.fromList [(k, v) | (k, v) <- kvs]

lmsingleton :: Ord k => k -> v -> LatticeMap k v
lmsingleton k v = LM $ M.singleton k v

{-
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


lmempty :: LatticeMap k v
lmempty = LM $ M.empty

lmtolist :: Ord k => LatticeMap k v -> [(k, v)]
lmtolist (LM m) = M.toList m

instance (Ord k, Lattice v) => Lattice (LatticeMap k v) where
  lbot = LM $ M.empty
  ljoin (LM kv) kv' =
     foldl (\kv' (k, v)  -> lmInsert k v kv')  kv' (M.toList kv)

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

-- | Witness a galois connection.
class GaloisConnection a b | a -> b, b -> a where
    abstract :: a -> b
    concrete :: b -> a

qcGaloisConnectionLowerLift:: (Ord a, GaloisConnection a b) => a -> Bool
qcGaloisConnectionLowerLift a = a <= (concrete . abstract $ a)

qcGaloisConnectionLiftLower :: (Ord b, GaloisConnection a b) => b -> Bool
qcGaloisConnectionLiftLower b = (abstract . concrete $ b) == b
-}
