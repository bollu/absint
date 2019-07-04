{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
module PolySCEV(V, AI, mkAI, runIOGTop) where
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..),
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import qualified ISL.Native.Types as ISLTy (Id)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.IORef
import Data.Text.Prettyprint.Doc.Util
import Data.Maybe
import IR
import Lattice
import Absdomain
import Foreign.Ptr
import Interpreter
import System.IO.Unsafe

data V = VBot | V deriving(Eq, Show, Ord)

data G = G


newtype IOG a = IOG  { runIOG :: G -> IO a } deriving(Functor)

instance Monad IOG where
  return a = IOG $ \g -> return a
  ma >>= f = IOG $ \g -> do
    a <- runIOG ma g
    runIOG (f a) g

instance Applicative IOG where
  pure = return
  ff <*> fa = do
    f <- ff
    a <- fa
    return $ f a

instance Pretty V where
  pretty = pretty . show

instance Lattice IOG V where
  lbot  = return VBot
  ljoin v1 v2 = return v1


aie :: Expr -> AbsDom V -> IOG V
aie = undefined

ait :: Term -> BBId -> AbsDom V -> IOG V
ait = undefined

aiStart :: IOG (AbsState V)
aiStart = undefined

mkAI :: Program -> AI IOG V
mkAI p = AI { aiE = aie , aiT = ait, aiStartState = aiStart }

mkg :: IO G
mkg = return $ G

runIOGTop :: IOG a -> IO a
runIOGTop ma = do
  g <- mkg
  runIOG ma g
