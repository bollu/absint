{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
module PolySCEV(V, AI, mkAI) where
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..),
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import qualified ISL.Native.Types as ISLTy (Id)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import Data.Maybe
import IR
import Lattice
import Absdomain
import Foreign.Ptr
import Interpreter
import System.IO.Unsafe

gctx :: Ptr Ctx
gctx = unsafePerformIO $ do
  c <- ctxAlloc
  islAbortOnError c
  return c


-- | Short alias
uio :: IO a -> a
uio = unsafePerformIO


-- | Pwaff
newtype P = P (Ptr Pwaff)

instance Show P where
    show (P pw) =
        uio $ (pwaffCopy pw >>= pwaffCoalesce >>= pwaffToStr)

instance Pretty P where
    pretty = pretty . show

instance Eq P where
  P p == P p' = uio $ pwaffIsEqual p p'

-- | Sets
newtype S = S (Ptr Set) deriving(Show)

instance Eq S where
  S s == S s' =  fromJust $ uio $ setIsEqual s s'

-- | abstract value
data V = V { vsym :: P -- ^ pwsymbolic value, with _no acceleration_ at all
           } deriving(Eq, Show)

instance Pretty V where
    pretty (V vsym) = pretty vsym

instance Lattice V where
    lbot = undefined
    ltop = undefined
    ljoin = undefined
    lmeet = error "undefined meet for lattice V"



-- | global data needed for this stuff
data G = G { gparams :: S.Set Id -- ^ formal parameters
           , gvivs :: S.Set Id -- ^ IDs of only loops
           , gvars :: S.Set Id -- ^ regular variables
           , gall :: S.Set Id
           , glocs :: S.Set Loc -- ^ locations in the program
           , gislids :: M.Map Id (Ptr ISLTy.Id) -- ^ ISL ids
           , gls :: Ptr LocalSpace -- ^ localspace that is of the right shape
           }

-- | New local space
-- ls :: G -> LocalSpace
-- ls = unsafePerformIO $ do
--   s <- spaceSetAlloc ctx 0 (length gall)
--   reurn undefined


-- | Pwaff that is purely pwsymbolic
pwsymbolic :: G -> Id -> Ptr Pwaff
pwsymbolic g@G{..} id = uio $ do
  Just ix <- findDimById gls IslDimSet (gislids M.! id)
  affVarOnDomain gls IslDimSet ix >>= pwaffFromAff

-- | Create a pwaff that takes on the value of the variable
-- pwVar :: Ptr Ctx -> OM.OrderedMap Id (Ptr ISLTy.Id) -> Id -> IO (Ptr Pwaff)
-- pwVar ctx id2isl id = do
--   ls <- absSetSpace ctx id2isl >>= localSpaceFromSpace
--   Just ix <- findDimById ls IslDimSet (id2isl OM.! id)
--   affVarOnDomain ls IslDimSet ix >>= pwaffFromAff


-- | Pwaff that is undefined everywhere
pwundef :: G -> Ptr Pwaff
pwundef g@G{..} = uio $ do
  ls <- localSpaceCopy gls
  emptyset <- localSpaceCopy gls >>= getSpace >>= setEmpty

  pwaff <- pwaffInt gctx ls 0
  pwaff <- pwaffIntersectDomain pwaff emptyset
  return pwaff

-- | Pwaff that is constant everywhere
constant :: G -> Int -> Ptr Pwaff
constant g@G{..} i = uio $ do
  pwaffInt gctx gls  i


-- | Create ISL ids
mkIslIds :: [Id] -> IO [(Id, Ptr ISLTy.Id)]
mkIslIds ids =
  traverse (\id -> (id, ) <$> idAlloc gctx (show id)) ids

-- | Create a G instance for a given program.
mkG :: Program -> IO G
mkG p = do
    let gvars = progvarids p
    let gparams = progparams p
    let gvivs = progvivs p
    let glocs = S.fromList $ progbbs p >>= bbGetLocs
    let gall = gvivs `S.union` gparams `S.union` gvars
    gislids <- M.fromList <$> mkIslIds (S.toList gall)
    gls <- localSpaceIds gctx gislids
    return $ G {..}

-- | Abstract interpret an expression
aie :: G -> Expr -> AbsDom V -> V
aie G{..} (EInt i) = undefined
aie G{..} (EId id) = undefined
aie G{..} (EBinop  op e1 e2) = undefined


-- | Abstract interpret an expression
ait :: G
      -> Term -- ^ terminator instruction
      -> BBId  -- ^  bbid of successor
      -> AbsDom V -- ^ abstract domain to use
      -> V
ait G{..} t succ ad = undefined

aistart :: G -> AbsState V
aistart g@G{..} =
  let symvars = gparams
      botvars = gvars
      d = lmfromlist $
            [ (id, V $ P $ pwundef g) | id <- S.toList gvars] <>
            [ (id, V $ P $ pwsymbolic g id) | id <- S.toList symvars] :: AbsDom V

  -- | Each abstract state has
  -- the same abstract domain: everything is pwsymbolic
      s = lmfromlist [(l, d) | l <- S.toList glocs ] :: AbsState V
   in s


mkAI :: Program -> IO (AI V)
mkAI p = do
  g <- mkG p
  return $ AI (aie g) (ait g) (aistart g)
