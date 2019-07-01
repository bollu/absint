{-# LANGUAGE RecordWildCards #-}
module PolySCEV(V, AI, mkAI) where
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..),
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import qualified ISL.Native.Types as ISLTy (Id)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import IR
import Lattice
import Absdomain
import Foreign.Ptr
import Interpreter



-- | abstract value
data V = V { vsym :: Pwaff -- ^ pwsymbolic value, with _no acceleration_ at all
             , vacc :: Pwaff -- ^ accelerated value.
             , vaccloops :: S.Set Id -- ^ accelerated against which loops
           }

instance Eq V where
    (==) = undefined

instance Show V where
    show = undefined

instance Lattice V where
    lbot = undefined
    ltop = undefined
    ljoin = undefined
    lmeet = error "undefined meet for lattice V"



-- | global data needed for this stuff
data G = G { gparams :: S.Set Id -- ^ formal parameters
           , gvivs :: S.Set Id -- ^ IDs of only loops
           , gvars :: S.Set Id -- ^ regular variables
           , glocs :: S.Set Loc -- ^ locations in the program
           , islctx :: Ptr Ctx -- ^ ISL context
           }

-- | New local space
ls :: G -> LocalSpace
ls = undefined

-- | Pwaff that is purely pwsymbolic
pwsymbolic :: G -> Id -> V
pwsymbolic g@G{..} id = undefined

-- | Pwaff that is undefined everywhere
pwundef :: G -> Id -> V
pwundef g@G{..} id = undefined

-- | Pwaff that is constant everywhere
constant :: G -> Int -> V
constant g@G{..} id = undefined

-- | Create a G instance for a given program.
mkG :: Program -> IO G
mkG p = do
    islctx <- ctxAlloc
    islAbortOnError islctx
    let gvars = progvarids p
    let gparams = progparams p
    let gvivs = progvivs p
    let glocs = S.fromList $ progbbs p >>= bbGetLocs
    return $ G{..}

-- | Abstract interpret an expression
aie :: G -> Expr -> AbsDom V -> V
aie G{..} (EInt i) = undefined
aie G{..} (EId id) =undefined
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
            [ (id, pwundef g id) | id <- S.toList gvars] <>
            [ (id, pwsymbolic g id) | id <- S.toList symvars] :: AbsDom V

  -- | Each abstract state has
  -- the same abstract domain: everything is pwsymbolic
      s = lmfromlist [(l, d) | l <- S.toList glocs ] :: AbsState V
   in s


mkAI :: Program -> IO (AI V)
mkAI p = do
  g <- mkG p
  return $ AI (aie g) (ait g) (aistart g)
