{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}
module PolySCEV(V(..), AI, mkAI, runIOGTop) where
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..),
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import qualified ISL.Native.Types as ISLTy (Id)
import qualified Data.Set as S
import Control.Monad.Fail
import Data.Traversable
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
import qualified OrderedMap as OM
import qualified System.IO.Unsafe as Unsafe

uio :: IO a -> a
uio = Unsafe.unsafePerformIO

-- | Reader that provides context of G and ability to use IO
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

instance MonadFail IOG where
    fail s = IOG $ \g -> Control.Monad.Fail.fail s

liftIO :: IO a -> IOG a
liftIO f = IOG $ const f



-- | Abstract values
data V = V { vp :: P, vs :: S } deriving(Eq)

instance Show V where
    show (V p s) = show p ++ show s

-- | Global context
data G = G { gctx :: Ptr Ctx
           , vivs :: S.Set Id
           , vars :: S.Set Id
           , params :: S.Set Id
           , ids :: S.Set Id
           , gid2isl :: OM.OrderedMap Id (Ptr ISLTy.Id)
           }



-- | read from G
gread :: (G -> a) -> IOG a
gread f = IOG $ \g -> return (f g)


gsp :: IOG (Ptr Space)
gsp = do
    id2isl <- gread gid2isl
    ctx <- gread gctx
    s <- liftIO $ spaceSetAlloc ctx 0 (length id2isl)
    s <- liftIO $ OM.foldMWithIx s id2isl
        (\s ix _ islid -> idCopy islid >>= setDimId s IslDimSet ix)
    return s

glsp :: IOG (Ptr LocalSpace)
glsp = do
  id2isl <- gread gid2isl
  sp <- gsp
  liftIO $ localSpaceFromSpace sp


-- | Get the ISL id for a given ID
gislid :: Id -> IOG (Ptr ISLTy.Id)
gislid id = do
    id2isl <- gread gid2isl
    return $ id2isl OM.! id

newtype P = P (Ptr Pwaff) deriving(Spaced)

instance Eq P where
    P pw == P pw' = undefined


instance Show P where
    show (P pw) =
        uio (pwaffCopy pw >>= pwaffCoalesce >>= pwaffToStr)


instance Pretty P where
    pretty (P pw) = pretty (show pw)


newtype S = S (Ptr Set) deriving(Spaced)


instance Eq S where
    S s == S s' = undefined


instance Show S where
    show (S s) =
        uio (setCopy s >>= setCoalesce >>= setToStr)

instance Pretty S where
    pretty (S s) = pretty (show s)

-- | Get a symbolic representation of the given variable
psym :: Id -> IOG P
psym id = do
  ls <- glsp
  id2isl <- gread gid2isl
  Just ix <- liftIO $ findDimById ls IslDimSet (id2isl OM.! id)
  aff <- liftIO $ affVarOnDomain ls IslDimSet ix >>= pwaffFromAff
  return $ (P aff)

-- | Get a constant value
pconst :: Int -> IOG P
pconst i = do
    ctx <- gread gctx
    ls <- glsp
    p <- liftIO $ pwaffInt ctx ls i
    return $ P p

-- | Get a value that is defined nowhere
pnone :: IOG P
pnone = do
    ls <- glsp
    sp <- gsp
    emptyset <- liftIO $ setEmpty sp

    P pwaff <- pconst 0
    pwaff <- liftIO $ pwaffIntersectDomain pwaff emptyset
    return $ P pwaff

padd :: P -> P -> IOG P
padd (P p) (P p') = do
    p <- liftIO $ pwaffCopy p
    p' <- liftIO $ pwaffCopy p'
    pa <- liftIO $ pwaffAdd p p'
    return $ P pa

plt :: P -> P -> IOG P
plt (P pw1) (P pw2) = do
    pw1 <- liftIO $ pwaffCopy pw1
    pw2 <- liftIO $ pwaffCopy pw2
    lt <- liftIO $ pwaffLtSet pw1 pw2

    P pwt <- pconst (-1)
    pwt <- liftIO $ setCopy lt >>= pwaffIntersectDomain pwt

    P pwf <- pconst 0
    pwf <- liftIO $ setComplement lt >>= pwaffIntersectDomain pwf
    pwlt <- liftIO $ pwaffUnionMax pwt pwf
    return $ P pwlt


-- | Return the set on which P equals -1 [true]
ptrueset :: P -> IOG S
ptrueset (P pw) = do
    pw <- liftIO $ pwaffCopy pw
    P pone <- pconst (-1)
    strue <- liftIO $ pwaffEqSet pone pw
    return $ S strue


-- | Return the set where P equals 0 [false]
pfalseset :: P -> IOG S
pfalseset (P pw) = do
    pw <- liftIO $ pwaffCopy pw
    P pone <- pconst (0)
    strue <- liftIO $ pwaffEqSet pone pw
    return $ S strue

-- | Take the piecewise AND of two pwaffs that are indicators
-- of sets
pand :: P -> P -> IOG P
pand (P pw1) (P pw2) = do
    pw1 <- liftIO $ pwaffCopy pw1
    pw2 <- liftIO $ pwaffCopy pw2


    P pone <- pconst (-1)
    pw1t <- liftIO $ pwaffEqSet pone pw1

    P pone <- pconst (-1)
    pw2t <- liftIO $ pwaffEqSet pone pw2

    botht <- liftIO $ setIntersect pw1t pw2t
    P pone <- pconst (-1)
    pone <- liftIO $ setCopy botht >>= \botht -> pwaffIntersectDomain pone botht

    P pzero <- pconst 0
    bothtc <- liftIO $ setCopy botht >>= setComplement
    pzero <- liftIO $ pwaffIntersectDomain pzero bothtc


    pwcombined <- liftIO $ pwaffUnionMax pone pzero
    return $ P pwcombined

-- | Take the complement of a pwaff that is an indicator of a set
pcomplement :: P -> IOG P
pcomplement (P pw) = do
    pw <- liftIO $ pwaffCopy pw
    P pone <- pconst (-1)

    sone <- liftIO $ pwaffEqSet pone pw

    szero <- liftIO $ setCopy sone >>= setComplement

    P pone <- pconst (-1)
    pone <- liftIO $ pwaffIntersectDomain pone szero

    P pzero <- pconst 0
    pzero <- liftIO $ pwaffIntersectDomain pzero sone

    pwcombined <- liftIO $ pwaffUnionMax pone pzero
    return $ P pwcombined


-- | take union
punion :: P -> P -> IOG P
punion (P pl) (P pr) = do
    dl <- liftIO $ pwaffCopy pl >>= pwaffDomain
    dr <- liftIO $ pwaffCopy pr >>= pwaffDomain
    dcommon <- liftIO $ setCopy dl >>= \dl -> setCopy dr >>= \dr -> setIntersect dl dr
    deq <- liftIO $ pwaffCopy pl >>= \pl -> pwaffCopy pr >>= \pr -> pwaffEqSet pl pr

    Just commonSubsetEq <- liftIO $ setIsSubset dcommon deq
    Just commonEqualEq <- liftIO $ setIsEqual dcommon deq

    pl <- liftIO $ pwaffCopy pl
    pr <- liftIO $ pwaffCopy pr
    punion <- liftIO $ pwaffUnionMax pl pr


    if commonSubsetEq
    then  do
        return $ P punion
    else do
        dneq <- liftIO $ setCopy deq >>= setComplement
        liftIO $ putDocW 80 $ vcat $
            [pretty "\n---"
            , pretty "pl: " <> pretty pl
            , pretty "dl: " <> pretty dl
            , pretty "pr: " <> pretty pr
            , pretty "-----"
            , pretty "dr: " <> pretty dr
            , pretty "dcommon: " <> pretty dcommon
            , pretty "deq: " <> pretty deq
            , pretty "dNEQ: " <> pretty dneq
            , pretty "commonEqualEq: " <> pretty commonEqualEq
            , pretty "commonSubsetEq: " <> pretty commonSubsetEq
            , pretty "---\n"]
        return $ P punion
        -- Control.Monad.Fail.fail $ "pwaffs are not equal on common domain"

snone :: IOG S
snone = do
    sp <- gsp
    emptyset <- liftIO $ setEmpty sp
    return $ S emptyset

sunion :: S -> S -> IOG S
sunion (S s1) (S s2) = do
    s1 <- liftIO $ setCopy s1
    s2 <- liftIO $ setCopy s2
    su <- liftIO $ setUnion s1 s2
    return $ S su

scomplement :: S -> IOG S
scomplement (S s) = do
    s <- liftIO $ setCopy s
    sc <- liftIO $ setComplement s
    return $ S sc


instance Pretty V where
  pretty = pretty . show


instance Lattice IOG P where
  lbot  =  pnone
  ljoin p1 p2 = punion p1 p2

instance Lattice IOG S where
  lbot  =  snone
  ljoin s1 s2 = sunion s1 s2

instance Lattice IOG V where
  lbot  = V <$> lbot <*> lbot
  ljoin (V p1 s1) (V p2 s2) = V <$> (ljoin p1 p2) <*> (ljoin s1 s2)


-- | Interpret an expression
aie :: Expr -> AbsDom V -> IOG V
aie  (EInt i) _ = V <$> pconst i <*> lbot
aie  (EId id) d = d #! id
aie  (EBinop op id id') d = do
  (V p _) <- d #! id
  (V p' _) <- d #! id'
  case op of
    Add -> V <$> padd p p' <*> lbot
    Lt -> V <$> plt p p' <*> lbot


-- | Interpret a terminator.
ait :: Term
    -> BBId -- ^ next basic block ID
    -> AbsDom V
    -> IOG V
ait (Done _ bbcur) bbidnext d = d #! bbcur
ait (Br _ bbcur _) bbidnext d = d #! bbcur
ait (BrCond _ bbcur c bbl bbr) bbidnext d = do
    -- | execution condtions of BB
    V _ scur <- d #! bbcur
    -- | current pwaff
    V pc _ <- d #! c
    sthen <- ptrueset pc
    selse <- pfalseset pc
    if bbidnext == bbl
    then  V <$> lbot <*> (ptrueset pc)
    else if bbidnext == bbr
    then V <$> lbot <*> (pfalseset pc)
    else error $ "condbr only has bbl and bbr as successors"



aiStart :: Program -> IOG (AbsState V)
aiStart p = do
    -- | get the parameters
    ps <- gread params
    id2isl <- gread gid2isl
    -- | create a map from the parameters. abstract domain
    -- maps each parameter to symbolic variable.
    id2sym <- forM (S.toList ps) $ \id -> do
                    p <- psym id
                    s <- lbot
                    return $ (id, V p s)
    return $ lmsingleton (progEntryLoc p) (lmfromlist id2sym)


-- | Create the AI object
mkAI :: Program -> AI IOG V
mkAI p = AI { aiE = aie , aiT = ait, aiStartState = aiStart p }

-- | Make the global context
mkg :: Program -> IO G
mkg p = do
    gctx <- ctxAlloc
    islAbortOnError gctx
    let vivs = progvivs p
    let vars = progvarids p
    let params = progparams p
    let ids = params `S.union`
              vivs `S.union`
              vars

    gid2isl <- OM.fromList <$>
                for (S.toList ids)
                    (\id -> (id, ) <$> idAlloc gctx (show id))
    return $ G{..}


runIOGTop :: Program -> IOG a -> IO a
runIOGTop p ma = do
  g <- mkg p
  runIOG ma g
