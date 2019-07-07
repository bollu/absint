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
import Control.Applicative
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


instance (Show a, Eq a, Monad m, MonadFail m) => Lattice m (Maybe a) where
    lbot = return Nothing
    ljoin Nothing x = return x
    ljoin x Nothing = return x
    ljoin (Just x) (Just y) = do
        if x /= y
        then Control.Monad.Fail.fail $
            "maybe not equal: " <> show x <> " " <> show y
        else return (Just x)

-- | Maybe with left-leaning union
newtype LeftLean a = LeftLean { unLeftLean :: (Maybe a) } deriving(Eq, Show)

mkLeftLean :: a -> LeftLean a
mkLeftLean = LeftLean . Just

instance (Show a, Eq a, Monad m, MonadFail m) => Lattice m (LeftLean a) where
    lbot = return $ LeftLean Nothing
    ljoin (LeftLean Nothing) x = return x
    ljoin x _ = return x

-- | Abstract values, and
data V = V { vp :: P, vs :: S, vloop :: Maybe Id, vid :: LeftLean Id } deriving(Eq)

instance Show V where
    show (V p s bbid vid) = show p <> " " <> show s <> " " <>
                            show bbid <> " " <>show vid

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
    P pw == P pw' = uio (pwaffIsEqual pw pw')


instance Show P where
    show (P pw) =
        uio (pwaffCopy pw >>= pwaffCoalesce >>= pwaffToStr)


instance Pretty P where
    pretty = pretty . show


newtype S = S (Ptr Set) deriving(Spaced)


instance Eq S where
    S s == S s' = uio (fromJust <$> setIsEqual s s')



instance Show S where
    show (S s) =
        uio (setCopy s >>= setCoalesce >>= setToStr)

instance Pretty S where
    pretty  = pretty . show

newtype C = C (Ptr Constraint)

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

pmul :: P -> P -> IOG P
pmul (P p) (P p') = do
  p <- liftIO $ pwaffCopy p
  p' <- liftIO $ pwaffCopy p'
  out <- liftIO $ pwaffMul p p'
  return $ P out

pscale :: Int -> P -> IOG P
pscale i p = do
  pi <- pconst i
  pmul p pi

psub :: P -> P -> IOG P
psub p p' = do
  p' <- pscale (-1) p'
  padd p p'


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




-- https://github.com/bollu/absint/blob/06f37247b2aa9be1f5ee35e672380adae64febec/src/Main.hs
-- | Given a pwaff ([x, y] -> delta) and an id "y", make the map
-- [x, y] -> [x, y + delta]
liftDeltaPwaffToMap :: Ptr Pwaff -> Id -> IOG (Ptr Map)
liftDeltaPwaffToMap pwdelta liftid = do
    -- { [x, y] }
    sp <- gsp
    -- { [x, y] -> [x, y] }
    mapspace <- liftIO $ do
                    sp <- spaceCopy sp
                    sp' <- spaceCopy sp
                    spaceMapFromDomainAndRange  sp sp'

    id2isl <- gread gid2isl
    -- [Ptr Pwaff]
    pullback_pws <- forM  (OM.toList id2isl) $ \(id, islid) ->  do
                      Just ix <- liftIO $ findDimById sp IslDimSet islid
                      (P pwsym) <- psym id
                      pwout <- if id == liftid
                                 then liftIO $ pwaffAdd pwsym pwdelta -- [y] -> [y + delta]
                                 else return pwsym -- [x] -> [x]
                      return pwout
    liftIO $ forM pullback_pws (\p -> pwaffToStr p >>= putStrLn)
    liftIO $ putStrLn $ "3"
    ctx <- gread gctx
    -- | create a pw_aff_list
    listpws <- liftIO $ toListPwaff ctx pullback_pws
    liftIO $ putStrLn $ "4"
    -- | create a multipw
    multipw <- liftIO $ multipwaffFromPwaffList mapspace listpws
    liftIO $ putStrLn $ "5"
    liftIO $  multipwaffToStr multipw >>= \s -> putStrLn $ "multipw: " ++ s
    liftIO $ mapFromMultiPwaff multipw



-- eg. y: { [viv, x, y] -> [100] }
--     delta: { [viv, x, y] -> [1] }
--     acc: { [viv, x, y] -> y + viv }
pacc :: P  -- ^ Init map
     -> P -- ^ Delta map
     -> Id -- ^ Dimension to apply the delta to (y)
     -> Id -- ^ name of the viv dimension (viv)
     -> IOG P
pacc init delta editid vivid = do
  liftIO $ putDocW 80 $ vcat $
    [pretty "\n---"
    , pretty "init: " <> pretty init
    , pretty "delta: " <> pretty delta
    , pretty "\n---"]
  -- Control.Monad.Fail.fail $ "debug"
  -- now create the map that is [delta] -> [delta^k]
  let P pwdelta = delta
  pwdelta <- liftIO $ pwaffCopy pwdelta
  -- | { [viv, x, y] -> [viv, x, y + 1] }
  mdelta <- liftDeltaPwaffToMap pwdelta editid
  -- | { [k] -> [[viv, x, y] -> [viv, x, y + k]] }
  (mdeltaPow, isexact) <- liftIO $ mapPower mdelta

  liftIO $ putDocW 80 $ vcat $
    [pretty "\n---[1]"
    , pretty "mdeltaPow: " <> pretty mdeltaPow
    , pretty "isexact: " <> pretty isexact]


  -- | [k] -> { [] -> [[viv, x, y] -> [viv, x, y + k]] }
  mdeltaPow <- liftIO $ mapMoveDims mdeltaPow IslDimParam (fromIntegral 0)
             IslDimIn (fromIntegral 0) (fromIntegral 1)

  liftIO $ putDocW 80 $ vcat $
    [pretty "\n---[2]"
    , pretty "mdeltaPow: " <> pretty mdeltaPow]

  -- | [k] -> { [viv, x, y] -> [viv, x, y + k] } (UNWRAPPED)
  mdeltaPow <- liftIO $ mapRange mdeltaPow >>= setUnwrap

  liftIO $ putDocW 80 $ vcat $
    [pretty "\n---[3]"
    , pretty "mdeltaPow: " <> pretty mdeltaPow]

  id2isl <- gread gid2isl
  Just vivix <- liftIO $ findDimById mdeltaPow IslDimIn (id2isl OM.! vivid)

  -- | equate [k] to [viv]
  -- | [k=viv] -> { [viv, x, y] -> [viv, x, y + k=viv] } (k=viv)
  mdeltaPow <- liftIO $ mapEquate mdeltaPow IslDimParam 0 IslDimIn vivix

  liftIO $ putDocW 80 $ vcat $
    [pretty "\n---[4]"
    , pretty "mdeltaPow: " <> pretty mdeltaPow]

  -- | Project out [k] (THE ONLY PARAMETER DIM!!!)
  -- | { [viv, x, y] -> [viv, x, y + viv] } (k is lost, only viv)
  mdeltaPow <- liftIO $ mapProjectOut mdeltaPow IslDimParam 0 1


  liftIO $ putDocW 80 $ vcat $
    [pretty "\n---[5]"
    , pretty "mdeltaPow: " <> pretty mdeltaPow]

  liftIO $ putStrLn $ "\n\n"

  -- | { [viv, x, y] -> [(viv), (x), (y + viv)] } (we have a pw_multi_aff, so each dimension is a separate pw_aff)
  -- TODO: do we need an mpwa? (multi-pw-aff ?)
  pwma <- liftIO $ pwmultiaffFromMap mdeltaPow
  liftIO $ putStrLn $ "PWMA:\n\n"
  liftIO $  pwmultiaffToStr pwma >>= putStrLn


  -- | Find the location where (y+viv) lives in the pwma, and extract it out
  Just editix <- liftIO $ findDimById mdeltaPow IslDimOut (id2isl OM.! editid)
  pw <- liftIO $ pwmultiaffGetPwaff pwma (fromIntegral editix)
  return $ P pw





-- | domain of a P
pdomain :: P -> IOG S
pdomain (P pw) = do
    pw <- liftIO $ pwaffCopy pw
    s <- liftIO $ pwaffDomain pw
    return $ S s

-- | Return the domain on which the two pwaffs are equal
peqset :: P -> P -> IOG S
peqset (P p1) (P p2) = do
    p1 <- liftIO $ pwaffCopy p1
    p2 <- liftIO $ pwaffCopy p2
    s <- liftIO $ pwaffEqSet p1 p2
    return $ S s

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

-- | Retrict the domain of P to S
prestrict :: P -> S -> IOG P
prestrict (P pw) (S s) = do
  pw <- liftIO $ pwaffCopy pw
  s <- liftIO $ setCopy s
  pw <- liftIO $ pwaffIntersectDomain pw s

  return $ P pw


-- | Take union. In overlapping area, pick maximum
punionmax :: P -> P -> IOG P
punionmax (P p1) (P p2) = do
    p1 <- liftIO $ pwaffCopy p1
    p2 <- liftIO $ pwaffCopy p2
    pu <- liftIO $ pwaffUnionMax p1 p2
    return $ P pu


-- | take union
paccunion :: Maybe (Id, Id)  -- ^ Id of value to accelerate, and the ID of the viv dimension
          -> P
          -> P
          -> IOG P
paccunion maccid pl pr = do
    dl <- pdomain pl
    dr <- pdomain pr

    dcommon <- sintersect dl dr
    deq <- peqset pl pr

    commonSubsetEq <- ssubset dcommon deq
    let commonEqualEq = dcommon == deq

    paccunion <- punionmax pl pr

    if commonSubsetEq
    then  do
      return $ paccunion
    else do
      dneq <- scomplement deq
      liftIO $ putDocW 80 $ vcat $
          [pretty "\n---"
          , pretty "loopid: " <> pretty maccid
          , pretty "\n---"
          , pretty "pl: " <> pretty pl
          , pretty "dl: " <> pretty dl
          , pretty "-----"
          , pretty "pr: " <> pretty pr
          , pretty "dr: " <> pretty dr
          , pretty "-----"
          , pretty "dcommon: " <> pretty dcommon
          , pretty "deq: " <> pretty deq
          , pretty "dNEQ: " <> pretty dneq
          , pretty "commonEqualEq: " <> pretty commonEqualEq
          , pretty "commonSubsetEq: " <> pretty commonSubsetEq
          , pretty "---\n"]

      -- | The only place where we can have disagreement
      -- between old and new values is along a backedge.
      -- So accelerate the backedge.
      delta <- psub pr pl
      -- | We need to provide an ID
      let Just (toaccid, vivid) = maccid
      out <- pacc pl delta toaccid vivid
      return $ out
      -- Control.Monad.Fail.fail $ "pwaffs are not equal on common domain"


snone :: IOG S
snone = do
    sp <- gsp
    emptyset <- liftIO $ setEmpty sp
    return $ S emptyset

suniv :: IOG S
suniv = do
  sp <- gsp
  univset <- liftIO $ setUniverse sp
  return $ S univset


sunion :: S -> S -> IOG S
sunion (S s1) (S s2) = do
    s1 <- liftIO $ setCopy s1
    s2 <- liftIO $ setCopy s2
    su <- liftIO $ setUnion s1 s2
    return $ S su


sintersect :: S -> S -> IOG S
sintersect (S s1) (S s2) = do
    s1 <- liftIO $ setCopy s1
    s2 <- liftIO $ setCopy s2
    out <- liftIO $ setIntersect s1 s2
    return $ S out

scomplement :: S -> IOG S
scomplement (S s) = do
    s <- liftIO $ setCopy s
    sc <- liftIO $ setComplement s
    return $ S sc

ssubset :: S -> S -> IOG Bool
ssubset (S s1) (S s2) =
    fromJust <$> liftIO (setIsSubset s1 s2)


-- | Make a parameter zero
sparamzero :: S
          -> Id -- ^ ID of the parameter
          -> IOG S
sparamzero (S s) id = do
    s <- liftIO $ setCopy s
    id2isl <- gread gid2isl
    ls <- glsp
    Just ix <- liftIO $ findDimById ls IslDimSet (id2isl OM.! id)
    c <- liftIO $ getSpace s >>= localSpaceFromSpace >>=
        constraintAllocEquality
    c <- liftIO $ constraintSetCoefficient c IslDimSet ix 1
    c <- liftIO $ constraintSetConstant c 0
    s <- liftIO $ setAddConstraint s c
    return $ S s

sparamgt0 :: S
    -> Id
    -> IOG S
sparamgt0 (S s) id = do
    s <- liftIO $ setCopy s
    id2isl <- gread gid2isl
    ls <- glsp
    Just ix <- liftIO $ findDimById ls IslDimSet (id2isl OM.! id)
    c <- liftIO $ getSpace s >>= localSpaceFromSpace >>=
        constraintAllocInequality
    c <- liftIO $ constraintSetCoefficient c IslDimSet ix (1)
    c <- liftIO $ constraintSetConstant c (-1)
    s <- liftIO $ setAddConstraint s c
    return $ S s



instance Pretty V where
  pretty = pretty . show


instance Lattice IOG S where
  lbot  =  snone
  ljoin s1 s2 = sunion s1 s2



instance Lattice IOG V where
  lbot  = V <$> pnone <*> lbot <*> lbot <*> lbot
  ljoin (V p1 s1 bbid1 vid1) (V p2 s2 bbid2 vid2) = do
      bbid <- ljoin bbid1 bbid2
      vid <- ljoin vid1 vid2

      let mvidbbid = liftA2 (,) (unLeftLean vid) bbid


      p <-  paccunion mvidbbid p1 p2
      s <- ljoin s1 s2
      return $ V p s bbid vid


-- | Interpret an expression
aie :: Expr -> AbsDom V -> IOG V
aie  (EInt i) _ = V <$> pconst i <*> lbot <*> lbot <*> lbot
aie  (EId id) d = d #! id
aie  (EBinop op id id') d = do
  p <- vp <$> d #! id
  p' <- vp <$> d #! id'
  case op of
    Add -> V <$> padd p p' <*> lbot <*> lbot <*> lbot
    Lt -> V <$> plt p p' <*> lbot <*> lbot <*> lbot

-- | Interpret an assignment
aia :: Assign -> AbsDom V -> IOG V
aia a d = do
  sbb <- vs <$> d #! (assignownbbid a)
  V p s _ _ <- aie (assignexpr a) d
  -- | restrict the value to the current BB domain
  p <- prestrict p sbb
  return $ V p s Nothing (mkLeftLean (name a))


-- | Interpret a terminator.
ait :: Term
    -> BBId -- ^ next basic block ID
    -> AbsDom V
    -> IOG V
ait (Done _ bbcur) bbidnext d = d #! bbcur
ait (Br _ bbcur _) bbidnext d = d #! bbcur


ait (BrCond _ bbcur c bbl bbr) bbidnext d = do
    -- | execution condtions of BB
    scur <- vs <$> d #! bbcur
    -- | current pwaff
    pc  <- vp <$> d #! c
    sthen <- ptrueset pc
    selse <- pfalseset pc
    if bbidnext == bbl
    then  V <$> pnone <*> (ptrueset pc) <*> lbot <*> lbot
    else if bbidnext == bbr
    then V <$> pnone <*> (pfalseset pc) <*> lbot <*> lbot
    else error $ "condbr only has bbl and bbr as successors"


-- | Starting state. Map every parameter to symbolic,
-- map entry BB to universe domain
aiStart :: Program -> IOG (AbsState V)
aiStart prog = do
    -- | get the parameters
    ps <- gread params
    id2isl <- gread gid2isl
    -- | create a map from the parameters. abstract domain
    -- maps each parameter to symbolic variable.
    id2sym <- forM (S.toList ps) $ \id -> do
                    p <- psym id
                    s <- lbot
                    return $ (id, V p s Nothing (mkLeftLean id))
    -- | Map the entry block to full domain
    entry2v <- do
                 p <- pnone
                 s <- suniv
                 let id = progEntryId prog
                 return (id, V p s Nothing (mkLeftLean id))
    return $ lmsingleton (progEntryLoc prog)
                (lmfromlist $ entry2v:id2sym)


-- | AI the left value in the loop
aiLoopL :: Phi -> AbsDom V -> V -> IOG  V
aiLoopL phi d vl = do
    let phiid = name phi
    let loopid = phiownbbid phi
    d <- pdomain (vp vl)
     -- | d : viv = 0
    dviv0 <- sparamzero d loopid
    -- | d^c: viv > 0
    dvivgt0 <- sparamgt0 d loopid

    -- | phi: viv > 0
    sym <- psym phiid
    sym <- prestrict sym dvivgt0

    p <- prestrict (vp vl) dviv0
    p <- paccunion Nothing p sym

    return $ V p (vs vl) (Just (phiownbbid phi)) (mkLeftLean (name phi))



-- | AI the right value in the loop
aiLoopR :: Phi ->  AbsDom V -> V ->IOG  V
aiLoopR phi d a = return a


-- | Create the AI object
mkAI :: Program -> AI IOG V
mkAI p = AI { aiA = aia
            , aiT = ait
            , aiStartState = aiStart p
            , aiLoopPhiL = aiLoopL
            , aiLoopPhiR = aiLoopR
            }

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
