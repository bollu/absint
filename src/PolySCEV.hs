{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}
module PolySCEV(V(..), AI, mkAI, runIOGTop) where
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..),
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint, Multipwaff)
import qualified ISL.Native.Types as ISLTy (Id)
import qualified Data.Set as S
import Control.Monad.Fail
import Control.Applicative
import Control.Monad
import Data.Traversable
import Data.Foldable
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

-- | Fix a monadic computation till fixpoint
mfixstable :: (Monad m, Eq a) => (a -> m a) -> a -> m a
mfixstable f a = do
    a' <- f a
    if a == a'
    then return a'
    else mfixstable f a'

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
data V = V { vp :: P, vs :: S, vloop :: Maybe Id, vid :: LeftLean Id, vsubst :: LatticeMap Id P  } deriving(Eq)

instance Show V where
    show (V p s bbid vid subst) = show p <> " " <> show s <> " " <>
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

withP :: P -> (Ptr Pwaff -> IOG a) -> IOG a
withP (P pw) f = do
    pw <- liftIO $ pwaffCopy pw
    f pw

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



-- | Given a pwaff ([x, y] -> z) and an id "y", make the map
-- [x, y] -> [(x), (z)]
liftPwaffToMultipwaff :: Ptr Pwaff -> Id -> IOG (Ptr Multipwaff)
liftPwaffToMultipwaff pw liftid = do
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
                                 then return pw -- [x, y] -> [z]
                                 else return pwsym -- [x, y] -> [x]
                      return pwout
    -- liftIO $ do
    --     putStrLn $ "\n pullback pws:\n"
    --     forM pullback_pws (\p -> pwaffToStr p >>= putStrLn)
    ctx <- gread gctx
    -- | create a pw_aff_list
    listpws <- liftIO $ toListPwaff ctx pullback_pws
    --- liftIO $ putStrLn "\nvvvv\n"
    -- | create a multipw
    multipw <- liftIO $ multipwaffFromPwaffList mapspace listpws
    --- liftIO $ putStrLn "\n^^^^\n"
    -- liftIO $  multipwaffToStr multipw >>= \s -> putStrLn $ "multipw: " ++ s
    return multipw


-- https://github.com/bollu/absint/blob/06f37247b2aa9be1f5ee35e672380adae64febec/src/Main.hs
-- | Given a pwaff ([x, y] -> delta) and an id "y", make the map
-- [x, y] -> [x, y + delta]
liftDeltaPwaffToMap :: Ptr Pwaff -> Id -> IOG (Ptr Map)
liftDeltaPwaffToMap pwdelta liftid = do
    pwdelta <- liftIO $ pwaffCopy pwdelta
    (P pwsym) <- psym liftid
    -- [x, y] -> [(y + delta)]
    pwlift <- liftIO $ pwaffAdd pwsym pwdelta
    multipw <- liftPwaffToMultipwaff pwlift liftid
    liftIO $ mapFromMultiPwaff multipw



-- eg. y: { [viv, x, y] -> [100] }
--     delta: { [viv, x, y] -> [1] }
--     acc: { [viv, x, y] -> y + viv }
ppow :: P  -- ^ Init map
     -> P -- ^ Delta map
     -> Id -- ^ Dimension to apply the delta to (y)
     -> Id -- ^ name of the viv dimension (viv)
     -> IOG (Maybe P)
ppow init delta editid vivid = do
  -- liftIO $ putDocW 80 $ vcat $
  --   [pretty "\n---"
  --   , pretty "init: " <> pretty init
  --   , pretty "delta: " <> pretty delta
  --   , pretty "\n---"]
  -- Control.Monad.Fail.fail $ "debug"
  -- now create the map that is [delta] -> [delta^k]
  let P pwdelta = delta
  pwdelta <- liftIO $ pwaffCopy pwdelta
  -- | { [viv, x, y] -> [viv, x, y + delta] }
  mdelta <- liftDeltaPwaffToMap pwdelta editid
  -- | { [k] -> [[viv, x, y] -> [viv, x, y + delta*k]] }
  (mdeltaPow, isexact) <- liftIO $ mapPower mdelta

  -- liftIO $ putDocW 80 $ vcat $
  --   [pretty "\n---[1]"
  --   , pretty "\nmdeltaPow: " <> pretty mdeltaPow
  --   , pretty "\nisexact: " <> pretty isexact]

  -- | We can't accelerate
  if isexact == 0
  then -- TODO: for now, return the left. To be correct, we need to find ou
       -- which of left or right is more advanced and proceed accordingly
       return $ Nothing
  else do
    -- | [k] -> { [] -> [[viv, x, y] -> [viv, x, y + delta*k]] }
    mdeltaPow <- liftIO $ mapMoveDims mdeltaPow IslDimParam (fromIntegral 0)
               IslDimIn (fromIntegral 0) (fromIntegral 1)

    -- liftIO $ putDocW 80 $ vcat $
    --   [pretty "\n---[2]"
    --   , pretty "mdeltaPow: " <> pretty mdeltaPow]

    -- | [k] -> { [viv, x, y] -> [viv, x, y + delta*k] } (UNWRAPPED)
    mdeltaPow <- liftIO $ mapRange mdeltaPow >>= setUnwrap

    -- liftIO $ putDocW 80 $ vcat $
    --   [pretty "\n---[3]"
    --   , pretty "mdeltaPow: " <> pretty mdeltaPow]

    id2isl <- gread gid2isl
    Just vivix <- liftIO $ findDimById mdeltaPow IslDimIn (id2isl OM.! vivid)

    -- | equate [k] to [viv]
    -- | [k=viv] -> { [viv, x, y] -> [viv, x, y + delta*(k=viv)] } (k=viv)
    mdeltaPow <- liftIO $ mapEquate mdeltaPow IslDimParam 0 IslDimIn vivix

    -- liftIO $ putDocW 80 $ vcat $
    --   [pretty "\n---[4]"
    --   , pretty "mdeltaPow: " <> pretty mdeltaPow]

    -- | Project out [k] (THE ONLY PARAMETER DIM!!!)
    -- | { [viv, x, y] -> [viv, x, y + delta*viv] } (k is lost, only viv)
    mdeltaPow <- liftIO $ mapProjectOut mdeltaPow IslDimParam 0 1


    -- liftIO $ putDocW 80 $ vcat $
    --   [pretty "\n---[5]"
    --   , pretty "mdeltaPow: " <> pretty mdeltaPow]

    --- liftIO $ putStrLn $ "\n\n"

    -- | { [viv, x, y] -> [(viv), (x), (y + delta*viv)] } (we have a pw_multi_aff, so each dimension is a separate pw_aff)
    pwma <- liftIO $ pwmultiaffFromMap mdeltaPow
    -- liftIO $ putStrLn $ "PWMA:\n\n"
    liftIO $  pwmultiaffToStr pwma >>= putStrLn


    -- | Find the location where (y+viv) lives in the pwma, and extract it out
    -- | { [viv, x, y] -> [(y + delta*viv)} (returns the accelerated value)
    Just editix <- liftIO $ findDimById mdeltaPow IslDimOut (id2isl OM.! editid)
    pw <- liftIO $ pwmultiaffGetPwaff pwma (fromIntegral editix)
    return $ Just (P pw)



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
punionmax__ :: P -> P -> IOG P
punionmax__ (P p1) (P p2) = do
    p1 <- liftIO $ pwaffCopy p1
    p2 <- liftIO $ pwaffCopy p2
    pu <- liftIO $ pwaffUnionMax p1 p2
    return $ P pu

-- | Check if the pwaff involves an ID in its computation
pinvolves :: P -> Id -> IOG Bool
pinvolves (P pw) id = do
    id2isl <- gread gid2isl
    Just ix <- liftIO $ findDimById pw IslDimIn (id2isl OM.! id)
    Just involves <- liftIO $ pwaffInvolvesDims pw IslDimIn ix 1
    return $ involves

-- | Union pwaffs ensuring that they are equal on their overlapping domain
punioneq :: P -> P -> IOG P
punioneq pl pr = do
    dl <- pdomain pl
    dr <- pdomain pr

    dcommon <- sintersect dl dr
    deq <- peqset pl pr

    commonSubsetEq <- ssubset dcommon deq
    let commonEqualEq = dcommon == deq

    punion <- punionmax__ pl pr

    if commonSubsetEq
    then  do
      return $ punion
    else do
      dneq <- scomplement deq

      liftIO $ putDocW 80 $ vcat $
          [pretty "\n---"
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
      Control.Monad.Fail.fail $ "pwaffs are not equal on common domain"


-- | Project a dimension out from a pwaff and return the new pwaff
-- There is no guarantee that this will continue to be a pwaff, so be
-- careful.
pproject :: Id -> P -> IOG P
pproject id (P pw) = do
    pw <- liftIO $ pwaffCopy pw
    m <- liftIO $ mapFromPwaff pw
    islid <- gislid id
    Just ix <- liftIO $ findDimById m IslDimIn islid
    -- | remove the dimension
    m <- liftIO $ mapProjectOut m IslDimIn ix 1
    -- | Add back the dimension and set the id
    m <- liftIO $ mapInsertDims m IslDimIn (ix - 1) 1
    -- | set the ID
    m <- liftIO $ mapSetDimId m IslDimIn ix islid

    pw <- liftIO $ pwaffFromMap m
    return $ P pw

-- | Get the pwaff as it was at the zero parameter.
pEvalParam0 :: Id -> P -> IOG P
pEvalParam0 id p = do
  -- { id =  0 }
  sid0 <-  suniv >>= \s -> sparamzero s id
  -- { p : id = 0 }
  pid0 <- prestrict p sid0
  -- { project out the 'id' dimension
  pproject id pid0

psubst :: Id  -- ^ id to be substituted: x
       -> P -- ^ P with new vaue for substitution: x: [x, y] -> new
       -> P  -- ^ P to substitute into [x, y] -> x + y
       -> IOG P -- [x, y] -> new + y
psubst id newval pold = do
  -- | [x, y] -> [(new), (y)]
  mpw <- withP newval $ \p -> liftPwaffToMultipwaff p id
  -- | substitute beginvalue
  finalpw <- withP pold $ \pwold -> liftIO $ pwaffPullbackMultipwaff pwold mpw
  return $ P finalpw

-- | Take a map of substitutions and apply them all once
psubstmap :: LatticeMap Id P
   -> P
   -> IOG P
psubstmap id2p pinit =
    foldM  (\pcur (idsubst, p') ->
                psubst idsubst p' pcur)
           pinit
           (lmtolist id2p)



-- | take union, accelerating when pwaffs overlap and disagree
punionacc ::
          Id -- ^ ID of value to accelerate
          -> Id -- ^ ID of viv dimension
          -> P
          -> P
          -> IOG (LatticeMap Id P, P) -- ^ substitutions made, and the new accelerated value
punionacc toaccid vivid pl pr = do
    dl <- pdomain pl
    dr <- pdomain pr

    dcommon <- sintersect dl dr
    deq <- peqset pl pr

    commonSubsetEq <- ssubset dcommon deq
    let commonEqualEq = dcommon == deq

    if commonSubsetEq
    then  do
      liftA2 (,) lbot (punionmax__ pl pr)
    else do
      dneq <- scomplement deq

      -- | The only place where we can have disagreement
      -- between old and new values is along a backedge.
      -- So accelerate the backedge.
      -- TODO, NOTE: we assume that pr is farther along than pl.
      -- This can be verified by inspecting their minimum value along the
      -- viv dimension
      delta <- psub pr pl

      -- liftIO $ putDocW 80 $ vcat $
      --     [pretty "\n---"
      --     , pretty "toaccid:  " <> pretty toaccid
      --     , pretty "vivid:  " <> pretty vivid
      --     , pretty "\n---"
      --     , pretty "\n---"
      --     , pretty "pl: " <> pretty pl
      --     , pretty "dl: " <> pretty dl
      --     , pretty "-----"
      --     , pretty "pr: " <> pretty pr
      --     , pretty "dr: " <> pretty dr
      --     , pretty "-----"
      --     , pretty "dcommon: " <> pretty dcommon
      --     , pretty "deq: " <> pretty deq
      --     , pretty "dNEQ: " <> pretty dneq
      --     , pretty "commonEqualEq: " <> pretty commonEqualEq
      --     , pretty "commonSubsetEq: " <> pretty commonSubsetEq
      --     , pretty "---\n"
      --     , pretty "delta: " <> pretty delta]

      -- liftIO $ putStrLn $ "\n\n**INVOLVES: " <> show (linvolves, rinvolves)
      -- | deltapow: [viv, x, toacc] -> [x, toacc + delta * viv]
      mdeltapow <- ppow pl delta toaccid vivid

      case mdeltapow of
        Nothing -> fmap (, pl) lbot
        Just deltapow -> do
            -- liftIO $ putDocW 80 $ pretty "\ndeltapow: " <> pretty deltapow


            -- | Now find the value that is in the pl at (viv=0)
            -- Replace the `toaccid` dimension in `deltapow` with `plviv0`.
            -- NOTE: THIS DOES NOT HAVE (viv =0)
            plbegin <- pEvalParam0 vivid pl

            -- | Substitute plbegin in deltapow. Note that this is only defined
            -- for (viv > 0)
            subst <- psubst toaccid plbegin deltapow

            -- | We also create value at (viv = 0), which is the pwaff
            -- plbegin, restricted to (viv = 0)
            plviv0 <- prestrictparam0 plbegin vivid


            -- liftIO $ putDocW 80 $ pretty "\nfinal accelerated(BEOFRE UNION): " <> pretty subst <> pretty "   " <> pretty plviv0
            final <- punioneq subst plviv0



            -- | Return the substitution map made
            let substmap = lmsingleton toaccid deltapow


            -- liftIO $ putDocW 80 $ pretty "\nfinal accelerated: " <> pretty final
            return $ (substmap, final)

            {-
            -- check if either left or right involve the vivid. If only one of
            -- them does, then use that. Otherwise, fail.
            -- If they are both accelerated, then increment the right's parameter dim by 1 and take
            -- | involves is not a sane way to check for this, because involves
            -- | also checks the constraints.
            (linvolves, rinvolves) <- liftA2 (,) (pinvolves pl vivid) (pinvolves pr vivid)
            case (False, False) of
              (True, True) -> do
                                pr' <- pparamincr' pr vivid
                                delta <- psub pr' pl
                                liftIO $ putDocW 80 $ vcat $
                                    [pretty "\n---TRUE TRUE ---\n"
                                    , pretty "pl: " <> pretty pl
                                    , pretty "pr: " <> pretty pr
                                    , pretty "pr': " <> pretty pr'
                                    , pretty "delta: " <> pretty delta
                                    , pretty "--"]
                                pzero <- pconst 0
                                if delta /= pzero
                                then Control.Monad.Fail.fail $ "delta is not zero!"
                                else return $ pr
              (True, False) -> return $ pl
              (False, True) -> return $ pr
              (False, False) -> ppow pl delta toaccid vivid
              -}



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

-- | Restrict a pwaff to the case where a parameter is 0
prestrictparam0 :: P -> Id -> IOG P
prestrictparam0 p id = do
    univ <- suniv
    sidzero <- sparamzero univ id
    prestrict p sidzero

pparamincr' :: P -> Id -> IOG P
pparamincr' (P pw) incrid = do
   ctx <- gread gctx
   pw <- liftIO $ pwaffCopy pw
   id2isl <- gread gid2isl
   mapspace <- do
                 sp <- gsp
                 sp' <- gsp
                 liftIO $ spaceMapFromDomainAndRange  sp sp'
   -- [Pwaffs to pullback against]
   pullback_pws <- forM (OM.toList id2isl) $ \(id, islid) ->  do
                     Just ix <- liftIO $ findDimById pw IslDimIn islid
                     (P pwsym) <- psym id
                     pwout <- if id == incrid
                                then do
                                    (P pone) <- pconst (-1)
                                    liftIO $ pwaffAdd pwsym pone
                                else return pwsym -- [x] -> [x]
                     return pwout
   listpws <- liftIO $ toListPwaff ctx pullback_pws
   -- | create a multipw
   multipw <- liftIO $ multipwaffFromPwaffList mapspace listpws
   pw <- liftIO $ pwaffPullbackMultipwaff pw multipw
   return $ P pw


instance Pretty V where
  pretty = pretty . show


instance Lattice IOG S where
  lbot  =  snone
  ljoin s1 s2 = sunion s1 s2


instance Lattice IOG P where
  lbot  =  pnone
  ljoin = punioneq



instance Lattice IOG V where
  lbot  = V <$> pnone <*> lbot <*> lbot <*> lbot <*> lbot
  ljoin vl@(V p1 s1 bbid1 vid1 subst1) vr@(V p2 s2 bbid2 vid2 subst2) = do
      bbid <- ljoin bbid1 bbid2
      vid <- ljoin vid1 vid2
      s <- ljoin s1 s2
      subst <- ljoin subst1 subst2

     -- | Apply all substitutions considered so far.
      p1 <- (psubstmap subst) p1
      p2 <- (psubstmap subst) p2

      liftIO $ putDocW 80 $
          vcat [pretty "unioning: " <>
                pretty (show vid1) <>
                pretty " " <>
                pretty (show vid2) <> pretty "\n",
                indent 4 $ pretty p1, indent 4 $ pretty p2,
                pretty "\n",
                pretty subst,
                pretty "\n"
               ]

      (substacc, p) <-  case (bbid, vid) of
                          (Just bbid, LeftLean (Just vid)) -> punionacc vid bbid p1 p2
                          _ ->  liftA2 (,) lbot (punioneq p1 p2)

      subst <- (substacc `ljoin` subst)
      return $ V p s bbid vid  subst


-- | Interpret an expression
aie :: Expr -> AbsDom V -> IOG V
aie  (EInt i) _ = V <$> pconst i <*> lbot <*> lbot <*> lbot <*> lbot
aie  (EId id) d = d #! id
aie  (EBinop op id id') d = do
  v <- d #! id
  v' <- d #! id'
  let p = vp v
  let p' =  vp v'
  let subst =  vsubst v
  let subst' = vsubst v'

  case op of
    Add -> V <$> padd p p' <*> lbot <*> lbot <*> lbot <*> subst `ljoin` subst'
    Lt -> V <$> plt p p' <*> lbot <*> lbot <*> lbot <*> subst `ljoin` subst'

-- | Interpret an assignment
aia :: Assign -> AbsDom V -> IOG V
aia a d = do
  sbb <- vs <$> d #! (assignownbbid a)
  V p s _ _ subst <- aie (assignexpr a) d
  -- | restrict the value to the current BB domain
  p <- prestrict p sbb
  return $ V p s Nothing (mkLeftLean (name a)) subst


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
    then  V <$> pnone <*> (ptrueset pc) <*> lbot <*> lbot <*> lbot
    else if bbidnext == bbr
    then V <$> pnone <*> (pfalseset pc) <*> lbot <*> lbot <*> lbot
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
                    subst <- lbot
                    return $ (id, V p s Nothing (mkLeftLean id) subst)
    -- | Map the entry block to full domain
    entry2v <- do
                 p <- pnone
                 s <- suniv
                 let id = progEntryId prog
                 subst <- lbot
                 return (id, V p s Nothing (mkLeftLean id) subst)
    return $ lmsingleton (progEntryLoc prog)
                (lmfromlist $ entry2v:id2sym)


-- | AI the left value in the loop
aiLoopL :: Phi -> AbsDom V -> V -> IOG  V
aiLoopL phi d vl = do
    let phiid = name phi
    let loopid = phiownbbid phi
    d <- pdomain (vp vl)
     -- |  {viv = 0}
    dviv0 <- sparamzero d loopid
    -- | { viv > 0 }
    dvivgt0 <- sparamgt0 d loopid

    -- | { phiid : viv > 0 }
    sym <- psym phiid
    sym <- prestrict sym dvivgt0

    -- | { vl : viv = 0 }
    p <- prestrict (vp vl) dviv0
    -- | { vl : viv = 0; phiid : viv > 0 }
    p <- punioneq p sym

    return $ V p (vs vl) (Just (phiownbbid phi)) (mkLeftLean (name phi)) (vsubst vl)



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
