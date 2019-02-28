{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Absdomain where
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..), 
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import qualified ISL.Native.Types as ISLTy (Id)
import Foreign.Ptr
import Data.Text.Prettyprint.Doc
import qualified Data.Map as M
import IR
import qualified System.IO.Unsafe as Unsafe (unsafePerformIO)
import Lattice
import Control.Monad (foldM)
import Control.Applicative

-- Abstract interpretation
-- =======================
localSpaceIds :: Ptr Ctx -> M.Map Id  (Ptr ISLTy.Id) -> IO (Ptr LocalSpace)
localSpaceIds ctx id2isl = do
  ls <- localSpaceSetAlloc ctx 0 (length id2isl)
  putStrLn "local space created."
  let islidcounters = zip (M.elems id2isl) [0, 1..]
  islidcounters <- traverse (\(id, c) -> (, c) <$> idCopy id) islidcounters

  putStrLn "local space adding dimensions."
  ls <- foldM 
          (\ls (islid, ix) -> 
              localSpaceSetDimId ls IslDimSet ix islid) ls
                islidcounters
  putStrLn "local space added dimensions"
  localSpaceDump ls
  return ls



-- add a new dimension to the map and return its index
mapAddUnnamedDim :: Ptr Map -> DimType -> Maybe (Ptr ISLTy.Id) -> IO (Ptr Map, Int)
mapAddUnnamedDim m dt mislid = do
    ndim <- mapDim m dt
    m <- mapAddDims m dt 1
    m <- case mislid of 
          Nothing -> return m
          Just islid -> mapSetDimId m dt ndim islid
    return (m, fromIntegral ndim)
      
pwaffFromMap :: Ptr Map -> IO (Ptr Pwaff)
pwaffFromMap m = do
    pwma <- (pwmultiaffFromMap m)
    pwa <- pwmultiaffGetPwaff pwma 0
    return pwa

-- returns the position of the first occurence of id if exists, otherwise returns Nothing
mapGetIxOfId :: Ptr Map -> DimType -> Ptr ISLTy.Id  -> IO (Maybe Int)
mapGetIxOfId m dt islid = do
  ndim <- mapDim m dt
  id2ix <- M.fromList <$> traverse (\ix ->  (,ix) <$> (mapGetDimId m dt ix)) [0..ndim-1]
  return $ fromIntegral <$> (id2ix M.!? islid)


mapConditionallyMoveDims :: Ptr Map 
                         -> (Ptr ISLTy.Id -> Bool) -- filter for dimension ID
                         -> DimType  -- input dimension
                         -> DimType -- output dimension
                         -> IO (Ptr Map)
mapConditionallyMoveDims m idfilter din dout = 
  let move :: Ptr Map -> Int -> IO (Ptr Map)
      move m ixin = do
        nin <- mapDim m din
        nout <- mapDim m dout
        
        if fromIntegral ixin >= nin
           then return m
           else do
                 idin <- mapGetDimId m din (fromIntegral ixin)
                 let shouldmove = idfilter idin
                 --mapToStr m >>= 
                 --  (\s -> putStrLn $ "nin: " ++ show nin ++ 
                 --           "|ixin: " ++ show ixin ++ 
                 --           "|shouldmove: " ++ show shouldmove ++ 
                 --           "|nout: " ++ show nout ++ 
                 --           " " ++ s)
                 if shouldmove
                    then do
                        m <- mapMoveDims m dout nout din (fromIntegral ixin) (fromIntegral 1)
                        move m ixin
                    else move m (ixin + 1)
  in move m 0 


class Spaced a where
  getSpace :: a -> IO (Ptr Space)
  -- get the number of dimensions for the given dimtype
  ndim :: a -> DimType -> IO Int
  ndim a dt = getSpace a >>= \s -> spaceDim s dt 

  -- get the dimension ID
  getDimId :: a -> DimType -> Int -> IO (Ptr ISLTy.Id)
  getDimId a dt ix = getSpace a >>= \s -> spaceGetDimId s dt ix

  -- set the dimension ID
  setDimId :: a -> DimType -> Int -> Ptr ISLTy.Id ->  IO a

  -- add dimensions
  addDims :: a -> DimType -> Int -> IO a

  findDimById :: a -> DimType -> Ptr ISLTy.Id -> IO (Maybe Int)
  findDimById a dt id = 
    getSpace a >>= \s -> do
      n <- ndim s dt
      mixs <- traverse (\ix -> do 
        ixid <- spaceGetDimId s dt ix
        if ixid == id 
           then return (Just ix)
           else return Nothing) [0..(n-1)]
      return $ foldl (<|>) Nothing mixs

-- add dimensions with the given IDs. 
-- NOTE, TODO: I am abusing "name" to mean "id'd". Hopefully, this will
-- not get confusing.
addNamedDims :: Spaced a => a -> DimType -> [Ptr ISLTy.Id] -> IO a
addNamedDims x dt ids = do
  n <- ndim x dt
  -- tuples of new IDs and their locations
  let newidixs = zip ids [n..]
  x <- addDims x dt (length ids)
  foldM (\x (id, ix) -> setDimId x dt ix id) x newidixs

instance Spaced (Ptr Space) where
  getSpace = return
  setDimId x dt i id = spaceSetDimId x dt (fromIntegral i) id
  addDims x dt i = spaceAddDims x dt (fromIntegral i)


instance Spaced (Ptr LocalSpace) where
  getSpace = localSpaceGetSpace
  setDimId x dt i id = localSpaceSetDimId x dt i id
  addDims x dt i = localSpaceAddDims x dt (fromIntegral i)


instance Spaced (Ptr Set) where
  getSpace = setGetSpace
  setDimId x dt i id = setSetDimId x dt (fromIntegral i) id
  addDims x dt i = setAddDims x dt (fromIntegral i)

instance Spaced (Ptr Map) where
  getSpace = mapGetSpace
  setDimId x dt i id = mapSetDimId x dt (fromIntegral i) id
  addDims x dt i = mapAddDims x dt (fromIntegral i)

instance Spaced (Ptr Pwaff) where
  getSpace = pwaffGetSpace
  setDimId x dt i id = pwaffSetDimId x dt (fromIntegral i) id
  addDims x dt i = pwaffAddDims x dt (fromIntegral i)

-- align a to b's space
class Spaced b => Alignable a b where
  alignParams :: a -> b -> IO a

instance Spaced b => Alignable (Ptr Pwaff) b where
  alignParams pwaff b = getSpace b >>= \s -> pwaffAlignParams pwaff s

constraintEqualityForSpaced :: Spaced  a => a -> IO (Ptr Constraint)
constraintEqualityForSpaced set = do
  getSpace set >>= localSpaceFromSpace >>= constraintAllocEquality


-- Abstract interpretation
-- =======================
instance Pretty (Ptr Pwaff) where
    pretty pw = pretty $ (Unsafe.unsafePerformIO (pwaffCoalesce pw >>= pwaffToStr))

instance Pretty (Ptr Set) where
    pretty s = pretty $ (Unsafe.unsafePerformIO (setCoalesce s >>= setToStr))

instance Pretty (Ptr Space) where
    pretty s = pretty $ (Unsafe.unsafePerformIO (spaceToStr s))


instance Pretty (Ptr Map) where
    pretty s = pretty $ (Unsafe.unsafePerformIO (mapToStr s))


-- abstract environments
type AbsVEnv = LatticeMap Id (Ptr Pwaff)


