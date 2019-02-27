module Util where
import Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text.Lazy as L
import Data.Text.Prettyprint.Doc
import Foreign.Ptr
import qualified Data.Map as M
import qualified Data.Set as S
import GHC.Stack (HasCallStack)

docToText :: Doc ann -> L.Text
docToText doc = renderLazy (layoutPretty defaultLayoutOptions doc)

docToString :: Doc ann -> String
docToString = L.unpack . docToText

prettyableToText :: Pretty a => a -> L.Text
prettyableToText a = docToText (pretty a)

prettyableToString :: Pretty a => a -> String
prettyableToString  a = docToString (pretty a)

instance {-# OVERLAPPABLE #-} Pretty (Ptr a) where
  pretty pa = pretty $ show pa

-- Pretty Utils
-- ============
instance Pretty a => Pretty (S.Set a) where
  pretty s = case S.toList s of
               [] -> pretty "emptyset"
               xs -> indent 1 $ vcat $ [pretty "{"] ++ (map pretty xs)  ++ [pretty "}"]

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
  pretty m = 
    if M.null m 
       then pretty "emptymap" 
       else (indent 4 (vcat $ [
                vcat [pretty k <+> pretty "->", indent 4 $ (pretty v)]
                | (k, v) <- M.toList m]))


(!!#) :: HasCallStack => Ord k => Pretty k => Pretty v => M.Map k v -> k -> v
(!!#) m k = 
  case M.lookup k m of
    Just v -> v
    Nothing -> error . docToString $  
                vcat [pretty "==", pretty "* missing key: ", pretty k,
                  pretty "* in map: ", pretty m]


-- Helper to repeat till fixpoint
-- ===============================
repeatTillFix :: (Eq a) =>  (a -> a) -> a -> a
repeatTillFix f a =
  let a' = f a in
  if a == a' then a else repeatTillFix f a'


-- repeat till fixpoint, or the max count
repeatTillFixDebug :: Eq a => Int -> (a -> a) -> a -> a
repeatTillFixDebug 0 f a = a
repeatTillFixDebug n f a = 
  let a' = f a in if a' == a then a else repeatTillFixDebug (n - 1) f a'


repeatTillFixDebugTrace :: Eq a => Int -> (a -> a) -> a -> [a]
repeatTillFixDebugTrace 0 f a = [a]
repeatTillFixDebugTrace n f a = 
  let a' = f a in if a' == a then [a] else a:repeatTillFixDebugTrace (n - 1) f a'

repeatTillFixDebugTraceM :: (Monad m) => Int -> (a -> a -> Bool) -> (a -> m a) -> a -> m [a]
repeatTillFixDebugTraceM 0 eqf f a = return [a]
repeatTillFixDebugTraceM n eqf f a = do
  a' <- f a
  if eqf a a' 
  then return [a]
  else do
    as <- repeatTillFixDebugTraceM (n - 1) eqf f a'
    return (a' : as)

