{-# LANGUAGE RecordWildCards #-}
module UI(UI.render) where
import IR

import Brick
import Data.Maybe(fromMaybe)
import Graphics.Vty.Attributes (defAttr)
import qualified Graphics.Vty as V
import qualified Brick.Main as M
import qualified Brick.Types as T
import Brick.Widgets.Core
  ( (<+>)
  , (<=>)
  , hLimit
  , vLimit
  , str
  )
import qualified Brick.Widgets.Center as C
import qualified Brick.Widgets.Border as B
import qualified Brick.Widgets.Edit as E
import qualified Brick.AttrMap as A
import qualified Brick.Focus as F
import qualified Brick.Widgets.ProgressBar as P
import qualified Brick.Widgets.List as L
import qualified Data.List as PreludeList(splitAt)

import Brick.Util (on)

import Brick.Util (on)

type N = ()

instance L.Splittable [] where
  splitAt = PreludeList.splitAt

-- | A UI Node has a location, possibly an ID, and a string of what is to be
-- printed
data UINode = UINode Loc (Maybe Id) String

instance Located UINode where
  location (UINode loc _ _) = loc


drawUINode :: Show a => (Id -> a) -> UINode -> (Widget N)
drawUINode id2a (UINode _ Nothing rhs) = padBottom (Pad 1) $ padTop (Pad 1) $  str rhs
drawUINode id2a (UINode _ (Just id) rhs) =
  padBottom (Pad 1) $ (str . show . id2a $ id)  <=>  str rhs


data S a = S { l :: L.GenericList () [] UINode
             , niters :: Int
             , curiter :: Int
             , curloc :: Loc
             , locid2a :: Loc -> Id -> a }


mkUINodeGeneric :: (Show a, Located a, IR.Named a) => a -> UINode
mkUINodeGeneric x =  UINode (location x) (Just . name $ x) (show x)

mkUINodeTerm x =  UINode (location x) Nothing (show x)

mkUINodeBB :: BB -> [UINode]
mkUINodeBB bb =
  [UINode (location bb) (Just . name $ bb) ((show . unID . bbid $ bb) <> ":")] ++ 
  map mkUINodeGeneric (bbphis bb) ++ 
  map mkUINodeGeneric (bbinsts bb) ++ 
  [mkUINodeTerm (bbterm bb)]

mkUINodeProgram :: Program -> [UINode]
mkUINodeProgram p =
  concatMap mkUINodeBB (progbbs p)

initS :: Show a => Program ->  (Loc -> Id -> a) -> S a
initS p f = S {
  l = (L.list  () (mkUINodeProgram p) 3)
  -- | Total number of iterations.
  , niters = 10
  -- | Current iteration.
  , curiter = 0
  -- | Currently selected location.
  , curloc = startloc
  -- | Function mapping location and identifier to value.
  , locid2a = f
}

-- | Top bar that draws number of iterations
drawiters :: S a -> Widget N
drawiters s = str $ "iter: " ++ show (curiter s) ++ "/" ++ show (niters s)


-- | Arrow that points at the selected element of the list
drawSelectedPtr :: Bool -> Widget N
drawSelectedPtr False = str "  "
drawSelectedPtr True = str "->"

-- | Draw the code window
drawcode :: Show a => S a -> Widget N
drawcode S{..} = 
 let
     hasFocus = True
     -- | render :: Bool -> e -> Widget N
     render selected e = drawSelectedPtr selected <+> drawUINode (locid2a curloc) e
      -- | Find a way to find out if this has focus
     in B.border (vLimit 30 (L.renderList render hasFocus l))

-- | toplevel draw function
draw :: Show a => S a -> [Widget N]
draw s = [drawiters s <=> drawcode s]

-- | Choose the cursor we wish to focus on
chooseCursor :: (S a) -> [CursorLocation N] -> Maybe (CursorLocation N)
chooseCursor _ [] = Nothing
chooseCursor _ (x:xs) = Just x

-- | toplevel event hander
handleEvent :: S a -> BrickEvent N e -> EventM N (Next (S a))
handleEvent s (VtyEvent (V.EvKey V.KEsc [])) = halt s
handleEvent s (VtyEvent (V.EvKey (V.KChar 'q') [])) = halt s

handleEvent s@S{..} (VtyEvent (V.EvKey V.KLeft [])) = 
    continue $ s { curiter = max (curiter - 1) 0 }
handleEvent s@S{..} (VtyEvent (V.EvKey (V.KChar 'h') [])) = 
    continue $ s { curiter = max (curiter - 1) 0 }

handleEvent s@S{..} (VtyEvent (V.EvKey V.KRight [])) = 
    continue $ s { curiter = min (curiter + 1) niters }
handleEvent s@S{..} (VtyEvent (V.EvKey (V.KChar 'l') [])) = 
    continue $ s { curiter = max (curiter - 1) 0 }

handleEvent s (VtyEvent e) = do
  l' <- L.handleListEventVi L.handleListEvent e (l s)
  -- | Get the new selected location. If it's the old one,
  -- then just use it. Otherwise, get the location
  -- from the newly selected one.
  let newloc = fromMaybe
                 (curloc s)
                 (location . snd <$> L.listSelectedElement l')
  continue $ s {l = l', curloc = newloc}


-- | Initial event
startEvent :: S a -> EventM N (S a)
startEvent s = return s


-- | No idea what this does.
mkAttrMap :: S a -> AttrMap
mkAttrMap s = attrMap defAttr []

app :: Show a => App (S a) e N
app = App {
  appDraw = draw
  , appChooseCursor = chooseCursor
  , appHandleEvent = handleEvent
  , appStartEvent = startEvent
  , appAttrMap = mkAttrMap
}

-- | Function exposed to outside world that render the TUI
render :: Show a => Program
  -> (Loc -> Id -> a)
  -> IO ()
render p f = do
    s <- defaultMain app (initS p f)
    return ()

