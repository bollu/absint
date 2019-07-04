{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module UI(UI.render, Iteration(..)) where
import IR

import Brick
import Data.Maybe(fromMaybe)
import Graphics.Vty.Attributes (defAttr)
import qualified Data.Set as S
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

newtype Iteration = Iteration Int deriving(Eq, Ord, Show, Num)

type N = ()

instance L.Splittable [] where
  splitAt = PreludeList.splitAt

-- | A UI Node has a location, possibly an ID, and a string of what is to be
-- printed
data UINode = UINode Loc (Maybe Id) String

instance Located UINode where
  location (UINode loc _ _) = loc


drawUINode :: Show a => (Id -> a) -> UINode -> (Widget N)
drawUINode id2a (UINode _ Nothing rhs) =
  padBottom (Pad 1) $ padTop (Pad 1) $  str rhs
drawUINode id2a (UINode _ (Just id) rhs) =
  padBottom (Pad 1) $ (str . show . id2a $ id)  <=>  str rhs


data S a = S { l :: L.GenericList () [] UINode
             , niters :: Iteration
             , curiter :: Iteration
             , curloc :: Loc
             , info :: Iteration -> Loc -> Id -> a }


mkUINodeGeneric :: (Show a, Located a, IR.Named a) => a -> UINode
mkUINodeGeneric x =  UINode (location x) (Just . name $ x) (show x)

mkUINodeTerm x =  UINode (location x) Nothing (show x)

mkUINodeBB :: BB -> [UINode]
mkUINodeBB bb =
  [UINode (location bb) (Just . name $ bb) ((show . unID . bbid $ bb) <> ":")] ++
  map mkUINodeGeneric (bbphis bb) ++
  map mkUINodeGeneric (bbinsts bb) ++
  [mkUINodeTerm (bbterm bb)]

mkUINodeParams :: Program -> [UINode]
mkUINodeParams program =
    let ps = S.toList (progparams program)
     in [UINode (progEntryLoc program) (Just p) (show p) | p <- ps]

mkUINodeProgram :: Program -> [UINode]
mkUINodeProgram p =
  mkUINodeParams p ++ concatMap mkUINodeBB (progbbs p)

initS :: Show a => Program
      ->  (Iteration -> Loc -> Id -> a)
      -> Iteration -> S a
initS p f niters = S {
  l = (L.list  () (mkUINodeProgram p) 3)
  -- | Total number of iterations.
  , niters = niters
  -- | Current iteration.
  , curiter = 0
  -- | Currently selected location.
  , curloc = startloc
  -- | Function mapping iteration, location, and identifier to a value
  ,info = f
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
     render selected e = drawSelectedPtr selected <+>
                         drawUINode (info curiter  curloc) e
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
  -> (Iteration -> Loc -> Id -> a)
  -> Iteration
  -> IO ()
render p info niters = do
    s <- defaultMain app (initS p info niters)
    return ()

