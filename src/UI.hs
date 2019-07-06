{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
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
import PolySCEV
import Brick.Util (on)
import Brick.Util (on)
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..),
  Aff, Pwaff, Ctx, Space, LocalSpace, Map, Set, Constraint)
import Absdomain
import qualified ISL.Native.Types as ISLTy (Id)

newtype Iteration = Iteration Int deriving(Eq, Ord, Show, Num)

type N = ()

instance L.Splittable [] where
  splitAt = PreludeList.splitAt

-- | Attributes for various UI nodes used to control style
highlightedAttr, locAttr, vAttr :: AttrName
highlightedAttr = "highlighted"
locAttr = "loc"
vAttr = "v"

-- | vertical space each UI Node takes.
vspaceUINode :: Int
vspaceUINode  = 3


-- | Indentation
windent :: Int -> Widget N
windent n = str $ (replicate n ' ')


-- | A UI Node has a location, possibly an ID, and a string of what
-- is to be printed
data UINode =
    UINode { uiloc :: (Maybe Loc)
           , uiid :: (Maybe Id)
           , uistr :: String
           , uiindent :: Int
           }


-- | Render the location
drawLoc :: Loc -> Widget N
drawLoc (Loc l) = withAttr locAttr $ hLimit 3 $ padRight Max $  str $ show l

-- | Draw the abstract info
drawV :: V -> Widget N
drawV v = withAttr vAttr $
  (str $ "P: " <> (show . dropUnusedParams . vp $ v)) <=>
  (str $ "S: " <> (show . dropUnusedParams . vs $ v))

drawUINode :: (Id -> Maybe V)
  -> UINode -> Widget N
drawUINode f UINode{..} =
    let wv = case uiid >>= f of
                Just v -> drawV v
                Nothing -> emptyWidget
        wnode = str uistr
        wloc = case uiloc of
                 Just l -> drawLoc l
                 Nothing -> emptyWidget
     in (wloc) <+> (padLeft (Pad uiindent)  (wv <=> wnode))


data S = S { l :: L.GenericList () [] UINode
             , niters :: Iteration
             , curiter :: Iteration
             , curloc :: Loc
             , info :: Iteration -> Loc -> Id -> Maybe V }


mkUINodeAssign :: Assign -> UINode
mkUINodeAssign (Assign loc ownbbid id expr) =
    UINode (Just loc) (Just id) (unID id <> " = " <> show expr) 4

mkUINodePhi :: Phi -> UINode
mkUINodePhi (Phi loc ty id l r) =
    UINode (Just loc) (Just id)
           ("phi " <> (unID id) <> " = " <> show l <> " " <> show r)
           4

mkUINodeTerm :: Term -> UINode
mkUINodeTerm t = let
  s = case t of
        Done _ _ -> "done"
        Br _ l r -> "br " <> show l <> " " <>  show r

        BrCond _ _  c l r -> "brcond " <> show c <> " " <>
                          show l <> " " <>
                          show r
  in UINode (Just . location $ t) Nothing s 4

mkUINodeBBHeader :: BB -> UINode
mkUINodeBBHeader bb =
    UINode (Just . location $ bb)
           (Just . name $ bb)
           ((unID . bbid $ bb) <> ":")
           0

mkUINodeBB :: BB -> [UINode]
mkUINodeBB bb =
  [mkUINodeBBHeader bb] ++
  map mkUINodePhi (bbphis bb) ++
  map mkUINodeAssign (bbinsts bb) ++
  [mkUINodeTerm (bbterm bb)]

mkUINodeParams :: Program -> [UINode]
mkUINodeParams program =
    let ps = S.toList (progparams program)
     in [UINode Nothing (Just p) (show p) 0 | p <- ps]

mkUINodeProgram :: Program -> [UINode]
mkUINodeProgram p =
  mkUINodeParams p ++ concatMap mkUINodeBB (progbbs p)

initS :: Program
      ->  (Iteration -> Loc -> Id -> Maybe V)
      -> Iteration -> S
initS p f niters = S {
  l = (L.list  () (mkUINodeProgram p) vspaceUINode)
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
drawiters :: S -> Widget N
drawiters s = str $ "iter: " ++ show (curiter s) ++ "/" ++ show (niters s)


-- | Arrow that points at the selected element of the list
drawSelectedPtr :: Bool -> Widget N
drawSelectedPtr False = vBox $ replicate vspaceUINode (str " ")
drawSelectedPtr True = vBox $ replicate vspaceUINode (str ">")

-- | Draw the code window
drawcode :: S -> Widget N
drawcode S{..} =
 let
     hasFocus = True
     -- | Id -> Maybe V
     f = info  curiter curloc
     -- | render :: Bool -> e -> Widget N
     render True e = forceAttr highlightedAttr $
       drawSelectedPtr True <+> drawUINode f e
     render False e = drawSelectedPtr False <+> drawUINode f e

       -- | Find a way to find out if this has focus
     in B.border ((L.renderList render hasFocus l))

-- | toplevel draw function
draw :: S -> [Widget N]
draw s = [drawiters s <=> drawcode s]

-- | Choose the cursor we wish to focus on
chooseCursor :: S -> [CursorLocation N] -> Maybe (CursorLocation N)
chooseCursor _ [] = Nothing
chooseCursor _ (x:xs) = Just x

-- | toplevel event hander
handleEvent :: S -> BrickEvent N e -> EventM N (Next S)
handleEvent s (VtyEvent (V.EvKey V.KEsc [])) = halt s
handleEvent s (VtyEvent (V.EvKey (V.KChar 'q') [])) = halt s

handleEvent s@S{..} (VtyEvent (V.EvKey V.KLeft [])) =
    continue $ s { curiter = max (curiter - 1) 0 }

handleEvent s@S{..} (VtyEvent (V.EvKey V.KRight [])) =
    continue $ s { curiter = min (curiter + 1) niters }

handleEvent s@S{..} (VtyEvent (V.EvKey V.KUp [V.MShift])) = 
    continue $ s { l = L.listMoveBy (-2) l}

handleEvent s@S{..} (VtyEvent (V.EvKey V.KDown [V.MShift])) = 
    continue $ s { l = L.listMoveBy 2 l}


handleEvent s (VtyEvent e) = do
  l' <- L.handleListEvent e (l s)
  -- | Get the new selected location. If it's the old one,
  -- then just use it. Otherwise, get the location
  -- from the newly selected one.
  let newloc = fromMaybe
                 (curloc s)
                 (do
                     (_, n) <- L.listSelectedElement l'
                     uiloc n
                 )
  continue $ s {l = l', curloc = newloc}


-- | Initial event
startEvent :: S -> EventM N S
startEvent s = return s


-- | No idea what this does.
mkAttrMap :: S -> AttrMap
mkAttrMap s = attrMap defAttr
  [(locAttr, V.defAttr `V.withStyle` V.dim)
  , (highlightedAttr, V.defAttr `V.withStyle` V.bold `V.withForeColor` V.blue)
  , (vAttr, V.defAttr `V.withStyle` V.dim)
  ]

app :: App S e N
app = App {
  appDraw = draw
  , appChooseCursor = chooseCursor
  , appHandleEvent = handleEvent
  , appStartEvent = startEvent
  , appAttrMap = mkAttrMap
}


-- | Function exposed to outside world that render the TUI
render :: Program
  -> (Iteration -> Loc -> Id -> Maybe V)
  -> Iteration
  -> IO ()
render p info niters = do
    s <- defaultMain app (initS p info niters)
    return ()

