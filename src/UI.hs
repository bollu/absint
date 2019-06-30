{-# LANGUAGE RecordWildCards #-}
module UI(UI.render) where
import IR

import Brick
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

data S a = S { l :: L.GenericList () [] (Widget N), niters :: Int, curiter :: Int, loc2a :: Loc -> a }


renderphi :: Show a => (Loc -> a) ->  Phi -> Widget N
renderphi loc2a a = padLeft (Pad 4) $ padBottom (Pad 1) $ (str . show . loc2a . location $ a) <=> (str . show $ a)

renderassign :: Show a => (Loc -> a) -> Assign -> Widget N
renderassign loc2a x = padLeft (Pad 4) $padBottom (Pad 1) $ (str . show . loc2a . location $ x) <=> (str . show $ x)

renderterm :: Show a => (Loc -> a) -> Term -> Widget N
renderterm loc2a x =  padLeft (Pad 4) $padBottom (Pad 1) $ (str . show . loc2a . location $ x) <=> (str . show $ x)

renderbb :: Show a => (Loc -> a) -> BB -> [Widget N]
renderbb loc2a bb = 
  [padBottom (Pad 1) $ (str . show . loc2a . bbloc $ bb) <=> str (show (bbloc bb) ++ " " ++ show(bbid bb))] ++ 
  map (renderphi loc2a) (bbphis bb) ++ 
  map (renderassign loc2a) (bbinsts bb) ++ 
  [renderterm loc2a (bbterm bb)]

renderprogram :: Show a => (Loc -> a) -> Program -> [Widget N]
renderprogram loc2a p =  (concatMap (renderbb loc2a) (progbbs p))

initS :: Show a => Program ->  (Loc -> a) -> S a
initS p loc2a = S {
  l = (L.list  () (renderprogram loc2a p) 3)
  , niters = 10
  , curiter = 0
  , loc2a = loc2a
}

drawiters :: S a -> Widget N
drawiters s = str $ "iter: " ++ show (curiter s) ++ "/" ++ show (niters s)


drawcode :: Show a => S a -> Widget N
drawcode S{..} = 
 let hasFocus = True
     -- | render :: Bool -> e -> Widget N
     render True e = (str  "->") <+> e 
     render False e = (str  "  ") <+> e 
     in B.border (vLimit 30 (L.renderList render hasFocus l))

draw :: Show a => S a -> [Widget N]
draw s = 
 let hasFocus = True
     -- | render :: Bool -> e -> Widget N
     render True e = str $ "->" ++ e 
     render False e = str $ "  " ++e 
 in [drawiters s <=> drawcode s]

chooseCursor :: (S a) -> [CursorLocation N] -> Maybe (CursorLocation N)
chooseCursor _ [] = Nothing
chooseCursor _ (x:xs) = Just x

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
  continue $ s {l = l'}

startEvent :: S a -> EventM N (S a)
startEvent s = return s


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

render :: Show a => Program -> (Loc -> a) -> IO ()
render p f = do
    s <- defaultMain app (initS p f)
    return ()

