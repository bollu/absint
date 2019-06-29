module UI(renderProgram) where
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

newtype S = S { l :: L.GenericList () [] String }

phiflatten :: Phi -> String
phiflatten = show

assignflatten :: Assign -> String
assignflatten a = show a

termflatten :: Term -> String
termflatten t = show t

bbflatten :: BB -> [String]
bbflatten bb = 
  [show (bbloc bb) ++ " " ++ show(bbid bb)] ++ 
  map phiflatten (bbphis bb) ++ 
  map assignflatten (bbinsts bb) ++ 
  [termflatten (bbterm bb)]

pflatten :: Program -> [String]
pflatten p = concatMap bbflatten (progbbs p)

initS :: Program ->  S
initS p = S (L.list  () (pflatten p) 2)

draw :: S -> [Widget N]
draw s = 
 let hasFocus = True
     -- | render :: Bool -> e -> Widget N
     render True e = str $ "->" ++ e 
     render False e = str $ "  " ++e 
 in [L.renderList render hasFocus (l s)]

chooseCursor :: S -> [CursorLocation N] -> Maybe (CursorLocation N)
chooseCursor _ [] = Nothing
chooseCursor _ (x:xs) = Just x

handleEvent :: S -> BrickEvent N e -> EventM N (Next S)
handleEvent s (VtyEvent (V.EvKey V.KEsc [])) = halt s
handleEvent s (VtyEvent e) = do
  l' <- L.handleListEvent e (l s) 
  continue $ S l'

startEvent :: S -> EventM N S
startEvent s = return s


mkAttrMap :: S -> AttrMap
mkAttrMap s = attrMap defAttr []

app :: App S e N
app = App {
  appDraw = draw
  , appChooseCursor = chooseCursor
  , appHandleEvent = handleEvent
  , appStartEvent = startEvent
  , appAttrMap = mkAttrMap
}

renderProgram :: Program -> (Loc -> a) -> IO ()
renderProgram p f = do
    s <- defaultMain app (initS p)
    return ()

