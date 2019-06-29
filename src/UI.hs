module UI(renderProgram) where
import IR

import Brick
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
import Brick.Util (on)

import Brick.Util (on)

newtype S = S ()

initS :: S
initS = S ()

app :: App S e ()
app = simpleApp $ P.progressBar (Just "progress") 0.5

renderProgram :: Program -> (Loc -> a) -> IO ()
renderProgram p f = do
    s <- defaultMain app initS 
    return ()

