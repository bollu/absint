{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
module IR where
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import qualified Data.Set as S
import qualified Control.Monad.State as ST
import qualified Data.Map.Strict as M
import qualified OrderedMap as OM
import Data.List (elemIndex)
import Control.Monad(guard)
import Util
import Data.Maybe (catMaybes, fromJust)

-- Identifiers
newtype Id = Id { unID:: String } deriving(Eq, Ord)
instance Show Id where
  show (Id s) = s

class Named a where
  name :: a -> Id

instance Pretty Id where
  pretty (Id s) =  pretty s

-- Concrete Syntax
data Binop = Add | Lt deriving(Eq, Ord)
instance Show Binop where
  show Add = "op:+"
  show Lt = "op:<"

instance Pretty Binop where
  pretty Add = pretty "+."
  pretty Lt = pretty "<."


data Expr = EInt !Int
    | EBinop !Binop !Id !Id
    | EId Id
  deriving(Eq, Ord)

instance Show Expr where
    show (EInt i) = show i
    show (EId id) = show id
    show (EBinop  op e1 e2) =
        "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Pretty Expr where
  pretty (EInt i) = pretty i
  pretty (EId id) = pretty id
  pretty (EBinop op e1 e2) = parens $  pretty e1 <+> pretty op <+> pretty e2


-- Program counter
data Loc = Loc { unLoc :: !Int } deriving(Eq, Ord)

instance Show Loc where
  show (Loc pc) = "loc:" ++ show pc

instance Pretty Loc where
  pretty = pretty . show

locincr :: Loc -> Loc
locincr (Loc i) = Loc (i + 1)

pcinit :: Loc
pcinit = Loc 0

class Located a where
  location :: a -> Loc

instance Located Loc where
    location = id


type BBId = Id

-- Instructions
data Assign = Assign {
    assignloc :: !Loc,
    assignownbbid :: !BBId,
    assignid :: !Id,
    assignexpr :: !Expr
}deriving(Eq, Ord)

instance Pretty Assign where
  pretty (Assign pc bbid id expr) =
    pretty pc <+> pretty bbid <+> pretty id <+> equals <+> pretty expr

instance Show Assign where
  show (Assign pc bbid id expr) =
    show pc <> " " <> show bbid <> "  " <>
    show id <> " =  " <> show expr

instance Located Assign where
  location = assignloc

instance Named Assign where
  name = assignid

-- Phi nodes
data Phity = Philoop | Phicond deriving(Eq, Ord)

instance Show Phity where
  show (Philoop) = "loop"
  show (Phicond) = "cond"

instance Pretty Phity where
  pretty = pretty . show

data Phi = Phi {
    philoc :: !Loc,
    phity :: Phity,
    phiid :: Id,
    phil :: (BBId, Id),
    phir :: (BBId, Id)
} deriving(Eq, Ord)

instance Named Phi where
  name = phiid

instance Located Phi where
  location (Phi loc ty _ _ _) = loc

instance Pretty Phi where
  pretty (Phi loc ty id l r) =
    pretty loc <+> pretty "phi" <+> pretty ty <+>
      pretty id <+> equals <+> pretty l <+> pretty r

instance Show Phi where
  show (Phi loc ty id l r) =
    show loc ++  " phi " ++ show ty ++
      " " ++ show id ++ " = " ++ show l ++ " " ++ show r

-- Terminator instruction
data Term = Br !Loc BBId BBId
          | BrCond !Loc BBId Id BBId BBId
          | Done !Loc BBId deriving(Eq, Ord, Show)

instance Located Term where
  location (Br loc _ _) = loc
  location (BrCond loc _ _ _ _) = loc
  location (Done loc _ ) = loc

instance Pretty Term where
  pretty (Br pc selfid bbid) = pretty pc <+> pretty selfid <+> pretty "br" <+> pretty bbid
  pretty (BrCond pc selfid cid bbidl bbidr) =
    pretty pc <+> pretty selfid <+> pretty "brcond" <+>
      pretty cid <+> pretty bbidl <+> pretty bbidr
  pretty (Done selfid loc) = pretty loc <+> pretty selfid <+> pretty "done"

-- get next basic blocks from terminator
termnextbbs :: Term -> [BBId]
termnextbbs (Done  _ _) = []
termnextbbs (Br _ _ bb) = [bb]
termnextbbs (BrCond _ _ _ bbl bbr) = [bbl, bbr]

data BBTy =
  BBLoop (S.Set BBId) -- if it's a loop, the list of basic blocks that are bodies of this loop
  deriving(Eq, Ord, Show)

instance Pretty BBTy where
  pretty (BBLoop bs) = pretty "bbloop"  <+> pretty bs

data BB = BB {
 bbid :: BBId,
 bbty :: Maybe BBTy,
 bbloc :: Loc,
 bbphis :: [Phi],
 bbinsts :: [Assign],
 bbterm :: Term
}deriving(Eq, Ord, Show)

instance Named BB where
  name = bbid

instance Pretty BB where
  pretty (BB bbid bbty bbloc phis is term) =
    pretty bbloc <+> pretty bbid <+> pretty bbty <> line <>
      indent 4 (vcat $ (map pretty phis) ++  (map pretty is) ++ [pretty term])

instance Located BB where
  location (BB _ _ loc _ _ _) = loc


bbModifyInsts :: ([Assign] -> [Assign]) -> BB -> BB
bbModifyInsts f (BB id ty loc phis insts term) =
  BB id ty loc phis (f insts) term

bbModifyPhis :: ([Phi] -> [Phi]) -> BB -> BB
bbModifyPhis f (BB id ty loc phis insts term) =
  BB id ty loc (f phis) insts term

bbModifyTerm :: (Term -> Term) -> BB -> BB
bbModifyTerm f (BB id ty loc phis insts term) =
  BB id ty loc phis insts (f term)

-- return locations of everything in the BB
bbGetLocs :: BB -> [Loc]
bbGetLocs (BB _ _ loc phis insts term) =
  [loc] ++ (map location phis) ++ (map location insts) ++ [location term]



-- | Get final location in a basic block
bbFinalLoc :: BB -> Loc
bbFinalLoc =  last . bbGetLocs

-- | Get the location before a given location in the basic block
bbGetPrevLoc :: Located a => BB -> a -> Loc
bbGetPrevLoc bb a =
    let l = location a
        ls = bbGetLocs bb
        mix = elemIndex l ls
    in fromJust $ do
        ix <- mix
        guard (ix > 0)
        return $ ls !! (ix - 1)


-- | Get the location right after a given location in the basic block
bbGetNextLoc :: Located a => BB -> a -> Loc
bbGetNextLoc bb a =
    let l = location a
        ls = bbGetLocs bb
        mix = elemIndex l ls
    in fromJust $ do
        ix <- mix
        guard (ix + 1 < length ls)
        return $ ls !! (ix + 1)

-- | get the location of the first instruction in the BB
bbFirstInstLoc :: BB -> Loc
bbFirstInstLoc bb =
    head $ (map location (bbphis bb)) ++
            (map location (bbinsts bb)) ++
             [location (bbterm bb)]

bbGetIds :: BB -> [Id]
bbGetIds (BB _ _ _ phis assigns _) =
    map phiid phis ++ map assignid assigns


-- | Get edges out of BB
bbedges :: BB -> [(BBId, BBId)]
bbedges bb = map (bbid bb,) (termnextbbs . bbterm $ bb)

-- Program is a collection of basic blocks, and list of input parameter names.
-- First basic block is the entry block (block that gets executed on startup)
data Program = Program { progparams :: S.Set Id, progbbs :: [BB]  } deriving(Eq)

-- | Get a basic block with the ID
progGetBB :: BBId -> Program -> BB
progGetBB curid p = head . filter ((curid ==) . bbid) . progbbs $ p


-- | get entry block
progBBEntry :: Program -> BB
progBBEntry p = head (progbbs p)

-- | Location of start block
progStartLoc :: Program -> Loc
progStartLoc = location . progBBEntry


-- | get the entry basic block ID
progEntryId :: Program -> BBId
progEntryId  = bbid . progBBEntry

-- | Location of entry basic block
progEntryLoc :: Program -> Loc
progEntryLoc = location . progBBEntry

-- | IDs of variables in the program, *no* parameters
progvarids :: Program -> S.Set Id
progvarids p = (S.fromList (progbbs p >>= bbGetIds))


-- | Virtual induction variables in the program
progvivs :: Program -> S.Set Id
progvivs p = S.fromList $ map (nlheader) (prognls p)

-- | Edges in the program
progedges :: Program -> [(BBId, BBId)]
progedges p = progbbs p >>= bbedges

-- Create a map, mapping basic block IDs to basic blocks
-- for the given program
progbbid2bb :: Program -> M.Map BBId BB
progbbid2bb (Program _ bbs) =
  foldl (\m bb -> M.insert (bbid bb) bb m) M.empty bbs

-- | Mapping from basic header IDs to natural loops
progbbid2nl :: Program -> M.Map BBId NaturalLoop
progbbid2nl (Program _ bbs) = M.fromList $ do
  bb <- bbs
  let ty = bbty bb
  case ty of
    Just (BBLoop bodies) -> return (bbid bb, NaturalLoop (bbid bb) bodies)
    Nothing -> []

-- | Map baic block ids to predecessors
progbbid2preds :: Program -> M.Map BBId [BB]
progbbid2preds p =
    let existing = M.fromListWith (++) $ (do
            bb <- progbbs p
            bbn <- termnextbbs . bbterm $ bb
            return $ (bbn, [bb]))
        empty = M.fromList $ [(bbid bb, [])  | bb <- progbbs p]
    in M.unionWith (++) existing empty




-- get the largest location
programMaxLoc :: Program -> Loc
programMaxLoc (Program _ bbs) =
  let locs = bbs >>= bbGetLocs
   in maximum locs

instance Pretty Program where
  pretty (Program params bbs) = vcat $
    [pretty "prog" <> parens (pretty (S.toList params)),
            (indent 1 $ (vcat  $ map pretty bbs))]


data NaturalLoop =
  NaturalLoop { nlheader :: BBId, nlbody :: S.Set BBId } deriving(Eq, Ord, Show)

instance Pretty NaturalLoop where
  pretty (NaturalLoop header body) =
    pretty "natural loop" <+> pretty header <+> pretty body

nl2loopid :: NaturalLoop -> Id
nl2loopid = nlheader


-- Return if the natural loop contains the basic block
nlContainsBB :: BBId -> NaturalLoop ->  Bool
nlContainsBB id (NaturalLoop headerid bodyids) =
  id == headerid || id `S.member` bodyids


-- | extract a natural loop if the BB represents one
bbloopheaderLoops :: BB -> Maybe NaturalLoop
bbloopheaderLoops bb = fmap
    (\(BBLoop bbs) -> NaturalLoop (bbid bb) bbs) (bbty bb)


-- | Get all natural loops in the program
prognls :: Program -> [NaturalLoop]
prognls p = catMaybes . (map bbloopheaderLoops) . progbbs $ p


-- Program builder
-- ===============
-- ===============

(+.) :: String -> String -> Expr
(+.) id id' = EBinop Add (Id id) (Id id')


(<.) :: String -> String -> Expr
(<.) id id' = EBinop Lt (Id id) (Id id')


-- Builder of program state
data ProgramBuilder = ProgramBuilder {
  builderparams ::  S.Set Id,
  builderpc :: Loc,
  curbbid :: Maybe BBId,
  bbid2bb :: OM.OrderedMap BBId BB
}

-- | Initial location.
-- NOTE: This information is used by UI to set the
-- starting location in the UI
startloc :: Loc
startloc = Loc (-1)

runProgramBuilder :: ST.State ProgramBuilder () -> Program
runProgramBuilder pbst =
  let pbinit :: ProgramBuilder
      pbinit = ProgramBuilder mempty startloc Nothing OM.empty

      pbout :: ProgramBuilder
      pbout = ST.execState pbst pbinit

      progbbs :: [BB]
      progbbs = map snd (OM.toList (bbid2bb pbout))

      progparams = builderparams pbout
   in Program progparams progbbs

param :: String -> ST.State ProgramBuilder Expr
param pname = do
  ST.modify (\s -> s {
    builderparams = (Id pname) `S.insert` (builderparams s) })
  return (EId (Id pname))

builderLocIncr :: ST.State ProgramBuilder Loc
builderLocIncr = do
  loc <- ST.gets builderpc
  ST.modify (\s -> s { builderpc = locincr (builderpc s) })
  return loc

-- builds a new basic block, but *does not focus on it*
buildNewBB :: String -> Maybe BBTy -> ST.State ProgramBuilder BBId
buildNewBB name ty = do
  loc <- builderLocIncr
  locret <- builderLocIncr
  let bbid = Id name
  let bb = BB bbid ty loc [] [] (Done locret bbid)
  ST.modify (\s -> s { bbid2bb = OM.insert bbid bb (bbid2bb s) } )

  return bbid

focusBB :: BBId -> ST.State ProgramBuilder ()
focusBB bbid = ST.modify (\s -> s { curbbid = Just bbid })

builderCurBBModify :: (BB -> BB) -> ST.State ProgramBuilder ()
builderCurBBModify f =
  ST.modify (\s -> let m = bbid2bb s
                       (Just bbid) = curbbid s
                       m' = OM.adjust f bbid m
                 in s { bbid2bb = m' })


appendInst :: Assign -> ST.State ProgramBuilder ()
appendInst i = builderCurBBModify (bbModifyInsts (++ [i]))

appendPhi :: Phi -> ST.State ProgramBuilder ()
appendPhi ph = builderCurBBModify (bbModifyPhis (++ [ph]))

setTerm :: Term -> ST.State ProgramBuilder ()
setTerm term = builderCurBBModify (bbModifyTerm (const term))

assign :: String -> Expr -> ST.State ProgramBuilder ()
assign id e = do
  loc <- builderLocIncr
  ownbbid <- fromJust <$>  ST.gets curbbid
  appendInst (Assign loc ownbbid (Id id) e)

done :: ST.State ProgramBuilder ()
done = do
  loc <- builderLocIncr
  ownbbid <- fromJust <$>  ST.gets curbbid
  setTerm (Done loc ownbbid)

phi :: Phity -> String -> (BBId, String) -> (BBId, String) -> ST.State ProgramBuilder ()
phi ty id (bbidl, idl) (bbidr, idr) = do
  loc <- builderLocIncr
  appendPhi (Phi loc ty (Id id) (bbidl, Id idl) (bbidr, Id idr))

condbr :: String -> BBId -> BBId -> ST.State ProgramBuilder ()
condbr id bbidt bbidf = do
  loc <- builderLocIncr
  ownbbid <- fromJust <$>  ST.gets curbbid
  setTerm (BrCond loc ownbbid (Id id) bbidt bbidf)


br :: BBId -> ST.State ProgramBuilder ()
br bbid = do
  loc <- builderLocIncr
  ownbbid <- fromJust <$>  ST.gets curbbid
  setTerm (Br loc ownbbid bbid)
