{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where
import qualified Data.Map.Strict as M
import qualified OrderedMap as OM
import qualified Data.Map.Merge.Strict as M
import qualified Data.Set as S
import Data.List (intercalate, nub)
import Data.Semigroup
import qualified Control.Monad.State as ST
import Data.Foldable
import Control.Applicative
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import Control.Exception (assert)
import Data.Maybe (catMaybes)
import ISL.Native.C2Hs
import ISL.Native.Types (DimType(..))

-- Pretty Utils
-- ============

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
  pretty m = 
    if M.null m 
       then pretty "{}" 
       else (vcat $ [pretty "|" <> pretty k <+> pretty ">>" <+> indent 1 (pretty v) | (k, v) <- M.toList m]) <> line

-- Lattice theory
-- ==============
-- top = join of all elements
class SemiJoin a where
  join :: a -> a -> a
  top :: a

-- bottom = meet of all elements 
class SemiMeet a where
  meet :: a -> a -> a
  bottom :: a

class (SemiJoin a, SemiMeet a) => Lattice a

instance SemiJoin a => SemiJoin (Maybe a) where
  top = Just top

  join Nothing a = a
  join a Nothing = a
  join (Just a) (Just b) = Just (join a b)

instance SemiMeet a => SemiMeet (Maybe a) where
  bottom = Nothing

  meet Nothing _ = Nothing
  meet _ Nothing = Nothing
  meet (Just a) (Just b) = Just (meet a b)

instance (SemiJoin a, SemiJoin b) => SemiJoin (a, b) where
  top = (top, top)
  join (a, b) (a', b') = (a `join` a', b `join` b')

instance (SemiMeet a, SemiMeet b) => SemiMeet (a, b) where
  bottom = (bottom, bottom)
  meet (a, b) (a', b') = (a `meet` a', b `meet` b')

instance (Lattice a, Lattice b) => Lattice (a, b)

data LiftedLattice a = LL !a | LLBot | LLTop deriving(Eq, Ord, Functor)

instance Pretty a => Pretty (LiftedLattice a) where
  pretty (LL a) = pretty a
  pretty LLBot = pretty "_|_"
  pretty LLTop = pretty "T"

instance Eq a => SemiJoin (LiftedLattice a) where
  top = LLTop

  join LLBot a = a
  join a LLBot = a
  join LLTop _ = LLTop
  join _ LLTop = LLTop
  join (LL a) (LL b) = if a == b then LL a else LLTop

instance Eq a => SemiMeet (LiftedLattice a) where
  bottom = LLBot

  meet LLBot _ = LLBot
  meet _ LLBot = LLBot
  meet a LLTop = a
  meet LLTop a = a
  meet (LL a) (LL b) = if a == b then LL a else LLBot

instance Eq a => Lattice (LiftedLattice a)



liftLL2 :: (a -> b -> c) -> LiftedLattice a -> LiftedLattice b -> LiftedLattice c
liftLL2 f LLTop _ = LLTop
liftLL2 f _ LLTop = LLTop
liftLL2 f LLBot _ = LLBot
liftLL2 f _ LLBot  = LLBot
liftLL2 f (LL a) (LL b) = LL (f a b)

instance Show a => Show (LiftedLattice a) where
  show LLBot = "_|_"
  show LLTop = "T"
  show (LL a) = show a


class Lattice a => BooleanAlgebra a where
  complement :: a -> a

-- implication in the boolean algebra
imply :: BooleanAlgebra a => a -> a -> a
imply a b = (complement a) `join` b

-- symbol
(===>) :: BooleanAlgebra a => a -> a -> a
(===>) = imply


-- Adjoin a top element 
data ToppedLattice a = TLTop | TL !a deriving (Eq, Ord, Functor)

instance Show a => Show (ToppedLattice a) where
  show TLTop = "T"
  show (TL a) = show a

data BottomedLattice a = TLBot | TB !a deriving(Eq, Ord, Functor)

instance Show a => Show (BottomedLattice a) where
  show TLBot = "_|_"
  show (TB a) = show a


-- A map based representation of a function (a -> b), which on partial
-- missing keys returns _|_
data SemiMeetMap k v = LM !(M.Map k v)  deriving (Eq, Ord, Functor)

-- Insert a regular value into a lattice map
lminsert :: Ord k => k -> v -> SemiMeetMap k v -> SemiMeetMap k v
lminsert k v (LM m) = LM $ M.insert k v m

-- pointwise produce of two lattice maps
-- If a value is missing in either lattice, put a bottom in its place
lmproduct :: (SemiMeet v, SemiMeet w, Ord k) => SemiMeetMap k v -> SemiMeetMap k w -> SemiMeetMap k (v, w)
lmproduct (LM m) (LM m') = let
  missingm' = M.mapMissing (\k w -> bottom)
  missingm =  M.mapMissing (\k v -> bottom)
  merger = M.zipWithMatched (\k tx ty -> (tx, ty))
  in LM $ M.merge missingm' missingm merger m m'

adjust :: Ord k => k -> (v -> v) -> SemiMeetMap k v -> SemiMeetMap k v
adjust k f (LM m) = LM $ M.adjust f k m

(!!!) :: (Ord k, SemiMeet v) => SemiMeetMap k v -> k -> v
(!!!) (LM m) k = case m M.!? k of
                   Just v -> v
                   Nothing -> bottom


(!!?) :: Ord k => SemiMeetMap k v -> k -> Maybe v
(!!?) (LM m) k = m M.!? k 

lmfromlist :: Ord k => [(k, v)] -> SemiMeetMap k v
lmfromlist kvs = LM $ M.fromList [(k, v) | (k, v) <- kvs]

lmempty :: SemiMeetMap k v 
lmempty = LM $ M.empty

lmtolist :: Ord k => SemiMeetMap k v -> [(k, v)]
lmtolist (LM m) = M.toList m

instance (Ord k, Show k, Show v) => Show (SemiMeetMap k v) where
  show (LM m) = show $ [(k, m M.! k) | k <- M.keys m]


instance (Ord k, Pretty k, Pretty v) => Pretty (SemiMeetMap k v) where
  pretty (LM m) =  pretty m -- vcat $ [pretty k <+> pretty "->" <+> pretty (m M.! k) | k <- M.keys m]

instance SemiMeet v => SemiMeet (SemiMeetMap k v) where
  bottom = LM M.empty
  meet _ _ = error "TODO: define meet"

-- Helper to repeat till fixpoint
-- ===============================


repeatTillFix :: (Eq a) =>  (a -> a) -> a -> [a]
repeatTillFix f a =
  let a' = f a in
  if a == a' then [a] else a:repeatTillFix f a'


-- repeat till fixpoint, or the max count
repeatTillFixDebug :: Eq a => Int -> (a -> a) -> a -> [a]
repeatTillFixDebug 0 f a = [a]
repeatTillFixDebug n f a = 
  let a' = f a in if a' == a then [a] else a': repeatTillFixDebug (n - 1) f a'

-- Program syntax
-- ==============

-- Identifiers
newtype Id = Id String deriving(Eq, Ord)
instance Show Id where
  show (Id s) = "id:" ++ s

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

data Expr = EInt !Int | EBool !Bool  | EBinop !Binop !Expr !Expr | EId Id
  deriving(Eq, Ord)

instance Show Expr where
    show (EInt i) = show i
    show (EBool b) = show b
    show (EId id) = show id
    show (EBinop  op e1 e2) = "(" ++ show op ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Pretty Expr where
  pretty (EInt i) = pretty i
  pretty (EBool b) = pretty b
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

data BBId = BBId String deriving(Eq, Ord, Show)
instance Pretty BBId where
  pretty (BBId id) = pretty id

-- Instructions
data Inst = Assign !Loc !Id !Expr  deriving(Eq, Ord, Show)
instance Pretty Inst where
  pretty (Assign pc id expr) =
    pretty pc <+> pretty id <+> equals <+> pretty expr

instance Located Inst where
  location (Assign loc _ _) = loc

-- Phi nodes
data Phi = Phi !Loc Id (BBId, Id) (BBId, Id) deriving(Eq, Ord, Show)

instance Located Phi where
  location (Phi loc _ _ _) = loc

instance Pretty Phi where
  pretty (Phi pc id l r) =
    pretty pc <+> pretty "phi" <+> 
      pretty id <+> equals <+> pretty l <+> pretty r

-- Terminator instruction
data Term = Br !Loc BBId 
          | BrCond !Loc Id BBId BBId 
          | Done !Loc deriving(Eq, Ord)

instance Located Term where
  location (Br loc _) = loc
  location (BrCond loc _ _ _) = loc
  location (Done loc) = loc

instance Pretty Term where
  pretty (Br pc bbid) = pretty pc <+> pretty "br" <+> pretty bbid
  pretty (BrCond pc cid bbidl bbidr) = 
    pretty pc <+> pretty "brcond" <+> 
      pretty cid <+> pretty bbidl <+> pretty bbidr
  pretty (Done loc) = pretty loc <+> pretty "done"

data BBTy = BBLoop deriving(Eq, Ord)

instance Pretty BBTy where
  pretty (BBLoop) = pretty "bbloop"

data BB = BB {
 bbid :: BBId,
 bbty :: Maybe BBTy,
 bbloc :: Loc,
 bbphis :: [Phi],
 bbinsts :: [Inst],
 bbterm :: Term 
}deriving(Eq, Ord)

instance Pretty BB where
  pretty (BB bbid bbty bbloc phis is term) = 
    pretty bbloc <+> pretty bbid <+> pretty bbty <> line <>
      indent 4 (vcat $ (map pretty phis) ++  (map pretty is) ++ [pretty term])

instance Located BB where
  location (BB _ _ loc _ _ _) = loc


bbModifyInsts :: ([Inst] -> [Inst]) -> BB -> BB
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


-- Program is a collection of basic blocks. First basic block is the
-- entry block (block that gets executed on startup
newtype Program = Program [BB] deriving(Eq)


programMaxLoc :: Program -> Loc
programMaxLoc (Program bbs) = 
  let locs = bbs >>= bbGetLocs 
   in maximum locs

instance Pretty Program where
  pretty (Program bbs) = vcat $ map pretty bbs

-- Statements of the language
-- data Stmt = Assign !Loc !Id !Expr
--             | If !Loc !Id !Stmt !Stmt !Loc -- branch value id, true branch, false branch
--             | While !Loc !Id !Stmt !Loc -- while cond stmt, pc of entry, pc of exit
--             | Seq !Stmt !Stmt
--             | Skip !Loc deriving(Eq)
-- 
-- -- Return the Loc of the first statement in the block
-- stmtLocStart :: Stmt -> Loc
-- stmtLocStart (Assign pc _ _)  = pc
-- stmtLocStart (If pc _ _ _ _) = pc
-- stmtLocStart (While pc _ _ _) = pc
-- stmtLocStart (Seq s1 _) = stmtLocStart s1
-- stmtLocStart (Skip pc) = pc
-- 
-- 
-- -- Return the Loc of the last statement in the block
-- stmtLocEnd :: Stmt -> Loc
-- stmtLocEnd (Assign pc _ _)  = pc
-- stmtLocEnd (If _ _ _ _ pc') = pc'
-- stmtLocEnd (While _ _ _ pc') = pc'
-- stmtLocEnd (Seq _ s2) = stmtLocEnd s2
-- stmtLocEnd (Skip pc) = pc
-- 
-- instance Show Stmt where
--   show (Assign pc id e) = show pc ++ ":" ++ "(= " ++  show id ++ " " ++ show e ++  ")"
--   show (If pc cond t e pc') = show pc ++ ":" ++ "(if " ++ show cond ++ " " ++ show t ++ " " ++ show e ++ ")" ++ show pc' ++ ":END IF"
--   show (While pc cond s pc') = show pc ++ ":" ++ "(while " ++ show cond ++ " " ++ show s ++ ")" ++ show pc' ++ ":END WHILE"
--   show (Seq s1 s2) =  show s1 ++ ";;" ++ show s2
--   show (Skip pc) = show pc ++ ":" ++ "done"
-- 
-- instance Pretty Stmt where
--   pretty s@(Assign pc id e) = pretty pc <+> (parens $ pretty "=" <+> pretty id <+> pretty e)
--   pretty s@(If pc cond t e pc') = 
--     pretty pc <+> 
--       (parens $ pretty "if" <+> 
--                 pretty cond <+> 
--                 indent 1 (line <> pretty t <> 
--                           line <> pretty e <>
--                           line <> pretty pc' <+> pretty "ENDIF"))
--   pretty (Seq s1 s2) =  pretty s1 <> line <> pretty s2
--   pretty (While pc cond s pc') = 
--     pretty pc <+> 
--       (parens $ 
--         pretty "(while" <+> 
--           pretty cond <+> 
--             indent 1 (line <> pretty s <> line <> pretty pc' <+> pretty "ENDWHILE"))
--   pretty (Skip pc) = pretty pc <+> pretty "Skip"

-- A Program is a top level statement
-- type Program = Stmt 




-- Language semantics
-- ==================


type BBId2Loc = M.Map BBId Loc

-- current basic block and location within the basic block being executed
data PC = PCEntry | PCNext BBId BBId | PCDone deriving(Eq, Ord)

-- Environments of the language
type Env = (M.Map Id Int)


-- Initial env
envBegin :: Env
envBegin = M.empty

-- Expression evaluation
exprEval :: Expr -> Env -> Int
exprEval (EInt i) _ =  i
exprEval (EBool b) _ =  if b then 1 else 0
exprEval (EId id) env = env M.! id
exprEval (EBinop op e1 e2) env = exprEval e1 env `opimpl` exprEval e2 env where
  opimpl = case op of
             Add -> (+)
             Lt -> (\a b -> if a < b then 1 else 0)

-- Execute a phi node
phiExec ::  BBId -- previous BB ID
        -> Phi  -- Phi node to execute
        -> Env -> Env
phiExec prevbbid p@(Phi _ id (bbidl, idl) (bbidr, idr)) env = 
  if prevbbid == bbidl 
     then M.insert id (env M.! idl) env
     else if prevbbid == bbidr 
     then M.insert id (env M.! idr) env
     else error $ "incorrect phi: " ++ show p



-- Execute an instruction
instExec :: Inst -> Env -> Env
instExec (Assign _ id e) env = M.insert id (exprEval e env) env

-- Execute a terminator instruction
termExec :: Term 
         -> BBId  -- ID of the current basic block
         -> Env  -- environment 
         -> PC
termExec (Br _ bbid') bbid env = PCNext bbid bbid'

termExec (BrCond _ condid bbidl bbidr) bbid env = 
  let bbid' =  (if env M.! condid == 1 then  bbidl else bbidr)
   in PCNext bbid bbid'

termExec (Done _) _ env = PCDone


-- Execute a basic block
bbExec :: BB  -- current basic block
       -> Maybe BBId  -- BB id of previous basic block
       -> Env -> (Env, PC)
bbExec (BB bbid _ _ phis insts term) Nothing env = 
  let env' = foldl (flip instExec) env insts
      pc' = termExec term bbid env'
   in (env', pc')

bbExec (BB bbid _ _ phis insts term) (Just prevbbid) env = 
  do
    let env' = foldl (flip (phiExec prevbbid)) env phis
    let env'' = foldl (flip instExec) env' insts
        pc' = termExec term bbid env'' 
     in (env'', pc')

-- Create a map, mapping basic block IDs to basic blocks
-- for the given program
programBBId2BB :: Program -> M.Map BBId BB
programBBId2BB (Program bbs) = 
  foldl (\m bb -> M.insert (bbid bb) bb m) M.empty bbs

programExec :: Program -> Env -> Env
programExec p@(Program bbs) env = 
  let bbid2bb :: M.Map BBId BB
      bbid2bb = programBBId2BB p

      go :: (Env, PC) -> Env
      go (env, PCEntry) = go $ bbExec (head bbs) Nothing env 
      go (env, (PCNext prevbbid curbbid)) = 
        go $ bbExec (bbid2bb M.! curbbid) (Just prevbbid) env
      go (env, PCDone) = env
  in go (env, PCEntry)

-- Denotational semantics
-- ========================

-- Example
-- =======


class ToExpr a where
  toexpr :: a -> Expr

instance ToExpr Id where
  toexpr a = EId a


instance ToExpr String where
  toexpr a = EId (Id a)

instance ToExpr Bool where
  toexpr True = EInt 1
  toexpr False = EInt 0

instance ToExpr Expr where
  toexpr = id

(+.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(+.) a b = EBinop Add (toexpr a) (toexpr b)


(<.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(<.) a b = EBinop Lt (toexpr a) (toexpr b)

-- Builder of program state
data ProgramBuilder = ProgramBuilder { 
  builderpc :: Loc, 
  curbbid :: Maybe BBId,
  bbid2bb :: OM.OrderedMap BBId BB
}


runProgramBuilder :: ST.State ProgramBuilder () -> Program
runProgramBuilder pbst = 
  let pbinit :: ProgramBuilder
      pbinit = ProgramBuilder (Loc (-1)) Nothing OM.empty

      pbout :: ProgramBuilder
      pbout = ST.execState pbst pbinit
   in Program $ map snd (OM.toList (bbid2bb pbout))


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
  let bbid = BBId name
  let bb = BB bbid ty loc [] [] (Done locret)
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


appendInst :: Inst -> ST.State ProgramBuilder ()
appendInst i = builderCurBBModify (bbModifyInsts (++ [i]))

appendPhi :: Phi -> ST.State ProgramBuilder ()
appendPhi ph = builderCurBBModify (bbModifyPhis (++ [ph]))

setTerm :: Term -> ST.State ProgramBuilder ()
setTerm term = builderCurBBModify (bbModifyTerm (const term))

assign :: String -> Expr -> ST.State ProgramBuilder ()
assign id e = do
  loc <- builderLocIncr
  appendInst (Assign loc (Id id) e)

done :: ST.State ProgramBuilder ()
done = do
  loc <- builderLocIncr
  setTerm (Done loc)


phi :: String -> (BBId, String) -> (BBId, String) -> ST.State ProgramBuilder ()
phi id (bbidl, idl) (bbidr, idr) = do
  loc <- builderLocIncr
  appendPhi (Phi loc (Id id) (bbidl, Id idl) (bbidr, Id idr))

condbr :: String -> BBId -> BBId -> ST.State ProgramBuilder ()
condbr id bbidt bbidf = do
  loc <- builderLocIncr
  setTerm (BrCond loc (Id id) bbidt bbidf)


br :: BBId -> ST.State ProgramBuilder ()
br bbid = do
  loc <- builderLocIncr
  setTerm (Br loc bbid)

pLoop :: Program
pLoop = runProgramBuilder $ do
  entry <- buildNewBB "entry" Nothing 
  loop <- buildNewBB "loop" (Just BBLoop)
  exit <- buildNewBB "exit" Nothing

  focusBB entry
  assign "x_entry" (EInt 1)
  br loop

  focusBB exit
  done

  focusBB loop
  phi "x_loop" (entry, "x_entry") (loop, "x_next")

  assign "x_loop_lt_5" ("x_loop" <. (EInt 5))
  assign "x_next" ("x_loop" +. (EInt 1))

  condbr "x_loop_lt_5" loop exit



-- data StmtBuilder = StmtBuilder { sbpc :: Loc }
-- 
-- sbLocIncr :: ST.State StmtBuilder Loc
-- sbLocIncr = do
--   pc <- ST.gets sbpc
--   ST.modify  (\s -> s { sbpc = (locincr (sbpc s)) })
--   return pc
-- 
--   
-- 
-- stmtBuild :: ST.State StmtBuilder Stmt -> Stmt
-- stmtBuild st = let begin = StmtBuilder (locincr pcinit) in 
--              ST.evalState st begin
-- 
-- stmtSequence :: [ST.State StmtBuilder Stmt] -> ST.State StmtBuilder Stmt
-- stmtSequence [x] = x
-- stmtSequence (x:xs) = do
--   x' <- x
--   xs' <- stmtSequence xs
--   return $ Seq x' xs'

-- assign :: ToExpr a => String -> a -> ST.State StmtBuilder Stmt
-- assign id a =
--   do
--     pc <- sbLocIncr
--     let s = Assign pc (Id id) (toexpr a)
--     return s
-- 
-- 
-- skip :: ST.State StmtBuilder Stmt
-- skip = do
--   pc <- sbLocIncr
--   let s = Skip pc
--   return s
-- 
-- 
-- while :: String -> ST.State StmtBuilder Stmt -> ST.State StmtBuilder Stmt
-- while idcond loopbuilder = do
--   pc <- sbLocIncr
--   loop <- loopbuilder
--   pc' <- sbLocIncr
-- 
--   let l = While pc (Id idcond) loop pc'
--   return l
-- 
-- if_ :: String -> ST.State StmtBuilder Stmt -> ST.State StmtBuilder Stmt -> ST.State StmtBuilder Stmt
-- if_ idcond thenbuilder elsebuilder = do
--   pc <- ST.gets sbpc
--   sbLocIncr
--   then_ <- thenbuilder
--   else_ <- elsebuilder
--   pc' <- sbLocIncr
--   return (If pc (Id idcond) then_ else_ pc')
-- 
-- 
--   
-- 
-- pIf :: (Stmt, OpaqueVals) 
-- pIf =
--   let if1_then = stmtSequence $ [
--         assign "y" (EInt 1)]
-- 
--       if1_else =  stmtSequence $ [
--         assign "y" (EInt 3) ]
--   
--   in (stmtBuild . stmtSequence $ [
--   skip,
--   assign "x" (EInt 5),
--   assign "x_lt_10" ("x" <. EInt 10),
--   if_ "x_lt_10" if1_then if1_else,
--   assign "z" ("y" +. EInt 1 )], OpaqueVals mempty)
-- 
-- pLoop :: (Stmt, OpaqueVals)
-- pLoop = (stmtBuild . stmtSequence $ [
--   assign "x" (EInt 1),
--   assign "x_lt_5" ("x" <. EInt 5),
--   while "x_lt_5" $ stmtSequence $ [
--       skip,
--       assign "x_next" ("x" +.  EInt 1),
--       assign "x_lt_5_next" ("x" <. EInt 5),
--       assign "x" "x_next",
--       assign "x_lt_5" "x_lt_5_next"
--   ],
--   assign "z" ("x" +. EInt (-5))],
--  OpaqueVals (M.fromList $ [(Loc 4, [Id "x"])]))
-- 
-- pTwoNestedLoop :: (Stmt, OpaqueVals)
-- pTwoNestedLoop = (stmtBuild . stmtSequence $ [
--   assign "x" (EInt 1),
--   assign "x_lt_5" ("x" <. EInt 5),
--   while "x_lt_5" $ stmtSequence $ [
--       skip,
--       assign "x_next" ("x" +.  EInt 1),
--       assign "x_lt_5_next" ("x" <. EInt 5),
-- 
--       assign "y" (EInt 2),
--       assign "y_lt_10" ("y" <. EInt 10),
--       while "y_lt_10" $ stmtSequence $ [
--         skip,
--         assign "y_plus_x" ("y" +. "x"),
--         assign "y_plus_x_next" ("y" +. "x_next"),
--         assign "y_next" ("y" +.  EInt 5),
--         assign "y" "y_next",
--         assign "y_lt_10_next" ("y" <. EInt 10),
--         assign "y_lt_10" "y_lt_10_next"
--     ],
--     assign "x" "x_next",
--     assign "x_lt_5" "x_lt_5_next",
--     assign "alpha" ("y" +. EInt (-12))
--   ],
--   assign "beta" ("x" +. EInt (-5))],
--  OpaqueVals (M.fromList $ [(Loc 4, [Id "x"]), (Loc 12, [Id "y"])]))
-- 
-- -- ========================
-- -- CHOOSE YOUR PROGRAM HERE
-- -- ========================
pcur :: Program
pcur = pLoop
-- 
-- curToOpaqify :: OpaqueVals
-- curToOpaqify = snd pLoop
-- 
-- -- Derived properties of the chosen program
-- -- ========================================
-- 
-- curCSemInt :: CSem (LiftedLattice Int)
-- curCSemInt = stmtCollectFix concreteCSem (Loc (-1)) pcur (initCollectingSem pcur)
-- 
-- 
-- curCSemSym :: CSem (LiftedLattice SymVal)
-- curCSemSym = stmtCollectFix (symbolCSem curToOpaqify) (Loc (-1)) pcur (initCollectingSem pcur)
-- 
-- curCSemIntSym :: CSem (LiftedLattice Int, LiftedLattice SymVal)
-- curCSemIntSym = stmtCollectFix (concreteSymbolicCSem curToOpaqify) (Loc (-1)) pcur (initCollectingSem pcur)
-- 
-- -- map identifiers to a function of loop iterations to values
-- curAbs :: Id2CollectedVal (LiftedLattice Int, LiftedLattice SymVal)
-- curAbs = alphacsem curCSemIntSym pcur
-- 
-- lookupAbsAtVals :: Id  --- value to lookup
--   -> [(Id, Int)] --- value of identifiers expected at the definition of value
--   -> (LiftedLattice Int, LiftedLattice SymVal) -- value of identifier discovered
-- lookupAbsAtVals needle idvals = 
--   let
--   -- Extract out the concrete int value
--   extractConcrete :: Maybe (LiftedLattice Int, LiftedLattice SymVal) -> Maybe Int
--   extractConcrete (Just (LL i, _)) = Just i
--   extractConcrete _ = Nothing
-- 
--   -- check if the pair of (Id, Int) is in env
--   envContains :: CSemEnv (LiftedLattice Int, LiftedLattice SymVal) -> (Id, Int) -> Bool
--   envContains env (id, i) = extractConcrete (env !!? id) == Just i
-- 
--   in
--   curAbs needle (\env -> all (envContains env) idvals)
-- 

example1 :: String
example1 = unlines
  [ "[n] -> { [i,j] -> [i2,j2] : i2 = i + 1 and j2 = j + 1 and "
  , "1 <= i and i < n and 1 <= j and j < n or "
  , "i2 = i + 1 and j2 = j - 1 and "
  , "1 <= i and i < n and 2 <= j and j <= n }"
  ]
testisl :: IO ()
testisl = do
  ctx <- ctxAlloc


  -- test 1
  m <- mapReadFromStr ctx example1
  (m, exact) <- mapPower m
  s <- mapToStr m
  print exact
  print s
  mapFree m



main :: IO ()
main = do
  -- putStrLn "***ISL test***"
  --   testisl

    putStrLn "***program***"
    putDocW 80 (pretty pcur)
    putStrLn ""
    
    putStrLn "***program output***"
    let outenv =  (programExec pcur) envBegin
    print outenv


    putStrLn "***collecting semantics (concrete x symbol):***"
    -- forM_  (S.toList curCSemIntSym) (\m -> (putDocW 80 . pretty $ m) >> putStrLn "---")

    putStrLn "***sampling program using the abstraction:***"

    -- let idsToLookup = ["x", "x_lt_5", "y", "z"]
    -- let idsToLookup = ["x_lt_5", "x_lt_5_next", "x", "x_next", "z"]
    -- forM_ idsToLookup 
    --   (\id -> (putDocW 80 $ 
    --             pretty id <+> 
    --             pretty "=" <+> 
    --             pretty (lookupAbsAtVals (Id id) [])) >> putStrLn "")

