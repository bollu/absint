module Opsem where
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Internal
import Data.Text.Prettyprint.Doc.Util
import qualified Data.Map as M
import qualified Data.Set as S
import Util
import IR


-- current basic block and location within the basic block being executed
data PC = PCEntry | PCNext BBId BBId | PCDone deriving(Eq, Ord, Show)

instance Pretty PC where
  pretty (PCEntry) = pretty "pcentry"
  pretty (PCNext bbid bbid') =
    pretty "pcnext" <+> pretty bbid <+> pretty bbid'
  pretty (PCDone) = pretty "pcdone"

type VEnv v = M.Map Id v
-- trip count
type LEnv = M.Map BBId Int

data Env v = Env (VEnv v) LEnv PC deriving(Eq, Ord, Show)

instance Pretty v => Pretty (Env v) where
  pretty (Env venv lenv pc) =
    pretty "Env:" <> indent 1 (vcat [pretty pc, pretty "venv: " <+> pretty venv, pretty "lenv:" <+> pretty lenv ])


envBegin :: Env v
envBegin = Env mempty mempty PCEntry


envFromParamList :: [(Id, v)] -> Env v
envFromParamList id2v = Env (M.fromList id2v) mempty PCEntry

-- map variables to functions of loop trip counts
type TripCount = M.Map Id Int


-- collecting semantics in general. Map PC to a set of environments
type Collecting a = M.Map Loc (S.Set (Env a))

-- Setup the initial environment for the collecting semantics
collectingBegin :: Ord a => Program -> Env a -> Collecting a
collectingBegin p@(Program _ (entry:_)) initenv =
  let locs = map Loc [-1..(unLoc (programMaxLoc p))]
      allempty = M.fromList $ zip locs (repeat mempty)
   in M.insert (location entry) (S.singleton initenv) allempty

-- concrete environments
type ConcreteEnv = Env Int

-- The concrete domain is the collecting semantics of the concrete environment
type ConcreteDomain  = Collecting ConcreteEnv


-- type SemExpr = Expr -> Env a -> a
-- type SemPhi = Phi -> BBId -> Env a -> Env a
-- type SemInst = Assign -> Env a -> Env a
-- type SemTerm = Term -> BBId -> Env a -> PC
--
-- definitino of semantics
data Semantics a = Semantics {
 semExpr :: Expr -> VEnv a -> a,
 semPredicate :: a -> Maybe Bool
}

mkSemInst :: (Expr -> VEnv a -> a) -> Assign -> VEnv a -> VEnv a
mkSemInst sem (Assign _ id e) env  =
  M.insert id (sem e env) env

mkSemTerm :: Pretty a => (a -> Maybe Bool) -- concrete value to truth value
          -> Term
          -> BBId -- current bb id
          -> VEnv a
          -> PC
mkSemTerm _ (Br _ _ bbid') bbid env = PCNext bbid bbid'

mkSemTerm judgement (BrCond _ _ condid bbidl bbidr) bbid env =
  let (Just bcond) = judgement (env !!# condid)
      bbid' =  (if bcond then  bbidl else bbidr)
   in PCNext bbid bbid'
mkSemTerm _ (Done _ _) _ _ = PCDone

mkSemPhi :: Pretty a => Phi
         -> BBId  -- prevbbid
         -> VEnv a
         -> VEnv a
mkSemPhi  p@(Phi _ _ id (bbidl, idl) (bbidr, idr)) prevbbid env =
  if prevbbid == bbidl
     then M.insert id (env !!# idl) env
     else if prevbbid == bbidr
     then M.insert id (env !!# idr) env
     else error $ "incorrect phi: " ++ show p


envInsertOrUpdate :: Ord k => v -> (v -> v) -> k -> M.Map k v -> M.Map k v
envInsertOrUpdate v f k m =
  case m M.!? k  of
    Just v' -> M.insert k (f v') m
    Nothing -> M.insert k v m

-- update the lenv with respect to the bb type
bbLenvUpdate :: BBId -> Maybe BBTy -> LEnv -> LEnv
bbLenvUpdate _ Nothing lenv = lenv
bbLenvUpdate bbid (Just (BBLoop _)) lenv = envInsertOrUpdate 0 (+1) bbid lenv

-- Execute a basic block
bbExec :: Pretty a => Semantics a -> BB -> Env a -> Env a
bbExec sem (BB bbid bbty _ phis insts term) (Env venv lenv pcprev) =
  let lenvbb = bbLenvUpdate bbid bbty lenv
      venvphi = case pcprev of
                      PCNext prevbbid _ -> foldl (\venv phi -> mkSemPhi phi prevbbid venv) venv phis
                      PCEntry -> venv
                      PCDone -> error "canot have PC done and then execute a BB"
      venvinst = foldl (\venv inst -> mkSemInst (semExpr sem) inst venv) venvphi insts
      pc' = mkSemTerm (semPredicate sem) term bbid venvinst
   in Env venvinst lenvbb pc'




programExec :: Pretty a => Semantics a -> Program -> Env a -> Env a
programExec sem p@(Program _ bbs) env@(Env _ _ pc) =
  let bbid2bb :: M.Map BBId BB
      bbid2bb = progbbid2bb p
  in
    case pc of
      PCDone -> env
      PCEntry -> programExec sem p $ bbExec sem (head bbs) env
      PCNext _ curbbid -> programExec sem p $ bbExec sem (bbid2bb !!# curbbid) env


-- Concrete semantics
-- ===================

-- Expression evaluation
semExprConcrete :: Expr -> VEnv Int -> Int
semExprConcrete (EInt i) _ =  i
semExprConcrete (EId id) env = env !!# id
semExprConcrete (EBinop op id1 id2) env =
    (env !!# id1) `opimpl` (env !!# id2)  where
  opimpl = case op of
             Add -> (+)
             Lt -> (\a b -> if a < b then 1 else 0)

semPredicateConcrete :: Int -> Maybe Bool
semPredicateConcrete 0 = Just False
semPredicateConcrete 1 = Just True
semPredicateConcrete _ = Nothing

semConcrete :: Semantics Int
semConcrete = Semantics {
  semExpr = semExprConcrete,
  semPredicate = semPredicateConcrete
}
