module FaultLocal (
  runFaultLocal,
  uniqueSrcSpans, generateFLAnnotation,
  flResultToJSON
) where

import qualified Data.List as L
import Data.HashSet as S hiding (map,foldr,filter)
import Data.HashMap.Strict as M hiding (map,foldr,filter)
import qualified Data.Vector as V
import Control.Monad.State
import Control.Monad
import Text.Read hiding (get)
import qualified Text.JSON as J
import System.IO
import System.Directory
import System.CPUTime (getCPUTime)
import SrcLoc
import Data.Text (Text, pack, unpack)
import Data.Time.Clock.POSIX (getPOSIXTime)

import Data.Graph as G
import Data.Tree as T

import Language.Fixpoint.Interface
import Language.Fixpoint.Types hiding (Status(..))
import Language.Fixpoint.Config
import Language.Haskell.Liquid.Types hiding (Result(..), Config)
import qualified Language.Haskell.Liquid.ACSS as A
import Language.Haskell.Liquid.Annotate (generateHtml)
import Language.Haskell.Liquid.GhcMisc (Loc(..), srcSpanStartLoc, srcSpanEndLoc)
import Language.Fixpoint.Partition


-- I don't want to add the tuple package as a dependency
-- so here are some alternatives ... 
fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

snd3 :: (a,b,c) -> b
snd3 (_,y,_) = y

thd3 :: (a,b,c) -> c
thd3 (_,_,z) = z

joinStrs :: String -> [String] -> String
joinStrs j l = foldr (\x acc -> j ++ x ++ acc) "" l

uniqueSrcSpan :: SrcSpan -> Maybe RealSrcSpan
uniqueSrcSpan (RealSrcSpan loc) = Just loc
uniqueSrcSpan (UnhelpfulSpan _) = Nothing

uniqueSrcSpans :: [SrcSpan] -> [RealSrcSpan]
uniqueSrcSpans locs = L.nub $ locs >>= realLocs
  where realLocs = maybe [] (\x -> [x]) . uniqueSrcSpan

-- FAULT LOCAL ALGO 1
isSafe :: FixResult (SubC Cinfo) -> Bool
isSafe Safe = True
isSafe _    = False

-- higher order delta debugging algo
-- just needs a test function for it to work
deltaDebug :: Eq c => (Config -> FInfo Cinfo -> b -> [c] -> IO Bool) -> Config -> FInfo Cinfo -> b -> [c] -> [c] -> IO [c]
deltaDebug test cfg finfo ddata set r = do
  if length set == 1
    then return set
    else do
      let (s1, s2) = splitAt ((length set) `div` 2) set
      test1 <- test cfg finfo ddata (s1 ++ r)
      if not test1
        then deltaDebug test cfg finfo ddata s1 r
        else do
          test2 <- test cfg finfo ddata (s2 ++ r)
          if not test2
            then deltaDebug test cfg finfo ddata s2 r
            else do
              d1 <- deltaDebug test cfg finfo ddata s1 (s2 ++ r)
              d2 <- deltaDebug test cfg finfo ddata s2 (s1 ++ r)
              return (d1 ++ d2)

-- split a list into lists of size n
splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery n xs = as : splitEvery n bs 
  where (as,bs) = splitAt n xs

-- split a list into n lists
splitInto :: Int -> [a] -> [[a]]
splitInto n a = splitEvery ((length a) `div` n) a

complement :: Eq a => [a] -> [a] -> [a]
complement a b = filter (\x -> not $ x `elem` b) a

-- 1-minimizing delta debugging algorithm
-- see ddmin in https://www.st.cs.uni-saarland.de/papers/tse2002/tse2002.pdf
deltaDebug2 :: Eq c => (Config -> FInfo Cinfo -> b -> [c] -> IO Bool) -> Config -> FInfo Cinfo -> b -> [c] -> Int -> IO [c]
deltaDebug2 test cfg finfo ddata set n = do
  if length set < 2
    then return set
    else do
      let subsets = splitInto n set
      -- test subsets
      res1 <- foldM testSubset Nothing subsets
      case res1 of
        -- test fails for some subset
        Just failset -> deltaDebug2 test cfg finfo ddata failset 2
        Nothing -> do
          -- test complements
          res2 <- foldM testSubset Nothing (map (complement set) subsets)
          case res2 of
            Just failset2 -> deltaDebug2 test cfg finfo ddata failset2 $ max (n-1) 2
            Nothing -> do
              if length set > n
                -- increase granularity
                then deltaDebug2 test cfg finfo ddata set $ min (length set) (2*n)
                -- nothing else to do; return set
                else return set
  where testSubset prev subset = do
          case prev of
            -- stop once we find a failing subset
            Just _ -> do
              return prev
            Nothing -> do
              res <- test cfg finfo ddata subset
              if not res
                then return (Just subset)
                else return Nothing

testConstraints :: Handle -> Config -> FInfo Cinfo -> () -> [Integer] -> IO Bool
testConstraints log cfg finfo _ consid = do
  hPutStrLn log "testing constraint set "
  hPrint log consid
  let cons = filter (flip elem consid . fst) $ M.toList $ cm finfo
  let finfo' = finfo { cm = M.fromList cons }
  Result res _ <- solve cfg finfo'
  if isSafe res
    then do
      hPutStrLn log "safe!"
      return True
    else do
      hPutStrLn log "not safe!"
      return False

-- fault local algo 1: remove constraints
faultLocal1 :: Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan], String)
faultLocal1 log cfg finfo failedCons graph = do
  let consid = map fst $ M.toList $ cm finfo
  sol <- deltaDebug (testConstraints log) cfg finfo () consid []
  hPutStrLn log "found solution: "
  hPrint log sol
  let solCons = filter (flip elem sol . fst) $ M.toList $ cm finfo
  return ((uniqueSrcSpans . map (ci_loc . sinfo . snd)) solCons, joinStrs " " $ map show sol)


----- FAULT LOCAL ALGO 2
-- calculate the powerset of a set
data Polarity = LHS | RHS

makeBlankReft :: Polarity -> SortedReft -> SortedReft
makeBlankReft LHS (RR sort (Reft (sym, Refa _))) = 
  RR sort (Reft (sym, Refa PFalse))
makeBlankReft RHS (RR sort (Reft (sym, Refa _))) = 
  RR sort (Reft (sym, Refa PTrue))

-- make a blank copy of a single binding
copyBinding :: (BindId, Symbol, SortedReft) -> State (FInfo Cinfo) (BindId, BindId)
copyBinding (id,sym,reft) = do  
  finfo <- get 
  let reft' = makeBlankReft LHS reft
  let (id', bs') = insertBindEnv sym reft' (bs finfo)
  put $ finfo { bs = bs' }
  return (id, id')
  
-- make "blank" copies of bindings
-- return id pairs of original bindings and blank ones
copyBindings :: State (FInfo Cinfo) [(BindId, BindId)]
copyBindings = do
  finfo <- get
  let bmap = bindEnvToList $ bs finfo
  forM bmap copyBinding


data EraseItem =  EraseBind Integer BindId
                | EraseLHS Integer
                | EraseRHS Integer
                deriving (Eq)

instance Show EraseItem where
  show (EraseBind id bind) = "B " ++ (show id) ++ " " ++ (show bind)
  show (EraseLHS id) = "L " ++ (show id)
  show (EraseRHS id) = "R " ++ (show id)
          

-- create a list of possible bindings / refinements to erase
-- this only supports LHS and RHS refinements for now
-- since adding bindings would create combinatorial explosion
createEraseList :: FInfo Cinfo -> [[EraseItem]]
createEraseList finfo = 
  let subcs = M.toList $ cm finfo in 
  map (\(id,_) -> [EraseLHS id, EraseRHS id]) subcs

-- erase the left/right hand refinement of a subtyping constraint
eraseSubCReft :: Integer -> Polarity -> State (FInfo Cinfo) ()
eraseSubCReft subcID pol = do
  finfo <- get
  let cmap = cm finfo
  case M.lookup subcID cmap of 
    Nothing -> return ()
    Just subc -> do
      let reft = slhs subc
      let subc' = newSubC subc reft pol
      let cmap' = M.insert subcID subc' cmap
      put $ finfo { cm = cmap' }
      return ()
  where newSubC subc reft LHS = subc { slhs = makeBlankReft LHS reft }
        newSubC subc reft RHS = subc { srhs = makeBlankReft RHS reft }

-- erase a single refinement
applyEraseItem :: [(BindId, BindId)] -> EraseItem -> State (FInfo Cinfo) ()
applyEraseItem _ (EraseBind _ _) = return ()
applyEraseItem _ (EraseLHS subcID) = do
  eraseSubCReft subcID LHS
applyEraseItem _ (EraseRHS subcID) = do
  eraseSubCReft subcID RHS
 
-- erase a list of refinements
applyEraseList :: [EraseItem] -> [(BindId, BindId)] -> State (FInfo Cinfo) ()
applyEraseList eraseList bindPairs = do
  forM_ eraseList (applyEraseItem bindPairs)
  
-- apply single candidate erasures of refinements
-- then try to solve new constraint set
tryErase :: Config -> FInfo Cinfo -> [(BindId, BindId)] -> [EraseItem] -> IO (Result Cinfo)
tryErase cfg finfo bindPairs eraseList = do
  let finfo' = execState (applyEraseList eraseList bindPairs) finfo
  res <- solve cfg finfo'
  return res

testErase :: Handle -> Config -> FInfo Cinfo -> [(BindId, BindId)] -> [EraseItem] -> IO Bool
testErase log cfg finfo bindPairs eraseList = do
  hPutStrLn log "testing erase items: "
  hPrint log eraseList
  Result res _ <- tryErase cfg finfo bindPairs eraseList
  if isSafe res
    then do
      hPutStrLn log "safe!"
      return True
    else do
      hPutStrLn log "not safe!"
      return False

eraseItemToSrcSpan :: FInfo Cinfo -> EraseItem -> [SrcSpan]
eraseItemToSrcSpan finfo (EraseLHS id) =
  case M.lookup id (cm finfo) of
    Just con -> [ci_loc $ sinfo con]
    Nothing -> []
eraseItemToSrcSpan finfo (EraseRHS id) =
  case M.lookup id (cm finfo) of
    Just con -> [ci_loc $ sinfo con]
    Nothing -> []
eraseItemToSrcSpan finfo (EraseBind _ bid) =
  case M.lookup bid (bindInfo finfo) of
    Just (Ci loc _) -> [loc]
    Nothing -> []

-- fault local algo 2: erase refinements
-- use delta debugging algo
faultLocal2 :: Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan],String)
faultLocal2 log cfg finfo failedCons graph = do
  let (bindPairs, finfo') = runState copyBindings finfo
  let eraseList = createEraseList finfo' >>= id
  sol <- deltaDebug (testErase log) cfg finfo bindPairs eraseList []
  hPutStrLn log "found solution: "
  hPrint log sol
  return $ (uniqueSrcSpans $ sol >>= eraseItemToSrcSpan finfo, joinStrs " " $ map show sol)

{-
powerset :: [a] -> [[a]]
powerset []     = [[]]
powerset (x:xs) = let ptail = powerset xs in ptail ++ map (x:) ptail

cartProduct :: [[a]] -> [[a]]
cartProduct [] = [[]]
cartProduct (x:xs) = x >>= (\e -> map (e:) (cartProduct xs))

-- FAULT LOCAL ALGO 3
removeErasePowersets :: [EraseItem] -> [[EraseItem]] -> [[EraseItem]]
removeErasePowersets e eraseList = 
  filter (\e' -> not $ all (\et -> et `elem` e') e) eraseList

-- apply all candidate erasures
tryAllErase :: Handle -> Config -> FInfo Cinfo -> [(BindId, BindId)] -> [[EraseItem]] -> IO [([EraseItem], Result Cinfo)]
tryAllErase log cfg finfo bindPairs [] = return []
tryAllErase log cfg finfo bindPairs (e:ex) = do
  hPutStrLn log "trying eraselist: "
  hPrint log e
  res@(items, fres) <- tryErase cfg finfo bindPairs e
  if isSafe res
    then do 
      -- the supersets of the current erasure candidates
      -- are guaranteed to be safe also
      let ex' = removeErasePowersets e ex 
      tailres <- tryAllErase log cfg finfo bindPairs ex'
      return $ (e,res):tailres
    else do
      tailres <- tryAllErase log cfg finfo bindPairs ex
      return tailres
  
-- fault local algo 3: erase refinements
-- calculate powerset and cull away redundant solver calls
-- this takes up a lot of memory, hangs for even small programs
faultLocal3 :: Handle -> Config -> FInfo Cinfo -> IO [RealSrcSpan]
faultLocal3 log cfg finfo = do
  let (bindPairs, finfo') = runState copyBindings finfo
  let eraseLists = powerset (createEraseList finfo') >>= cartProduct
  let eraseLists' = sortBy (\x y -> length x `compare` length y) eraseLists

  sols <- tryAllErase log cfg finfo' bindPairs eraseLists'
  hPutStrLn log "solution: "
  hPrint log $ map fst sols
  -- TODO: this is kind of broken, so don't return anything for now
  return []
-}


-- FAULT LOCAL ALGO 4
getGamma :: SubC Cinfo -> HashSet BindId
getGamma = S.fromList . elemsIBindEnv . senv

getBindMap :: FInfo Cinfo -> BindMap (Symbol, SortedReft)
getBindMap finfo = case bs finfo of
  BE _ bmap -> bmap

eraseRefinement :: BindId -> BindMap (Symbol, SortedReft) -> BindMap (Symbol, SortedReft)
eraseRefinement id map =
  case M.lookup id map of
    Just (sym, RR sort (Reft (sym2, Refa _))) -> 
      -- let newbind = (sym, RR sort (Reft (sym2, Refa $ PNot pred))) in
      let newbind = (sym, RR sort (Reft (sym2, Refa PFalse))) in
      -- let newbind = (sym, RR sort (Reft (sym2, Refa PTrue))) in
      M.insert id newbind map
    -- no refinement to erase, so just return the original map
    Nothing -> map

tryBinding :: Config -> FInfo Cinfo -> [BindId] -> IO (FixResult (SubC Cinfo))
tryBinding cfg finfo idlist = do
  let env = bs finfo
  let map = getBindMap finfo
  let map' = foldr eraseRefinement map idlist
  let finfo' = finfo { bs = env { beBinds = map' } }
  Result res _ <- solve cfg finfo' 
  return res

tryBindings :: Handle -> Config -> FInfo Cinfo -> [[BindId]] -> [BindId] -> IO [BindId]
tryBindings _ _ _ [] acc = return acc
tryBindings log cfg finfo (bindids:bs) acc = do
  hPutStrLn log "trying bindings: "
  hPrint log bindids
  let map = getBindMap finfo
  r <- tryBinding cfg finfo bindids
  case r of 
    Safe -> do
      hPutStrLn log "implicated!"
      impbinds <- forM bindids (\bindid -> do
        let bindval = M.lookup bindid map
        case bindval of
          Just _ -> do
            return [bindid]
          Nothing ->
            return [])
      tryBindings log cfg finfo bs ((impbinds >>= id) ++ acc)
    _ -> do
      hPutStrLn log "not implicated!"
      tryBindings log cfg finfo bs acc

bindingToSrcSpan :: FInfo Cinfo -> BindId -> [SrcSpan]
bindingToSrcSpan finfo id =
  case M.lookup id (bindInfo finfo) of 
    Just (Ci loc _) -> [loc]
    Nothing -> []

-- fault local algo 4: erase refinements of bindings
faultLocal4 :: Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan],String)
faultLocal4 log cfg finfo failedCons graph = do
  -- gather bindings used in the constraints
  let gammas = foldr (\c acc -> (getGamma c):acc) [] (M.elems $ cm finfo)
  let bindings = S.toList $ S.unions gammas
  let trylist = map (\bind -> [bind]) bindings
  impbinds <- tryBindings log cfg finfo trylist []
  hPutStrLn log "solution: "
  hPrint log impbinds
  return $ (uniqueSrcSpans $ impbinds >>= bindingToSrcSpan finfo, joinStrs " " $ map show impbinds)

-- FAULT LOCAL ALGO 5
-- constraint filtering on connected components
type ConsID = (Integer, SubC Cinfo)
type ConsVars = ([KVar], [Symbol])
type ConsGraph = [(Integer, Integer)]


-- collect kvars in a constraint
-- returns a tuple (left, right)
-- where left is the list of kvars on the LHS of a constraint
-- and right is the list of kvars on the RHS of a constraint
collectVars :: BindEnv -> ConsID -> (ConsVars, ConsVars)
collectVars env (_, con) = (left, right) 
  where bindPreds = map (reftPred . sr_reft . snd) $ envCs env $ senv con
        left = foldTup traversePred ((reftPred $ lhsCs con):bindPreds) ([],[])
        right = foldTup traversePred [reftPred $ rhsCs con] ([],[])
        foldTup f elems acc = foldr (foldTupF f) acc elems
        foldTupF f pred acc = let vars = f pred in ((fst vars) ++ (fst acc), (snd vars) ++ (snd acc))
        traversePred PTrue = ([],[])
        traversePred PFalse = ([], [])
        traversePred (PAnd preds) = foldTup traversePred preds ([],[])
        traversePred (POr preds) = foldTup traversePred preds ([],[])
        traversePred (PNot pred) = traversePred pred
        traversePred (PImp p q) = foldTup traversePred [p, q] ([],[])
        traversePred (PIff p q) = foldTup traversePred [p, q] ([],[])
        traversePred (PBexp e) = traverseExpr e
        traversePred (PAtom _ e1 e2) = foldTup traverseExpr [e1, e2] ([],[])
        traversePred (PKVar kv _) = ([kv], [])
        traversePred (PAll _ p) = traversePred p
        traversePred PTop = ([],[])
        traverseExpr (ESym _) = ([],[])
        traverseExpr (ECon _) = ([],[])
        traverseExpr (EVar v) = ([], [v])
        traverseExpr (ELit _ _) = ([], [])
        traverseExpr (ENeg e) = traverseExpr e
        traverseExpr (EApp _ exprs) = foldTup traverseExpr exprs ([],[])
        traverseExpr (EBin _ e1 e2) = foldTup traverseExpr [e1, e2] ([],[])
        traverseExpr (EIte pred e1 e2) = foldTup traverseExpr [e1,e2] (traversePred pred)
        traverseExpr (ECst e _) = traverseExpr e
        traverseExpr EBot = ([],[])

-- check if there is an edge between two constraints
consShareVars :: (ConsID, (ConsVars, ConsVars)) -> (ConsID, (ConsVars, ConsVars)) -> Bool
consShareVars (_,(_,(k1,_))) (_,((k2,_),_)) = any (\k -> k `elem` k2) k1

-- create constraint graph
makeConsGraph :: BindEnv -> [ConsID] -> ConsGraph
makeConsGraph _ []    = []
makeConsGraph env cons  = toConsEdge $ makeConsGraph_ consVars
  where toConsEdge            = map (\(c1,c2) -> (fst $ fst c1, fst $ fst c2))
        makeConsGraph_ []     = []
        makeConsGraph_ (x:xs) = (makeEdges x xs) ++ (makeConsGraph_ xs)
        consVars              = map (\c -> (c, collectVars env c)) cons
        makeEdges _ []        = []
        makeEdges e (e':es)   = let tedges = makeEdges e es in
                                if consShareVars e e'
                                  then (e,e'):tedges
                                  else
                                    if consShareVars e' e
                                      then (e',e):tedges
                                      else tedges

finfoToConsGraph :: FInfo Cinfo -> ConsGraph
finfoToConsGraph finfo = makeConsGraph (bs finfo) (M.toList $ cm finfo)

-- get list of transitively reachable nodes 
-- do this by dfs
consReachable :: ConsGraph -> Integer -> [Integer]
consReachable graph node = dfs graph [node] []
  where dfs _ [] visited     = visited
        dfs g (n:ns) visited = dfs g (neighbors g (n:visited) n ++ ns) (n:visited)
        neighbors g v n = unvisited v $ g >>= \(e1,e2) ->
          if e1 == n then [e2] else (if e2 == n then [e1] else [])
        unvisited v   = filter (not . (flip elem v))

-- calculate connected components of a graph
-- do this by running dfs on each node
-- and placing the node on the correct conn component
getConnComponents :: [ConsID] -> ConsGraph -> (ConsGraph, [[ConsID]])
-- getConnComponents cons g  = (g, connBindings ccs)
getConnComponents cons g  = (g, ccs)
  where ids               = map fst cons
        ccs               = map ccToConsID $ getCC ids []
        ccToConsID cs     = cs >>= consToConsID cons
        consToConsID [] _       = []
        consToConsID (x@(cid',_):cs) cid = if cid == cid'
          then [x]
          else consToConsID cs cid
        getCC []     ccs  = ccs
        getCC (x:xs) ccs  = getCC xs $ insertCC x ccs
        insertCC x []     = [consReachable g x]
        insertCC x (c:cs) = if shareCC x c
                              then if x `elem` c 
                                     then c:cs
                                     else (x:c):cs
                              else c:(insertCC x cs)
        shareCC x c          = any (flip elem $ c) $ consReachable g x

-- EXPERIMENTAL: connected CCs that share non-trivial bindings
-- non-trivial bindings are those that aren't in all constraints
connBindings []            = []
connBindings ccomps = newccs
  where newccs            = map (>>= id) $ getCC ccomps []
        getCC [] ccs      = ccs
        getCC (x:xs) ccs  = getCC xs $ insertCC x ccs
        insertCC x []     = [[x]]
        insertCC x (c:cs) = if shareBinds x c
                              then if inCC x c
                                     then c:cs
                                     else (x:c):cs
                              else c:(insertCC x cs)
        ccBinds c         = map (filter (flip elem nontrivialBinds) . elemsIBindEnv . senv . snd) c >>= id
        nontrivialBinds   = filter (\b -> not $ all (b `elem`) consBinds) allBinds
        allBinds          = L.nub $ consBinds >>= id

        consBinds         = map (elemsIBindEnv . senv . snd) cons
        cons              = ccomps >>= id
        shareBinds x y    = any (flip elem $ map ccBinds y >>= id) $ ccBinds x
        inCC x c          = any (== map fst x) $ map (map fst) c

{-
-- calculate graph and then connected component of KVGraph
partitionConstraints :: BindEnv -> [ConsID] -> (ConsGraph, [[ConsID]])
partitionConstraints env cons  = getConnComponents cons $ makeConsGraph env cons

partitionFInfo :: FInfo Cinfo -> (ConsGraph, [FInfo Cinfo])
partitionFInfo finfo =
  let (graph, ccs) = partitionConstraints (bs finfo) (M.toList $ cm finfo) in
  (graph, map (\cons -> finfo { cm = M.fromList cons }) ccs)
-}

makeKVGraph :: FInfo Cinfo -> KVGraph
makeKVGraph = kvGraph . kvEdges

isVertexCons :: CVertex -> Bool
isVertexCons (KVar _) = False
isVertexCons (Cstr _) = True

partitionFInfo :: FInfo Cinfo -> KVGraph -> [FInfo Cinfo]
partitionFInfo finfo graph =
  let part = decompose graph in
  let conspart = map (map consVertexId . filter isVertexCons) part in
  let finfopart = map (\consids -> finfo { cm = getCons consids }) conspart in
  finfopart
  where consVertexId (Cstr i) = i
        getCons consids = M.fromList $ filter (flip elem consids . fst) $ M.toList $ cm finfo

-- fault local algo 5: like algo 1, but partition constraint set
-- into equiv classes that share kvars and variables and run
-- delta debugging on those equiv classes separately
-- the solution is the union of the delta debug solutions
-- of every equiv class
faultLocal5 :: Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan],String)
faultLocal5 log cfg finfo failedCons graph = do
  -- let (graph,part) = partition' finfo
  let part= partitionFInfo finfo graph

  hPutStr log "Number of partitions:"
  hPrint log $ length part
  hPutStrLn log "KVGraph:"
  hPrint log graph
  
  results <- forM (zip [1..] part) $ \(i, finfoPart) -> do
    -- only run delta debugging on partitions that have
    -- unsatisfiable constraints
    hPutStrLn log $ "testing partition " ++ (show i)

    partSafe <- testConstraints log cfg finfoPart () $ map fst $ M.toList $ cm finfoPart
    if partSafe
      then do
        hPutStrLn log "connected component is safe. skipping "
        return ([]," ")
      else do
        hPutStrLn log "connected component is unsafe. running constraint filtering"
        faultLocal1 log cfg finfoPart failedCons graph

  let (locs, ids) = unzip results 
  let locs' = L.nub $ locs >>= id
  let ids' = concat ids
  return $ (locs', ids')

-- test a constraint set along with a failed constraint
-- this lets us find the cause of failure for the failed constrained
testConstraints' :: Handle -> Config -> FInfo Cinfo -> [Integer] -> [Integer] -> IO Bool
testConstraints' log cfg finfo fcons cons = do
  hPutStrLn log $ "testing constraint set for failed constraints " ++ (show fcons) ++ ":"
  hPrint log cons
  let conmap = M.toList $ cm finfo
  let compCons = filter (\c -> elem (fst c) cons) conmap
  let finfo' = finfo { cm = M.fromList compCons }
  Result res _ <- solve cfg finfo'
  if isSafe res
    then do
      hPutStrLn log "safe!"
      return True
    else do
      hPutStrLn log "not safe!"
      return False


-- FL ALGO 6

-- make graph symmetrically closed by adding
-- a transverse edge for every edge
-- this effectively makes an undirected edge to a directed edge
-- for dijkstra's algorithm
saturate :: KVGraph -> KVGraph
saturate g = map (\(v,v',dests) -> (v,v',L.nub dests)) $ foldr processVertex g g
  where processVertex (v,_,dests) acc = foldr (processEdge v) acc dests
        processEdge v dest acc = insertEdge acc (dest,v)
        insertEdge g' (src,dest) =
          if src `elem` map fst3 g'
            then foldr (\e@(v,_,dests) acc ->
                          if src == v
                            then (v,v,dest:dests):acc
                            else e:acc) [] g'
            else (src,src,[dest]):g'

-- interface
getConsOrder :: KVGraph -> CVertex-> [(CVertex,Int)]
getConsOrder g src = M.toList $ execState (getConsOrder_ g src toVisit) initState
  where initState = M.insert src 0 M.empty
        toVisit   = map fst3 g

-- this implements dijkstra's algorithm
-- instead of stopping when a destination node is reached,
-- this computes the shortest path from the source to every
-- node in the graph reachable from src
getConsOrder_ :: KVGraph -> CVertex -> [CVertex] -> State (M.HashMap CVertex Int) ()
getConsOrder_ g src []        = return ()
getConsOrder_ g src unvisited = do
  next <- getNextVertex
  case next of
    -- no reachable vertices left, even though there are still
    -- unvisited vertices. return the result
    Nothing -> do
      return ()
    -- process the next vertex by updating the rank of its neighbors
    Just (v,rank) -> do
      let neighbors = getNeighbors v
      updateRanks (rank+1) neighbors
      getConsOrder_ g src (v `L.delete` unvisited)
  where findMin (k,v) Nothing         = if v >= 0 then Just (k,v) else Nothing
        findMin (k,v) (Just (k',min)) =
          if v >= 0 && v < min  then Just (k,v) else Just (k',min)
        -- pick the vertices with the smallest nonnegative rank
        -- (nonnegative rank means that it is reachable from src)
        getNextVertex = do
          ranks <- get 
          let unvisitedRanks = map (\v -> (v, M.lookupDefault (-1) v ranks)) unvisited
          return $ foldr findMin Nothing unvisitedRanks
        -- get vertices adjacent from v
        getNeighbors v = case L.lookup v (map (\(v,_,d) -> (v,d)) g) of 
                          Just dests -> dests
                          Nothing -> []
        -- update rank of vertices
        -- only update is new rank is smaller than old
        updateRanks rank' vs = mapM_ (updateRank rank') vs
        updateRank rank' v = do
          ranks <- get
          let rank = M.lookupDefault (-1) v ranks
          if rank > rank' || rank < 0
            then put $ M.insert v rank' ranks
            else return ()

cvToId (Cstr id) = id
cvToId (KVar _)  = -1 --this is not supposed to be called
idToCv id = Cstr id

-- order solution constraints by distance to failed constraint
getRankedConstraints :: Bool -> Int -> Handle -> KVGraph -> [Integer] -> [Integer] -> IO [Integer]
getRankedConstraints order numSol log satGraph sol fcons = do
  if order
    then do
      let initRanks = foldr (\c acc -> M.insert c 0 acc) M.empty sol
      let accumRanks = flip execState initRanks (do 
          -- add up rankings for every failed constraint
          -- the constraints with the least accumulated rankings
          -- are the top ones
          forM_ fcons $ \fconId -> do
            let ranks = getConsOrder satGraph (idToCv fconId) 
            let ranks' = filter (isVertexCons . fst) ranks
            let ranks'' = filter (flip elem sol . cvToId . fst) ranks'
            let ranks''' = map (\(c,r) -> (cvToId c, r)) ranks''
            forM_ ranks''' $ \(c,rank) -> do
              accumRanks <- get
              let accumRank = M.lookupDefault 0 c accumRanks
              put $ M.insert c (accumRank+rank) accumRanks)

      let accumRanks' = M.toList accumRanks
      let ranksTotal = L.sortBy (\a b -> snd a `compare` snd b) accumRanks'

      -- take the rank of the nth constraint, where
      -- n = numSolConstraints. then take all constraints with
      -- rank less than or equal to it
      let cutoff = if numSol > length ranksTotal
                      then (-1)
                      else snd $ ranksTotal !! (numSol-1)
      let ranksCutoff = filter (\(_,r) -> cutoff < 0 || r <= cutoff) ranksTotal

      hPutStrLn log "Ordering for solution constraints: "
      hPrint log ranksTotal

      return $ map fst ranksCutoff

    else return sol


faultLocal6 :: Bool -> Int -> Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan],String)
faultLocal6 order numSol log cfg finfo failedCons graph = do
  {-
  let graph = finfoToConsGraph finfo
  let vertices = L.nub $ graph >>= (\(s,e) -> [s,e])
  let graph' = map (\v -> (v,v,map snd $ filter (\e -> fst e == v) graph)) vertices
  let (graph'', gmap) = G.graphFromEdges' graph'
  let ccomps = map (map (fst3 . gmap) . T.flatten) $ G.components graph''
  let ccomps' = filter (\ccomp -> any (flip elem ccomp) failedCons) ccomps
  -}

  let satGraph = saturate graph
  let (graph', gmap) = G.graphFromEdges' satGraph
  let ccomps = map (map cvToId . filter isVertexCons . map (fst3 . gmap) . T.flatten) $ G.components graph'
  -- let ccomps = map (map cvToId . map (fst3 . gmap) . T.flatten) $ G.components graph'
  -- let ccomps' = filter (\ccomp -> any (flip elem ccomp) failedCons) ccomps
  -- let ccompPairs = map (\con -> (con, head $ filter (elem con) ccomps')) failedCons
  let ccompPairs = map (\ccomp -> (ccomp, filter (flip elem ccomp) failedCons)) ccomps
  let ccompPairs' = filter (\(_,cons) -> length cons > 0) ccompPairs

  hPutStr log "Failed constraints:"
  hPrint log failedCons

  hPutStr log "Number of partitions:"
  hPrint log $ length ccomps
  hPutStr log "Number of partitions to check:"
  hPrint log $ length ccompPairs'

  hPutStrLn log "Saturated KVGraph:"
  hPrint log satGraph
  hPutStrLn log "weakly connected comps and failed constraints:"
  hPrint log ccompPairs

  -- there is a bug in Liquid Haskell where there are no failed constraints
  -- passed to the fault localization algo even though there are constraints
  -- that did fail (see KmpIO.hs). this makes FC trace check NO conn comps.
  -- as a fix, this falls back to regular filter constraints if there are
  -- not failed constraints found
  if length ccompPairs' > 0
    then do
      results <- forM (uncurry (zip3 [1..]) $ unzip ccompPairs') $ \(i, ccomp, fcons) -> do
        hPutStrLn log $ "localizing fault for constraints " ++ (show fcons)
        sol <- deltaDebug (testConstraints' log) cfg finfo fcons ccomp []
        sol' <- getRankedConstraints order numSol log satGraph sol fcons

        hPutStrLn log $ "found solution for constraints " ++ (show fcons) ++ ": "
        hPrint log sol'

        let solCons = filter (\c -> elem (fst c) sol') $ M.toList $ cm finfo
        let infoStr = "(" ++ (show fcons) ++ ", [" ++ (joinStrs " " $ map show sol') ++ "])"
        return ((uniqueSrcSpans . map (ci_loc . sinfo . snd)) solCons, infoStr)

      let (locs, ids) = unzip results 
      let locs' = L.nub $ locs >>= id
      let ids' = joinStrs " " ids
      return $ (locs', ids')

    else do
      hPutStrLn log "No failed constraints found. Falling back to filter constraints"
      faultLocal1 log cfg finfo failedCons graph


-- fault local algo 7: filterConstraints with ddmin
faultLocal7 :: Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan], String)
faultLocal7 log cfg finfo failedCons graph = do
  let consid = map fst $ M.toList $ cm finfo
  sol <- deltaDebug2 (testConstraints log) cfg finfo () consid 2
  hPutStrLn log "found solution: "
  hPrint log sol
  let solCons = filter (flip elem sol . fst) $ M.toList $ cm finfo
  return ((uniqueSrcSpans . map (ci_loc . sinfo . snd)) solCons, joinStrs " " $ map show sol)

faultLocal8 :: Bool -> Int -> Handle -> Config -> FInfo Cinfo -> [Integer] -> KVGraph -> IO ([RealSrcSpan],String)
faultLocal8 order numSol log cfg finfo failedCons graph = do
  {-
  let graph = finfoToConsGraph finfo
  let vertices = L.nub $ graph >>= (\(s,e) -> [s,e])
  let graph' = map (\v -> (v,v,map snd $ filter (\e -> fst e == v) graph)) vertices
  let (graph'', gmap) = G.graphFromEdges' graph'
  let ccomps = map (map (fst3 . gmap) . T.flatten) $ G.components graph''
  let ccomps' = filter (\ccomp -> any (flip elem ccomp) failedCons) ccomps
  -}

  let satGraph = saturate graph
  let (graph', gmap) = G.graphFromEdges' satGraph
  let ccomps = map (map cvToId . filter isVertexCons . map (fst3 . gmap) . T.flatten) $ G.components graph'
  -- let ccomps = map (map cvToId . map (fst3 . gmap) . T.flatten) $ G.components graph'
  -- let ccomps' = filter (\ccomp -> any (flip elem ccomp) failedCons) ccomps
  -- let ccompPairs = map (\con -> (con, head $ filter (elem con) ccomps')) failedCons
  let ccompPairs = map (\ccomp -> (ccomp, filter (flip elem ccomp) failedCons)) ccomps
  let ccompPairs' = filter (\(_,cons) -> length cons > 0) ccompPairs

  hPutStr log "Failed constraints:"
  hPrint log failedCons

  hPutStr log "Number of partitions:"
  hPrint log $ length ccomps
  hPutStr log "Number of partitions to check:"
  hPrint log $ length ccompPairs'

  hPutStrLn log "Saturated KVGraph:"
  hPrint log satGraph
  hPutStrLn log "weakly connected comps and failed constraints:"
  hPrint log ccompPairs

  -- there is a bug in Liquid Haskell where there are no failed constraints
  -- passed to the fault localization algo even though there are constraints
  -- that did fail (see KmpIO.hs). this makes FC trace check NO conn comps.
  -- as a fix, this falls back to regular filter constraints if there are
  -- not failed constraints found
  if length ccompPairs' > 0
    then do
      results <- forM (uncurry (zip3 [1..]) $ unzip ccompPairs') $ \(i, ccomp, fcons) -> do
        hPutStrLn log $ "localizing fault for constraints " ++ (show fcons)
        sol <- deltaDebug2 (testConstraints' log) cfg finfo fcons ccomp 2
        sol' <- getRankedConstraints order numSol log satGraph sol fcons

        hPutStrLn log $ "found solution for constraints " ++ (show fcons) ++ ": "
        hPrint log sol'

        let solCons = filter (\c -> elem (fst c) sol') $ M.toList $ cm finfo
        let infoStr = "(" ++ (show fcons) ++ ", [" ++ (joinStrs " " $ map show sol') ++ "])"
        return ((uniqueSrcSpans . map (ci_loc . sinfo . snd)) solCons, infoStr)

      let (locs, ids) = unzip results 
      let locs' = L.nub $ locs >>= id
      let ids' = joinStrs " " ids
      return $ (locs', ids')

    else do
      hPutStrLn log "No failed constraints found. Falling back to filter constraints"
      faultLocal7 log cfg finfo failedCons graph

realSrcSpanToTup :: RealSrcSpan -> (Int,Int,Int,Int)
realSrcSpanToTup loc = (sline,scol,eline,ecol)
  where sline = srcSpanStartLine loc
        scol  = srcSpanStartCol loc
        eline = srcSpanEndLine loc
        ecol  = srcSpanEndCol loc

instance J.JSON RealSrcSpan where
  showJSON loc  = let (sline,scol,eline,ecol) = realSrcSpanToTup loc in
    J.makeObj [("sline",J.showJSON sline)
              ,("scol",J.showJSON scol)
              ,("eline",J.showJSON eline)
              ,("ecol",J.showJSON ecol)]

  readJSON _ = J.Error "decoding RealSrcSpan not supported currently"

flResultToJSON :: (String, [RealSrcSpan], String, Double) -> J.JSValue
flResultToJSON (name,locs,info,time) = J.makeObj [("name",J.JSString $ J.toJSString name)
                                       ,("locs",J.showJSONs locs)
                                       ,("info",J.JSString $ J.toJSString info)
                                       ,("time",J.showJSON time)]

nullLocJSON = J.makeObj [("sline",J.showJSON (0 ::Int))
                        ,("scol",J.showJSON  (0 :: Int))
                        ,("eline",J.showJSON (0 :: Int))
                        ,("ecol",J.showJSON (0 :: Int))]

conToJSON :: (Integer, SubC Cinfo) -> J.JSValue
conToJSON (id, con) = J.makeObj [("id", J.showJSON id)
                       ,("LHS", J.JSString $ J.toJSString $ show $ sr_reft $ slhs con)
                       ,("RHS", J.JSString $ J.toJSString $ show $ sr_reft $ srhs con)
                       ,("loc", maybe nullLocJSON J.showJSON $ uniqueSrcSpan $ ci_loc $ sinfo con)]

{-
consGraphToJSON :: ConsGraph -> J.JSValue
consGraphToJSON graph = J.JSArray $ map edgeToJSON graph
  where edgeToJSON (s,e) = J.makeObj [("source",J.showJSON s),("dest",J.showJSON e)]
-}

kvGraphToJSON :: KVGraph -> J.JSValue
kvGraphToJSON graph = J.JSArray [ makeEdge src dest | (src, _, dests) <- graph, dest <- dests, src /= dest]
  where makeEdge s e = J.makeObj [("source",vertexJSON s), ("dest",vertexJSON e)]
        makeEdge s e = J.makeObj [("source",vertexJSON s), ("dest",vertexJSON e)]
        isKVar (KVar _) = True
        isKVar (Cstr _) = False
        vertexJSON (KVar (KV k)) = J.JSString $ J.toJSString $ show k
        vertexJSON (Cstr i) = J.showJSON i

generateFLAnnotation :: [RealSrcSpan] -> A.AnnMap
generateFLAnnotation locs = A.Ann { A.types = M.empty, A.errors = errlocs, A.status = A.Unsafe }
  where errlocs = map (\loc -> (srcSpanStartLoc loc, srcSpanEndLoc loc, "possible error location")) locs

liquidDir   = ".liquid/"
liquidflDir = ".liquidfl/"
fqExt       = ".fq"

runFaultLocal :: [Integer] -> Config -> FInfo Cinfo -> IO ()
runFaultLocal failedCons cfg finfo = do
  let sfile = srcFile cfg
  {-
  t <- round `liftM` getPOSIXTime
  let flDir = liquidflDir ++ (show t) ++ "/"
  -}
  let flDir = liquidflDir

  -- create flDir if it doesn't exist
  dirExist <- doesDirectoryExist flDir
  if dirExist
    then return ()
    else createDirectory flDir

  -- save extant fq file in flDir
  copyFile (liquidDir ++ sfile ++ fqExt) (flDir ++ sfile ++ fqExt)

  -- let algos = [("Filter constraints", faultLocal1), ("Erase constraint refinements", faultLocal2), ("Erase binding refinements", faultLocal4), ("Filter constraints in connected components", faultLocal5)]
  -- let algos = [("Filter constraints", faultLocal1),("Filter constraints in connected components", faultLocal5), ("Reduce search space", faultLocal6)]
  let algos = [("Filter constraints", faultLocal1),("Filter constraints with ddmin", faultLocal7), ("filterConstraintsWCC", faultLocal6 False 0),("filterConstraintsWCC with ddmin", faultLocal8 False 0)]

  -- output log of algorithms
  let graph = makeKVGraph finfo
  let logname = flDir ++ sfile ++ ".fllog"
  results <- withFile logname WriteMode $ \log -> do
    forM algos $ \(name, fl) -> do
      hPutStrLn log "####################"
      hPutStrLn log name
      hPutStrLn log "####################"
      start <- getCPUTime
      (locs, info) <- fl log cfg finfo failedCons graph
      end <- getCPUTime
      let diff = (fromIntegral (end - start)) / (10^12) :: Double
      return (locs, info, diff)

  -- output list of implicated source locations
  -- this is a JSON file
  let algoNames = map fst algos
  let algoLocs = map fst3 results
  let algoInfo = map snd3 results
  let algoTime = map thd3 results
  let algoResults = L.zip4 algoNames algoLocs algoInfo algoTime
  let jsonRes = J.JSArray $ map flResultToJSON algoResults
  let jsonCons = J.JSArray $ map conToJSON $ M.toList $ cm finfo
  let jsonGraph = kvGraphToJSON graph
  -- let jsonGraph = kvGraphToJSON $ makeKVGraph finfo
  let jsonObj = J.makeObj [("results", jsonRes), ("cons",jsonCons), ("graph", jsonGraph)]
  let flname = flDir ++ sfile ++ ".flout"
  withFile flname WriteMode $ \file -> do
    hPutStr file $ J.encode jsonObj
  
  -- output annotated html files
  let annotFiles = map (\(i, _) -> flDir ++ sfile ++ ".flannot" ++ (show i) ++ ".html") $ zip [1..] algos
  forM_ (zip annotFiles results) $ \(fname, (result,_,_)) -> do
    let annots = generateFLAnnotation result
    generateHtml sfile fname annots
  
