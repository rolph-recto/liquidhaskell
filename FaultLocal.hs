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

-- for shuffling
import System.Random
import Data.Array.IO

import Language.Fixpoint.Interface
import Language.Fixpoint.Types hiding (Status(..))
import Language.Fixpoint.Config
import Language.Haskell.Liquid.Types hiding (Result(..), Config)
import qualified Language.Haskell.Liquid.ACSS as A
import Language.Haskell.Liquid.Annotate (generateHtml)
import Language.Haskell.Liquid.GhcMisc (Loc(..), srcSpanStartLoc, srcSpanEndLoc)
import Language.Fixpoint.Partition

joinStrs :: String -> [String] -> String
joinStrs j l = foldr (\x acc -> acc ++ j ++ x) "" l

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
deltaDebug :: (Config -> FInfo Cinfo -> b -> [c] -> IO Bool) -> Config -> FInfo Cinfo -> b -> [c] -> [c] -> IO [c]
deltaDebug testSet cfg finfo ddata set r = do
  if length set == 1
    then return set
    else do
      let (s1, s2) = splitAt ((length set) `div` 2) set
      test1 <- testSet cfg finfo ddata (s1 ++ r)
      if not test1
        then deltaDebug testSet cfg finfo ddata s1 r
        else do
          test2 <- testSet cfg finfo ddata (s2 ++ r)
          if not test2
            then deltaDebug testSet cfg finfo ddata s2 r
            else do
              d1 <- deltaDebug testSet cfg finfo ddata s1 (s2 ++ r)
              d2 <- deltaDebug testSet cfg finfo ddata s2 (s1 ++ r)
              return (d1 ++ d2)

testConstraints :: Handle -> Config -> FInfo Cinfo -> () -> [(Integer, SubC Cinfo)] -> IO Bool
testConstraints log cfg finfo _ cons  = do
  hPutStrLn log "testing constraint set "
  hPrint log $ map fst cons
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
faultLocal1 :: Handle -> Config -> FInfo Cinfo -> IO ([RealSrcSpan], String)
faultLocal1 log cfg finfo = do
  let cons = M.toList $ cm finfo
  sol <- deltaDebug (testConstraints log) cfg finfo () cons []
  hPutStrLn log "found solution: "
  hPrint log $ map fst sol
  return ((uniqueSrcSpans . map (ci_loc . sinfo . snd)) sol, joinStrs " " $ map (show . fst) sol)


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
faultLocal2 :: Handle -> Config -> FInfo Cinfo -> IO ([RealSrcSpan],String)
faultLocal2 log cfg finfo = do
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
faultLocal4 :: Handle -> Config -> FInfo Cinfo -> IO ([RealSrcSpan],String)
faultLocal4 log cfg finfo = do
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

-- calculate graph and then connected component of KVGraph
partitionConstraints :: BindEnv -> [ConsID] -> (ConsGraph, [[ConsID]])
partitionConstraints env cons  = getConnComponents cons $ makeConsGraph env cons

partitionFInfo :: FInfo Cinfo -> (ConsGraph, [FInfo Cinfo])
partitionFInfo finfo =
  let (graph, ccs) = partitionConstraints (bs finfo) (M.toList $ cm finfo) in
  (graph, map (\cons -> finfo { cm = M.fromList cons }) ccs)

-- fault local algo 5: like algo 1, but partition constraint set
-- into equiv classes that share kvars and variables and run
-- delta debugging on those equiv classes separately
-- the solution is the union of the delta debug solutions
-- of every equiv class
faultLocal5 :: Handle -> Config -> FInfo Cinfo -> IO ([RealSrcSpan],String)
faultLocal5 log cfg finfo = do
  -- let (graph,part) = partition' finfo
  let (graph,part) = partitionFInfo finfo

  hPutStr log "Number of partitions:"
  hPrint log $ length part
  hPutStrLn log "KVGraph:"
  hPrint log graph
  
  results <- forM (zip [1..] part) $ \(i, finfoPart) -> do
    -- only run delta debugging on partitions that have
    -- unsatisfiable constraints
    hPutStrLn log $ "testing partition " ++ (show i)

    partSafe <- testConstraints log cfg finfoPart () $ M.toList $ cm finfoPart
    if partSafe
      then do
        hPutStrLn log "connected component is safe. skipping "
        return ([]," ")
      else do
        hPutStrLn log "connected component is unsafe. running constraint filtering"
        faultLocal1 log cfg finfoPart

  let (locs, ids) = unzip results 
  let locs' = L.nub $ locs >>= id
  let ids' = concat ids
  return $ (locs', ids')

{--
-- FL ALGO 6

-- Randomly shuffle a list in O(n)
-- from https://wiki.haskell.org/Random_shuffle
shuffle :: [a] -> IO [a]
shuffle xs = do
  ar <- newArray n xs
  forM [1..n] $ \i -> do
      j <- randomRIO (i,n)
      vi <- readArray ar i
      vj <- readArray ar j
      writeArray ar j vi
      return vj
  where
    n = length xs
    newArray :: Int -> [a] -> IO (IOArray Int a)
    newArray n xs =  newListArray (1,n) xs

-- fault local algo 6:
-- run constraint filtering several times while shuffling the
-- constraints, and then take the intersection of the results
-- this ensures that if there are multiply minimal failsets,
-- that the algo will find them; and the intersection of these failsets
-- most likely correspond to the bug location since they are the "real cause"
-- if there is only one minimal set, then it will be found several times and
-- its intersection is itself, so it will be returned as normal
faultLocal6 :: Handle -> Config -> FInfo Cinfo -> IO ([RealSrcSpan],String)
faultLocal6 log cfg finfo = do
  shuffles <- sequence $ take 5 $ repeat $ shuffle $ M.toList $ cm finfo

  -- return a list of con ids implicated for each shuffle
  conslists <- forM (zip [1..] shuffles) $ \(id, cons) -> do
    hPutStrLn log $ "running filt constraint for shuffle " ++ (show id)
    sol <- deltaDebug (testConstraints log) cfg finfo () cons []
    hPutStrLn log "found solution: "
    hPrint log $ map fst sol
    return $ map fst sol

  -- return the intersection of the con lists returned
  -- by definition, the intersection of all the con lists is a subset of 
  -- the first con list; we compute this subset
  let consids = filter (\con -> all (elem con) $ tail conslists) $ head conslists
  let cons = filter (\con -> fst con `elem` consids) (M.toList $ cm finfo)
  return ((uniqueSrcSpans . map (ci_loc . sinfo . snd)) cons, joinStrs " " $ map (show . fst) cons)
--}


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
                       ,("LHS", J.JSString $ J.toJSString $ show $ slhs con)
                       ,("RHS", J.JSString $ J.toJSString $ show $ srhs con)
                       ,("loc", maybe nullLocJSON J.showJSON $ uniqueSrcSpan $ ci_loc $ sinfo con)]

consGraphToJSON :: ConsGraph -> J.JSValue
consGraphToJSON graph = J.JSArray $ map edgeToJSON graph
  where edgeToJSON (s,e) = J.makeObj [("source",J.showJSON s),("dest",J.showJSON e)]

generateFLAnnotation :: [RealSrcSpan] -> A.AnnMap
generateFLAnnotation locs = A.Ann { A.types = M.empty, A.errors = errlocs, A.status = A.Unsafe }
  where errlocs = map (\loc -> (srcSpanStartLoc loc, srcSpanEndLoc loc, "possible error location")) locs

-- I don't want to add the tuple package as a dependency
-- so here are some alternatives ... 
fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

snd3 :: (a,b,c) -> b
snd3 (_,y,_) = y

thd3 :: (a,b,c) -> c
thd3 (_,_,z) = z

liquidDir   = ".liquid/"
liquidflDir = ".liquidfl/"
fqExt       = ".fq"

runFaultLocal :: Config -> FInfo Cinfo -> IO ()
runFaultLocal cfg finfo = do
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
  let algos = [("Filter constraints", faultLocal1),("Filter constraints in connected components", faultLocal5)]

  -- output log of algorithms
  let logname = flDir ++ sfile ++ ".fllog"
  results <- withFile logname WriteMode $ \log -> do
    forM algos $ \(name, fl) -> do
      hPutStrLn log "####################"
      hPutStrLn log name
      hPutStrLn log "####################"
      start <- getCPUTime
      (locs, info) <- fl log cfg finfo
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
  let jsonGraph = consGraphToJSON $ makeConsGraph (bs finfo) (M.toList $ cm finfo)
  let jsonObj = J.makeObj [("results", jsonRes), ("cons",jsonCons), ("graph", jsonGraph)]
  let flname = flDir ++ sfile ++ ".flout"
  withFile flname WriteMode $ \file -> do
    hPutStr file $ J.encode jsonObj
  
  -- output annotated html files
  let annotFiles = map (\(i, _) -> flDir ++ sfile ++ ".flannot" ++ (show i) ++ ".html") $ zip [1..] algos
  forM_ (zip annotFiles results) $ \(fname, (result,_,_)) -> do
    let annots = generateFLAnnotation result
    generateHtml sfile fname annots
  
