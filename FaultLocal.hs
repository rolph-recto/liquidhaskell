module FaultLocal (
  runFaultLocal,
  uniqueSrcSpans, generateFLAnnotation,
  flResultToJSON
) where

import Data.List
import Data.HashSet as S hiding (map,foldr,filter)
import Data.HashMap.Strict as M hiding (map,foldr,filter)
import Control.Monad.State
import Control.Monad
import Text.Read hiding (get)
import qualified Text.JSON as J
import System.IO
import System.Directory
import SrcLoc
import Data.Text (Text, pack, unpack)
import Text.Karver
import System.CPUTime (getCPUTime)

import Language.Fixpoint.Interface
import Language.Fixpoint.Types hiding (Status(..))
import Language.Fixpoint.Config
import Language.Haskell.Liquid.Types hiding (Result(..), Config)
import qualified Language.Haskell.Liquid.ACSS as A
import Language.Haskell.Liquid.Annotate (generateHtml)
import Language.Haskell.Liquid.GhcMisc (Loc(..), srcSpanStartLoc, srcSpanEndLoc)
import Language.Fixpoint.Partition

uniqueSrcSpans :: [SrcSpan] -> [RealSrcSpan]
uniqueSrcSpans locs = nub $ locs >>= realLocs
  where realLocs (RealSrcSpan loc) = [loc]
        realLocs (UnhelpfulSpan _)   = []

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
faultLocal1 :: Handle -> Config -> FInfo Cinfo -> IO [RealSrcSpan]
faultLocal1 log cfg finfo = do
  let cons = M.toList $ cm finfo
  sol <- deltaDebug (testConstraints log) cfg finfo () cons []
  hPutStrLn log "found solution: "
  hPrint log $ map fst sol
  return $ (uniqueSrcSpans . map (ci_loc . sinfo . snd)) sol


-- FAULT LOCAL ALGO 2
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
faultLocal2 :: Handle -> Config -> FInfo Cinfo -> IO [RealSrcSpan]
faultLocal2 log cfg finfo = do
  let (bindPairs, finfo') = runState copyBindings finfo
  let eraseList = createEraseList finfo' >>= id
  sol <- deltaDebug (testErase log) cfg finfo bindPairs eraseList []
  hPutStrLn log "found solution: "
  hPrint log sol
  return $ uniqueSrcSpans $ sol >>= eraseItemToSrcSpan finfo

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
faultLocal4 :: Handle -> Config -> FInfo Cinfo -> IO [RealSrcSpan]
faultLocal4 log cfg finfo = do
  -- gather bindings used in the constraints
  let gammas = foldr (\c acc -> (getGamma c):acc) [] (M.elems $ cm finfo)
  let bindings = S.toList $ S.unions gammas
  let trylist = map (\bind -> [bind]) bindings
  impbinds <- tryBindings log cfg finfo trylist []
  hPutStrLn log "solution: "
  hPrint log impbinds
  return $ uniqueSrcSpans $ impbinds >>= bindingToSrcSpan finfo

{-

type ConsID = (Integer, SubC Cinfo)
type ConsVars = ([KVar], [Symbol])

collectVars :: ConsID -> ConsVars
collectVars (_, con) = foldTup traversePred [reftPred $ lhsCs con, reftPred $ rhsCs con]
  where foldTup f elems acc = foldr (foldTupF f) acc elems
        foldTupF f pred acc = let vars = f pred in ((fst vars) ++ (fst acc), (snd vars) ++ (snd acc)) ([], []) 
        traversePred PTrue = ([],[])
        traversePred PFalse = ([], [])
        traversePred (PAnd preds) = foldTup traversePred preds ([],[])
        traversePred (POr preds) = foldTup traversePred preds ([],[])
        traversePred (PNot pred) = traversePred pred
        traversePred (PImp p q) = foldTup traversePred [p, q] ([],[])
        traversePred (PIff p q) = foldTup traversePred [p, q] ([],[])
        traversePred (PBexp e) = traverseExpr e
        traversePred (Atom e1 e2) = foldTup traverseExpr [e1, e2] ([],[])
        traversePred (PKvar kv _) = ([kv], [])
        traversePred (PAll _ p) = traversePred p
        traversePred PTop = ([],[])
        traverseExpr (ESym s) = ([],[])
        traverseExpr (ECon c) = ([],[])
        traverseExpr (EVar v) = ([], [v])
        traverseExpr (ELit l s) = ([], [])
        traverseExpr (App s exprs) = foldTup traverseExpr exprs ([],[])
        traverseExpr (EBin op e1 e2) = foldTup traverseExpr [e1, e2] ([],[])
        traverseExpr (EIte pred e1 e2) = foldTup traverseExpr [e1,e2] (traversePred pred)
        traverseExpr (ECst e s) = traverseExpr e
        traverseExpr EBot = ([],[])

-- check if there is an edge between two constraints
consShareVars :: (ConsID, ConsVars) -> (ConsID, ConsVars) -> Bool
consShareVars (c1,(k1,v1)) (c2,(k2,v2)) =
  let shareKVars = any (\k -> k `elem` k2) k1 in
  let shareVars = any (\v -> `elem` v2) v1 in
  shareKVars || shareVars

-- create constraint graph
makeConsGraph :: [ConsID] -> [(ConsID, ConsID)]
makeConsGraph []    = []
makeConsGraph cons  = toConsEdge $ makeConsGraph_ $ map (\c -> (c, collectVars c)) cons
  where toConsEdge g = map (\(c1,c2) -> (fst c1, fst c2)) g
        makeConsGraph_ = (makeEdges x xs) ++ (makeConsGraph_ xs)
        makeEdges e []      = []
        makeEdges e (e':es) = let tedges = makeEdges e es in
                              if consShareVars e e' then (e,e'):tedges else tedges

-- calculate the connected components of the constraint graph
getConnComponents :: [(ConsID, ConsID)] -> [[ConsID]]
get

partitionConstraints :: [ConsID] -> [[ConsID]]
partitionConstraints cons = foldr
-}

-- fault local algo 5: like algo 1, but partition constraint set
-- into equiv classes that share kvars and variables and run
-- delta debugging on those equiv classes separately
-- the solution is the union of the delta debug solutions
-- of every equiv class
faultLocal5 :: Handle -> Config -> FInfo Cinfo -> IO [RealSrcSpan]
faultLocal5 log cfg finfo = do
  let (graph,part) = partition' finfo

  hPutStr log "Number of partitions:"
  hPrint log $ length part
  hPutStrLn log "KVGraph:"
  hPrint log graph
  
  results <- forM part $ \finfoPart -> faultLocal1 log cfg finfoPart
  return $ nub $ results >>= id

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

flResultToJSON :: (String, [RealSrcSpan], Double) -> J.JSValue
flResultToJSON (name,locs,time) = J.makeObj [("name",J.JSString $ J.toJSString name)
                                       ,("locs",J.showJSONs locs)
                                       ,("time",J.showJSON time)]

generateFLAnnotation :: [RealSrcSpan] -> A.AnnMap
generateFLAnnotation locs = A.Ann { A.types = M.empty, A.errors = errlocs, A.status = A.Unsafe }
  where errlocs = map (\loc -> (srcSpanStartLoc loc, srcSpanEndLoc loc, "possible error location")) locs

flDir = ".liquidfl/"
tmpCompareFile = "/.cabal/template.flcompare.html"

runFaultLocal :: Config -> FInfo Cinfo -> IO ()
runFaultLocal cfg finfo = do
  dirExist <- doesDirectoryExist flDir
  if dirExist
    then return ()
    else createDirectory flDir

  let algos = [("Filter constraints", faultLocal1), ("Erase constraint refinements", faultLocal2), ("Erase binding refinements", faultLocal4), ("Filter constraints in connected components", faultLocal5)]
  -- let algos = [("Filter constraints", faultLocal1), ("Erase constraint refinements", faultLocal2), ("Erase binding refinements", faultLocal4)]

  -- output log of algorithms
  let logname = flDir ++ (srcFile cfg) ++ ".fllog"
  results <- withFile logname WriteMode $ \log -> do
    forM algos $ \(name, fl) -> do
      hPutStrLn log "####################"
      hPutStrLn log name
      hPutStrLn log "####################"
      start <- getCPUTime
      locs <- fl log cfg finfo
      end <- getCPUTime
      let diff = (fromIntegral (end - start)) / (10^12) :: Double
      return (locs, diff)

  -- output list of implicated source locations
  -- this is a JSON file

  let flname = flDir ++ (srcFile cfg) ++ ".flout"
  withFile flname WriteMode $ \file -> do
    let algoResults = (uncurry $ zip3 $ map fst algos) (unzip results)
    let jsonRes = J.JSArray $ map flResultToJSON algoResults
    hPutStr file $ J.encode jsonRes
    {-
    forM_ algoResults $ \(name,result) -> do
      hPutStrLn file "####################"
      hPutStrLn file name
      forM result ((hPutStrLn file). show)
    -}
  
  -- output annotated html files
  let annotFiles = map (\(i, _) -> flDir ++ (srcFile cfg) ++ ".flannot" ++ (show i) ++ ".html") $ zip [1..] algos
  forM_ (zip annotFiles results) $ \(fname, (result,_)) -> do
    let annots = generateFLAnnotation result
    generateHtml (srcFile cfg) fname annots
  
  -- output html file that compares annotated html files
  let cmpflname = flDir ++ (srcFile cfg) ++ ".flcompare.html"
  homeDir <- getHomeDirectory
  tplStr <- readFile (homeDir ++ tmpCompareFile)
  let litSrcName = Literal $ pack $ srcFile cfg
  let htmlStr = renderTemplate (M.insert (pack "filename") litSrcName M.empty) (pack tplStr)
  writeFile cmpflname (unpack htmlStr)
  
