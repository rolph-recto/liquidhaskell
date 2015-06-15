module FaultLocal (
  faultLocal
) where

import Data.List
import Data.HashSet as S hiding (map,foldr,filter)
import Data.HashMap.Strict as M hiding (map,foldr,filter)
import Control.Monad.State
import Control.Monad
import Text.Read hiding (get)
import System.IO

import Language.Fixpoint.Interface
import Language.Fixpoint.Types
import Language.Fixpoint.Config
import Language.Haskell.Liquid.Types (Cinfo(..))

-- FAULT LOCAL ALGO 1
isSafe :: Result a -> Bool
isSafe (Safe, _) = True
isSafe _  = False

-- higher order delta debugging algo
-- just needs a test function for it to work
deltaDebug :: (Config -> FInfo Cinfo -> b -> [c] -> IO Bool) -> Config -> FInfo Cinfo -> b -> [c] -> [c] -> IO [c]
deltaDebug testSet cfg finfo ddata set r = do
  let (s1, s2) = splitAt ((length set) `div` 2) set
  if length set == 1
    then return set
    else do
      test1 <- testSet cfg finfo ddata (s1 ++ r)
      if test1
        then deltaDebug testSet cfg finfo ddata s1 r
        else do
          test2 <- testSet cfg finfo ddata (s2 ++ r)
          if test2
            then deltaDebug testSet cfg finfo ddata s2 r
            else do
              d1 <- deltaDebug testSet cfg finfo ddata s1 (s2 ++ r)
              d2 <- deltaDebug testSet cfg finfo ddata s2 (s1 ++ r)
              return (d1 ++ d2)

testConstraints :: Config -> FInfo Cinfo -> () -> [(Integer, SubC Cinfo)] -> IO Bool
testConstraints cfg finfo _ cons  = do
  putStrLn "testing constraint set "
  print cons
  let finfo' = finfo { cm = M.fromList cons }
  res <- solve cfg finfo'
  return $ isSafe res

-- fault local algo 1: remove constraints
faultLocal1 :: Config -> FInfo Cinfo -> Handle -> IO ()
faultLocal1 cfg finfo h = do
  let cons = M.toList $ cm finfo
  sol <- deltaDebug testConstraints cfg finfo () cons []
  hPutStrLn h "Solution: "
  hPrint h $ map (ci_loc . sinfo . snd) sol


-- FAULT LOCAL ALGO 2
-- calculate the powerset of a set
powerset :: [a] -> [[a]]
powerset []     = [[]]
powerset (x:xs) = let ptail = powerset xs in ptail ++ map (x:) ptail

cartProduct :: [[a]] -> [[a]]
cartProduct [] = [[]]
cartProduct (x:xs) = x >>= (\e -> map (e:) (cartProduct xs))

data Polarity = LHS | RHS

makeBlankReft :: Polarity -> SortedReft -> SortedReft
makeBlankReft LHS (RR sort (Reft (sym, Refa pred))) = 
  RR sort (Reft (sym, Refa PFalse))
makeBlankReft RHS (RR sort (Reft (sym, Refa pred))) = 
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


data EraseItem =  EraseBind { subc :: Integer, bind :: BindId }
                | EraseLHS { subc :: Integer }
                | EraseRHS { subc :: Integer }
                deriving (Eq, Show)
          

-- create a list of possible bindings / refinements to erase
-- this only supports LHS and RHS refinements for now
-- since adding bindings would create combinatorial explosion
createEraseList :: FInfo Cinfo -> [[EraseItem]]
createEraseList finfo = 
  let subcs = M.toList $ cm finfo in 
  map (\(id,subc) -> [EraseLHS id, EraseRHS id]) subcs

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
applyEraseItem bindPairs (EraseBind subcID bind) = return ()
applyEraseItem bindPairs (EraseLHS subcID) = do
  eraseSubCReft subcID LHS
applyEraseItem bindPairs (EraseRHS subcID) = do
  eraseSubCReft subcID RHS
 
-- erase a list of refinements
applyEraseList :: [EraseItem] -> [(BindId, BindId)] -> State (FInfo Cinfo) ()
applyEraseList eraseList bindPairs = do
  finfo <- get
  forM_ eraseList (applyEraseItem bindPairs)

  
-- apply single candidate erasures of refinements
-- then try to solve new constraint set
tryErase :: Config -> FInfo Cinfo -> [(BindId, BindId)] -> [EraseItem] -> IO (Result Cinfo)
tryErase cfg finfo bindPairs eraseList = do
  putStrLn "Try erasing these refinements: "
  print eraseList
  let finfo' = execState (applyEraseList eraseList bindPairs) finfo
  -- print $ cm finfo'
  res <- solve cfg finfo'
  return res

testErase :: Config -> FInfo Cinfo -> [(BindId, BindId)] -> [EraseItem] -> IO Bool
testErase cfg finfo bindPairs eraseList = do
  res <- tryErase cfg finfo bindPairs eraseList
  return $ isSafe res

printEraseItem :: Handle -> FInfo Cinfo -> EraseItem -> IO ()
printEraseItem h finfo (EraseLHS id) = do
  case M.lookup id (cm finfo) of
    Just con -> do
      hPutStrLn h "eraseLHS"
      hPrint h $ ci_loc $ sinfo con
    Nothing -> return ()
printEraseItem h finfo (EraseRHS id) = do
  case M.lookup id (cm finfo) of
    Just con -> do
      hPutStrLn h "eraseRHS"
      hPrint h $ ci_loc $ sinfo con
    Nothing -> return ()

printEraseItem h finfo _ = return ()
  

-- fault local algo 2: erase refinements
-- use delta debugging algo
faultLocal2 :: Config -> FInfo Cinfo -> Handle -> IO ()
faultLocal2 cfg finfo h = do
  putStrLn "copying bindings"
  let (bindPairs, finfo') = runState copyBindings finfo
  putStrLn "creating eraselists"
  let eraseList = createEraseList finfo' >>= id
  sol <- deltaDebug testErase cfg finfo bindPairs eraseList []

  hPutStrLn h "Solution: "
  forM_ sol (printEraseItem h finfo)


-- FAULT LOCAL ALGO 3
removeErasePowersets :: [EraseItem] -> [[EraseItem]] -> [[EraseItem]]
removeErasePowersets e eraseList = 
  filter (\e' -> not $ all (\et -> et `elem` e') e) eraseList

-- apply all candidate erasures
tryAllErase :: Config -> FInfo Cinfo -> [(BindId, BindId)] -> [[EraseItem]] -> IO [([EraseItem], Result Cinfo)]
tryAllErase cfg finfo bindPairs [] = return []
tryAllErase cfg finfo bindPairs (e:ex) = do
  putStrLn "trying eraselist "
  print e
  res@(items, fres) <- tryErase cfg finfo bindPairs e
  if isSafe res
    then do 
      -- the supersets of the current erasure candidates
      -- are guaranteed to be safe also
      let ex' = removeErasePowersets e ex 
      tailres <- tryAllErase cfg finfo bindPairs ex'
      return $ (e,res):tailres
    else do
      tailres <- tryAllErase cfg finfo bindPairs ex
      return tailres
  
-- fault local algo 3: erase refinements
-- calculate powerset and cull away redundant solver calls
-- this takes up a lot of memory, hangs for even small programs
faultLocal3 :: Config -> FInfo Cinfo -> Handle -> IO ()
faultLocal3 cfg finfo h = do
  putStrLn  "copying bindings"
  let (bindPairs, finfo') = runState copyBindings finfo
  putStrLn  "creating eraselists"
  let eraseLists = powerset (createEraseList finfo') >>= cartProduct
  let eraseLists' = sortBy (\x y -> length x `compare` length y) eraseLists

  putStrLn  "trying eraselists"
  sols <- tryAllErase cfg finfo' bindPairs eraseLists'
  hPutStrLn h "number of eraselists: "
  hPrint h $ length eraseLists'
  hPutStrLn h "number of possible solutions: "
  hPrint h $ length sols
  hPutStrLn h "possible solutions:"
  sequence $ map (\sol -> hPutStrLn h $ show sol) sols
  return ()


-- FAULT LOCAL ALGO 4
getGamma :: SubC Cinfo -> HashSet BindId
getGamma = S.fromList . elemsIBindEnv . senv

getBindMap :: FInfo Cinfo -> BindMap (Symbol, SortedReft)
getBindMap finfo = case bs finfo of
  BE _ bmap -> bmap

eraseRefinement :: BindId -> BindMap (Symbol, SortedReft) -> BindMap (Symbol, SortedReft)
eraseRefinement id map =
  case M.lookup id map of
    Just (sym, RR sort (Reft (sym2, Refa pred))) -> 
      -- let newbind = (sym, RR sort (Reft (sym2, Refa $ PNot pred))) in
      let newbind = (sym, RR sort (Reft (sym2, Refa PFalse))) in
      -- let newbind = (sym, RR sort (Reft (sym2, Refa PTrue))) in
      M.insert id newbind map
    -- no refinement to erase, so just return the original map
    Nothing -> map

tryBinding :: Config -> FInfo Cinfo -> [BindId] -> IO (Result Cinfo)
tryBinding cfg finfo idlist = do
  let env = bs finfo
  let map = getBindMap finfo
  let map' = foldr eraseRefinement map idlist
  let finfo' = finfo { bs = env { beBinds = map' } }
  solve cfg finfo' 

tryBindings :: Config -> FInfo Cinfo -> [[BindId]] -> [BindId] -> IO [BindId]
tryBindings cfg finfo [] acc = return acc
tryBindings cfg finfo (bindids:bs) acc = do
  putStr "Trying bindings "
  print bindids
  let map = getBindMap finfo
  (r, sol) <- tryBinding cfg finfo bindids
  case r of 
    Safe -> do
      impbinds <- forM bindids (\bindid -> do
        let bindval = M.lookup bindid map
        case bindval of
          Just bind -> do
            return [bindid]
          Nothing ->
            return [])
      tryBindings cfg finfo bs ((impbinds >>= id) ++ acc)
    _ -> tryBindings cfg finfo bs acc

printBinding :: FInfo Cinfo -> BindId -> IO ()
printBinding finfo id = do
  case M.lookup id (bindInfo finfo) of
    Just (Ci loc _) -> print loc
    Nothing -> return()

-- fault local algo 4: erase refinements of bindings
faultLocal4 :: Config -> FInfo Cinfo -> Handle -> IO ()
faultLocal4 cfg finfo h = do
  -- gather bindings used in the constraints
  let gammas = foldr (\c acc -> (getGamma c):acc) [] (M.elems $ cm finfo)
  let bindings = S.toList $ S.unions gammas
  let trylist = map (\bind -> [bind]) bindings
  impbinds <- tryBindings cfg finfo trylist []
  hPutStrLn h "Number of bindings total: "
  hPrint h $ length bindings
  hPutStrLn h "Number of bindings implicated: "
  hPrint h $ length impbinds
  hPutStrLn h "Bindings implicated: "
  forM_ impbinds (printBinding finfo)

faultLocal :: Config -> FInfo Cinfo -> IO ()
faultLocal cfg finfo = do
  let flname = (srcFile cfg) ++ ".flout"
  -- let algos = [("Filter constraints (delta debugging)", faultLocal1), ("Erase constraint refinements (delta debugging)", faultLocal2), ("Erase constraint refinements (powerset)", faultLocal3), ("Erase binding refinements", faultLocal4)]
  let algos = [("Filter constraints (delta debugging)", faultLocal1), ("Erase constraint refinements (delta debugging)", faultLocal2), ("Erase binding refinements", faultLocal4)]
  withFile flname WriteMode (\file -> do
    forM_ algos (\(name,fl) -> do
      hPutStrLn file name
      fl cfg finfo file))

{-   
  ans <- getLine
  case readMaybe ans :: Maybe Int of
    Just n -> do
      if n >= 1 && n <= 4
        then do
          let fl = algos !! (n-1)
          fl cfg finfo
        else return ()
    Nothing -> return ()
-}
  
