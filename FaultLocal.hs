module FaultLocal (
  faultLocal
) where

import Data.List
import Data.HashSet as S hiding (map,foldr,filter)
import Data.HashMap.Strict as M hiding (map,foldr,filter)
import Control.Monad.State
import Control.Monad
import Text.Read hiding (get)

import Language.Fixpoint.Interface
import Language.Fixpoint.Types
import Language.Fixpoint.Config

-- FAULT LOCAL ALGO 1
isSafe :: Result a -> Bool
isSafe (Safe, _) = True
isSafe _  = False

-- higher order delta debugging algo
-- just needs a test function for it to work
deltaDebug :: (Config -> FInfo a -> b -> [c] -> IO Bool) -> Config -> FInfo a -> b -> [c] -> [c] -> IO [c]
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

testConstraints :: Config -> FInfo a -> () -> [(Integer, SubC a)] -> IO Bool
testConstraints cfg finfo _ cons  = do
  putStrLn "testing constraint set "
  print cons
  let finfo' = finfo { cm = M.fromList cons }
  res <- solve cfg finfo'
  return $ isSafe res

-- fault local algo 1: remove constraints
faultLocal1 :: Config -> FInfo a -> IO ()
faultLocal1 cfg finfo = do
  let cons = M.toList $ cm finfo
  sol <- deltaDebug testConstraints cfg finfo () cons []
  putStrLn "Solution: "
  print sol


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
copyBinding :: (BindId, Symbol, SortedReft) -> State (FInfo a) (BindId, BindId)
copyBinding (id,sym,reft) = do  
  finfo <- get 
  let reft' = makeBlankReft LHS reft
  let (id', bs') = insertBindEnv sym reft' (bs finfo)
  put $ finfo { bs = bs' }
  return (id, id')
  
-- make "blank" copies of bindings
-- return id pairs of original bindings and blank ones
copyBindings :: State (FInfo a) [(BindId, BindId)]
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
createEraseList :: FInfo a -> [[EraseItem]]
createEraseList finfo = 
  let subcs = M.toList $ cm finfo in 
  map (\(id,subc) -> [EraseLHS id, EraseRHS id]) subcs

-- erase the left/right hand refinement of a subtyping constraint
eraseSubCReft :: Integer -> Polarity -> State (FInfo a) ()
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
applyEraseItem :: [(BindId, BindId)] -> EraseItem -> State (FInfo a) ()
applyEraseItem bindPairs (EraseBind subcID bind) = return ()
applyEraseItem bindPairs (EraseLHS subcID) = do
  eraseSubCReft subcID LHS
applyEraseItem bindPairs (EraseRHS subcID) = do
  eraseSubCReft subcID RHS
 
-- erase a list of refinements
applyEraseList :: [EraseItem] -> [(BindId, BindId)] -> State (FInfo a) ()
applyEraseList eraseList bindPairs = do
  finfo <- get
  forM_ eraseList (applyEraseItem bindPairs)

  
-- apply single candidate erasures of refinements
-- then try to solve new constraint set
tryErase :: Config -> FInfo a -> [(BindId, BindId)] -> [EraseItem] -> IO (Result a)
tryErase cfg finfo bindPairs eraseList = do
  putStrLn "Try erasing these refinements: "
  -- print eraseList
  let finfo' = execState (applyEraseList eraseList bindPairs) finfo
  -- print $ cm finfo'
  res <- solve cfg finfo'
  return res

testErase :: Config -> FInfo a -> [(BindId, BindId)] -> [EraseItem] -> IO Bool
testErase cfg finfo bindPairs eraseList = do
  res <- tryErase cfg finfo bindPairs eraseList
  return $ isSafe res

printEraseItem :: FInfo a -> EraseItem -> IO ()
printEraseItem finfo (EraseLHS id) = do
  putStrLn "eraseLHS"
  print $ M.lookup id (cm finfo)
printEraseItem finfo (EraseRHS id) = do
  putStrLn "eraseRHS"
  print $ M.lookup id (cm finfo)
printEraseItem finfo _ = return ()
  

-- fault local algo 2: erase refinements
-- use delta debugging algo
faultLocal2 :: Config -> FInfo a -> IO ()
faultLocal2 cfg finfo = do
  putStrLn "copying bindings"
  let (bindPairs, finfo') = runState copyBindings finfo
  putStrLn "creating eraselists"
  let eraseList = createEraseList finfo' >>= id
  sol <- deltaDebug testErase cfg finfo bindPairs eraseList []

  putStrLn "Solution: "
  forM_ sol (printEraseItem finfo)


-- FAULT LOCAL ALGO 3
removeErasePowersets :: [EraseItem] -> [[EraseItem]] -> [[EraseItem]]
removeErasePowersets e eraseList = 
  filter (\e' -> not $ all (\et -> et `elem` e') e) eraseList

-- apply all candidate erasures
tryAllErase :: Config -> FInfo a -> [(BindId, BindId)] -> [[EraseItem]] -> IO [([EraseItem], Result a)]
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
faultLocal3 :: Config -> FInfo a -> IO ()
faultLocal3 cfg finfo = do
  putStrLn "copying bindings"
  let (bindPairs, finfo') = runState copyBindings finfo
  putStrLn "creating eraselists"
  let eraseLists = powerset (createEraseList finfo') >>= cartProduct
  let eraseLists' = sortBy (\x y -> length x `compare` length y) eraseLists

  putStrLn "trying eraselists"
  sols <- tryAllErase cfg finfo' bindPairs eraseLists'
  putStrLn "number of eraselists: "
  print $ length eraseLists'
  putStrLn "number of possible solutions: "
  print $ length sols
  putStrLn "possible solutions:"
  sequence $ map (\sol -> putStrLn $ show sol) sols
  return ()


-- FAULT LOCAL ALGO 4
getGamma :: SubC a -> HashSet BindId
getGamma = S.fromList . elemsIBindEnv . senv

getBindMap :: FInfo a -> BindMap (Symbol, SortedReft)
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

tryBinding :: Config -> FInfo a -> [BindId] -> IO (Result a)
tryBinding cfg finfo idlist = do
  let env = bs finfo
  let map = getBindMap finfo
  let map' = foldr eraseRefinement map idlist
  let finfo' = finfo { bs = env { beBinds = map' } }
  solve cfg finfo' 

tryBindings :: Config -> FInfo a -> [[BindId]] -> [BindId] -> IO [BindId]
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


-- fault local algo 4: erase refinements of bindings
faultLocal4 :: Config -> FInfo a -> IO ()
faultLocal4 cfg finfo = do
  -- gather bindings used in the constraints
  let gammas = foldr (\c acc -> (getGamma c):acc) [] (M.elems $ cm finfo)
  let bindings = S.toList $ S.unions gammas
  let trylist = map (\bind -> [bind]) bindings
  impbinds <- tryBindings cfg finfo trylist []
  putStrLn "Number of bindings total: "
  print $ length bindings
  putStrLn "Number of bindings implicated: "
  print $ length impbinds
  putStrLn "Bindings implicated: "
  sequence $ map (\b -> putStrLn $ show $ lookupBindEnv b (bs finfo)) impbinds
  return ()

faultLocal :: Config -> FInfo a -> IO ()
faultLocal cfg finfo = do
  let algos = [faultLocal1, faultLocal2, faultLocal3, faultLocal4]
  putStrLn "1. Filter constraints (delta debugging)"
  putStrLn "2. Erase constraint refinements (delta debugging)"
  putStrLn "3. Erase constraint refinements (powerset)"
  putStrLn "4. Erase binding refinements"
  putStrLn "Which algorithm to use? "
  ans <- getLine
  case readMaybe ans :: Maybe Int of
    Just n -> do
      if n >= 1 && n <= 4
        then do
          let fl = algos !! (n-1)
          fl cfg finfo
        else return ()
    Nothing -> return ()


