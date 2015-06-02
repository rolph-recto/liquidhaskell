{-# LANGUAGE TupleSections  #-}

import           Data.Maybe
import           Data.Monoid      (mconcat, mempty)
import           System.Exit
import           Control.Applicative ((<$>))
import           Control.Monad
import           Control.DeepSeq
import           Text.PrettyPrint.HughesPJ
import           CoreSyn
import           Var
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           System.Console.CmdArgs.Default

import qualified Language.Fixpoint.Config as FC
import qualified Language.Haskell.Liquid.DiffCheck as DC
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Interface
import           Language.Fixpoint.Types (sinfo)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Errors
import           Language.Haskell.Liquid.CmdLine
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.TransformRec
import           Language.Haskell.Liquid.Annotate (mkOutput)
-- import           Language.Haskell.Liquid.FaultLocal

main :: IO b
main = do cfg0     <- getOpts
          res      <- mconcat <$> mapM (checkOne cfg0) (files cfg0)
          let ecode = resultExit $  {- traceShow "RESULT" $ -} o_result res
          -- putStrLn  $ "ExitCode: " ++ show ecode
          -- exitWith ecode
          case ecode of 
            ExitSuccess   -> exitWith ecode
            ExitFailure _ -> do
              putStrLn "Do you want to perform fault localization (yes/no)?"
              ans <- getLine
              if ans == "yes"
                then do
                  consFL <- checkOneFL cfg0 $ head $ files cfg0
                  putStrLn ("# of constraints implicated: " ++ (show $ length consFL))
                  forM_ consFL (\cons -> do
                    print $ ci_loc $ sinfo cons)
                  exitWith ecode
                else exitWith ecode

checkOneFL cfg0 t = do
  val <- getGhcInfo cfg0 t
  case val of
    Left _ -> return []
    Right info -> liquidOneFL t info

liquidOneFL target info = do
  let cfg   = config $ spec info 
  let cbs' = transformScope (cbs info)
  dc <- prune cfg cbs' target info
  let cgi   = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs'}
  -- cgi `deepseq` 0
  let cons = fixCs cgi
  consFL <- deltaDebug cfg target cgi info dc cons []
  return consFL

-- test() for delta debugging algorithm
-- intuitively, check if set of constraints cons induces
-- failure of the refinement
testDelta cfg target cgi info dc cons = do
  putStrLn $ "testing delta: " ++ (show $ length cons)
  let cgi' = cgi { fixCs = cons }
  out <- solveCs cfg target cgi' info dc
  let ecode = resultExit $ o_result out
  case ecode of 
    ExitSuccess -> return False
    ExitFailure _ -> return True

deltaDebug cfg target cgi info dc cons r = do
  let (c1, c2) = splitAt ((length cons) `div` 2) cons
  if length cons == 1
    then return cons
    else do
      test1 <- testDelta cfg target cgi info dc (c1 ++ r)
      if test1
        then deltaDebug cfg target cgi info dc c1 r
        else do
          test2 <- testDelta cfg target cgi info dc (c2 ++ r)
          if test2
            then deltaDebug cfg target cgi info dc c2 r
            else do
              d1 <- deltaDebug cfg target cgi info dc c1 (c2 ++ r)
              d2 <- deltaDebug cfg target cgi info dc c2 (c1 ++ r)
              return (d1 ++ d2)
    

checkOne :: Config -> FilePath -> IO (Output Doc)
checkOne cfg0 t = getGhcInfo cfg0 t >>= either errOut (liquidOne t)
  where
    errOut r    = exitWithResult cfg0 t $ mempty { o_result = r}

liquidOne :: FilePath -> GhcInfo -> IO (Output Doc)
liquidOne target info =
  do donePhase Loud "Extracted Core using GHC"
     let cfg   = config $ spec info
     whenLoud  $ do putStrLn "**** Config **************************************************"
                    print cfg
     whenLoud  $ do putStrLn $ showpp info
                    putStrLn "*************** Original CoreBinds ***************************"
                    putStrLn $ showpp (cbs info)
     let cbs' = transformScope (cbs info)
     whenLoud  $ do donePhase Loud "transformRecExpr"
                    putStrLn "*************** Transform Rec Expr CoreBinds *****************"
                    putStrLn $ showpp cbs'
                    putStrLn "*************** Slicing Out Unchanged CoreBinds *****************"
     dc <- prune cfg cbs' target info
     let cbs'' = maybe cbs' DC.newBinds dc
     let info' = maybe info (\z -> info {spec = DC.newSpec z}) dc
     let cgi   = {-# SCC "generateConstraints" #-} generateConstraints $! info' {cbs = cbs''}
     cgi `deepseq` donePhase Loud "generateConstraints"
     out      <- solveCs cfg target cgi info' dc
     donePhase Loud "solve"
     let out'  = mconcat [maybe mempty DC.oldOutput dc, out]
     DC.saveResult target out'
     exitWithResult cfg target out'

-- checkedNames ::  Maybe DC.DiffCheck -> Maybe [Name.Name]
checkedNames dc          = concatMap names . DC.newBinds <$> dc
   where
     names (NonRec v _ ) = [showpp $ shvar v]
     names (Rec xs)      = map (shvar . fst) xs
     shvar               = showpp . varName


-- prune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Maybe Diff)
prune cfg cbs target info
  | not (null vs) = return . Just $ DC.DC (DC.thin cbs vs) mempty sp
  | diffcheck cfg = DC.slice target cbs sp
  | otherwise     = return Nothing
  where
    vs            = tgtVars sp
    sp            = spec info

<<<<<<< HEAD
-- printConstraints :: [SubC] -> IO ()
-- printConstraints cons = forM_ cons (print . consWeight)

solveCs cfg target cgi info dc 
  = do
       let finfo = cgInfoFInfo info cgi
       (r, sol) <- solve fx target (hqFiles info) finfo
=======
solveCs cfg target cgi info dc
  = do finfo    <- cgInfoFInfo info cgi
       (r, sol) <- solve fx finfo
>>>>>>> 93075f43817e7d040b120142466af0e7b7e292a7
       let names = checkedNames dc
       let warns = logErrors cgi
       let annm  = annotMap cgi
       let res   = ferr sol r
       let out0  = mkOutput cfg res sol annm
       return    $ out0 { o_vars = names } { o_errors  = warns} { o_result = res }
    where
       fx        = def { FC.solver  = fromJust (smtsolver cfg)
                       , FC.real    = real   cfg
                       , FC.native  = native cfg
                       , FC.srcFile = target
                       }
       ferr s r  = fmap (tidyError s) $ result $ sinfo <$> r

-- filterConstraints filt finfo =
    -- finfo { cm = M.fromList $ filt $ M.toList $ cm finfo }


-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
