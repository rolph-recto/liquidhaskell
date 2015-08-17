{-# LANGUAGE TupleSections  #-}
{-# LANGUAGE CPP #-}

{-@ LIQUID "--cabaldir" @-}
{-@ LIQUID "--diff"     @-}

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid      (mconcat, mempty)
import           Control.Applicative ((<$>))
#endif

import           Data.Maybe
import           System.Exit
import           Control.Monad
import           Control.DeepSeq
import           Text.PrettyPrint.HughesPJ
import           CoreSyn
import           Var
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           System.Console.CmdArgs.Default
import           System.IO
import           System.Directory

import qualified Language.Fixpoint.Config as FC
import qualified Language.Haskell.Liquid.DiffCheck as DC
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Interface
import           Language.Fixpoint.Types (SubC(..), sinfo, Result(..), FixResult(..))
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Errors
import           Language.Haskell.Liquid.CmdLine
import           Language.Haskell.Liquid.GhcInterface
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.TransformRec
import           Language.Haskell.Liquid.Annotate (mkOutput, generateHtml)
import qualified Language.Haskell.Liquid.ACSS as A
import           Language.Haskell.Liquid.GhcMisc (Loc(..), srcSpanStartLoc, srcSpanEndLoc)
import           Data.HashMap.Strict as M hiding (map,foldr,filter,null)
import           Data.List
import           SrcLoc
-- import           Language.Haskell.Liquid.FaultLocal
import           FaultLocal
import           System.Environment (getArgs)
import qualified Text.JSON as J

main :: IO b
main = do cfg0     <- getOpts
          (failedCons, res) <- mconcat <$> mapM (checkOne cfg0) (files cfg0)
          let ecode = resultExit $  {- traceShow "RESULT" $ -} o_result res
          -- putStrLn  $ "ExitCode: " ++ show ecode
          -- exitWith ecode
          case ecode of 
            ExitSuccess   -> exitWith ecode
            ExitFailure _ -> do
              if faultLocal cfg0
                then do
                  checkOneFL (runFaultLocal failedCons) cfg0 $ head $ files cfg0
                  exitWith ecode
                  {--
                  consFL <- checkOneFL cfg0 $ head $ files cfg0
                  putStrLn ("# of constraints implicated: " ++ (show $ length consFL))
                  forM_ consFL (\cons -> do
                    print $ ci_loc $ sinfo cons)
                  exitWith ecode
                  --}
                else
                  if flrepl cfg0
                    then do
                      checkOneFL flRepl cfg0 $ head $ files cfg0
                      exitWith ecode
                    else exitWith ecode

checkOneFL f cfg0 t = do
  val <- getGhcInfo cfg0 t
  case val of
    Left _ -> return []
    Right info -> do
      liquidOneFL f t info
      return []

liquidOneFL f target info = do
  let cfg = config $ spec info 
  let cbs' = transformScope (cbs info)
  prune cfg cbs' target info
  let cgi = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs'}
  finfo <- cgInfoFInfo info cgi
  f (fx cfg) finfo
  where
     fx cfg = def { FC.solver  = fromJust (smtsolver cfg)
              , FC.real    = real   cfg
              , FC.native  = native cfg
              , FC.srcFile = target
              }

flRepl cfg finfo = do
  putStr "b/w/q >>"
  hFlush stdout
  conStr <- getLine
  let cons = words conStr
  case head cons of
    "b" -> do
      let consid = map (\x -> read x :: Integer) $ tail cons
      putStr "blacklisting cons:"
      print consid
      let cm' = M.fromList $ filter (not . flip elem consid . fst) $ M.toList $ cm finfo
      solveNewCons cm'
      
    "w" -> do
      let consid = map (\x -> read x :: Integer) $ tail cons
      let cm' = M.fromList $ filter (flip elem consid . fst) $ M.toList $ cm finfo
      putStrLn "WHITELISTED "
      print consid
      solveNewCons cm'

    "q" -> return ()
    _   -> flRepl cfg finfo

  where solveNewCons cm' = do
          let finfo' = finfo { cm = cm' }
          Result res _ <- solve cfg finfo'
          case res of 
            Safe -> do
              putStrLn "safe!"
              flRepl cfg finfo
            Unsafe fcons -> do
              putStrLn "unsafe!"
              sequence $ map (print . sid) fcons
              flRepl cfg finfo
            Crash fcons errmsg -> do
              putStrLn "crash!"
              putStrLn errmsg
              sequence $ map (print . sid) fcons
              flRepl cfg finfo
            UnknownError errmsg -> do
              putStrLn errmsg
              flRepl cfg finfo


{--
liquidOneFL target info = do
  let cfg   = config $ spec info 
  let cbs' = transformScope (cbs info)
  dc <- prune cfg cbs' target info
  let cgi   = {-# SCC "generateConstraints" #-} generateConstraints $! info {cbs = cbs'}
  -- cgi `deepseq` 0
  let cons = fixCs cgi
  consFL <- deltaDebug cfg target cgi info dc cons []
  return consFL
--}

-- test() for delta debugging algorithm
-- intuitively, check if set of constraints cons induces
-- failure of the refinement
{-
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
-}
    

checkOne :: Config -> FilePath -> IO ([Integer], Output Doc)
checkOne cfg0 t = getGhcInfo cfg0 t >>= either errOut (liquidOne t)
  where
    errOut r    = do
      doc <- exitWithResult cfg0 t $ mempty { o_result = r}
      return ([], doc)

liquidOne :: FilePath -> GhcInfo -> IO ([Integer], Output Doc)
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
     (failedCons, out)      <- solveCs cfg target cgi info' dc
     donePhase Loud "solve"
     let out'  = mconcat [maybe mempty DC.oldOutput dc, out]
     DC.saveResult target out'
     outDoc <- exitWithResult cfg target out'
     return (filtNothing failedCons, outDoc)
     where filtNothing fc = fc >>= (\c -> maybe [] (\id -> [id]) c)

checkedNames ::  Maybe DC.DiffCheck -> Maybe [String]
checkedNames dc          = concatMap names . DC.newBinds <$> dc
   where
     names (NonRec v _ ) = [showpp $ shvar v]
     names (Rec xs)      = map (shvar . fst) xs
     shvar               = showpp . varName

prune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Maybe DC.DiffCheck)
prune cfg cbinds target info
  | not (null vs) = return . Just $ DC.DC (DC.thin cbinds vs) mempty sp
  | diffcheck cfg = DC.slice target cbinds sp
  | otherwise     = return Nothing
  where
    vs            = tgtVars sp
    sp            = spec info


flDir = ".liquidfl/"
printResults cfg r sol = case r of 
  Unsafe cons -> do
    putStrLn "Unsafe!"
    dumpErrOut cons
    return $ map sid cons

  Crash cons _ -> do
    putStrLn "Crash!"
    dumpErrOut cons
    return $ map sid cons
  
  UnknownError _ -> do
    putStrLn "Unknown error!"
    dumpErrOut []
    return []

  Safe -> do
    putStrLn "Safe!"
    putStrLn "Solution: "
    print sol
    return []
  
  where dumpErrOut cons = do
          -- create flDir if it doesn't exist
          dirExists <- doesDirectoryExist flDir
          if dirExists
            then return ()
            else createDirectory flDir

          -- emit JSON file of error output
          let errname = flDir ++ (head $ files cfg) ++ ".errout"
          withFile errname WriteMode $ \file -> do
            let conIDs = J.showJSONs $ map sid cons
            let locs = J.showJSONs $ uniqueSrcSpans $ map (ci_loc . sinfo) cons
            let info = J.JSString $ J.toJSString $ foldr (\x acc -> x ++ " " ++ acc) "" $ map (maybe "" show . sid) cons
            let jres =  J.makeObj [("cons",conIDs),("locs",locs),("info",info),("time",J.showJSON (0:: Int))]
            hPutStr file $ J.encode jres

          let errHtml = flDir ++ (head $ files cfg) ++ ".errout.html"
          let locs = (uniqueSrcSpans . map (ci_loc . sinfo)) cons
          let annots = generateFLAnnotation locs
          generateHtml (head $ files cfg) errHtml annots

solveCs cfg target cgi info dc
  = do finfo    <- cgInfoFInfo info cgi
       Result r sol <- solve fx finfo
       failedCons <- printResults cfg r sol
       let names = checkedNames dc
       let warns = logErrors cgi
       let annm  = annotMap cgi
       let res   = ferr sol r
       let out0  = mkOutput cfg res sol annm
       return (failedCons, out0 { o_vars = names } { o_errors  = warns} { o_result = res })
    where
       fx        = def { FC.solver  = fromJust (smtsolver cfg)
                       , FC.real    = real   cfg
                       , FC.native  = native cfg
                       , FC.srcFile = target
                       -- , FC.stats   = True
                       }
       ferr s r  = fmap (tidyError s) $ result $ sinfo <$> r

-- filterConstraints filt finfo =
    -- finfo { cm = M.fromList $ filt $ M.toList $ cm finfo }


-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
