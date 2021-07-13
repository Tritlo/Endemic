{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Endemic.Util
-- Description : Contains general and other orphaned functions of Endemic
-- License     : MIT
-- Stability   : experimental
-- Your everyday Util file.
-- Most of the functions contained are about logging.
-- This is a pure module.
module Endemic.Util where

import Control.Exception (assert)
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Bits
import Data.Char (isSpace, toUpper)
import Data.IORef (IORef, modifyIORef, newIORef, readIORef)
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Time.Clock (getCurrentTime)
import Data.Time.Format (defaultTimeLocale, formatTime)
import Endemic.Configuration
import Endemic.Types (EExpr, EType, LogLevel (..))
import GHC
import GHC.IO.Unsafe (unsafePerformIO)
import GHC.Stack (callStack, getCallStack, withFrozenCallStack)
import qualified GHC.Stack as GHS
import GhcPlugins (HasCallStack, Outputable (ppr), fsLit, mkVarUnqual, showSDocUnsafe)
import SrcLoc
import System.CPUTime (getCPUTime)
import System.Directory (doesFileExist)
import System.IO (hFlush, stdout)
import Text.Printf (printf)

progAtTy :: EExpr -> EType -> EExpr
progAtTy e_prog e_ty =
  noLoc $ ExprWithTySig NoExtField (noLoc $ HsPar NoExtField e_prog) e_ty

undefVar :: HsExpr GhcPs
undefVar = HsVar NoExtField $ noLoc $ mkVarUnqual $ fsLit "undefined"

-- | Removes whitespace before and after a string
trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- | Splits a list by a given element.
-- The splitting element is not included in the created lists.  This could be
-- provided by libraries, but we didn't want to introduce a dependency for
-- 6 lines of code (this is not JS).
split :: Eq a => a -> [a] -> [[a]]
split _ [] = []
split a as =
  t : case r of
    [] -> []
    _ : rs -> split a rs
  where
    (t, r) = break (a ==) as

logStr :: HasCallStack => LogLevel -> String -> IO ()
logStr olvl str = do
  lvl <- readIORef lOGLEVEL
  when (olvl >= lvl) $ do
    let (loc : _) = map snd $ getCallStack callStack
        sfile = split '/' $ GHS.srcLocFile loc
        (i, l) = assert (not (null sfile) && not (any null sfile)) (init sfile, last sfile)
        sfileRes = intercalate "/" (map (take 1) i ++ [l])
        sline = show (GHS.srcLocStartLine loc)
    showLoc <- readIORef lOGLOC
    let locO = if showLoc then "<" ++ sfileRes ++ ":" ++ sline ++ "> " else ""
    putStrLn $ locO ++ show olvl ++ ": " ++ str

logOut :: (HasCallStack, Outputable p) => LogLevel -> p -> IO ()
logOut olvl = withFrozenCallStack . logStr olvl . showUnsafe

showUnsafe :: Outputable p => p -> String
showUnsafe = showSDocUnsafe . ppr

-- Prints a string, and then flushes, so that intermediate strings show up
putStr' :: String -> IO ()
putStr' str = putStr str >> hFlush stdout

-- Drop a prefix of a string, i.e. dropPrefix "123" "123abc" == "abc"
dropPrefix :: String -> String -> String
dropPrefix (p : ps) (s : ss) | p == s = dropPrefix ps ss
dropPrefix _ s = s

prop_dropsPrefix :: String -> String -> Bool
prop_dropsPrefix st rest = dropPrefix st (st ++ rest) == rest

-- Checks if a string starts with a given prefix
startsWith :: String -> String -> Bool
startsWith [] _ = True
startsWith (p : ps) (s : ss) | p == s = startsWith ps ss
startsWith _ _ = False

prop_startsWith :: String -> String -> Bool
prop_startsWith st rest = startsWith st (st ++ rest)

contextLet :: [String] -> String -> String
contextLet context l =
  "let {" ++ intercalate "; " (concatMap lines context) ++ "} in " ++ l

-- Turns a list of booleans into an int
boolsToBit :: [Bool] -> Int
boolsToBit bs
  | length bs > size =
    error $ "Only works for lists of length <= " ++ show size
  where
    size = finiteBitSize (0 :: Int)
boolsToBit bs = (foldl (.|.) zeroBits . map (bit . fst) . filter snd . zip [0 ..]) bs

-- Turns an int into a list of booleans
bitToBools :: Int -> [Bool]
bitToBools b = map (testBit b) [0 .. finiteBitSize (0 :: Int) -1]

-- | We want to be able to make SrcSpans into the ones made by `justParseExpr`,
-- which means we replace the actual filenames with "<interactive>".
mkInteractive :: SrcSpan -> SrcSpan
-- Case 1: We have a real source Span
mkInteractive (RealSrcSpan rs) = RealSrcSpan $ mkRealSrcSpan ns ne
  where
    -- Make a lookup for the old span but use the interactive for further computing

    UnhelpfulSpan ic = interactiveSrcSpan
    rss = realSrcSpanStart rs
    rse = realSrcSpanEnd rs
    ns = mkRealSrcLoc ic (srcLocLine rss) (srcLocCol rss)
    ne = mkRealSrcLoc ic (srcLocLine rse) (srcLocCol rse)
-- Case 2: The source span was interactive or other anyway
mkInteractive (UnhelpfulSpan _) = interactiveSrcSpan

-- | Inserts the given element at the given index in the list, or at the end
insertAt ::
  -- | the index at which the element should be inserted (0 is head)
  Int ->
  -- | the element to be inserted
  a ->
  -- | the list in which to insert
  [a] ->
  -- | the list with the new element at given index,
  --   or at the end if the given index was out of list.
  [a]
insertAt _ a [] = [a]
insertAt 0 a as = a : as
insertAt n a (x : xs) = x : insertAt (n -1) a xs

-- | Transforms time given in ns (as measured by "time") into a string
showTime :: Integer -> String
showTime time_i =
  if res > 1000
    then printf "%.2f" ((fromIntegral res * 1e-3) :: Double) ++ "s"
    else show res ++ "ms"
  where
    res :: Integer
    res = floor $ fromIntegral time_i * (1e-9 :: Double)

-- | Stopwatch for a given function, measures the time taken by a given act.
time :: MonadIO m => m a -> m (Integer, a)
time act = do
  start <- liftIO getCPUTime
  r <- act
  done <- liftIO getCPUTime
  return (done - start, r)

statsRef :: IORef (Map.Map (String, Int) Integer)
{-# NOINLINE statsRef #-}
statsRef = unsafePerformIO $ newIORef Map.empty

collectStats :: (MonadIO m, HasCallStack) => m a -> m a
collectStats a = do
  (t, r) <- time a
  let ((_, GHS.SrcLoc {..}) : _) = getCallStack callStack
  liftIO $ modifyIORef statsRef (Map.insertWith (+) (srcLocFile, srcLocStartLine) t)
  withFrozenCallStack $ liftIO $ logStr AUDIT (showTime t)
  return r

reportStats :: MonadIO m => m ()
reportStats = liftIO $ do
  logStr AUDIT "SUMMARY"
  res <- Map.toList <$> readIORef statsRef
  let pp ((f, l), t) = "<" ++ f ++ ":" ++ show l ++ "> " ++ showTime t
  mapM_ (logStr AUDIT . pp) res

reportStats' :: MonadIO m => LogLevel -> m ()
reportStats' lvl = liftIO $ do
  logStr lvl "SUMMARY"
  res <- Map.toList <$> readIORef statsRef
  let pp ((f, l), t) = "<" ++ f ++ ":" ++ show l ++ "> " ++ showTime t
  mapM_ (logStr lvl . pp) res

-- | Helper to save all given patches to the corresponding files.
-- Files will start as fix1.patch in the given base-folder.
-- The files are in reverse order to have a nicer recursion - patch 1 is the last one found.
savePatchesToFiles ::
  OutputConfig ->
  -- | The patches, represented as pretty-printed strings
  [String] ->
  IO ()
savePatchesToFiles _ [] = return ()
savePatchesToFiles oc@OutputConf {..} patches@(p : ps) = do
  let n = length patches
  saveToFile oc p (directory ++ "/fix" ++ (show n) ++ ".patch")
  savePatchesToFiles oc ps

-- | Saves the given String to a file.
-- Throws an Error in case the file already existet
-- (this is a bit chicken, but I want this app to be save so no wildcard overwriting of stuff).
-- To be repeatably usable, we just add the current timestamp to the output directory upstream,
-- that is we make a folder output-yy-mm-dd-hh-mm and start writing patch1 patch2 ...
saveToFile ::
  OutputConfig ->
  -- | The Content of the file to be created
  String ->
  -- | The Path to the file to be created, including the file name (e.g. "./tmp/fileA.txt")
  String ->
  IO ()
saveToFile OutputConf {..} content path = do
  fileExists <- doesFileExist path
  if fileExists && (not overwrite)
    then error "File already exists - aborting creation of patch"
    else do
      -- handle <- openFile path ReadWriteMode
      writeFile path content
      --hClose handle
      return ()

-- | Returns the current time as yyyy-mm-dd-HH-MM
formattedTime :: OutputConfig -> IO String
formattedTime OutputConf {..} = do
  time <- getCurrentTime
  let format = "%Y-%m-%d-%HH-%MM"
  -- TODO: Save locale here?
  return (formatTime defaultTimeLocale format time)
