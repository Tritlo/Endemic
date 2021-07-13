{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Endemic.Eval
-- Description : Contains most parts that directly rely on GHC Compilation
-- License     : MIT
-- Stability   : experimental
--
-- This module holds most of the methods that interact with the GHC.
-- This is a low-level module. This module is impure.
-- This consists of the following blocks:
--
-- 1. Parsing a given problem from String into actual expressions of the Code
-- 2. Compiling given expression and their types, e.g. to check for hole fits later
-- 3. Finding Candidates for Genetic Programming
-- 4. Configuration for this and other parts of the project
module Endemic.Eval where

-- GHC API

import Bag (bagToList, emptyBag, listToBag, unitBag)
import Constraint
import Control.Concurrent.Async (mapConcurrently)
import Control.Monad (when, (>=>))
import qualified CoreUtils
import qualified Data.Bifunctor
import Data.Bits (complement)
import Data.Char (isAlphaNum)
import Data.Dynamic (Dynamic, fromDynamic)
import Data.Function (on)
import Data.IORef (IORef, newIORef, readIORef)
import Data.List (groupBy, intercalate, partition)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, isNothing, mapMaybe)
import qualified Data.Set as Set
import Data.Time.Clock (getCurrentTime)
import Data.Tree (Tree (Node, rootLabel))
import Desugar (deSugarExpr)
import DynFlags
import Endemic.Check
import Endemic.Configuration
import Endemic.Plugin (synthPlug)
import Endemic.Traversals (flattenExpr)
import Endemic.Types
import Endemic.Util
import ErrUtils (pprErrMsgBagWithLoc)
import FV (fvVarSet)
import GHC
import GHC.Paths (libdir)
import GHC.Prim (unsafeCoerce#)
import GhcPlugins hiding (exprType)
import PrelNames (mkMainModule, toDynName)
import RnExpr (rnLExpr)
import StringBuffer (stringToStringBuffer)
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath (dropExtension, takeFileName)
import System.IO (Handle, hClose, hGetLine, openTempFile)
import System.Posix.Process
import System.Posix.Signals
import System.Process
import System.Timeout (timeout)
import TcExpr (tcInferSigma)
import TcHoleErrors (HoleFit (..), TypedHole (..))
import TcSimplify (captureTopConstraints)
import Trace.Hpc.Mix
import Trace.Hpc.Tix (Tix (Tix), TixModule (..), readTix)
import Trace.Hpc.Util (HpcPos, fromHpcPos)

-- Configuration and GHC setup

holeFlags :: [GeneralFlag]
holeFlags =
  [ Opt_ShowHoleConstraints,
    Opt_ShowProvOfHoleFits,
    Opt_ShowTypeAppVarsOfHoleFits,
    Opt_ShowTypeAppOfHoleFits,
    Opt_ShowTypeOfHoleFits
  ]

setFlags :: [GeneralFlag]
setFlags = [Opt_Hpc]

config :: Int -> DynFlags -> DynFlags
config lvl sflags =
  flip (foldl gopt_set) setFlags $
    (foldl gopt_unset sflags (Opt_OmitYields : holeFlags))
      { maxValidHoleFits = Nothing,
        maxRefHoleFits = Nothing,
        refLevelHoleFits = Just lvl
      }

----

-- | This method takes a package given as a string and puts it into the GHC PackageFlag-Type
toPkg :: String -> PackageFlag
toPkg str = ExposePackage ("-package " ++ str) (PackageArg str) (ModRenaming True [])

-- | Initializes the context and the hole fit plugin with no
-- expression fit candidates
initGhcCtxt :: CompileConfig -> Ghc (IORef [(TypedHole, [HoleFit])])
initGhcCtxt cc = initGhcCtxt' False cc []

-- | Intializes the hole fit plugin we use to extract fits and inject
-- expression fits, as well as adding any additional imports.
initGhcCtxt' ::
  Bool ->
  -- | Whether to use Caching
  CompileConfig ->
  -- | The experiment configuration
  [ExprFitCand] ->
  Ghc (IORef [(TypedHole, [HoleFit])])
initGhcCtxt' use_cache CompConf {..} local_exprs = do
  -- First we have to add "base" to scope
  flags <- config hole_lvl <$> getSessionDynFlags
  --`dopt_set` Opt_D_dump_json
  plugRef <- liftIO $ newIORef []
  let flags' =
        flags
          { packageFlags =
              packageFlags flags
                ++ map toPkg packages,
            staticPlugins = sPlug : staticPlugins flags
          }
      sPlug =
        StaticPlugin $
          PluginWithArgs
            { paArguments = [],
              paPlugin = synthPlug use_cache local_exprs plugRef
            }
  -- "If you are not doing linking or doing static linking, you can ignore the list of packages returned."
  toLink <- setSessionDynFlags flags'
  -- (hsc_dynLinker <$> getSession) >>= liftIO . (flip extendLoadedPkgs toLink)
  -- Then we import the prelude and add it to the context
  imports <- mapM (fmap IIDecl . parseImportDecl) importStmts
  getContext >>= setContext . (imports ++)
  return plugRef

justParseExpr :: CompileConfig -> RExpr -> Ghc (LHsExpr GhcPs)
justParseExpr cc str = do
  _ <- initGhcCtxt cc
  parseExprNoInit str

parseExprNoInit :: HasCallStack => RExpr -> Ghc (LHsExpr GhcPs)
parseExprNoInit str =
  handleSourceError
    (\err -> printException err >> error ("parse failed in: `" ++ str ++ "`"))
    (parseExpr str)

runJustParseExpr :: CompileConfig -> RExpr -> IO (LHsExpr GhcPs)
runJustParseExpr cc str = runGhc (Just libdir) $ justParseExpr cc str

type ValsAndRefs = ([HoleFit], [HoleFit])

-- |
--  The compiler result, which can either be a set of values and refs (everything
--  worked) or still be dynamic, which means that some kind of error occurred.
--  That could be that the holes are not resolvable, the program does not clearly
--  terminate etc.
type CompileRes = Either [ValsAndRefs] Dynamic

-- | By integrating with a hole fit plugin, we can extract the fits (with all
-- the types and everything directly, instead of having to parse the error
-- message)
getHoleFitsFromError ::
  IORef [(TypedHole, [HoleFit])] ->
  SourceError ->
  Ghc (Either [ValsAndRefs] b)
getHoleFitsFromError plugRef err = do
  liftIO $ logOut AUDIT $ pprErrMsgBagWithLoc $ srcErrorMessages err
  res <- liftIO $ readIORef plugRef
  when (null res) (printException err)
  let gs = groupBy (sameHole `on` fst) res
      allFitsOfHole ((th, f) : rest) = (th, concat $ f : map snd rest)
      allFitsOfHole [] = error "no-fits!"
      valsAndRefs = map ((partition part . snd) . allFitsOfHole) gs
  return $ Left valsAndRefs
  where
    part (RawHoleFit _) = True
    part HoleFit {..} = hfRefLvl <= 0
    sameHole :: TypedHole -> TypedHole -> Bool
    sameHole
      TyH {tyHCt = Just CHoleCan {cc_hole = h1}}
      TyH {tyHCt = Just CHoleCan {cc_hole = h2}} =
        holeOcc h1 == holeOcc h2
    sameHole _ _ = False

monomorphiseType :: CompileConfig -> RType -> IO (Maybe RType)
monomorphiseType cc ty =
  runGhc (Just libdir) $ do
    _ <- initGhcCtxt cc
    flags <- getSessionDynFlags
    let pp = showSDoc flags . ppr
    nothingOnError (pp . mono <$> exprType TM_Default ("undefined :: " ++ ty))
  where
    mono ty' = substTyWith tvs (replicate (length tvs) unitTy) base_ty
      where
        (tvs, base_ty) = splitForAllTys ty'

-- |
--  This method tries attempts to parse a given Module into a repair problem.
moduleToProb ::
  CompileConfig ->
  -- | A given Compilerconfig to use for the Module
  FilePath ->
  -- | The Path under which the module is located
  Maybe String ->
  -- | "mb_target" whether to target a specific type (?)
  IO (CompileConfig, ParsedModule, [EProblem])
moduleToProb cc@CompConf {..} mod_path mb_target = do
  let target = Target (TargetFile mod_path Nothing) True Nothing
  -- Feed the given Module into GHC
  runGhc (Just libdir) $ do
    _ <- initGhcCtxt cc
    addTarget target
    _ <- load LoadAllTargets
    let mname = mkModuleName $ dropExtension $ takeFileName mod_path
    -- Retrieve the parsed module
    modul@ParsedModule {..} <- getModSummary mname >>= parseModule
    let (L _ HsModule {..}) = pm_parsed_source
        cc' = cc {importStmts = importStmts ++ imps'}
          where
            imps' = map showUnsafe hsmodImports
        -- Retrieves the Values declared in the given Haskell-Module
        valueDeclarations :: [LHsBind GhcPs]
        valueDeclarations = mapMaybe fromValD hsmodDecls
          where
            fromValD (L l (ValD _ b)) = Just (L l b)
            fromValD _ = Nothing
        -- Retrieves the Sigmas declared in the given Haskell-Module
        sigmaDeclarations :: [LSig GhcPs]
        sigmaDeclarations = mapMaybe fromSigD hsmodDecls
          where
            fromSigD (L l (SigD _ s)) = Just (L l s)
            fromSigD _ = Nothing

        toCtxt :: [LHsBind GhcPs] -> LHsLocalBinds GhcPs
        toCtxt vals = noLoc $ HsValBinds NoExtField (ValBinds NoExtField (listToBag vals) sigmaDeclarations)
        ctxt :: LHsLocalBinds GhcPs
        ctxt = toCtxt valueDeclarations

        props :: [LHsBind GhcPs]
        props = mapMaybe fromPropD hsmodDecls
          where
            fromPropD (L l (ValD _ b@FunBind {..}))
              | ((==) "prop" . take 4 . occNameString . occName . unLoc) fun_id =
                Just (L l b)
            fromPropD _ = Nothing

        fix_targets :: [RdrName]
        fix_targets = Set.toList $ fun_ids `Set.intersection` prop_vars
          where
            funId (L _ (ValD _ FunBind {..})) = Just $ unLoc fun_id
            funId _ = Nothing
            fun_ids = Set.fromList $ mapMaybe funId hsmodDecls
            mbVar (L _ (HsVar _ v)) = Just $ unLoc v
            mbVar _ = Nothing
            prop_vars =
              Set.fromList $
                mapMaybe mbVar $
                  flattenExpr (noLoc $ HsLet NoExtField (toCtxt props) (tf "undefined"))

        getTarget :: RdrName -> Maybe EProblem
        getTarget t_name =
          case prog_sig of
            Just s ->
              Just $
                EProb
                  { e_target = t_name,
                    e_prog = wp_expr s,
                    e_ctxt = ctxt,
                    e_ty = prog_ty s,
                    e_props = wrapped_props
                  }
            _ -> Nothing
          where
            isTDef (L _ (SigD _ (TypeSig _ ids _))) = t_name `elem` map unLoc ids
            isTDef (L _ (ValD _ FunBind {..})) = t_name == unLoc fun_id
            isTDef _ = False
            -- We get the type of the program
            getTType (L _ (SigD _ ts@(TypeSig _ ids _)))
              | t_name `elem` map unLoc ids = Just ts
            getTType _ = Nothing
            -- takes prop :: t ==> prop' :: target_type -> t since our
            -- previous assumptions relied on the properties to take in the
            -- function being fixed  as the first argument.
            wrapProp :: LHsBind GhcPs -> LHsBind GhcPs
            wrapProp (L l fb@FunBind {..}) = L l fb {fun_id = nfid, fun_matches = nmatches fun_matches}
              where
                mkFid (L l' (Unqual occ)) = L l' (Unqual (nocc occ))
                mkFid (L l' (Qual m occ)) = L l' (Qual m (nocc occ))
                nfid = mkFid fun_id
                nocc o = mkOccName (occNameSpace o) $ insertAt 4 '\'' $ occNameString o
                nmatches mg@MG {mg_alts = (L l' alts)} = mg {mg_alts = L l' $ map nalt alts}
                  where
                    nalt (L l'' m@Match {..}) = L l'' m {m_pats = nvpat : m_pats, m_ctxt = n_ctxt}
                      where
                        n_ctxt =
                          case m_ctxt of
                            fh@FunRhs {mc_fun = L l''' _} ->
                              fh {mc_fun = L l''' $ unLoc nfid}
                            o -> o
                    nvpat = noLoc $ VarPat NoExtField $ noLoc t_name
            wrapProp e = e
            wrapped_props = map wrapProp props
            prog_binds :: LHsBindsLR GhcPs GhcPs
            prog_binds = listToBag $ mapMaybe f $ filter isTDef hsmodDecls
              where
                f (L _ (ValD _ b)) = Just $ noLoc b
                f _ = Nothing
            prog_sig :: Maybe (Sig GhcPs)
            prog_sig = case mapMaybe getTType hsmodDecls of
              (pt : _) -> Just pt
              _ -> Nothing
            prog_ty :: Sig GhcPs -> EType
            prog_ty prog_sig' = sig
              where
                (TypeSig _ _ sig) = prog_sig'
            wp_expr :: Sig GhcPs -> LHsExpr GhcPs
            wp_expr prog_sig' = noLoc $ HsLet noExtField (noLoc lbs) (noLoc le)
              where
                le = HsVar noExtField $ noLoc t_name
                lbs =
                  HsValBinds noExtField $
                    ValBinds noExtField prog_binds [noLoc prog_sig']
        probs = case mb_target of
          Just t ->
            case getTarget (mkVarUnqual $ fsLit t) of
              Just r -> [r]
              _ -> error $ "Could not find type of the target `" ++ t ++ "`!"
          Nothing -> mapMaybe getTarget fix_targets
    return (cc', modul, probs)

-- Create a fake base loc for a trace.
fakeBaseLoc :: CompileConfig -> EExpr -> IO SrcSpan
fakeBaseLoc = fmap (getLoc <$>) . buildTraceCorrelExpr

-- When we do the trace, we use a "fake_target" function. This build the
-- corresponding expression,
buildTraceCorrelExpr :: CompileConfig -> EExpr -> IO (LHsExpr GhcPs)
buildTraceCorrelExpr cc expr = do
  let correl = baseFun (mkVarUnqual $ fsLit "fake_target") expr
      correl_ctxt = noLoc $ HsValBinds NoExtField (ValBinds NoExtField (unitBag correl) [])
      correl_expr = (noLoc $ HsLet NoExtField correl_ctxt hole) :: LHsExpr GhcPs
  pcorrel <- runJustParseExpr cc $ showUnsafe correl_expr
  let (L _ (HsLet _ (L _ (HsValBinds _ (ValBinds _ bg _))) _)) = pcorrel
      [L _ FunBind {fun_matches = MG {mg_alts = (L _ alts)}}] = bagToList bg
      [L _ Match {m_grhss = GRHSs {grhssGRHSs = [L _ (GRHS _ _ bod)]}}] = alts
  return bod

-- We build a Map from the traced expression and to the  original so we can
-- correlate the trace information with the expression we're checking.
buildTraceCorrel :: CompileConfig -> EExpr -> IO (Map.Map SrcSpan SrcSpan)
buildTraceCorrel cc expr =
  Map.fromList
    . filter (\(b, e) -> isGoodSrcSpan b && isGoodSrcSpan e)
    . flip (zipWith (\b e -> (getLoc b, getLoc e))) (flattenExpr expr)
    . flattenExpr
    <$> buildTraceCorrelExpr cc expr

traceTarget ::
  CompileConfig ->
  EExpr ->
  EProp ->
  [RExpr] ->
  IO (Maybe (Tree (SrcSpan, [(BoxLabel, Integer)])))
traceTarget cc e fp ce = head <$> traceTargets cc e [(fp, ce)]

-- Run HPC to get the trace information.
traceTargets ::
  CompileConfig ->
  EExpr ->
  [(EProp, [RExpr])] ->
  IO [Maybe (Tree (SrcSpan, [(BoxLabel, Integer)]))]
traceTargets cc expr@(L (RealSrcSpan realSpan) _) ps_w_ce = do
  let tempDir = "./fake_targets"
  createDirectoryIfMissing False tempDir
  (the_f, handle) <- openTempFile tempDir "FakeTarget.hs"
  -- We generate the name of the module from the temporary file
  let mname = filter isAlphaNum $ dropExtension $ takeFileName the_f
      correl = baseFun (mkVarUnqual $ fsLit "fake_target") expr
      modTxt = exprToTraceModule cc mname correl ps_w_ce
      strBuff = stringToStringBuffer modTxt
      exeName = dropExtension the_f
      mixFilePath = tempDir

  logStr DEBUG modTxt
  -- Note: we do not need to dump the text of the module into the file, it
  -- only needs to exist. Otherwise we would have to write something like
  -- `hPutStr handle modTxt`
  hClose handle
  _ <- liftIO $ mapM (logStr DEBUG) $ lines modTxt
  runGhc (Just libdir) $ do
    _ <- initGhcCtxt cc
    -- We set the module as the main module, which makes GHC generate
    -- the executable.
    dynFlags <- getSessionDynFlags
    _ <-
      setSessionDynFlags $
        dynFlags
          { mainModIs = mkMainModule $ fsLit mname,
            hpcDir = "./fake_targets"
          }
    now <- liftIO getCurrentTime
    let tid = TargetFile the_f Nothing
        target = Target tid True $ Just (strBuff, now)

    -- Adding and loading the target causes the compilation to kick
    -- off and compiles the file.
    addTarget target
    _ <- load LoadAllTargets
    -- We should for here in case it doesn't terminate, and modify
    -- the run function so that it use the trace reflect functionality
    -- to timeout and dump the tix file if possible.
    let runTrace which = liftIO $ do
          let tixFilePath = exeName ++ "_" ++ show @Integer which ++ ".tix"
          (_, _, _, ph) <-
            createProcess
              (proc exeName [show which])
                { env = Just [("HPCTIXFILE", tixFilePath)],
                  -- We ignore the output
                  std_out = CreatePipe
                }
          ec <- timeout timeoutVal $ waitForProcess ph

          let -- If it doesn't respond to signals, we can't do anything
              -- other than terminate
              loop :: Maybe ExitCode -> Integer -> IO ()
              loop _ 0 = terminateProcess ph
              loop exit_code n = when (isNothing exit_code) $ do
                -- If it's taking too long, it's probably stuck in a loop.
                -- By sending the right signal though, it will dump the tix
                -- file before dying.
                mb_pid <- getPid ph
                case mb_pid of
                  Just pid ->
                    do
                      signalProcess keyboardSignal pid
                      ec2 <- timeout timeoutVal $ waitForProcess ph
                      loop ec2 (n -1)
                  _ ->
                    -- It finished in the brief time between calls, so we're good.
                    return ()
          -- We give it 3 tries
          loop ec 3

          tix <- readTix tixFilePath
          let rm m = (m,) <$> readMix [mixFilePath] (Right m)
          case tix of
            Just (Tix mods) -> do
              -- We throw away any extra functions in the file, such as
              -- the properties and the main function, and only look at
              -- the ticks for our expression
              [n@Node {rootLabel = (root, _)}] <- filter isTarget . concatMap toDom <$> mapM rm mods
              return $ Just (fmap (Data.Bifunctor.first (toFakeSpan the_f root)) n)
            _ -> return Nothing
    removeTarget tid
    let (checks, _) = unzip $ zip [0 ..] ps_w_ce
    mapM runTrace checks
  where
    toDom :: (TixModule, Mix) -> [MixEntryDom [(BoxLabel, Integer)]]
    toDom (TixModule _ _ _ ts, Mix _ _ _ _ es) =
      createMixEntryDom $ zipWith (\t (pos, bl) -> (pos, (bl, t))) ts es
    isTarget Node {rootLabel = (_, [(TopLevelBox ["fake_target"], _)])} = True
    isTarget _ = False
    -- We convert the HpcPos to the equivalent span we would get if we'd
    -- parsed and compiled the expression directly.
    toFakeSpan :: FilePath -> HpcPos -> HpcPos -> SrcSpan
    toFakeSpan the_f root sp = mkSrcSpan start end
      where
        fname = fsLit $ takeFileName the_f
        (_, _, rel, rec) = fromHpcPos root
        eloff = rel - srcSpanEndLine realSpan
        ecoff = rec - srcSpanEndCol realSpan
        (sl, sc, el, ec) = fromHpcPos sp
        -- We add two spaces before every line in the source.
        start = mkSrcLoc fname (sl - eloff) (sc - ecoff -1)
        -- GHC Srcs end one after the end
        end = mkSrcLoc fname (el - eloff) (ec - ecoff)
traceTargets cc e@(L _ xp) ps_w_ce = do
  tl <- fakeBaseLoc cc e
  traceTargets cc (L tl xp) ps_w_ce

exprToTraceModule :: CompileConfig -> String -> LHsBind GhcPs -> [(EProp, [RExpr])] -> RExpr
exprToTraceModule CompConf {..} mname expr ps_w_ce =
  unlines $
    ["module " ++ mname ++ " where"]
      ++ importStmts
      ++ checkImports
      ++ concatMap (lines . showUnsafe) failing_props
      ++ [showUnsafe expr]
      ++ [concat ["checks = [", checks, "]"]]
      ++ [ "",
           "main :: IO ()",
           "main = do [which] <- getArgs",
           "          act <- checks !! (read which)",
           "          print (isSuccess act) "
         ]
  where
    (failing_props, failing_argss) = unzip ps_w_ce
    toName :: LHsBind GhcPs -> String
    toName (L _ FunBind {fun_id = fid}) = showUnsafe fid
    toName (L _ VarBind {var_id = vid}) = showUnsafe vid
    toName _ = error "Unsupported bind!"
    pnames = map toName failing_props
    nas = zip pnames failing_argss
    toCall pname args =
      "quickCheckWithResult (" ++ (showUnsafe (qcArgsExpr Nothing)) ++ ") ("
        ++ pname
        ++ " fake_target "
        ++ unwords args
        ++ ")"
    checks :: String
    checks = intercalate ", " $ map (uncurry toCall) nas

-- | Prints the error and stops execution
reportError :: (HasCallStack, GhcMonad m, Outputable p) => p -> SourceError -> m b
reportError p e = do
  liftIO $ do
    putStrLn "FAILED!"
    putStrLn "UNEXPECTED EXCEPTION WHEN COMPILING CHECK:"
    putStrLn (showUnsafe p)
  printException e
  error "UNEXPECTED EXCEPTION"

-- | Tries an action, returning Nothing in case of error
nothingOnError :: GhcMonad m => m a -> m (Maybe a)
nothingOnError act = handleSourceError (const $ return Nothing) (Just <$> act)

-- | Tries an action, reports about it in case of error
reportOnError :: (GhcMonad m, Outputable t) => (t -> m a) -> t -> m a
reportOnError act a = handleSourceError (reportError a) (act a)

-- When we want to compile only one parsed check
compileParsedCheck :: HasCallStack => CompileConfig -> EExpr -> IO Dynamic
compileParsedCheck cc expr = runGhc (Just libdir) $ do
  _ <- initGhcCtxt (cc {hole_lvl = 0})
  dynCompileParsedExpr `reportOnError` expr

-- | Since initialization has some overhead, we have a special case for compiling
-- multiple checks at once.
compileParsedChecks :: HasCallStack => CompileConfig -> [EExpr] -> IO [CompileRes]
compileParsedChecks cc exprs = runGhc (Just libdir) $ do
  _ <- initGhcCtxt (cc {hole_lvl = 0})
  mapM (reportOnError ((Right <$>) . dynCompileParsedExpr)) exprs

-- | Adapted from dynCompileExpr in InteractiveEval
dynCompileParsedExpr :: GhcMonad m => LHsExpr GhcPs -> m Dynamic
dynCompileParsedExpr parsed_expr = do
  let loc = getLoc parsed_expr
      to_dyn_expr =
        mkHsApp
          (L loc . HsVar noExtField . L loc $ getRdrName toDynName)
          parsed_expr
  hval <- compileParsedExpr to_dyn_expr
  return (unsafeCoerce# hval :: Dynamic)

-- |
--  This method returns the types of gene-candidates.
--  To do so, it first needs to compile the code.
genCandTys :: CompileConfig -> (RType -> RExpr -> RExpr) -> [RExpr] -> IO [RType]
genCandTys cc bcat cands = runGhc (Just libdir) $ do
  _ <- initGhcCtxt (cc {hole_lvl = 0})
  flags <- getSessionDynFlags
  catMaybes
    <$> mapM
      ( \c ->
          nothingOnError $
            flip bcat c . showSDoc flags . ppr <$> exprType TM_Default c
      )
      cands

-- | The time to wait for everything to timeout, hardcoded to the same amount
--   as QuickCheck at the moment (1ms)
timeoutVal :: Int
timeoutVal = fromIntegral qcTime

-- | Right True means that all the properties hold, while Right False mean that
-- There is some error or infinite loop.
-- Left bs indicates that the properties as ordered by bs are the ones that hold
runCheck :: Either [ValsAndRefs] Dynamic -> IO (Either [Bool] Bool)
runCheck (Left _) = return (Right False)
runCheck (Right dval) =
  -- Note! By removing the call to "isSuccess" in the buildCheckExprAtTy we
  -- can get more information, but then there can be a mismatch of *which*
  -- `Result` type it is... even when it's the same QuickCheck but compiled
  -- with different flags. Ugh. So we do it this way, since *hopefully*
  -- Bool will be the same (unless *base* was compiled differently, *UGGH*).
  case fromDynamic @(IO [Bool]) dval of
    Nothing -> do
      logStr WARN "wrong type!!"
      return (Right False)
    Just fd_res -> do
      -- We need to forkProcess here, since we might be evaulating
      -- non-yielding infinte expressions (like `last (repeat head)`), and
      -- since they never yield, we can't do forkIO and then stop that thread.
      -- If we could ensure *every library* was compiled with -fno-omit-yields
      -- we could use lightweight threads, but that is a very big restriction,
      -- especially if we want to later embed this into a plugin.
      pid <- forkProcess (proc' fd_res)
      res <- timeout timeoutVal (getProcessStatus True False pid)
      case res of
        Just (Just (Exited ExitSuccess)) -> return $ Right True
        Nothing -> do
          signalProcess killProcess pid
          return $ Right False
        -- If we have more than 8 props, we cannot tell
        -- which ones failed from the exit code.
        Just (Just (Exited (ExitFailure x))) | x < 0 -> return $ Right False
        Just (Just (Exited (ExitFailure x))) ->
          return (Left $ take 8 $ bitToBools $ complement x)
        -- Anything else and we have no way to tell what went wrong.
        _ -> return $ Right False
  where
    proc' action = do
      res <- action
      exitImmediately $
        if and res
          then ExitSuccess
          else -- We complement here, since ExitFailure 0 (i.e.
          -- all tests failed) is turned into ExitSuccess.
          -- We are limited to a maximum of 8 here, since the POSIX exit
          -- code is only 8 bits.

            ExitFailure $
              if length res <= 8
                then complement $ boolsToBit res
                else -1

compile :: CompileConfig -> RType -> IO CompileRes
compile cc str = runGhc (Just libdir) $ do
  plugRef <- initGhcCtxt cc
  -- Then we can actually run the program!
  handleSourceError
    (getHoleFitsFromError plugRef)
    (Right <$> dynCompileExpr str)

compileAtType :: CompileConfig -> RExpr -> RType -> IO CompileRes
compileAtType cc str ty = compile cc ("((" ++ str ++ ") :: " ++ ty ++ ")")

showHF :: HoleFit -> String
showHF = showSDocUnsafe . pprPrefixOcc . hfId

readHole :: HoleFit -> (String, [RExpr])
readHole (RawHoleFit sdc) = (showSDocUnsafe sdc, [])
readHole hf@HoleFit {..} =
  ( showHF hf,
    map (showSDocUnsafe . ppr) hfMatches
  )

exprToCheckModule :: CompileConfig -> String -> EProblem -> [EExpr] -> RExpr
exprToCheckModule CompConf {..} mname tp fixes =
  unlines $
    ["module " ++ mname ++ " where"]
      ++ importStmts
      ++ checkImports
      ++ lines (showUnsafe ctxt)
      ++ lines (showUnsafe check_bind)
      ++ [ "",
           "runC__ :: Bool -> Int -> IO [Bool]",
           "runC__ pr which = do let f True  = 1",
           "                         f False = 0",
           "                     act <- checks__ !! which",
           "                     if pr then (putStrLn (concat (map (show . f) act))) else return ()",
           "                     return act"
         ]
      ++ [ "",
           -- We can run multiple in parallell, but then we will have issues
           -- if any of them loop infinitely.
           "main__ :: IO ()",
           "main__ = do whiches <- getArgs",
           "            mapM_ (runC__ True . read) whiches"
         ]
  where
    (ctxt, check_bind) = buildFixCheck tp fixes

-- | Parse, rename and type check an expression
justTcExpr :: CompileConfig -> EExpr -> Ghc (Maybe ((LHsExpr GhcTc, Type), WantedConstraints))
justTcExpr cc parsed = do
  _ <- initGhcCtxt cc
  hsc_env <- getSession
  (_, res) <-
    liftIO $
      runTcInteractive hsc_env $ captureTopConstraints $ rnLExpr parsed >>= tcInferSigma . fst
  return res

-- | We get the type of the given expression by desugaring it and getting the type
-- of the resulting Core expression
getExprTy :: HscEnv -> LHsExpr GhcTc -> IO (Maybe Type)
getExprTy hsc_env expr = fmap CoreUtils.exprType . snd <$> deSugarExpr hsc_env expr

-- | Takes an expression and generates HoleFitCandidates from every subexpression.
getExprFitCands ::
  -- | The general compiler setup
  CompileConfig ->
  -- | The expression to be holed
  EExpr ->
  IO [ExprFitCand]
getExprFitCands cc expr = runGhc (Just libdir) $ do
  -- setSessionDynFlags reads the package database.
  _ <- setSessionDynFlags =<< getSessionDynFlags
  -- If it type checks, we can use the expression
  mb_tcd_context <- justTcExpr cc expr
  let esAndNames =
        case mb_tcd_context of
          Just ((tcd_context, _), wc) ->
            -- We get all the expressions in the program here,
            -- so that we can  pass it along to our custom holeFitPlugin.
            let flat = flattenExpr tcd_context
                -- Vars are already in scope
                nonTriv :: LHsExpr GhcTc -> Bool
                nonTriv (L _ HsVar {}) = False
                -- We don't want more holes
                nonTriv (L _ HsUnboundVar {}) = False
                -- We'll get whatever expression is within the parenthesis
                -- or wrap anyway
                nonTriv (L _ HsPar {}) = False
                nonTriv (L _ HsWrap {}) = False
                nonTriv _ = True
                e_ids (L _ (HsVar _ v)) = Just $ unLoc v
                e_ids _ = Nothing
                -- We remove the ones already present and drop the first one
                -- (since it will be the program itself)
                flat' = filter nonTriv $ tail flat
             in map (\e -> (e, bagToList $ wc_simple wc, mapMaybe e_ids $ flattenExpr e)) flat'
          _ -> []
  hsc_env <- getSession
  -- After we've found the expressions and any ids contained within them, we
  -- need to find their types
  liftIO $
    mapM
      ( \(e, wc, rs) -> do
          ty <- getExprTy hsc_env e
          return $ case ty of
            Nothing -> EFC e emptyBag rs ty
            Just expr_ty -> EFC e (listToBag (relevantCts expr_ty wc)) rs ty
      )
      esAndNames
  where
    -- Taken from TcHoleErrors, which is sadly not exported. Takes a type and
    -- a list of constraints and filters out irrelvant constraints that do not
    -- mention any typve variable in the type.
    relevantCts :: Type -> [Ct] -> [Ct]
    relevantCts expr_ty simples =
      if isEmptyVarSet (fvVarSet expr_fvs')
        then []
        else filter isRelevant simples
      where
        ctFreeVarSet :: Ct -> VarSet
        ctFreeVarSet = fvVarSet . tyCoFVsOfType . ctPred
        expr_fvs' = tyCoFVsOfType expr_ty
        expr_fv_set = fvVarSet expr_fvs'
        anyFVMentioned :: Ct -> Bool
        anyFVMentioned ct =
          not $
            isEmptyVarSet $
              ctFreeVarSet ct `intersectVarSet` expr_fv_set
        -- We filter out those constraints that have no variables (since
        -- they won't be solved by finding a type for the type variable
        -- representing the hole) and also other holes, since we're not
        -- trying to find hole fits for many holes at once.
        isRelevant ct =
          not (isEmptyVarSet (ctFreeVarSet ct))
            && anyFVMentioned ct
            && not (isHoleCt ct)
