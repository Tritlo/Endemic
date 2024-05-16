{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module PropR.Configuration.Types where

import Data.Aeson
import Data.Default
import Data.Maybe (fromMaybe)
import Data.Time.Format
import Data.Time.LocalTime
import Deriving.Aeson
import GHC (ParsedModule, TypecheckedModule (TypecheckedModule))
import PropR.Configuration.Materializeable
import PropR.Search.Exhaustive.Configuration
import PropR.Search.Genetic.Configuration
import PropR.Search.PseudoGenetic.Configuration
import PropR.Search.Random.Configuration
import PropR.Types
import System.FilePath ((</>))

-- | Logging configuration
data LogConfig = LogConf
  { logLoc :: Bool,
    logLevel :: LogLevel,
    logTimestamp :: Bool,
    logFile :: Maybe String
  }
  deriving (Show, Eq, Generic)
  deriving
    (FromJSON, ToJSON)
    via CustomJSON '[FieldLabelModifier '[CamelToSnake], RejectUnknownFields] LogConfig

-- We need these as well

deriving instance Generic TimeZone

deriving instance ToJSON TimeZone

deriving instance FromJSON TimeZone

deriving instance Generic TimeLocale

deriving instance ToJSON TimeLocale

deriving instance FromJSON TimeLocale

-- | A configuration contains all the settings
data Configuration = Conf
  { compileConfig :: CompileConfig,
    outputConfig :: OutputConfig,
    searchAlgorithm :: SearchAlgorithm,
    logConfig :: LogConfig,
    randomSeed :: Maybe Int
  }
  deriving (Show, Eq, Generic)
  deriving
    (FromJSON, ToJSON)
    via CustomJSON '[FieldLabelModifier '[CamelToSnake], RejectUnknownFields] Configuration

instance Default Configuration where
  def =
    Conf
      { compileConfig = def,
        outputConfig = def,
        searchAlgorithm = def,
        logConfig = def,
        randomSeed = Nothing
      }

-- An unmaterialied config, with possible gaps in it. This is then
-- "materialized" by filling in the gaps
instance Materializeable Configuration where
  data Unmaterialized Configuration = UmConf
    { -- Configuration for the compilation and repair of programs
      umCompileConfig :: Maybe (Unmaterialized CompileConfig),
      umOutputConfig :: Maybe (Unmaterialized OutputConfig),
      umLogConfig :: Maybe (Unmaterialized LogConfig),
      -- Configuration for the genetic repair algorithm.
      --  Left if we're to use the PseudoGenConf, Right otherwise.
      -- Defaults to a Genetic Configuration.
      umSearchAlgorithm :: Maybe (Unmaterialized SearchAlgorithm),
      umRandomSeed :: Maybe Int
    }
    deriving (Show, Eq, Generic)
    deriving
      (FromJSON, ToJSON)
      via CustomJSON
            '[ OmitNothingFields,
               RejectUnknownFields,
               FieldLabelModifier '[StripPrefix "um", CamelToSnake]
             ]
            (Unmaterialized Configuration)

  conjure = UmConf n n n n n
    where
      n = Nothing

  override conf Nothing = conf
  override Conf {..} (Just UmConf {..}) =
    Conf
      { compileConfig = override compileConfig umCompileConfig,
        outputConfig = override outputConfig umOutputConfig,
        logConfig = override logConfig umLogConfig,
        searchAlgorithm = override searchAlgorithm umSearchAlgorithm,
        randomSeed = mbOverride randomSeed umRandomSeed
      }

-- | Holds the primary switch wether we want to use Genetic Search or BFS,
-- and the assoicated configuration
data SearchAlgorithm
  = Genetic GeneticConfiguration
  | PseudoGenetic PseudoGenConf
  | Random RandomConf
  | Exhaustive ExhaustiveConf
  deriving (Show, Eq, Generic)
  deriving
    (FromJSON, ToJSON)
    via CustomJSON '[FieldLabelModifier '[CamelToSnake], RejectUnknownFields] SearchAlgorithm

instance Default SearchAlgorithm where
  def = Genetic def

instance Materializeable SearchAlgorithm where
  data Unmaterialized SearchAlgorithm
    = UmGenetic (Unmaterialized GeneticConfiguration)
    | UmPseudoGenetic (Unmaterialized PseudoGenConf)
    | UmRandom (Unmaterialized RandomConf)
    | UmExhaustive (Unmaterialized ExhaustiveConf)
    deriving (Show, Eq, Generic)
    deriving
      (FromJSON, ToJSON)
      via CustomJSON
            '[ OmitNothingFields,
               RejectUnknownFields,
               ConstructorTagModifier '[StripPrefix "Um"],
               FieldLabelModifier '[StripPrefix "um", CamelToSnake]
             ]
            (Unmaterialized SearchAlgorithm)

  conjure = UmGenetic conjure

  override c Nothing = c
  override (Genetic conf) (Just (UmGenetic gc)) =
    Genetic $ override conf (Just gc)
  override (PseudoGenetic conf) (Just (UmPseudoGenetic pgc)) =
    PseudoGenetic $ override conf (Just pgc)
  override (Random conf) (Just (UmRandom pgc)) =
    Random $ override conf (Just pgc)
  override (Exhaustive conf) (Just (UmExhaustive pgc)) =
    Exhaustive $ override conf (Just pgc)
  override _ (Just (UmPseudoGenetic psc)) =
    PseudoGenetic $ materialize $ Just psc
  override _ (Just (UmGenetic gc)) =
    Genetic $ materialize $ Just gc
  override _ (Just (UmRandom r)) =
    Random $ materialize $ Just r
  override _ (Just (UmExhaustive e)) =
    Exhaustive $ materialize $ Just e

-- | Configuration for the output
data OutputConfig = OutputConf
  { -- | The users locale, for complete reproduction
    locale :: Maybe TimeLocale,
    -- | Which directory to write the patches to.
    directory :: FilePath,
    -- | Whether to overwrite previous patches
    overwrite :: Bool,
    -- | Whether to save the patches
    savePatches :: Bool
  }
  deriving (Show, Eq, Generic)
  deriving
    (FromJSON, ToJSON)
    via CustomJSON '[FieldLabelModifier '[CamelToSnake], RejectUnknownFields] OutputConfig

instance Default OutputConfig where
  def =
    OutputConf
      { locale = Nothing,
        directory = "./output-patches-",
        overwrite = False,
        savePatches = True
      }

instance Materializeable OutputConfig where
  data Unmaterialized OutputConfig = UmOutConf
    { umLocale :: Maybe TimeLocale,
      umDirectory :: Maybe FilePath,
      umOverwrite :: Maybe Bool,
      umSavePatches :: Maybe Bool
    }
    deriving (Show, Eq, Generic)
    deriving
      (FromJSON, ToJSON)
      via CustomJSON '[OmitNothingFields, RejectUnknownFields, FieldLabelModifier '[StripPrefix "um", CamelToSnake]] (Unmaterialized OutputConfig)

  conjure = UmOutConf Nothing Nothing Nothing Nothing

  override c Nothing = c
  override OutputConf {..} (Just UmOutConf {..}) =
    OutputConf
      { locale = mbOverride locale umLocale,
        directory = fromMaybe directory umDirectory,
        overwrite = fromMaybe overwrite umOverwrite,
        savePatches = fromMaybe savePatches umSavePatches
      }

instance Materializeable CompileConfig where
  data Unmaterialized CompileConfig = UmCompConf
    { umImportStmts :: Maybe [String],
      umPackages :: Maybe [String],
      umExtensions:: Maybe [String],
      umHoleLvl :: Maybe Int,
      umHoleDepth :: Maybe Int,
      umUnfoldTastyTests :: Maybe Bool,
      umModBase :: Maybe [FilePath],
      umQcChecks :: Maybe Int,
      umAdditionalTargets :: Maybe [FilePath],
      umTempDirBase :: Maybe FilePath,
      umRandomizeHpcDir :: Maybe Bool,
      umRandomizeHiDir :: Maybe Bool,
      umParChecks :: Maybe Bool,
      umUseInterpreted :: Maybe Bool,
      umTimeout :: Maybe Integer,
      umNoTimeout :: Maybe Bool,
      umPrecomputeFixes :: Maybe Bool,
      umKeepLoopingFixes :: Maybe Bool,
      umAllowFunctionFits :: Maybe Bool,
      umExcludeTargets :: Maybe [String],
      umExtendDefaults :: Maybe Bool,
      umFilterIncorrectFixes :: Maybe Bool,
      umUseSpectrum :: Maybe Int,
      umGhcFlags :: Maybe [String]
    }
    deriving (Show, Eq, Generic)
    deriving
      (FromJSON, ToJSON)
      via CustomJSON '[OmitNothingFields, RejectUnknownFields, FieldLabelModifier '[StripPrefix "um", CamelToSnake]] (Unmaterialized CompileConfig)

  conjure =
    UmCompConf
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing
      Nothing

  override c Nothing = c
  override CompConf {..} (Just UmCompConf {..}) =
    CompConf
      { importStmts = fromMaybe importStmts umImportStmts,
        packages = fromMaybe packages umPackages,
        extensions = fromMaybe extensions umExtensions,
        holeLvl = fromMaybe holeLvl umHoleLvl,
        holeDepth = fromMaybe holeDepth umHoleDepth,
        modBase = fromMaybe modBase umModBase,
        qcChecks = fromMaybe qcChecks umQcChecks,
        unfoldTastyTests = fromMaybe unfoldTastyTests umUnfoldTastyTests,
        additionalTargets = fromMaybe additionalTargets umAdditionalTargets,
        tempDirBase = fromMaybe tempDirBase umTempDirBase,
        randomizeHpcDir = fromMaybe randomizeHpcDir umRandomizeHpcDir,
        randomizeHiDir = fromMaybe randomizeHiDir umRandomizeHiDir,
        parChecks = fromMaybe parChecks umParChecks,
        useInterpreted = fromMaybe useInterpreted umUseInterpreted,
        timeout = fromMaybe timeout umTimeout,
        noTimeout = fromMaybe noTimeout umNoTimeout,
        precomputeFixes = fromMaybe precomputeFixes umPrecomputeFixes,
        keepLoopingFixes = fromMaybe keepLoopingFixes umKeepLoopingFixes,
        allowFunctionFits = fromMaybe allowFunctionFits umAllowFunctionFits,
        excludeTargets = fromMaybe excludeTargets umExcludeTargets,
        extendDefaults = fromMaybe extendDefaults umExtendDefaults,
        filterIncorrectFixes = fromMaybe filterIncorrectFixes umFilterIncorrectFixes,
        useSpectrum = fromMaybe useSpectrum umUseSpectrum,
        ghcFlags = fromMaybe ghcFlags umGhcFlags
      }

-- | Configuration for the compilation itself
data CompileConfig = CompConf
  { -- | a list of imports required/wanted for the compilation
    importStmts :: [String],
    -- | a list of packages used for the compilation
    packages :: [String],
    -- | a list of extensions used for the compilation
    extensions :: [String],
    -- | Base path to use for modules, if available
    modBase :: [FilePath],
    -- | How many QuickCheck checks are run before accepting as true,
    -- defaults to 1 000
    qcChecks :: Int,
    -- | Any additional targets to include
    additionalTargets :: [FilePath],
    -- | The "level" and "depth" of the holes, see general notes on this.
    -- holeLvl determines how many additional holes a hole fit can have.
    -- Note: a holeLvl > 0 means that we must have a holeDepth of > 0,
    -- since we *must* fill all holes.
    holeLvl :: Int,
    -- |  Hole depth determines how many levels of additional holes we allow.
    -- I.e. we have holeLvl = 1 then and x :: a, y :: a -> a in scope, a hole
    -- _ :: a would give the following:
    -- + holeDepth 0 would give x :: a,
    -- + holeDepth 1 would give x :: a, (y x) :: a
    -- + holeDepth 2 would give x :: a, (y x) :: a, and (y (y x)) :: a etc.
    holeDepth :: Int,
    -- | Whether to unfold tasty TestTrees into multiple tests
    unfoldTastyTests :: Bool,
    -- | Where to put files generated during the run. We do a lot
    -- of file system accesses, so this should be a fast directory.
    tempDirBase :: FilePath,
    -- | Whether or not to use parallelisation
    parChecks :: Bool,
    -- | Whether to randomize the HPC directory when parChecks is enabled. Can
    -- help with congestion on highly parallell systems.
    -- Use this if you're getting crashes saying:
    -- "Exception: .hpc/FourFixes.mix: openFile: resource busy (file is locked)"
    randomizeHpcDir :: Bool,
    -- | Whether to randomize the directory where .hi files are placed when
    -- parChecks is enabled. Similar to randomizeHpcDir, but can cause a
    -- bigger slowdown.
    -- Use this if you're getting crashes saying:
    -- "Exception: tests/cases/ThreeFixes.hi: openBinaryFile: resource busy (file is locked)"
    randomizeHiDir :: Bool,
    -- | Whether or not to use bytecode or to just interpret the resulting code.
    -- Usuallly safe to set to true, except when Core-to-Core plugins are involved.
    useInterpreted :: Bool,
    -- | Set the timeout in microseconds for each heck, after which we assume the
    -- check is in an infinte loop.
    timeout :: Integer,
    -- | If no_timeout is set, we ignore the timeout parameter and disable
    -- timeouts.
    noTimeout :: Bool,
    -- | Whether or not we're allowed to precompute the fixes at the beginning.
    -- Better in most cases, but can slow down if we have big programs and aren't
    -- considering all of it (e.t. random search). Might interfere with
    -- function fits and refinement fits.
    precomputeFixes :: Bool,
    -- | Whether or not we keep looping fits in the precomputed fixes. Defaults
    -- to off, but maybe it's needed in conjunction with something else.
    keepLoopingFixes :: Bool,
    -- | Whether to allow fits of the type `(_ x)` where x is some identifier
    -- in the code. Makes the search space bigger, but finds more fits.
    allowFunctionFits :: Bool,
    -- | Targets to exclude from repairing. Could be things like examples or
    -- test helpers that we don't want to change.
    excludeTargets :: [String],
    -- | Extend defaults allows us to use GHC's extended defaulting during
    -- hole-fit generation. Only works if we're not relying too much on
    -- type-defaulting, since the types will not be defaulted during checking.
    extendDefaults :: Bool,
    -- | With filter incorrect fixes set, we try to recover from incorrect fixes
    -- by checking the fixes one by one and seeing which ones compile. Without
    -- this flag, we simply fail on incorrect fixes.
    filterIncorrectFixes :: Bool,
    -- | Use spectrum turns on using spectral analysis to try to distinguish
    -- the good parts and bad parts by using the difference between failing
    -- and successful properties. The number indicates how many of the
    -- top suspicious candidates to consider.
    useSpectrum :: Int,
    -- | Flags passed to the internal GHC during initalization. Useful for
    -- stuff like -package, -package-db
    ghcFlags :: [String]
  }
  deriving (Show, Eq, Generic)
  deriving
    (FromJSON, ToJSON)
    via CustomJSON '[FieldLabelModifier '[CamelToSnake], RejectUnknownFields] CompileConfig

instance Default CompileConfig where
  def =
    CompConf
      { holeLvl = 0,
        holeDepth = 1,
        packages = ["base"],
        extensions = [],
        importStmts = [],
        unfoldTastyTests = True,
        modBase = [],
        qcChecks = 1000,
        additionalTargets = [],
        tempDirBase = "." </> "temp_dir",
        parChecks = True,
        randomizeHpcDir = True,
        randomizeHiDir = True,
        useInterpreted = True,
        timeout = 1_000_000,
        noTimeout = False,
        precomputeFixes = True,
        keepLoopingFixes = False,
        allowFunctionFits = True,
        excludeTargets = [],
        extendDefaults = False,
        filterIncorrectFixes = True,
        useSpectrum = 0,
        ghcFlags = []
      }

instance Default LogConfig where
  def = LogConf {logLoc = False, logLevel = WARN, logFile = Nothing, logTimestamp = True}

instance Materializeable LogConfig where
  data Unmaterialized LogConfig = UmLogConf
    { umLogLoc :: Maybe Bool,
      umLogLevel :: Maybe LogLevel,
      umLogTimestamp :: Maybe Bool,
      umLogFile :: Maybe String
    }
    deriving (Show, Eq, Generic)
    deriving
      (FromJSON, ToJSON)
      via CustomJSON '[OmitNothingFields, RejectUnknownFields, FieldLabelModifier '[StripPrefix "um", CamelToSnake]] (Unmaterialized LogConfig)

  conjure = UmLogConf Nothing Nothing Nothing Nothing

  override c Nothing = c
  override LogConf {..} (Just UmLogConf {..}) =
    LogConf
      { logLoc = fromMaybe logLoc umLogLoc,
        logLevel = fromMaybe logLevel umLogLevel,
        logTimestamp = fromMaybe logTimestamp umLogTimestamp,
        logFile = mbOverride logFile umLogFile
      }

data AdditionalConf = AddConf
  { -- | If assumeNoLoops is true, we check the fixes assuming that there
    -- are no loops in the generated code. Beware! Will die with a message
    -- saying Alarm Clock in case there were loops.
    assumeNoLoops :: Bool
  }

instance Default AdditionalConf where
  def = AddConf {assumeNoLoops = True}

-- | The Problem Description is generated at runtime, descriping a particular
-- program to fix.
data ProblemDescription = ProbDesc
  { progProblem :: EProblem,
    exprFitCands :: [ExprFitCand],
    compConf :: CompileConfig,
    addConf :: AdditionalConf,
    -- | The typechecked module, if available
    probModule :: Maybe TypecheckedModule,
    -- | Fix candidates, if available
    initialFixes :: Maybe [EFix]
  }

setProg :: ProblemDescription -> EProg -> ProblemDescription
setProg desc@ProbDesc {progProblem = pp} prog = desc {progProblem = pp {e_prog = prog}}

-- Inline version of setProg
(<~) :: ProblemDescription -> EProg -> ProblemDescription
(<~) = setProg
