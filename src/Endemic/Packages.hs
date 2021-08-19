{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Endemic.Packages where

import Control.Arrow (first, (&&&), (***))
import Control.Monad (join)
import Data.IORef
import Data.List (nub, partition, sort)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Distribution.ModuleName
import Distribution.PackageDescription
import Distribution.PackageDescription.Configuration
import Distribution.PackageDescription.Parsec
import Distribution.Pretty (prettyShow)
import Distribution.Simple
import Distribution.Simple.Build
import Distribution.Simple.Configure
import Distribution.Simple.Program
import Distribution.Simple.Program.Db
import Distribution.Types.GenericPackageDescription
import Distribution.Types.LocalBuildInfo
import Distribution.Verbosity
import Endemic
import Endemic.Diff (fixesToDiffs)
import Endemic.Util
import System.Directory
import System.FilePath

-- | Finds the cabal file in the given file, errors if there's no such file or
-- multiple files.
findCabalFile :: IO FilePath
findCabalFile = do
  mb_cabal_file <- filter isCabal <$> listDirectory "."
  case mb_cabal_file of
    (_ : _ : _) -> error $ "Multiple cabal files found!"
    [] -> error $ "No cabal file found!"
    [cabal_file] -> makeAbsolute cabal_file
  where
    rev_cabal = reverse ".cabal"
    isCabal = (rev_cabal ==) . take (length rev_cabal) . reverse

repairPackage :: Configuration -> FilePath -> IO [String]
repairPackage conf@Conf {..} target_dir = withCurrentDirectory target_dir $ do
  cabal_file <- findCabalFile
  logStr TRACE $ "Using cabal file " ++ cabal_file
  g_desc <- readGenericPackageDescription silent cabal_file
  --   lbi_res <- newIORef Nothing
  --   let hooks =
  --         simpleUserHooks
  --           { postBuild = \_ _ _ lbi ->
  --               writeIORef lbi_res (Just lbi)
  --           }
  let p_desc@PackageDescription {..} = flattenPackageDescription g_desc
      PackageIdentifier {pkgName = pname} = package
      testModName TestSuite {testInterface = TestSuiteExeV10 _ fp, ..} =
        Just
          (testBuildInfo, addHsSourceDir testBuildInfo fp)
      testModName TestSuite {testInterface = TestSuiteLibV09 _ mname, ..} =
        Just
          (testBuildInfo, addHsSourceDir testBuildInfo $ toFilePath mname <.> ".hs")
      testModName _ = Nothing
      addHsSourceDir BuildInfo {..} = (dir </>)
        where
          dir = case hsSourceDirs of
            [d] -> d
            _ -> error "Multiple source dirs not supported!"
  let found_mods = mapMaybe testModName testSuites
      non_local_deps BuildInfo {..} = partition (\(Dependency dname _ _) -> dname /= pname) targetBuildDepends

  found_tests <- mapM (\(b, p) -> (b,) <$> makeAbsolute p) found_mods
  logStr TRACE $ "Found test modules:"
  mapM_ (logStr DEBUG . show . snd) found_tests
  logStr TRACE $ "Non local deps"
  let depToName = (\(Dependency dname _ _) -> unPackageName dname)
      packages =
        map
          ( join (***) (map depToName)
              . non_local_deps
              . fst
          )
          found_tests
      m_w_pkgs = zipWith (\(b, m) p -> (m, b, p)) found_tests packages
  case m_w_pkgs of
    [] -> error "No repairable testsuite found!"
    -- TODO: Add a test-suite argument to disambiguate when there are multiple
    -- testsuites:
    (_ : _ : _) -> error "Multiple repairable testsuites found!"
    [(testMod, buildInfo, (non_lcl_pkgs, lcl_pkgs))] -> do
      logStr DEBUG testMod
      logStr DEBUG $ show packages
      -- TODO: Add the source dirs from the library being fixed, and the
      -- pacakges required by the library to be fixed.
      let (lib_dirs, lib_pkgs) =
            if null lcl_pkgs
              then ([], [])
              else case library of
                Nothing -> ([], [])
                Just Library {..} ->
                  ( hsSourceDirs libBuildInfo,
                    map depToName $ fst $ non_local_deps libBuildInfo
                  )
          test_dirs = hsSourceDirs buildInfo
          dirs = test_dirs ++ lib_dirs
          pkgs = nub $ sort $ non_lcl_pkgs ++ lib_pkgs
      abs_dirs <- mapM makeAbsolute dirs
      let conf' =
            conf
              { compileConfig =
                  compileConfig
                    { packages = pkgs,
                      modBase = abs_dirs
                    }
              }
      -- TODO: We could instead incorporate the module vs package into
      -- describe problem instead
      logStr DEBUG $ show conf'
      describeProblem conf' testMod
        >>= \case
          Just desc -> fixesToDiffs desc <$> runRepair searchAlgorithm desc
          Nothing -> logStr INFO "All props are passing, nothing to repair." >> return []
