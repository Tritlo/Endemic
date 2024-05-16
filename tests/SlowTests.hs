{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Data.Default
import Data.Functor (($>))
import Data.IORef (readIORef, writeIORef)
import Data.List (sort)
import qualified Data.Map as Map
import Data.Maybe (isJust, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import PropR (describeProblem, getExprFitCands)
import PropR.Configuration
import PropR.Diff (applyFixes, fixesToDiffs, getFixBinds, ppDiff)
import PropR.Eval
import PropR.Search
import PropR.Search.Exhaustive
import PropR.Search.PseudoGenetic (pseudoGeneticRepair)
import PropR.Traversals
import PropR.Types
import PropR.Util (logStr, traceOut, traceOutId, withLogLevel)
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit
import TestUtils

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ 
      mkSimpleModuleTest 240_000_000 "Repair BrokenGCD" "tests/cases/BrokenGCD.hs" (Just "gcd'")
    , specialTests
    , tastyFixTests
    , randTests
    , properGenTests
    , genTests
    , exhaustiveTests
    , refinementTests
    , let tccc = (compileConfig tESTCONF) { useSpectrum = 15}
      in mkSimpleModuleTest' (Just $ tESTCONF { compileConfig =  tccc})
         480_000_000 "Repair BrokenGCD" "tests/cases/BrokenGCD.hs" (Just "gcd'")
    ]

runGenRepair :: ProblemDescription -> IO (Set EFix)
runGenRepair desc = runGenMonad tESTGENCONF desc tESTSEED geneticSearchPlusPostprocessing

runGenRepair' :: GeneticConfiguration -> ProblemDescription -> IO (Set EFix)
runGenRepair' gen_conf desc = runGenMonad gen_conf desc tESTSEED geneticSearchPlusPostprocessing

mkGenConfTestEx :: Integer -> TestName -> FilePath -> TestTree
mkGenConfTestEx = mkRepairTest tESTCONF runGenRepair

mkSearchTestExPartial :: SearchAlgorithm -> Integer -> TestName -> FilePath -> TestTree
mkSearchTestExPartial search_conf timeout tag file =
  mkRepairTest' tESTCONF (runRepair search_conf) timeout tag file def {allowMix = True, acceptNew = False}

mkSearchTestEx :: SearchAlgorithm -> Integer -> TestName -> FilePath -> TestTree
mkSearchTestEx search_conf = mkRepairTest tESTCONF (runRepair search_conf)

mkPseudoGenTestEx :: Integer -> TestName -> FilePath -> TestTree
mkPseudoGenTestEx = mkRepairTest tESTCONF (pseudoGeneticRepair def)

tastyFixTests :: TestTree
tastyFixTests =
  testGroup
    "Tasty fix tests"
    [ mkGenConfTestEx 180_000_000 "Repair TastyFix" "tests/cases/TastyFix.hs",
      mkGenConfTestEx 180_000_000 "Repair TastyMix" "tests/cases/TastyMix.hs",
      mkGenConfTestEx 180_000_000 "Repair TastyTwoFix" "tests/cases/TastyTwoFix.hs"
    ]

randTests :: TestTree
randTests =
  testGroup
    "Random search tests"
    [ let conf = Random def {randStopOnResults = True, randIgnoreFailing = True}
       in mkSearchTestExPartial conf 180_000_000 "Repair TastyFix" "tests/cases/TastyFix.hs"
    ]

exhaustiveTests :: TestTree
exhaustiveTests =
  testGroup
    "Exhaustive search tests"
    [ let conf = Exhaustive def {exhStopOnResults = True}
       in mkSearchTestEx conf 180_000_000 "Repair TastyFix" "tests/cases/TastyFix.hs",
      let conf = Exhaustive def {exhStopOnResults = True}
       in mkSearchTestEx conf 180_000_000 "Repair TwoFixes" "tests/cases/TwoFixes.hs"
    ]

properGenTests :: TestTree
properGenTests =
  testGroup
    "Genetic search tests"
    [ mkGenConfTestEx 180_000_000 "Repair TwoFixes" "tests/cases/TwoFixes.hs",
      mkGenConfTestEx 180_000_000 "Repair ThreeFixes" "tests/cases/ThreeFixes.hs",
      -- With all the new fixes, we need to bump the population size
      mkGenConfTestEx 180_000_000 "Repair FourFixes" "tests/cases/FourFixes.hs"
      --mkRepairTest def (runGenRepair' tESTGENCONF {populationSize = 92}) 240_000_000 "Repair FourFixes" "tests/cases/FourFixes.hs"
    ]

genTests :: TestTree
genTests =
  testGroup
    "PseudoGenetic search tests"
    [ mkPseudoGenTestEx 240_000_000 "Repair TwoFixes" "tests/cases/TwoFixes.hs",
      mkPseudoGenTestEx 180_000_000 "Repair ThreeFixes" "tests/cases/ThreeFixes.hs",
      mkPseudoGenTestEx 180_000_000 "Repair FourFixes" "tests/cases/FourFixes.hs"
    ]

-- These all test compilation corner cases
specialTests :: TestTree
specialTests =
  testGroup
    "Special"
    [ mkGenConfTestEx 30_000_000 "Repair UsesDependency" "tests/cases/UsesDependency.hs",
      mkGenConfTestEx 30_000_000 "Repair Operators" "tests/cases/Operators.hs",
      mkGenConfTestEx 30_000_000 "Repair Data" "tests/cases/Data.hs",
      mkGenConfTestEx 180_000_000 "Repair Multi" "tests/cases/Multi.hs",
      mkGenConfTestEx 30_000_000 "Repair DoubleDecl" "tests/cases/DoubleDecl.hs",
      mkGenConfTestEx 60_000_000 "All props pass" "tests/cases/AllPropsPass.hs",
      mkGenConfTestEx 60_000_000 "No props" "tests/cases/NoProps.hs",
      mkRepairTest
        tESTCONF {compileConfig = (compileConfig tESTCONF) {useInterpreted = False}}
        runGenRepair
        60_000_000
        "Non-Interpreted"
        "tests/cases/LoopBreaker.hs",
      mkRepairTest
        tESTCONF {compileConfig = (compileConfig tESTCONF) {useInterpreted = True, parChecks = False}}
        runGenRepair
        120_000_000
        "Interpreted Non-Par"
        "tests/cases/LoopBreaker.hs",
      mkRepairTest
        tESTCONF {compileConfig = (compileConfig tESTCONF) {useInterpreted = True, parChecks = True}}
        runGenRepair
        240_000_000
        "Interpreted Par"
        "tests/cases/LoopBreaker.hs",
      mkRepairTest
        tESTCONF {compileConfig = (compileConfig tESTCONF) {allowFunctionFits = True}}
        runGenRepair
        60_000_000
        "Wrap fits"
        "tests/cases/Wrap.hs",
      mkRepairTest'
        tESTCONF
        runGenRepair
        60_000_000
        "Ambiguous fits"
        "tests/cases/AmbiguousTypeVariables.hs"
        def {allowMix = True},
      mkRepairTest'
        tESTCONF {compileConfig = (compileConfig tESTCONF) {excludeTargets = ["brokenPair"]}}
        runGenRepair
        5_000_000
        "Exclude targets"
        "tests/cases/ThreeFixes.hs"
        def {mb_expected = Just []},
      mkGenConfTestEx 60_000_000 "ExprWhere fits" "tests/cases/ExprWhere.hs",
      mkGenConfTestEx 60_000_000 "DefaultingFixes" "tests/cases/DefaultingFixes.hs",
      mkGenConfTestEx 60_000_000 "Issue 88" "tests/cases/Issue88.hs",
      mkRepairTest
        tESTCONF {compileConfig = (compileConfig tESTCONF) {allowFunctionFits = True}}
        runGenRepair
        60_000_000
        "Issue 87 with function fits"
        "tests/cases/Issue87.hs",
      mkRepairTest
        tESTCONF {compileConfig = (compileConfig tESTCONF) {allowFunctionFits = False}}
        runGenRepair
        60_000_000
        "Issue 87 w/o function fits"
        "tests/cases/Issue87.hs"
    ]

refinementTests :: TestTree
refinementTests =
  testGroup
    "Refinments"
    [ mkRepairTest'
        ( tESTCONF
            { compileConfig = (compileConfig tESTCONF) {holeLvl = 2},
              logConfig = (logConfig tESTCONF) {logLoc = True}
            }
        )
        runGenRepair
        240_000_000
        "Refinement test"
        "tests/cases/SimpleRefinement.hs"
        def {allowMix = True}
    ]

main :: IO ()
main = defaultMain tests
