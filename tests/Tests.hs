{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Arrow
import Data.Bits (finiteBitSize)
import Data.Default
import Data.Dynamic (Dynamic, fromDynamic)
import Data.List (find, sort)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, isJust, mapMaybe)
import Data.Tree
import Data.Tuple (swap)
import PropR.Configuration
import PropR.Diff
import PropR.Eval
import PropR.Repair
import PropR.Traversals
import PropR.Types
import PropR.Util
import PropR.Packages
import GHC (GhcPs, LHsExpr, noExtField, tm_parsed_module, noAnn, reLoc, getLocA)
import GHC.Plugins (GenLocated (L), getLoc, unLoc)
import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import TestUtils
import Trace.Hpc.Mix
import Data.Char

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ utilTests,
      repairTests,
      failingPropsTests,
      counterExampleTests,
      traceTests,
      moduleTests,
      sanctifyTests,
      packageTests
    ]

-- Helpers
compileParsedCheck :: HasCallStack => CompileConfig -> EExpr -> IO Dynamic
compileParsedCheck cc expr =
  runGhc' (cc {holeLvl = 0}) $
    dynCompileParsedExpr `reportOnError` expr

runJustParseExpr :: CompileConfig -> RExpr -> IO (LHsExpr GhcPs)
runJustParseExpr cc str = runGhcWithCleanup cc $ justParseExpr cc str

prop_insertAt :: Eq a => Int -> a -> [a] -> Property
prop_insertAt n a as = abs n < length as ==> insertAt n' a as !! n' == a
  where
    n' = n `mod` length as

utilTests :: TestTree
utilTests =
  testProperties
    "Utils"
    [ ("dropPrefix", property prop_dropsPrefix),
      ("startsWith", property prop_startsWith),
      ("insertAt", property (prop_insertAt @Integer))
    ]

repairTests =
  testGroup
    "Repair"
    [ -- A simple tests to see if we can repair (foldl (-) 0) to (foldl (+) 0)
      -- in a reasonable amount of time (here 10s)
      localOption (mkTimeout 30_000_000) $
        testCase "Basic Repair `foldl (-) 0`" $ do
          let cc =
                (compileConfig tESTCONF)
                  { packages = ["base", "process", "QuickCheck"],
                    importStmts = ["import Prelude hiding (id, ($), ($!), asTypeOf)"]
                  }
              ty = "[Int] -> Int"
              wrong_prog = "(foldl (-) 0)"
              props = ["prop_isSum f xs = f xs == sum xs"]
              context =
                [ "zero = 0 :: Int",
                  "one = 1 :: Int",
                  "add = (+) :: Int -> Int -> Int"
                ]
              expected = "((foldl (+) 0)) :: [Int] -> Int"
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp@EProb {..} <- translate cc rp
          fixes <- repair cc tp
          let fixProgs = map (eProgToEProgFix . applyFixToEProg e_prog) fixes
          expected `elem` concatMap (map (trim . showUnsafe)) fixProgs @? "Expected repair not found in fixes",
      localOption (mkTimeout 20_000_000) $
        testCase "GetExprCands finds important candidates" $ do
          let wrong_prog =
                unlines
                  [ "let { gcd' 0 b = gcd' 0 b",
                    "    ; gcd' a b | b == 0 = a",
                    "    ; gcd' a b = if (a > b) then gcd' (a-b) b else gcd' a (b-a)",
                    "    ; a_constant_string = \"hello, world!\"}",
                    "     in gcd'"
                  ]
              expected =
                ["EFC {\"hello, world!\"}",
                 "EFC {0}",
                 "EFC {(gcd' 0 b)}",
                 "EFC {(gcd' 0)}",
                 "EFC {0}",
                 "EFC {0}",
                 "EFC {(b == 0)}",
                 "EFC {((==) b)}",
                 "EFC {0}",
                 "EFC {0}",
                 "EFC {(if (a > b) then gcd' (a - b) b else gcd' a (b - a))}",
                 "EFC {(a > b)}",
                 "EFC {((>) a)}",
                 "EFC {(gcd' (a - b) b)}",
                 "EFC {(gcd' (a - b))}",
                 "EFC {(a - b)}",
                 "EFC {((-) a)}",
                 "EFC {(gcd' a (b - a))}",
                 "EFC {(gcd' a)}",
                 "EFC {(b - a)}",
                 "EFC {((-) b)}"]

              no_ff = (compileConfig tESTCONF) {allowFunctionFits = False}
              -- TODO 9.8: these identifiers shouldn't really be there.
              remove_extra_space = unwords . words . unlines . lines
              remove_ids [] = []
              remove_ids s | (b,_:e) <- span (/= '_') s,
                             e' <- dropWhile isAlphaNum e
                             = (b ++ remove_ids e')
              remove_ids s = s
          expr_cands <- runJustParseExpr (no_ff) wrong_prog
                          >>= (runGhc' (no_ff) . getExprFitCands . Left)
          map (remove_ids . remove_extra_space . showUnsafe) expr_cands @?= expected,
      localOption (mkTimeout 60_000_000) $
        testCase "Repair `gcd'` with gcd" $ do
          let props =
                [ "prop_1 f = f 0 55 == 55",
                  "prop_2 f = f 1071 1029 == 21"
                ]
              ty = "Int -> Int -> Int"
              wrong_prog =
                unlines
                  [ "let { gcd' 0 b = gcd' 0 b",
                    "    ; gcd' a b | b == 0 = a",
                    "    ; gcd' a b = if (a > b) then gcd' (a-b) b else gcd' a (b-a)}",
                    "     in gcd'"
                  ]
              context = []
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          fixes <- map (trim . showUnsafe) <$> (translate (compileConfig tESTCONF) rp >>= repair (compileConfig tESTCONF))
          not (null fixes) @? "No fix found"
    ]

failingPropsTests =
  testGroup
    "Failing props"
    [ localOption (mkTimeout 15_000_000) $
        testCase "Failing props for gcd" $ do
          let props :: [String]
              props =
                [ "prop_1 f = f 0 55 == 55",
                  "prop_2 f = f 1071 1029 == 21"
                ]
              ty = "Int -> Int -> Int"
              wrong_prog =
                unlines
                  [ "let { gcd' 0 b = gcd' 0 b",
                    "    ; gcd' a b | b == 0 = a",
                    "    ; gcd' a b = if (a > b) then gcd' (a-b) b else gcd' a (b-a)}",
                    "     in gcd'"
                  ]
              context = []
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp <- translate (compileConfig tESTCONF) rp
          failed_props <- failingProps (compileConfig tESTCONF) tp
          -- Only the first prop should be failing (due to an infinite loop)
          map showUnsafe failed_props @?= [head props],
      localOption (mkTimeout 10_000_000) $
        testCase "Only one failing prop" $ do
          let cc =
                (compileConfig tESTCONF)
                  { packages = ["base", "process", "QuickCheck"],
                    importStmts = ["import Prelude hiding (id, ($), ($!), asTypeOf)"]
                  }
              ty = "[Int] -> Int"
              wrong_prog = "(foldl (-) 0)"
              props = ["prop_isSum f xs = f xs == sum xs"]
              context =
                [ "zero = 0 :: Int",
                  "one = 1 :: Int",
                  "add = (+) :: Int -> Int -> Int"
                ]
              expected = "((foldl (+) 0)) :: [Int] -> Int"
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp <- translate cc rp
          failed_props <- failingProps cc tp
          map showUnsafe failed_props @?= props,
      localOption (mkTimeout 30_000_000) $
        testCase "Two failing TastyProps" $ do
          Just desc@ProbDesc {..} <- describeProblem tESTCONF "tests/cases/TastyTwoFix.hs"
          failed_props <- failingProps compConf progProblem
          length failed_props @?= 2
    ]

counterExampleTests =
  testGroup
    "Counter Examples"
    [ localOption (mkTimeout 10_000_000) $
        testCase "Only one counter example" $ do
          let cc =
                (compileConfig tESTCONF)
                  { packages = ["base", "process", "QuickCheck"],
                    importStmts = ["import Prelude hiding (id, ($), ($!), asTypeOf)"]
                  }
              ty = "[Int] -> Int"
              wrong_prog = "(foldl (-) 0)"
              props = ["prop_isSum f xs = f xs == sum xs"]
              context = []
              expected = "((foldl (+) 0)) :: [Int] -> Int"
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp <- translate cc rp
          [failed_prop] <- failingProps cc tp
          Just [counter_example] <- propCounterExample cc tp failed_prop
          let expr = "(foldl (-) 0) " ++ counter_example ++ " == sum " ++ counter_example
          res <- runJustParseExpr cc expr >>= compileParsedCheck cc
          case fromDynamic @Bool res of
            Just v -> not v @? "Counter Example is not a counter example!"
            Nothing -> error "Incorrect type!!",
      localOption (mkTimeout 10_000_000) $
        testCase "Multiple examples" $ do
          let cc =
                (compileConfig tESTCONF)
                  { packages = ["base", "process", "QuickCheck"],
                    importStmts = ["import Prelude hiding (id, ($), ($!), asTypeOf)"]
                  }
              ty = "Int -> Int -> Int"
              wrong_prog = "(-)"
              props = ["prop_isPlus f a b = f a b == (a + b)"]
              context = []
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp <- translate cc rp
          [failed_prop] <- failingProps cc tp
          Just counter_example_args <- propCounterExample cc tp failed_prop
          let arg_str = unwords counter_example_args
              expr = "(-) " ++ arg_str ++ " == (+) " ++ arg_str
          res <- runJustParseExpr cc expr >>= compileParsedCheck cc
          case fromDynamic @Bool res of
            Just v -> not v @? "Counter Example is not a counter example!"
            Nothing -> error "Incorrect type!!",
      localOption (mkTimeout 15_000_000) $
        testCase "No args loop fail" $ do
          let cc = (compileConfig tESTCONF)
              props :: [String]
              props =
                [ "prop_1 f = f 0 55 == 55",
                  "prop_2 f = f 1071 1029 == 21"
                ]
              ty = "Int -> Int -> Int"
              wrong_prog =
                unlines
                  [ "let { gcd' 0 b = gcd' 0 b",
                    "    ; gcd' a b | b == 0 = a",
                    "    ; gcd' a b = if (a > b) then gcd' (a-b) b else gcd' a (b-a)}",
                    "     in gcd'"
                  ]
              context = []
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp <- translate cc rp
          [failed_prop] <- failingProps cc tp
          -- Only the first prop should be failing (due to an infinite loop)
          showUnsafe failed_prop @?= head props
          Just counter_example_args <- propCounterExample cc tp failed_prop
          null counter_example_args @? "The counter example should not have any arguments!"
    ]

traceTests =
  testGroup
    "Trace tests"
    [ localOption (mkTimeout 10_000_000) $
        testCase "Trace foldl" $ do
          let cc = (compileConfig tESTCONF)
              ty = "[Int] -> Int"
              wrong_prog = "(foldl (-) 0)"
              props = ["prop_isSum f xs = f xs == sum xs"]
              context = []
              expected = "((foldl (+) 0)) :: [Int] -> Int"
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp@EProb {..} <- translate cc rp
          [failed_prop] <- failingProps cc tp
          Just counter_example <- propCounterExample cc tp failed_prop
          let eprog_fix = eProgToEProgFix e_prog
          Just [(texp, Node {subForest = [tree@Node {rootLabel = (tl, tname)}]})] <-
            traceTarget cc tp eprog_fix failed_prop counter_example
          expr <- runJustParseExpr cc wrong_prog
          showUnsafe expr @?= showUnsafe texp
          all ((== 1) . snd) (concatMap snd $ flatten tree) @? "All subexpressions should be touched only once!",
      localOption (mkTimeout 30_000_000) $
        testCase "Trace finds loop" $ do
          let cc = (compileConfig tESTCONF)
              props :: [String]
              props =
                [ "prop_1 f = f 0 55 == 55",
                  "prop_2 f = f 1071 1029 == 21"
                ]
              ty = "Int -> Int -> Int"
              wrong_prog =
                unlines
                  [ "let { gcd' 0 b = gcd' 0 b",
                    "    ; gcd' a b | b == 0 = a",
                    "    ; gcd' a b = if (a > b) then gcd' (a-b) b else gcd' a (b-a)}",
                    "     in gcd'"
                  ]
              context = []
              rp =
                RProb
                  { r_target = "",
                    r_ctxt = context,
                    r_ty = ty,
                    r_prog = wrong_prog,
                    r_props = props
                  }
          setSeedGenSeed tESTSEED
          tp@EProb {..} <- translate cc rp
          [failed_prop] <- failingProps cc tp
          Just counter_example_args <- propCounterExample cc tp failed_prop
          -- We generate the trace
          let [(_, e_ty, e_prog')] = e_prog
              prog_at_ty = progAtTy e_prog' e_ty
              eprog_fix = eProgToEProgFix $ applyFixToEProg e_prog mempty
          Just [(texp, res)] <- traceTarget cc tp eprog_fix failed_prop counter_example_args
          let eMap = Map.fromList $ map (getLocA &&& showUnsafe) $ flattenExpr texp
              trc = map (\(s, r) -> (eMap Map.!? s, r, maximum $ map snd r)) $ flatten res
              isXBox (ExpBox _) = True
              isXBox _ = False
              isInEMapOrNotExpBox (Just _, _, _) = True
              isInEMapOrNotExpBox (_, r, _) = not (any (isXBox . fst) r)
              isLooper (Just "gcd' 0 b", _, _) = True
              isLooper _ = False

              loopEntry = find isLooper trc

          all isInEMapOrNotExpBox trc @? "All the expressions should be present in the trace!"
          isJust loopEntry @? "The loop causing expresssion should be in the trace"
          let Just (_, _, loops) = loopEntry
          loops >= 100_000 @? "There should have been a lot of invocations of the loop!"
    ]

sanctifyTests =
  testGroup
    "Sanctify tests"
    [ localOption (mkTimeout 1_000_000) $
        testCase "Sanctify foldl program" $ do
          let cc = (compileConfig tESTCONF)
              toFix = "tests/cases/BrokenModule.hs"
              repair_target = Just "broken"
          (cc', _, Just EProb {..}) <- moduleToProb cc toFix repair_target
          -- There are 7 ways to replace parts of the broken function in BrokenModule
          -- with holes:
          let [(_, _, e_prog')] = e_prog
          length (sanctifyExpr noAnn e_prog') @?= 7,
      localOption (mkTimeout 1_000_000) $
        testCase "Fill foldl program" $ do
          let cc = compileConfig tESTCONF
              toFix = "tests/cases/BrokenModule.hs"
              repair_target = Just "broken"
          (cc', _, Just EProb {..}) <- moduleToProb cc toFix repair_target
          let [(_, _, e_prog')] = e_prog
              (holes, holey) = unzip $ sanctifyExpr noAnn e_prog'
              filled = mapMaybe (fillHole Nothing undefVar) holey
          length filled @?= 7
          all (uncurry (==)) (zip holes (map fst filled)) @? "All fillings should match holes!"
    ]

moduleTests :: TestTree
moduleTests =
  testGroup
    "Module tests"
    [ localOption (mkTimeout 30_000_000) $
        testCase "Repair BrokenModule finds correct target" $ do
          let toFix = "tests/cases/BrokenModule.hs"
          (_, _, Just EProb {..}) <- moduleToProb (compileConfig tESTCONF) toFix Nothing
          let [(e_target, _, _)] = e_prog
          showUnsafe e_target @?= "broken",
      mkSimpleModuleTest 30_000_000 "Repair BrokenModule With Diff" "tests/cases/BrokenModule.hs" (Just "broken"),
      mkSimpleModuleTest 30_000_000 "Repair MagicConstant" "tests/cases/MagicConstant.hs" Nothing,
      mkSimpleModuleTest 10_000_000 "All props pass" "tests/cases/AllPropsPass.hs" Nothing,
      mkSimpleModuleTest 5_000_000 "No props" "tests/cases/NoProps.hs" Nothing,
      mkSimpleModuleTest 30_000_000 "Unnamed faked" "tests/cases/unnamed.hs" Nothing,
      mkSimpleModuleTest 30_000_000 "Main module faked" "tests/cases/mainMod.hs" Nothing,
      mkSimpleModuleTest 30_000_000 "Prelude overwrite" "tests/cases/PreludeOverwrite.hs" Nothing,
      mkSimpleModuleTest 30_000_000 "Prelude overwrite imports" "tests/cases/PreludeOverwriteImports.hs" Nothing
    ]

packageTests :: TestTree
packageTests =
  testGroup
    "Package tests"
    [  localOption (mkTimeout 30_000_000) $
            testCase "Repair Simple Package" $ do
                let conf = tESTCONF
                    -- diffs = "not working"
                diffs <- repairPackage conf "tests/packages/basic"

                error $ show diffs
        ]

main = defaultMain tests
