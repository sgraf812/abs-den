{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module TestMain (main) where

import           Hedgehog hiding (label,eval)
import           Hedgehog.Gen (sized, int)
import           Hedgehog.Range (constant)
import           Control.Monad
import qualified Gen
import           Control.Monad.IO.Class
import           Debug.Trace
import qualified Data.Map as Map
import           Data.Maybe
import           Data.String
import qualified Data.List.NonEmpty as NE
import           Text.Printf
import           Control.Concurrent
import           Control.Concurrent.Async.Lifted (race)
import           Control.Exception

import           Exp hiding (assert)
import           Interpreter
import           Abstraction


main :: IO ()
main = void $
  checkParallel $$(discover)

sizeFactor :: Int
sizeFactor = 2

withTimeLimit :: Int -> TestT IO a -> TestT IO a
withTimeLimit timeout v = do
  result <-
    race
      (liftIO $ threadDelay timeout)
      v
  case result of
    Left () -> fail "Timeout exceeded"
    Right x -> pure x

eqListBy :: (a -> b -> Bool) -> [a] -> [b] -> Bool
eqListBy f []     []     = True
eqListBy f (x:xs) (y:ys) = f x y && eqListBy f xs ys
eqListBy _ _      _      = False

prop_Eq_Expr_reflexive =
  property $ do
    --e <- forAll (sized (\s -> trace (show s) Gen.closedExpr))
    --liftIO $ print (Gen.exprSize e)
    --liftIO $ print (Gen.exprDepth e)
    e <- forAll Gen.closedExpr
    e === e

prop_runCFA =
  property $ do
    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
    let !_ = runCFA (eval e emp)
    return ()

--prop_maxinf_maximal_trace_stuck_or_balanced =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p = run le Map.empty (End (E le))
--    let p' = takeT (sizeFactor*100) p
--    let maximal = p' == takeT (sizeFactor*101) p
--    let value = val p'
--    let stuck = isNothing value
--    let balanced = isBalanced p'
--    --test $ withTimeLimit 10000 $ do
--    test $ do
--      assert (not maximal || stuck || balanced)
--      classify "stuck" stuck
--      classify "balanced" balanced
--      classify "potentially infinite" (not maximal)
--    --forM_ [0..20] $ \n ->
--    --  classify (fromString (printf "larger than %3d" (20*n))) (Gen.exprSize e > 20*n)
--    --forM_ [0..20] $ \n ->
--    --  classify (fromString (printf "longer than %3d" (20*n))) (lenT p' > 20*n)
--
--prop_maxinf_stateless_is_cont =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p1 = run le Map.empty (End (E le))
--    let p2 = Cont.run le Map.empty (End (E le))
--    let p1' = takeT (sizeFactor*100) p1
--    let p2' = takeT (sizeFactor*100) p2
--    p1' === Cont.concTrace p2'
--
--prop_direct_cont_abs =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p = Cont.run le Map.empty (End (E le))
--    let p' = takeT (sizeFactor*100) p
--    p' === Cont.absTrace (Cont.concTrace p')
--
--prop_stateful_stateless =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p1 = Stateful.run le
--    let p2 = Stateless.run le Map.empty (End (E le))
--    let p1' = takeT (sizeFactor*100) p1
--    let p2' = takeT (sizeFactor*100) p2
--    traceLabels p1' === traceLabels p2'
--
--prop_dynamicenv_stateless =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p1 = DynamicEnv.run le
--    let p2 = run le Map.empty (End (E le))
--    let p1' = takeT (sizeFactor*100) p1
--    let p2' = takeT (sizeFactor*100) p2
--    traceLabels p1' === traceLabels p2'
--
--prop_envless_stateless =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p1 = Envless.run le
--    let p2 = run le Map.empty (End (E le))
--    let p1' = takeT (sizeFactor*100) p1
--    let p2' = takeT (sizeFactor*100) p2
--    traceLabels p1' === traceLabels p2'
--
--prop_stackless_stateless =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let p1 = Stackless.run le
--    let p2 = run le Map.empty (End (E le))
--    let p1' = takeT (sizeFactor*100) p1
--    let p2' = takeT (sizeFactor*100) p2
--    traceLabels p1' === traceLabels p2'
--
--prop_abs_conc_roundtrip =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    let strace = takeT (sizeFactor*50) $ Stateful.run le
--    let strace' = LessToFull.forward $ LessToFull.backward strace
--    strace === strace'
--    let trace = takeT (sizeFactor*50) $ Stateless.runInit le
--    let trace' = LessToFull.backward $ LessToFull.forward trace
--    trace === trace'
--
--prop_abs_continue_stateful_commutes =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    forM_ [1..20*sizeFactor] $ \n -> do
--      let p1  = takeT n $ Stateless.runInit le
--      let sp1 = LessToFull.forward p1
--      let sp2 = takeT n $ Stateful.run le
--      diff sp1 (Stateful.bisimilarForNSteps 20) sp2
--
--prop_conc_continue_stateless_commutes =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    let le = label e
--    forM_ [1..20*sizeFactor] $ \n -> do
--      let p1  = takeT n $ Stateful.run le
--      let sp1 = LessToFull.backward p1
--      let sp2 = takeT n $ Stateless.runInit le
--      diff sp1 (Stateless.bisimilarForNSteps 20) sp2
--
--prop_stateless_split_prefix =
--  property $ do
--    e <- forAll (Gen.openExpr (Gen.mkEnvWithNVars 2))
--    forM_ [1..20] $ \n -> do
--      let le = label e
--      let p = Stateless.runInit le
--      let pref = takeT n p
--      le' <- case tgt pref of Ret _ -> discard; E le' -> pure le'
--      let suff1 = dropT n p
--      let suff2 = Stateless.run le' (Stateless.materialiseEnv pref) pref
--      let p1 = takeT (sizeFactor*40) suff1
--      let p2 = takeT (sizeFactor*40) suff2
--      let is_pref a b = NE.toList (traceLabels a) `NE.isPrefixOf` traceLabels b
--      diff p2 is_pref p1
--
