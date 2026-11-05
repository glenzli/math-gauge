-- Prepared local Lake project; automatic source inventory.
import Lake
open Lake DSL
package benchmarkCandidate
require mathlib from "/Users/glen/lab/benchmark/preparation-v0.3.0-tcodex-20261103/env/mathlib"
@[default_target]
lean_lib BenchmarkCandidate where
  roots := #[`«AxiomCheck», `«CH03».«Basic», `«CH03».«ComputeTest2», `«CH03».«ComputeTest3», `«CH03».«ComputeTest», `«CH03».«Core1», `«CH03».«Core2», `«CH03».«Core3», `«CH03».«Core4», `«CH03».«Core5», `«CH03».«Core6», `«CH03».«ENNTest», `«CH03».«Examples», `«CH03».«Exercise34», `«CH03».«Exercise35», `«CH03».«Exercises», `«CH03».«Fin4Test», `«CH03».«FinTest», `«CH03».«LineExamples», `«CH03».«NatTest», `«CH03».«NumTest», `«CH03».«OperatorLocalDegeneracy», `«CH03».«PhiTest2», `«CH03».«PhiTest», `«CH03».«StepCover», `«CH03».«SwapTest», `«CH03».«Test», `«Check2», `«Check», `«Main», `«MergedMainMin», `«MergedMain», `«formal_oet».«vol_01».«ch_01_foundations».«gauge_space», `«formal_oet».«vol_01».«ch_01_foundations».«metric_entropy», `«formal_oet».«vol_01».«ch_01_foundations».«operator_space», `«formal_oet».«vol_01».«ch_02_operator_bounds».«decoupling», `«formal_oet».«vol_01».«ch_02_operator_bounds».«lip_matrix», `«formal_oet».«vol_01».«ch_02_operator_bounds».«single_channel»]
