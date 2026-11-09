-- Prepared local Lake project; automatic source inventory.
import Lake
open Lake DSL
package benchmarkCandidate
require mathlib from "/Users/glen/lab/benchmark/preparation-v0.3.0-tcodex-20261103/env/mathlib"
@[default_target]
lean_lib BenchmarkCandidate where
  roots := #[`«Main», `«formal_oet».«vol_01».«ch_01_foundations».«gauge_space», `«formal_oet».«vol_01».«ch_01_foundations».«operator_space»]
