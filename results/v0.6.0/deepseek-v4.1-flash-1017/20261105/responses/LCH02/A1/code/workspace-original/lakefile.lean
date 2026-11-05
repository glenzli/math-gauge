-- LCH02 candidate project.
import Lake
open Lake DSL

package benchmarkCandidate
require mathlib from "/Users/glen/lab/benchmark/preparation-v0.3.0-tcodex-20261103/env/mathlib"

@[default_target]
lean_lib BenchmarkCandidate where
  roots := #[`Main,
    `«OET».«Chapter02».«Matrix», `«OET».«Chapter02».«Bounds», `«OET».«Chapter02».«Chains»,
    `«formal_oet».«vol_01».«ch_01_foundations».«gauge_space»,
    `«formal_oet».«vol_01».«ch_01_foundations».«operator_space»]
