# Lean 对应表

| 数学义务 | 实际声明 |
|---|---|
| 真实陪集切片、成员条件 | Core.cosetSlice、mem_cosetSlice、slice_subset |
| 同一陪集的差位于子群 | Bridge.slice_difference |
| 差集覆盖转为子群陪集覆盖 | Bridge.lift_cover |
| F⊆A、精确基数上界与完整覆盖 | Candidate.dense_coset_cover |

所有声明位于 MathGauge.F105 命名空间。Ruzsa 引理为实际导入的已证明 Mathlib 定理。此表不覆盖原 PFR 熵论或完整主定理。编译不替代语义审核，human pending。
