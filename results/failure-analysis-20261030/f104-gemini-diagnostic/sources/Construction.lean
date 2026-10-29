import Core

open scoped Topology
open TopologicalSpace

namespace MathGauge.F104

universe u v w

variable {ι : Type u} {X : Type v} {Y : ι → Type w}

/-- 构造使全部 $f_i$ 连续的最粗拓扑：
在 Mathlib 中，诱导拓扑 `TopologicalSpace.induced (f i) (t i)` 是使单个 $f_i$ 连续的最粗拓扑；
使族中所有映射连续的最粗拓扑是各诱导拓扑在拓扑格中的下确界（最大下界）：
`⨅ i, TopologicalSpace.induced (f i) (t i)`。 -/
@[reducible] def assembled (t : ∀ i, TopologicalSpace (Y i))
    (f : ∀ i, X → Y i) : TopologicalSpace X :=
  ⨅ i, TopologicalSpace.induced (f i) (t i)

/-- 最粗性：对任意使全部 $f_i$ 连续的拓扑 $s$，$s$ 细于 `assembled t f`。
在 Mathlib 的偏序下（开集反向包含），$s$ 比 $\tau$ 细表现为 `s ≤ assembled t f`。 -/
theorem construction_bound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (hs : Realizes t f s) : s ≤ assembled t f := by
  apply le_iInf
  intro i
  letI : TopologicalSpace X := s
  letI : TopologicalSpace (Y i) := t i
  exact continuous_iff_le_induced.mp (hs i)

/-- 最粗性的开集包含刻画：`assembled t f` 中的任意开集均在 $s$ 中开。 -/
theorem construction_bound_isOpen (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (hs : Realizes t f s) {U : Set X}
    (hU : (assembled t f).IsOpen U) : s.IsOpen U :=
  construction_bound t f s hs U hU

end MathGauge.F104
