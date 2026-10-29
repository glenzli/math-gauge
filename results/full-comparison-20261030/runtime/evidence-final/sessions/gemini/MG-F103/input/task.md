# 一族映射诱导的拓扑

设 $X$ 为任意集合，$A$ 为任意指标集。对每个 $a\in A$，给定拓扑空间 $(Y_a,\tau_a)$ 和映射 $f_a:X\to Y_a$。构造 $X$ 上使全部 $f_a$ 连续的最粗拓扑 $\tau$，并证明这个拓扑唯一。

还须证明其映射性质：对任意拓扑空间 $(Z,\sigma)$ 及映射 $g:Z\to X$，$g:(Z,\sigma)\to(X,\tau)$ 连续，当且仅当每个 $f_a\circ g:(Z,\sigma)\to(Y_a,\tau_a)$ 连续。

审核附件作为上述结果的形式化提交是否完整对齐。说明各声明实际使用的前提、证明的结论及它们和正文的对应关系，并给出支持判断的数学依据。编译结果和语义判断分别报告；不能把自己补充的论证说成附件已经完成。

附件为 Core.lean、Construction.lean、Candidate.lean。

环境为 Lean 4.29.1，Mathlib 固定修订 5e932f97dd25535344f80f9dd8da3aab83df0fe6。


File: `Core.lean`
```lean
import Mathlib.Topology.Order
open scoped Topology
namespace MathGauge.F103
universe u v w
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
def Realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) : Prop := ∀ i, Continuous[s, t i] (f i)
end MathGauge.F103
```


File: `Construction.lean`
```lean
import Core
open scoped Topology
namespace MathGauge.F103
universe u v w
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
@[reducible] def assembled (t : ∀ i, TopologicalSpace (Y i))
    (f : ∀ i, X → Y i) : TopologicalSpace X :=
  ⨅ i, TopologicalSpace.induced (f i) (t i)
end MathGauge.F103
```


File: `Candidate.lean`
```lean
import Construction
open scoped Topology
namespace MathGauge.F103
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
theorem candidate_realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (assembled t f) := by
  intro i
  exact continuous_iff_le_induced.2 (iInf_le _ i)
theorem candidate_coarsest (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (h : Realizes t f s) : s ≤ assembled t f := by
  exact le_iInf fun i => continuous_iff_le_induced.1 (h i)
theorem candidate_inbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X) :
    Continuous[s, assembled t f] g ↔ ∀ i, Continuous[s, t i] (f i ∘ g) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]
theorem candidate_unique (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (h : Realizes t f s)
    (hs : ∀ r : TopologicalSpace X, Realizes t f r → r ≤ s) : s = assembled t f := by
  exact le_antisymm (candidate_coarsest t f s h) (hs _ (candidate_realizes t f))
#print axioms candidate_realizes
#print axioms candidate_coarsest
#print axioms candidate_inbound
#print axioms candidate_unique
end MathGauge.F103
```
