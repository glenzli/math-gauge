# 一族映射诱导的拓扑

设 $X$ 为任意集合，$A$ 为任意指标集。对每个 $a\in A$，给定拓扑空间 $(Y_a,\tau_a)$ 和映射 $f_a:X\to Y_a$。构造 $X$ 上使全部 $f_a$ 连续的最粗拓扑 $\tau$，并证明这个拓扑唯一。

还须证明其映射性质：对任意拓扑空间 $(Z,\sigma)$ 及映射 $g:Z\to X$，$g:(Z,\sigma)\to(X,\tau)$ 连续，当且仅当每个 $f_a\circ g:(Z,\sigma)\to(Y_a,\tau_a)$ 连续。

附件是针对上述任务的一个形式化提交。先判断其实际覆盖范围，再修改或补充 Lean，使最终交付完成上述任务。保持正文的对象、条件与结论。

提交完整 Lean 文件和覆盖说明。每个文件用独立的代码块交付，格式为 ` ```lean filename=文件名.lean `（实际使用三个反引号），不得只引用本地文件路径。允许等价表述和不同证明路线。说明最终各声明对应正文哪一部分，以及尚未完成的部分。

附件为 Core.lean、Construction.lean、Candidate.lean。

环境为 Lean 4.29.1，Mathlib 固定修订 5e932f97dd25535344f80f9dd8da3aab83df0fe6。


File: `Core.lean`
```lean
import Mathlib.Topology.Order
open scoped Topology
namespace MathGauge.F104
universe u v w
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
def Realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) : Prop := ∀ i, Continuous[s, t i] (f i)
end MathGauge.F104
```


File: `Construction.lean`
```lean
import Core
open scoped Topology
namespace MathGauge.F104
universe u v w
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
@[reducible] def assembled (t : ∀ i, TopologicalSpace (Y i))
    (f : ∀ i, X → Y i) : TopologicalSpace X :=
  sInf {s | Realizes t f s}
theorem construction_bound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (hs : Realizes t f s) : assembled t f ≤ s := by
  exact sInf_le hs
end MathGauge.F104
```


File: `Candidate.lean`
```lean
import Construction
open scoped Topology
namespace MathGauge.F104
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}
theorem candidate_realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (assembled t f) := by
  intro i
  have hb : Realizes t f (⊥ : TopologicalSpace X) := fun _ => continuous_bot
  exact continuous_le_dom (construction_bound t f ⊥ hb) continuous_bot
theorem candidate_inbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X)
    (hg : Continuous[s, assembled t f] g) :
    ∀ i, Continuous[s, t i] (f i ∘ g) := by
  intro i
  letI : TopologicalSpace Z := s
  letI : TopologicalSpace X := assembled t f
  letI : TopologicalSpace (Y i) := t i
  exact (candidate_realizes t f i).comp hg
#print axioms candidate_realizes
#print axioms candidate_inbound
end MathGauge.F104
```
