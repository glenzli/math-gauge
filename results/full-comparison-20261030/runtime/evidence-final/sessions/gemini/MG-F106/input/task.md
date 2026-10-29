# 从陪集切片构造有限覆盖

设 $G$ 为任意阿贝尔群，$A\subset G$ 为有限集合，$H\le G$ 为子群，$x\in G$，$K\in\mathbb R$。记
$$B=\{a\in A:a-x\in H\}.$$
假设 $B\ne\varnothing$ 且 $|A+A|\le K|A|$。构造有限集合 $F\subseteq A$，使
$$|F|\le\frac{K|A|}{|B|},\qquad
\forall a\in A\ \exists t\in F:\ a-t\in H.$$
基数在不等式中视为实数。背景定义以附件 `Core.lean` 为准；允许使用 Mathlib 及经典逻辑。

完成这一目标的 Lean 形式化。最终回答须在以文件名标注的 Lean 代码块中交付全部新增源码，并说明各声明覆盖的结论；提供可导入的 `Solution.lean`。沿用附件中的定义，完整写出最终定理类型与证明。

Lean 4.29.1，Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。


File: `Core.lean`
```lean
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Pointwise
namespace MathGauge.F106
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def cosetSlice (A : Finset G) (H : AddSubgroup G) (x : G) : Finset G := by
  classical
  exact A.filter (fun a => a - x ∈ H)

def Covers (A : Finset G) (H : AddSubgroup G) (F : Finset G) : Prop :=
  ∀ a ∈ A, ∃ t ∈ F, a - t ∈ H

@[simp] theorem mem_cosetSlice (A : Finset G) (H : AddSubgroup G) (x a : G) :
    a ∈ cosetSlice A H x ↔ a ∈ A ∧ a - x ∈ H := by
  classical
  simp [cosetSlice]

theorem slice_subset (A : Finset G) (H : AddSubgroup G) (x : G) :
    cosetSlice A H x ⊆ A := by
  intro a ha
  exact (mem_cosetSlice A H x a).mp ha |>.1

end MathGauge.F106
```
