# 商环层中的理想

设 $R$ 为任意交换含幺环，$I$ 为 $R$ 的理想。对每个 $n\in\mathbb N$，令
\[
Q_n=R/I^{n+1},\qquad q_n:R\longrightarrow Q_n,\qquad J_n=q_n(I),
\]
其中 $q_n(I)$ 表示理想的像。若 $m\le n$，令 $\rho_{m,n}:Q_n\to Q_m$ 为满足 $\rho_{m,n}q_n=q_m$ 的商环同态。

所要求的结果是：每个 $J_n^{n+1}$ 都等于零理想；对于 $m\le n$，$\rho_{m,n}(J_n)=J_m$；对于 $l\le m\le n$，$\rho_{l,m}\circ\rho_{m,n}=\rho_{l,n}$。

审核附件作为上述结果的形式化提交是否完整对齐。说明各声明实际使用的前提、证明的结论及它们和正文的对应关系，并给出支持判断的数学依据。编译结果和语义判断分别报告；不能把自己补充的论证说成附件已经完成。

附件为 Core.lean、Transfer.lean、Candidate.lean。

环境为 Lean 4.29.1，Mathlib 固定修订 5e932f97dd25535344f80f9dd8da3aab83df0fe6。


File: `Core.lean`
```lean
import Mathlib.RingTheory.Ideal.Quotient.Operations
namespace MathGauge.F101
variable {R : Type*} [CommRing R]
abbrev Level (I : Ideal R) (n : ℕ) := R ⧸ I ^ (n + 1)
def residual (I : Ideal R) (n : ℕ) : Ideal (Level I n) :=
  I.map (Ideal.Quotient.mk (I ^ (n + 1)))
def transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) : Level I n →+* Level I m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
end MathGauge.F101
```


File: `Transfer.lean`
```lean
import Core
namespace MathGauge.F101
variable {R : Type*} [CommRing R]
structure SourceData (I : Ideal R) where
  exponent : ℕ
  annihilates : I ^ exponent = ⊥
theorem mapped_power (I J : Ideal R) (n : ℕ) :
    (I.map (Ideal.Quotient.mk J)) ^ n = (I ^ n).map (Ideal.Quotient.mk J) := by
  exact (Ideal.map_pow _ _ _).symm
theorem transport (I J : Ideal R) (d : SourceData I) :
    IsNilpotent (I.map (Ideal.Quotient.mk J)) := by
  refine ⟨d.exponent, ?_⟩
  change (I.map (Ideal.Quotient.mk J)) ^ d.exponent = ⊥
  rw [mapped_power, d.annihilates, Ideal.map_bot]
theorem transition_image (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := by
  simp only [residual, transition, Ideal.map_map, Ideal.Quotient.factor_comp_mk]
theorem transition_comp (I : Ideal R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (transition I h).comp (transition I k) = transition I (h.trans k) := by
  unfold transition
  exact Ideal.Quotient.factor_comp _ _
end MathGauge.F101
```


File: `Candidate.lean`
```lean
import Transfer
namespace MathGauge.F101
variable {R : Type*} [CommRing R]
theorem candidate_nilpotent (I : Ideal R) (d : SourceData I) (n : ℕ) :
    IsNilpotent (residual I n) := transport I (I ^ (n + 1)) d
theorem candidate_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := transition_image I h
theorem candidate_composition (I : Ideal R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (transition I h).comp (transition I k) = transition I (h.trans k) :=
  transition_comp I h k
#print axioms candidate_nilpotent
#print axioms candidate_transition
#print axioms candidate_composition
end MathGauge.F101
```
