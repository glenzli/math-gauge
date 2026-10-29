import Mathlib.RingTheory.Ideal.Quotient.Operations
import Core

namespace MathGauge.F102

variable {R : Type*} [CommRing R]

/-!
### 辅助引理 (Auxiliary lemmas)
-/

/-- 对于任意理想 $K$，$K$ 在典范商映射下的像为商环中的零理想 $\bot$。 -/
lemma map_quotient_mk_self (K : Ideal R) : K.map (Ideal.Quotient.mk K) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact Submodule.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

/-- 过渡同态在元素上的作用：$\rho_{m,n}(q_n(x)) = q_m(x)$。 -/
lemma transition_mk (I : Ideal R) {m n : ℕ} (h : m ≤ n) (x : R) :
    transition I h (Ideal.Quotient.mk (I ^ (n + 1)) x) =
      Ideal.Quotient.mk (I ^ (m + 1)) x := rfl

/-- 过渡同态与典范商映射的复合：$\rho_{m,n} \circ q_n = q_m$。 -/
theorem transition_comp_mk (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (transition I h).comp (Ideal.Quotient.mk (I ^ (n + 1))) =
      Ideal.Quotient.mk (I ^ (m + 1)) := by
  ext x
  rfl

/-!
### 结果 1：每个 $J_n^{n+1}$ 都等于零理想
-/

/-- 每个 $J_n^{n+1}$ 等于零理想（表述为底元 $\bot$）。 -/
theorem residual_pow_succ_eq_bot (I : Ideal R) (n : ℕ) :
    residual I n ^ (n + 1) = ⊥ := by
  change (I.map (Ideal.Quotient.mk (I ^ (n + 1)))) ^ (n + 1) = ⊥
  rw [← Ideal.map_pow]
  exact map_quotient_mk_self (I ^ (n + 1))

/-- 每个 $J_n^{n+1}$ 等于零理想（表述为零元 $0$）。 -/
theorem residual_pow_succ_eq_zero (I : Ideal R) (n : ℕ) :
    residual I n ^ (n + 1) = 0 :=
  residual_pow_succ_eq_bot I n

/-!
### 结果 2：对于 $m \le n$，$\rho_{m,n}(J_n) = J_m$
-/

/-- 对于 $m \le n$，$\rho_{m,n}(J_n) = J_m$。 -/
theorem map_transition_residual (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := by
  change (I.map (Ideal.Quotient.mk (I ^ (n + 1)))).map (transition I h) =
    I.map (Ideal.Quotient.mk (I ^ (m + 1)))
  rw [Ideal.map_map]
  rw [transition_comp_mk]

/-- `map_transition_residual` 的别名。 -/
theorem transition_residual (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m :=
  map_transition_residual I h

/-!
### 结果 3：对于 $l \le m \le n$，$\rho_{l,m} \circ \rho_{m,n} = \rho_{l,n}$
-/

/-- 对于 $l \le m \le n$，环同态复合满足 $\rho_{l,m} \circ \rho_{m,n} = \rho_{l,n}$。 -/
theorem transition_comp (I : Ideal R) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    (transition I hlm).comp (transition I hmn) = transition I (hlm.trans hmn) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 带有显式传递性证明 $hln : l \le n$ 形式的复合定理。 -/
theorem transition_comp' (I : Ideal R) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (hln : l ≤ n) :
    (transition I hlm).comp (transition I hmn) = transition I hln :=
  transition_comp I hlm hmn

/-- 复合定理的逐点（element-wise）形式。 -/
theorem transition_comp_apply (I : Ideal R) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (x : Level I n) :
    transition I hlm (transition I hmn x) = transition I (hlm.trans hmn) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 带有显式传递性证明 $hln : l \le n$ 的逐点形式。 -/
theorem transition_comp_apply' (I : Ideal R) {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (hln : l ≤ n) (x : Level I n) :
    transition I hlm (transition I hmn x) = transition I hln x :=
  transition_comp_apply I hlm hmn x

/-!
### 补充：自同态恒等性质
-/

/-- 当 $m = n$ 时，过渡同态为恒等同态。 -/
theorem transition_refl (I : Ideal R) (n : ℕ) :
    transition I (le_refl n) = RingHom.id (Level I n) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end MathGauge.F102
