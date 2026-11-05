import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv

namespace OperatorLocalDegeneracy

set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations

variable {X : Type} {bot : X}

noncomputable def r_null (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_uniform (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

theorem prop_3_11_lt_sSup (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X)
    {x : X} (hx : x ∈ U) (hdist : d_in x y < r_null d_in d_out ϕ y U) :
    d_out (ϕ.func x) (ϕ.func y) = 0 := by
  dsimp [r_null] at hdist
  rcases lt_sSup_iff.mp hdist with ⟨r, hr_adm, hxr⟩
  exact hr_adm.2.2 x hx hxr

theorem prop_3_12_ii (d_in d_mid d_out : X → X → ENNReal)
    (ϕ ψ : Operator X bot) (U : Set X)
    (L : ENNReal) (hL_pos : 0 < L) (hL_top : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d_mid (ϕ.func x) (ϕ.func y) ≤ L * d_in x y) :
    (r_null_uniform d_mid d_out ψ (ϕ.func '' U)) / L ≤
      r_null_uniform d_in d_out (ψ * ϕ) U := by
  set R2 := r_null_uniform d_mid d_out ψ (ϕ.func '' U)
  dsimp [r_null_uniform]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  dsimp [r_null]
  by_cases hR2 : R2 / L = 0
  · rw [hR2]; exact bot_le
  have h_bound : ∀ c : ENNReal, 0 < c → c < R2 / L →
      c ≤ sSup { r | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out ((ψ * ϕ).func x) ((ψ * ϕ).func y) = 0 } := by
    intro c hc0 hc
    apply le_sSup
    have h_c_top : c < ⊤ := by
      by_contra! h_c
      have : c = ⊤ := top_le_iff.mp h_c
      subst this
      exact (not_top_lt hc).elim
    have hcL : L * c < R2 := by
      have h_iff := ENNReal.lt_div_iff_mul_lt (a := R2) (b := L) (c := c) (Or.inl hL_pos.ne') (Or.inl hL_top.ne)
      have hcL := h_iff.mp hc
      rw [mul_comm]
      exact hcL
    refine ⟨hc0, h_c_top, ?_⟩
    intro x hx hdist
    have h_mid_lt : d_mid (ϕ.func x) (ϕ.func y) < R2 := by
      have h1 := hLip x hx y hy
      have h2 : L * d_in x y < L * c := by
        rw [mul_comm L (d_in x y), mul_comm L c]
        exact ENNReal.mul_lt_mul_left hL_pos.ne' hL_top.ne hdist
      exact lt_of_le_of_lt h1 (lt_trans h2 hcL)
    have h_R2_le : R2 ≤ r_null d_mid d_out ψ (ϕ.func y) (ϕ.func '' U) := by
      dsimp [R2, r_null_uniform]
      exact biInf_le (fun u => r_null d_mid d_out ψ u (ϕ.func '' U)) ⟨y, hy, rfl⟩
    have h_mid_lt_sup : d_mid (ϕ.func x) (ϕ.func y) < r_null d_mid d_out ψ (ϕ.func y) (ϕ.func '' U) :=
      lt_of_lt_of_le h_mid_lt h_R2_le
    change d_out (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0
    exact prop_3_11_lt_sSup d_mid d_out ψ (ϕ.func '' U) (ϕ.func y) ⟨x, hx, rfl⟩ h_mid_lt_sup
  by_contra! hlt
  rcases exists_between hlt with ⟨c, hc_sup, hc_r2⟩
  have hc0 : 0 < c := lt_of_le_of_lt bot_le hc_sup
  have hc_le := h_bound c hc0 hc_r2
  exact (lt_self_iff_false c).mp (lt_of_le_of_lt hc_le hc_sup)
