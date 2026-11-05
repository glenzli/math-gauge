import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

variable {X : Type} {bot : X}

theorem ex_3_2_i (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K r_N : ENNReal) (hK_pos : 0 < K) (hrN_pos : 0 < r_N)
    (h_unif : r_N ≤ r_null_uniform d_in d_out ϕ U)
    (hcoLip : ∀ x ∈ U, ∀ y ∈ U, K * d_in x y ≤ d_out (ϕ.func x) (ϕ.func y)) :
    ¬∃ x ∈ U, ∃ y ∈ U, 0 < d_in x y ∧ d_in x y < r_N := by
  rintro ⟨x, hx, y, hy, hdist_pos, hdist_rN⟩
  have hlt : d_in x y < r_null_uniform d_in d_out ϕ U := lt_of_lt_of_le hdist_rN h_unif
  have hzero := prop_3_15_i d_in d_out ϕ U hx hy hlt
  have h1 := hcoLip x hx y hy
  rw [hzero] at h1
  have h_prod_zero : K * d_in x y = 0 := nonpos_iff_eq_zero.mp h1
  rw [mul_eq_zero] at h_prod_zero
  rcases h_prod_zero with hK0 | hd0
  · exact (lt_self_iff_false 0).mp (lt_of_le_of_lt (le_of_eq hK0.symm) hK_pos)
  · rw [hd0] at hdist_pos
    exact (lt_self_iff_false 0).mp hdist_pos

theorem ex_3_2_ii (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K r_N : ENNReal) (hK_pos : 0 < K) (hrN_pos : 0 < r_N)
    (h_unif : r_N ≤ r_null_uniform d_in d_out ϕ U)
    (hcoLip : ∀ x ∈ U, ∀ y ∈ U, K * d_in x y ≤ d_out (ϕ.func x) (ϕ.func y))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d_in x y = 0 ∨ r_N ≤ d_in x y := by
  by_cases hzero : d_in x y = 0
  · left; exact hzero
  · right
    have hpos : 0 < d_in x y := pos_iff_ne_zero.mpr hzero
    have hno := ex_3_2_i d_in d_out ϕ U K r_N hK_pos hrN_pos h_unif hcoLip
    by_contra! hlt
    exact hno ⟨x, hx, y, hy, hpos, hlt⟩

#check @ex_3_2_i
#check @ex_3_2_ii
