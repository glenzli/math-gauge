import Spectral
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators
open Matrix
namespace MathGauge.RecursiveClosure
variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

/-- A finite-dimensional maximum principle, valid for signed vectors. -/
theorem weighted_maximum_principle (A : Matrix J J ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : J → ℝ) (hw : ∀ i, 0 < w i) (q : ℝ) (hq : q < 1)
    (hb : ∀ i, (A *ᵥ w) i ≤ q*w i)
    (z : J → ℝ) (hz : z ≤ A *ᵥ z) : z ≤ 0 := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => z j / w j) Finset.univ_nonempty
  have hall : ∀ j, z j ≤ (z i / w i) * w j := by
    intro j
    exact (div_le_iff₀ (hw j)).mp (hmax j (Finset.mem_univ j))
  by_cases hpos : 0 < z i / w i
  · have hmul : (A *ᵥ z) i ≤ (z i / w i) * (A *ᵥ w) i := by
      calc
        _ ≤ ∑ j, A i j * ((z i / w i) * w j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hall j) (hA i j)
        _ = _ := by
          simp only [mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    have hbound := (hz i).trans (hmul.trans (mul_le_mul_of_nonneg_left (hb i) hpos.le))
    have hzi : 0 < z i := (div_pos_iff.mp hpos).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge (hw i).le h.2))
    have he : z i / w i * (q * w i) = q * z i := by field_simp [(hw i).ne']
    rw [he] at hbound
    nlinarith
  · intro j
    exact (hall j).trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos) (hw j).le)

theorem one_sub_matrix_isUnit (A : Matrix J J ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : J → ℝ) (hw : ∀ i, 0 < w i) (q : ℝ) (hq : q < 1)
    (hb : ∀ i, (A *ᵥ w) i ≤ q*w i) : IsUnit (1-A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y he
  have hz : (1-A) *ᵥ (x-y) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
  have heq : x-y = A *ᵥ (x-y) := by
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hz
  have hle := weighted_maximum_principle A hA w hw q hq hb (x-y) heq.le
  have hge := weighted_maximum_principle A hA w hw q hq hb (-(x-y)) (by
    rw [Matrix.mulVec_neg, ← heq])
  funext i
  have h1 := hle i
  have h2 := hge i
  simp only [Pi.sub_apply, Pi.zero_apply, Pi.neg_apply] at h1 h2
  linarith

/-- The displayed inverse is the actual matrix inverse, not an assumed
resolvent or a scalar norm estimate. Finiteness of the vector is explicit. -/
theorem inverse_comparison (A : Matrix J J ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : J → ℝ) (hw : ∀ i, 0 < w i) (q : ℝ) (hq : q < 1)
    (hb : ∀ i, (A *ᵥ w) i ≤ q*w i)
    (d η : J → ℝ) (h : d ≤ A *ᵥ d + η) : d ≤ (1-A)⁻¹ *ᵥ η := by
  let u := (1-A)⁻¹ *ᵥ η
  have hu : (1-A) *ᵥ u = η := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (one_sub_matrix_isUnit A hA w hw q hq hb)),
      Matrix.one_mulVec]
  have hu' : u - A *ᵥ u = η := by
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hu
  have hs : d-u ≤ A *ᵥ (d-u) := by
    intro i
    have hi := h i
    have hui := congrFun hu' i
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub] at *
    linarith
  have hz := weighted_maximum_principle A hA w hw q hq hb (d-u) hs
  intro i
  have hi := hz i
  exact sub_nonpos.mp hi

end MathGauge.RecursiveClosure
