import ErgodicConsequences
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology Finset
namespace MathGauge.OrthogonalComponents
open ErgodicOperators ErgodicRecovery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Part := Bool × Bool

def side (T : E →L[ℝ] E) (b : Bool) : E →L[ℝ] E := if b then T else 1-T

theorem side_star {T : E →L[ℝ] E} (hT : IsStarProjection T) (b : Bool) :
    IsStarProjection (side T b) := by cases b <;> simp only [side, Bool.false_eq_true, if_false, if_true]; exact hT.one_sub; exact hT

theorem side_commute {T S : E →L[ℝ] E} (h : Commute T S) (b c : Bool) :
    Commute (side T b) (side S c) := by
  cases b <;> cases c <;> simp only [side, Bool.false_eq_true, if_false, if_true]
  · exact (Commute.one_right _).sub_right ((Commute.one_left _).sub_left h)
  · exact (Commute.one_left _).sub_left h
  · exact (Commute.one_right _).sub_right h
  · exact h

theorem side_cross {T : E →L[ℝ] E} (hT : IsStarProjection T) (b c : Bool) (h : b ≠ c) :
    side T b * side T c = 0 := by
  cases b <;> cases c <;> simp_all only [side, Bool.false_eq_true, if_false, if_true, ne_eq, not_true_eq_false]
  · exact hT.one_sub_mul_self
  · exact hT.mul_one_sub_self

def component (T S : E →L[ℝ] E) (i : Part) : E →L[ℝ] E := side T i.1 * side S i.2

theorem component_star {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (i : Part) :
    IsStarProjection (component T S i) :=
  (side_star hT _).mul (side_star hS _) (side_commute h _ _)

theorem component_cross {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (i j : Part) (hij : i ≠ j) :
    component T S i * component T S j = 0 := by
  have hc := (side_commute h.symm i.2 j.1).eq
  have he : component T S i * component T S j =
      (side T i.1 * side T j.1) * (side S i.2 * side S j.2) := by
    simp only [component,mul_assoc]
    rw [← mul_assoc (side S i.2),hc,mul_assoc]
  rw [he]
  by_cases h1 : i.1 = j.1
  · have h2 : i.2 ≠ j.2 := by intro he; exact hij (Prod.ext h1 he)
    rw [side_cross hS _ _ h2,mul_zero]
  · rw [side_cross hT _ _ h1,zero_mul]

theorem component_sum (T S : E →L[ℝ] E) : ∑ i : Part, component T S i = 1 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,component,side,
    Bool.false_eq_true,if_false,if_true]
  noncomm_ring

theorem component_decomposition (T S : E →L[ℝ] E) (x : E) :
    ∑ i : Part, component T S i x = x := by
  rw [← ContinuousLinearMap.sum_apply,component_sum]
  rfl

theorem component_orthogonal {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (i j : Part) (hij : i ≠ j) (x y : E) :
    inner ℝ (component T S i x) (component T S j y) = 0 := by
  have he := (component_star hT hS h i).isSelfAdjoint.isSymmetric x (component T S j y)
  change inner ℝ (component T S i x) (component T S j y) =
    inner ℝ x (component T S i (component T S j y)) at he
  rw [he]
  change inner ℝ x ((component T S i * component T S j) y) = 0
  rw [component_cross hT hS h i j hij]
  simp

/-- Pythagoras for the four actual orthogonal components, including zero components. -/
theorem weighted_norm_square {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (a : Part → ℝ) (x : E) :
    ‖∑ i, a i • component T S i x‖ ^ 2 =
      ∑ i, (a i)^2 * ‖component T S i x‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]; ring
  · intro j _ hji
    rw [component_orthogonal hT hS h j i hji]
    ring
  · simp

theorem component_square_sum {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (x : E) :
    ∑ i : Part, ‖component T S i x‖^2 = ‖x‖^2 := by
  simpa only [one_smul,one_pow,one_mul,component_decomposition] using
    (weighted_norm_square hT hS h (fun _ => 1) x).symm

theorem weighted_bound {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (a : Part → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, |a i| ≤ r) (x : E) :
    ‖∑ i, a i • component T S i x‖ ≤ r * ‖x‖ := by
  have hs : ‖∑ i, a i • component T S i x‖^2 ≤ r^2 * ‖x‖^2 := by
    rw [weighted_norm_square hT hS h,← component_square_sum hT hS h x,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [abs_nonneg (a i),sq_abs (a i),ha i]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg x))).mp
  simpa only [mul_pow] using hs

end MathGauge.OrthogonalComponents
