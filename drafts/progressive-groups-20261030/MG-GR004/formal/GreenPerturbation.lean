import FiniteComplexTarget

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.HilbertPerturbation
open HilbertCriteria
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def Green (L : F →L[ℂ] F) {c : ℝ} (hc : 0<c)
    (hL : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) : F →L[ℂ] F :=
  (coerciveEquiv L c hc hL).symm.toContinuousLinearMap

theorem Green_right (L : F →L[ℂ] F) {c : ℝ} (hc : 0<c)
    (hL : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) :
    L.comp (Green L hc hL) = ContinuousLinearMap.id ℂ F := by
  apply ContinuousLinearMap.ext
  exact (coerciveEquiv L c hc hL).apply_symm_apply

theorem Green_left (L : F →L[ℂ] F) {c : ℝ} (hc : 0<c)
    (hL : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) :
    (Green L hc hL).comp L = ContinuousLinearMap.id ℂ F := by
  apply ContinuousLinearMap.ext
  exact (coerciveEquiv L c hc hL).symm_apply_apply

theorem Green_norm (L : F →L[ℂ] F) {c : ℝ} (hc : 0<c)
    (hL : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) :
    ‖Green L hc hL‖ ≤ c⁻¹ := coercive_inverse_bound L c hc hL

theorem adjoint_product_difference (A A' : E →L[ℂ] F) :
    A'.comp A'.adjoint-A.comp A.adjoint =
      (A'-A).comp A'.adjoint+A.comp (A'-A).adjoint := by
  simp only [map_sub,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
  abel

theorem adjoint_product_bound (A A' : E →L[ℂ] F) {δ : ℝ} (hδ : ‖A'-A‖ ≤ δ) :
    ‖A'.comp A'.adjoint-A.comp A.adjoint‖ ≤ 2*‖A‖*δ+δ^2 := by
  have hd0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hAp : ‖A'‖ ≤ ‖A‖+δ := by
    have hn := norm_add_le (A'-A) A
    simp only [sub_add_cancel] at hn
    linarith
  rw [adjoint_product_difference]
  have h1 := (A'-A).opNorm_comp_le A'.adjoint
  have h2 := A.opNorm_comp_le (A'-A).adjoint
  have hn := norm_add_le ((A'-A).comp A'.adjoint) (A.comp (A'-A).adjoint)
  simp only [ContinuousLinearMap.adjoint.norm_map] at h1 h2
  have ha := mul_le_mul hδ hAp (norm_nonneg _) hd0
  have hb := mul_le_mul_of_nonneg_left hδ (norm_nonneg A)
  nlinarith

theorem laplacian_perturbation_bound (A A' : E →L[ℂ] F) (B B' : F →L[ℂ] G)
    {δA δB : ℝ} (hA : ‖A'-A‖ ≤ δA) (hB : ‖B'-B‖ ≤ δB) :
    ‖laplacian A' B'-laplacian A B‖ ≤
      2*‖A‖*δA+δA^2+2*‖B‖*δB+δB^2 := by
  have h1 := adjoint_product_bound A A' hA
  have he : ‖B'.adjoint-B.adjoint‖ = ‖B'-B‖ := by
    rw [← map_sub]
    exact ContinuousLinearMap.adjoint.norm_map _
  have h2 := adjoint_product_bound B.adjoint B'.adjoint (he ▸ hB)
  simp only [ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.adjoint.norm_map] at h2
  have hid : laplacian A' B'-laplacian A B =
      (A'.comp A'.adjoint-A.comp A.adjoint)+(B'.adjoint.comp B'-B.adjoint.comp B) := by
    unfold laplacian
    abel
  rw [hid]
  have hn := norm_add_le (A'.comp A'.adjoint-A.comp A.adjoint) (B'.adjoint.comp B'-B.adjoint.comp B)
  linarith

theorem coercive_perturbation (L L' : F →L[ℂ] F) {c η : ℝ}
    (hL : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) (hη : ‖L'-L‖ ≤ η) :
    ∀ x, (c-η)*‖x‖^2 ≤ Complex.re (inner ℂ (L' x) x) := by
  intro x
  have hn : ‖(L'-L) x‖ ≤ η*‖x‖ := ((L'-L).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hη (norm_nonneg x))
  have hinner : Complex.re (inner ℂ (L x-L' x) x) ≤ η*‖x‖^2 := by
    have h := re_inner_le_norm (𝕜 := ℂ) (L x-L' x) x
    have hd : ‖L x-L' x‖ = ‖(L'-L) x‖ := by rw [ContinuousLinearMap.sub_apply,norm_sub_rev]
    rw [hd] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg x)).trans_eq (by ring))
  rw [inner_sub_left,Complex.sub_re] at hinner
  nlinarith [hL x]

theorem inverse_difference (L M U V : F →L[ℂ] F)
    (hU : L.comp U=ContinuousLinearMap.id ℂ F)
    (hV : V.comp M=ContinuousLinearMap.id ℂ F) : V-U=V.comp ((L-M).comp U) := by
  rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,
    hU,ContinuousLinearMap.comp_id,
    ← ContinuousLinearMap.comp_assoc,hV,ContinuousLinearMap.id_comp]

theorem Green_perturbation_norm (L L' : F →L[ℂ] F) {c η : ℝ}
    (hc : 0<c) (hηc : η<c)
    (hL : ∀ x, c*‖x‖^2 ≤ Complex.re (inner ℂ (L x) x)) (hη : ‖L'-L‖ ≤ η) :
    ‖Green L' (sub_pos.mpr hηc) (coercive_perturbation L L' hL hη)-Green L hc hL‖ ≤
      η/(c*(c-η)) := by
  let U := Green L hc hL
  let V := Green L' (sub_pos.mpr hηc) (coercive_perturbation L L' hL hη)
  have hnU := Green_norm L hc hL
  have hnV := Green_norm L' (sub_pos.mpr hηc) (coercive_perturbation L L' hL hη)
  change ‖V-U‖ ≤ _
  rw [inverse_difference L L' U V (Green_right L hc hL)
    (Green_left L' (sub_pos.mpr hηc) (coercive_perturbation L L' hL hη))]
  have hn : ‖L-L'‖ ≤ η := by simpa only [norm_sub_rev] using hη
  have hd0 : 0 ≤ η := (norm_nonneg _).trans hη
  have hp : 0 < c-η := sub_pos.mpr hηc
  calc
    _ ≤ ‖V‖*(‖L-L'‖*‖U‖) :=
      (V.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ((L-L').opNorm_comp_le U) (norm_nonneg V))
    _ ≤ (c-η)⁻¹*(η*c⁻¹) := mul_le_mul hnV
      (mul_le_mul hn hnU (norm_nonneg _) hd0) (by positivity) (by positivity)
    _ = η/(c*(c-η)) := by rw [div_eq_mul_inv,mul_inv_rev]; ring

theorem contraction_perturbation_norm (A A' : E →L[ℂ] F) (U V : F →L[ℂ] F)
    {δ b q : ℝ} (hδ : ‖A'-A‖ ≤ δ) (hb : ‖V‖ ≤ b) (hq : ‖V-U‖ ≤ q) :
    ‖A'.adjoint.comp V-A.adjoint.comp U‖ ≤ δ*b+‖A‖*q := by
  have he : A'.adjoint.comp V-A.adjoint.comp U =
      (A'-A).adjoint.comp V+A.adjoint.comp (V-U) := by
    simp only [map_sub,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  have h1 := (A'-A).adjoint.opNorm_comp_le V
  have h2 := A.adjoint.opNorm_comp_le (V-U)
  simp only [ContinuousLinearMap.adjoint.norm_map] at h1 h2
  have hd0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hh1 := mul_le_mul hδ hb (norm_nonneg _) hd0
  have hh2 := mul_le_mul_of_nonneg_left hq (norm_nonneg A)
  have hh := norm_add_le ((A'-A).adjoint.comp V) (A.adjoint.comp (V-U))
  linarith

end MathGauge.HilbertPerturbation
