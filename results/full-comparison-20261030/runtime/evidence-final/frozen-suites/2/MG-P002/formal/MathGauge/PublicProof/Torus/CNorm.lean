import MathGauge.PublicProof.Torus.CubicBound
import MathGauge.PublicProof.Torus.GeneralTransport

noncomputable section
namespace MathGauge.PublicProof.Torus
open Set
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

/-- The order is exactly ∂x^a ∂y^b. -/
def orderedWord (a b : ℕ) : List Bool := List.replicate a false ++ List.replicate b true

def orderedDerivative (a b : ℕ) (f : Plane → ℂ) : Plane → ℂ := derivativeWord (orderedWord a b) f

/-- The exact maximum/supremum in the task, on its periodic universal cover. -/
def cmValues (m : ℕ) (f : Plane → ℂ) : Set ℝ :=
  {v | ∃ a b : ℕ, a + b ≤ m ∧ ∃ x : Plane, v = ‖orderedDerivative a b f x‖}

def cmNormCover (m : ℕ) (f : Plane → ℂ) : ℝ := sSup (cmValues m f)

lemma orderedWord_length (a b : ℕ) : (orderedWord a b).length = a + b := by simp [orderedWord]

lemma coordinatePartial_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : Bool) :
    ContDiff ℝ ∞ (coordinatePartial j f) :=
  (ContinuousLinearMap.apply ℝ ℂ (if j then (0, 1) else (1, 0))).contDiff.comp
    (hf.fderiv_right (by simp))

lemma derivativeWord_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (w : List Bool) :
    ContDiff ℝ ∞ (derivativeWord w f) := by
  induction w with
  | nil => exact hf
  | cons j js ih => exact coordinatePartial_smooth ih j

lemma norm_derivativeWord_le_moment {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (w : List Bool) (m : ℕ) (hm : w.length ≤ m) (x : Plane) :
    ‖derivativeWord w f x‖ ≤ ‖omega‖ ^ m * coeffSeminorm m (coefficient f) := by
  have ha := rapid_coefficient hf hp
  have he : series (coefficient f) = f := funext (series_coefficient hf hp)
  have hd := derivativeWord_series w ha
  rw [he] at hd
  rw [hd]
  apply (norm_series_le (ha.coefficientWord w) x).trans
  have hw (k : PairFrequency) : 1 ≤ Borrowed.TorusInverse.weight k := by
    dsimp [Borrowed.TorusInverse.weight]
    linarith [abs_nonneg (k.1 : ℝ), abs_nonneg (k.2 : ℝ)]
  have hb (k : PairFrequency) : ‖coefficientWord w (coefficient f) k‖ ≤
      ‖omega‖ ^ m * (Borrowed.TorusInverse.weight k ^ m * ‖coefficient f k‖) := by
    calc
      _ ≤ (‖omega‖ * Borrowed.TorusInverse.weight k) ^ w.length * ‖coefficient f k‖ :=
        norm_coefficientWord_le _ _ _
      _ ≤ (‖omega‖ * Borrowed.TorusInverse.weight k) ^ m * ‖coefficient f k‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le norm_omega_ge_one (hw k)) hm)
          (norm_nonneg _)
      _ = _ := by rw [mul_pow]; ring
  have ht := (ha.coefficientWord w).summable_norm.tsum_le_tsum hb ((ha m).mul_left (‖omega‖ ^ m))
  simpa only [coeffSeminorm, pow_zero, one_mul, tsum_mul_left] using ht

lemma cmValues_nonempty (m : ℕ) (f : Plane → ℂ) : (cmValues m f).Nonempty := by
  exact ⟨‖orderedDerivative 0 0 f (0, 0)‖, 0, 0, by omega, (0, 0), rfl⟩

lemma cmValues_bddAbove {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) (m : ℕ) :
    BddAbove (cmValues m f) := by
  refine ⟨‖omega‖ ^ m * coeffSeminorm m (coefficient f), ?_⟩
  rintro v ⟨a, b, hab, x, rfl⟩
  exact norm_derivativeWord_le_moment hf hp (orderedWord a b) m
    (by simpa only [orderedWord_length] using hab) x

lemma orderedDerivative_le_cmNorm {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f)
    {a b m : ℕ} (hab : a + b ≤ m) (x : Plane) :
    ‖orderedDerivative a b f x‖ ≤ cmNormCover m f :=
  le_csSup (cmValues_bddAbove hf hp m) ⟨a, b, hab, x, rfl⟩

lemma cmNormCover_nonneg {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) (m : ℕ) :
    0 ≤ cmNormCover m f :=
  (norm_nonneg _).trans (orderedDerivative_le_cmNorm hf hp (a := 0) (b := 0) (by omega) (0, 0))

lemma xJet_eq_word (n : ℕ) (f : Plane → ℂ) : xJet n f = derivativeWord (List.replicate n false) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xJet_succ, ih, List.replicate_succ]
    rfl

lemma partialX_swap {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    partialX (swapFunction f) = swapFunction (coordinatePartial true f) := by
  funext x
  have hd := ((hf.differentiable (by simp)) (x.2, x.1)).hasFDerivAt.comp x
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).prodMk (hasFDerivAt_fst (𝕜 := ℝ) (p := x)))
  have he := congrArg (fun L : Plane →L[ℝ] ℂ => L (1, 0)) hd.fderiv
  simpa only [partialX, swapFunction, coordinatePartial, ↓reduceIte,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply] using he

lemma xJet_swap_eq_word {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    xJet n (swapFunction f) = swapFunction (derivativeWord (List.replicate n true) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xJet_succ, ih, partialX_swap (derivativeWord_smooth hf _), List.replicate_succ]
    rfl

def fourConstant (m : ℕ) : ℝ :=
  ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ m) * 3 ^ (m + 4) *
    ∑' k : PairFrequency, (Borrowed.TorusInverse.weight k ^ 3)⁻¹

lemma fourConstant_nonneg (m : ℕ) : 0 ≤ fourConstant m := by
  unfold fourConstant
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun k => inv_nonneg.mpr (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _))

lemma fourConstant_mono {n m : ℕ} (hnm : n ≤ m) : fourConstant n ≤ fourConstant m := by
  have hS : 0 ≤ ∑' k : PairFrequency, (Borrowed.TorusInverse.weight k ^ 3)⁻¹ :=
    tsum_nonneg (fun k => inv_nonneg.mpr (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _))
  apply mul_le_mul_of_nonneg_right _ hS
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ norm_omega_ge_one hnm) (by positivity)
  · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  · positivity
  · positivity

/-- The entire `C^(m+4) → C^m` estimate, with one constant uniform over
all derivatives of total order at most `m` and all input functions. -/
theorem cmNormCover_inverse_bound_four {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (d : Direction) (m : ℕ) :
    cmNormCover m (directionalInverse d (coefficient f)) ≤ fourConstant m * cmNormCover (m + 4) f := by
  apply csSup_le (cmValues_nonempty _ _)
  rintro v ⟨a, b, hab, x, rfl⟩
  let w := orderedWord a b
  have hw : w.length ≤ m := by simpa [w, orderedWord_length] using hab
  have hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ cmNormCover (m + 4) f := by
    intro x _ y _
    exact orderedDerivative_le_cmNorm hf hp (a := 0) (b := 0) (by omega) (x, y)
  have hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (w.length + 4) f (x, y)‖ ≤ cmNormCover (m + 4) f := by
    intro x _ y _
    rw [xJet_eq_word]
    simpa only [orderedDerivative, orderedWord, List.replicate_zero, List.append_nil] using
      orderedDerivative_le_cmNorm hf hp (a := w.length + 4) (b := 0) (m := m + 4) (by omega) (x, y)
  have hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (w.length + 4) (swapFunction f) (x, y)‖ ≤ cmNormCover (m + 4) f := by
    intro x _ y _
    rw [xJet_swap_eq_word hf]
    exact orderedDerivative_le_cmNorm hf hp (a := 0) (b := w.length + 4) (m := m + 4) (by omega) (y, x)
  have h := inverse_derivativeWord_bound_four d hf hp w hzero hfirst hsecond x
  exact h.trans (mul_le_mul_of_nonneg_right (fourConstant_mono hw) (cmNormCover_nonneg hf hp _))

end MathGauge.PublicProof.Torus
