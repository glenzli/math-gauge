import MathGauge.PublicProof.Torus.Functions
import MathGauge.PublicProof.Torus.Sobolev
import MathGauge.PublicProof.Torus.CNorm

noncomputable section
namespace MathGauge.PublicProof.Torus
open MeasureTheory
open scoped Topology ContDiff ENNReal
open Borrowed.TorusInverse Borrowed.SmoothFourierData

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The two standard finite-product presentations of the actual quotient torus. -/
def toPair (u : C(Torus2, ℂ)) : C(PairTorus, ℂ) where
  toFun y := u ![y.1, y.2]
  continuous_toFun := by
    apply u.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd

lemma native_toPair (u : C(Torus2, ℂ)) : nativeFunction (toPair u) = u := by
  ext y
  change u ![y 0, y 1] = u y
  congr 1
  ext i
  fin_cases i <;> rfl

lemma toPair_native (f : C(PairTorus, ℂ)) : toPair (nativeFunction f) = f := by
  ext y
  rfl

def coverOf (u : C(Torus2, ℂ)) : Plane → ℂ := torusLift (toPair u)

lemma coverOf_eq_pullback (u : C(Torus2, ℂ)) (x : Plane) :
    coverOf u x = pullback u ![x.1, x.2] := by
  change u ![(x.1 : UnitAddCircle), (x.2 : UnitAddCircle)] = u (project ![x.1, x.2])
  congr 1
  ext i
  fin_cases i <;> rfl

lemma pullback_eq_coverOf (u : C(Torus2, ℂ)) (x : Cover2) :
    pullback u x = coverOf u (x 0, x 1) := by
  change u (project x) = u ![(x 0 : UnitAddCircle), (x 1 : UnitAddCircle)]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Smoothness is equivalent across the two actual periodic coordinate presentations.
`∞` is the smooth index here; no analyticity hypothesis is added. -/
theorem smooth_iff_coverOf (u : C(Torus2, ℂ)) : Smooth u ↔ ContDiff ℝ ∞ (coverOf u) := by
  constructor
  · intro h
    have hc : ContDiff ℝ ∞ (fun x : Plane => (![x.1, x.2] : Cover2)) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact contDiff_fst
      · exact contDiff_snd
    convert h.comp hc using 1
    funext x
    exact coverOf_eq_pullback u x
  · intro h
    have hc : ContDiff ℝ ∞ (fun x : Cover2 => (x 0, x 1)) := by fun_prop
    have hh := h.comp hc
    change ContDiff ℝ ∞ (pullback u)
    convert hh using 1
    funext x
    exact pullback_eq_coverOf u x

lemma coverOf_periodic (u : C(Torus2, ℂ)) : UnitPeriodic (coverOf u) := torusLift_periodic _

lemma native_coeff_eq_cover (u : C(Torus2, ℂ)) (k : Frequency) :
    coeff u k = coefficient (coverOf u) (k 0, k 1) := by
  have h := native_coefficient_eq (toPair u) k
  rw [native_toPair] at h
  unfold coverOf
  rw [coefficient_lift_eq_torus]
  exact h

lemma native_meanZero_iff_cover (u : C(Torus2, ℂ)) :
    MeanZero u ↔ coefficient (coverOf u) 0 = 0 := by
  rw [meanZero_iff_coeff_zero, native_coeff_eq_cover]
  rfl

def frequencyEquiv : Frequency ≃ PairFrequency where
  toFun k := (k 0, k 1)
  invFun k := ![k.1, k.2]
  left_inv k := by ext i; fin_cases i <;> rfl
  right_inv k := by rfl

lemma pairWeight_frequencyEquiv (k : Frequency) : pairWeight (frequencyEquiv k) = weight k := by
  exact congrArg weight (frequencyEquiv.left_inv k)

/-- The task's exact Fourier norm on the native torus. -/
def nativeHNorm (r : ℝ) (u : Torus2 → ℂ) : ℝ :=
  Real.sqrt (∑' k : Frequency, weight k ^ (2 * r) * ‖coeff u k‖ ^ 2)

/-- Exact normalization and Euclidean frequency weights are preserved, not just norm equivalence. -/
theorem nativeHNorm_eq_cover (r : ℝ) (u : C(Torus2, ℂ)) : nativeHNorm r u = hNorm r (coverOf u) := by
  unfold nativeHNorm hNorm
  congr 1
  have h := frequencyEquiv.tsum_eq (fun k => energyTerm r (coefficient (coverOf u)) k)
  convert h using 1
  apply tsum_congr
  intro k
  rw [energyTerm, pairWeight_frequencyEquiv, native_coeff_eq_cover]
  rfl

/-- Every smooth periodic cover descends to an actual continuous torus function. -/
def ofCover (f : Plane → ℂ) (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) : C(Torus2, ℂ) :=
  nativeFunction (descendContinuous f hf.continuous hp)

lemma coverOf_ofCover (f : Plane → ℂ) (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) :
    coverOf (ofCover f hf hp) = f := by
  unfold coverOf ofCover
  rw [toPair_native]
  rfl

lemma ofCover_smooth (f : Plane → ℂ) (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) :
    Smooth (ofCover f hf hp) := by
  rw [smooth_iff_coverOf, coverOf_ofCover]
  exact hf

lemma coverOf_injective : Function.Injective coverOf := by
  intro u v h
  apply coeff_injective
  funext k
  dsimp only
  rw [native_coeff_eq_cover, native_coeff_eq_cover, h]

lemma ofCover_coverOf (u : C(Torus2, ℂ)) (hu : Smooth u) :
    ofCover (coverOf u) ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u) = u := by
  apply coverOf_injective
  rw [coverOf_ofCover]

end MathGauge.PublicProof.Torus
