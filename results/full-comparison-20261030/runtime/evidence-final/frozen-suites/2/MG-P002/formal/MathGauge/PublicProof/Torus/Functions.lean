import MathGauge.PublicProof.Torus.Arithmetic
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Actual functions on `(ℝ / ℤ)²`, with normalized Haar measure.
Smoothness is defined by smoothness of the periodic pullback to `ℝ²`.
This file proves the actual Fourier coefficient and uniqueness statements;
it does not postulate a Fourier/rapid-decay equivalence. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal ContDiff

namespace MathGauge.PublicProof.Torus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Torus2 := UnitAddTorus (Fin 2)
abbrev Cover2 := Fin 2 → ℝ

def project (x : Cover2) : Torus2 := fun i => (x i : UnitAddCircle)

def pullback (u : Torus2 → ℂ) (x : Cover2) : ℂ := u (project x)

/-- Smooth actual torus functions, represented by their continuous function and
smooth periodic pullback. No Fourier conditions are included. -/
def Smooth (u : C(Torus2, ℂ)) : Prop := ContDiff ℝ ∞ (pullback u)

def MeanZero (u : Torus2 → ℂ) : Prop := ∫ y, u y = 0

def coeff (u : Torus2 → ℂ) (k : Frequency) : ℂ := UnitAddTorus.mFourierCoeff u k

def mode (k : Frequency) : C(Torus2, ℂ) := UnitAddTorus.mFourier k

/-- Intrinsic coordinate derivatives: differentiate the corresponding translation
curve on the quotient, so no representative of a torus point is chosen. -/
def coordinateDerivative (i : Fin 2) (u : Torus2 → ℂ) (y : Torus2) : ℂ :=
  deriv (fun t : ℝ => u (y + project (Pi.single i t))) 0

def transport (α : ℝ) (u : Torus2 → ℂ) (y : Torus2) : ℂ :=
  (α : ℂ) * coordinateDerivative 0 u y + coordinateDerivative 1 u y

/-- Repeated actual coordinate derivatives, in the order used by the task. -/
def mixedDerivative (a b : ℕ) (u : Torus2 → ℂ) : Torus2 → ℂ :=
  (coordinateDerivative 0)^[a] ((coordinateDerivative 1)^[b] u)

lemma coeff_zero (u : Torus2 → ℂ) : coeff u 0 = ∫ y, u y := by
  simp [coeff, UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero]

lemma meanZero_iff_coeff_zero (u : Torus2 → ℂ) : MeanZero u ↔ coeff u 0 = 0 := by
  rw [coeff_zero]
  rfl

lemma coeff_mode (k : Frequency) : coeff (mode k) = Pi.single k 1 := by
  ext j
  rw [coeff, ← UnitAddTorus.mFourierCoeff_toLp (f := mode k),
    ← UnitAddTorus.mFourierBasis_repr]
  have hb : (mode k).toLp 2 volume ℂ = UnitAddTorus.mFourierBasis k := by
    exact (congrFun UnitAddTorus.coe_mFourierBasis k).symm
  rw [hb, HilbertBasis.repr_self]
  simp only [lp.coeFn_single]

lemma mode_meanZero {k : Frequency} (hk : k ≠ 0) : MeanZero (mode k) := by
  rw [meanZero_iff_coeff_zero, coeff_mode]
  simp [hk.symm]

lemma mode_pullback (k : Frequency) (x : Cover2) :
    pullback (mode k) x =
      Complex.exp (2 * Real.pi * Complex.I * ((k 0 : ℂ) * x 0 + (k 1 : ℂ) * x 1)) := by
  simp only [pullback, mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    project, Fin.prod_univ_two, fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_add]
  congr 1
  ring

lemma mode_smooth (k : Frequency) : Smooth (mode k) := by
  change ContDiff ℝ ∞ (fun x : Cover2 => pullback (mode k) x)
  simp_rw [mode_pullback]
  have h0 : ContDiff ℝ ∞ (fun x : Cover2 => (x 0 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)
  have h1 : ContDiff ℝ ∞ (fun x : Cover2 => (x 1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)
  exact (contDiff_const.mul ((contDiff_const.mul h0).add (contDiff_const.mul h1))).cexp

lemma coeff_injective : Function.Injective (fun u : C(Torus2, ℂ) => coeff u) := by
  intro f g h
  have hp : f.toLp 2 volume ℂ = g.toLp 2 volume ℂ := by
    apply UnitAddTorus.mFourierBasis.repr.injective
    ext k
    simpa only [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp, coeff] using congrFun h k
  exact ContinuousMap.toLp_injective volume hp

end MathGauge.PublicProof.Torus
