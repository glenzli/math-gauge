import InputTransport
import Partitions
import FiniteResidual
import PathBounds
import TerminationBoundary

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype V] [Fintype E] [Fintype I] {g : Gauge Y I}

/-- The conjunction requested by the task: literal uniqueness and finite uniform geometric error. -/
def StrongClosure (s : System Y V E I g) : Prop :=
  ∃ F : s.Family, s.transform F=F ∧ (∀ G, s.transform G=G → G=F) ∧
    ∃ q : ℝ≥0, 0<q ∧ q<1 ∧ ∀ H : s.Family, ∃ C : ℝ≥0,
      ∀ n : ℕ, 1≤n → (⨆ vi, s.delta (s.transform^[n] H) F vi) ≤ (C : ℝ≥0∞)*(q : ℝ≥0∞)^n

theorem strongClosure_unique (s : System Y V E I g) (h : s.StrongClosure) :
    ∃! F : s.Family, s.transform F=F := by
  obtain ⟨F,hF,hu,_⟩ := h
  exact ⟨F,hF,hu⟩

end MathGauge.RecursiveClosure.System
namespace MathGauge.RecursiveClosure.Counterexample

theorem full_target_false : ¬sys.StrongClosure :=
  fun h => not_unique_fixed (sys.strongClosure_unique h)

theorem full_subset_target_false : ¬subsetSystem.StrongClosure :=
  fun h => subset_system_not_unique (subsetSystem.strongClosure_unique h)

/-- The literal aggregate has the stated spectral bound although the complete target fails. -/
theorem spectral_does_not_imply_full_target :
    spectralRadius ℂ (complexMatrix sys.coeff)<1 ∧ ¬sys.StrongClosure := by
  constructor
  · rw [actual_spectral_eq_half]; norm_num
  · exact full_target_false

/-- Even the selected zero fixed family admits no finite bound from this legitimate initial family. -/
theorem no_finite_geometric_error : ¬∃ q C : ℝ≥0, ∀ n : ℕ, 1≤n →
    (⨆ vi, sys.delta (sys.transform^[n] initial) (solution 0) vi) ≤ (C : ℝ≥0∞)*(q : ℝ≥0∞)^n := by
  rintro ⟨q,C,h⟩
  obtain ⟨vi,hvi⟩ := error_top_every_depth 1
  have hh := (le_iSup (fun vi => sys.delta (sys.transform^[1] initial) (solution 0) vi) vi).trans (h 1 le_rfl)
  rw [hvi] at hh
  exact (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)) (top_le_iff.mp hh)

end MathGauge.RecursiveClosure.Counterexample
namespace MathGauge.RecursiveClosure.Obstructions

def singletonEquiv {Y : Type} (y : Y) : {x : Y // x=y} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨y,rfl⟩
  left_inv x := Subtype.ext x.property.symm
  right_inv x := by cases x; rfl

def positiveSubset := positiveSystem.transportInputs
  (fun _ => {x : Positive // x=(⟨1,by norm_num⟩ : Positive)}) (fun _ => singletonEquiv (⟨1,by norm_num⟩ : Positive))

def swapSubset := swapSystem.transportInputs
  (fun _ => {x : Bool // x=false}) (fun _ => singletonEquiv false)

theorem positive_subset_no_fixed : ¬∃ F : positiveSubset.Family, positiveSubset.transform F=F := by
  rintro ⟨F,hF⟩
  let e := positiveSystem.familyTransport _ (fun _ => singletonEquiv (⟨1,by norm_num⟩ : Positive))
  apply positive_no_fixed
  refine ⟨e.symm F, ?_⟩
  apply (positiveSystem.fixed_transport _ (fun _ => singletonEquiv (⟨1,by norm_num⟩ : Positive)) _).mp
  change positiveSubset.transform (e (e.symm F))=e (e.symm F)
  simpa only [Equiv.apply_symm_apply] using hF

theorem swap_subset_no_fixed : ¬∃ F : swapSubset.Family, swapSubset.transform F=F := by
  rintro ⟨F,hF⟩
  let e := swapSystem.familyTransport _ (fun _ => singletonEquiv false)
  apply swap_no_fixed
  refine ⟨e.symm F, ?_⟩
  apply (swapSystem.fixed_transport _ (fun _ => singletonEquiv false) _).mp
  change swapSubset.transform (e (e.symm F))=e (e.symm F)
  simpa only [Equiv.apply_symm_apply] using hF

end MathGauge.RecursiveClosure.Obstructions
