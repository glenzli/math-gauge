import Limits
import Extra
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype I] {g : Gauge Y I}
variable (s : System Y V E I g) (Z : V → Type) (e : ∀ v, Z v ≃ s.Input v)

def transportInputs : System Y V E I g where
  Input := Z
  src := s.src
  dst := s.dst
  step v x := (s.step v (e v x)).map id (fun ⟨a,z⟩ => ⟨a,(e (s.dst a)).symm z⟩)
  step_src := by
    intro v x a z h
    cases hs : s.step v (e v x) with
    | inl y => simp [hs] at h
    | inr az =>
      rcases az with ⟨a',z'⟩
      simp only [hs,Sum.map_inr,Sum.inr.injEq] at h
      have ha : a'=a := congrArg Sigma.fst h
      subst a
      exact s.step_src v (e v x) a' z' hs
  ret := s.ret
  L := s.L
  lip := s.lip

def familyTransport : s.Family ≃ (s.transportInputs Z e).Family where
  toFun F v x := F v (e v x)
  invFun F v x := F v ((e v).symm x)
  left_inv F := by funext v x; simp
  right_inv F := by funext v x; simp

theorem transform_transport (F : s.Family) :
    (s.transportInputs Z e).transform (s.familyTransport Z e F)=
      s.familyTransport Z e (s.transform F) := by
  funext v x
  change (s.transportInputs Z e).transform (fun v x => F v (e v x)) v x=s.transform F v (e v x)
  cases h : s.step v (e v x) with
  | inl y => simp [transform,transportInputs,familyTransport,h]
  | inr az =>
    rcases az with ⟨a,z⟩
    simp [transform,transportInputs,familyTransport,h]
    exact congrArg (fun u => s.ret a (F (s.dst a) u)) ((e (s.dst a)).apply_symm_apply z)

theorem fixed_transport (F : s.Family) :
    (s.transportInputs Z e).transform (s.familyTransport Z e F)=s.familyTransport Z e F ↔
      s.transform F=F := by
  rw [s.transform_transport Z e]
  exact (s.familyTransport Z e).injective.eq_iff

theorem delta_transport (F G : s.Family) (vi : V × I) :
    (s.transportInputs Z e).delta (s.familyTransport Z e F) (s.familyTransport Z e G) vi=s.delta F G vi := by
  apply le_antisymm
  · apply iSup_le; intro x; exact s.point_le_delta F G _ _ (e vi.1 x)
  · apply iSup_le; intro x
    have hh := (s.transportInputs Z e).point_le_delta (s.familyTransport Z e F)
      (s.familyTransport Z e G) vi.1 vi.2 ((e vi.1).symm x)
    simpa [familyTransport] using hh

end MathGauge.RecursiveClosure.System
namespace MathGauge.RecursiveClosure.Counterexample

def subsetSystem := sys.transportInputs (fun _ => Set.range inputEmbedding) (fun _ => actualInputEquiv.symm)

theorem subset_system_not_unique : ¬∃! F : subsetSystem.Family, subsetSystem.transform F=F := by
  intro h
  obtain ⟨F,hF,hU⟩ := h
  let e := sys.familyTransport (fun _ => Set.range inputEmbedding) (fun _ => actualInputEquiv.symm)
  apply not_unique_fixed
  refine ⟨e.symm F, ?_, ?_⟩
  · apply (sys.fixed_transport (fun _ => Set.range inputEmbedding) (fun _ => actualInputEquiv.symm) _).mp
    change subsetSystem.transform (e (e.symm F))=e (e.symm F)
    simpa only [Equiv.apply_symm_apply] using hF
  · intro G hG
    apply e.injective
    exact (hU (e G) ((sys.fixed_transport _ _ _).mpr hG)).trans (e.apply_symm_apply F).symm

/-- The spectrum computation is transported to the original node-by-component index set. -/
theorem actual_spectral_eq_half : spectralRadius ℂ (complexMatrix sys.coeff)=(1/2 : ℝ≥0∞) := by
  let e : Fin 4 ≃ Bool × Fin 2 := Equiv.ofBijective ix ix_bijective
  have he : Matrix.reindexAlgEquiv ℂ ℂ e M=complexMatrix sys.coeff := by
    ext i j
    change M (e.symm i) (e.symm j)=complexMatrix sys.coeff i j
    rw [M_is_aggregate]
    change ((sys.coeff (e (e.symm i)) (e (e.symm j)) : ℝ≥0) : ℂ)=_
    simp [complexMatrix]
  rw [← he]
  unfold spectralRadius
  rw [AlgEquiv.spectrum_eq]
  exact matrix_spectral_eq_half

end MathGauge.RecursiveClosure.Counterexample
