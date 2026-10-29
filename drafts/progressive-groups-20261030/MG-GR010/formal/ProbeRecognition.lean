import MappingTopologyBoundary
import MappingEvaluationBoundary

noncomputable section
open TopologicalSpace Topology Set CategoryTheory Opposite
universe u
namespace MathGauge.GR010.ProbeRecognition
open MathGauge.Mapping

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The quantifier is over all Hausdorff target spaces in the original universe. -/
def OriginalFull (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [T2Space Y] (η : probe X ⟶ probe Y),
    ∃ f : C(X,Y), probe_post f=η

theorem all_probes_original_iff [T2Space X] :
    OriginalFull X ↔ UCompactlyGeneratedSpace.{u} X := by
  constructor
  · intro h
    obtain ⟨f,hf⟩ := h (Kify X) (probe_kify_iso X).hom
    have he : (f : X → Kify X)=kup := by
      funext x
      exact congrArg (fun η => probe_point η x) hf
    have hk : Continuous (kup : X → Kify X) := he ▸ f.continuous
    apply uCompactlyGeneratedSpace_of_continuous_maps
    intro Z _ g hg
    have hgk : Continuous (fun x : Kify X => g (kdown x)) :=
      continuous_from_kify _ (fun S f => hg S f)
    exact hgk.comp hk
  · intro h
    letI := h
    intro Y _ _ η
    let f : C(X,Y) := ⟨probe_point η,
      (continuous_probe_point η).comp (continuous_into_kify (continuous_id (X := X)))⟩
    refine ⟨f,?_⟩
    ext S g s
    exact (probe_naturality_point η S.unop g s).symm

theorem first_countable_compactly_generated [FirstCountableTopology X] :
    UCompactlyGeneratedSpace.{u} X := inferInstance

theorem first_countable_topology [FirstCountableTopology X] :
    TopologicalSpace.compactlyGenerated.{u} X = (inferInstance : TopologicalSpace X) :=
  eq_compactlyGenerated.symm

def homeoProbeIso (e : Kify X ≃ₜ Kify Y) : probe X ≅ probe Y where
  hom := map_to_probe ⟨e,e.continuous⟩
  inv := map_to_probe ⟨e.symm,e.symm.continuous⟩
  hom_inv_id := by ext S g s; exact congrArg kdown (e.symm_apply_apply (kup (g s)))
  inv_hom_id := by ext S g s; exact congrArg kdown (e.apply_symm_apply (kup (g s)))

/-- This is the homeomorphism of the actual map kf, not an arbitrary
homeomorphism between the same two spaces. -/
theorem isIso_iff_khomeomorph (f : C(X,Y)) :
    IsIso (probe_post f) ↔
      ∃ e : Kify X ≃ₜ Kify Y, ∀ x,e x=kmap f x := by
  constructor
  · intro h
    letI := h
    exact ⟨probe_iso_homeo (asIso (probe_post f)),fun _ => rfl⟩
  · rintro ⟨e,he⟩
    have hh : (homeoProbeIso e).hom=probe_post f := by
      ext S g s
      exact congrArg kdown (he (kup (g s)))
    rw [← hh]
    infer_instance

def firstCountableHomeomorph [FirstCountableTopology X] [FirstCountableTopology Y]
    (f : C(X,Y)) [IsIso (probe_post f)] : X ≃ₜ Y :=
  (kify_homeo X).symm.trans
    ((probe_iso_homeo (asIso (probe_post f))).trans (kify_homeo Y))

@[simp] theorem firstCountableHomeomorph_apply [FirstCountableTopology X]
    [FirstCountableTopology Y] (f : C(X,Y)) [IsIso (probe_post f)] (x : X) :
    firstCountableHomeomorph f x=f x := rfl

/-- The actual identity from the discrete kification has an isomorphic
probe functor but is not a homeomorphism of the original topologies. -/
theorem fortissimo_counterexample (D : Type u) [Uncountable D] :
    let f : C(Kify (Fortissimo D),Fortissimo D) := ⟨kdown,continuous_kdown _⟩
    IsIso (probe_post f) ∧
      ¬ ∃ e : Kify (Fortissimo D) ≃ₜ Fortissimo D, ∀ x,e x=f x := by
  dsimp only
  constructor
  · change IsIso (probe_kify_iso (Fortissimo D)).inv
    infer_instance
  · rintro ⟨e,he⟩
    have heinv : (e.symm : Fortissimo D → Kify (Fortissimo D))=kup := by
      funext x
      apply e.injective
      rw [e.apply_symm_apply,he]
      rfl
    exact fortissimo_not_continuous_to_kify D (heinv ▸ e.symm.continuous)

theorem concrete_fortissimo_counterexample :
    let f : C(Kify (Fortissimo (Set ℕ)),Fortissimo (Set ℕ)) := ⟨kdown,continuous_kdown _⟩
    IsIso (probe_post f) ∧
      ¬ ∃ e : Kify (Fortissimo (Set ℕ)) ≃ₜ Fortissimo (Set ℕ), ∀ x,e x=f x := by
  letI := powerset_nat_uncountable
  exact fortissimo_counterexample (Set ℕ)

end MathGauge.GR010.ProbeRecognition
