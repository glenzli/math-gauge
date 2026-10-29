import MappingExponential

noncomputable section
open TopologicalSpace Topology Set CategoryTheory Opposite
universe u
namespace MathGauge.Mapping

/-- The profinite probe presheaf appearing in MG-R010. -/
abbrev probe (X : Type u) [TopologicalSpace X] : Profinite.{u}ᵒᵖ ⥤ Type u where
  obj S := C(S.unop,X)
  map a f := f.comp a.unop.hom.hom

/-- The explicit ultrafilter profinite cover, without leaving the carrier universe. -/
def compact_cover (S : CompHaus.{u}) : Profinite.{u} := Profinite.of (Ultrafilter S)

def compact_cover_map (S : CompHaus.{u}) : C(compact_cover S,S) :=
  ⟨Ultrafilter.extend id, continuous_ultrafilter_extend id⟩

theorem compact_cover_surjective (S : CompHaus.{u}) :
    Function.Surjective (compact_cover_map S) := by
  intro s
  exact ⟨pure s, congr_fun (ultrafilter_extend_extends (id : S → S)) s⟩

theorem compact_cover_quotient (S : CompHaus.{u}) : IsQuotientMap (compact_cover_map S) :=
  IsQuotientMap.of_surjective_continuous (compact_cover_surjective S)
    (compact_cover_map S).continuous

theorem continuous_from_kify_profinite {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : Kify X → Y)
    (h : ∀ (S : Profinite.{u}) (g : C(S,X)), Continuous (fun s => f (kup (g s)))) :
    Continuous f := by
  apply continuous_from_kify
  intro S g
  apply (compact_cover_quotient S).continuous_iff.mpr
  exact h (compact_cover S) (g.comp (compact_cover_map S))

theorem compact_profinite_detection {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) :
    (∀ (S : Profinite.{u}) (g : C(S,X)), Continuous (f ∘ g)) ↔
    (∀ (S : CompHaus.{u}) (g : C(S,X)), Continuous (f ∘ g)) := by
  constructor
  · intro h S g
    apply (compact_cover_quotient S).continuous_iff.mpr
    exact h (compact_cover S) (g.comp (compact_cover_map S))
  · intro h S g
    exact h (CompHaus.of S) g

theorem kify_isOpen_iff {X : Type u} [TopologicalSpace X] (O : Set (Kify X)) :
    IsOpen O ↔ ∀ (S : CompHaus.{u}) (f : C(S,X)), IsOpen ((fun s => kup (f s)) ⁻¹' O) := by
  change IsOpen[TopologicalSpace.compactlyGenerated.{u} X] O ↔ _
  rw [TopologicalSpace.compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff]
  exact ⟨fun h S f => h ⟨S,f⟩, fun h ⟨S,f⟩ => h S f⟩

theorem kify_isOpen_iff_profinite {X : Type u} [TopologicalSpace X] (O : Set (Kify X)) :
    IsOpen O ↔ ∀ (S : Profinite.{u}) (f : C(S,X)), IsOpen ((fun s => kup (f s)) ⁻¹' O) := by
  constructor
  · intro h S f
    exact h.preimage (continuous_kprobe (CompHaus.of S) f)
  · intro h
    apply (kify_isOpen_iff O).mpr
    intro S f
    apply (compact_cover_quotient S).isOpen_preimage.mp
    exact h (compact_cover S) (f.comp (compact_cover_map S))

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def probe_point (η : probe X ⟶ probe Y) : X → Y :=
  fun x => η.app (op (Profinite.of PUnit.{u+1})) (ContinuousMap.const _ x) PUnit.unit

theorem probe_naturality_point (η : probe X ⟶ probe Y) (S : Profinite.{u})
    (f : C(S,X)) (s : S) : η.app (op S) f s = probe_point η (f s) := by
  let cs : Profinite.of PUnit.{u+1} ⟶ S :=
    CompHausLike.ofHom _ (ContinuousMap.const _ s)
  have h := congrArg (fun a : C(PUnit.{u+1},Y) => a PUnit.unit)
    (ConcreteCategory.congr_hom (η.naturality cs.op) f)
  exact h.symm

theorem continuous_probe_point (η : probe X ⟶ probe Y) :
    Continuous (fun x : Kify X => probe_point η (kdown x)) := by
  apply continuous_from_kify_profinite
  intro S f
  have heq : (fun s : S => probe_point η (f s)) = (η.app (op S) f) := by
    funext s
    exact (probe_naturality_point η S f s).symm
  rw [show (fun s : S => probe_point η (kdown (kup (f s)))) =
    (fun s : S => probe_point η (f s)) from rfl, heq]
  exact (η.app (op S) f).continuous

def probe_to_map (η : probe X ⟶ probe Y) : C(Kify X,Kify Y) :=
  ⟨fun x => kup (probe_point η (kdown x)), continuous_into_kify (continuous_probe_point η)⟩

def map_to_probe (f : C(Kify X,Kify Y)) : probe X ⟶ probe Y where
  app S g := ⟨fun s => kdown (f (kup (g s))),
    (continuous_kdown Y).comp (f.continuous.comp (continuous_kprobe (CompHaus.of S.unop) g))⟩
  naturality := by
    intro S T a
    ext g s
    rfl

/-- All natural transformations, with their actual functions, are classified. -/
def probe_map_equiv : (probe X ⟶ probe Y) ≃ C(Kify X,Kify Y) where
  toFun := probe_to_map
  invFun := map_to_probe
  left_inv η := by
    ext S f s
    exact (probe_naturality_point η S.unop f s).symm
  right_inv f := by ext x; rfl

@[simp] theorem map_to_probe_id : map_to_probe (ContinuousMap.id (Kify X)) = 𝟙 (probe X) := by
  ext S f s
  rfl

@[simp] theorem map_to_probe_comp (f : C(Kify X,Kify Y)) (g : C(Kify Y,Kify Z)) :
    map_to_probe (g.comp f) = map_to_probe f ≫ map_to_probe g := by
  ext S a s
  rfl

end MathGauge.Mapping
