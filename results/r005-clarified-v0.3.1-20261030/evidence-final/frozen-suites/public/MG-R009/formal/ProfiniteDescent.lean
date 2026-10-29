import SheafBaseChange
import MappingUniverse

noncomputable section
open CategoryTheory Opposite
universe u g w
namespace MathGauge.Descent

abbrev ProfSite := coherentTopology Profinite.{u}
abbrev ProfSheaf := Sheaf ProfSite.{u} (Type (max (u + 1) w))

theorem prof_cover_iff {U : Profinite.{u}} (S : Sieve U) : S ∈ ProfSite U ↔
    ∃ (ι : Type) (_ : Finite ι) (V : ι → Profinite.{u})
      (f : (i : ι) → V i ⟶ U),
      (∀ x : U, ∃ (i : ι) (y : V i), f i y = x) ∧ (∀ i, S (f i)) := by
  rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily]
  constructor
  · rintro ⟨ι,hι,V,f,hf,hS⟩
    exact ⟨ι,hι,V,f,((Profinite.effectiveEpiFamily_tfae V f).out 0 2).mp hf,hS⟩
  · rintro ⟨ι,hι,V,f,hf,hS⟩
    exact ⟨ι,hι,V,f,Profinite.effectiveEpiFamily_of_jointly_surjective V f hf,hS⟩

/-- The actual probe sheaf with the larger value universe required in the question. -/
abbrev prof_probe_sheaf (X : Type u) [TopologicalSpace X] : ProfSheaf.{u,w} where
  obj := MathGauge.Mapping.probeV.{u,max (u+1) w} X
  property := by
    let h := (TopCat.toSheafCompHausLike.{u,u} (fun X => TotallyDisconnectedSpace X)
      (TopCat.of X) (fun _ _ f h => ((Profinite.effectiveEpi_tfae f).out 0 2).mp h)).property
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact Presieve.isSheaf_comp_uliftFunctor _ h

/-- A group homomorphism into homeomorphisms, stated as its pointwise action laws. -/
structure SpaceAction (Γ : Type g) [Group Γ] (X : Type u) [TopologicalSpace X] where
  act : Γ → X ≃ₜ X
  one : ∀ x, act 1 x = x
  mul : ∀ a b x, act (a*b) x = act a (act b x)

namespace SpaceAction
variable {Γ : Type g} [Group Γ] {X : Type u} [TopologicalSpace X]

def probe_action (A : SpaceAction Γ X) : PAction (Γ := Γ) (prof_probe_sheaf.{u,w} X).obj where
  act a := {
    app U f := ⟨⟨fun x => A.act a (f.down x),(A.act a).continuous.comp f.down.continuous⟩⟩
    naturality := by intro U V f; rfl }
  one := by ext U f x; exact A.one (f.down x)
  mul a b := by ext U f x; exact A.mul a b (f.down x)

/-- The requested profinite-space theorem is an instance of the proved sheaf classification. -/
def classification (T : Profinite.{u}) (A : SpaceAction Γ T) :
    let a : PAction (Γ := Γ) (prof_probe_sheaf.{u,w} T).obj := A.probe_action
    Over (a.quotient_sheaf ProfSite) ≌ StableEquivariant a :=
  descent_equivalence A.probe_action

end SpaceAction
end MathGauge.Descent
