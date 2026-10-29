import Mathlib.CategoryTheory.Sites.LocallyBijective

/- The four arguments below extend mathlib's concrete plus/sheafification locality lemmas
   from Type (max u v) to any containing value universe Type (max u v w).
   They use the same actual covering representatives and refinement relation. -/
noncomputable section
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology.Plus
universe u v w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

instance large_local_surjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S,x,rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y,f,hf⟩,?_⟩) S.2
    rw [toPlus_eq_mk,res_mk_eq_mk_pullback,eq_mk_iff_exists]
    refine ⟨S.pullback f,homOfLE le_top,𝟙 _,?_⟩
    ext ⟨Z,g,hg⟩
    simpa using x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

instance large_local_injective_toPlus (P : Cᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    rw [toPlus_eq_mk,toPlus_eq_mk,eq_mk_iff_exists] at h
    obtain ⟨W,h₁,h₂,eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y,f,hf⟩) W.2

set_option backward.isDefEq.respectTransparency false in
instance large_local_surjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallySurjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance large_local_injective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallyInjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

end MathGauge.Descent
