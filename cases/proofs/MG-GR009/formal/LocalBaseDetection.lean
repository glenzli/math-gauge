import SheafBaseChange

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]
variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)
variable (B : Sheaf J (Type (max u v w))) (b : B ⟶ A.quotient_sheaf J)
variable (E : EquivariantOver A)

/-- Stabilizers are detected after a genuinely locally surjective sheaf base
change. The proof lifts the base section only on its covering image sieve. -/
theorem stabilizer_trivial_of_local_base [Presheaf.IsLocallySurjective J b.hom]
    (hE : (basechange_record A B b E).StabilizerTrivial) : E.StabilizerTrivial := by
  intro U e a ha
  let z := (A.quotient_projection J).app U (E.projection.hom.app U e)
  have hcov := Presheaf.imageSieve_mem J b.hom z
  apply (((isSheaf_iff_isSheaf_of_type J _).mp E.sheaf.property).isSeparated _ hcov).ext
  intro V f hf
  obtain ⟨c,hc⟩ := hf
  have hp : (E.projection ≫ quotient_hom A).hom.app (op V)
      (E.sheaf.obj.map f.op e)=b.hom.app (op V) c := by
    change (A.quotient_projection J).app (op V)
      (E.projection.hom.app (op V) (E.sheaf.obj.map f.op e))=b.hom.app (op V) c
    rw [← nat_restrict E.projection.hom,← nat_restrict (A.quotient_projection J)]
    exact hc.symm
  let ec : (basechange_record A B b E).sheaf.obj.obj (op V) :=
    ⟨(E.sheaf.obj.map f.op e,c),hp⟩
  have hfix : ((pullback_action A B b).act a).app (op V)
      ((basechange_record A B b E).projection.hom.app (op V) ec)=
      (basechange_record A B b E).projection.hom.app (op V) ec := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    change (A.act a).app (op V) (E.projection.hom.app (op V)
      (E.sheaf.obj.map f.op e))=E.projection.hom.app (op V) (E.sheaf.obj.map f.op e)
    rw [← nat_restrict E.projection.hom,← A.restrict_act,ha]
  have h := congrArg (fun x => x.val.1) (hE (op V) ec a hfix)
  change (E.action.act a).app (op V) (E.sheaf.obj.map f.op e)=E.sheaf.obj.map f.op e at h
  rw [E.action.restrict_act]
  exact h

theorem realizable_iff_local_base [Presheaf.IsLocallySurjective J b.hom] :
    E.Realizable ↔ (basechange_record A B b E).Realizable := by
  rw [E.realizable_iff_stabilizer_trivial,
    (basechange_record A B b E).realizable_iff_stabilizer_trivial]
  exact ⟨basechange_stabilizer_trivial A B b E,
    stabilizer_trivial_of_local_base A B b E⟩

end MathGauge.Descent
