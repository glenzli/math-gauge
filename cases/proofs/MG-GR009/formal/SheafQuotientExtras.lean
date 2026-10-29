import SheafBaseChange

noncomputable section
open CategoryTheory Opposite
universe u v g w
namespace MathGauge.Descent
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Type g} [Group Γ]
variable {H : Sheaf J (Type (max u v w))} (A : PAction (Γ := Γ) H.obj)

def PAction.actIso (a : Γ) : H.obj ≅ H.obj where
  hom := A.act a
  inv := A.act a⁻¹
  hom_inv_id := by rw [← A.mul,inv_mul_cancel,A.one]
  inv_hom_id := by rw [← A.mul,mul_inv_cancel,A.one]

theorem EquivariantOver.comparison_isIso_iff (E : EquivariantOver A) :
    IsIso E.comparison ↔ E.StabilizerTrivial := by
  constructor
  · intro hi
    letI := hi
    apply E.realizable_iff_stabilizer_trivial.mp
    exact ⟨E.action.quotient_sheaf J,E.quotient_to_base,@asIso _ _ _ _ E.comparison hi,rfl,
      E.comparison_equivariant⟩
  · exact E.comparison_isIso

/-- The actual local-orbit kernel pair, with no representability assumption. -/
theorem quotient_kernel_condition (U : Cᵒᵖ) (x y : H.obj.obj U) :
    (A.quotient_projection J).app U x = (A.quotient_projection J).app U y ↔
      A.local_orbit_sieve x y ∈ J U.unop := A.quotient_eq_iff_local_orbit J U x y

/-- The quotient is the coequalizer of its actual kernel pair. -/
theorem quotient_kernel_universal (Y : Sheaf J (Type (max u v w))) (b : H ⟶ Y)
    (hb : fibre_fst_hom (quotient_hom A) (quotient_hom A) ≫ b =
      fibre_snd_hom (quotient_hom A) (quotient_hom A) ≫ b) :
    ∃! f : A.quotient_sheaf J ⟶ Y, quotient_hom A ≫ f = b := by
  have hi : A.Invariant b.hom := by
    intro a
    ext U x
    let z : (fibre_sheaf (quotient_hom A) (quotient_hom A)).obj.obj U :=
      ⟨((A.act a).app U x,x),congrArg (fun η => η.app U x) (A.quotient_invariant J a)⟩
    exact congrArg (fun η => η.hom.app U z) hb
  refine ⟨A.quotient_lift J Y b.hom hi,?_,?_⟩
  · exact Sheaf.hom_ext (A.quotient_lift_fac J Y b.hom hi)
  · intro f hf
    apply Sheaf.hom_ext
    apply A.quotient_hom_ext J Y
    exact (congrArg (fun η => η.hom) hf).trans (A.quotient_lift_fac J Y b.hom hi).symm

/-- Local group labels do not add a stabilizer condition beyond the testwise one. -/
theorem EquivariantOver.local_stabilizer (E : EquivariantOver A) (hE : E.StabilizerTrivial)
    (U : Cᵒᵖ) (e e' : E.sheaf.obj.obj U) (S : Sieve U.unop) (hS : S ∈ J U.unop)
    (hlocal : ∀ (V : C) (f : V ⟶ U.unop), S f →
      ∃ a : Γ, (A.act a).app (op V) (H.obj.map f.op (E.projection.hom.app U e)) =
        H.obj.map f.op (E.projection.hom.app U e) ∧
      E.sheaf.obj.map f.op e' = (E.action.act a).app (op V) (E.sheaf.obj.map f.op e)) :
    e' = e := by
  apply (((isSheaf_iff_isSheaf_of_type J _).mp E.sheaf.property).isSeparated S hS).ext
  intro V f hf
  obtain ⟨a,ha,he⟩ := hlocal V f hf
  rw [he]
  apply hE (op V) (E.sheaf.obj.map f.op e) a
  simpa only [← nat_restrict E.projection.hom] using ha

end MathGauge.Descent
