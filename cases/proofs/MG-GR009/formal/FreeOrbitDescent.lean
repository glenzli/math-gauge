import FiniteOrbitSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite
universe u g w
namespace MathGauge.Descent.FiniteOrbit
variable {Γ : Type g} [Group Γ] [Finite Γ]
variable (T : Profinite.{u}) [MulAction Γ T] [ContinuousConstSMul Γ T]

/-- The empty covering family forces uniqueness of sections on the empty
test object; no point is chosen there. -/
theorem empty_test_subsingleton (E : ProfSheaf.{u,w}) (U : Profinite.{u}) [IsEmpty U] :
    Subsingleton (E.obj.obj (op U)) := by
  have hcov : (⊥ : Sieve U) ∈ ProfSite U := by
    rw [prof_cover_iff]
    exact ⟨Empty,inferInstance,(fun x => nomatch x),(fun x => nomatch x),
      (fun x => isEmptyElim x),(fun x => nomatch x)⟩
  constructor
  intro x y
  apply (((isSheaf_iff_isSheaf_of_type ProfSite _).mp E.property).isSeparated _ hcov).ext
  intro V f hf
  exact False.elim hf

theorem free_stabilizers_trivial
    (hfree : ∀ (a : Γ) (t : T), a • t=t → a=1)
    (E : EquivariantOver (action.{u,g,w} (Γ := Γ) T)) : E.StabilizerTrivial := by
  intro U e a ha
  by_cases hn : Nonempty U.unop
  · obtain ⟨x⟩ := hn
    have he := congrArg (fun f => f.down x) ha
    have hone : a=1 := hfree a ((E.projection.hom.app U e).down x) he
    subst a
    exact E.action.one_apply U e
  · letI : IsEmpty U.unop := not_nonempty_iff.mp hn
    letI := empty_test_subsingleton E.sheaf U.unop
    exact Subsingleton.elim _ _

theorem every_equivariant_realizable
    (hfree : ∀ (a : Γ) (t : T), a • t=t → a=1)
    (E : EquivariantOver (action.{u,g,w} (Γ := Γ) T)) : E.Realizable :=
  E.realizable_iff_stabilizer_trivial.mpr (free_stabilizers_trivial T hfree E)

end MathGauge.Descent.FiniteOrbit
