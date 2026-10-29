import NeighborhoodValues
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The cofinality in S3 is proved for the actual neighborhood category and
the actual abelian-group presheaf colimit. No separation, smoothness, or
finite-point hypothesis is needed for this stronger elementary statement. -/

namespace MathGauge.GP003

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open TopologicalSpace Opposite
open MathGauge.PublicProof.Semilocal

universe u
variable {X : TopCat.{u}} (s : Set X) (W : Opens X) (hsW : s ⊆ W)

def RestrictedNeighborhoods := {U : SetNeighborhoods s // U.1 ≤ W}

instance : PartialOrder (RestrictedNeighborhoods s W) :=
  inferInstanceAs (PartialOrder {U : SetNeighborhoods s // U.1 ≤ W})

def restrictedInclusion : RestrictedNeighborhoods s W ⥤ SetNeighborhoods s :=
  (show Monotone (fun U : RestrictedNeighborhoods s W => U.1) from
    fun _ _ h => h).functor

def intersectNeighborhood : SetNeighborhoods s ⥤ RestrictedNeighborhoods s W :=
  (show Monotone (fun U : SetNeighborhoods s =>
    (⟨⟨U.1 ⊓ W, fun x hx => ⟨U.2 hx, hsW hx⟩⟩, inf_le_right⟩ :
      RestrictedNeighborhoods s W)) from
    fun _ _ h => inf_le_inf_right W h).functor

def inclusionIntersectionAdjunction :
    restrictedInclusion s W ⊣ intersectNeighborhood s W hsW :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun U => homOfLE (show U.1.1 ≤ U.1.1 ⊓ W from le_inf le_rfl U.2)
          naturality := fun _ _ _ => Subsingleton.elim _ _ }
      counit :=
        { app := fun U => homOfLE (show U.1 ⊓ W ≤ U.1 from inf_le_left)
          naturality := fun _ _ _ => Subsingleton.elim _ _ }
      left_triangle := by ext; exact Subsingleton.elim _ _
      right_triangle := by ext; exact Subsingleton.elim _ _ }

include hsW in
theorem restrictedInclusion_final : (restrictedInclusion s W).op.Final := by
  haveI : (restrictedInclusion s W).Initial :=
    Functor.initial_of_adjunction (inclusionIntersectionAdjunction s W hsW)
  infer_instance

include hsW in
theorem exists_restricted_refinement (U : SetNeighborhoods s) :
    ∃ V : RestrictedNeighborhoods s W, V.1 ≤ U :=
  ⟨(intersectNeighborhood s W hsW).obj U, (show U.1 ⊓ W ≤ U.1 from inf_le_left)⟩

def restrictedNeighborhoodValue (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    AddCommGrpCat.{u} :=
  colimit ((restrictedInclusion s W).op ⋙ (neighborhood_inclusion s).op ⋙ F)

def restrictedNeighborhoodComparison (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    restrictedNeighborhoodValue s W F ⟶ neighborhood_value F s :=
  colimit.pre ((neighborhood_inclusion s).op ⋙ F) (restrictedInclusion s W).op

include hsW in
theorem restrictedNeighborhoodComparison_isIso
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    IsIso (restrictedNeighborhoodComparison s W F) := by
  haveI := restrictedInclusion_final s W hsW
  unfold restrictedNeighborhoodComparison
  exact Functor.Final.colimit_pre_isIso (restrictedInclusion s W).op
    (G := (neighborhood_inclusion s).op ⋙ F)

def restrictedNeighborhoodIso (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    restrictedNeighborhoodValue s W F ≅ neighborhood_value F s := by
  haveI := restrictedNeighborhoodComparison_isIso s W hsW F
  exact asIso (restrictedNeighborhoodComparison s W F)

theorem restrictedNeighborhoodComparison_representative
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (U : RestrictedNeighborhoods s W) :
    colimit.ι ((restrictedInclusion s W).op ⋙ (neighborhood_inclusion s).op ⋙ F) (op U) ≫
      restrictedNeighborhoodComparison s W F =
    colimit.ι ((neighborhood_inclusion s).op ⋙ F) (op U.1) := by
  exact colimit.ι_pre ((neighborhood_inclusion s).op ⋙ F) (restrictedInclusion s W).op (op U)

end
end MathGauge.GP003
