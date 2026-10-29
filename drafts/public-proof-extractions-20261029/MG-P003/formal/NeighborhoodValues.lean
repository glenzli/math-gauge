import SheafificationStalk
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.Final

/-!
Actual small-site values on shrinking neighborhoods of a set of points and the
canonical sheafification comparison on those values. The index category is
proved filtered in the restriction direction; neither exactness of a motivic
cover nor bijectivity of the finite-point comparison is assumed or concluded.
-/

namespace MathGauge.PublicProof.Semilocal

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}

/-- Open neighborhoods of a point set, ordered by ordinary inclusion. -/
def SetNeighborhoods (s : Set X) := {U : Opens X // s ⊆ U}

instance (s : Set X) : PartialOrder (SetNeighborhoods s) :=
  inferInstanceAs (PartialOrder {U : Opens X // s ⊆ U})

instance (s : Set X) : Nonempty (SetNeighborhoods s) :=
  ⟨⟨⊤, fun _ _ => trivial⟩⟩

instance (s : Set X) : IsCodirectedOrder (SetNeighborhoods s) :=
  ⟨fun U V => ⟨⟨U.1 ⊓ V.1, fun _ hx => ⟨U.2 hx, V.2 hx⟩⟩,
    (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left),
    (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right)⟩⟩

/-- Restriction maps run over the opposite of the neighborhood order. -/
theorem neighborhood_index_filtered (s : Set X) : IsFiltered (SetNeighborhoods s)ᵒᵖ :=
  inferInstance

/-- The actual inclusion into the small topological site. -/
def neighborhood_inclusion (s : Set X) : SetNeighborhoods s ⥤ Opens X :=
  (show Monotone (fun U : SetNeighborhoods s => U.1) from fun _ _ h => h).functor

/-- The actual abelian-group colimit of sections on neighborhoods. -/
def neighborhood_value (F : TopCat.Presheaf AddCommGrpCat.{u} X) (s : Set X) :
    AddCommGrpCat.{u} :=
  colimit ((neighborhood_inclusion s).op ⋙ F)

/-- The map on neighborhood colimits induced by a genuine presheaf map. -/
def neighborhood_value_map {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (η : F ⟶ G) (s : Set X) : neighborhood_value F s ⟶ neighborhood_value G s :=
  colim.map (whiskerLeft (neighborhood_inclusion s).op η)

/-- On a representative, the map is precisely the original natural map. -/
theorem neighborhood_value_map_representative
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (η : F ⟶ G)
    (s : Set X) (U : SetNeighborhoods s) :
    colimit.ι ((neighborhood_inclusion s).op ⋙ F) (op U) ≫
      neighborhood_value_map η s =
    η.app (op U.1) ≫ colimit.ι ((neighborhood_inclusion s).op ⋙ G) (op U) := by
  exact colimit.ι_map (whiskerLeft (neighborhood_inclusion s).op η) (op U)

/-- Genuine filtered abelian-group colimits retain componentwise monomorphisms.
In the reference proof this can be applied after separatedness has been proved. -/
theorem neighborhood_value_map_injective
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (η : F ⟶ G) (s : Set X)
    (hη : ∀ U : Opens X, Function.Injective (η.app (op U))) :
    Function.Injective (neighborhood_value_map η s) := by
  haveI : Mono (whiskerLeft (neighborhood_inclusion s).op η) :=
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
      (AddCommGrpCat.mono_iff_injective _).mpr (hη U.unop.1)
  apply (AddCommGrpCat.mono_iff_injective _).mp
  change Mono (colim.map (whiskerLeft (neighborhood_inclusion s).op η))
  infer_instance

/-- The canonical small-site Zariski comparison on finite-point neighborhoods.
The target assertion that this map is an isomorphism for the task's transfer
presheaves is deliberately not declared as a theorem or assumed as a field. -/
def finite_neighborhood_sheafification_comparison
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (sigma : Finset X) :
    neighborhood_value F (sigma : Set X) ⟶
      neighborhood_value
        (CategoryTheory.sheafify (Opens.grothendieckTopology X) F) (sigma : Set X) :=
  neighborhood_value_map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F) (sigma : Set X)

/-- The singleton neighborhood system is the actual system defining a stalk. -/
def singleton_neighborhood_orderIso (x : X) :
    SetNeighborhoods ({x} : Set X) ≃o OpenNhds x where
  toFun U := ⟨U.1, U.2 (Set.mem_singleton x)⟩
  invFun U := ⟨U.1, fun y hy => (Set.mem_singleton_iff.mp hy) ▸ U.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The singleton case of the canonical neighborhood-colimit comparison,
identified with the actual stalk comparison through the neighborhood equivalence. -/
theorem singleton_neighborhood_value_comparison_isIso
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (x : X) :
    IsIso (neighborhood_value_map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F) ({x} : Set X)) := by
  let E := (singleton_neighborhood_orderIso x).equivalence.functor.op
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  let G := CategoryTheory.sheafify (Opens.grothendieckTopology X) F
  haveI hstalk : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    singleton_neighborhood_comparison_isIso X F x
  haveI hmap : IsIso (colim.map (whiskerLeft (OpenNhds.inclusion x).op η)) :=
    inferInstanceAs (IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η))
  haveI hpreF : IsIso (colimit.pre ((OpenNhds.inclusion x).op ⋙ F) E) := inferInstance
  haveI hpreG : IsIso (colimit.pre ((OpenNhds.inclusion x).op ⋙ G) E) := inferInstance
  have h := colimit.pre_map (whiskerLeft (OpenNhds.inclusion x).op η) E
  haveI : IsIso (colim.map (whiskerLeft E (whiskerLeft (OpenNhds.inclusion x).op η)) ≫
      colimit.pre ((OpenNhds.inclusion x).op ⋙ G) E) := by
    rw [← h]
    infer_instance
  change IsIso (colim.map (whiskerLeft E (whiskerLeft (OpenNhds.inclusion x).op η)))
  exact IsIso.of_isIso_comp_right _ (colimit.pre ((OpenNhds.inclusion x).op ⋙ G) E)

end

end MathGauge.PublicProof.Semilocal
