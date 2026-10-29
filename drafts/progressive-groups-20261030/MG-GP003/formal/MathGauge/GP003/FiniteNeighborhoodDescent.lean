import MathGauge.GP003.FiniteGermDescent
import NeighborhoodValues

/-! Descent directly for the neighborhood-colimit extension specified in S1.
No assumption that the selected points detect all opens of the ambient scheme
is imposed. A finite compatible family glues on their union neighborhood. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open MathGauge.PublicProof.Semilocal

universe u
variable {X : TopCat.{u}}

def neighborhoodGerm (F : X.Presheaf AddCommGrpCat.{u}) (s : Set X) (x : X) (hx : x ∈ s) :
    neighborhood_value F s ⟶ F.stalk x :=
  colimit.desc ((neighborhood_inclusion s).op ⋙ F)
    { pt := F.stalk x
      ι :=
        { app := fun U => F.germ U.unop.1 x (U.unop.2 hx)
          naturality := by
            intro U V f
            exact F.germ_res ((neighborhood_inclusion s).map f.unop) x (V.unop.2 hx) } }

@[simp] theorem neighborhoodGerm_representative (F : X.Presheaf AddCommGrpCat.{u})
    (s : Set X) (x : X) (hx : x ∈ s) (U : SetNeighborhoods s) :
    colimit.ι ((neighborhood_inclusion s).op ⋙ F) (op U) ≫ neighborhoodGerm F s x hx =
      F.germ U.1 x (U.2 hx) := colimit.ι_desc _ _

variable {ι : Type u} (x : ι → X)

def neighborhoodGermFamily (F : X.Presheaf AddCommGrpCat.{u}) :
    neighborhood_value F (Set.range x) →+ ∀ i, F.stalk (x i) where
  toFun a i := neighborhoodGerm F (Set.range x) (x i) ⟨i,rfl⟩ a
  map_zero' := by funext i; exact map_zero _
  map_add' a b := by funext i; exact map_add _ a b

@[simp] theorem neighborhoodGermFamily_representative
    (F : X.Presheaf AddCommGrpCat.{u}) (U : SetNeighborhoods (Set.range x))
    (a : F.obj (op U.1)) (i : ι) :
    neighborhoodGermFamily x F (colimit.ι ((neighborhood_inclusion (Set.range x)).op ⋙ F) (op U) a) i =
      F.germ U.1 (x i) (U.2 ⟨i,rfl⟩) a := by
  change neighborhoodGerm F (Set.range x) (x i) ⟨i,rfl⟩
    (colimit.ι ((neighborhood_inclusion (Set.range x)).op ⋙ F) (op U) a) = _
  exact ConcreteCategory.congr_hom (neighborhoodGerm_representative F (Set.range x)
    (x i) ⟨i,rfl⟩ U) a

/-- Even for an infinite family, equality of all selected germs is equality
in the actual neighborhood colimit of a sheaf. -/
theorem neighborhood_germs_injective (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (neighborhoodGermFamily x G.obj) := by
  intro a b hab
  let F := (neighborhood_inclusion (Set.range x)).op ⋙ G.obj
  obtain ⟨U,a,rfl⟩ := Concrete.colimit_exists_rep F a
  obtain ⟨V,b,rfl⟩ := Concrete.colimit_exists_rep F b
  have he i : (TopCat.Presheaf.germ G.obj) U.unop.1 (x i) (U.unop.2 ⟨i,rfl⟩) a =
      (TopCat.Presheaf.germ G.obj) V.unop.1 (x i) (V.unop.2 ⟨i,rfl⟩) b := by
    have hh := congrFun hab i
    change neighborhoodGermFamily x G.obj
      (colimit.ι ((neighborhood_inclusion (Set.range x)).op ⋙ G.obj) (op U.unop) a) i =
        neighborhoodGermFamily x G.obj
          (colimit.ι ((neighborhood_inclusion (Set.range x)).op ⋙ G.obj) (op V.unop) b) i at hh
    simpa only [neighborhoodGermFamily_representative] using hh
  choose W hx hWU hWV hW using fun i => (TopCat.Presheaf.germ_eq G.obj) (x i)
    (U.unop.2 ⟨i,rfl⟩) (V.unop.2 ⟨i,rfl⟩) a b (he i)
  let Z : SetNeighborhoods (Set.range x) :=
    ⟨iSup W, by rintro _ ⟨i,rfl⟩; exact (le_iSup W i) (hx i)⟩
  have hZU : Z.1 ≤ U.unop.1 := iSup_le fun i => (hWU i).le
  have hZV : Z.1 ≤ V.unop.1 := iSup_le fun i => (hWV i).le
  have hlocal : G.obj.map (homOfLE hZU).op a = G.obj.map (homOfLE hZV).op b := by
    apply G.eq_of_locally_eq' W Z.1 (fun i => homOfLE (le_iSup W i)) le_rfl
    intro i
    rw [restriction_comp, restriction_comp]
    exact hW i
  exact Concrete.colimit_rep_eq_of_exists F a b
    ⟨op Z, (homOfLE hZU).op, (homOfLE hZV).op, hlocal⟩

/-- Finite simultaneous refinement and sheaf gluing produce an actual open
neighborhood of the selected points, with no semilocality assumption on X. -/
theorem finite_germs_glue_neighborhood [Finite ι]
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : ∀ i, (TopCat.Presheaf.stalk G.obj) (x i))
    (hc : ∀ i j, leftOverlapMap G.obj (x i) (x j) (a i) =
      rightOverlapMap G.obj (x i) (x j) (a j)) :
    ∃ (U : SetNeighborhoods (Set.range x)) (b : G.obj.obj (op U.1)),
      ∀ i, (TopCat.Presheaf.germ G.obj) U.1 (x i) (U.2 ⟨i,rfl⟩) b = a i := by
  classical
  choose U hx s hs using fun i => (TopCat.Presheaf.germ_exist G.obj) (x i) (a i)
  have hpair i j : ∃ (W : OpenNhds (x i)) (Z : OpenNhds (x j))
      (hWU : W.1 ≤ U i) (hZV : Z.1 ≤ U j),
      G.obj.map (homOfLE (inf_le_left.trans hWU) : W.1 ⊓ Z.1 ⟶ U i).op (s i) =
        G.obj.map (homOfLE (inf_le_right.trans hZV) : W.1 ⊓ Z.1 ⟶ U j).op (s j) := by
    apply overlap_eq_refinement G.obj (x i) (x j) ⟨U i, hx i⟩ ⟨U j, hx j⟩ (s i) (s j)
    simpa only [hs] using hc i j
  choose A B hA hB hAB using hpair
  let W (i : ι) : Opens X :=
    ⟨(U i : Set X) ∩ ⋂ j, ((A i j).1 : Set X) ∩ ((B j i).1 : Set X),
      (U i).isOpen.inter (isOpen_iInter_of_finite fun j =>
        (A i j).1.isOpen.inter (B j i).1.isOpen)⟩
  have hW (i : ι) : x i ∈ W i :=
    ⟨hx i, Set.mem_iInter.mpr fun j => ⟨(A i j).2, (B j i).2⟩⟩
  have hWU (i : ι) : W i ≤ U i := fun _ h => h.1
  have hWA (i j : ι) : W i ≤ (A i j).1 := fun _ h => (Set.mem_iInter.mp h.2 j).1
  have hWB (i j : ι) : W j ≤ (B i j).1 := fun _ h => (Set.mem_iInter.mp h.2 i).2
  let t (i : ι) : G.obj.obj (op (W i)) := G.obj.map (homOfLE (hWU i)).op (s i)
  have ht : TopCat.Presheaf.IsCompatible G.obj W t := by
    intro i j
    have hsub : W i ⊓ W j ≤ (A i j).1 ⊓ (B i j).1 := inf_le_inf (hWA i j) (hWB i j)
    have hh := congrArg (G.obj.map (homOfLE hsub).op) (hAB i j)
    change G.obj.map (homOfLE inf_le_left : W i ⊓ W j ⟶ W i).op
      (G.obj.map (homOfLE (hWU i)).op (s i)) =
        G.obj.map (homOfLE inf_le_right : W i ⊓ W j ⟶ W j).op
          (G.obj.map (homOfLE (hWU j)).op (s j))
    calc
      _ = G.obj.map (homOfLE (inf_le_left.trans (hWU i)) : W i ⊓ W j ⟶ U i).op (s i) :=
        restriction_comp G.obj (hWU i) inf_le_left (s i)
      _ = G.obj.map (homOfLE hsub).op
          (G.obj.map (homOfLE (inf_le_left.trans (hA i j))).op (s i)) :=
        (restriction_comp G.obj (inf_le_left.trans (hA i j)) hsub (s i)).symm
      _ = _ := hh
      _ = G.obj.map (homOfLE (inf_le_right.trans (hWU j)) : W i ⊓ W j ⟶ U j).op (s j) :=
        restriction_comp G.obj (inf_le_right.trans (hB i j)) hsub (s j)
      _ = _ := (restriction_comp G.obj (hWU j) inf_le_right (s j)).symm
  let Z : SetNeighborhoods (Set.range x) :=
    ⟨iSup W, by rintro _ ⟨i,rfl⟩; exact (le_iSup W i) (hW i)⟩
  obtain ⟨b, hb, _⟩ := G.existsUnique_gluing' W Z.1
    (fun i => homOfLE (le_iSup W i)) le_rfl t ht
  refine ⟨Z, b, ?_⟩
  intro i
  have hh := congrArg ((TopCat.Presheaf.germ G.obj) (W i) (x i) (hW i)) (hb i)
  rw [(TopCat.Presheaf.germ_res_apply G.obj)] at hh
  dsimp [t] at hh
  rw [(TopCat.Presheaf.germ_res_apply G.obj)] at hh
  exact hh.trans (hs i)

/-- Every element of the actual finite-point neighborhood value has compatible
images in the actual pair-neighborhood overlap colimits. -/
theorem neighborhood_germs_compatible (F : X.Presheaf AddCommGrpCat.{u})
    (a : neighborhood_value F (Set.range x)) :
    overlapDifference x F (neighborhoodGermFamily x F a) = 0 := by
  obtain ⟨U, a, rfl⟩ := Concrete.colimit_exists_rep
    ((neighborhood_inclusion (Set.range x)).op ⋙ F) a
  funext i j
  change leftOverlapMap F (x i) (x j) (neighborhoodGermFamily x F _ i) -
    rightOverlapMap F (x i) (x j) (neighborhoodGermFamily x F _ j) = 0
  rw [neighborhoodGermFamily_representative, neighborhoodGermFamily_representative]
  apply sub_eq_zero.mpr
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    leftOverlapMap_germ F (x i) (x j) ⟨U.unop.1,U.unop.2 ⟨i,rfl⟩⟩ ⟨U.unop.1,U.unop.2 ⟨j,rfl⟩⟩,
    rightOverlapMap_germ F (x i) (x j) ⟨U.unop.1,U.unop.2 ⟨i,rfl⟩⟩ ⟨U.unop.1,U.unop.2 ⟨j,rfl⟩⟩]

/-- The actual neighborhood-colimit value is the equalizer of its stalk and
pair-overlap restriction maps. There is no assumed extension sheaf on a new space. -/
theorem finite_neighborhood_descent_exact [Finite ι]
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (neighborhoodGermFamily x G.obj) ∧
      Function.Exact (neighborhoodGermFamily x G.obj) (overlapDifference x G.obj) := by
  refine ⟨neighborhood_germs_injective x G, ?_⟩
  intro a
  constructor
  · intro ha
    have hc i j : leftOverlapMap G.obj (x i) (x j) (a i) =
        rightOverlapMap G.obj (x i) (x j) (a j) :=
      sub_eq_zero.mp (congrFun (congrFun ha i) j)
    obtain ⟨U,b,hb⟩ := finite_germs_glue_neighborhood x G a hc
    refine ⟨colimit.ι ((neighborhood_inclusion (Set.range x)).op ⋙ G.obj) (op U) b, ?_⟩
    funext i
    rw [neighborhoodGermFamily_representative]
    exact hb i
  · rintro ⟨b,rfl⟩
    exact neighborhood_germs_compatible x G.obj b

end
end MathGauge.GP003
