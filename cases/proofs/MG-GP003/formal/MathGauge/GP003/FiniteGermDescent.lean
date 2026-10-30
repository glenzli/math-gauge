import MathGauge.GP003.TwoPointComparison
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u
variable {X : TopCat.{u}}

abbrev PairNeighborhoods (x y : X) := (OpenNhds x)ᵒᵖ × (OpenNhds y)ᵒᵖ

def pairIntersection (x y : X) : PairNeighborhoods x y ⥤ (Opens X)ᵒᵖ where
  obj p := op (p.1.unop.1 ⊓ p.2.unop.1)
  map {p q} f := (homOfLE (show q.1.unop.1 ⊓ q.2.unop.1 ≤ p.1.unop.1 ⊓ p.2.unop.1 from
    inf_le_inf (show q.1.unop.1 ≤ p.1.unop.1 from f.1.unop.le)
      (show q.2.unop.1 ≤ p.2.unop.1 from f.2.unop.le))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def overlapValue (F : X.Presheaf AddCommGrpCat.{u}) (x y : X) :=
  colimit (pairIntersection x y ⋙ F)

def pairLeftRestriction (F : X.Presheaf AddCommGrpCat.{u}) (x y : X) :
    CategoryTheory.Prod.fst ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ) ⋙ ((OpenNhds.inclusion x).op ⋙ F) ⟶ pairIntersection x y ⋙ F where
  app p := F.map (homOfLE inf_le_left : p.1.unop.1 ⊓ p.2.unop.1 ⟶ p.1.unop.1).op
  naturality _ _ _ := by dsimp; simp only [← F.map_comp]; rfl

def pairRightRestriction (F : X.Presheaf AddCommGrpCat.{u}) (x y : X) :
    CategoryTheory.Prod.snd ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ) ⋙ ((OpenNhds.inclusion y).op ⋙ F) ⟶ pairIntersection x y ⋙ F where
  app p := F.map (homOfLE inf_le_right : p.1.unop.1 ⊓ p.2.unop.1 ⟶ p.2.unop.1).op
  naturality _ _ _ := by dsimp; simp only [← F.map_comp]; rfl

def leftOverlapMap (F : X.Presheaf AddCommGrpCat.{u}) (x y : X) :
    F.stalk x ⟶ overlapValue F x y :=
  inv (colimit.pre ((OpenNhds.inclusion x).op ⋙ F) (CategoryTheory.Prod.fst ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ))) ≫
    colim.map (pairLeftRestriction F x y)

def rightOverlapMap (F : X.Presheaf AddCommGrpCat.{u}) (x y : X) :
    F.stalk y ⟶ overlapValue F x y :=
  inv (colimit.pre ((OpenNhds.inclusion y).op ⋙ F) (CategoryTheory.Prod.snd ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ))) ≫
    colim.map (pairRightRestriction F x y)

theorem leftOverlapMap_germ (F : X.Presheaf AddCommGrpCat.{u}) (x y : X)
    (U : OpenNhds x) (V : OpenNhds y) :
    F.germ U.1 x U.2 ≫ leftOverlapMap F x y =
      F.map (homOfLE inf_le_left : U.1 ⊓ V.1 ⟶ U.1).op ≫
        colimit.ι (pairIntersection x y ⋙ F) (op U, op V) := by
  let p : PairNeighborhoods x y := (op U, op V)
  have h : colimit.ι (CategoryTheory.Prod.fst ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ) ⋙ ((OpenNhds.inclusion x).op ⋙ F)) p ≫
      colimit.pre ((OpenNhds.inclusion x).op ⋙ F) (CategoryTheory.Prod.fst ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ)) = F.germ U.1 x U.2 := by
    cases U
    cases V
    simpa only [p, TopCat.Presheaf.germ, CategoryTheory.Prod.fst, CategoryTheory.Prod.snd] using
      colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ F) (CategoryTheory.Prod.fst ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ)) p
  rw [← h]
  simp only [leftOverlapMap, Category.assoc, IsIso.hom_inv_id_assoc]
  exact colimit.ι_map (pairLeftRestriction F x y) p

theorem rightOverlapMap_germ (F : X.Presheaf AddCommGrpCat.{u}) (x y : X)
    (U : OpenNhds x) (V : OpenNhds y) :
    F.germ V.1 y V.2 ≫ rightOverlapMap F x y =
      F.map (homOfLE inf_le_right : U.1 ⊓ V.1 ⟶ V.1).op ≫
        colimit.ι (pairIntersection x y ⋙ F) (op U, op V) := by
  let p : PairNeighborhoods x y := (op U, op V)
  have h : colimit.ι (CategoryTheory.Prod.snd ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ) ⋙ ((OpenNhds.inclusion y).op ⋙ F)) p ≫
      colimit.pre ((OpenNhds.inclusion y).op ⋙ F) (CategoryTheory.Prod.snd ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ)) = F.germ V.1 y V.2 := by
    cases U
    cases V
    simpa only [p, TopCat.Presheaf.germ, CategoryTheory.Prod.fst, CategoryTheory.Prod.snd] using
      colimit.ι_pre ((OpenNhds.inclusion y).op ⋙ F) (CategoryTheory.Prod.snd ((OpenNhds x)ᵒᵖ) ((OpenNhds y)ᵒᵖ)) p
  rw [← h]
  simp only [rightOverlapMap, Category.assoc, IsIso.hom_inv_id_assoc]
  exact colimit.ι_map (pairRightRestriction F x y) p

/-- Equality in the genuine overlap colimit has a simultaneous open-neighborhood
witness. Neither localization morphism is asserted to be an open immersion. -/
theorem overlap_eq_refinement (F : X.Presheaf AddCommGrpCat.{u}) (x y : X)
    (U : OpenNhds x) (V : OpenNhds y)
    (a : F.obj (op U.1)) (b : F.obj (op V.1))
    (h : leftOverlapMap F x y (F.germ U.1 x U.2 a) =
      rightOverlapMap F x y (F.germ V.1 y V.2 b)) :
    ∃ (W : OpenNhds x) (Z : OpenNhds y) (hWU : W.1 ≤ U.1) (hZV : Z.1 ≤ V.1),
      F.map (homOfLE (inf_le_left.trans hWU) : W.1 ⊓ Z.1 ⟶ U.1).op a =
        F.map (homOfLE (inf_le_right.trans hZV) : W.1 ⊓ Z.1 ⟶ V.1).op b := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    leftOverlapMap_germ F x y U V, rightOverlapMap_germ F x y U V,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  obtain ⟨W, f, g, he⟩ := Concrete.colimit_exists_of_rep_eq (pairIntersection x y ⋙ F)
    (i := (op U, op V)) (j := (op U, op V))
    (F.map (homOfLE inf_le_left : U.1 ⊓ V.1 ⟶ U.1).op a)
    (F.map (homOfLE inf_le_right : U.1 ⊓ V.1 ⟶ V.1).op b) h
  refine ⟨W.1.unop, W.2.unop, f.1.unop.le, g.2.unop.le, ?_⟩
  calc
    _ = (pairIntersection x y ⋙ F).map f
        (F.map (homOfLE inf_le_left : U.1 ⊓ V.1 ⟶ U.1).op a) := by
      exact ConcreteCategory.congr_hom (F.map_comp
        (homOfLE inf_le_left : U.1 ⊓ V.1 ⟶ U.1).op ((pairIntersection x y).map f)) a
    _ = _ := he
    _ = _ := by
      exact (ConcreteCategory.congr_hom (F.map_comp
        (homOfLE inf_le_right : U.1 ⊓ V.1 ⟶ V.1).op ((pairIntersection x y).map g)) b).symm


lemma restriction_comp (F : X.Presheaf AddCommGrpCat.{u}) {U V W : Opens X}
    (hVU : V ≤ U) (hWV : W ≤ V) (a : F.obj (op U)) :
    F.map (homOfLE hWV).op (F.map (homOfLE hVU).op a) =
      F.map (homOfLE (hWV.trans hVU)).op a :=
  (ConcreteCategory.congr_hom (F.map_comp (homOfLE hVU).op (homOfLE hWV).op) a).symm

variable {ι : Type u} (x : ι → X)
    (hcover : ∀ W : Opens X, (∀ i, x i ∈ W) → W = ⊤)

include hcover in
/-- All sections are determined by germs at a family detecting open covers. -/
theorem finite_point_germs_injective (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (fun a : G.obj.obj (op ⊤) =>
      fun i => (TopCat.Presheaf.germ G.obj) ⊤ (x i) (by trivial) a) := by
  intro a b hab
  have he i := congrFun hab i
  choose U hx iU iV habU using fun i => (TopCat.Presheaf.germ_eq G.obj) (x i)
    (show x i ∈ (⊤ : Opens X) from trivial) (show x i ∈ (⊤ : Opens X) from trivial)
    a b (he i)
  have htop : iSup U = ⊤ := hcover _ fun i => (le_iSup U i) (hx i)
  apply G.eq_of_locally_eq' U ⊤ iU (by rw [htop]) a b
  intro i
  simpa only [Subsingleton.elim (iV i) (iU i)] using habU i

include hcover in
/-- A finite compatible family of actual stalks glues. Compatibility is measured
in the genuine filtered colimits over intersections of pairs of neighborhoods. -/
theorem finite_point_germs_glue [Finite ι]
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : ∀ i, (TopCat.Presheaf.stalk G.obj) (x i))
    (hc : ∀ i j, leftOverlapMap G.obj (x i) (x j) (a i) =
      rightOverlapMap G.obj (x i) (x j) (a j)) :
    ∃! b : G.obj.obj (op ⊤), ∀ i, (TopCat.Presheaf.germ G.obj) ⊤ (x i) (by trivial) b = a i := by
  classical
  choose U hx s hs using fun i => (TopCat.Presheaf.exists_germ_eq G.obj) (a i)
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
  have htop : iSup W = ⊤ := hcover _ fun i => (le_iSup W i) (hW i)
  obtain ⟨b, hb, _⟩ := G.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top)
    (by rw [htop]) t ht
  refine ⟨b, ?_, ?_⟩
  · intro i
    have hh := congrArg ((TopCat.Presheaf.germ G.obj) (W i) (x i) (hW i)) (hb i)
    rw [(TopCat.Presheaf.germ_res_apply G.obj)] at hh
    dsimp [t] at hh
    rw [(TopCat.Presheaf.germ_res_apply G.obj)] at hh
    exact hh.trans (hs i)
  · intro c hc'
    apply finite_point_germs_injective x hcover G
    funext i
    exact (hc' i).trans (by
      have hh := congrArg ((TopCat.Presheaf.germ G.obj) (W i) (x i) (hW i)) (hb i)
      rw [(TopCat.Presheaf.germ_res_apply G.obj)] at hh
      dsimp [t] at hh
      rw [(TopCat.Presheaf.germ_res_apply G.obj)] at hh
      exact (hh.trans (hs i)).symm)


def germFamily (F : X.Presheaf AddCommGrpCat.{u}) :
    F.obj (op ⊤) →+ ∀ i, F.stalk (x i) where
  toFun a i := F.germ ⊤ (x i) (by trivial) a
  map_zero' := by funext i; exact map_zero _
  map_add' a b := by funext i; exact map_add _ a b

def overlapDifference (F : X.Presheaf AddCommGrpCat.{u}) :
    (∀ i, F.stalk (x i)) →+ ∀ i j, overlapValue F (x i) (x j) where
  toFun a i j := leftOverlapMap F (x i) (x j) (a i) -
    rightOverlapMap F (x i) (x j) (a j)
  map_zero' := by funext i j; simp
  map_add' a b := by funext i j; simp only [Pi.add_apply, map_add]; abel

theorem global_germs_compatible (F : X.Presheaf AddCommGrpCat.{u})
    (b : F.obj (op ⊤)) : overlapDifference x F (germFamily x F b) = 0 := by
  funext i j
  change leftOverlapMap F (x i) (x j) (F.germ ⊤ (x i) (by trivial) b) -
    rightOverlapMap F (x i) (x j) (F.germ ⊤ (x j) (by trivial) b) = 0
  apply sub_eq_zero.mpr
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    leftOverlapMap_germ F (x i) (x j) ⟨⊤, by trivial⟩ ⟨⊤, by trivial⟩,
    rightOverlapMap_germ F (x i) (x j) ⟨⊤, by trivial⟩ ⟨⊤, by trivial⟩]

include hcover in
/-- The actual equalizer of the two overlap restrictions: the left map is
injective and its image is exactly the kernel of their difference. -/
theorem finite_point_descent_exact [Finite ι]
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (germFamily x G.obj) ∧
      Function.Exact (germFamily x G.obj) (overlapDifference x G.obj) := by
  refine ⟨finite_point_germs_injective x hcover G, ?_⟩
  intro a
  constructor
  · intro ha
    have hc i j : leftOverlapMap G.obj (x i) (x j) (a i) =
        rightOverlapMap G.obj (x i) (x j) (a j) := by
      apply sub_eq_zero.mp
      exact congrFun (congrFun ha i) j
    obtain ⟨b, hb, _⟩ := finite_point_germs_glue x hcover G a hc
    exact ⟨b, funext hb⟩
  · rintro ⟨b, rfl⟩
    exact global_germs_compatible x G.obj b

end
end MathGauge.GP003
