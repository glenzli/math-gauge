import MathGauge.GP003.FiniteNeighborhoodDescent

/-!
The finite-set assembly in the semilocal comparison, on the actual small site.
All values, germs, overlap maps and comparison maps are the existing colimits.
The final result is conditional: the binary gluing hypothesis is a remaining
geometric obligation for the actual presheaf with transfers. This module neither
proves that obligation nor identifies an arbitrary presheaf with a transfer
presheaf. In particular, it does not complete stage S5 by itself.
-/

namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open MathGauge.PublicProof.Semilocal

universe u
variable {X : TopCat.{u}}

/-- The actual presheaf map induces the map on the pair-neighborhood colimit. -/
def overlapValueMap {F G : X.Presheaf AddCommGrpCat.{u}}
    (η : F ⟶ G) (x y : X) : overlapValue F x y ⟶ overlapValue G x y :=
  colim.map (whiskerLeft (pairIntersection x y) η)

theorem overlapValueMap_injective {F G : X.Presheaf AddCommGrpCat.{u}}
    (η : F ⟶ G) (x y : X)
    (hη : ∀ U : Opens X, Function.Injective (η.app (op U))) :
    Function.Injective (overlapValueMap η x y) := by
  haveI : Mono (whiskerLeft (pairIntersection x y) η) :=
    (NatTrans.mono_iff_mono_app _).mpr fun U =>
      (AddCommGrpCat.mono_iff_injective _).mpr (hη _)
  apply (AddCommGrpCat.mono_iff_injective _).mp
  change Mono (colim.map (whiskerLeft (pairIntersection x y) η))
  infer_instance

theorem leftOverlapMap_naturality {F G : X.Presheaf AddCommGrpCat.{u}}
    (η : F ⟶ G) (x y : X) :
    leftOverlapMap F x y ≫ overlapValueMap η x y =
      (stalkFunctor AddCommGrpCat x).map η ≫ leftOverlapMap G x y := by
  apply F.stalk_hom_ext
  intro U hx
  let V : OpenNhds y := ⟨⊤, by trivial⟩
  rw [← Category.assoc, leftOverlapMap_germ F x y ⟨U, hx⟩ V,
    Category.assoc, overlapValueMap, colimit.ι_map]
  rw [stalkFunctor_map_germ_assoc,
    leftOverlapMap_germ G x y ⟨U, hx⟩ V]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun f => f ≫ colimit.ι (pairIntersection x y ⋙ G) (op ⟨U, hx⟩, op V))
    (η.naturality (homOfLE inf_le_left : U ⊓ V.1 ⟶ U).op)

theorem rightOverlapMap_naturality {F G : X.Presheaf AddCommGrpCat.{u}}
    (η : F ⟶ G) (x y : X) :
    rightOverlapMap F x y ≫ overlapValueMap η x y =
      (stalkFunctor AddCommGrpCat y).map η ≫ rightOverlapMap G x y := by
  apply F.stalk_hom_ext
  intro V hy
  let U : OpenNhds x := ⟨⊤, by trivial⟩
  rw [← Category.assoc, rightOverlapMap_germ F x y U ⟨V, hy⟩,
    Category.assoc, overlapValueMap, colimit.ι_map]
  rw [stalkFunctor_map_germ_assoc,
    rightOverlapMap_germ G x y U ⟨V, hy⟩]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun f => f ≫ colimit.ι (pairIntersection x y ⋙ G) (op U, op ⟨V, hy⟩))
    (η.naturality (homOfLE inf_le_right : U.1 ⊓ V ⟶ V).op)

/-- Naturality identifies the germ of the actual colimit comparison with the
actual map of stalks. It is not just a comparison of object isomorphism classes. -/
theorem neighborhoodGerm_naturality {F G : X.Presheaf AddCommGrpCat.{u}}
    (η : F ⟶ G) (s : Set X) (x : X) (hx : x ∈ s) :
    neighborhood_value_map η s ≫ neighborhoodGerm G s x hx =
      neighborhoodGerm F s x hx ≫ (stalkFunctor AddCommGrpCat x).map η := by
  apply colimit.hom_ext
  intro U
  cases U using Opposite.rec with
  | _ U =>
    rw [← Category.assoc, neighborhood_value_map_representative,
      Category.assoc, neighborhoodGerm_representative,
      ← Category.assoc, neighborhoodGerm_representative,
      stalkFunctor_map_germ]

theorem neighborhoodGerm_ext (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (s : Set X) {a b : neighborhood_value G.obj s}
    (h : ∀ x (hx : x ∈ s), neighborhoodGerm G.obj s x hx a =
      neighborhoodGerm G.obj s x hx b) : a = b := by
  obtain ⟨U, a, rfl⟩ := Concrete.colimit_exists_rep ((neighborhood_inclusion s).op ⋙ G.obj) a
  obtain ⟨V, b, rfl⟩ := Concrete.colimit_exists_rep ((neighborhood_inclusion s).op ⋙ G.obj) b
  have he (x : s) : (TopCat.Presheaf.germ G.obj) U.unop.1 x (U.unop.2 x.property) a =
      (TopCat.Presheaf.germ G.obj) V.unop.1 x (V.unop.2 x.property) b := by
    have hu := ConcreteCategory.congr_hom (neighborhoodGerm_representative G.obj s x x.property U.unop) a
    have hv := ConcreteCategory.congr_hom (neighborhoodGerm_representative G.obj s x x.property V.unop) b
    exact hu.symm.trans ((h x x.property).trans hv)
  choose W hx hWU hWV hW using fun x : s => (TopCat.Presheaf.germ_eq G.obj) x
    (U.unop.2 x.property) (V.unop.2 x.property) a b (he x)
  let Z : SetNeighborhoods s :=
    ⟨iSup W, by intro x hx'; exact (le_iSup W ⟨x, hx'⟩) (hx ⟨x, hx'⟩)⟩
  have hZU : Z.1 ≤ U.unop.1 := iSup_le fun x => (hWU x).le
  have hZV : Z.1 ≤ V.unop.1 := iSup_le fun x => (hWV x).le
  have hlocal : G.obj.map (homOfLE hZU).op a = G.obj.map (homOfLE hZV).op b := by
    apply G.eq_of_locally_eq' W Z.1 (fun x => homOfLE (le_iSup W x)) le_rfl
    intro x
    rw [restriction_comp, restriction_comp]
    exact hW x
  exact Concrete.colimit_rep_eq_of_exists ((neighborhood_inclusion s).op ⋙ G.obj) a b
    ⟨op Z, (homOfLE hZU).op, (homOfLE hZV).op, hlocal⟩

theorem neighborhoodGerm_compatible (F : X.Presheaf AddCommGrpCat.{u})
    (s : Set X) (a : neighborhood_value F s) (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
    leftOverlapMap F x y (neighborhoodGerm F s x hx a) =
      rightOverlapMap F x y (neighborhoodGerm F s y hy a) := by
  obtain ⟨U, a, rfl⟩ := Concrete.colimit_exists_rep ((neighborhood_inclusion s).op ⋙ F) a
  cases U using Opposite.rec with
  | _ U =>
    have hxg := ConcreteCategory.congr_hom (neighborhoodGerm_representative F s x hx U) a
    have hyg := ConcreteCategory.congr_hom (neighborhoodGerm_representative F s y hy U) a
    simp only [ConcreteCategory.comp_apply] at hxg hyg
    change leftOverlapMap F x y (neighborhoodGerm F s x hx
      (colimit.ι ((neighborhood_inclusion s).op ⋙ F) (op U) a)) =
      rightOverlapMap F x y (neighborhoodGerm F s y hy
        (colimit.ι ((neighborhood_inclusion s).op ⋙ F) (op U) a))
    apply (congrArg (leftOverlapMap F x y) hxg).trans
    apply Eq.trans _ (congrArg (rightOverlapMap F x y) hyg).symm
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      leftOverlapMap_germ F x y ⟨U.1, U.2 hx⟩ ⟨U.1, U.2 hy⟩,
      rightOverlapMap_germ F x y ⟨U.1, U.2 hx⟩ ⟨U.1, U.2 hy⟩]

open Classical in
/-- A fully explicit binary geometric input. It asks for simultaneous gluing
of one stalk and an already constructed finite-block value in the selected
presheaf (the separated quotient in the MVW route). It is not asserted for
arbitrary presheaves; the transfer geometry
must construct it before the conditional comparison below can be applied. -/
def SingletonBlockGluing (F : X.Presheaf AddCommGrpCat.{u}) : Prop :=
  ∀ (x : X) (s : Finset X), x ∉ s → s.Nonempty →
    ∀ (a : F.stalk x) (b : neighborhood_value F (s : Set X)),
      (∀ y (hy : y ∈ s), leftOverlapMap F x y a =
        rightOverlapMap F x y (neighborhoodGerm F (s : Set X) y hy b)) →
      ∃ c : neighborhood_value F ((insert x s : Finset X) : Set X),
        neighborhoodGerm F _ x (Finset.mem_insert_self x s) c = a ∧
        ∀ y (hy : y ∈ s),
          neighborhoodGerm F _ y (Finset.mem_insert_of_mem hy) c =
            neighborhoodGerm F (s : Set X) y hy b

/-- Finite insertion induction performs the actual gluing. Its base case is
a representative of an actual stalk; its induction hypothesis is used only
for the smaller finite point block. -/
theorem finite_germs_glue_of_singleton_block_gluing
    (F : X.Presheaf AddCommGrpCat.{u}) (hglue : SingletonBlockGluing F)
    (s : Finset X) (hs : s.Nonempty) (a : ∀ x : X, F.stalk x)
    (hc : ∀ x ∈ s, ∀ y ∈ s, leftOverlapMap F x y (a x) =
      rightOverlapMap F x y (a y)) :
    ∃ b : neighborhood_value F (s : Set X),
      ∀ x (hx : x ∈ s), neighborhoodGerm F (s : Set X) x hx b = a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert x s hx ih =>
    by_cases hs' : s.Nonempty
    · obtain ⟨b, hb⟩ := ih hs' (fun y hy z hz =>
        hc y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz))
      obtain ⟨c, hcx, hcs⟩ := hglue x s hx hs' (a x) b (by
        intro y hy
        rw [hb y hy]
        exact hc x (Finset.mem_insert_self x s) y (Finset.mem_insert_of_mem hy))
      refine ⟨c, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hcx
      · exact (hcs y hy).trans (hb y hy)
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      obtain ⟨U, hxU, aU, haU⟩ := F.germ_exist x (a x)
      let W : SetNeighborhoods (↑(insert x (∅ : Finset X)) : Set X) :=
        ⟨U, by
          intro y hy
          have hyx : y = x := by simpa using hy
          exact hyx ▸ hxU⟩
      refine ⟨colimit.ι ((neighborhood_inclusion _).op ⋙ F) (op W) aU, ?_⟩
      intro y hy
      have hyx : y = x := by simpa using hy
      subst y
      exact (ConcreteCategory.congr_hom (neighborhoodGerm_representative F _ x _ W) aU).trans haU

/-- Once the specified binary transfer geometry is proved, the comparison is
bijective for every finite nonempty point set. Componentwise injectivity is
used on the actual overlap colimits; no overlap surjectivity is assumed. -/
theorem finite_neighborhood_comparison_of_singleton_block_gluing
    (H : X.Presheaf AddCommGrpCat.{u}) (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (η : H ⟶ G.obj)
    (hmono : ∀ U : Opens X, Function.Injective (η.app (op U)))
    (hstalk : ∀ x : X, Function.Surjective ((stalkFunctor AddCommGrpCat x).map η))
    (hglue : SingletonBlockGluing H) (s : Finset X) (hs : s.Nonempty) :
    Function.Bijective (neighborhood_value_map η (s : Set X)) := by
  classical
  refine ⟨neighborhood_value_map_injective η _ hmono, ?_⟩
  intro b
  let a (x : X) : H.stalk x := if hx : x ∈ s then
    Classical.choose (hstalk x (neighborhoodGerm G.obj (s : Set X) x hx b)) else 0
  have ha (x : X) (hx : x ∈ s) :
      (stalkFunctor AddCommGrpCat x).map η (a x) =
        neighborhoodGerm G.obj (s : Set X) x hx b := by
    dsimp [a]
    rw [dif_pos hx]
    exact Classical.choose_spec (hstalk x (neighborhoodGerm G.obj (s : Set X) x hx b))
  have hc : ∀ x ∈ s, ∀ y ∈ s, leftOverlapMap H x y (a x) =
      rightOverlapMap H x y (a y) := by
    intro x hx y hy
    apply overlapValueMap_injective η x y hmono
    have hl := ConcreteCategory.congr_hom (leftOverlapMap_naturality η x y) (a x)
    have hr := ConcreteCategory.congr_hom (rightOverlapMap_naturality η x y) (a y)
    simp only [ConcreteCategory.comp_apply] at hl hr
    change overlapValueMap η x y (leftOverlapMap H x y (a x)) =
      overlapValueMap η x y (rightOverlapMap H x y (a y))
    exact hl.trans ((congrArg (leftOverlapMap G.obj x y) (ha x hx)).trans
      ((neighborhoodGerm_compatible G.obj (s : Set X) b x y hx hy).trans
        ((congrArg (rightOverlapMap G.obj x y) (ha y hy)).symm.trans hr.symm)))
  obtain ⟨c, hc⟩ := finite_germs_glue_of_singleton_block_gluing H hglue s hs a hc
  refine ⟨c, neighborhoodGerm_ext G (s : Set X) ?_⟩
  intro x hx
  have hn := ConcreteCategory.congr_hom (neighborhoodGerm_naturality η (s : Set X) x hx) c
  simp only [ConcreteCategory.comp_apply] at hn
  change neighborhoodGerm G.obj (s : Set X) x hx
    (neighborhood_value_map η (s : Set X) c) = _ at hn
  exact hn.trans ((congrArg ((stalkFunctor AddCommGrpCat x).map η) (hc x hx)).trans (ha x hx))

/-- Specialization to the literal Zariski sheafification unit. Its stalk
surjectivity is proved by Mathlib, not requested as another geometric input.
In the MVW route this applies to the separated quotient, not directly to the
original presheaf. Its construction, binary gluing and comparison with the
original finite-point values remain geometric obligations. -/
theorem finite_neighborhood_sheafification_of_singleton_block_gluing
    (F : X.Presheaf AddCommGrpCat.{u})
    (hmono : ∀ U : Opens X, Function.Injective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op U)))
    (hglue : SingletonBlockGluing F) (s : Finset X) (hs : s.Nonempty) :
    IsIso (finite_neighborhood_sheafification_comparison F s) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply finite_neighborhood_comparison_of_singleton_block_gluing F
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj F)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F) hmono _ hglue s hs
  intro x
  haveI := singleton_neighborhood_comparison_isIso X F x
  exact (ConcreteCategory.bijective_of_isIso
    ((stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F))).2

theorem neighborhood_value_map_comp {E F G : X.Presheaf AddCommGrpCat.{u}}
    (α : E ⟶ F) (β : F ⟶ G) (s : Set X) :
    neighborhood_value_map (α ≫ β) s =
      neighborhood_value_map α s ≫ neighborhood_value_map β s := by
  unfold neighborhood_value_map
  rw [← colim.map_comp]
  rfl

/-- Restore the *original* canonical unit after a separated-quotient reduction.
The maps are the actual presheaf map and its actual sheafification map, so the
unit compatibility is proved, not supplied. The two quotient isomorphism inputs
are precisely remaining geometric comparisons, not an assumption of the target
unit isomorphism. No pointwise injection of the original presheaf is requested. -/
theorem finite_neighborhood_original_unit_of_quotient_comparison
    (F H : X.Presheaf AddCommGrpCat.{u}) (α : F ⟶ H)
    (hmono : ∀ U : Opens X, Function.Injective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) H).app (op U)))
    (hglue : SingletonBlockGluing H) (s : Finset X) (hs : s.Nonempty)
    (hfinite : IsIso (neighborhood_value_map α (s : Set X)))
    (hsheaf : IsIso (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) α)) :
    IsIso (finite_neighborhood_sheafification_comparison F s) := by
  letI := hfinite
  letI := hsheaf
  let ηF := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  let ηH := CategoryTheory.toSheafify (Opens.grothendieckTopology X) H
  let β := CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) α
  haveI : IsIso (neighborhood_value_map ηH (s : Set X)) :=
    finite_neighborhood_sheafification_of_singleton_block_gluing H hmono hglue s hs
  haveI : IsIso (neighborhood_value_map β (s : Set X)) := by
    unfold neighborhood_value_map
    infer_instance
  have hn := congrArg (fun θ => neighborhood_value_map θ (s : Set X))
    (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X) α)
  change neighborhood_value_map (α ≫ ηH) (s : Set X) =
    neighborhood_value_map (ηF ≫ β) (s : Set X) at hn
  rw [neighborhood_value_map_comp, neighborhood_value_map_comp] at hn
  haveI : IsIso (neighborhood_value_map ηF (s : Set X) ≫
      neighborhood_value_map β (s : Set X)) := by
    change IsIso (neighborhood_value_map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F) (s : Set X) ≫
      neighborhood_value_map (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) α)
        (s : Set X))
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right (neighborhood_value_map ηF (s : Set X))
    (neighborhood_value_map β (s : Set X))

end
end MathGauge.GP003
