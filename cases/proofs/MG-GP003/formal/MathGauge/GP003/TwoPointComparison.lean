import NeighborhoodRefinement
import NeighborhoodValues
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace Opposite
open MathGauge.PublicProof.Semilocal

universe u
variable {X : TopCat.{u}}

def twoOpenRestriction (H : X.Presheaf AddCommGrpCat.{u}) (U V : Opens X) :
    H.obj (op ⊤) →+ (H.obj (op U) × H.obj (op V)) :=
  (H.map (homOfLE le_top : U ⟶ ⊤).op).hom.prod
    (H.map (homOfLE le_top : V ⟶ ⊤).op).hom

def twoOpenDifference (H : X.Presheaf AddCommGrpCat.{u}) (U V : Opens X) :
    (H.obj (op U) × H.obj (op V)) →+ H.obj (op (U ⊓ V)) :=
  ((H.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.comp (AddMonoidHom.fst _ _)) -
    ((H.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.comp (AddMonoidHom.snd _ _))

theorem local_representative_of_stalk_surjective
    {H G : X.Presheaf AddCommGrpCat.{u}} (η : H ⟶ G) (x : X)
    (hηx : Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η))
    (b : G.obj (op ⊤)) :
    ∃ U : Opens X, ∃ hx : x ∈ U, ∃ a : H.obj (op U),
      η.app (op U) a = G.map (homOfLE le_top : U ⟶ ⊤).op b := by
  obtain ⟨a, ha⟩ := hηx (G.germ ⊤ x (by trivial) b)
  obtain ⟨U, hxU, aU, rfl⟩ := H.germ_exist x a
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  obtain ⟨W, hxW, iU, iT, he⟩ := G.germ_eq x hxU (show x ∈ (⊤ : Opens X) from trivial)
    (η.app (op U) aU) b ha
  refine ⟨W, hxW, H.map iU.op aU, ?_⟩
  rw [η.naturality_apply]
  exact he

theorem restrict_lift {H G : X.Presheaf AddCommGrpCat.{u}} (η : H ⟶ G)
    {U W : Opens X} (hWU : W ≤ U) {a : H.obj (op U)} {b : G.obj (op ⊤)}
    (ha : η.app (op U) a = G.map (homOfLE le_top : U ⟶ ⊤).op b) :
    η.app (op W) (H.map (homOfLE hWU).op a) =
      G.map (homOfLE le_top : W ⟶ ⊤).op b := by
  rw [η.naturality_apply, ha, ← ConcreteCategory.comp_apply, ← G.map_comp]
  rfl

/-- The comparison in S2, on the actual small site of a space whose two
closed points detect open covers. Only the explicitly supplied successful
shrinking property is assumed; no original unshrunk row is presumed exact. -/
theorem comparison_two_closed_points
    (x y : X) (hxy : x ≠ y)
    (hxclosed : IsClosed ({x} : Set X)) (hyclosed : IsClosed ({y} : Set X))
    (hcover : ∀ W : Opens X, x ∈ W → y ∈ W → W = ⊤)
    (H : X.Presheaf AddCommGrpCat.{u}) (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (η : H ⟶ G.obj)
    (hmono : ∀ W : Opens X, Function.Injective (η.app (op W)))
    (hxiso : Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η))
    (hyiso : Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map η))
    (hrefine : ∀ U₀ V : Opens X,
      Separates ({x} : Set X) {y} U₀ V → U₀ ⊔ V = ⊤ →
      ∃ U : Opens X, U ≤ U₀ ∧ U ⊔ V = ⊤ ∧
        Function.Exact (twoOpenRestriction H U V) (twoOpenDifference H U V)) :
    Function.Bijective (η.app (op ⊤)) := by
  refine ⟨hmono ⊤, ?_⟩
  intro b
  obtain ⟨U₀, hxU₀, a₀, ha₀⟩ := local_representative_of_stalk_surjective η x hxiso b
  obtain ⟨V₀, hyV₀, b₀, hb₀⟩ := local_representative_of_stalk_surjective η y hyiso b
  let U : Opens X := U₀ ⊓ ⟨({y} : Set X)ᶜ, hyclosed.isOpen_compl⟩
  let V : Opens X := V₀ ⊓ ⟨({x} : Set X)ᶜ, hxclosed.isOpen_compl⟩
  have hs : Separates ({x} : Set X) {y} U V := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨hxU₀, by simpa using hxy⟩
    · exact Set.disjoint_left.mpr fun z hz hzu => hzu.2 hz
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨hyV₀, by simpa using hxy.symm⟩
    · exact Set.disjoint_left.mpr fun z hz hzv => hzv.2 hz
  have hUV : U ⊔ V = ⊤ := hcover _ (Or.inl (hs.1 (Set.mem_singleton _)))
    (Or.inr (hs.2.2.1 (Set.mem_singleton _)))
  obtain ⟨U', hU'U, hU'V, he⟩ := hrefine U V hs hUV
  let aU : H.obj (op U') := H.map (homOfLE (hU'U.trans inf_le_left)).op a₀
  let aV : H.obj (op V) := H.map (homOfLE inf_le_left).op b₀
  have haU : η.app (op U') aU = G.obj.map (homOfLE le_top : U' ⟶ ⊤).op b :=
    restrict_lift η (hU'U.trans inf_le_left) ha₀
  have haV : η.app (op V) aV = G.obj.map (homOfLE le_top : V ⟶ ⊤).op b :=
    restrict_lift η inf_le_left hb₀
  have hz : twoOpenDifference H U' V (aU, aV) = 0 := by
    apply hmono (U' ⊓ V)
    change η.app (op (U' ⊓ V))
      (H.map (homOfLE inf_le_left : U' ⊓ V ⟶ U').op aU -
        H.map (homOfLE inf_le_right : U' ⊓ V ⟶ V).op aV) = η.app (op (U' ⊓ V)) 0
    rw [map_sub, map_zero]
    rw [η.naturality_apply (homOfLE inf_le_left : U' ⊓ V ⟶ U').op aU,
      η.naturality_apply (homOfLE inf_le_right : U' ⊓ V ⟶ V).op aV, haU, haV]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.obj.map_comp, ← G.obj.map_comp]
    exact sub_self _
  obtain ⟨a, ha⟩ := (he (aU, aV)).mp hz
  refine ⟨a, ?_⟩
  apply G.eq_of_locally_eq₂ (homOfLE le_top : U' ⟶ ⊤)
    (homOfLE le_top : V ⟶ ⊤) (by rw [hU'V])
  · rw [← η.naturality_apply]
    exact (congrArg (fun z => η.app (op U') z.1) ha).trans haU
  · rw [← η.naturality_apply]
    exact (congrArg (fun z => η.app (op V) z.2) ha).trans haV

end
end MathGauge.GP003
