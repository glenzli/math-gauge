/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits

namespace MathGauge.GP003.SmoothZariski
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
universe u v
variable {S : Scheme.{u}} [baseNoetherian : IsNoetherian S]

/-- The actual opens of a smooth finite-type model, with their original maps to the base. -/
def opensFunctor (X : SmoothSite S) : X.left.Opens ⥤ SmoothSite S where
  obj U := SmoothSite.mk (U.ι ≫ X.hom)
  map f := SmoothSite.homMk (X.left.homOfLE f.le) (by simp)
  map_id U := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_rfl _ _
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (X.left.homOfLE_homOfLE f.le g.le).symm

def openInclusion (X : SmoothSite S) (U : X.left.Opens) :
    (opensFunctor X).obj U ⟶ X := SmoothSite.homMk U.ι rfl

instance openInclusion_open (X : SmoothSite S) (U : X.left.Opens) :
    IsOpenImmersion (openInclusion X U).left := by
  change IsOpenImmersion U.ι
  infer_instance

instance opensFunctor_map_open (X : SmoothSite S) {U V : X.left.Opens} (f : U ⟶ V) :
    IsOpenImmersion ((opensFunctor X).map f).left := by
  change IsOpenImmersion (X.left.homOfLE f.le)
  infer_instance

/-- Zariski families on the actual smooth site: open immersions jointly covering
the underlying scheme. No Nisnevich cover is substituted. -/
def precoverage (S : Scheme.{u}) : Precoverage (SmoothSite S) where
  coverings X := { R | (∀ ⦃Y⦄ (f : Y ⟶ X), R f → IsOpenImmersion f.left) ∧
    ∀ x : X.left, ∃ (Y : SmoothSite S) (f : Y ⟶ X) (y : Y.left), R f ∧ f.left y = x }

/-- The pointwise description of the genuine Zariski covering sieves. -/
def topology (S : Scheme.{u}) [IsNoetherian S] : GrothendieckTopology (SmoothSite S) where
  sieves X := { R | ∀ x : X.left, ∃ (Y : SmoothSite S) (f : Y ⟶ X) (y : Y.left),
    R f ∧ IsOpenImmersion f.left ∧ f.left y = x }
  top_mem' X x := ⟨X, 𝟙 X, x, trivial, inferInstance, rfl⟩
  pullback_stable' X Y R f hR y := by
    obtain ⟨Z, g, z, hg, hgo, hgz⟩ := hR (f.left y)
    have := hgo
    let W : Y.left.Opens := f.left ⁻¹ᵁ g.left.opensRange
    let a := openInclusion Y W
    let q : W.toScheme ⟶ Z.left :=
      IsOpenImmersion.lift g.left (W.ι ≫ f.left) (by
        rintro _ ⟨t, rfl⟩
        exact t.2)
    let b : (opensFunctor Y).obj W ⟶ Z := SmoothSite.homMk q (by
      rw [← MorphismProperty.Over.w g, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, MorphismProperty.Over.w f]
      rfl)
    have hba : b ≫ g = a ≫ f := by
      apply MorphismProperty.Over.Hom.ext
      exact IsOpenImmersion.lift_fac _ _ _
    refine ⟨(opensFunctor Y).obj W, a, ⟨y, ?_⟩, ?_, inferInstance, rfl⟩
    · exact ⟨z, hgz⟩
    · change R (a ≫ f)
      rw [← hba]
      exact R.downward_closed hg b
  transitive' X R hR T hT x := by
    obtain ⟨Y, f, y, hf, hfo, hfy⟩ := hR x
    obtain ⟨Z, g, z, hg, hgo, hgz⟩ := hT hf y
    have := hfo
    have := hgo
    refine ⟨Z, g ≫ f, z, hg, ?_, ?_⟩
    · change IsOpenImmersion (g.left ≫ f.left)
      infer_instance
    · change f.left (g.left z) = x
      rw [hgz, hfy]

theorem topology_eq_generated (S : Scheme.{u}) [IsNoetherian S] :
    topology S = (precoverage S).toGrothendieck := by
  apply le_antisymm
  · intro X R hR
    let Q : Presieve X := fun _ f => R f ∧ IsOpenImmersion f.left
    have hQ : Q ∈ precoverage S X := by
      constructor
      · intro Y f hf
        exact hf.2
      · intro x
        obtain ⟨Y, f, y, hf, hfo, hfy⟩ := hR x
        exact ⟨Y, f, y, ⟨hf, hfo⟩, hfy⟩
    apply (precoverage S).toGrothendieck.superset_covering _
      (Precoverage.generate_mem_toGrothendieck hQ)
    exact (Sieve.generate_le_iff _ _).mpr fun Y f hf => hf.1
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR x
    obtain ⟨Y, f, y, hf, hfy⟩ := hR.2 x
    exact ⟨Y, f, y, Sieve.le_generate R _ _ hf, hR.1 _ hf, hfy⟩


/-- The defined Zariski families are exactly the underlying ordinary open covers. -/
theorem precoverage_eq_comap (S : Scheme.{u}) :
    precoverage S = Scheme.zariskiPrecoverage.comap (SmoothSite.forgetScheme S) := by
  ext X R
  constructor
  · intro hR
    constructor
    · intro x
      obtain ⟨Y, f, y, hf, hfy⟩ := hR.2 x
      exact ⟨Y.left, Scheme.forget.map f.left, ⟨⟨hf⟩⟩, y, hfy⟩
    · intro Y f hf
      cases hf with
      | of hf => exact hR.1 _ hf
  · intro hR
    constructor
    · intro Y f hf
      exact hR.2 (Presieve.map_map hf)
    · intro x
      obtain ⟨Y, f, hf, y, hfy⟩ := hR.1 x
      cases hf with
      | of hf =>
        cases hf with
        | of hf => exact ⟨_, _, y, hf, hfy⟩

/-- Every actual Zariski cover is Nisnevich; this uses only the proved coverage
inclusion and does not assert equality of the two topologies. -/
theorem topology_le_nisnevich (S : Scheme.{u}) [IsNoetherian S] :
    topology S ≤ SmoothSite.nisnevichTopology S := by
  rw [topology_eq_generated, SmoothSite.nisnevichTopology, precoverage_eq_comap,
    SmoothSite.nisnevichPrecoverage]
  exact Precoverage.toGrothendieck_mono
    (by intro X R hR; exact Nisnevich.zariskiPrecoverage_le_precoverage _ hR)

/-- The underlying ordinary presheaf of a Nisnevich sheaf is a Zariski sheaf. -/
def nisnevichToZariski
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u+1}) :
    Sheaf (topology S) AddCommGrpCat.{u+1} :=
  ⟨F.obj, F.property.of_le (topology_le_nisnevich S)⟩

/-- Compatibility is transported through the actual scheme intersection and
its unique lift, retaining every morphism over the original base. -/
theorem opens_compatible (X : SmoothSite S) :
    CompatiblePreserving.{v} (topology S) (opensFunctor X) := by
  constructor
  intro F Z T a ha U V Y f g i j hi hj h
  have hfg : f.left ≫ U.ι = g.left ≫ V.ι := by
    have hh := congrArg (fun e => e.left ≫ Z.ι) h
    simpa [opensFunctor, Category.assoc] using hh
  let q : Y.left ⟶ (U ⊓ V).toScheme :=
    IsOpenImmersion.lift (U ⊓ V).ι (f.left ≫ U.ι) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      refine ⟨(f.left y).2, ?_⟩
      change (f.left y).1 ∈ V
      have e := congrArg (fun e : Y.left ⟶ X.left => e y) hfg
      change (f.left y).1 = (g.left y).1 at e
      rw [e]
      exact (g.left y).2)
  have hqf : q ≫ X.left.homOfLE (show U ⊓ V ≤ U from inf_le_left) = f.left := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact IsOpenImmersion.lift_fac _ _ _
  have hqg : q ≫ X.left.homOfLE (show U ⊓ V ≤ V from inf_le_right) = g.left := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact (IsOpenImmersion.lift_fac _ _ _).trans hfg
  let b : Y ⟶ (opensFunctor X).obj (U ⊓ V) := SmoothSite.homMk q (by
    change q ≫ ((U ⊓ V).ι ≫ X.hom) = Y.hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
    exact MorphismProperty.Over.w f)
  have hbf : b ≫ (opensFunctor X).map (homOfLE inf_le_left) = f := by
    apply MorphismProperty.Over.Hom.ext
    exact hqf
  have hbg : b ≫ (opensFunctor X).map (homOfLE inf_le_right) = g := by
    apply MorphismProperty.Over.Hom.ext
    exact hqg
  have hab := ha (homOfLE (show U ⊓ V ≤ U from inf_le_left))
    (homOfLE (show U ⊓ V ≤ V from inf_le_right)) hi hj (Subsingleton.elim _ _)
  have hh := congrArg (fun e => F.obj.map b.op e) hab
  have hbf' := congrArg (fun e => F.obj.map e.op (a i hi)) hbf
  have hbg' := congrArg (fun e => F.obj.map e.op (a j hj)) hbg
  exact hbf'.symm.trans ((F.obj.map_comp_apply
    ((opensFunctor X).map (homOfLE (show U ⊓ V ≤ U from inf_le_left))).op
    b.op (a i hi)).trans (hh.trans ((F.obj.map_comp_apply
      ((opensFunctor X).map (homOfLE (show U ⊓ V ≤ V from inf_le_right))).op
      b.op (a j hj)).symm.trans hbg')))

theorem opens_coverPreserving (X : SmoothSite S) :
    CoverPreserving (Opens.grothendieckTopology X.left) (topology S)
      (opensFunctor X) := by
  constructor
  intro U R hR x
  obtain ⟨V, f, hf, hx⟩ := hR x.1 x.2
  refine ⟨(opensFunctor X).obj V, (opensFunctor X).map f, ⟨x.1, hx⟩,
    ?_, inferInstance, ?_⟩
  · exact ⟨V, f, 𝟙 _, hf, by simp⟩
  · apply Subtype.ext
    exact Scheme.homOfLE_apply f.le ⟨x.1, hx⟩

instance opens_continuous (X : SmoothSite S) :
    (opensFunctor X).IsContinuous (Opens.grothendieckTopology X.left) (topology S) :=
  Functor.isContinuous_of_coverPreserving (opens_compatible X)
    (opens_coverPreserving X)

instance opens_cocontinuous (X : SmoothSite S) :
    (opensFunctor X).IsCocontinuous (Opens.grothendieckTopology X.left) (topology S) where
  cover_lift {U} {R} hR := by
    intro x hx
    obtain ⟨Y, g, y, hg, hgo, hgy⟩ := hR ⟨x, hx⟩
    have := hgo
    let V : X.left.Opens := (g.left ≫ U.ι).opensRange
    have hVU : V ≤ U := by
      rintro z ⟨t, rfl⟩
      exact (g.left t).2
    let e : Y.left ≅ V.toScheme :=
      IsOpenImmersion.isoOfRangeEq (g.left ≫ U.ι) V.ι (by
        rw [Scheme.Opens.range_ι]
        rfl)
    let q : (opensFunctor X).obj V ⟶ Y := SmoothSite.homMk e.inv (by
      rw [← MorphismProperty.Over.w g]
      change e.inv ≫ (g.left ≫ (U.ι ≫ X.hom)) = V.ι ≫ X.hom
      rw [← Category.assoc g.left U.ι X.hom, ← Category.assoc,
        IsOpenImmersion.isoOfRangeEq_inv_fac])
    have fac : q ≫ g = (opensFunctor X).map (homOfLE hVU) := by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono U.ι).mp
      change e.inv ≫ g.left ≫ U.ι = X.left.homOfLE hVU ≫ U.ι
      rw [Scheme.homOfLE_ι]
      exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
    refine ⟨V, homOfLE hVU, ?_, ?_⟩
    · change R ((opensFunctor X).map (homOfLE hVU))
      rw [← fac]
      exact R.downward_closed hg q
    · exact ⟨y, congrArg Subtype.val hgy⟩

local instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u+1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u+1, u+1, u, u} _

/-- Every actual big-site Zariski sheaf restricts to the usual topological
sheaf on X. Its underlying presheaf and every restriction map are unchanged. -/
def restrictSheaf (X : SmoothSite S)
    (F : Sheaf (topology S) AddCommGrpCat.{u+1}) :
    Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u+1} :=
  ⟨(opensFunctor X).op ⋙ F.obj,
    (opensFunctor X).op_comp_isSheaf (Opens.grothendieckTopology X.left) (topology S) F⟩

/-- Sheafification on the genuine smooth Zariski site restricts to ordinary
small-site sheafification. No separation, transfer or homotopy-invariance
assumption on F is used. -/
def restrictionIso (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) :
    CategoryTheory.sheafify (Opens.grothendieckTopology X.left) ((opensFunctor X).op ⋙ F) ≅
      (opensFunctor X).op ⋙ CategoryTheory.sheafify (topology S) F :=
  (sheafToPresheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u+1}).mapIso
    (((opensFunctor X).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u+1} (Opens.grothendieckTopology X.left) (topology S)).app F)

/-- Identification of the actual canonical units, as natural transformations. -/
theorem restrictionIso_unit (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X.left) ((opensFunctor X).op ⋙ F) ≫
      (restrictionIso X F).hom =
        whiskerLeft (opensFunctor X).op (CategoryTheory.toSheafify (topology S) F) :=
  (opensFunctor X).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u+1} (Opens.grothendieckTopology X.left) (topology S) F


/-- A proved pointwise zero-neighborhood theorem for the actual unit supplies
local injectivity on the Zariski topology. This does not ask for a simultaneous
finite-point neighborhood and does not assert finite-point comparison. -/
theorem locallyInjective_of_open_kernel
    {F G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}} (α : F ⟶ G)
    (hzero : ∀ (X : SmoothSite S) (a : F.obj (op X)), α.app (op X) a = 0 →
      ∀ x : X.left, ∃ (U : X.left.Opens), x ∈ U ∧
        F.map (openInclusion X U).op a = 0) :
    Presheaf.IsLocallyInjective (topology S) α := by
  constructor
  intro X a b hab
  cases X using Opposite.rec with
  | _ X =>
   intro x
   have hz : α.app (op X) (a - b) = 0 := by
     rw [_root_.map_sub, hab, sub_self]
   obtain ⟨U, hx, hU⟩ := hzero X (a - b) hz x
   refine ⟨(opensFunctor X).obj U, openInclusion X U, ⟨x, hx⟩,
     ?_, inferInstance, rfl⟩
   change F.map (openInclusion X U).op a = F.map (openInclusion X U).op b
   exact sub_eq_zero.mp (by simpa only [_root_.map_sub] using hU)

/-- If the canonical map to a Zariski sheaf is locally injective, its canonical
factor through Zariski sheafification is pointwise injective. Applying this to
the Nisnevich unit requires the actual zero-neighborhood theorem above and the
proved Zariski sheaf property of its target; neither is smuggled into S5. -/
theorem sheafifyLift_injective
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1})
    (G : Sheaf (topology S) AddCommGrpCat.{u+1}) (α : F ⟶ G.obj)
    [Presheaf.IsLocallyInjective (topology S) α] :
    ∀ X, Function.Injective ((sheafifyLift (topology S) α G.property).app X) := by
  let β : (presheafToSheaf (topology S) AddCommGrpCat.{u+1}).obj F ⟶ G :=
    ⟨sheafifyLift (topology S) α G.property⟩
  have : Presheaf.IsLocallyInjective (topology S) β.hom := by
    apply (Presheaf.comp_isLocallyInjective_iff (topology S)
      (CategoryTheory.toSheafify (topology S) F) β.hom).mp
    change Presheaf.IsLocallyInjective (topology S)
      (CategoryTheory.toSheafify (topology S) F ≫ sheafifyLift (topology S) α G.property)
    rw [toSheafify_sheafifyLift]
    infer_instance
  exact (Sheaf.isLocallyInjective_iff_injective β).mp inferInstance


omit baseNoetherian

/-- All open neighborhoods of the specified point set, with ordinary inclusion.
There is no density condition and no requirement that the individual points
are closed. Finite nonempty sets in S5 are special cases. -/
def Neighborhoods (X : SmoothSite S) (s : Set X.left) :=
  { U : X.left.Opens // s ⊆ U }

instance (X : SmoothSite S) (s : Set X.left) : PartialOrder (Neighborhoods X s) :=
  inferInstanceAs (PartialOrder { U : X.left.Opens // s ⊆ U })

instance (X : SmoothSite S) (s : Set X.left) : Nonempty (Neighborhoods X s) :=
  ⟨⟨⊤, fun _ _ => trivial⟩⟩

instance (X : SmoothSite S) (s : Set X.left) : IsCodirectedOrder (Neighborhoods X s) :=
  ⟨fun U V => ⟨⟨U.1 ⊓ V.1, fun _ hx => ⟨U.2 hx, V.2 hx⟩⟩,
    (show U.1 ⊓ V.1 ≤ U.1 from inf_le_left),
    (show U.1 ⊓ V.1 ≤ V.1 from inf_le_right)⟩⟩

/-- The actual shrinking-neighborhood direction is filtered. -/
theorem neighborhood_index_filtered (X : SmoothSite S) (s : Set X.left) :
    IsFiltered (Neighborhoods X s)ᵒᵖ := inferInstance

def neighborhoodInclusion (X : SmoothSite S) (s : Set X.left) :
    Neighborhoods X s ⥤ X.left.Opens :=
  (show Monotone (fun U : Neighborhoods X s => U.1) from fun _ _ h => h).functor

/-- The literal abelian-group colimit over every open containing s. -/
def neighborhoodValue (X : SmoothSite S)
    (P : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left) :
    AddCommGrpCat.{u+1} :=
  colimit ((neighborhoodInclusion X s).op ⋙ P)

def neighborhoodMap (X : SmoothSite S)
    {P Q : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (η : P ⟶ Q) (s : Set X.left) :
    neighborhoodValue X P s ⟶ neighborhoodValue X Q s :=
  colim.map (whiskerLeft (neighborhoodInclusion X s).op η)

/-- Insertion of an actual neighborhood section into the colimit. -/
def neighborhoodι (X : SmoothSite S)
    (P : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left)
    (U : Neighborhoods X s) : P.obj (op U.1) ⟶ neighborhoodValue X P s :=
  colimit.ι ((neighborhoodInclusion X s).op ⋙ P) (op U)

/-- Every element has an actual representative on a neighborhood of the whole
specified point set. -/
theorem neighborhood_exists_rep (X : SmoothSite S)
    (P : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left)
    (a : neighborhoodValue X P s) :
    ∃ (U : Neighborhoods X s) (t : P.obj (op U.1)), neighborhoodι X P s U t = a := by
  obtain ⟨U, t, ht⟩ := Concrete.colimit_exists_rep ((neighborhoodInclusion X s).op ⋙ P) a
  exact ⟨U.unop, t, ht⟩

/-- Equality means equality after one common shrink that still contains every
specified point. This is an equality of actual restriction maps. -/
theorem neighborhood_rep_eq_iff_exists (X : SmoothSite S)
    (P : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left)
    (U V : Neighborhoods X s) (a : P.obj (op U.1)) (b : P.obj (op V.1)) :
    neighborhoodι X P s U a = neighborhoodι X P s V b ↔
      ∃ (W : Neighborhoods X s) (hWU : W.1 ≤ U.1) (hWV : W.1 ≤ V.1),
        P.map (homOfLE hWU).op a = P.map (homOfLE hWV).op b := by
  constructor
  · intro h
    obtain ⟨W, f, g, hW⟩ := Concrete.colimit_exists_of_rep_eq
      ((neighborhoodInclusion X s).op ⋙ P) a b h
    exact ⟨W.unop, f.unop.le, g.unop.le, hW⟩
  · rintro ⟨W, hWU, hWV, hW⟩
    exact Concrete.colimit_rep_eq_of_exists ((neighborhoodInclusion X s).op ⋙ P) a b
      ⟨op W, (homOfLE hWU).op, (homOfLE hWV).op, hW⟩

/-- A representative vanishes iff it actually vanishes on a smaller
neighborhood of the entire point set. -/
theorem neighborhood_rep_zero_iff (X : SmoothSite S)
    (P : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left)
    (U : Neighborhoods X s) (a : P.obj (op U.1)) :
    neighborhoodι X P s U a = 0 ↔
      ∃ (V : Neighborhoods X s) (hVU : V.1 ≤ U.1), P.map (homOfLE hVU).op a = 0 := by
  rw [show (0 : neighborhoodValue X P s) = neighborhoodι X P s U 0 from
    (map_zero _).symm, neighborhood_rep_eq_iff_exists]
  constructor
  · rintro ⟨V, hVU, hVU', hV⟩
    exact ⟨V, hVU, hV.trans (map_zero _)⟩
  · rintro ⟨V, hVU, hV⟩
    exact ⟨V, hVU, hVU, hV.trans (map_zero _).symm⟩

theorem neighborhoodMap_representative (X : SmoothSite S)
    {P Q : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (η : P ⟶ Q) (s : Set X.left)
    (U : Neighborhoods X s) :
    neighborhoodι X P s U ≫ neighborhoodMap X η s =
      η.app (op U.1) ≫ neighborhoodι X Q s U :=
  colimit.ι_map (whiskerLeft (neighborhoodInclusion X s).op η) (op U)

@[simp]
theorem neighborhoodMap_apply_rep (X : SmoothSite S)
    {P Q : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (η : P ⟶ Q) (s : Set X.left)
    (U : Neighborhoods X s) (a : P.obj (op U.1)) :
    neighborhoodMap X η s (neighborhoodι X P s U a) =
      neighborhoodι X Q s U (η.app (op U.1) a) :=
  ConcreteCategory.congr_hom (neighborhoodMap_representative X η s U) a

theorem neighborhoodMap_comp (X : SmoothSite S)
    {P Q R : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (α : P ⟶ Q) (β : Q ⟶ R)
    (s : Set X.left) :
    neighborhoodMap X (α ≫ β) s = neighborhoodMap X α s ≫ neighborhoodMap X β s := by
  unfold neighborhoodMap
  rw [← colim.map_comp]
  rfl

/-- Pointwise injections remain injective on the actual filtered value. -/
theorem neighborhoodMap_injective (X : SmoothSite S)
    {P Q : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (η : P ⟶ Q) (s : Set X.left)
    (hη : ∀ U : X.left.Opens, Function.Injective (η.app (op U))) :
    Function.Injective (neighborhoodMap X η s) := by
  intro a b hab
  obtain ⟨U, a, rfl⟩ := neighborhood_exists_rep X P s a
  obtain ⟨V, b, rfl⟩ := neighborhood_exists_rep X P s b
  rw [neighborhoodMap_apply_rep, neighborhoodMap_apply_rep] at hab
  obtain ⟨W, hWU, hWV, hW⟩ := (neighborhood_rep_eq_iff_exists X Q s U V _ _).mp hab
  apply (neighborhood_rep_eq_iff_exists X P s U V a b).mpr
  refine ⟨W, hWU, hWV, hη W.1 ?_⟩
  exact (η.naturality_apply (homOfLE hWU).op a).trans
    (hW.trans (η.naturality_apply (homOfLE hWV).op b).symm)

/-- Actual lifts after a shrink produce surjectivity on the colimit. The
hypothesis is explicit representative data, not surjectivity of the target map. -/
theorem neighborhoodMap_surjective_of_eventual_lift (X : SmoothSite S)
    {P Q : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (η : P ⟶ Q) (s : Set X.left)
    (hlift : ∀ (U : Neighborhoods X s) (b : Q.obj (op U.1)),
      ∃ (V : Neighborhoods X s) (hVU : V.1 ≤ U.1) (a : P.obj (op V.1)),
        η.app (op V.1) a = Q.map (homOfLE hVU).op b) :
    Function.Surjective (neighborhoodMap X η s) := by
  intro b
  obtain ⟨U, b, rfl⟩ := neighborhood_exists_rep X Q s b
  obtain ⟨V, hVU, a, ha⟩ := hlift U b
  refine ⟨neighborhoodι X P s V a, ?_⟩
  rw [neighborhoodMap_apply_rep]
  apply (neighborhood_rep_eq_iff_exists X Q s V U _ _).mpr
  refine ⟨V, le_rfl, hVU, ?_⟩
  simpa using ha

/-- A kernel section killed after an actual common shrink gives injectivity
on the colimit. This does not replace simultaneous vanishing by pointwise
vanishing; the witness V must still contain all of s. -/
theorem neighborhoodMap_injective_of_eventual_zero (X : SmoothSite S)
    {P Q : X.left.Opensᵒᵖ ⥤ AddCommGrpCat.{u+1}} (η : P ⟶ Q) (s : Set X.left)
    (hzero : ∀ (U : Neighborhoods X s) (a : P.obj (op U.1)), η.app (op U.1) a = 0 →
      ∃ (V : Neighborhoods X s) (hVU : V.1 ≤ U.1), P.map (homOfLE hVU).op a = 0) :
    Function.Injective (neighborhoodMap X η s) := by
  apply (injective_iff_map_eq_zero (neighborhoodMap X η s).hom).mpr
  intro a ha
  obtain ⟨U, a, rfl⟩ := neighborhood_exists_rep X P s a
  rw [neighborhoodMap_apply_rep] at ha
  obtain ⟨V, hVU, hV⟩ := (neighborhood_rep_zero_iff X Q s U _).mp ha
  have hVa : η.app (op V.1) (P.map (homOfLE hVU).op a) = 0 :=
    (η.naturality_apply (homOfLE hVU).op a).trans hV
  obtain ⟨W, hWV, hW⟩ := hzero V _ hVa
  apply (neighborhood_rep_zero_iff X P s U a).mpr
  refine ⟨W, hWV.trans hVU, ?_⟩
  have hc : (homOfLE (hWV.trans hVU) : W.1 ⟶ U.1) =
      (homOfLE hWV : W.1 ⟶ V.1) ≫ homOfLE hVU := Subsingleton.elim _ _
  rw [hc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hW

include baseNoetherian

/-- S5's value of an actual smooth-site presheaf, with no extension of the site
or chosen replacement for its values. -/
def siteNeighborhoodValue (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left) :
    AddCommGrpCat.{u+1} :=
  neighborhoodValue X ((opensFunctor X).op ⋙ F) s

/-- The actual map eta_S in the problem statement. -/
def siteNeighborhoodUnit (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left) :
    siteNeighborhoodValue X F s ⟶
      siteNeighborhoodValue X (CategoryTheory.sheafify (topology S) F) s :=
  neighborhoodMap X
    (whiskerLeft (opensFunctor X).op (CategoryTheory.toSheafify (topology S) F)) s

/-- On each representative, eta_S is exactly the original Zariski unit. -/
theorem siteNeighborhoodUnit_representative (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left)
    (U : Neighborhoods X s) :
    colimit.ι ((neighborhoodInclusion X s).op ⋙ (opensFunctor X).op ⋙ F) (op U) ≫
      siteNeighborhoodUnit X F s =
    (CategoryTheory.toSheafify (topology S) F).app (op ((opensFunctor X).obj U.1)) ≫
      colimit.ι ((neighborhoodInclusion X s).op ⋙ (opensFunctor X).op ⋙
        CategoryTheory.sheafify (topology S) F) (op U) := by
  exact colimit.ι_map
    (whiskerLeft (neighborhoodInclusion X s).op
      (whiskerLeft (opensFunctor X).op (CategoryTheory.toSheafify (topology S) F)))
    (op U)

/-- Big/small comparison on the same all-open-neighborhood colimit. -/
def neighborhoodRestrictionIso (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left) :
    neighborhoodValue X
      (CategoryTheory.sheafify (Opens.grothendieckTopology X.left)
        ((opensFunctor X).op ⋙ F)) s ≅
      siteNeighborhoodValue X (CategoryTheory.sheafify (topology S) F) s :=
  colim.mapIso (isoWhiskerLeft (neighborhoodInclusion X s).op (restrictionIso X F))

/-- The colimit comparison respects the literal units, including for every
finite point set. It is not a supplied isomorphism hypothesis. -/
theorem neighborhoodRestrictionIso_unit (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left) :
    neighborhoodMap X
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.left)
        ((opensFunctor X).op ⋙ F)) s ≫ (neighborhoodRestrictionIso X F s).hom =
      siteNeighborhoodUnit X F s := by
  change colim.map _ ≫ colim.map _ = colim.map _
  rw [← colim.map_comp]
  change colim.map (whiskerLeft (neighborhoodInclusion X s).op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X.left)
        ((opensFunctor X).op ⋙ F)) ≫
    whiskerLeft (neighborhoodInclusion X s).op (restrictionIso X F).hom) = _
  rw [← whiskerLeft_comp, restrictionIso_unit]


/-- Assembly of the actual geometric conclusions into S5's original map.
Both hypotheses ask for explicit sections on smaller neighborhoods that still
contain all of s; neither assumes invertibility, separatedness, nor a change
of topology. They are intermediate consumers to be instantiated by the proved
finite-correspondence geometry. -/
theorem siteNeighborhoodUnit_isIso_of_eventual_zero_lift (X : SmoothSite S)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}) (s : Set X.left)
    (hzero : ∀ (U : Neighborhoods X s) (a : F.obj (op ((opensFunctor X).obj U.1))),
      (CategoryTheory.toSheafify (topology S) F).app (op ((opensFunctor X).obj U.1)) a = 0 →
      ∃ (V : Neighborhoods X s) (hVU : V.1 ≤ U.1),
        F.map ((opensFunctor X).map (homOfLE hVU)).op a = 0)
    (hlift : ∀ (U : Neighborhoods X s)
        (b : (CategoryTheory.sheafify (topology S) F).obj (op ((opensFunctor X).obj U.1))),
      ∃ (V : Neighborhoods X s) (hVU : V.1 ≤ U.1)
        (a : F.obj (op ((opensFunctor X).obj V.1))),
        (CategoryTheory.toSheafify (topology S) F).app (op ((opensFunctor X).obj V.1)) a =
          (CategoryTheory.sheafify (topology S) F).map
            ((opensFunctor X).map (homOfLE hVU)).op b) :
    IsIso (siteNeighborhoodUnit X F s) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨neighborhoodMap_injective_of_eventual_zero X
      (whiskerLeft (opensFunctor X).op (CategoryTheory.toSheafify (topology S) F)) s hzero,
    neighborhoodMap_surjective_of_eventual_lift X
      (whiskerLeft (opensFunctor X).op (CategoryTheory.toSheafify (topology S) F)) s hlift⟩

end
end MathGauge.GP003.SmoothZariski
