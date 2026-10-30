/-
Portions copyright (c) 2026 kangxyz and Motivic Cohomology contributors.
SPDX-License-Identifier: Apache-2.0

Math Gauge GP003 S5: original ambient-neighborhood comparison.
The open-image transport follows Motivic/Cohomology/A1/LocalVanishing/OpenImage
at kangxyz/motivic a6805c4a87cdfd7717dd7a94039246a167f15380:
https://github.com/kangxyz/motivic/tree/a6805c4a87cdfd7717dd7a94039246a167f15380
Upstream license: https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/LICENSE

Only the affine neighborhood already chosen in S5 is used. The original
ambient scheme need not be affine or quasi-affine. Both eventual-section
premises are instantiated by the proved transfer geometry in S5Complete.
-/
import MathGauge.GP003.S5SiteBridge
import MathGauge.GP003.S5SimultaneousUniversal

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u
namespace MathGauge.GP003.Transfers
open MathGauge.GP003.SmoothZariski
variable {k : Type u} [Field k]

/-- The supplied affine neighborhood suffices to find an affine refinement
inside every original neighborhood. No affine or quasi-affine hypothesis is
placed on the ambient smooth scheme. -/
theorem exists_affine_subneighborhood (X : SmoothSite (Spec (.of k)))
    (s : Finset X.left) (W : X.left.Opens) (hW : IsAffineOpen W)
    (hsW : (↑s : Set X.left) ⊆ W) (U : X.left.Opens)
    (hsU : (↑s : Set X.left) ⊆ U) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ (↑s : Set X.left) ⊆ V ∧ V ≤ U := by
  let : IsAffine W.toScheme := hW
  let T : Set W.toScheme := W.ι ⁻¹' (↑s : Set X.left)
  have hT : T.Finite := s.finite_toSet.preimage W.ι.isOpenEmbedding.injective.injOn
  obtain ⟨V, hV, hTV, hVU⟩ := S5Simultaneous.exists_affineOpen_inside_finitelyMany
    (W.ι ⁻¹ᵁ U) T hT (fun x hx => hsU hx)
  let : IsAffine V.toScheme := hV
  have hAffine : IsAffineOpen (W.ι ''ᵁ V) := by
    simpa only [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι] using
      (isAffineOpen_opensRange (V.ι ≫ W.ι))
  refine ⟨W.ι ''ᵁ V, hAffine, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hsW hx⟩, hTV hx, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hVU hy

/-- The inverse open-image isomorphism as an actual map of smooth-site objects. -/
def openImageInverse {Y X : SmoothSite (Spec (.of k))}
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    (opensFunctor X).obj f.left.opensRange ⟶ Y :=
  SmoothSite.homMk f.left.isoOpensRange.inv (by
    change f.left.isoOpensRange.inv ≫ Y.hom = f.left.opensRange.ι ≫ X.hom
    have hw : f.left ≫ X.hom = Y.hom := f.w
    rw [← hw, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp])

@[reassoc]
theorem openImageInverse_comp {Y X : SmoothSite (Spec (.of k))}
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    openImageInverse f ≫ f = openInclusion X f.left.opensRange := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.Hom.isoOpensRange_inv_comp f.left

instance open_comp_left {Y Z X : SmoothSite (Spec (.of k))}
    (f : Y ⟶ Z) (g : Z ⟶ X) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion (f ≫ g).left := by
  change IsOpenImmersion (f.left ≫ g.left)
  infer_instance

/-- Composition through an actual open subset agrees with its literal
restriction arrow after transporting the source to the open image. -/
theorem openImageInverse_restriction {Y X : SmoothSite (Spec (.of k))}
    (U : X.left.Opens) (r : Y ⟶ (opensFunctor X).obj U)
    [IsOpenImmersion r.left] :
    let f := r ≫ openInclusion X U
    let V := f.left.opensRange
    ∃ hVU : V ≤ U,
      openImageInverse f ≫ r = (opensFunctor X).map (homOfLE hVU) := by
  let f := r ≫ openInclusion X U
  have : IsOpenImmersion f.left := by
    change IsOpenImmersion (r.left ≫ U.ι)
    infer_instance
  have hVU : f.left.opensRange ≤ U := by
    rintro x ⟨y, rfl⟩
    exact (r.left y).property
  refine ⟨hVU, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono U.ι).mp
  change (openImageInverse f).left ≫ r.left ≫ U.ι = X.left.homOfLE hVU ≫ U.ι
  rw [X.left.homOfLE_ι hVU]
  exact Scheme.Hom.isoOpensRange_inv_comp f.left


/-- Explicit affine section data imply the literal original neighborhood-unit
isomorphism. Every refinement still contains the whole prescribed finite set. -/
theorem siteNeighborhoodUnit_isIso_of_affine_zero_lift
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u+1})
    (hzero : ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left]
      (t : Finset Y.left), t.Nonempty → ∀ a : F.obj (op Y),
      (CategoryTheory.toSheafify (topology (Spec (.of k))) F).app (op Y) a = 0 →
      ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ Y),
        IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑t : Set Y.left) ⊆ Set.range r.left ∧
          F.map r.op a = 0)
    (hlift : ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left]
      (t : Finset Y.left), t.Nonempty →
      ∀ b : (CategoryTheory.sheafify (topology (Spec (.of k))) F).obj (op Y),
      ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ Y),
        IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑t : Set Y.left) ⊆ Set.range r.left ∧
          ∃ a : F.obj (op S),
            (CategoryTheory.toSheafify (topology (Spec (.of k))) F).app (op S) a =
              (CategoryTheory.sheafify (topology (Spec (.of k))) F).map r.op b)
    (X : SmoothSite (Spec (.of k))) (s : Finset X.left) (hs : s.Nonempty)
    (W : X.left.Opens) (hW : IsAffineOpen W) (hsW : (↑s : Set X.left) ⊆ W) :
    IsIso (siteNeighborhoodUnit X F (↑s : Set X.left)) := by
  classical
  let G := CategoryTheory.sheafify (topology (Spec (.of k))) F
  let η := CategoryTheory.toSheafify (topology (Spec (.of k))) F
  apply siteNeighborhoodUnit_isIso_of_eventual_zero_lift
  · intro U a ha
    obtain ⟨V, hV, hsV, hVU⟩ := exists_affine_subneighborhood X s W hW hsW U.1 U.2
    let A := (opensFunctor X).obj V
    let : IsAffine A.left := hV
    let T : Set A.left := V.ι ⁻¹' (↑s : Set X.left)
    have hT : T.Finite := s.finite_toSet.preimage V.ι.isOpenEmbedding.injective.injOn
    let t : Finset A.left := hT.toFinset
    have ht : t.Nonempty := by
      obtain ⟨x, hx⟩ := hs
      exact ⟨⟨x, hsV hx⟩, hT.mem_toFinset.mpr hx⟩
    let q : A ⟶ (opensFunctor X).obj U.1 := (opensFunctor X).map (homOfLE hVU)
    have haA : η.app (op A) (F.map q.op a) = 0 := by
      rw [η.naturality_apply, ha, map_zero]
    obtain ⟨S, r, hS, hr, htr, hz⟩ := hzero A t ht (F.map q.op a) haA
    have : IsOpenImmersion r.left := hr
    have : IsOpenImmersion q.left := inferInstanceAs
      (IsOpenImmersion ((opensFunctor X).map (homOfLE hVU)).left)
    let r' := r ≫ q
    let f := r' ≫ openInclusion X U.1
    have hsf : (↑s : Set X.left) ⊆ f.left.opensRange := by
      intro x hx
      obtain ⟨y, hy⟩ := htr (hT.mem_toFinset.mpr (show (⟨x, hsV hx⟩ : A.left) ∈ T from hx))
      refine ⟨y, ?_⟩
      have hfleft : f.left = r.left ≫ V.ι := by
        change (r.left ≫ q.left) ≫ U.1.ι = r.left ≫ V.ι
        rw [Category.assoc]
        exact congrArg (fun h => r.left ≫ h) (X.left.homOfLE_ι hVU)
      exact (congrArg (fun h => h y) hfleft).trans
        (congrArg (fun z : A.left => V.ι z) hy)
    obtain ⟨hOU, hg⟩ := openImageInverse_restriction U.1 r'
    refine ⟨⟨f.left.opensRange, hsf⟩, hOU, ?_⟩
    change F.map ((opensFunctor X).map (homOfLE hOU)).op a = 0
    rw [← hg, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    have hz' : F.map r'.op a = 0 := by
      simpa only [r', op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hz
    rw [hz', map_zero]
  · intro U b
    obtain ⟨V, hV, hsV, hVU⟩ := exists_affine_subneighborhood X s W hW hsW U.1 U.2
    let A := (opensFunctor X).obj V
    let : IsAffine A.left := hV
    let T : Set A.left := V.ι ⁻¹' (↑s : Set X.left)
    have hT : T.Finite := s.finite_toSet.preimage V.ι.isOpenEmbedding.injective.injOn
    let t : Finset A.left := hT.toFinset
    have ht : t.Nonempty := by
      obtain ⟨x, hx⟩ := hs
      exact ⟨⟨x, hsV hx⟩, hT.mem_toFinset.mpr hx⟩
    let q : A ⟶ (opensFunctor X).obj U.1 := (opensFunctor X).map (homOfLE hVU)
    obtain ⟨S, r, hS, hr, htr, a, ha⟩ := hlift A t ht (G.map q.op b)
    have : IsOpenImmersion r.left := hr
    have : IsOpenImmersion q.left := inferInstanceAs
      (IsOpenImmersion ((opensFunctor X).map (homOfLE hVU)).left)
    let r' := r ≫ q
    let f := r' ≫ openInclusion X U.1
    have hsf : (↑s : Set X.left) ⊆ f.left.opensRange := by
      intro x hx
      obtain ⟨y, hy⟩ := htr (hT.mem_toFinset.mpr (show (⟨x, hsV hx⟩ : A.left) ∈ T from hx))
      refine ⟨y, ?_⟩
      have hfleft : f.left = r.left ≫ V.ι := by
        change (r.left ≫ q.left) ≫ U.1.ι = r.left ≫ V.ι
        rw [Category.assoc]
        exact congrArg (fun h => r.left ≫ h) (X.left.homOfLE_ι hVU)
      exact (congrArg (fun h => h y) hfleft).trans
        (congrArg (fun z : A.left => V.ι z) hy)
    obtain ⟨hOU, hg⟩ := openImageInverse_restriction U.1 r'
    let g := openImageInverse f
    refine ⟨⟨f.left.opensRange, hsf⟩, hOU, F.map g.op a, ?_⟩
    change η.app (op ((opensFunctor X).obj f.left.opensRange)) (F.map g.op a) =
      G.map ((opensFunctor X).map (homOfLE hOU)).op b
    rw [η.naturality_apply, ha, ← hg]
    simp only [r', op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl

end MathGauge.GP003.Transfers
