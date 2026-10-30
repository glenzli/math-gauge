/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5SiteBridge
import Motivic.Cohomology.A1.Moving.OneSided
import Motivic.Transfers.Presheaf.FiniteScalarComparison
import Motivic.Transfers.Presheaf.FiniteScalarDescent
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarMarkedOpen

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme
universe v u
namespace MathGauge.GP003.Transfers
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- A native scalar correspondence is carried to the original finite scalar
models by the actual forget-base functor and canonical graph isomorphisms. -/
def scalarCorrespondence {U V : SmoothSite (Spec (.of k))}
    (β : Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj U) ⟶
      Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj V)) :
    Cor.mk (SmoothSite.finiteScalarExtension (E := E) U) ⟶
      Cor.mk (SmoothSite.finiteScalarExtension (E := E) V) :=
  (Cor.graphFunctor k).map (SmoothSite.fieldBaseChangeFiniteScalarIso (L := E) U).inv ≫
    (Cor.finiteSeparableForgetBase k E).map β ≫
    (Cor.graphFunctor k).map (SmoothSite.fieldBaseChangeFiniteScalarIso (L := E) V).hom

/-- This comparison is an equality of original signed-correspondence actions. -/
theorem transfer_scalarCorrespondence (P : PresheafWithTransfers.{v} k)
    {U V : SmoothSite (Spec (.of k))}
    (β : Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj U) ⟶
      Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj V)) :
    P.transfer (scalarCorrespondence β) =
      (finiteScalarSectionIso (L := E) P V).inv ≫
        (finiteSeparableExtension E P).transfer β ≫
        (finiteScalarSectionIso (L := E) P U).hom := by
  simp only [scalarCorrespondence, transfer_comp, Category.assoc]
  rfl

/-- Canonical comparison transports an actual native factorization to the
ordinary scalar models, with the actual original restrictions unchanged. -/
theorem scalarCorrespondence_factor (P : PresheafWithTransfers.{v} k)
    {U V X : SmoothSite (Spec (.of k))} (r : U ⟶ X) (a : V ⟶ X)
    (β : Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj U) ⟶
      Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj V))
    (hβ : (finiteSeparableExtension E P).transfer ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map a)) ≫
        (finiteSeparableExtension E P).transfer β =
      (finiteSeparableExtension E P).transfer ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map r))) :
    P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) a)) ≫
        P.transfer (scalarCorrespondence β) =
      P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) r)) := by
  apply (cancel_epi (finiteScalarSectionIso (L := E) P X).hom).mp
  rw [← Category.assoc, ← finiteScalarSectionIso_naturality,
    transfer_scalarCorrespondence]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hβ, finiteScalarSectionIso_naturality]

/-- The whole finite-flat scalar trace, followed by the actual signed scalar
correspondence and scalar projection. It does not depend on the coefficient P. -/
def tracedScalarCorrespondence {U V : SmoothSite (Spec (.of k))}
    (β : Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj U) ⟶
      Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj V)) : Cor.mk U ⟶ Cor.mk V :=
  Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U) ≫
    scalarCorrespondence β ≫
    (Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) V)

/-- The descended operator factors degree times the original restriction. -/
theorem tracedScalarCorrespondence_factor (P : PresheafWithTransfers.{v} k)
    {U V X : SmoothSite (Spec (.of k))} (r : U ⟶ X) [Flat r.left] (a : V ⟶ X)
    (β : Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj U) ⟶
      Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k E)).obj V))
    (hβ : (finiteSeparableExtension E P).transfer ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map a)) ≫
        (finiteSeparableExtension E P).transfer β =
      (finiteSeparableExtension E P).transfer ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map r))) :
    P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer (tracedScalarCorrespondence β) =
      (Module.finrank k E : ℤ) • P.transfer ((Cor.graphFunctor k).map r) := by
  have hφ := scalarCorrespondence_factor P r a β hβ
  simpa only [tracedScalarCorrespondence, transfer_comp, finiteScalarFactorization,
    Category.assoc] using restriction_finiteScalarFactorization P a r
      (P.transfer (scalarCorrespondence β)) hφ

variable {L : Type u} [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Two actual scalar moving endpoints on a common original open give one
original signed correspondence. Its factorization holds for every HI PST,
so the same correspondence can act on F and its proven HI sheafification. -/
theorem exists_uniform_factor_of_coprime_native_endpoints
    {U V X : SmoothSite (Spec (.of k))} (r : U ⟶ X) [Flat r.left] (a : V ⟶ X)
    {T : SmoothSite (Spec (.of E))} {T' : SmoothSite (Spec (.of L))}
    (rE : T ⟶ (SmoothSite.fieldBaseChange (algebraMap k E)).obj X)
    (rL : T' ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj X)
    (eE : (SmoothSite.fieldBaseChange (algebraMap k E)).obj U ⟶ T)
    (eL : (SmoothSite.fieldBaseChange (algebraMap k L)).obj U ⟶ T')
    (heE : eE ≫ rE = (SmoothSite.fieldBaseChange (algebraMap k E)).map r)
    (heL : eL ≫ rL = (SmoothSite.fieldBaseChange (algebraMap k L)).map r)
    (hmE : OneSidedMovingEndpoints.HasMovingEndpoints rE
      ((SmoothSite.fieldBaseChange (algebraMap k E)).map a))
    (hmL : OneSidedMovingEndpoints.HasMovingEndpoints rL
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ β : Cor.mk U ⟶ Cor.mk V, ∀ (P : PresheafWithTransfers.{v} k), P.IsA1Invariant →
      P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer β =
        P.transfer ((Cor.graphFunctor k).map r) := by
  obtain ⟨βE, αE, hE0, hE1⟩ := hmE
  obtain ⟨βL, αL, hL0, hL1⟩ := hmL
  let γE := (Cor.graphFunctor E).map eE ≫ βE
  let γL := (Cor.graphFunctor L).map eL ≫ βL
  let m := Module.finrank k E
  let n := Module.finrank k L
  refine ⟨Nat.gcdA m n • tracedScalarCorrespondence γE +
    Nat.gcdB m n • tracedScalarCorrespondence γL, ?_⟩
  intro P hP
  have hγE : (finiteSeparableExtension E P).transfer ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map a)) ≫
        (finiteSeparableExtension E P).transfer γE =
      (finiteSeparableExtension E P).transfer ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map r)) := by
    rw [show γE = (Cor.graphFunctor E).map eE ≫ βE from rfl, transfer_comp,
      ← Category.assoc, ← restriction_factor_of_moving_endpoints
        (finiteSeparableExtension E P) (finiteSeparableExtension_isA1Invariant E P hP)
        rE ((SmoothSite.fieldBaseChange (algebraMap k E)).map a) βE αE hE0 hE1,
      ← transfer_comp, ← Functor.map_comp, heE]
  have hγL : (finiteSeparableExtension L P).transfer ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map a)) ≫
        (finiteSeparableExtension L P).transfer γL =
      (finiteSeparableExtension L P).transfer ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map r)) := by
    rw [show γL = (Cor.graphFunctor L).map eL ≫ βL from rfl, transfer_comp,
      ← Category.assoc, ← restriction_factor_of_moving_endpoints
        (finiteSeparableExtension L P) (finiteSeparableExtension_isA1Invariant L P hP)
        rL ((SmoothSite.fieldBaseChange (algebraMap k L)).map a) βL αL hL0 hL1,
      ← transfer_comp, ← Functor.map_comp, heL]
  rw [transfer_add, transfer_zsmul, transfer_zsmul,
    Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    tracedScalarCorrespondence_factor P r a γE hγE,
    tracedScalarCorrespondence_factor P r a γL hγL,
    smul_smul, smul_smul, ← add_smul]
  have hd : Nat.gcdA m n * (m : ℤ) + Nat.gcdB m n * (n : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA m n), mul_comm (Nat.gcdB m n), ← Nat.gcd_eq_gcd_ab,
      hdegree.gcd_eq_one, Nat.cast_one]
  rw [hd, one_smul]

/-- If an extension open contains the entire preimage of an original open,
the actual native base change factors through that extension open. -/
theorem exists_native_scalar_open_factor
    (X : SmoothSite (Spec (.of k))) (U : X.left.Opens)
    {T : SmoothSite (Spec (.of E))}
    (rE : T ⟶ (SmoothSite.fieldBaseChange (algebraMap k E)).obj X)
    [IsOpenImmersion rE.left]
    (hU : (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹ᵁ U ≤ rE.left.opensRange) :
    ∃ e : (SmoothSite.fieldBaseChange (algebraMap k E)).obj
        ((SmoothZariski.opensFunctor X).obj U) ⟶ T,
      e ≫ rE = (SmoothSite.fieldBaseChange (algebraMap k E)).map
        (SmoothZariski.openInclusion X U) := by
  let U₀ := (SmoothZariski.opensFunctor X).obj U
  let j := SmoothZariski.openInclusion X U
  let m := (SmoothSite.fieldBaseChange (algebraMap k E)).map j
  have hn : m.left ≫ (SmoothSite.finiteScalarProjection (E := E) X).left =
      (SmoothSite.finiteScalarProjection (E := E) U₀).left ≫ U.ι :=
    SmoothSite.baseChange_map_fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) j
  have hr : Set.range m.left ⊆ Set.range rE.left := by
    rintro _ ⟨y, rfl⟩
    apply hU
    have he := congrArg (fun f => f y) hn
    change (SmoothSite.finiteScalarProjection (E := E) X).left (m.left y) =
      U.ι ((SmoothSite.finiteScalarProjection (E := E) U₀).left y) at he
    change (SmoothSite.finiteScalarProjection (E := E) X).left (m.left y) ∈ U
    rw [he]
    exact ((SmoothSite.finiteScalarProjection (E := E) U₀).left y).property
  let q := IsOpenImmersion.lift rE.left m.left hr
  have hq : q ≫ rE.left = m.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨SmoothSite.homMk q ?_, ?_⟩
  · rw [← MorphismProperty.Over.w rE, ← Category.assoc, hq, MorphismProperty.Over.w m]
  · apply MorphismProperty.Over.Hom.ext
    exact hq

/-- The two complete preimages descend to one original open containing every
mark. Arbitrary chosen lifts would not suffice for this construction. -/
theorem exists_common_open_of_full_scalar_preimages
    (X : SmoothSite (Spec (.of k))) (marks : Set X.left)
    {T : SmoothSite (Spec (.of E))} {T' : SmoothSite (Spec (.of L))}
    (rE : T ⟶ (SmoothSite.fieldBaseChange (algebraMap k E)).obj X)
    (rL : T' ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj X)
    [IsOpenImmersion rE.left] [IsOpenImmersion rL.left]
    (hE : (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹' marks ⊆ Set.range rE.left)
    (hL : (SmoothSite.finiteScalarProjection (E := L) X).left ⁻¹' marks ⊆ Set.range rL.left) :
    ∃ (U : X.left.Opens), marks ⊆ (U : Set X.left) ∧
      ∃ (eE : (SmoothSite.fieldBaseChange (algebraMap k E)).obj
          ((SmoothZariski.opensFunctor X).obj U) ⟶ T)
        (eL : (SmoothSite.fieldBaseChange (algebraMap k L)).obj
          ((SmoothZariski.opensFunctor X).obj U) ⟶ T'),
        eE ≫ rE = (SmoothSite.fieldBaseChange (algebraMap k E)).map
          (SmoothZariski.openInclusion X U) ∧
        eL ≫ rL = (SmoothSite.fieldBaseChange (algebraMap k L)).map
          (SmoothZariski.openInclusion X U) := by
  obtain ⟨U, hmarks, hUE, hUL⟩ :=
    (SmoothSite.finiteScalarProjection (E := E) X).left.exists_common_marked_open
      (SmoothSite.finiteScalarProjection (E := L) X).left
      rE.left.opensRange rL.left.opensRange marks hE hL
  obtain ⟨eE, heE⟩ := exists_native_scalar_open_factor X U rE hUE
  obtain ⟨eL, heL⟩ := exists_native_scalar_open_factor X U rL hUL
  exact ⟨U, hmarks, eE, eL, heE, heL⟩

/-- Actual finite scalar moving geometry descends by original trace and Bezout.
The returned beta is a single signed finite correspondence, independent of the
presheaf and section. All marks remain in its original source neighborhood. -/
theorem exists_uniform_factor_of_coprime_scalar_moving
    (X : SmoothSite (Spec (.of k))) {V : SmoothSite (Spec (.of k))}
    (a : V ⟶ X) (marks : Set X.left)
    {T : SmoothSite (Spec (.of E))} {T' : SmoothSite (Spec (.of L))}
    (rE : T ⟶ (SmoothSite.fieldBaseChange (algebraMap k E)).obj X)
    (rL : T' ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj X)
    [IsOpenImmersion rE.left] [IsOpenImmersion rL.left]
    (hE : (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹' marks ⊆ Set.range rE.left)
    (hL : (SmoothSite.finiteScalarProjection (E := L) X).left ⁻¹' marks ⊆ Set.range rL.left)
    (hmE : OneSidedMovingEndpoints.HasMovingEndpoints rE
      ((SmoothSite.fieldBaseChange (algebraMap k E)).map a))
    (hmL : OneSidedMovingEndpoints.HasMovingEndpoints rL
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ (U : X.left.Opens), marks ⊆ (U : Set X.left) ∧
      ∃ β : Cor.mk ((SmoothZariski.opensFunctor X).obj U) ⟶ Cor.mk V,
        ∀ (P : PresheafWithTransfers.{v} k), P.IsA1Invariant →
          P.transfer ((Cor.graphFunctor k).map a) ≫ P.transfer β =
            P.transfer ((Cor.graphFunctor k).map (SmoothZariski.openInclusion X U)) := by
  obtain ⟨U, hU, eE, eL, heE, heL⟩ :=
    exists_common_open_of_full_scalar_preimages X marks rE rL hE hL
  have : Flat (SmoothZariski.openInclusion X U).left := inferInstance
  obtain ⟨β, hβ⟩ := exists_uniform_factor_of_coprime_native_endpoints
    (SmoothZariski.openInclusion X U) a rE rL eE eL heE heL hmE hmL hdegree
  exact ⟨U, hU, β, hβ⟩

end MathGauge.GP003.Transfers
