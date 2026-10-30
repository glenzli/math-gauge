/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import Motivic.Cohomology.A1.Sheafification.DenseDetection
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The kernel of the genuine Nisnevich unit is exactly Zariski-local zero for an
original homotopy invariant presheaf with transfers. This identifies the native
transfer image with the Zariski separated quotient; it does not assert the
semilocal comparison or simultaneous finite-point vanishing.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- Actual original sections vanish on ordinary open neighborhoods of every
point. This is not vanishing on a single neighborhood of a finite point set. -/
def ZariskiLocallyZero (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) : Prop :=
  ∀ x : X.left, ∃ O : X.left.Opens, x ∈ O ∧
    P.transfer ((Cor.graphFunctor k).map (openInclusion X O)) s = 0

/-- Generic splitting of a Nisnevich cover and original all-field local-zero
geometry produce actual Zariski zero neighborhoods for a unit-kernel section. -/
theorem zariskiLocallyZero_of_nisnevich_unit_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X))
    (hs : (toNisnevichSheafify k P).hom.app (op (Cor.mk X)) s = 0) :
    ZariskiLocallyZero P X s := by
  classical
  intro x
  let C := integralAffineCover k X
  obtain ⟨i, t, ht⟩ := C.exists_eq x
  let T : SmoothSite (Spec (.of k)) := SmoothSite.mk (C.f i ≫ X.hom)
  let f : T ⟶ X := SmoothSite.homMk (C.f i) rfl
  have : IsAffine T.left := inferInstanceAs (IsAffine (C.X i))
  have : IsIntegral T.left := inferInstanceAs (IsIntegral (C.X i))
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (C.f i))
  let Q := (toPresheaf k).obj P
  let η := (toPresheaf k).map (toNisnevichSheafify k P)
  let v := P.transfer ((Cor.graphFunctor k).map f) s
  have hv : η.app (op T) v = η.app (op T) 0 := by
    change (toNisnevichSheafify k P).hom.app (op (Cor.mk T)) v =
      (toNisnevichSheafify k P).hom.app (op (Cor.mk T)) 0
    rw [map_zero]
    have hn := ConcreteCategory.congr_hom
      (transfer_naturality (toNisnevichSheafify k P) ((Cor.graphFunctor k).map f)) s
    simp only [ConcreteCategory.comp_apply] at hn
    apply hn.trans
    change ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map f)
      ((toNisnevichSheafify k P).hom.app (op (Cor.mk X)) s) = 0
    rw [hs, map_zero]
  have hR := Presheaf.equalizerSieve_mem (nisnevichTopology (Spec (.of k))) η v 0 hv
  obtain ⟨W, hW, hz⟩ := exists_generic_open_mem_covering_sieve T _ hR
  have hz' : P.transfer ((Cor.graphFunctor k).map (openInclusion T W)) v = 0 := by
    exact hz.trans (map_zero _)
  have : Nonempty ((opensFunctor T).obj W).left := ⟨⟨genericPoint T.left, hW⟩⟩
  have : IsOpenImmersion (openInclusion T W).left :=
    inferInstanceAs (IsOpenImmersion W.ι)
  obtain ⟨O, hO, htO, hzero⟩ := integralAffineLocalZero_of_field k
    (openInclusion T W) P hP v hz' t
  let : IsAffine O.toScheme := hO
  let A := (opensFunctor T).obj O
  let g : A ⟶ X := openInclusion T O ≫ f
  have : IsAffine A.left := hO
  have : IsOpenImmersion g.left :=
    inferInstanceAs (IsOpenImmersion (O.ι ≫ C.f i))
  have hg : P.transfer ((Cor.graphFunctor k).map g) s = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hzero
  exact ⟨g.left.opensRange, ⟨⟨t, htO⟩, ht⟩,
    P.zero_on_open_image_general g s hg⟩

/-- Zariski local zero is killed by the actual unit because its target is a
sheaf for a topology containing ordinary open covers. No HI is needed here. -/
theorem nisnevich_unit_eq_zero_of_zariskiLocallyZero
    (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X))
    (hs : ZariskiLocallyZero P X s) :
    (toNisnevichSheafify k P).hom.app (op (Cor.mk X)) s = 0 := by
  classical
  choose O hx hzero using hs
  let A (x : X.left) := (opensFunctor X).obj (O x)
  let f (x : X.left) : A x ⟶ X := openInclusion X (O x)
  let G := (SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)
  let η := (toPresheaf k).map (toNisnevichSheafify k P)
  have hpre : Presieve.ofArrows A f ∈ nisnevichPrecoverage (Spec (.of k)) X := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun x => inferInstanceAs (Etale (O x).ι),
      fun x => ⟨x, ⟨x, hx x⟩, rfl,
        inferInstanceAs (IsIso ((O x).ι.residueFieldMap ⟨x, hx x⟩))⟩⟩
  have hcover : Presheaf.equalizerSieve (F := G.obj) (η.app (op X) s) 0 ∈
      nisnevichTopology (Spec (.of k)) X := by
    apply mem_nisnevichTopology_iff.mpr
    refine ⟨Presieve.ofArrows A f, hpre, ?_⟩
    rw [Presieve.ofArrows_le_iff]
    intro x
    change ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map (f x))
      ((toNisnevichSheafify k P).hom.app (op (Cor.mk X)) s) =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map (f x)) 0
    rw [map_zero]
    have hn := ConcreteCategory.congr_hom
      (transfer_naturality (toNisnevichSheafify k P) ((Cor.graphFunctor k).map (f x))) s
    simp only [ConcreteCategory.comp_apply] at hn
    apply hn.symm.trans
    change (toNisnevichSheafify k P).hom.app (op (Cor.mk (A x)))
      (P.transfer ((Cor.graphFunctor k).map (f x)) s) = 0
    rw [hzero x, map_zero]
  exact G.property.isSeparated X _ hcover _ _ (fun _ _ hf => hf)

/-- Equality of the two genuine kernels, for every field and smooth object. -/
theorem nisnevich_unit_eq_zero_iff_zariskiLocallyZero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) :
    (toNisnevichSheafify k P).hom.app (op (Cor.mk X)) s = 0 ↔
      ZariskiLocallyZero P X s :=
  ⟨zariskiLocallyZero_of_nisnevich_unit_eq_zero P hP X s,
    nisnevich_unit_eq_zero_of_zariskiLocallyZero P X s⟩

/-- Every actual signed finite correspondence preserves the Zariski-zero
subgroup. Naturality is invoked only after the actual kernel identification. -/
theorem transfer_zariskiLocallyZero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X Y : SmoothSite (Spec (.of k))} (α : Cor.mk X ⟶ Cor.mk Y)
    (s : P.sections (Cor.mk Y)) (hs : ZariskiLocallyZero P Y s) :
    ZariskiLocallyZero P X (P.transfer α s) := by
  apply zariskiLocallyZero_of_nisnevich_unit_eq_zero P hP
  have hzero := nisnevich_unit_eq_zero_of_zariskiLocallyZero P Y s hs
  have hn := ConcreteCategory.congr_hom
    (transfer_naturality (toNisnevichSheafify k P) α) s
  simp only [ConcreteCategory.comp_apply] at hn
  change (toNisnevichSheafify k P).hom.app (op (Cor.mk X)) (P.transfer α s) = 0
  exact hn.trans (by rw [hzero, map_zero])

/-- The native additive transfer image, now identified by its Zariski kernel. -/
abbrev zariskiSeparatedTransfers (P : PresheafWithTransfers.{u + 1} k) :=
  nisnevichImage P

theorem separated_image_unit_eq_zero_iff_zariskiLocallyZero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) :
    (toNisnevichImage P).hom.app (op (Cor.mk X)) s = 0 ↔
      ZariskiLocallyZero P X s := by
  rw [← nisnevich_unit_eq_zero_iff_zariskiLocallyZero P hP]
  have hi := (AddCommGrpCat.mono_iff_injective
    ((nisnevichImageι P).hom.app (op (Cor.mk X)))).mp inferInstance
  have hf := ConcreteCategory.congr_hom
    (congrArg (fun η => η.hom.app (op (Cor.mk X))) (toNisnevichImage_ι P)) s
  constructor
  · intro h
    rw [← hf]
    change (nisnevichImageι P).hom.app (op (Cor.mk X))
      ((toNisnevichImage P).hom.app (op (Cor.mk X)) s) = 0
    rw [h, map_zero]
  · intro h
    apply hi
    rw [map_zero]
    exact hf.trans h

/-- The transferred separated quotient retains the original A1 invariance. -/
theorem zariskiSeparatedTransfers_isA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    (zariskiSeparatedTransfers P).IsA1Invariant :=
  nisnevichImage_isA1Invariant P hP

/-- The actual subgroup removed by the quotient. The preceding theorem
identifies membership with ordinary Zariski-local zero under exactly HI. -/
def zariskiZeroSubgroup (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) : AddSubgroup (P.sections (Cor.mk X)) :=
  ((toNisnevichImage P).hom.app (op (Cor.mk X))).hom.ker

theorem mem_zariskiZeroSubgroup_iff
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) :
    s ∈ zariskiZeroSubgroup P X ↔ ZariskiLocallyZero P X s :=
  separated_image_unit_eq_zero_iff_zariskiLocallyZero P hP X s

/-- The first isomorphism theorem identifies the literal quotient group with
the actual additive presheaf image, using its proved pointwise epimorphism. -/
def zariskiQuotientEquiv (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) :
    P.sections (Cor.mk X) ⧸ zariskiZeroSubgroup P X ≃+
      (zariskiSeparatedTransfers P).sections (Cor.mk X) :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    ((toNisnevichImage P).hom.app (op (Cor.mk X))).hom
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)

/-- This is the original quotient map, not a chosen unrelated isomorphism. -/
theorem zariskiQuotientEquiv_mk (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) :
    zariskiQuotientEquiv P X (QuotientAddGroup.mk s) =
      (toNisnevichImage P).hom.app (op (Cor.mk X)) s := by
  rfl

end MathGauge.GP003.Transfers
