/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5ZariskiKernel
import MathGauge.GP003.S5SiteBridge

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme

universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- The original Nisnevich unit is locally injective for actual Zariski opens,
by the proved original-section kernel theorem, over every field. -/
theorem nisnevich_unit_zariski_locallyInjective
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Presheaf.IsLocallyInjective (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).map (toNisnevichSheafify k P)) := by
  apply SmoothZariski.locallyInjective_of_open_kernel
  intro X s hs
  exact zariskiLocallyZero_of_nisnevich_unit_eq_zero P hP X s hs

/-- The native quotient map is a Zariski local equivalence, not merely a
Nisnevich local equivalence. Its surjectivity is the actual image quotient. -/
theorem separated_quotient_zariski_locallyBijective
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Presheaf.IsLocallyInjective (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).map (toNisnevichImage P)) ∧
      Presheaf.IsLocallySurjective (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).map (toNisnevichImage P)) := by
  let J := SmoothZariski.topology (Spec (.of k))
  have := nisnevich_unit_zariski_locallyInjective P hP
  constructor
  · apply Presheaf.isLocallyInjective_of_isLocallyInjective_fac J
      (φ := (toPresheaf k).map (toNisnevichImage P))
      (ψ := (toPresheaf k).map (nisnevichImageι P))
      (φψ := (toPresheaf k).map (toNisnevichSheafify k P))
    rw [← Functor.map_comp, toNisnevichImage_ι]
  · apply Presheaf.isLocallySurjective_of_surjective J
    intro X
    exact (AddCommGrpCat.epi_iff_surjective
      ((toNisnevichImage P).hom.app (op (Cor.mk X.unop)))).mp inferInstance

/-- The canonical map on Zariski sheafifications of the literal quotient is
an isomorphism. It is the existing sheafifyMap of the original natural map. -/
theorem separated_quotient_zariski_sheafify_isIso
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    IsIso (CategoryTheory.sheafifyMap (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).map (toNisnevichImage P))) := by
  let J := SmoothZariski.topology (Spec (.of k))
  let q := (toPresheaf k).map (toNisnevichImage P)
  have := (separated_quotient_zariski_locallyBijective P hP).1
  have := (separated_quotient_zariski_locallyBijective P hP).2
  have : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map q) :=
    (J.W_iff q).mp (J.W_of_isLocallyBijective q)
  exact inferInstanceAs
    (IsIso ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map
      ((presheafToSheaf J AddCommGrpCat.{u + 1}).map q)))

/-- The genuine Nisnevich sheaf, viewed only as a Zariski sheaf. -/
def nisnevichZariskiSheaf (P : PresheafWithTransfers.{u + 1} k) :
    Sheaf (SmoothZariski.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  SmoothZariski.nisnevichToZariski
    ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P))

/-- The comparison to Nisnevich sheafification is the canonical extension of
the original unit along ordinary Zariski sheafification. -/
def zariskiToNisnevich (P : PresheafWithTransfers.{u + 1} k) :
    CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P) ⟶ (nisnevichZariskiSheaf P).obj :=
  sheafifyLift (SmoothZariski.topology (Spec (.of k)))
    ((toPresheaf k).map (toNisnevichSheafify k P)) (nisnevichZariskiSheaf P).property

/-- Exact compatibility of the two original units. -/
theorem zariskiToNisnevich_unit (P : PresheafWithTransfers.{u + 1} k) :
    CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P) ≫ zariskiToNisnevich P =
      (toPresheaf k).map (toNisnevichSheafify k P) :=
  toSheafify_sheafifyLift _ _ _

/-- The canonical Zariski-to-Nisnevich comparison is pointwise injective.
No injectivity of the original presheaf unit is assumed or inferred globally. -/
theorem zariskiToNisnevich_injective
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    Function.Injective ((zariskiToNisnevich P).app X) := by
  have := nisnevich_unit_zariski_locallyInjective P hP
  exact SmoothZariski.sheafifyLift_injective ((toPresheaf k).obj P)
    (nisnevichZariskiSheaf P) ((toPresheaf k).map (toNisnevichSheafify k P)) X

end MathGauge.GP003.Transfers
