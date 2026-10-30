/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5ZariskiComparison
import Motivic.Cohomology.A1.Moving.OneSided
import Motivic.Cohomology.A1.Sheafification.HomotopyInvariance

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme
universe u
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- A genuine common Cor/A1 moving endpoint lifts any Zariski-sheaf section
which has an original representative on the good open. The equality is in
actual Zariski sheafification, proved through its canonical injection into
Nisnevich sheafification. F is assumed homotopy invariant but not separated;
no homotopy invariance or transfer structure on its Zariski sheafification is
assumed. The required Nisnevich invariance is proved. -/
theorem zariski_section_lift_of_moving_endpoints
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {S X V : SmoothSite (Spec (.of k))} (r : S ⟶ X) (v : V ⟶ X)
    (hm : OneSidedMovingEndpoints.HasMovingEndpoints r v)
    (b : (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).obj (op X))
    (a : P.sections (Cor.mk V))
    (ha : (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).app (op V) a =
      (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P)).map v.op b) :
    ∃ c : P.sections (Cor.mk S),
      (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P)).app (op S) c =
      (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P)).map r.op b := by
  obtain ⟨β, α, h0, h1⟩ := hm
  let Q := ((nisnevichSheafify k).obj P).obj
  let z := zariskiToNisnevich P
  let η := toNisnevichSheafify k P
  let ηz := CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
    ((toPresheaf k).obj P)
  let B := CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
    ((toPresheaf k).obj P)
  have hunit (Y : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk Y)) :
      z.app (op Y) (ηz.app (op Y) s) = η.hom.app (op (Cor.mk Y)) s := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (zariskiToNisnevich_unit P) (op Y)) s
  have hzv : z.app (op V) (B.map v.op b) =
      Q.transfer ((Cor.graphFunctor k).map v) (z.app (op X) b) := by
    exact ConcreteCategory.congr_hom (z.naturality v.op) b
  have hzr : z.app (op S) (B.map r.op b) =
      Q.transfer ((Cor.graphFunctor k).map r) (z.app (op X) b) := by
    exact ConcreteCategory.congr_hom (z.naturality r.op) b
  have hav : η.hom.app (op (Cor.mk V)) a =
      Q.transfer ((Cor.graphFunctor k).map v) (z.app (op X) b) := by
    rw [← hunit V a, ha, hzv]
  refine ⟨P.transfer β a, ?_⟩
  apply zariskiToNisnevich_injective P hP (op S)
  rw [hunit, hzr]
  have hnat := ConcreteCategory.congr_hom (transfer_naturality η β) a
  change η.hom.app (op (Cor.mk S)) (P.transfer β a) =
    Q.transfer β (η.hom.app (op (Cor.mk V)) a) at hnat
  rw [hnat, hav]
  have hQ : Q.IsA1Invariant := nisnevichSheafify_isA1Invariant P hP
  have hf := ConcreteCategory.congr_hom
    (restriction_factor_of_moving_endpoints Q hQ r v β α h0 h1)
    (z.app (op X) b)
  exact hf.symm

/-- A common genuine transfer restriction factor lifts any Zariski-sheaf section
which has an original representative on the good open. The equality is in
actual Zariski sheafification, proved through its canonical injection into
Nisnevich sheafification. F is assumed homotopy invariant but not separated;
no homotopy invariance or transfer structure on its Zariski sheafification is
assumed. The required Nisnevich invariance is proved. -/
theorem zariski_section_lift_of_transfer_factor
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {S X V : SmoothSite (Spec (.of k))} (r : S ⟶ X) (v : V ⟶ X)
    (β : Cor.mk S ⟶ Cor.mk V)
    (hfactor : ∀ (Q : PresheafWithTransfers.{u + 1} k), Q.IsA1Invariant →
      Q.transfer ((Cor.graphFunctor k).map r) =
        Q.transfer ((Cor.graphFunctor k).map v) ≫ Q.transfer β)
    (b : (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).obj (op X))
    (a : P.sections (Cor.mk V))
    (ha : (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).app (op V) a =
      (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P)).map v.op b) :
    ∃ c : P.sections (Cor.mk S),
      (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P)).app (op S) c =
      (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
        ((toPresheaf k).obj P)).map r.op b := by
  let Q := ((nisnevichSheafify k).obj P).obj
  let z := zariskiToNisnevich P
  let η := toNisnevichSheafify k P
  let ηz := CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
    ((toPresheaf k).obj P)
  let B := CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
    ((toPresheaf k).obj P)
  have hunit (Y : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk Y)) :
      z.app (op Y) (ηz.app (op Y) s) = η.hom.app (op (Cor.mk Y)) s := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (zariskiToNisnevich_unit P) (op Y)) s
  have hzv : z.app (op V) (B.map v.op b) =
      Q.transfer ((Cor.graphFunctor k).map v) (z.app (op X) b) := by
    exact ConcreteCategory.congr_hom (z.naturality v.op) b
  have hzr : z.app (op S) (B.map r.op b) =
      Q.transfer ((Cor.graphFunctor k).map r) (z.app (op X) b) := by
    exact ConcreteCategory.congr_hom (z.naturality r.op) b
  have hav : η.hom.app (op (Cor.mk V)) a =
      Q.transfer ((Cor.graphFunctor k).map v) (z.app (op X) b) := by
    rw [← hunit V a, ha, hzv]
  refine ⟨P.transfer β a, ?_⟩
  apply zariskiToNisnevich_injective P hP (op S)
  rw [hunit, hzr]
  have hnat := ConcreteCategory.congr_hom (transfer_naturality η β) a
  change η.hom.app (op (Cor.mk S)) (P.transfer β a) =
    Q.transfer β (η.hom.app (op (Cor.mk V)) a) at hnat
  rw [hnat, hav]
  have hQ : Q.IsA1Invariant := nisnevichSheafify_isA1Invariant P hP
  have hf := ConcreteCategory.congr_hom
    (hfactor Q hQ)
    (z.app (op X) b)
  exact hf.symm

end MathGauge.GP003.Transfers
