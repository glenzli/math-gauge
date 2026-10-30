/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5TransferSectionLift

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

/-- On every nonempty smooth model, each Zariski-sheaf section has an original
representative on a nonempty affine open. When the model is integral that
open is automatically dense. No representative on a prescribed point set
is asserted here; the simultaneous moving theorem supplies that later. -/
theorem exists_affine_zariski_representative
    (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) [Nonempty X.left]
    (b : (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).obj (op X)) :
    ∃ (V : SmoothSite (Spec (.of k))) (_ : IsAffine V.left)
      (_ : Nonempty V.left) (v : V ⟶ X),
      IsOpenImmersion v.left ∧ ∃ a : P.sections (Cor.mk V),
        (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
          ((toPresheaf k).obj P)).app (op V) a =
        (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
          ((toPresheaf k).obj P)).map v.op b := by
  let J := SmoothZariski.topology (Spec (.of k))
  let F := (toPresheaf k).obj P
  let B := CategoryTheory.sheafify J F
  let η := CategoryTheory.toSheafify J F
  have hcover := Presheaf.imageSieve_mem J η b
  obtain ⟨x⟩ := ‹Nonempty X.left›
  obtain ⟨Y, f, y, ⟨a, ha⟩, hf, hfy⟩ := hcover x
  have := hf
  obtain ⟨i, t, ht⟩ := Y.left.affineCover.exists_eq y
  let V : SmoothSite (Spec (.of k)) :=
    SmoothSite.mk (Y.left.affineCover.f i ≫ Y.hom)
  let c : V ⟶ Y := SmoothSite.homMk (Y.left.affineCover.f i) rfl
  have hV : IsAffine V.left := inferInstanceAs (IsAffine (Y.left.affineCover.X i))
  have hne : Nonempty V.left := ⟨t⟩
  have hcf : IsOpenImmersion (c ≫ f).left :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineCover.f i ≫ f.left))
  refine ⟨V, hV, hne, c ≫ f, hcf, F.map c.op a, ?_⟩
  change η.app (op V) (F.map c.op a) = B.map (c ≫ f).op b
  rw [NatTrans.naturality_apply, ha, op_comp, B.map_comp,
    ConcreteCategory.comp_apply]

end MathGauge.GP003.Transfers
