/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Finite
import Motivic.Transfers.Presheaf.Basic

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers
open AlgebraicGeometry.Scheme
universe u v
namespace MathGauge.GP003.Transfers
variable {k : Type u} [Field k]

/-- Additivity on the actual correspondence category, without a sheaf
assumption, gives unique section assembly on literal disjoint unions. -/
theorem sections_binary_coproduct_bijective
    (P : PresheafWithTransfers.{v} k) (X Y : SmoothSite (Spec (.of k))) :
    Function.Bijective (fun s : P.sections (Cor.mk (SmoothSite.coproduct X Y)) =>
      (P.transfer ((Cor.graphFunctor k).map (SmoothSite.coproductInl X Y)) s,
       P.transfer ((Cor.graphFunctor k).map (SmoothSite.coproductInr X Y)) s)) := by
  obtain ⟨p, q, hpp, hpq, hqp, hqq, ht⟩ :=
    Cor.exists_coproduct_projections k (Cor.mk X) (Cor.mk Y)
  let i := Cor.coproductInl k (Cor.mk X) (Cor.mk Y)
  let j := Cor.coproductInr k (Cor.mk X) (Cor.mk Y)
  change i ≫ p = _ at hpp
  change i ≫ q = _ at hpq
  change j ≫ p = _ at hqp
  change j ≫ q = _ at hqq
  change p ≫ i + q ≫ j = _ at ht
  have hcompose (s : P.sections (Cor.mk (SmoothSite.coproduct X Y))) :
      P.transfer p (P.transfer i s) + P.transfer q (P.transfer j s) = s := by
    have h := ConcreteCategory.congr_hom (congrArg P.transfer ht) s
    simp only [transfer_add, transfer_comp, transfer_id] at h
    exact h
  constructor
  · intro s t h
    have hi := congrArg Prod.fst h
    have hj := congrArg Prod.snd h
    change P.transfer i s = P.transfer i t at hi
    change P.transfer j s = P.transfer j t at hj
    rw [← hcompose s, hi, hj, hcompose t]
  · rintro ⟨s, t⟩
    refine ⟨P.transfer p s + P.transfer q t, ?_⟩
    apply Prod.ext
    · change P.transfer i (P.transfer p s + P.transfer q t) = s
      rw [_root_.map_add]
      have hi := ConcreteCategory.congr_hom (congrArg P.transfer hpp) s
      have hj := ConcreteCategory.congr_hom (congrArg P.transfer hpq) t
      simp only [transfer_id, ConcreteCategory.id_apply] at hi
      simp only [transfer_zero] at hj
      rw [transfer_comp, ConcreteCategory.comp_apply] at hi hj
      rw [hi, hj]
      change s + 0 = s
      exact add_zero s
    · change P.transfer j (P.transfer p s + P.transfer q t) = t
      rw [_root_.map_add]
      have hi := ConcreteCategory.congr_hom (congrArg P.transfer hqp) s
      have hj := ConcreteCategory.congr_hom (congrArg P.transfer hqq) t
      simp only [transfer_zero] at hi
      simp only [transfer_id, ConcreteCategory.id_apply] at hj
      rw [transfer_comp, ConcreteCategory.comp_apply] at hi hj
      rw [hi, hj]
      change 0 + t = t
      exact zero_add t


/-- Additive presheaves have exactly one section on the actual empty scheme. -/
theorem sections_subsingleton_of_isEmpty
    (P : PresheafWithTransfers.{v} k) (X : SmoothSite (Spec (.of k)))
    [IsEmpty X.left] : Subsingleton (P.sections (Cor.mk X)) := by
  have h : (𝟙 (Cor.mk X)) = 0 := Cor.hom_eq_zero_of_isEmpty_source k _
  have hf := congrArg P.transfer h
  simp only [transfer_id, transfer_zero] at hf
  refine ⟨fun a b => ?_⟩
  have ha := ConcreteCategory.congr_hom hf a
  have hb := ConcreteCategory.congr_hom hf b
  change a = 0 at ha
  change b = 0 at hb
  exact ha.trans hb.symm

/-- Finite disjoint unions are genuine products of sections for every additive
presheaf with transfers, including the empty union. -/
theorem sections_finite_coproduct_bijective
    (P : PresheafWithTransfers.{v} k) {n : ℕ}
    (Y : Fin n → SmoothSite (Spec (.of k))) :
    Function.Bijective (fun s : P.sections (Cor.mk (SmoothSite.finiteCoproduct Y)) =>
      fun i => P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.finiteCoproductι Y i)) s) := by
  induction n with
  | zero =>
    have : IsEmpty (SmoothSite.finiteCoproduct Y).left :=
      inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
    have := sections_subsingleton_of_isEmpty P (SmoothSite.finiteCoproduct Y)
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro t
      refine ⟨0, ?_⟩
      funext i
      exact Fin.elim0 i
  | succ n ih =>
    let tail := fun i : Fin n => Y i.succ
    let Z := SmoothSite.finiteCoproduct tail
    have hb := sections_binary_coproduct_bijective P (Y 0) Z
    have ht := ih tail
    have hsucc (s : P.sections (Cor.mk (SmoothSite.finiteCoproduct Y))) (i : Fin n) :
        P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i.succ)) s =
        P.transfer ((Cor.graphFunctor k).map (SmoothSite.finiteCoproductι tail i))
          (P.transfer ((Cor.graphFunctor k).map (SmoothSite.coproductInr (Y 0) Z)) s) := by
      change P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.finiteCoproductι tail i ≫ SmoothSite.coproductInr (Y 0) Z)) s = _
      rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
    constructor
    · intro a b h
      apply hb.1
      apply Prod.ext
      · exact congrFun h 0
      · apply ht.1
        funext i
        exact (hsucc a i).symm.trans ((congrFun h i.succ).trans (hsucc b i))
    · intro t
      obtain ⟨b, hb'⟩ := ht.2 (fun i => t i.succ)
      obtain ⟨a, ha⟩ := hb.2 (t 0, b)
      refine ⟨a, ?_⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrArg Prod.fst ha
      · exact (hsucc a j).trans ((congrArg
          (fun z => P.transfer ((Cor.graphFunctor k).map
            (SmoothSite.finiteCoproductι tail j)) z)
          (congrArg Prod.snd ha)).trans (congrFun hb' j))

end MathGauge.GP003.Transfers
