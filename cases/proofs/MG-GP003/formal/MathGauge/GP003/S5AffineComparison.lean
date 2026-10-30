/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5IntegralComparison
import MathGauge.GP003.S5DisjointGeometry

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

/-- Local constructions on the integral clopen components of an affine smooth
model give a finite pairwise-disjoint family covering the entire prescribed
point set. Extra points used on components without marks are internal choices. -/
theorem finite_component_shrink
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] (s : Finset X.left)
    (Q : ∀ Y : SmoothSite (Spec (.of k)), (Y ⟶ X) → Prop)
    (hlocal : ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left]
      (i : Y ⟶ X) [IsOpenImmersion i.left] (t : Finset Y.left), t.Nonempty →
      ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ Y), IsAffine S.left ∧
        IsOpenImmersion r.left ∧ (↑t : Set Y.left) ⊆ Set.range r.left ∧ Q S (r ≫ i)) :
    ∃ (n : ℕ) (Y : Fin n → SmoothSite (Spec (.of k))) (f : ∀ i, Y i ⟶ X),
      (∀ i, IsAffine (Y i).left) ∧ (∀ i, IsOpenImmersion (f i).left) ∧
      Pairwise (fun i j => Disjoint (Set.range (f i).left) (Set.range (f j).left)) ∧
      (∀ x ∈ s, ∃ i, x ∈ Set.range (f i).left) ∧ (∀ i, Q (Y i) (f i)) := by
  classical
  let I := {Z : Set X.left // Z ∈ irreducibleComponents X.left}
  let : Fintype I := (SmoothSite.finite_irreducibleComponents k X).fintype
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let C (i : Fin n) := SmoothSite.integralComponent k X (e i).val (e i).property
  let c (i : Fin n) : C i ⟶ X := SmoothSite.integralComponentι k X (e i).val (e i).property
  have hCa (i : Fin n) : IsAffine (C i).left := integralComponent_isAffine X _ _
  have hCi (i : Fin n) : IsIntegral (C i).left := inferInstance
  have hCo (i : Fin n) : IsOpenImmersion (c i).left := inferInstance
  have hfinit (i : Fin n) : ((c i).left ⁻¹' (↑s : Set X.left)).Finite :=
    s.finite_toSet.preimage (c i).left.isOpenEmbedding.injective.injOn
  let t (i : Fin n) : Finset (C i).left :=
    insert (Classical.arbitrary (C i).left) (hfinit i).toFinset
  have ht (i : Fin n) : (t i).Nonempty := Finset.insert_nonempty _ _
  have hex i := hlocal (C i) (c i) (t i) (ht i)
  choose Y r hYa hro htr hQ using hex
  let f (i : Fin n) : Y i ⟶ X := r i ≫ c i
  have hfo (i : Fin n) : IsOpenImmersion (f i).left := by
    have := hro i
    change IsOpenImmersion ((r i).left ≫ (c i).left)
    infer_instance
  have hrange (i : Fin n) : Set.range (f i).left ⊆ (e i).val := by
    rintro _ ⟨y, rfl⟩
    exact ((r i).left y).property
  refine ⟨n, Y, f, hYa, hfo, ?_, ?_, hQ⟩
  · intro i j hij
    have hne : (e i).val ≠ (e j).val := by
      intro h
      exact hij (e.injective (Subtype.ext h))
    exact (SmoothSite.pairwiseDisjoint_irreducibleComponents k X
      (e i).property (e j).property hne).mono (hrange i) (hrange j)
  · intro x hx
    let Z : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let i := e.symm Z
    have hxC : x ∈ (e i).val := by
      change x ∈ (e (e.symm Z)).val
      rw [e.apply_symm_apply]
      exact mem_irreducibleComponent
    let y : (C i).left := ⟨x, hxC⟩
    have hyt : y ∈ t i := Finset.mem_insert_of_mem
      ((hfinit i).mem_toFinset.mpr hx)
    obtain ⟨z, hz⟩ := htr i hyt
    refine ⟨i, z, ?_⟩
    change (c i).left ((r i).left z) = x
    rw [hz]
    rfl


/-- Simultaneous kernel vanishing on every smooth affine model, including
all its integral clopen components. Additivity alone reassembles F-sections. -/
theorem affine_kernel_zero
    (hgeometry : IntegralAffineMoving k)
    (P : PresheafWithTransfers.{u+1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (s : Finset X.left) (_hs : s.Nonempty) (a : P.sections (Cor.mk X))
    (ha : (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).app (op X) a = 0) :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑s : Set X.left) ⊆ Set.range r.left ∧
        P.transfer ((Cor.graphFunctor k).map r) a = 0 := by
  let F := (toPresheaf k).obj P
  let η := CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k))) F
  let Q (Y : SmoothSite (Spec (.of k))) (i : Y ⟶ X) :=
    P.transfer ((Cor.graphFunctor k).map i) a = 0
  have hlocal (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left]
      (i : Y ⟶ X) [IsOpenImmersion i.left] (t : Finset Y.left) (ht : t.Nonempty) :
      ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ Y), IsAffine S.left ∧
        IsOpenImmersion r.left ∧ (↑t : Set Y.left) ⊆ Set.range r.left ∧ Q S (r ≫ i) := by
    have hzero : η.app (op Y) (P.transfer ((Cor.graphFunctor k).map i) a) = 0 := by
      have hn := NatTrans.naturality_apply η i.op a
      exact hn.trans (by rw [ha, map_zero])
    obtain ⟨S, r, hS, hr, htr, hz⟩ := integral_affine_kernel_zero hgeometry P hP Y t ht
      (P.transfer ((Cor.graphFunctor k).map i) a) hzero
    refine ⟨S, r, hS, hr, htr, ?_⟩
    change P.transfer ((Cor.graphFunctor k).map (r ≫ i)) a = 0
    rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
    exact hz
  obtain ⟨n, Y, f, hYa, hfo, hd, hcov, hz⟩ := finite_component_shrink X s Q hlocal
  have := hYa
  have := hfo
  let T := SmoothSite.finiteCoproduct Y
  let r := SmoothSite.finiteCoproductDesc f
  refine ⟨T, r, finiteCoproduct_isAffine Y,
    finiteCoproductDesc_isOpenImmersion f hd, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, y, hy⟩ := hcov x hx
    refine ⟨(SmoothSite.finiteCoproductι Y i).left y, ?_⟩
    exact (congrArg (fun m => m.left y) (SmoothSite.finiteCoproductι_desc f i)).trans hy
  · apply (sections_finite_coproduct_bijective P Y).1
    funext i
    have he := ConcreteCategory.congr_hom
      (congrArg (fun g => P.transfer ((Cor.graphFunctor k).map g))
        (SmoothSite.finiteCoproductι_desc f i)) a
    rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] at he
    exact he.trans ((hz i).trans (map_zero _).symm)

/-- Simultaneous lifting on every smooth affine model. Section assembly uses
the genuine finite-correspondence biproduct, and equality is checked in the
actual Zariski sheaf along its ordinary component open cover. -/
theorem affine_section_lift
    (hgeometry : IntegralAffineMoving k)
    (P : PresheafWithTransfers.{u+1} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (s : Finset X.left) (_hs : s.Nonempty)
    (b : (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
      ((toPresheaf k).obj P)).obj (op X)) :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧ (↑s : Set X.left) ⊆ Set.range r.left ∧
        ∃ a : P.sections (Cor.mk S),
          (CategoryTheory.toSheafify (SmoothZariski.topology (Spec (.of k)))
            ((toPresheaf k).obj P)).app (op S) a =
          (CategoryTheory.sheafify (SmoothZariski.topology (Spec (.of k)))
            ((toPresheaf k).obj P)).map r.op b := by
  classical
  let J := SmoothZariski.topology (Spec (.of k))
  let F := (toPresheaf k).obj P
  let B := CategoryTheory.sheafify J F
  let η := CategoryTheory.toSheafify J F
  let Q (Y : SmoothSite (Spec (.of k))) (i : Y ⟶ X) :=
    ∃ a : P.sections (Cor.mk Y), η.app (op Y) a = B.map i.op b
  have hlocal (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left]
      (i : Y ⟶ X) [IsOpenImmersion i.left] (t : Finset Y.left) (ht : t.Nonempty) :
      ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ Y), IsAffine S.left ∧
        IsOpenImmersion r.left ∧ (↑t : Set Y.left) ⊆ Set.range r.left ∧ Q S (r ≫ i) := by
    obtain ⟨S, r, hS, hr, htr, a, ha⟩ := integral_affine_section_lift
      hgeometry P hP Y t ht (B.map i.op b)
    refine ⟨S, r, hS, hr, htr, a, ?_⟩
    rw [op_comp, B.map_comp, ConcreteCategory.comp_apply]
    exact ha
  obtain ⟨n, Y, f, hYa, hfo, hd, hcov, hQ⟩ := finite_component_shrink X s Q hlocal
  have := hYa
  have := hfo
  choose a ha using hQ
  let T := SmoothSite.finiteCoproduct Y
  let r := SmoothSite.finiteCoproductDesc f
  obtain ⟨c, hc⟩ := (sections_finite_coproduct_bijective P Y).2 a
  refine ⟨T, r, finiteCoproduct_isAffine Y,
    finiteCoproductDesc_isOpenImmersion f hd, ?_, c, ?_⟩
  · intro x hx
    obtain ⟨i, y, hy⟩ := hcov x hx
    refine ⟨(SmoothSite.finiteCoproductι Y i).left y, ?_⟩
    exact (congrArg (fun m => m.left y) (SmoothSite.finiteCoproductι_desc f i)).trans hy
  · have hcover : Presheaf.equalizerSieve (F := B) (η.app (op T) c) (B.map r.op b) ∈ J T := by
      intro x
      obtain ⟨i, y, hy⟩ := SmoothSite.finiteCoproduct_covers Y x
      refine ⟨Y i, SmoothSite.finiteCoproductι Y i, y, ?_, inferInstance, hy⟩
      change B.map (SmoothSite.finiteCoproductι Y i).op (η.app (op T) c) =
        B.map (SmoothSite.finiteCoproductι Y i).op (B.map r.op b)
      have hn := NatTrans.naturality_apply η (SmoothSite.finiteCoproductι Y i).op c
      have hm := congrFun hc i
      change F.map (SmoothSite.finiteCoproductι Y i).op c = a i at hm
      rw [← hn, hm, ha]
      have hh := congrArg (fun g => B.map g.op b) (SmoothSite.finiteCoproductι_desc f i)
      rw [op_comp, B.map_comp, ConcreteCategory.comp_apply] at hh
      exact hh.symm
    exact ((presheafToSheaf J AddCommGrpCat.{u+1}).obj F).property.isSeparated
      T _ hcover _ _ (fun _ _ hf => hf)

end MathGauge.GP003.Transfers
