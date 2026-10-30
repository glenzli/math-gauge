/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import MathGauge.GP003.S5DisjointAssembly
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.IntegralComponents

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

/-- The finite smooth disjoint union is also the literal finite coproduct of
its underlying schemes. -/
def finiteSchemeDesc {Z : Scheme.{u}} : {n : ℕ} →
    {Y : Fin n → SmoothSite (Spec (.of k))} →
    (∀ i, (Y i).left ⟶ Z) → ((SmoothSite.finiteCoproduct Y).left ⟶ Z)
  | 0, _, _ => Scheme.emptyTo Z
  | n + 1, _, f => coprod.desc (f 0) (finiteSchemeDesc (fun i : Fin n => f i.succ))

@[reassoc]
theorem finiteSchemeDesc_fac {Z : Scheme.{u}} {n : ℕ}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, (Y i).left ⟶ Z) (i : Fin n) :
    (SmoothSite.finiteCoproductι Y i).left ≫ finiteSchemeDesc f = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact coprod.inl_desc _ _
    · change ((SmoothSite.finiteCoproductι (fun t : Fin n => Y t.succ) j).left ≫
        coprod.inr) ≫ coprod.desc _ _ = _
      rw [Category.assoc, coprod.inr_desc]
      exact ih _ j

theorem finiteScheme_hom_ext {Z : Scheme.{u}} {n : ℕ}
    {Y : Fin n → SmoothSite (Spec (.of k))}
    {f g : (SmoothSite.finiteCoproduct Y).left ⟶ Z}
    (h : ∀ i, (SmoothSite.finiteCoproductι Y i).left ≫ f =
      (SmoothSite.finiteCoproductι Y i).left ≫ g) : f = g := by
  induction n with
  | zero => exact Scheme.empty_ext _ _
  | succ n ih =>
    apply coprod.hom_ext
    · exact h 0
    · apply ih
      intro i
      have hi := h i.succ
      change ((SmoothSite.finiteCoproductι (fun j : Fin n => Y j.succ) i).left ≫
        coprod.inr) ≫ f = ((SmoothSite.finiteCoproductι (fun j : Fin n => Y j.succ) i).left ≫
        coprod.inr) ≫ g at hi
      convert hi using 1 <;> simp only [Category.assoc] <;> rfl

def finiteSchemeIsColimit {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    IsColimit (Cofan.mk (SmoothSite.finiteCoproduct Y).left
      (fun i => (SmoothSite.finiteCoproductι Y i).left)) :=
  Cofan.IsColimit.mk _ (fun s => finiteSchemeDesc (fun i => s.inj i))
    (fun _s i => finiteSchemeDesc_fac _ i)
    (fun s _m hm => finiteScheme_hom_ext (fun i => (hm i).trans
      (finiteSchemeDesc_fac (fun j => s.inj j) i).symm))

/-- Descent of pairwise disjoint actual open immersions is an actual open
immersion. Thus componentwise shrinking returns an open in the original X,
rather than an abstract new model. -/
theorem finiteCoproductDesc_isOpenImmersion
    {n : ℕ} {X : SmoothSite (Spec (.of k))}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (f i).left]
    (hd : Pairwise (fun i j => Disjoint (Set.range (f i).left) (Set.range (f j).left))) :
    IsOpenImmersion (SmoothSite.finiteCoproductDesc f).left := by
  let e : (SmoothSite.finiteCoproduct Y).left ≅ ∐ (fun i => (Y i).left) :=
    (finiteSchemeIsColimit Y).coconePointUniqueUpToIso (colimit.isColimit _)
  have he (i : Fin n) : (SmoothSite.finiteCoproductι Y i).left ≫ e.hom =
      Sigma.ι (fun j => (Y j).left) i :=
    (finiteSchemeIsColimit Y).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨i⟩
  have hfac : e.hom ≫ Sigma.desc (fun i => (f i).left) =
      (SmoothSite.finiteCoproductDesc f).left := by
    apply finiteScheme_hom_ext
    intro i
    rw [← Category.assoc, he, Sigma.ι_comp_desc]
    exact (congrArg (fun h => h.left) (SmoothSite.finiteCoproductι_desc f i)).symm
  have : IsOpenImmersion (Sigma.desc (fun i => (f i).left)) :=
    isOpenImmersion_sigmaDesc _ _ hd
  rw [← hfac]
  infer_instance

/-- Every affine component of a smooth affine model is integral and affine;
the affineness follows from its actual clopen inclusion, not an assumption. -/
theorem integralComponent_isAffine
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsAffine (SmoothSite.integralComponent k X Z hZ).left := by
  let i := SmoothSite.integralComponentι k X Z hZ
  have : IsClosedImmersion i.left := by
    apply IsClosedImmersion.of_isPreimmersion
    change IsClosed (Set.range (SmoothSite.componentOpen k X Z hZ).ι)
    rw [Scheme.Opens.range_ι]
    exact (SmoothSite.isClopen_irreducibleComponent k X hZ).isClosed
  exact isAffine_of_isAffineHom i.left


/-- The same finite disjoint union is affine when every original summand is. -/
theorem finiteCoproduct_isAffine {n : ℕ}
    (Y : Fin n → SmoothSite (Spec (.of k))) [∀ i, IsAffine (Y i).left] :
    IsAffine (SmoothSite.finiteCoproduct Y).left := by
  induction n with
  | zero => change IsAffine (∅ : Scheme.{u}); infer_instance
  | succ n ih =>
    have := ih (fun i : Fin n => Y i.succ)
    change IsAffine ((Y 0).left ⨿ (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)).left)
    infer_instance

end MathGauge.GP003.Transfers
