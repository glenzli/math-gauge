# MG-C003 v0.1.1

本答卷包含完整 Lean 源码、构建文件及 92 项对照表。离线构建入口为 `python3 build.py /path/to/environment.json`，默认从该环境文件所在目录读取附件中的 `formal_oet/`。

```lean filename=Main.lean
import Ch3.Components
import Ch3.Factor
import Ch3.Radius
import Ch3.Scale
import Ch3.Entropy
import Ch3.Models
import Ch3.RealTools
import Ch3.Step
import Ch3.Floor
import Ch3.Readout
import Ch3.Rearrange
import Ch3.Correspondence
import Ch3.Chapter

/-!
第 3 章数学内容出自 Zhe Li（Glen Li / glenzli），《The Operator Evolution Theory》卷 I，v1.0.0。
本项目据冻结原文新编 Lean 证明，沿用附件中的第 1、2 章接口。
作者 ORCID https://orcid.org/0009-0006-6536-3453
作品 https://glenzli.com/books/oet/
版本 https://doi.org/10.5281/zenodo.21457931
源码 https://gitlab.com/glenzli/oet-public
许可 CC BY 4.0 https://creativecommons.org/licenses/by/4.0/
-/
```

```lean filename=Ch3/Chapter.lean
import Ch3.Correspondence
import Ch3.Step
import Ch3.Readout
import Ch3.Floor
import Ch3.Rearrange

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
section
variable {X I : Type} {b : X} {f g : Op b} {U A B : Set X} {d : I → Dist X}

theorem subfamilyConstant (_hU : U.Nonempty) (_hu : U ⊆ dom f) {J : Set I} (_hj : J.Nonempty)
    (hc : J ⊆ constSet d f U) (i : I) :
    (∀ y ∈ U, fiber (subdist d J) f U (f.func y) = U ∧ radius (d i) (subdist d J) f U y = ⊤) ∧
    uniform (d i) (subdist d J) f U U = ⊤ := by
  have h : ∀ j ∈ J, Const (d j) f U := fun _ hj => hc hj
  have hr := constRadii (d i) (constSub d h)
  exact ⟨fun _ hy => ⟨constSubFiber d h hy,hr.1 _ hy⟩,hr.2⟩

theorem subfamilyPartition (m : ∀ i, ExtendedPseudoMetric X b (d i)) (J : Set I) (hJ : J.Nonempty)
    (_hu : U ⊆ dom f) :
    (∀ F ∈ blocks (subdist d J) f U, F.Nonempty) ∧ ⋃₀ (blocks (subdist d J) f U) = U ∧
    (blocks (subdist d J) f U).PairwiseDisjoint id :=
  blockPartition (subfamily_pseudometric_is_extended d J hJ m)

theorem compositeBounds [Fintype I] (i j l : I) (_hn : U.Nonempty) (hu : U ⊆ dom (g*f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g ∧
    ((∀ a ∈ f.func '' U, ∀ c ∈ f.func '' U, d l a c = 0 → d j (g.func a) (g.func c) = 0) →
      matrix d f U l i ≤ matrix d (g*f) U j i) ∧
    (∀ L, positiveFinite L → (∀ x ∈ U, ∀ y ∈ U, d l (f.func x) (f.func y) ≤ L * d i x y) →
      matrix d g (f.func '' U) j l / L ≤ matrix d (g*f) U j i) := by
  refine ⟨?_,?_,fun h => compZeroRadius h,fun _ hL h => compLipRadius hL h⟩
  · intro x hx h
    exact hu hx (show g.func (f.func x) = b by rw [h,g.preserves_bot])
  · rintro _ ⟨x,hx,rfl⟩
    exact hu hx

theorem pullbackEndpoints (i j l : I) {L : ENNReal} (hL : positiveFinite L)
    (h : ∀ x ∈ U, ∀ y ∈ U, d l (f.func x) (f.func y) ≤ L * d i x y) :
    (matrix d g (f.func '' U) j l = 0 → matrix d g (f.func '' U) j l / L = 0) ∧
    (matrix d g (f.func '' U) j l = ⊤ → matrix d (g*f) U j i = ⊤) := by
  refine ⟨fun h₀ => by simp [h₀,div_eq_mul_inv],fun ht => ?_⟩
  have H : matrix d g (f.func '' U) j l / L ≤ matrix d (g*f) U j i := compLipRadius hL h
  rw [ht,ENNReal.top_div_of_ne_top hL.2.ne] at H
  exact top_unique H

theorem restrictScaleRadius (σ : Scale X I) (i j : I) (hB : B.Nonempty) (h : B ⊆ A)
    (_ha : A ⊆ dom f) {s : ENNReal} (_hs : positiveFinite s) :
    let a : Region X := ⟨A,hB.mono h⟩
    let b' : Region X := ⟨B,hB⟩
    σ.value i b' ≤ σ.value i a ∧ (σ.value i a < s → σ.value i b' < s) ∧
    (∀ y ∈ B, radius (d i) (d j) f A y ≤ radius (d i) (d j) f B y) ∧
    matrix d f A j i ≤ matrix d f B j i := by
  obtain ⟨h₁,h₂⟩ := scaleRestrict σ i ⟨A,hB.mono h⟩ ⟨B,hB⟩ h s
  exact ⟨h₁,h₂,fun _ _ => restrictRadius h,restrictUniform h⟩

theorem coverConstraint (i j : I) (_hne : A.Nonempty) (_hu : A ⊆ dom f)
    {t : ENNReal} (_ht : positiveFinite t) (hr : t ≤ matrix d f A j i) :
    (∀ x ∈ A, ball (d i) x t ∩ A ⊆ fiber (d j) f A (f.func x)) ∧
    ∀ B ⊆ A, ∀ e, positiveFinite e →
      cover (d j) e (f.func '' B) ≤ cover (d i) t B ∧
      (B.Nonempty → entropy (d j) e (f.func '' B) ≤ entropy (d i) t B) :=
  ⟨fun _ hx => thresholdBall hr hx,fun _ hB _ he =>
    ⟨thresholdCover hB hr he.1,fun _ => thresholdEntropy hB hr he.1⟩⟩

theorem singletonDelta (i j : I) (hne : U.Nonempty) (hu : U ⊆ dom f) {e : ENNReal} (he : positiveFinite e)
    (hg : good (d i) (d j) f U e) :
    ∃ hs, mapDelta d {i} {j} (singleton_nonempty _) (singleton_nonempty _) f U hne hu e he hs =
      delta (d i) (d j) f U e hg := by
  have h (k : I) : subdist d {k} = d k := subfamily_pseudometric_singleton d k
  exact ⟨by simpa only [h] using hg,by simp only [mapDelta,delta,h]⟩

theorem coEntropyBound [Fintype I] (i j : I) (K : I → I → ENNReal) (hK : IsCoLipMatrix d f U K)
    (hk : positiveFinite (K i j)) {e : ENNReal} (he : positiveFinite e) (hU : boundedAtAll (d i) U) :
    (∃ a : ℝ, entropy (d i) e U = a) ∧ (∃ a : ℝ, entropy (d i) (e/K i j) U = a) ∧
    ∃ hg : good (d i) (d j) f U e,
      delta (d i) (d j) f U e hg ≤ entropy (d i) e U - entropy (d i) (e/K i j) U ∧
      (cover (d j) e (f.func '' U) = ⊤ → delta (d i) (d j) f U e hg = ⊥) := by
  obtain ⟨hg,hb⟩ := coDelta d K i j hK hk he hU
  exact ⟨finiteLog hK.1 (hU e he),finiteLog hK.1 (hU _ (divScale he hk)),hg,hb,(deltaBranches hK.1 hg).2.1⟩

theorem radiusSingle (i j : I) (y : X) :
    radius (d i) (subdist d {j}) f U y = radius (d i) (d j) f U y := by
  rw [show subdist d {j} = d j from subfamily_pseudometric_singleton d j]

theorem subfamilyTarget (m : ∀ i, ExtendedPseudoMetric X b (d i)) (J : Set I) (hJ : J.Nonempty)
    (_hu : U ⊆ dom f) {y z : X} (h : subdist d J y z = 0) :
    fiber (subdist d J) f U y = fiber (subdist d J) f U z :=
  fiberTarget (subfamily_pseudometric_is_extended d J hJ m) h

theorem emptyTransform (f g : Op b) : transforms f g ∅ := pointFactor.2 (fun _ h => h.1.elim)

theorem gapDisjoint [Fintype I] (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hk : 0 < K i j) (hr : 0 < matrix d f U j i) :
    Disjoint ({0} : Set ENNReal) (Ici (matrix d f U j i)) ∧
    ∀ x ∈ U, ∀ y ∈ U, d i x y ∈ ({0} : Set ENNReal) ∪ Ici (matrix d f U j i) := by
  exact ⟨Set.disjoint_left.2 (fun _ hz hl => hr.not_ge (Set.mem_singleton_iff.mp hz ▸ hl)),
    fun _ hx _ hy => uniformGap d K i j hK hk hy hr hx⟩

end

namespace Step
theorem pointwiseCoverFails :
    (∀ y ∈ U, 0 < radius usual usual f U y) ∧
    ¬ ∃ t, positiveFinite t ∧ ∀ B ⊆ U, cover usual (1/2) (f.func '' B) ≤ cover usual t B := by
  constructor
  · rintro _ ⟨y,hy,rfl⟩
    exact (pointValue hy).1.symm ▸ (pointValue hy).2
  · rintro ⟨t,ht,h⟩
    obtain ⟨a,_,_,_,hB,hi,ho⟩ := noUniformCover ht
    have H := h _ hB
    rw [hi,ho] at H
    norm_num at H
end Step

namespace Affine
theorem commonFiber (g : Op (none : Line)) (c : ℝ) (h : ∀ x ∈ U, g.func x = pt c)
    (hc : g.func (pt c) ≠ none) :
    U ⊆ dom (g*g) ∧ fiber absolute (g*g) U (g.func (pt c)) = U := by
  obtain ⟨hv,_,hd,_⟩ := sameValue g c h
  refine ⟨hd.2 hc,?_⟩
  ext x
  exact ⟨fun hx => hx.1,fun hx => ⟨hx,by rw [hv _ hx]; exact (readMetric abs).dist_self _⟩⟩
end Affine

namespace Swap
theorem classifications :
    let D := fun _ : Unit => d
    U ⊆ dom (f*f) ∧ activeSet D f U = univ ∧ identSet D f U = ∅ ∧
    activeSet D (f*f) U = ∅ ∧ identSet D (f*f) U = univ := by
  have hd : U ⊆ dom (f*f) := by
    intro x hx
    rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
  obtain ⟨ha,hi,hj,hn⟩ := components
  exact ⟨hd,Set.eq_univ_of_forall (fun _ => ha),Set.eq_empty_iff_forall_notMem.2 (fun _ => hi),
    Set.eq_empty_iff_forall_notMem.2 (fun _ => hn),Set.eq_univ_of_forall (fun _ => hj)⟩
theorem inputAndOutput :
    channels false a c = ⊤ ∧ channels true a c = 1 ∧ U ⊆ dom (1 : Op (none : Option Bool)) := by
  refine ⟨rfl,rfl,?_⟩
  intro x hx
  rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
end Swap

namespace Floor
theorem fourDomains :
    (D (Icc 0 (1/2))).Nonempty ∧ (D (Icc (9/10) (11/10))).Nonempty ∧
    (D {0,2}).Nonempty ∧ (D (Icc 0 2)).Nonempty :=
  ⟨realNonempty (nonempty_Icc.mpr (by norm_num)),realNonempty (nonempty_Icc.mpr (by norm_num)),
    realNonempty ⟨0,Or.inl rfl⟩,realNonempty (nonempty_Icc.mpr (by norm_num))⟩
end Floor

namespace Rearrange
theorem table :
    (f.func (pt 0),f.func (pt 1),f.func (pt 2),f.func (pt 3)) = (pt 0,pt 1,pt 2,pt 3) ∧
    (g.func (pt 0),g.func (pt 1),g.func (pt 2),g.func (pt 3)) = (pt 0,pt 3,pt 1,pt 2) := by
  norm_num [f,g,U,pt]
theorem scales :
    boundedAtAll usual U ∧ ((7/4)/3 : ENNReal) = 7/12 ∧
    cover usual (7/4) (f.func '' U) = cover usual ((7/4)/1) U ∧
    cover usual (7/4) (g.func '' U) < cover usual ((7/4)/3) U := by
  have hfin : U.Finite := carrier ▸ S.finite_toSet
  obtain ⟨_,_,hf,hf',hg,hg'⟩ := numericalBounds
  refine ⟨fun _ he => finiteCover (readMetric id) hfin he.1,?_,hf.trans hf'.symm,?_⟩
  · apply le_antisymm <;> apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1 <;>
      norm_num [ENNReal.toReal_div]
  · rw [hg,hg']; norm_num
end Rearrange
end
end MG
```

```lean filename=Ch3/Components.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/-! Chapter 3 of Zhe Li (Glen Li / glenzli), *The Operator Evolution Theory*.
New Lean formalization, CC BY 4.0. https://glenzli.com/books/oet/ -/
namespace MG
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {b : X}
abbrev Op (b : X) := Operator X b
abbrev Dist (X : Type) := X → X → ENNReal
variable {p : Dist X} {f g : Op b} {U : Set X} {x y z : X}

def Const (p : Dist X) (f : Op b) (U : Set X) := ∀ x ∈ U, ∀ y ∈ U, p (f.func x) (f.func y) = 0
def Ident (p : Dist X) (f : Op b) (U : Set X) := ¬ Const p f U ∧ ∀ x ∈ U, p (f.func x) x = 0
def Active (p : Dist X) (f : Op b) (U : Set X) := ¬ Const p f U ∧ ¬ Ident p f U

theorem partition : (Const p f U ∨ Ident p f U ∨ Active p f U) ∧
    ¬ (Const p f U ∧ Ident p f U) ∧ ¬ (Const p f U ∧ Active p f U) ∧
    ¬ (Ident p f U ∧ Active p f U) := by unfold Active Ident; tauto

theorem zeroRow [Fintype I] (d : I → Dist X) (i : I) (h : Const (d i) f U)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ ∑ k, 0 * d k x y ∧ (∑ k, 0 * d k x y) = 0 := by
  simp [h x hx y hy]

theorem zeroEntry [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i k : I)
    (hc : Const (d i) f U) (hK : IsCoLipMatrix d f U K)
    (h : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨a, ha, c, hc', hp⟩ := h
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i a c hK ha hc' (hc _ ha _ hc') hp

theorem zeroLeft (m : ExtendedPseudoMetric X b p) (h : p x y = 0) : p x z = p y z := by
  apply le_antisymm
  · simpa [h] using m.triangle x y z
  · simpa [m.symm y x, h] using m.triangle y x z

theorem zeroRight (m : ExtendedPseudoMetric X b p) (h : p y z = 0) : p x y = p x z := by
  rw [m.symm x y, m.symm x z, zeroLeft m h]

theorem identDist (m : ExtendedPseudoMetric X b p) (h : Ident p f U) (hx : x ∈ U) (hy : y ∈ U) :
    p (f.func x) (f.func y) = p x y :=
  (zeroLeft m (h.2 _ hx)).trans (zeroRight m (h.2 _ hy))

theorem outerConst (h : Const p g (f.func '' U)) : Const p (g * f) U :=
  fun x hx y hy => h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩

theorem compIdent (m : ExtendedPseudoMetric X b p) (hf : Ident p f U)
    (hg : Ident p g (f.func '' U)) : Ident p (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    rw [← identDist m hg (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)]
    exact hc _ hx _ hy
  · intro x hx
    change p (g.func (f.func x)) x = 0
    rw [zeroLeft m (hg.2 _ ⟨x,hx,rfl⟩), hf.2 _ hx]

theorem compActive (m : ExtendedPseudoMetric X b p) (h : Active p (g * f) U) :
    Active p f U ∨ Active p g (f.func '' U) := by
  by_contra! hn
  rcases partition (p := p) (f := g) (U := f.func '' U) |>.1 with hc | hi | ha
  · exact h.1 (outerConst hc)
  · rcases partition (p := p) (f := f) (U := U) |>.1 with c | i | a
    · apply h.1
      intro x hx y hy
      exact (identDist m hi (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)).trans (c _ hx _ hy)
    · exact h.2 (compIdent m i hi)
    · exact hn.1 a
  · exact hn.2 ha

def chain : List (Op b) → Op b
  | [] => 1
  | f :: fs => chain fs * f

def stepActive (p : Dist X) : List (Op b) → Set X → Prop
  | [], _ => False
  | f :: fs, U => Active p f U ∨ stepActive p fs (f.func '' U)

theorem chain_order (fs : List (Op b)) : chain fs = OperatorChain fs.reverse := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [chain, ih, operator_chain_eq_prod]

theorem chain_domain (fs : List (Op b)) (h : U ⊆ dom (chain (f :: fs))) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom (chain fs) := by
  constructor
  · intro x hx hb
    apply h hx
    change (chain fs).func (f.func x) = b
    rw [hb, (chain fs).preserves_bot]
  · rintro _ ⟨x,hx,rfl⟩
    exact h hx

theorem emptyActive (m : ExtendedPseudoMetric X b p) : ¬ Active p (1 : Op b) U :=
  fun h => h.2 ⟨h.1, fun x _ => m.dist_self x⟩

theorem chainActive (m : ExtendedPseudoMetric X b p) (fs : List (Op b))
    (hU : U ⊆ dom (chain fs)) (h : Active p (chain fs) U) : stepActive p fs U := by
  induction fs generalizing U with
  | nil => exact (emptyActive m h).elim
  | cons f fs ih =>
    rcases compActive m (g := chain fs) (f := f) h with a | a
    · exact Or.inl a
    · exact Or.inr (ih (chain_domain fs hU).2 a)

theorem diagConst [Fintype I] (d : I → Dist X) (j : I) (L : I → I → ENNReal)
    (hf : Const (d j) f U) (hg : IsLipMatrix d g (f.func '' U) L)
    (row : ∀ k, k ≠ j → L k j = 0) : Const (d j) (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ bot_le
  simpa [hf x hx y hy] using lip_bound_of_single_input_row d g _ L j j hg row
    _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

def fiber (p : Dist X) (f : Op b) (U : Set X) (y : X) : Set X := {x | x ∈ U ∧ p (f.func x) y = 0}
noncomputable abbrev subdist := @subfamily_pseudometric
def blocks (p : Dist X) (f : Op b) (U : Set X) : Set (Set X) := fiber p f U '' (f.func '' U)

theorem subzero (d : I → Dist X) (J : Set I) :
    subdist d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  change (⨆ j : J, d j.val x y) = 0 ↔ _
  simp [Subtype.forall]

theorem fiberTarget (m : ExtendedPseudoMetric X b p) (h : p y z = 0) :
    fiber p f U y = fiber p f U z := by ext a; simp [fiber, zeroRight m h]

theorem fiberCover (m : ExtendedPseudoMetric X b p) :
    (∀ F ∈ blocks p f U, F.Nonempty) ∧ ⋃₀ (blocks p f U) = U := by
  constructor
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,m.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_,⟨y,_,rfl⟩,hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_,⟨x,hx,rfl⟩,rfl⟩, hx, m.dist_self _⟩

theorem fiberPartition (m : ExtendedPseudoMetric X b p) {F G : Set X} (hF : F ∈ blocks p f U) (hG : G ∈ blocks p f U) :
    F = G ∨ Disjoint F G := by
  obtain ⟨y,_,rfl⟩ := hF
  obtain ⟨z,_,rfl⟩ := hG
  by_cases h : Disjoint (fiber p f U y) (fiber p f U z)
  · exact Or.inr h
  · obtain ⟨x,hx,hx'⟩ := Set.not_disjoint_iff.mp h
    exact Or.inl (fiberTarget m ((zeroLeft m hx.2).symm.trans hx'.2))

theorem fiberInter (d : I → Dist X) {J : Set I} (hJ : J.Nonempty) :
    fiber (subdist d J) f U y = ⋂ j ∈ J, fiber (d j) f U y := by
  ext x
  simp only [fiber, mem_setOf_eq, subzero, mem_iInter]
  obtain ⟨j,hj⟩ := hJ
  exact ⟨fun h i hi => ⟨h.1,h.2 i hi⟩, fun h => ⟨(h j hj).1, fun i hi => (h i hi).2⟩⟩

theorem fiberAnti (d : I → Dist X) {J K : Set I} (h : J ⊆ K) :
    fiber (subdist d K) f U y ⊆ fiber (subdist d J) f U y :=
  fun _ hx => ⟨hx.1,(subzero d J).2 fun j hj => (subzero d K).1 hx.2 j (h hj)⟩

theorem fiberEnds (d : I → Dist X) (i : I) :
    fiber (subdist d {i}) f U y = {x ∈ U | d i (f.func x) y = 0} ∧
    fiber (subdist d univ) f U y ⊆ fiber (d i) f U y := by
  rw [show subdist d {i} = d i from subfamily_pseudometric_singleton d i]
  exact ⟨rfl, fun x hx => ⟨hx.1,(subzero d univ).1 hx.2 i trivial⟩⟩

theorem identFiber (m : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    fiber p f U y = {x ∈ U | p x y = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [zeroLeft m (hi.2 x hx)]

theorem constFiber (m : ExtendedPseudoMetric X b p) (hc : Const p f U) (hy : y ∈ f.func '' U) :
    fiber p f U y = U ∧ ∀ z, 0 < p z y → fiber p f U z = ∅ := by
  obtain ⟨a,ha,rfl⟩ := hy
  constructor
  · ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx,hc _ hx _ ha⟩⟩
  · intro z hz
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hz.ne' ((zeroLeft m hx.2).symm.trans (hc _ hx.1 _ ha))

end MG
```

```lean filename=Ch3/Correspondence.lean
import Ch3.Entropy

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X I : Type} {b : X} {d : I → Dist X} {f g : Op b} {U : Set X}
variable {p q : Dist X} {e : ENNReal}

def constSet (d : I → Dist X) (f : Op b) (U : Set X) := {i | Const (d i) f U}
def identSet (d : I → Dist X) (f : Op b) (U : Set X) := {i | Ident (d i) f U}
def activeSet (d : I → Dist X) (f : Op b) (U : Set X) := {i | Active (d i) f U}

theorem componentSets :
    identSet d f U = {i ∈ (constSet d f U)ᶜ | ∀ x ∈ U, d i (f.func x) x = 0} ∧
    activeSet d f U = (constSet d f U ∪ identSet d f U)ᶜ := by
  refine ⟨rfl,?_⟩
  ext i
  exact not_or.symm

theorem compSets (m : ∀ i, ExtendedPseudoMetric X b (d i)) (_hU : U ⊆ dom (g*f)) :
    activeSet d (g*f) U ⊆ activeSet d f U ∪ activeSet d g (f.func '' U) ∧
    identSet d f U ∩ identSet d g (f.func '' U) ⊆ identSet d (g*f) U :=
  ⟨fun i h => compActive (m i) h,fun i h => compIdent (m i) h.1 h.2⟩

def prefixOp (F : ℕ → Op b) : ℕ → Op b
  | 0 => 1
  | n+1 => F n * prefixOp F n

theorem prefixDomains (F : ℕ → Op b) (n : ℕ) :
    (prefixOp F 0).func '' U = U ∧
    (prefixOp F (n+1)).func '' U = (F n).func '' ((prefixOp F n).func '' U) := by
  exact ⟨Set.image_id U,by rw [Set.image_image]; rfl⟩

theorem finiteActive (m : ∀ i, ExtendedPseudoMetric X b (d i)) (F : ℕ → Op b) (n : ℕ)
    (hu : U ⊆ dom (prefixOp F n)) :
    (∀ k < n, (prefixOp F k).func '' U ⊆ dom (F k)) ∧
    activeSet d (prefixOp F n) U ⊆ ⋃ k < n, activeSet d (F k) ((prefixOp F k).func '' U) := by
  induction n with
  | zero =>
    exact ⟨fun k hk => (Nat.not_lt_zero k hk).elim,fun i hi => (emptyActive (m i) hi).elim⟩
  | succ n ih =>
    have hprev : U ⊆ dom (prefixOp F n) := by
      intro x hx hb
      apply hu hx
      change (F n).func ((prefixOp F n).func x) = b
      rw [hb,(F n).preserves_bot]
    obtain ⟨hd,ha⟩ := ih hprev
    constructor
    · intro k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h|rfl
      · exact hd k h
      · rintro _ ⟨x,hx,rfl⟩
        exact hu hx
    · intro i hi
      rcases compActive (m i) (f := prefixOp F n) (g := F n) hi with h|h
      · obtain ⟨k,hk,hi⟩ := Set.mem_iUnion₂.mp (ha h)
        exact Set.mem_iUnion₂.mpr ⟨k,by omega,hi⟩
      · exact Set.mem_iUnion₂.mpr ⟨n,Nat.lt_succ_self n,h⟩

theorem subdistMaximum [Finite I] {J : Set I} (hJ : J.Nonempty) (x y : X) :
    IsGreatest ((fun j => d j x y) '' J) (subdist d J x y) := by
  letI : Nonempty J := hJ.to_subtype
  obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f := fun k : J => d k x y)
  exact ⟨⟨j,j.2,hj⟩,fun _ ⟨i,hi,e⟩ => e ▸ le_iSup (fun k : J => d k x y) ⟨i,hi⟩⟩

theorem fiberEmpty {y : X} (h : ∀ z ∈ f.func '' U, 0 < p z y) : fiber p f U y = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hx => (h _ (mem_image_of_mem _ hx.1)).ne' hx.2

theorem blockPartition (m : ExtendedPseudoMetric X b p) :
    (∀ s ∈ blocks p f U, s.Nonempty) ∧ ⋃₀ (blocks p f U) = U ∧
      (blocks p f U).PairwiseDisjoint id := by
  obtain ⟨hn,hu⟩ := fiberCover (f := f) (U := U) m
  exact ⟨hn,hu,fun _ h _ k hne => (fiberPartition m h k).resolve_left hne⟩

theorem finerFibers (m : ∀ i, ExtendedPseudoMetric X b (d i)) :
    finer d U f g ↔ ∀ x ∈ U, fiber (subdist d univ) f U (f.func x) ⊆
      fiber (subdist d univ) g U (g.func x) := by
  constructor
  · intro h x hx y hy
    exact (relationFiber m hx hy.1).1 (h ((relationFiber m hx hy.1).2 hy))
  · intro h z hz
    exact (relationFiber m hz.1 hz.2.1).2 (h _ hz.1 ((relationFiber m hz.1 hz.2.1).1 hz))

theorem finiteFiner {n : ℕ} (F : Fin (n+1) → Op b) (_hd : ∀ k, U ⊆ dom (F k))
    (h : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) {a c : Fin (n+1)} (hac : a ≤ c) :
    finer d U (F a) (F c) :=
  ((Fin.monotone_iff_le_succ (f := fun i => zeroRel d (F i) U)).2 h) hac

theorem strictFiniteFiner {n : ℕ} (F : Fin (n+1) → Op b) (hd : ∀ k, U ⊆ dom (F k))
    (h : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) {k : Fin n}
    (hs : zeroRel d (F k.castSucc) U ⊂ zeroRel d (F k.succ) U) :
    zeroRel d (F 0) U ⊂ zeroRel d (F (Fin.last n)) U ∧
      ∃ z ∈ zeroRel d (F k.succ) U \ zeroRel d (F k.castSucc) U,
        z ∈ zeroRel d (F (Fin.last n)) U \ zeroRel d (F 0) U := by
  obtain ⟨z,hz,hn⟩ := Set.exists_of_ssubset hs
  have hz' := finiteFiner F hd h (Fin.le_last k.succ) hz
  have hn' : z ∉ zeroRel d (F 0) U := fun hc => hn (finiteFiner F hd h (Fin.zero_le _) hc)
  exact ⟨⟨finiteFiner F hd h (Fin.zero_le _),fun hc => hn' (hc hz')⟩,z,⟨hz,hn⟩,hz',hn'⟩

theorem pointMinimum [Finite I] {J : Set I} (hJ : J.Nonempty) (i : I) (y : X) :
    IsLeast ((fun j => radius (d i) (d j) f U y) '' J) (radius (d i) (subdist d J) f U y) := by
  rw [radiusInf]
  obtain ⟨j,hj,he⟩ := finiteMin hJ (fun k => radius (d i) (d k) f U y)
  exact ⟨⟨j,hj,he⟩,fun _ ⟨k,hk,e⟩ => e ▸ iInf_le (fun t : J => radius (d i) (d t) f U y) ⟨k,hk⟩⟩

theorem matrixMinimum [Finite I] {J : Set I} (hJ : J.Nonempty) (i : I) :
    IsLeast ((fun j => matrix d f U j i) '' J) (uniform (d i) (subdist d J) f U U) := by
  rw [uniformInf]
  obtain ⟨j,hj,he⟩ := finiteMin hJ (fun k => matrix d f U k i)
  exact ⟨⟨j,hj,he⟩,fun _ ⟨k,hk,e⟩ => e ▸ iInf_le (fun t : J => matrix d f U t i) ⟨k,hk⟩⟩

theorem radiusNotation {J : Set I} (i j : I) (y : X) :
    radius (d i) (subdist d {j}) f U y = radius (d i) (d j) f U y ∧
    (∀ A : Set X, uniform (d i) (subdist d J) f A U = ⨅ a : A, radius (d i) (subdist d J) f U a) ∧
    matrix d f U j i = ⨅ a : U, radius (d i) (d j) f U a := by
  rw [show subdist d {j} = d j from subfamily_pseudometric_singleton d j]
  exact ⟨rfl,fun _ => rfl,rfl⟩

theorem channelTable (σ : Scale X I) (A : Region X) (_hA : A.val ⊆ dom f)
    {s t : ENNReal} (_hs : positiveFinite s) (_ht : positiveFinite t) (i j : I) :
    let c := channel σ d f A s t (i,j)
    let a := σ.value i A
    let n := matrix d f A j i
    (c = (true,true) ↔ a < s ∧ t ≤ n) ∧ (c = (true,false) ↔ a < s ∧ n < t) ∧
    (c = (false,true) ↔ s ≤ a ∧ t ≤ n) ∧ (c = (false,false) ↔ s ≤ a ∧ n < t) := by
  simp [channel,bits]

theorem boundedNets : boundedAtAll p U ↔ ∀ r, positiveFinite r → ∃ C, Net p r U C := by
  simp only [boundedAtAll,lt_top_iff_ne_top,ne_eq,cover,covering_number_eq_top_iff,not_not,Net]

theorem entropyOrder {V : Set X} {r : ENNReal} :
    entropy p e U ≤ entropy q r V ↔ cover p e U ≤ cover q r V := logStrict.le_iff_le

theorem deltaSigns (hne : U.Nonempty) (h : good p q f U e) :
    (0 < delta p q f U e h ↔ entropy q e (f.func '' U) < entropy p e U) ∧
    (delta p q f U e h < 0 ↔ entropy p e U < entropy q e (f.func '' U)) ∧
    (delta p q f U e h = 0 ↔ entropy p e U = entropy q e (f.func '' U)) := by
  have ht : entropy p e U ≠ ⊤ ∨ entropy q e (f.func '' U) ≠ ⊤ := by
    rcases h with hi|ho
    · obtain ⟨a,ha⟩ := finiteLog hne hi
      exact Or.inl (ha ▸ EReal.coe_ne_top a)
    · obtain ⟨a,ha⟩ := finiteLog (hne.image _) ho
      exact Or.inr (ha ▸ EReal.coe_ne_top a)
  have hb : entropy p e U ≠ ⊥ := ((show (⊥ : EReal) < 0 by simp).trans_le (metric_entropy_nonneg _ _ _ hne)).ne'
  have neg := EReal.sub_neg ht (Or.inl hb)
  refine ⟨EReal.sub_pos,neg,?_⟩
  change _ - _ = 0 ↔ _
  constructor
  · intro he
    exact le_antisymm (le_of_not_gt fun k => (EReal.sub_pos.2 k).ne' he)
      (le_of_not_gt fun k => (neg.2 k).ne he)
  · intro he
    exact le_antisymm (EReal.sub_nonpos.2 he.le) (le_of_not_gt fun k => (neg.1 k).ne he)

theorem lipCenters {L : ENNReal} (hl : positiveFinite L)
    (h : ∀ x ∈ U, ∀ y ∈ U, q (f.func x) (f.func y) ≤ L*p x y)
    (C : Finset X) (hc : Net p (e/L) U C) :
    ∃ T : Finset X, Net q e (f.func '' U) T ∧ T.card ≤ C.card :=
  pushNet hc fun x hx y hy hd => (h _ hx _ hy).trans_lt
    (by simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hl.1.ne') (Or.inl hl.2.ne)).1 hd)

theorem coCenters [Fintype I] (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : positiveFinite (K i j))
    (T : Finset X) (ht : Net (d j) e (f.func '' U) T) :
    ∃ C : Finset X, Net (d i) (e/K i j) U C ∧ C.card ≤ T.card := by
  apply pullNet ht
  intro x hx y hy hd
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hk.1.ne') (Or.inl hk.2.ne)).2
  rw [mul_comm]
  exact (Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)).trans_lt
    ((hK.2.2 x hx y hy j).trans_lt hd)

end
end MG
```

```lean filename=Ch3/Entropy.lean
import Ch3.Scale
import Mathlib.Data.EReal.Operations

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X I : Type} {b : X} {f : Op b} {p q : Dist X} {A B U : Set X} {e r L : ENNReal}
abbrev cover := @covering_number
abbrev entropy := @metric_entropy
abbrev Net := @InternalEpsilonNet
def boundedAtAll (p : Dist X) (U : Set X) := ∀ r, positiveFinite r → cover p r U < ⊤
def good (p q : Dist X) (f : Op b) (U : Set X) (e : ENNReal) :=
  cover p e U < ⊤ ∨ cover q e (f.func '' U) < ⊤
def delta (p q : Dist X) (f : Op b) (U : Set X) (e : ENNReal) (_h : good p q f U e) :=
  entropy p e U - entropy q e (f.func '' U)

def mapDelta (d : I → Dist X) (S T : Set I) (_hS : S.Nonempty) (_hT : T.Nonempty)
    (f : Op b) (U : Set X) (_hne : U.Nonempty) (_hU : U ⊆ dom f) (e : ENNReal)
    (_he : positiveFinite e) (hg : good (subdist d S) (subdist d T) f U e) :=
  delta (subdist d S) (subdist d T) f U e hg

theorem mapDelta_formula (d : I → Dist X) {S T : Set I} (hS : S.Nonempty) (hT : T.Nonempty)
    (hne : U.Nonempty) (hU : U ⊆ dom f) (he : positiveFinite e) (hg) :
    mapDelta d S T hS hT f U hne hU e he hg =
      subfamily_metric_entropy d S e U - subfamily_metric_entropy d T e (f.func '' U) := rfl

theorem netBalls {C : Finset X} : Net p e U C ↔ (C : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ C, ball p c e := by
  simp [Net,InternalEpsilonNet,ball,Set.subset_def]

theorem netUpper {C : Finset X} (hC : Net p e U C) : cover p e U ≤ C.card :=
  iInf_le_of_le C (iInf_le_of_le hC le_rfl)

theorem coverLower {n : ENNReal} (h : ∀ C : Finset X, Net p e U C → n ≤ C.card) :
    n ≤ cover p e U := le_iInf fun C => le_iInf (h C)

theorem pushNet {C : Finset X} (hC : Net p r U C)
    (h : ∀ x ∈ U, ∀ c ∈ U, p x c < r → q (f.func x) (f.func c) < e) :
    ∃ T : Finset X, Net q e (f.func '' U) T ∧ T.card ≤ C.card := by
  classical
  refine ⟨C.image f.func,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro z hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    exact mem_image_of_mem _ (hC.1 hc)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨c,hc,hd⟩ := hC.2 x hx
    exact ⟨_,Finset.mem_image_of_mem _ hc,h _ hx _ (hC.1 hc) hd⟩

theorem pullNet {T : Finset X} (hT : Net q e (f.func '' U) T)
    (h : ∀ x ∈ U, ∀ c ∈ U, q (f.func x) (f.func c) < e → p x c < r) :
    ∃ C : Finset X, Net p r U C ∧ C.card ≤ T.card := by
  classical
  let rep (z : X) := if hz : z ∈ f.func '' U then hz.choose else b
  have spec (z) (hz : z ∈ f.func '' U) : rep z ∈ U ∧ f.func (rep z) = z := by
    simpa only [rep,dif_pos hz] using hz.choose_spec
  refine ⟨T.image rep,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    exact (spec _ (hT.1 hz)).1
  · intro x hx
    obtain ⟨z,hz,hd⟩ := hT.2 _ (mem_image_of_mem _ hx)
    obtain ⟨hu,hz'⟩ := spec _ (hT.1 hz)
    exact ⟨_,Finset.mem_image_of_mem _ hz,h x hx _ hu (hz'.symm ▸ hd)⟩

theorem pushCover (h : ∀ x ∈ U, ∀ c ∈ U, p x c < r → q (f.func x) (f.func c) < e) :
    cover q e (f.func '' U) ≤ cover p r U := by
  apply coverLower
  intro C hC
  obtain ⟨T,hT,hcard⟩ := pushNet hC h
  exact (netUpper hT).trans (Nat.cast_le.mpr hcard)

theorem pullCover (h : ∀ x ∈ U, ∀ c ∈ U, q (f.func x) (f.func c) < e → p x c < r) :
    cover p r U ≤ cover q e (f.func '' U) := by
  apply coverLower
  intro T hT
  obtain ⟨C,hC,hcard⟩ := pullNet hT h
  exact (netUpper hC).trans (Nat.cast_le.mpr hcard)

theorem logStrict : StrictMono log2_ereal := by
  intro a c h
  have hc := ((zero_le a).trans_lt h).ne'
  have ha := (h.trans_le le_top).ne
  by_cases h₀ : a = 0 <;> by_cases hT : c = ⊤
  all_goals simp [log2_ereal,h₀,hT,hc,ha]
  exact Real.logb_lt_logb one_lt_two (ENNReal.toReal_pos h₀ ha) ((ENNReal.toReal_lt_toReal ha hT).2 h)

theorem thresholdCover (hB : B ⊆ A) (ht : r ≤ uniform p q f A A) (he : 0 < e) :
    cover q e (f.func '' B) ≤ cover p r B :=
  pushCover fun _ hx _ hy hd => (cutUniform (hB hx) (hB hy) (hd.trans_le ht)).trans_lt he

theorem thresholdEntropy (hB : B ⊆ A) (ht : r ≤ uniform p q f A A) (he : 0 < e) :
    entropy q e (f.func '' B) ≤ entropy p r B := logStrict.monotone (thresholdCover hB ht he)

theorem coverOne (hne : U.Nonempty) {c : X} (hc : c ∈ U) (h : ∀ x ∈ U, p x c < e) :
    cover p e U = 1 := by
  classical
  have hn : Net p e U {c} :=
    ⟨by simpa using hc,fun x hx => ⟨c,Finset.mem_singleton_self _,h _ hx⟩⟩
  exact le_antisymm (by simpa using netUpper hn) (one_le_covering_number_of_nonempty _ _ _ hne)

theorem constCover (hne : U.Nonempty) (hc : Const q f U) (he : 0 < e) : cover q e (f.func '' U) = 1 := by
  obtain ⟨a,ha⟩ := hne
  apply coverOne ⟨_,mem_image_of_mem _ ha⟩ (mem_image_of_mem _ ha)
  rintro _ ⟨x,hx,rfl⟩
  exact (hc _ hx _ ha).trans_lt he

theorem smallCover (hne : U.Nonempty) {ts tn : ENNReal} (hs : diam p U < ts) (ht : ts ≤ tn)
    (hr : tn ≤ uniform p q f U U) (he : positiveFinite e) : cover q e (f.func '' U) = 1 :=
  constCover hne ((smallDomain hs ht).1 hr) he.1

theorem finiteCover (m : ExtendedPseudoMetric X b p) (hu : U.Finite) (he : 0 < e) :
    cover p e U < ⊤ := by
  classical
  have hn : Net p e U hu.toFinset :=
    ⟨by simp,fun x hx => ⟨x,hu.mem_toFinset.mpr hx,(m.dist_self _).trans_lt he⟩⟩
  exact (netUpper hn).trans_lt (ENNReal.natCast_lt_top _)

theorem finiteLog (hne : U.Nonempty) (h : cover p e U < ⊤) :
    ∃ a : ℝ, entropy p e U = a := by
  have hp := zero_lt_one.trans_le (one_le_covering_number_of_nonempty p e U hne)
  exact ⟨Real.logb 2 (cover p e U).toReal,by simp [entropy,metric_entropy,log2_ereal,hp.ne',h.ne,cover]⟩

theorem deltaBranches (hne : U.Nonempty) (hg : good p q f U e) :
    (cover p e U = ⊤ → delta p q f U e hg = ⊤) ∧
    (cover q e (f.func '' U) = ⊤ → delta p q f U e hg = ⊥) ∧
    (cover p e U < ⊤ → cover q e (f.func '' U) < ⊤ → ∃ a : ℝ, delta p q f U e hg = a) := by
  refine ⟨?_,?_,?_⟩
  · intro ht
    have ho := hg.resolve_left (not_lt_of_ge ht.ge)
    obtain ⟨a,ha⟩ := finiteLog (hne.image _) ho
    rw [delta,ha]
    simp [entropy,metric_entropy,ht,log2_ereal]
  · intro ht
    simp [delta,entropy,metric_entropy,ht,log2_ereal,EReal.sub_top]
  · intro ha hc
    obtain ⟨a,ha⟩ := finiteLog hne ha
    obtain ⟨c,hc⟩ := finiteLog (hne.image _) hc
    exact ⟨a-c,by rw [delta,ha,hc,EReal.coe_sub]⟩

theorem finiteData (mp : ExtendedPseudoMetric X b p) (mq : ExtendedPseudoMetric X b q)
    (hne : U.Nonempty) (hu : U.Finite) (he : positiveFinite e) :
    positiveFinite (cover p e U) ∧ positiveFinite (cover q e (f.func '' U)) ∧
    (∃ a : ℝ, entropy p e U = a) ∧ (∃ c : ℝ, entropy q e (f.func '' U) = c) ∧ good p q f U e := by
  have hi := finiteCover mp hu he.1
  have ho := finiteCover mq (hu.image f.func) he.1
  exact ⟨⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hne),hi⟩,
    ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hne.image _)),ho⟩,
    finiteLog hne hi,finiteLog (hne.image _) ho,Or.inl hi⟩

def subfamilyData (d : I → Dist X) (m : ∀ i, ExtendedPseudoMetric X b (d i))
    (S T : Set I) (hS : S.Nonempty) (hT : T.Nonempty) (hne : U.Nonempty) (hu : U.Finite) (he : positiveFinite e) :=
  @finiteData X b f (subdist d S) (subdist d T) U e
    (subfamily_pseudometric_is_extended d S hS m) (subfamily_pseudometric_is_extended d T hT m) hne hu he

theorem constDelta (hne : U.Nonempty) (hc : Const p f U) (he : 0 < e) :
    cover p e (f.func '' U) = 1 ∧ entropy p e (f.func '' U) = 0 ∧
      ∃ hg : good p p f U e, delta p p f U e hg = entropy p e U := by
  have hn := constCover hne hc he
  have hz : entropy p e (f.func '' U) = 0 := by change log2_ereal (cover p e (f.func '' U)) = 0; simp [hn,log2_ereal] 
  exact ⟨hn,hz,Or.inr (hn.trans_lt ENNReal.one_lt_top),by simp [delta,hz]⟩

theorem identCover (m : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    cover p e (f.func '' U) = cover p e U ∧ entropy p e (f.func '' U) = entropy p e U := by
  have hn := le_antisymm
    (pushCover (e := e) fun x hx y hy h => (identDist m hi hx hy).trans_lt h)
    (pullCover (r := e) fun x hx y hy h => (identDist m hi hx hy).symm.trans_lt h)
  exact ⟨hn,congrArg log2_ereal hn⟩

theorem identDelta (m : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hne : U.Nonempty)
    (hg : good p p f U e) : delta p p f U e hg = 0 := by
  obtain ⟨hn,he⟩ := identCover (e := e) m hi
  have hfin : cover p e U < ⊤ := hg.elim id (hn ▸ id)
  obtain ⟨a,ha⟩ := finiteLog hne hfin
  rw [delta,he,ha,← EReal.coe_sub,sub_self,EReal.coe_zero]

theorem lipCover (_hL : positiveFinite L)
    (hl : ∀ x ∈ U, ∀ y ∈ U, q (f.func x) (f.func y) ≤ L * p x y) :
    cover q e (f.func '' U) ≤ cover p (e/L) U :=
  pushCover fun x hx y hy hd => (hl _ hx _ hy).trans_lt (by simpa [mul_comm] using ENNReal.mul_lt_of_lt_div hd)

theorem divScale (he : positiveFinite e) (hL : positiveFinite L) : positiveFinite (e/L) :=
  ⟨ENNReal.div_pos he.1.ne' hL.2.ne, ENNReal.div_lt_top he.2.ne hL.1.ne'⟩

theorem lipDelta (hu : boundedAtAll p U) (hne : U.Nonempty) (he : positiveFinite e) (hL : positiveFinite L)
    (hl : ∀ x ∈ U, ∀ y ∈ U, q (f.func x) (f.func y) ≤ L * p x y) :
    (∃ a : ℝ, entropy p e U = a) ∧ (∃ a : ℝ, entropy p (e/L) U = a) ∧
    (∃ a : ℝ, entropy q e (f.func '' U) = a) ∧ ∃ hg : good p q f U e,
      entropy p e U - entropy p (e/L) U ≤ delta p q f U e hg := by
  have hn := lipCover (e := e) hL hl
  have hs := hu _ (divScale he hL)
  exact ⟨finiteLog hne (hu e he),finiteLog hne hs,finiteLog (hne.image _) (hn.trans_lt hs),
    Or.inl (hu e he),EReal.sub_le_sub le_rfl (logStrict.monotone hn)⟩

theorem coCover [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : positiveFinite (K i j)) :
    cover (d i) (e/K i j) U ≤ cover (d j) e (f.func '' U) := by
  apply pullCover
  intro x hx y hy hd
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hk.1.ne') (Or.inl hk.2.ne)).2
  rw [mul_comm]
  exact (Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)).trans_lt
    ((hK.2.2 x hx y hy j).trans_lt hd)

theorem coDelta [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : positiveFinite (K i j)) (he : positiveFinite e)
    (hu : boundedAtAll (d i) U) :
    ∃ hg : good (d i) (d j) f U e, delta (d i) (d j) f U e hg ≤ entropy (d i) e U - entropy (d i) (e/K i j) U :=
  ⟨Or.inl (hu e he),EReal.sub_le_sub le_rfl (logStrict.monotone (coCover d K i j hK hk))⟩

end
end MG
```

```lean filename=Ch3/Factor.lean
import Ch3.Components

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
variable {X I : Type} {b : X} {f g k : Op b} {U : Set X} {d : I → Dist X}

def pairs (f : Op b) (U : Set X) (R : X → X → Prop) : Set (X × X) :=
  {z | z.1 ∈ U ∧ z.2 ∈ U ∧ R (f.func z.1) (f.func z.2)}
abbrev eqRel (f : Op b) (U : Set X) := pairs f U Eq
abbrev zeroRel (d : I → Dist X) (f : Op b) (U : Set X) := pairs f U (GaugeZeroRelated d)
def finer (d : I → Dist X) (U : Set X) (f g : Op b) := zeroRel d f U ⊆ zeroRel d g U

theorem relationFiber (m : ∀ i, ExtendedPseudoMetric X b (d i)) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ zeroRel d f U ↔ y ∈ fiber (subdist d univ) f U (f.func x) := by
  change (_ ∧ _ ∧ ∀ i, _ = 0) ↔ _ ∧ _ = 0
  simp [hx,hy,subzero, (m _).symm (f.func y) (f.func x)]

def atImage (f : Op b) (U : Set X) (x : U) : f.func '' U := ⟨_,x.val,x.property,rfl⟩
theorem ontoImage : Function.Surjective (atImage f U) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem descend {S A B : Type} (a : S → A) (v : S → B) (ha : Function.Surjective a) :
    (∃ t : A → B, ∀ x, t (a x) = v x) ↔ ∀ x y, a x = a y → v x = v y := by
  constructor
  · rintro ⟨t,h⟩ x y he
    rw [← h, ← h, he]
  · intro h
    exact ⟨fun z => v (ha z).choose, fun x => h _ _ (ha (a x)).choose_spec⟩

def transforms (f g : Op b) (U : Set X) :=
  ∃ t : (f.func '' U) → X, ∀ x : U, t (atImage f U x) = g.func x

theorem pointFactor : transforms f g U ↔ eqRel f U ⊆ eqRel g U := by
  unfold transforms
  rw [descend _ _ ontoImage]
  constructor
  · intro h z hz
    exact ⟨hz.1,hz.2.1,h ⟨_,hz.1⟩ ⟨_,hz.2.1⟩ (Subtype.ext hz.2.2)⟩
  · intro h x y he
    exact (h (show (x.val,y.val) ∈ eqRel f U from
      ⟨x.2,y.2,congrArg Subtype.val he⟩)).2.2

theorem bothPoint : transforms f g U ∧ transforms g f U ↔ eqRel f U = eqRel g U := by
  rw [pointFactor,pointFactor,Set.Subset.antisymm_iff]

def positiveFinite (r : ENNReal) := 0 < r ∧ r < ⊤

theorem factorLip {p : Dist X} {K L : ENNReal} (hK : positiveFinite K) (_hL : L < ⊤)
    (t : (f.func '' U) → X) (ht : ∀ x : U, t (atImage f U x) = g.func x)
    (lo : ∀ x ∈ U, ∀ y ∈ U, K * p x y ≤ p (f.func x) (f.func y))
    (hi : ∀ x ∈ U, ∀ y ∈ U, p (g.func x) (g.func y) ≤ L * p x y)
    (u v : f.func '' U) : p (t u) (t v) ≤ (L/K) * p u v := by
  obtain ⟨x,rfl⟩ := ontoImage u
  obtain ⟨y,rfl⟩ := ontoImage v
  rw [ht,ht]
  calc
    _ ≤ L * p x y := hi _ x.2 _ y.2
    _ = (L/K) * (K * p x y) := by rw [← mul_assoc, ENNReal.div_mul_cancel hK.1.ne' hK.2.ne]
    _ ≤ _ := mul_le_mul_right (lo _ x.2 _ y.2) _

def imageSetoid (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f : Op b) (U : Set X) :
    Setoid (f.func '' U) where
  r x y := GaugeZeroRelated d x.val y.val
  iseqv := (gauge_zero_related_equivalence d (fun i => (m i).dist_self)
    (fun i => (m i).symm) (fun i => (m i).triangle)).comap Subtype.val

abbrev ImageQuot (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f : Op b) (U : Set X) :=
  Quotient (imageSetoid m f U)
def atClass (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f : Op b) (U : Set X) (x : U) :
    ImageQuot m f U := Quotient.mk _ (atImage f U x)

theorem classEq (m : ∀ i, ExtendedPseudoMetric X b (d i)) (x y : U) :
    atClass m f U x = atClass m f U y ↔ GaugeZeroRelated d (f.func x) (f.func y) :=
  Quotient.eq

theorem ontoClass (m : ∀ i, ExtendedPseudoMetric X b (d i)) : Function.Surjective (atClass m f U) := by
  intro q
  obtain ⟨s,rfl⟩ := Quotient.exists_rep q
  obtain ⟨x,rfl⟩ := ontoImage s
  exact ⟨x,rfl⟩

def quotTransforms (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f g : Op b) (U : Set X) :=
  ∃ t : ImageQuot m f U → ImageQuot m g U, ∀ x : U, t (atClass m f U x) = atClass m g U x

theorem quotFactor (m : ∀ i, ExtendedPseudoMetric X b (d i)) : quotTransforms m f g U ↔ finer d U f g := by
  unfold quotTransforms
  rw [descend _ _ (ontoClass m)]
  simp only [classEq]
  constructor
  · intro h z hz
    exact ⟨hz.1,hz.2.1,h ⟨_,hz.1⟩ ⟨_,hz.2.1⟩ hz.2.2⟩
  · intro h x y he
    exact (h (show (x.val,y.val) ∈ zeroRel d f U from ⟨x.2,y.2,he⟩)).2.2

theorem bothQuot (m : ∀ i, ExtendedPseudoMetric X b (d i)) :
    quotTransforms m f g U ∧ quotTransforms m g f U ↔ zeroRel d f U = zeroRel d g U := by
  rw [quotFactor,quotFactor,Set.Subset.antisymm_iff]
  rfl

def separatesOn (d : I → Dist X) (S : Set X) :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

theorem sepRel (m : ∀ i, ExtendedPseudoMetric X b (d i)) (hs : separatesOn d (f.func '' U)) :
    eqRel f U = zeroRel d f U := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨hz.1,hz.2.1,?_⟩
    intro i
    rw [hz.2.2, (m i).dist_self]
  · intro z hz
    exact ⟨hz.1,hz.2.1,hs _ (mem_image_of_mem _ hz.1) _ (mem_image_of_mem _ hz.2.1) hz.2.2⟩

theorem separatedFactors (m : ∀ i, ExtendedPseudoMetric X b (d i))
    (hf : separatesOn d (f.func '' U)) (hg : separatesOn d (g.func '' U)) :
    (transforms f g U ↔ quotTransforms m f g U) ∧
    ((transforms f g U ∧ transforms g f U) ↔ (quotTransforms m f g U ∧ quotTransforms m g f U)) := by
  rw [bothPoint,bothQuot,pointFactor,quotFactor,sepRel m hf,sepRel m hg]
  exact ⟨Iff.rfl,Iff.rfl⟩

theorem finerRefl : finer d U f f := Subset.rfl
theorem finerTrans (a : finer d U f g) (c : finer d U g k) : finer d U f k := a.trans c

theorem finerChain (F : ℕ → Op b) {n : ℕ} (step : ∀ r < n, finer d U (F r) (F (r+1)))
    {a c : ℕ} (hac : a ≤ c) (hc : c ≤ n) : finer d U (F a) (F c) := by
  induction c, hac using Nat.le_induction with
  | base => exact finerRefl
  | succ t _ ih => exact finerTrans (ih (by omega)) (step t (by omega))

theorem strictChain (F : ℕ → Op b) {n r : ℕ} (step : ∀ s < n, finer d U (F s) (F (s+1)))
    (hr : r < n) (hs : zeroRel d (F r) U ⊂ zeroRel d (F (r+1)) U) :
    zeroRel d (F 0) U ⊂ zeroRel d (F n) U ∧
      ∃ z ∈ zeroRel d (F (r+1)) U \ zeroRel d (F r) U, z ∈ zeroRel d (F n) U \ zeroRel d (F 0) U := by
  obtain ⟨z,hz,hn⟩ := Set.exists_of_ssubset hs
  have hz' := finerChain F step (a := r+1) (c := n) hr le_rfl hz
  have hn' : z ∉ zeroRel d (F 0) U := fun h => hn (finerChain F step (Nat.zero_le r) hr.le h)
  exact ⟨⟨finerChain F step (Nat.zero_le n) le_rfl, fun h => hn' (h hz')⟩,z,⟨hz,hn⟩,hz',hn'⟩

end MG
```

```lean filename=Ch3/Floor.lean
import Ch3.RealTools

namespace MG.Floor
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
def f := liftOp fun x : ℝ => (⌊x⌋ : ℝ)
abbrev D (S : Set ℝ) := realSet S
def N (S : Set ℝ) := uniform usual usual f (D S) (D S)
def kind (S : Set ℝ) := bits (diam usual (D S)) (N S) 1 1
theorem channel_eq {S : Set ℝ} (h : S.Nonempty) :
    channel (diamScale (fun _ : Unit => usual)) (fun _ : Unit => usual) f ⟨D S,realNonempty h⟩
      1 1 ((),()) = kind S := rfl
theorem domain (S : Set ℝ) : D S ⊆ dom f := realDom _ S

theorem crosses {u v : ℝ} (hu : u < 1) (hv : 1 ≤ v) : N (Icc u v) = 0 := by
  apply smallZero
  intro t ht
  let a := min (min (1-u) (1/2)) t
  have ha : 0 < a := lt_min (lt_min (by linarith) (by norm_num)) ht
  have h1 : a ≤ 1-u := (min_le_left _ t).trans (min_le_left _ _)
  have h2 : a ≤ 1/2 := (min_le_left _ t).trans (min_le_right _ _)
  have h3 : a ≤ t := min_le_right _ _
  have hfloor : ⌊1-a⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
  have hx : pt (1-a) ∈ D (Icc u v) := mem_realSet.2 ⟨by linarith,by linarith⟩
  have hy : pt 1 ∈ D (Icc u v) := mem_realSet.2 ⟨hu.le,hv⟩
  have hp : 0 < usual (f.func (pt (1-a))) (f.func (pt 1)) := by norm_num [usual,f,hfloor]
  calc
    _ ≤ usual (pt (1-a)) (pt 1) := separation hx hy hp
    _ = ENNReal.ofReal a := by simp [usual,abs_of_pos ha]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h3

theorem firstInterval :
    diam usual (D (Icc 0 (1/2))) = 1/2 ∧ N (Icc 0 (1/2)) = ⊤ ∧ kind (Icc 0 (1/2)) = (true,true) := by
  have hd := intervalDiam (u := 0) (v := 1/2) (by norm_num)
  norm_num at hd
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)] at hd
  have hc : Const usual f (D (Icc 0 (1/2))) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    have h (z : ℝ) (hz : z ∈ Icc (0:ℝ) (1/2)) : ⌊z⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨hz.1,lt_of_le_of_lt hz.2 (by norm_num)⟩
    simp [f,usual,h x hx,h y hy]
  have hr := (constRadii usual hc).2
  exact ⟨by simpa only [one_div] using hd,hr,by unfold kind N; rw [hd,hr]; norm_num [bits]⟩

theorem jumpInterval :
    diam usual (D (Icc (9/10) (11/10))) = 1/5 ∧ N (Icc (9/10) (11/10)) = 0 ∧
    kind (Icc (9/10) (11/10)) = (true,false) := by
  have hd := intervalDiam (u := 9/10) (v := 11/10) (by norm_num)
  norm_num at hd
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)] at hd
  have hr := crosses (u := 9/10) (v := 11/10) (by norm_num) (by norm_num)
  exact ⟨by simpa only [one_div] using hd,hr,by unfold kind; rw [hd,hr]; norm_num [bits]⟩

theorem pairValue : N {0,2} = 2 := by
  apply le_antisymm
  · have hx : pt 0 ∈ D {0,2} := mem_realSet.mpr (Or.inl rfl)
    have hy : pt 2 ∈ D {0,2} := mem_realSet.mpr (Or.inr rfl)
    have h := separation (p := usual) hx hy (q := usual) (f := f) (by norm_num [f,usual])
    simpa [usual] using h
  · apply uniformBound.2
    rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩
    change x = 0 ∨ x = 2 at hx
    change y = 0 ∨ y = 2 at hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> norm_num [usual,f]

theorem pairType :
    diam usual (D {0,2}) = 2 ∧ N {0,2} = 2 ∧ kind {0,2} = (false,true) := by
  have hd := pairDiam (u := 0) (v := 2) (by norm_num)
  norm_num at hd
  exact ⟨hd,pairValue,by unfold kind; rw [hd,pairValue]; norm_num [bits]⟩

theorem wholeInterval :
    diam usual (D (Icc 0 2)) = 2 ∧ N (Icc 0 2) = 0 ∧ kind (Icc 0 2) = (false,false) := by
  have hd := intervalDiam (u := 0) (v := 2) (by norm_num)
  norm_num at hd
  have hr := crosses (u := 0) (v := 2) (by norm_num) (by norm_num)
  exact ⟨by simpa only [one_div] using hd,hr,by unfold kind; rw [hd,hr]; norm_num [bits]⟩

theorem counterexample : (D {0,2}).Nonempty ∧ 1 ≤ N {0,2} ∧ ¬ Const usual f (D {0,2}) := by
  have hx : pt 0 ∈ D {0,2} := mem_realSet.2 (Or.inl rfl)
  have hy : pt 2 ∈ D {0,2} := mem_realSet.2 (Or.inr rfl)
  refine ⟨⟨_,hx⟩,by rw [pairValue]; norm_num,fun h => ?_⟩
  have H := h _ hx _ hy
  norm_num [f,usual] at H
end
end MG.Floor
```

```lean filename=Ch3/Models.lean
import Ch3.Scale

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {D E : Type}

def extend (p : Dist D) : Dist (Option D)
  | none, none => 0
  | some x, some y => p x y
  | _, _ => ⊤

theorem extended [Nonempty D] (p : Dist D) (hs : ∀ x, p x x = 0)
    (hc : ∀ x y, p x y = p y x) (ht : ∀ x y z, p x z ≤ p x y + p y z) :
    ExtendedPseudoMetric (Option D) none (extend p) where
  nonabsorbing := ⟨some (Classical.arbitrary D),by simp⟩
  dist_self := by rintro (_|x) <;> simp [extend,hs]
  symm := by rintro (_|x) (_|y) <;> simp [extend,hc]
  triangle := by rintro (_|x) (_|y) (_|z) <;> simp [extend,ht]
  isolate_bot := by rintro (_|x) hx <;> simp_all [extend]

def liftOp (a : D → D) : Op (none : Option D) := ⟨Option.map a,rfl⟩
@[simp] theorem lift_some (a : D → D) (x : D) : (liftOp a).func (some x) = some (a x) := rfl
@[simp] theorem mul_apply {X : Type} {b : X} (f g : Op b) (x : X) : (g*f).func x = g.func (f.func x) := rfl
@[simp] theorem one_apply {X : Type} {b : X} (x : X) : (1 : Op b).func x = x := rfl
@[simp] theorem lift_dom (a : D → D) : dom (liftOp a) = range some := by
  ext x
  cases x <;> simp [dom,liftOp]

def discreteRead [DecidableEq E] (a : D → E) (w : ENNReal) :=
  extend fun x y => if a x = a y then 0 else w

theorem discreteMetric [Nonempty D] [DecidableEq E] (a : D → E) (w : ENNReal) :
    ExtendedPseudoMetric (Option D) none (discreteRead a w) := by
  apply extended
  · simp
  · intro x y
    by_cases h : a x = a y <;> simp [h,eq_comm]
  · intro x y z
    by_cases h : a x = a y <;> by_cases k : a y = a z <;> by_cases l : a x = a z <;> simp_all

abbrev pt := @Option.some ℝ
abbrev Line := Option ℝ
def readDist (a : ℝ → ℝ) : Dist Line := extend fun x y => edist (a x) (a y)
abbrev usual := readDist id
abbrev absolute := readDist abs

theorem readMetric (a : ℝ → ℝ) : ExtendedPseudoMetric Line none (readDist a) :=
  extended _ (fun _ => edist_self _) (fun _ _ => edist_comm _ _) (fun _ _ _ => edist_triangle _ _ _)

@[simp] theorem read_points (a : ℝ → ℝ) (x y : ℝ) :
    readDist a (pt x) (pt y) = ENNReal.ofReal |a x - a y| := by
  change edist (a x) (a y) = _
  rw [edist_dist,Real.dist_eq]

def realSet (A : Set ℝ) : Set Line := pt '' A
theorem realDom (a : ℝ → ℝ) (A : Set ℝ) : realSet A ⊆ dom (liftOp a) := by
  rintro _ ⟨x,_,rfl⟩
  exact Option.some_ne_none _
theorem realNonempty {A : Set ℝ} (hA : A.Nonempty) : (realSet A).Nonempty := hA.image _
@[simp] theorem mem_realSet {x : ℝ} {A : Set ℝ} : pt x ∈ realSet A ↔ x ∈ A := by simp [realSet,pt]

namespace Swap
abbrev a := some false
abbrev c := some true
def U : Set (Option Bool) := {a,c}
def d := discreteRead (id : Bool → Bool) 1
def f := liftOp Bool.not

theorem model : ExtendedPseudoMetric _ none d := discreteMetric _ _
theorem domain : U ⊆ dom f := by intro x hx; rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
theorem image_eq : f.func '' U = U := by
  ext x
  simp [U, f, a,c,or_comm,eq_comm]

theorem components : Active d f U ∧ ¬ Ident d f U ∧ Ident d (f*f) U ∧ ¬ Active d (f*f) U := by
  have ha : a ∈ U := Or.inl rfl
  have hc : c ∈ U := Or.inr rfl
  have hn : ¬ Const d f U := fun h => one_ne_zero (h _ ha _ hc)
  have hi : ¬ Ident d f U := fun h => one_ne_zero (h.2 _ ha)
  have hj : Ident d (f*f) U := ⟨fun h => one_ne_zero (h _ ha _ hc),by
    intro x hx
    rcases hx with h|h <;> rw [h] <;> rfl⟩
  exact ⟨⟨hn,hi⟩,hi,hj,fun h => h.2 hj⟩

theorem strictInclusions :
    ({_i : Unit | Active d (f*f) U} ⊂ {_i : Unit | Active d f U} ∪ {_i : Unit | Active d f (f.func '' U)}) ∧
    ({_i : Unit | Ident d f U} ∩ {_i : Unit | Ident d f (f.func '' U)} ⊂ {_i : Unit | Ident d (f*f) U}) := by
  rw [image_eq,union_self,inter_self]
  obtain ⟨ha,hi,hj,hn⟩ := components
  exact ⟨⟨fun _ _ => ha,fun h => hn (h (a := ()) ha)⟩,⟨fun _ _ => hj,fun h => hi (h (a := ()) hj)⟩⟩

def channels (j : Bool) : Dist (Option Bool) := discreteRead (id : Bool → Bool) (if j then 1 else ⊤)
theorem channelsMetric (j : Bool) : ExtendedPseudoMetric _ none (channels j) := discreteMetric _ _
theorem infiniteInput (j : Bool) :
    (∀ y ∈ U, radius (channels false) (channels j) (1 : Op (none : Option Bool)) U y = ⊤) ∧
    matrix channels (1 : Op (none : Option Bool)) U j false = ⊤ ∧ ¬ Const (channels j) (1 : Op (none : Option Bool)) U := by
  have bound : ∀ y ∈ U, ∀ x ∈ U, channels false x y < ⊤ →
      channels j ((1 : Op (none : Option Bool)).func x) ((1 : Op (none : Option Bool)).func y) = 0 := by
    intro y hy x hx
    rcases hx with h|h <;> rcases hy with k|k <;> rw [h,k] <;> simp [channels,a,c,discreteRead,extend]
  refine ⟨fun y hy => top_unique (radiusBound.2 (bound y hy)),top_unique (uniformBound.2 bound),?_⟩
  intro h
  have H := h a (Or.inl rfl) c (Or.inr rfl)
  cases j <;> simp [channels,discreteRead,extend,a,c] at H
end Swap

namespace Seven
inductive P | a | b | p | q | r | s deriving DecidableEq, Inhabited, Fintype
open P

theorem cardinality : Fintype.card (Option P) = 7 := by decide

def key : P → P | q => p | x => x
def d (k : Bool) := discreteRead (if k then id else key) 1
def first : Op (none : Option P) := ⟨fun x => match x with
  | some .a => some .p | some .b => some .q | _ => none,rfl⟩
def lastOp : Op (none : Option P) := ⟨fun x => match x with
  | some .p => some .r | some .q => some .s | _ => none,rfl⟩
def U : Set (Option P) := {some a,some b}
theorem model (k : Bool) : ExtendedPseudoMetric _ none (d k) := discreteMetric _ _
theorem exampleData : U ⊆ dom (lastOp*first) ∧ first.func '' U = {some p,some q} ∧
    Const (d false) first U ∧ d true (some p) (some q) = 1 ∧
    d false ((lastOp*first).func (some a)) ((lastOp*first).func (some b)) = 1 ∧
    ¬ Const (d false) (lastOp*first) U := by
  refine ⟨?_,?_,?_,rfl,rfl,fun h => one_ne_zero (h _ (Or.inl rfl) _ (Or.inr rfl))⟩
  · intro x hx
    rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
  · rw [U,Set.image_insert_eq,Set.image_singleton]; rfl
  · intro x hx y hy
    rcases hx with h|h <;> rcases hy with k|k <;> rw [h,k] <;> rfl
end Seven
end
end MG
```

```lean filename=Ch3/Radius.lean
import Ch3.Factor

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X I : Type} {b : X} {f g : Op b} {U A B : Set X} {p q s : Dist X}
variable {x y : X} {r t : ENNReal}

def legal (p q : Dist X) (f : Op b) (U : Set X) (y : X) : Set ENNReal :=
  {r | positiveFinite r ∧ ∀ x ∈ U, p x y < r → q (f.func x) (f.func y) = 0}
def radius (p q : Dist X) (f : Op b) (U : Set X) (y : X) := sSup (legal p q f U y)
def uniform (p q : Dist X) (f : Op b) (A U : Set X) := ⨅ y : A, radius p q f U y
def matrix (d : I → Dist X) (f : Op b) (U : Set X) (j i : I) := uniform (d i) (d j) f U U

theorem legalBall : r ∈ legal p q f U y ↔ positiveFinite r ∧
    ball p y r ∩ U ⊆ fiber q f U (f.func y) :=
  ⟨fun h => ⟨h.1,fun _ hx => ⟨hx.2,h.2 _ hx.2 hx.1⟩⟩,
   fun h => ⟨h.1,fun _ hx hd => (h.2 ⟨hd,hx⟩).2⟩⟩
theorem radiusEmpty (h : legal p q f U y = ∅) : radius p q f U y = 0 := by simp [radius,h]
theorem uniform_le (hy : y ∈ A) : uniform p q f A U ≤ radius p q f U y :=
  iInf_le _ (⟨y,hy⟩ : A)

theorem extractRadius (h : t < radius p q f U y) : ∃ r ∈ legal p q f U y, t < r :=
  lt_sSup_iff.mp h
theorem cutPoint (hx : x ∈ U) (h : p x y < radius p q f U y) : q (f.func x) (f.func y) = 0 := by
  obtain ⟨r,hr,ht⟩ := extractRadius h
  exact hr.2 _ hx ht

theorem radiusBound : t ≤ radius p q f U y ↔ ∀ x ∈ U, p x y < t → q (f.func x) (f.func y) = 0 := by
  constructor
  · exact fun h x hx hd => cutPoint hx (hd.trans_le h)
  · intro h
    apply le_of_forall_lt
    intro a ha
    obtain ⟨r,har,hrt⟩ := exists_between ha
    exact har.trans_le (le_sSup (s := legal p q f U y)
      ⟨⟨(zero_le a).trans_lt har, hrt.trans_le le_top⟩,fun x hx hd => h x hx (hd.trans hrt)⟩)

theorem uniformBound : t ≤ uniform p q f A U ↔
    ∀ y ∈ A, ∀ x ∈ U, p x y < t → q (f.func x) (f.func y) = 0 := by
  simp only [uniform,le_iInf_iff,Subtype.forall,radiusBound]

theorem cutUniform (hx : x ∈ U) (hy : y ∈ A) (h : p x y < uniform p q f A U) :
    q (f.func x) (f.func y) = 0 := cutPoint hx (h.trans_le (uniform_le hy))

theorem cutFiber (mq : ExtendedPseudoMetric X b q) (h : x ∈ fiber q f U (f.func y)) :
    q (f.func y) (f.func x) = 0 := (mq.symm _ _).trans h.2

theorem cutSymm (mp : ExtendedPseudoMetric X b p) (mq : ExtendedPseudoMetric X b q)
    (hx : x ∈ U) (h : p y x < radius p q f U y) : q (f.func y) (f.func x) = 0 :=
  cutFiber (U := U) mq ⟨hx,cutPoint (p := p) hx (by rwa [mp.symm x y])⟩

theorem cutComp (mq : ExtendedPseudoMetric X b q) {V : Set X} (_hV : V ⊆ dom g)
    (_hx : x ∈ dom f) (_hy : y ∈ dom f) (_hfx : f.func x ∈ V) (_hfy : f.func y ∈ V)
    (h : f.func y ∈ fiber q g V (g.func (f.func x))) : q ((g*f).func x) ((g*f).func y) = 0 :=
  cutFiber (f := g) mq h

theorem constSub (d : I → Dist X) {J : Set I} (h : ∀ j ∈ J, Const (d j) f U) :
    Const (subdist d J) f U :=
  fun x hx y hy => (subzero d J).2 fun j hj => h j hj x hx y hy

theorem constSubFiber (d : I → Dist X) {J : Set I} (h : ∀ j ∈ J, Const (d j) f U) (hy : y ∈ U) :
    fiber (subdist d J) f U (f.func y) = U := by
  ext x
  exact ⟨fun hx => hx.1,fun hx => ⟨hx,constSub d h x hx y hy⟩⟩

theorem constRadii (p : Dist X) (h : Const q f U) :
    (∀ y ∈ U, radius p q f U y = ⊤) ∧ uniform p q f U U = ⊤ :=
  ⟨fun _ hy => top_unique (radiusBound.2 fun _ hx _ => h _ hx _ hy),
    top_unique (uniformBound.2 fun _ hy _ hx _ => h _ hx _ hy)⟩

theorem identBase (mp : ExtendedPseudoMetric X b p) (h : Ident p f U) (hy : y ∈ U) :
    fiber p f U (f.func y) = {x ∈ U | p x y = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [identDist mp h hx hy]

theorem identRadius (mp : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hy : y ∈ U)
    (hr : positiveFinite r) (h : ball p y r ∩ U ⊆ {x ∈ U | p x y = 0}) :
    r ≤ radius p p f U y ∧ 0 < r :=
  ⟨le_sSup (legalBall.2 ⟨hr,by rwa [identBase mp hi hy]⟩),hr.1⟩

theorem radiusInf (d : I → Dist X) (J : Set I) :
    radius p (subdist d J) f U y = ⨅ j : J, radius p (d j) f U y := by
  apply le_antisymm
  · apply le_iInf
    intro j
    exact radiusBound.2 fun x hx hd => (subzero d J).1 (cutPoint hx hd) _ j.2
  · exact radiusBound.2 fun x hx hd => (subzero d J).2 fun j hj =>
      cutPoint hx (hd.trans_le (iInf_le (fun k : J => radius p (d k) f U y) ⟨j,hj⟩))

theorem finiteMin [Finite I] {J : Set I} (hJ : J.Nonempty) (v : I → ENNReal) :
    ∃ j ∈ J, v j = ⨅ k : J, v k := by
  letI : Nonempty J := hJ.to_subtype
  obtain ⟨j,h⟩ := exists_eq_ciInf_of_finite (f := fun k : J => v k)
  exact ⟨j,j.2,h⟩

theorem uniformInf (d : I → Dist X) (J : Set I) (i : I) :
    uniform (d i) (subdist d J) f U U = ⨅ j : J, matrix d f U j i := by
  simp only [uniform, radiusInf, matrix]
  exact iInf_comm

theorem uniformAnti (d : I → Dist X) {J K : Set I} (h : J ⊆ K) (i : I) :
    uniform (d i) (subdist d K) f U U ≤ uniform (d i) (subdist d J) f U U := by
  rw [uniformInf,uniformInf]
  exact le_iInf fun j => iInf_le (fun k : K => matrix d f U k i) ⟨j.val,h j.2⟩

theorem compZeroRadius (h : ∀ a ∈ f.func '' U, ∀ c ∈ f.func '' U,
    s a c = 0 → q (g.func a) (g.func c) = 0) :
    uniform p s f U U ≤ uniform p q (g*f) U U :=
  uniformBound.2 fun y hy x hx hd => h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (cutUniform hx hy hd)

theorem compLipRadius {L : ENNReal} (_hL : positiveFinite L)
    (h : ∀ x ∈ U, ∀ y ∈ U, s (f.func x) (f.func y) ≤ L * p x y) :
    uniform s q g (f.func '' U) (f.func '' U) / L ≤ uniform p q (g*f) U U := by
  apply uniformBound.2
  intro y hy x hx hd
  apply cutUniform (f := g) (p := s) (mem_image_of_mem f.func hx) (mem_image_of_mem f.func hy)
  exact (h _ hx _ hy).trans_lt (by simpa [mul_comm] using ENNReal.mul_lt_of_lt_div hd)

theorem restrictRadius (h : B ⊆ A) : radius p q f A y ≤ radius p q f B y :=
  radiusBound.2 fun _ hx hd => cutPoint (h hx) hd

theorem restrictUniform (h : B ⊆ A) : uniform p q f A A ≤ uniform p q f B B :=
  uniformBound.2 fun _ hy _ hx hd => cutUniform (h hx) (h hy) hd

theorem separation (hx : x ∈ U) (hy : y ∈ U) (hp : 0 < q (f.func x) (f.func y)) :
    uniform p q f U U ≤ p x y := le_of_not_gt fun h => hp.ne' (cutUniform hx hy h)

theorem separationWitness {α τ : ENNReal} (_ht : positiveFinite τ) (_ha : positiveFinite α)
    (ha : uniform p q f U U < α) (_hat : α < τ) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, positiveFinite ε ∧ p x y < α ∧ ε ≤ q (f.func x) (f.func y) := by
  have hn := mt uniformBound.2 (not_le.mpr ha)
  push Not at hn
  obtain ⟨y,hy,x,hx,hd,hq⟩ := hn
  refine ⟨x,hx,y,hy,min 1 (q (f.func x) (f.func y)),⟨lt_min zero_lt_one (pos_iff_ne_zero.mpr hq),
    (min_le_left _ _).trans_lt ENNReal.one_lt_top⟩,hd,min_le_right _ _⟩

theorem thresholdBall (hr : t ≤ uniform p q f U U) (hy : y ∈ U) :
    ball p y t ∩ U ⊆ fiber q f U (f.func y) :=
  fun _ hx => ⟨hx.2,cutUniform hx.2 hy (lt_of_lt_of_le hx.1 hr)⟩

theorem pointGap [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : 0 < K i j) (hy : y ∈ U)
    (_hr : 0 < radius (d i) (d j) f U y) (hx : x ∈ U) :
    d i x y ∉ Ioo 0 (radius (d i) (d j) f U y) :=
  fun h => h.1.ne' (positive_colip_entry_reflects_zero d f U K i j hK hk x hx y hy (cutPoint hx h.2))

theorem uniformGap [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : 0 < K i j) (hy : y ∈ U)
    (_hr : 0 < matrix d f U j i) (hx : x ∈ U) : d i x y = 0 ∨ matrix d f U j i ≤ d i x y := by
  by_cases h : matrix d f U j i ≤ d i x y
  · exact Or.inr h
  · exact Or.inl (positive_colip_entry_reflects_zero d f U K i j hK hk x hx y hy
      (cutUniform hx hy (lt_of_not_ge h)))

end
end MG
```

```lean filename=Ch3/Readout.lean
import Ch3.RealTools

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
open scoped Classical in
theorem fiberInsert {X : Type} {b : X} (p : Dist X) (f : Op b) (x : X) (S : Set X) (y : X) :
    fiber p f (insert x S) y = if p (f.func x) y = 0 then insert x (fiber p f S y) else fiber p f S y := by
  ext a
  by_cases h : p (f.func x) y = 0 <;> by_cases ha : a = x <;> simp [fiber,h,ha]
open scoped Classical in
theorem fiberSingle {X : Type} {b : X} (p : Dist X) (f : Op b) (x y : X) :
    fiber p f {x} y = if p (f.func x) y = 0 then {x} else ∅ := by
  ext a
  by_cases h : p (f.func x) y = 0 <;> by_cases ha : a = x <;> simp [fiber,h,ha]

namespace Affine
def U : Set Line := {pt 0,pt 1}
def f := liftOp fun x : ℝ => 2*x-1
theorem domain : U ⊆ dom f ∧ U ⊆ dom (f*f) := by
  constructor <;> intro x hx <;> rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _

theorem firstStep : fiber absolute f U (f.func (pt 0)) = U ∧ Const absolute f U := by
  constructor
  · norm_num [U,f,absolute,fiberInsert,fiberSingle]
  · intro x hx y hy
    rcases hx with h|h <;> rcases hy with k|k <;> rw [h,k] <;> norm_num [f,absolute]

theorem secondStep : fiber absolute (f*f) U ((f*f).func (pt 0)) = {pt 0} ∧ Active absolute (f*f) U := by
  have h0 : pt 0 ∈ U := Or.inl rfl
  have h1 : pt 1 ∈ U := Or.inr rfl
  refine ⟨?_,fun hc => ?_,fun hi => ?_⟩
  · norm_num [U,f,absolute,fiberInsert,fiberSingle]
  · have h := hc _ h0 _ h1
    norm_num [f,absolute] at h
  · have h := hi.2 _ h0
    norm_num [f,absolute] at h

theorem sameValue (g : Op (none : Line)) (c : ℝ) (h : ∀ x ∈ U, g.func x = pt c) :
    (∀ x ∈ U, (g*g).func x = g.func (pt c)) ∧
    (∀ y, pt 0 ∈ fiber absolute (g*g) U y ↔ pt 1 ∈ fiber absolute (g*g) U y) ∧
    (U ⊆ dom (g*g) ↔ g.func (pt c) ≠ none) ∧
    (g.func (pt c) = none → Disjoint U (dom (g*g))) := by
  have H : ∀ x ∈ U, (g*g).func x = g.func (pt c) := fun x hx => congrArg g.func (h x hx)
  have h0 : pt 0 ∈ U := Or.inl rfl
  have h1 : pt 1 ∈ U := Or.inr rfl
  refine ⟨H,fun y => ?_,⟨fun hd => ?_,fun hn x hx => ?_⟩,fun hn => ?_⟩
  · simp only [fiber,mem_setOf_eq,h0,h1,H _ h0,H _ h1]
  · simpa only [dom,mem_setOf_eq,H _ h0] using hd h0
  · exact fun hb => hn ((H _ hx).symm.trans hb)
  · exact Set.disjoint_left.2 fun x hx hd => hd ((H _ hx).trans hn)
end Affine

namespace Translation
def U : Set Line := {pt (-3),pt (-2),pt 0,pt 2}
def f := liftOp fun x : ℝ => x+1
theorem domain : U ⊆ dom f ∧ U ⊆ dom (1 : Op (none : Line)) := by
  constructor <;> intro x hx <;> rcases hx with h|h|h|h <;> rw [h] <;> exact Option.some_ne_none _

theorem translated : f.func '' U = {pt (-2),pt (-1),pt 1,pt 3} := by
  norm_num [U,f,image_insert_eq,image_singleton]

theorem partitionId : blocks absolute (1 : Op (none : Line)) U =
    {{pt (-3)}, {pt (-2),pt 2}, {pt 0}} := by
  norm_num [blocks,U,image_insert_eq,image_singleton,fiberInsert,fiberSingle,absolute,Set.insert_comm,Set.pair_comm]

theorem partitionShift : blocks absolute f U =
    {{pt (-3)}, {pt (-2),pt 0}, {pt 2}} := by
  norm_num [blocks,U,image_insert_eq,image_singleton,fiberInsert,fiberSingle,f,absolute,Set.insert_comm,Set.pair_comm]

private theorem one_lt_eps : (1 : ENNReal) < 3/2 := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1
  norm_num [ENNReal.toReal_div]
private theorem eps_le_two : (3/2 : ENNReal) ≤ 2 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
  norm_num [ENNReal.toReal_div]
theorem inputCount : cover absolute (3/2) U = 2 := by
  classical
  have h0 : pt 0 ∈ U := by simp [U]
  have h2 : pt 2 ∈ U := by simp [U]
  apply le_antisymm
  · let C : Finset Line := {pt (-2),pt 0}
    have hC : Net absolute (3/2) U C := by
      constructor
      · simp [C,U,Set.subset_def]
      · norm_num [U,C,absolute,one_lt_eps,Finset.mem_insert,Finset.mem_singleton]
    exact (netUpper hC).trans (by norm_num [C,pt])
  · apply twoLower ⟨_,h0⟩
    intro c hc
    rcases hc with h|h|h|h <;> rw [h]
    · exact ⟨_,h0,by norm_num [absolute]; exact eps_le_two.trans (by norm_num)⟩
    · exact ⟨_,h0,by norm_num [absolute]; exact eps_le_two⟩
    · exact ⟨_,h2,by norm_num [absolute]; exact eps_le_two⟩
    · exact ⟨_,h0,by norm_num [absolute]; exact eps_le_two⟩

theorem outputCount : cover absolute (3/2) (f.func '' U) = 1 := by
  rw [translated]
  have h : pt (-2) ∈ ({pt (-2),pt (-1),pt 1,pt 3} : Set Line) := Or.inl rfl
  apply coverOne ⟨_,h⟩ h
  norm_num [absolute,one_lt_eps]

theorem entropyChange : ∃ h : good absolute absolute f U (3/2), delta absolute absolute f U (3/2) h = 1 := by
  refine ⟨Or.inr (outputCount.trans_lt ENNReal.one_lt_top),?_⟩
  change log2_ereal (cover absolute (3/2) U) - log2_ereal (cover absolute (3/2) (f.func '' U)) = 1
  rw [inputCount, outputCount]
  norm_num [log2_ereal, Real.logb_self_eq_one]
end Translation
end
end MG
```

```lean filename=Ch3/RealTools.lean
import Ch3.Models
import Ch3.Entropy

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {X : Type} {b : X} {p q : Dist X} {f : Op b} {A : Set X} {e : ENNReal}

theorem twoLower (hne : A.Nonempty) (hn : ∀ c ∈ A, ∃ x ∈ A, e ≤ p x c) :
    2 ≤ cover p e A := by
  classical
  apply coverLower
  intro C hC
  suffices 2 ≤ C.card by exact_mod_cast this
  by_contra! hc
  obtain ⟨a,ha⟩ := hne
  obtain ⟨c,hc',_⟩ := hC.2 a ha
  obtain ⟨x,hx,hbad⟩ := hn c (hC.1 hc')
  obtain ⟨z,hz,hd⟩ := hC.2 x hx
  have heq := Finset.card_le_one.mp (show C.card ≤ 1 by omega) z hz c hc'
  exact hbad.not_gt (heq ▸ hd)

theorem fullSeparated (S : Finset X) (m : ExtendedPseudoMetric X b p) (he : 0 < e)
    (hs : ∀ x ∈ S, ∀ y ∈ S, p x y < e → x = y) : cover p e (S : Set X) = S.card := by
  apply le_antisymm
  · exact netUpper ⟨Subset.rfl,fun x hx => ⟨x,hx,(m.dist_self _).trans_lt he⟩⟩
  · apply coverLower
    intro C hC
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    obtain ⟨y,hy,hd⟩ := hC.2 x hx
    exact hs x hx y (hC.1 hy) hd ▸ hy

theorem pairCover (m : ExtendedPseudoMetric X b p) (a c : X) (he : 0 < e) :
    cover p e {a,c} = if p a c < e then 1 else 2 := by
  classical
  have ha : a ∈ ({a,c} : Set X) := Or.inl rfl
  have hc : c ∈ ({a,c} : Set X) := Or.inr rfl
  split_ifs with h
  · apply coverOne ⟨a,ha⟩ hc
    intro x hx
    rcases hx with h'|h' <;> rw [h']
    · exact h
    · simpa [m.dist_self] using he
  · have hne : a ≠ c := fun heq => h (heq ▸ (m.dist_self c).trans_lt he)
    let S : Finset X := {a,c}
    have hS : (S : Set X) = {a,c} := by simp [S]
    rw [← hS,fullSeparated S m he]
    · simp [S,hne]
    · intro x hx y hy hd
      have hx' : x ∈ ({a,c} : Set X) := hS ▸ hx
      have hy' : y ∈ ({a,c} : Set X) := hS ▸ hy
      change x = a ∨ x = c at hx'
      change y = a ∨ y = c at hy'
      rcases hx' with h₁|h₁ <;> rcases hy' with h₂|h₂ <;> simp only [h₁,h₂] at hd ⊢
      all_goals first | rfl | exact (h hd).elim | exact (h ((m.symm a c).trans_lt hd)).elim

theorem smallZero {v : ENNReal} (h : ∀ t : ℝ, 0 < t → v ≤ ENNReal.ofReal t) : v = 0 := by
  by_contra hn
  obtain ⟨r,hp,hr⟩ := exists_between (pos_iff_ne_zero.2 hn)
  have hf := (hr.trans_le le_top).ne
  have H := h r.toReal (ENNReal.toReal_pos hp.ne' hf)
  rw [ENNReal.ofReal_toReal hf] at H
  exact hr.not_ge H

theorem realDiam {S : Set ℝ} {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) (h : S ⊆ Icc u v) :
    diam usual (realSet S) = ENNReal.ofReal (v-u) := by
  apply le_antisymm
  · apply diam_le
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    simp only [usual,read_points,id_eq]
    apply ENNReal.ofReal_le_ofReal
    exact abs_le.mpr ⟨by linarith [(h hx).1,(h hy).2],by linarith [(h hx).2,(h hy).1]⟩
  · have H := le_diam (p := usual) (mem_realSet.mpr hv) (mem_realSet.mpr hu)
    simpa [usual,abs_of_nonneg (sub_nonneg.mpr (h hv).1)] using H

theorem intervalDiam {u v : ℝ} (huv : u ≤ v) :
    diam usual (realSet (Icc u v)) = ENNReal.ofReal (v-u) :=
  realDiam ⟨le_rfl,huv⟩ ⟨huv,le_rfl⟩ Subset.rfl

theorem pairDiam {u v : ℝ} (huv : u ≤ v) :
    diam usual (realSet {u,v}) = ENNReal.ofReal (v-u) := by
  apply realDiam (Or.inl rfl) (Or.inr rfl)
  rintro _ (rfl|h)
  · exact ⟨le_rfl,huv⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨huv,le_rfl⟩

theorem scaleCounter :
    let A := realSet {0,1}
    let B := realSet {0}
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (1 : Op (none : Line)) ∧
    diam usual B = 0 ∧ diam usual A = 1 ∧
    diam usual B < (1/2 : ENNReal) ∧ (1/2 : ENNReal) ≤ diam usual A := by
  dsimp only
  have ha : diam usual (realSet {0,1}) = 1 := by norm_num [pairDiam (u := 0) (v := 1) (by norm_num)]
  have hb := pairDiam (u := 0) (v := 0) le_rfl
  simp at hb
  refine ⟨⟨pt 0,mem_realSet.2 rfl⟩,Set.image_mono (by simp),?_,hb,ha,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact Option.some_ne_none _
  · rw [hb]; norm_num
  · rw [ha]; norm_num

end
end MG
```

```lean filename=Ch3/Rearrange.lean
import Ch3.RealTools

namespace MG.Rearrange
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
def S : Finset Line := {pt 0,pt 1,pt 2,pt 3}
def U : Set Line := {pt 0,pt 1,pt 2,pt 3}
theorem carrier : (S : Set Line) = U := by simp [S,U]
theorem size : S.card = 4 := by norm_num [S,pt]

open scoped Classical in
def f : Op (none : Line) := ⟨fun x => if x ∈ U then x else none,by simp⟩
def g : Op (none : Line) := ⟨fun x => if x = pt 0 then pt 0 else if x = pt 1 then pt 3 else
  if x = pt 2 then pt 1 else if x = pt 3 then pt 2 else none,by simp [pt]⟩

theorem outside {x : Line} (hx : x ∉ U) : f.func x = none ∧ g.func x = none := by
  simp only [U,mem_insert_iff,mem_singleton_iff,not_or] at hx
  exact ⟨if_neg (by simpa [U] using hx),by simp [g,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2]⟩
theorem f_on {x : Line} (hx : x ∈ U) : f.func x = x := if_pos hx

theorem domain : dom f = U ∧ dom g = U := by
  constructor <;> ext x <;> by_cases hx : x ∈ U
  · have h : x ≠ none := by rcases hx with h|h|h|h <;> rw [h] <;> exact Option.some_ne_none _
    simp [dom,f_on hx,h,hx]
  · simp [dom,(outside hx).1,hx]
  · rcases hx with h|h|h|h <;> rw [h] <;> norm_num [dom,g,U,pt] <;> exact Option.some_ne_none _
  · simp [dom,(outside hx).2,hx]

theorem imageF : f.func '' U = U := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    rwa [f_on hz]
  · exact fun hx => ⟨_,hx,f_on hx⟩

theorem imageG : g.func '' U = U := by
  ext x
  norm_num [g,U,image_insert_eq,image_singleton,pt,or_comm,or_left_comm,or_assoc,eq_comm]

theorem countSmall {e : ENNReal} (he : 0 < e) (h1 : e ≤ 1) : cover usual e U = 4 := by
  rw [← carrier,fullSeparated S (readMetric id) he,size]
  · norm_num
  intro x hx y hy hd
  have h := hd.trans_le h1
  have hx' : x ∈ U := carrier ▸ hx
  have hy' : y ∈ U := carrier ▸ hy
  rcases hx' with h₁|h₁|h₁|h₁ <;> rcases hy' with h₂|h₂|h₂|h₂ <;> rw [h₁,h₂] at h ⊢ <;> norm_num [usual] at *

theorem countMiddle {e : ENNReal} (h1 : 1 < e) (h2 : e ≤ 2) : cover usual e U = 2 := by
  classical
  have hp := zero_lt_one.trans h1
  apply le_antisymm
  · let C : Finset Line := {pt 1,pt 2}
    have hn : Net usual e U C := by
      constructor
      · simp [C,U,Set.subset_def]
      · norm_num [U,C,usual,Finset.mem_insert,Finset.mem_singleton,h1,hp]
    exact (netUpper hn).trans (by norm_num [C,pt])
  · have h0 : pt 0 ∈ U := Or.inl rfl
    have h3 : pt 3 ∈ U := by simp [U]
    apply twoLower ⟨_,h0⟩
    intro c hc
    rcases hc with h|h|h|h <;> rw [h]
    · exact ⟨_,h3,h2.trans (by norm_num [usual])⟩
    · exact ⟨_,h3,h2.trans (by norm_num [usual])⟩
    · exact ⟨_,h0,h2.trans (by norm_num [usual])⟩
    · exact ⟨_,h0,h2.trans (by norm_num [usual])⟩

theorem countLarge {e : ENNReal} (he : 2 < e) : cover usual e U = 1 := by
  have h1 : pt 1 ∈ U := by simp [U]
  apply coverOne ⟨_,h1⟩ h1
  intro x hx
  apply lt_of_le_of_lt _ he
  rcases hx with h|h|h|h <;> rw [h] <;> norm_num [usual]

theorem counts {e : ENNReal} (he : positiveFinite e) :
    cover usual e U = if e ≤ 1 then 4 else if e ≤ 2 then 2 else 1 := by
  split_ifs with h k
  · exact countSmall he.1 h
  · exact countMiddle (lt_of_not_ge h) k
  · exact countLarge (lt_of_not_ge k)

theorem midpoint :
    pt (3/2) ∉ U ∧ U ⊆ ball usual (pt (3/2)) (7/4) ∧
      ∀ C : Finset Line, Net usual (7/4) U C → pt (3/2) ∉ C := by
  have hn : pt (3/2) ∉ U := by norm_num [U,pt]
  refine ⟨hn,?_,fun _ h hx => hn (h.1 hx)⟩
  intro x hx
  rcases hx with h|h|h|h <;> rw [h] <;>
    simp only [ball,mem_setOf_eq,usual,read_points,id_eq] <;>
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1 <;>
    norm_num [ENNReal.toReal_div,ENNReal.toReal_ofReal (abs_nonneg _)]

theorem sameCounts {e : ENNReal} (he : positiveFinite e) :
    cover usual e (f.func '' U) = cover usual e U ∧ cover usual e (g.func '' U) = cover usual e U ∧
    (∃ hf : good usual usual f U e, delta usual usual f U e hf = 0) ∧
    (∃ hg : good usual usual g U e, delta usual usual g U e hg = 0) := by
  have hfin : U.Finite := carrier ▸ S.finite_toSet
  have hn := finiteCover (readMetric id) hfin he.1
  have hu : U.Nonempty := ⟨_,Or.inl rfl⟩
  obtain ⟨v,hv⟩ := finiteLog hu hn
  exact ⟨congrArg _ imageF,congrArg _ imageG,⟨Or.inl hn,by rw [delta,imageF,hv,← EReal.coe_sub]; simp⟩,
    ⟨Or.inl hn,by rw [delta,imageG,hv,← EReal.coe_sub]; simp⟩⟩

def scalar (F : Op (none : Line)) (L : ENNReal) := HasScalarLipBound (fun _ : Unit => usual) F U () () L

theorem optimalF : IsLeast {L | scalar f L} 1 := by
  constructor
  · refine ⟨domain.1.ge,fun x hx y hy => ?_⟩
    simp [f_on hx,f_on hy]
  · intro L h
    have h0 : pt 0 ∈ U := Or.inl rfl
    have h1 : pt 1 ∈ U := by simp [U]
    simpa [f_on h0,f_on h1,usual] using h.2 _ h0 _ h1

theorem optimalG : IsLeast {L | scalar g L} 3 := by
  constructor
  · refine ⟨domain.2.ge,?_⟩
    norm_num [U,g,usual,pt,readDist,extend,edist_dist,Real.dist_eq]
  · intro L h
    have h0 : pt 0 ∈ U := Or.inl rfl
    have h1 : pt 1 ∈ U := by simp [U]
    simpa [g,usual,pt,readDist,extend,edist_dist,Real.dist_eq] using h.2 _ h0 _ h1

theorem numericalBounds :
    (cover usual (7/4) (f.func '' U) ≤ cover usual ((7/4)/1) U) ∧
    (cover usual (7/4) (g.func '' U) ≤ cover usual ((7/4)/3) U) ∧
    cover usual (7/4) (f.func '' U) = 2 ∧ cover usual ((7/4)/1) U = 2 ∧
    cover usual (7/4) (g.func '' U) = 2 ∧ cover usual ((7/4)/3) U = 4 := by
  have hf := lipCover (e := 7/4) (p := usual) (q := usual) (f := f) (L := 1)
    (by constructor <;> norm_num) optimalF.1.2
  have hg := lipCover (e := 7/4) (p := usual) (q := usual) (f := g) (L := 3)
    (by constructor <;> norm_num) optimalG.1.2
  have lo : (1:ENNReal) < 7/4 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_div]
  have hi : (7/4:ENNReal) ≤ 2 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_div]
  have small : ((7/4)/3:ENNReal) ≤ 1 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_div]
  refine ⟨hf,hg,?_,?_,?_,?_⟩
  · rw [imageF,countMiddle lo hi]
  · simpa using countMiddle lo hi
  · rw [imageG,countMiddle lo hi]
  · exact countSmall (by norm_num [ENNReal.div_pos_iff]) small

end
end MG.Rearrange
```

```lean filename=Ch3/Scale.lean
import Ch3.Radius

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {X I : Type} {b : X} {f : Op b} {U A B : Set X} {p q : Dist X}
def diam (p : Dist X) (A : Set X) := ⨆ x : A, ⨆ y : A, p x y
theorem le_diam {x y : X} (hx : x ∈ A) (hy : y ∈ A) : p x y ≤ diam p A :=
  le_iSup_of_le (⟨x,hx⟩ : A) (le_iSup_of_le (⟨y,hy⟩ : A) le_rfl)
theorem diam_le {t : ENNReal} (h : ∀ x ∈ A, ∀ y ∈ A, p x y ≤ t) : diam p A ≤ t :=
  iSup_le fun x => iSup_le fun y => h _ x.2 _ y.2

abbrev Region (X : Type) := {A : Set X // A.Nonempty}
structure Scale (X I : Type) where
  value : I → Region X → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → value i A ≤ value i B

def diamScale (d : I → Dist X) : Scale X I :=
  ⟨fun i A => diam (d i) A,fun _ _ _ h => diam_le fun _ hx _ hy => le_diam (h hx) (h hy)⟩

def bits (a n ts tn : ENNReal) : Bool × Bool := (decide (a < ts), decide (tn ≤ n))
def channel (σ : Scale X I) (d : I → Dist X) (f : Op b) (A : Region X)
    (ts tn : ENNReal) (ij : I × I) := bits (σ.value ij.1 A) (matrix d f A.val ij.2 ij.1) ts tn

theorem fourTypes (a n ts tn : ENNReal) :
    ∃! z : Bool × Bool,
      (z = (true,true) ∧ a < ts ∧ tn ≤ n) ∨ (z = (true,false) ∧ a < ts ∧ n < tn) ∨
      (z = (false,true) ∧ ts ≤ a ∧ tn ≤ n) ∨ (z = (false,false) ∧ ts ≤ a ∧ n < tn) := by
  refine ⟨bits a n ts tn, ?_, ?_⟩
  all_goals by_cases h : a < ts <;> by_cases k : tn ≤ n <;>
    simp_all [bits, not_lt, not_le, not_lt_of_ge, not_le_of_gt]

theorem scaleChannels (σ : Scale X I) (d : I → Dist X) (f : Op b) (A : Region X)
    {s s' t : ENNReal} (hs : s ≤ s') :
    {ij | (channel σ d f A s t ij).1 = true} ⊆ {ij | (channel σ d f A s' t ij).1 = true} := by
  intro ij
  simp only [mem_setOf_eq,channel,bits,decide_eq_true_eq]
  exact fun h => h.trans_le hs

theorem radiusChannels (σ : Scale X I) (d : I → Dist X) (f : Op b) (A : Region X)
    {s t t' : ENNReal} (ht : t ≤ t') :
    {ij | (channel σ d f A s t' ij).2 = true} ⊆ {ij | (channel σ d f A s t ij).2 = true} := by
  intro ij
  simp only [mem_setOf_eq,channel,bits,decide_eq_true_eq]
  exact fun h => ht.trans h

theorem scaleRestrict (σ : Scale X I) (i : I) (A B : Region X) (h : B.val ⊆ A.val) (ts : ENNReal) :
    σ.value i B ≤ σ.value i A ∧ (σ.value i A < ts → σ.value i B < ts) :=
  ⟨σ.mono i B A h,fun ht => (σ.mono i B A h).trans_lt ht⟩

theorem smallDomain {ts tn : ENNReal} (hs : diam p A < ts) (ht : ts ≤ tn) :
    tn ≤ uniform p q f A A ↔ Const q f A :=
  ⟨fun hr _ hx _ hy => cutUniform hx hy ((le_diam hx hy).trans_lt (hs.trans_le (ht.trans hr))),
    fun hc => (constRadii p hc).2 ▸ le_top⟩

end
end MG
```

```lean filename=Ch3/Step.lean
import Ch3.RealTools

namespace MG.Step
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
def W : Set ℝ := Ico (-1) 0 ∪ Ioc 0 1
def U := realSet W
def v (x : ℝ) : ℝ := if x < 0 then 0 else 1
def f := liftOp v
theorem domain : U.Nonempty ∧ U ⊆ dom f :=
  ⟨realNonempty ⟨1,Or.inr ⟨zero_lt_one,le_rfl⟩⟩,realDom v W⟩

theorem across {y R : ℝ} (hy : y ∈ W) (hR : |y| < R) :
    ∃ x ∈ W, |x-y| < R ∧ v x ≠ v y := by
  let a := min 1 ((R - |y|)/2)
  have hp : 0 < a := lt_min zero_lt_one (by linarith)
  have h1 : a ≤ 1 := min_le_left _ _
  have h2 : a ≤ (R - |y|)/2 := min_le_right _ _
  rcases hy with hy | hy
  · have hy' := hy.2
    rw [abs_of_neg hy'] at hR h2
    refine ⟨a,Or.inr ⟨hp,h1⟩,?_,by simp [v,hp.not_gt,hy']⟩
    rw [abs_of_pos (by linarith : 0 < a-y)]
    linarith
  · have hy' := hy.1
    rw [abs_of_pos hy'] at hR h2
    refine ⟨-a,Or.inl ⟨by linarith,by linarith⟩,?_,by simp [v,hp,hy'.not_gt]⟩
    rw [abs_of_neg (by linarith : -a-y < 0)]
    linarith

theorem step_eq_zero {x y : ℝ} : usual (f.func (pt x)) (f.func (pt y)) = 0 ↔ v x = v y := by
  change edist (v x) (v y) = 0 ↔ _
  exact edist_eq_zero

theorem legal_iff {y : ℝ} (hy : y ∈ W) {r : ENNReal} :
    r ∈ legal usual usual f U (pt y) ↔ 0 < r ∧ r ≤ ENNReal.ofReal |y| := by
  constructor
  · intro hr
    refine ⟨hr.1.1,le_of_not_gt ?_⟩
    intro h
    have hR := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hr.1.2.ne).1 h
    obtain ⟨x,hx,hd,hv⟩ := across hy hR
    apply hv
    apply step_eq_zero.1 (hr.2 _ (mem_realSet.2 hx) ?_)
    simpa only [usual,read_points,id_eq,ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.1.2.ne] using hd
  · rintro ⟨hp,hl⟩
    refine ⟨⟨hp,hl.trans_lt ENNReal.ofReal_lt_top⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩ hd
    have hy0 : y ≠ 0 := by rcases hy with h|h; exact h.2.ne; exact h.1.ne'
    have hxy : |x-y| < |y| :=
      (ENNReal.ofReal_lt_ofReal_iff (abs_pos.2 hy0)).1 (by simpa [usual] using hd.trans_le hl)
    apply step_eq_zero.2
    rw [abs_lt] at hxy
    by_cases hn : y < 0
    · rw [abs_of_neg hn] at hxy
      have hx' : x < 0 := by linarith
      simp [v,hn,hx']
    · rw [abs_of_nonneg (le_of_not_gt hn)] at hxy
      have hx' : 0 < x := by linarith
      simp [v,hn,hx'.not_gt]

theorem pointValue {y : ℝ} (hy : y ∈ W) :
    radius usual usual f U (pt y) = ENNReal.ofReal |y| ∧ 0 < ENNReal.ofReal |y| := by
  have hn : y ≠ 0 := by rcases hy with h|h; exact h.2.ne; exact h.1.ne'
  have hp := ENNReal.ofReal_pos.2 (abs_pos.2 hn)
  exact ⟨le_antisymm (sSup_le fun _ hr => ((legal_iff hy).1 hr).2) (le_sSup ((legal_iff hy).2 ⟨hp,le_rfl⟩)),hp⟩

theorem uniformZero : uniform usual usual f U U = 0 := by
  apply smallZero
  intro t ht
  let a := min 1 t
  have hp : 0 < a := lt_min zero_lt_one ht
  have ha : a ∈ W := Or.inr ⟨hp,min_le_left _ _⟩
  calc
    _ ≤ radius usual usual f U (pt a) := uniform_le (mem_realSet.2 ha)
    _ = ENNReal.ofReal |a| := (pointValue ha).1
    _ ≤ _ := by rw [abs_of_pos hp]; exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem noUniformCover {τ : ENNReal} (ht : positiveFinite τ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < τ ∧
      ({pt (-a),pt a} : Set Line) ⊆ U ∧
      cover usual τ {pt (-a),pt a} = 1 ∧ cover usual (1/2) (f.func '' {pt (-a),pt a}) = 2 := by
  let a := min 1 (τ.toReal/4)
  have hτ := ENNReal.toReal_pos ht.1.ne' ht.2.ne
  have ha : 0 < a := lt_min zero_lt_one (by linarith)
  have h1 : a ≤ 1 := min_le_left _ _
  have h2 : a ≤ τ.toReal/4 := min_le_right _ _
  have hτ' : ENNReal.ofReal (2*a) < τ := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ht.2.ne).2 (by linarith)
  refine ⟨a,ha,h1,hτ',?_,?_,?_⟩
  · intro x hx
    rcases hx with h|h <;> rw [h] <;> apply mem_realSet.2
    · exact Or.inl ⟨by linarith,by linarith⟩
    · exact Or.inr ⟨ha,h1⟩
  · rw [pairCover (readMetric id) _ _ ht.1,if_pos]
    simpa [usual,abs_of_neg (by linarith : -a-a < 0),two_mul] using hτ'
  · rw [Set.image_insert_eq,Set.image_singleton,pairCover (readMetric id) _ _ (by norm_num),if_neg]
    simp [f,v,ha,ha.not_gt]

end
end MG.Step
```

```toml filename=lakefile.toml
name = "MG_C003"
version = "0.1.1"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "Main"
globs = [
  "Main",
  "Ch3.+",
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.metric_entropy",
  "formal_oet.vol_01.ch_01_foundations.operator_space",
  "formal_oet.vol_01.ch_02_operator_bounds.lip_matrix",
  "formal_oet.vol_01.ch_02_operator_bounds.decoupling",
  "formal_oet.vol_01.ch_02_operator_bounds.single_channel"
]
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```json filename=lake-manifest.json
{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "url": "https://github.com/leanprover-community/plausible",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "83e90935a17ca19ebe4b7893c7f7066e266f50d3",
      "name": "plausible",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/LeanSearchClient",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "c5d5b8fe6e5158def25cd28eb94e4141ad97c843",
      "name": "LeanSearchClient",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/import-graph",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "48d5698bc464786347c1b0d859b18f938420f060",
      "name": "importGraph",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/ProofWidgets4",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "4dd0959c44d1af0462bd604d0f87c5781307d709",
      "name": "proofwidgets",
      "manifestFile": "lake-manifest.json",
      "inputRev": "v0.0.95+lean-v4.29.1",
      "inherited": true,
      "configFile": "lakefile.lean"
    },
    {
      "url": "https://github.com/leanprover-community/aesop",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "7152850e7b216a0d409701617721b6e469d34bf6",
      "name": "aesop",
      "manifestFile": "lake-manifest.json",
      "inputRev": "master",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/quote4",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "707efb56d0696634e9e965523a1bbe9ac6ce141d",
      "name": "Qq",
      "manifestFile": "lake-manifest.json",
      "inputRev": "master",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/batteries",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "756e3321fd3b02a85ffda19fef789916223e578c",
      "name": "batteries",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover/lean4-cli",
      "type": "git",
      "subDir": null,
      "scope": "leanprover",
      "rev": "7802da01beb530bf051ab657443f9cd9bc3e1a29",
      "name": "Cli",
      "manifestFile": "lake-manifest.json",
      "inputRev": "v4.29.0",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "name": "mathlib",
      "type": "git",
      "url": "https://github.com/leanprover-community/mathlib4",
      "rev": "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
      "inputRev": "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
      "inherited": false,
      "configFile": "lakefile.lean",
      "manifestFile": "lake-manifest.json",
      "scope": "",
      "subDir": null
    }
  ],
  "name": "MG_C003",
  "lakeDir": ".lake"
}
```

```python filename=build.py
"""Compile Main and its source imports using the supplied offline Lean environment."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CONFIG = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / "environment.json"
BACKGROUND = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else CONFIG.parent
OUTPUT = ROOT / ".build" / "lean"
LEAN_REV = "f72c35b3f637c8c6571d353742168ab66cc22c00"
MATHLIB_REV = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

def main():
    config = json.loads(CONFIG.read_text())
    lean = config["compiler"]
    version = subprocess.check_output([lean, "--version"], text=True)
    if "version 4.29.1," not in version or LEAN_REV not in version:
        raise ValueError(version)
    packages = config["public_packages"]
    mathlib = next(package for package in packages if package["name"] == "mathlib")
    if mathlib["revision"] != MATHLIB_REV:
        raise ValueError(mathlib["revision"])
    paths = [str(OUTPUT), *(package["olean_root"] for package in packages)]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))
    done = set()

    def build(module):
        if module in done:
            return
        relative = Path(*module.split(".")).with_suffix(".lean")
        root = BACKGROUND if module.startswith("formal_oet.") else ROOT
        source = (root / relative).read_text()
        for dep in re.findall(r"^import ([\w.]+)$", source, re.MULTILINE):
            if dep.startswith(("Ch3.", "formal_oet.")):
                build(dep)
        output = (OUTPUT / relative).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        print(module, flush=True)
        subprocess.run([lean, "-o", str(output), str(relative)], cwd=root, env=env, check=True)
        done.add(module)

    build("Main")

if __name__ == "__main__":
    main()
```

```json filename=alignment.json
{
  "case_id": "MG-C003",
  "version": "0.1.1",
  "items": [
    {
      "id": "CH03-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.Const"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.Ident"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.Active"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.constSet"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.identSet"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.activeSet"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.componentSets"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.partition"
        }
      ],
      "representation": "三个谓词分别检验像点两两零距、排除常值后的逐点零距、以及前两类的补集。取满足谓词的指标集得到正文的三个集合。partition 证明穷尽与两两互斥，取 U = dom f 即全域分划。",
      "dependencies": []
    },
    {
      "id": "CH03-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiber"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.subdist"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.subzero"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.subdistMaximum"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.blocks"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.fiberEmpty"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberEnds"
        }
      ],
      "representation": "fiber p f U y 对任意目标 y 给出 U 中输出到 y 的 p 距离为零的输入。取 p 为子族距离时，上确界是有限非空子族的最大值，零值等价于逐分量为零。单指标恢复原距离，目标与整个像集正分离时纤维为空。",
      "dependencies": []
    },
    {
      "id": "CH03-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.atImage"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.ontoImage"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.pairs"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.eqRel"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.zeroRel"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.relationFiber"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.imageSetoid"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.ImageQuot"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.atClass"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.classEq"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.finer"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.finerFibers"
        }
      ],
      "representation": "pairs 在原空间的点对上同时记录两个端点属于 U。点值相等与全分量零距给出两种关系。像子类型上的 Setoid 由冻结等价关系限制得到，atClass 取实际像点的商类。finer 是零距关系包含，亦等价于同一基点所定的全纤维包含。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.legal"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.radius"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.legalBall"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.radiusEmpty"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.radiusSingle"
        }
      ],
      "representation": "legal 中的 r 严格正且有限。legalBall 将逐点条件与输入开球交 U 包含于像目标的计算纤维对应。radius 是此集合的 ENNReal 上确界，空集给 0。输入、输出可任取扩展伪度量，单输出子族与原分量给相同半径。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.uniform"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.matrix"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.radiusNotation"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.uniform_le"
        }
      ],
      "representation": "uniform p q f A U 在基点子类型 A 上取下确界，每个点态半径始终在 U 上评估。矩阵取 A = U，matrix d f U j i 以 j 为输出行、i 为输入列。代入 dom f 得全域记号。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.Region"
        },
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.Scale"
        },
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.diam"
        },
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.diamScale"
        },
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.bits"
        },
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.channel"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.channelTable"
        }
      ],
      "representation": "尺度的定义域是非空集合子类型，单调条件使用集合包含。diam 在两个内部端点上取上确界，diamScale 证明该族单调。channel 的 Bool 对按输入 i、输出 j 读取严格尺度阈值和非严格半径阈值，channelTable 给出有限正阈值下的四个等价式。",
      "dependencies": [
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.cover"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.entropy"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.Net"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.netBalls"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.boundedAtAll"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.boundedNets"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number_attained"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number_eq_top_iff"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number_empty"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.log2_ereal"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy_nonneg"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy_empty"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy_eq_metric_entropy"
        }
      ],
      "representation": "中心用 Finset 表示，netBalls 验证中心内部性及开球并覆盖。冻结下确界在有有限网时取到最小基数，无有限网时为无穷，空集为零。熵采用冻结的扩展二进对数，子族熵用对应复合伪度量。全有界等价于每个有限正精度都存在有限内网。",
      "dependencies": []
    },
    {
      "id": "CH03-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.good"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.delta"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.mapDelta"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.mapDelta_formula"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.singletonDelta"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.deltaBranches"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.deltaSigns"
        }
      ],
      "representation": "mapDelta 指定非空域、域包含、两端非空子族和有限正精度。good 正好是至少一端覆盖数有限，作为差值的定义参数。已证明子族熵差公式、单分量换写、单侧无穷的符号、两端有限时的实数值，以及正负零与两端熵比较的对应。",
      "dependencies": [
        "CH03-D02",
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P01-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.zeroRow"
        }
      ],
      "representation": "对任意常值输出指标和 U 内两点，证明输出距离不超过零系数有限和，并证明该和等于零。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.zeroEntry"
        }
      ],
      "representation": "在所给 co-Lip 矩阵上任取输入 k，取出 U 内输入距离严格为正的见证，以输出常值的零距推出 K k i = 0。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.identDist"
        }
      ],
      "representation": "Ident 的逐点零距分别替换两个端点，由对称性和双向三角不等式得到像距与输入距相等。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P02-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.compActive"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.compSets"
        }
      ],
      "representation": "乘法 g*f 按先 f 后 g 复合。在 U 属于复合定义域的前提下，有效指标集包含于内步在 U、外步在 f(U) 的有效指标集之并。",
      "dependencies": [
        "CH03-D01",
        "CH03-P01-03",
        "CH03-P02-03",
        "CH03-P04-01"
      ]
    },
    {
      "id": "CH03-P02-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.chain"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.stepActive"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.chain_order"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.chain_domain"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.emptyActive"
        },
        {
          "file": "Ch3/Components.lean",
          "name": "MG.chainActive"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.prefixOp"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.prefixDomains"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.finiteActive"
        }
      ],
      "representation": "列表按实际施用顺序递推，其复合等于冻结 OperatorChain 对反序列表的值。另以 k 从 0 起表示第 k+1 步，证明前缀像域的递推和每一步的定义域合法性，并对任意长度证明指标并集包含。零步为恒等且无有效分量。",
      "dependencies": [
        "CH03-D01",
        "CH03-P02-01"
      ]
    },
    {
      "id": "CH03-P02-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.compIdent"
        }
      ],
      "representation": "两步在各自实际域都为恒等分量时，传递逐点零距；若复合常值，则外步的保距等式推出内步常值，与 Ident 的排除项矛盾。",
      "dependencies": [
        "CH03-D01",
        "CH03-P01-03"
      ]
    },
    {
      "id": "CH03-P03-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.d"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.f"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.U"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.model"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.domain"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.image_eq"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.components"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Swap.classifications"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.strictInclusions"
        }
      ],
      "representation": "Option Bool 的两个 some 点为非吸收点，距离为 1，none 隔离。布尔取反保持 U 且自复合固定两点。单指标全集与空集的计算给出两步有效、复合恒等，并分别证明有效集合和恒等集合的严格包含。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.outerConst"
        }
      ],
      "representation": "任取 U 内两点，将其 f 像作为实际像域内的两点代入外侧常值条件，得到 g*f 在 U 上常值。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.P"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.cardinality"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.key"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.d"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.first"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.lastOp"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.U"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.model"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Seven.exampleData"
        }
      ],
      "representation": "六个具名点加 none 恰有七点。第一个分量仅合并 p、q，另一分量离散。两个部分算子分别作用于 a、b 和 p、q，其余输入返回 none。证明复合域包含 U、内像为指定二点、内步常值、另一输入读数及复合输出读数都是 1，故复合非常值。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P05-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.diagConst"
        }
      ],
      "representation": "在 f(U) 上使用合法 Lip 矩阵的指定输出行，将和式化成对角系数乘内侧零距。ENNReal 的乘零律也适用于无穷系数。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P06-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberTarget"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.subfamilyTarget"
        }
      ],
      "representation": "对任意目标，以子族伪度量代入 fiberTarget。目标间零距给到两个目标的距离相同，故受限纤维相等。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberCover"
        }
      ],
      "representation": "blocks 是对实际像目标取纤维的集合像。每块以目标的一个原像为非空见证，各块的 sUnion 等于 U。取非空子族的已证实伪度量即给原结论。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberPartition"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.blockPartition"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.subfamilyPartition"
        }
      ],
      "representation": "两块若有共同输入，其目标必零距，由目标不变性得两块相同。集合像自动去重，已证明各块非空、覆盖 U 及不同块两两不交。",
      "dependencies": [
        "CH03-D02",
        "CH03-P06-01",
        "CH03-P06-02"
      ]
    },
    {
      "id": "CH03-P06-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberInter"
        }
      ],
      "representation": "对非空 J 给出以 j∈J 为指标的集合交等式。正向用逐分量零距，反向从非空性还原 x∈U。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberAnti"
        }
      ],
      "representation": "任意 J⊆K，将 K 上的全称零距条件限制到 J，得到相同目标与受限域上的反向纤维包含。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-06",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.fiberEnds"
        }
      ],
      "representation": "单元素子族精确恢复单分量的集合表达式，全指标子族的纤维包含于每个单分量纤维。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-07",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.identFiber"
        }
      ],
      "representation": "对任意目标 y，利用 x 与 f(x) 的分量零距替换距离的第一端点，得到 U 内的输入零距类。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-08",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Components.lean",
          "name": "MG.constFiber"
        }
      ],
      "representation": "从像目标 y₀ 的原像证明纤维等于 U。对所有与 y₀ 正距离的目标，纤维中的输入会通过零距传递导致矛盾，故纤维为空。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P07-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.transforms"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.pointFactor"
        }
      ],
      "representation": "transforms 的映射真实定义在 f(U) 子类型上，且在每个 x∈U 满足规定赋值。pointFactor 的正向用函数性得到点值关系包含。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.atImage"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.ontoImage"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.descend"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.pointFactor"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.emptyTransform"
        }
      ],
      "representation": "反向以到像集的满射为每个像点选代表元，以关系包含证明赋值公式。选择仅对实际像点进行，因此也构造了 U 为空时的空域函数。",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-01"
      ]
    },
    {
      "id": "CH03-P07-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.bothPoint"
        }
      ],
      "representation": "分别对两个方向的 transforms 应用单向判据，双包含正好等价于两个点值点对集相等。",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-01",
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P07-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.factorLip"
        }
      ],
      "representation": "在同一单分量距离上给定实际像映射 t 及其赋值、正有限 K 和有限非负 L。取两个像点的 U 内代表元，利用 K 的可逆性得到 t 的 L/K 上界，输入或像距离可为无穷。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P08-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.atClass"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.ontoClass"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.classEq"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.quotTransforms"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.quotFactor"
        }
      ],
      "representation": "把 U 映满实际像集的零距商，商类相等当且仅当像点全分量零距。quotFactor 以此满射实际构造商到商的函数并证明规定公式，反向从该公式恢复零距关系包含。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P08-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.bothQuot"
        }
      ],
      "representation": "对两个方向应用商因子化等价，双向商变换的存在恰好等价于相同 U 上零距点对集相等。",
      "dependencies": [
        "CH03-D03",
        "CH03-P08-01"
      ]
    },
    {
      "id": "CH03-P08-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.separatesOn"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.sepRel"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.separatedFactors"
        }
      ],
      "representation": "分离性仅在 f(U)、g(U) 内分别量化。先证明每侧的相等点对集与零距点对集相等，再证明单向及双向的点值、商值变换判据等价。",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-01",
        "CH03-P07-02",
        "CH03-P07-03",
        "CH03-P08-01",
        "CH03-P08-02"
      ]
    },
    {
      "id": "CH03-P09-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.finerRefl"
        },
        {
          "file": "Ch3/Factor.lean",
          "name": "MG.finerTrans"
        }
      ],
      "representation": "固定 d、U，以集合包含的自反性及传递性证明零距纤维预序的两条性质。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.finiteFiner"
        }
      ],
      "representation": "F 以 Fin (n+1) 指定所有层，Fin n 指定相邻步。公共域 U 和每一步关系包含推出任意 a≤c 两层的包含。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.strictFiniteFiner"
        }
      ],
      "representation": "从指定严格步取出属于后层而不属于前层的实际点对 z，用链上的两次包含证明 z 属于末层与首层之差，并给出端点严格包含。",
      "dependencies": [
        "CH03-D03",
        "CH03-P09-02"
      ]
    },
    {
      "id": "CH03-P10-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Models.lean",
          "name": "MG.extend"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.extended"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readDist"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readMetric"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.read_points"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.W"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.U"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.v"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.f"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.domain"
        }
      ],
      "representation": "Option ℝ 的 none 为吸收元，some 上使用通常实距，两类之间距离无穷。阶跃在负半轴取 0，在非负半轴取 1。W 精确取两个半开区间，已证明评估域非空且包含于算子定义域。",
      "dependencies": []
    },
    {
      "id": "CH03-P10-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.across"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.legal_iff"
        },
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.pointValue"
        }
      ],
      "representation": "对固定域中的每个实基点，越过绝对值界的半径内显式选择异号输入。合法半径恰满足 0<r≤ofReal(abs y)，取上确界等于该端点并严格为正。",
      "dependencies": [
        "CH03-D04",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P10-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.uniformZero"
        }
      ],
      "representation": "在同一个 Step.U 中，对每个 t>0 取基点 min(1,t)，以其点态半径控制统一半径，推出后者等于零。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P10-01",
        "CH03-P10-02"
      ]
    },
    {
      "id": "CH03-P11-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.constSub"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.constSubFiber"
        }
      ],
      "representation": "J 的每个分量在 U 上常值，则任一 U 内基点的像目标满足整个子族同时零距，其纤维等于 U。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P11-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.constRadii"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.subfamilyConstant"
        }
      ],
      "representation": "对任意输入分量，常值子族对全部基点的所有有限正半径满足零化条件，故点态上确界与 U 上下确界均为正无穷。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-D04",
        "CH03-D05",
        "CH03-P11-01",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P11-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.channels"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.channelsMetric"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Swap.inputAndOutput"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.Swap.infiniteInput"
        }
      ],
      "representation": "取两非吸收点、恒等算子，输入指标 false 的异点距离无穷。输出指标 j 遍历 Bool，同指标异点距无穷，异指标异点距 1。两种情况下每个点态半径与矩阵条目都是无穷，输出均非常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05",
        "CH03-P03-01",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P12-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.identBase"
        }
      ],
      "representation": "对 y∈U 的像目标，恒等分量的成对保距等式将输出零距纤维换成 U 内与 y 输入零距的点集。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P01-03"
      ]
    },
    {
      "id": "CH03-P12-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.identRadius"
        }
      ],
      "representation": "有限正 r₀ 的输入球交 U 若包含于输入零距类，则按像目标纤维等式成为合法半径，得到 r₀≤点态半径及 0<r₀。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-D04",
        "CH03-P12-01"
      ]
    },
    {
      "id": "CH03-P13-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.radiusInf"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.finiteMin"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.pointMinimum"
        }
      ],
      "representation": "先证子族点态半径等于以成员子类型为指标的下确界。对有限非空 J 进一步证明该值在条目集合中取得，给出 IsLeast。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P13-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.uniformInf"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.matrixMinimum"
        }
      ],
      "representation": "对 U 内基点取下确界，交换基点和输出指标的两层下确界。有限非空情形的 IsLeast 精确标出第 i 列、行属于 J 的矩阵条目最小值。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04",
        "CH03-D05",
        "CH03-P13-01"
      ]
    },
    {
      "id": "CH03-P13-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.uniformAnti"
        }
      ],
      "representation": "J⊆K 时对 K 的条目取下确界不大于对 J 取下确界，因此较大输出子族的统一半径较小或相等。",
      "dependencies": [
        "CH03-D02",
        "CH03-D05",
        "CH03-P13-02"
      ]
    },
    {
      "id": "CH03-P14-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.cutFiber"
        }
      ],
      "representation": "受限纤维给出输入 x 的像到基点 y 的像的距离为零，对称性给出正文方向的输出零距。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P14-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.extractRadius"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.cutPoint"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.cutSymm"
        }
      ],
      "representation": "严格低于点态上确界时，提取一个比给定距离大的合法有限正半径。用球成员关系得到零距，cutSymm 同时处理输入距离和输出距离的方向。",
      "dependencies": [
        "CH03-D04",
        "CH03-P14-01"
      ]
    },
    {
      "id": "CH03-P14-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.cutComp"
        }
      ],
      "representation": "以两个上游合法输入及其各自的下游域成员证明为前提，将下游纤维判据代入复合，得到规定方向的复合输出零距。",
      "dependencies": [
        "CH03-D02",
        "CH03-P14-01"
      ]
    },
    {
      "id": "CH03-P15-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.compZeroRadius"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.compositeBounds"
        }
      ],
      "representation": "复合域的合法性推出两个单步域合法。若外步在实际内像域将 l 零距送到 j 零距，则将任意低于内步统一半径的 i 距离传播至复合，取得矩阵条目下界。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P15-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.compLipRadius"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.pullbackEndpoints"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.compositeBounds"
        }
      ],
      "representation": "在 U 上有正有限 L 的 i 到 l 单通道界时，将实际像域外步半径除以 L 拉回。严格不等式在扩展实数上成立，另证下游值为零时商为零、为无穷时复合半径为无穷。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P16-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.fourTypes"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.channelTable"
        }
      ],
      "representation": "证明恰有一对布尔值匹配四种互补的比较；channelTable 再把该四种情况与同一合法域上实际通道的布尔值逐项对应。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.scaleChannels"
        }
      ],
      "representation": "仅增大输入尺度阈值 s，比较同一算子、域、尺度族及第二阈值时，原先第一位为真的全部通道仍为真。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.radiusChannels"
        }
      ],
      "representation": "仅增大零化阈值 t，比较同一域、算子、尺度族及第一阈值时，新第二位为真的通道集合包含于原集合。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.scaleRestrict"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.restrictScaleRadius"
        }
      ],
      "representation": "对任意单调尺度和非空 B⊆A，证明尺度值不增，同时推出 A 严格低于阈值时 B 亦严格低于阈值。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.restrictRadius"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.restrictScaleRadius"
        }
      ],
      "representation": "固定 B 内基点，A 上所有满足距离条件的点已有输出零距；将量词限制到 B，证明评估域缩小时点态半径不减。",
      "dependencies": [
        "CH03-D04",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P17-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.restrictUniform"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.restrictScaleRadius"
        }
      ],
      "representation": "同时将基点与受测点从 A 限制到 B，统一半径的逐对判据给出 A 上条目≤B 上条目。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P17-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/RealTools.lean",
          "name": "MG.realDiam"
        },
        {
          "file": "Ch3/RealTools.lean",
          "name": "MG.pairDiam"
        },
        {
          "file": "Ch3/RealTools.lean",
          "name": "MG.scaleCounter"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readMetric"
        }
      ],
      "representation": "在带吸收元实线的恒等算子定义域内取 A={0,1}、B={0}。由两端点的真实直径算得 1 与 0，对阈值 1/2 得到相反的尺度判断。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P18-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.uniform_le"
        },
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.cutUniform"
        }
      ],
      "representation": "任取 A 内两点，输入距离严格小于基点下确界，从而也小于相应点态半径，故输出零距。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P18-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.separation"
        }
      ],
      "representation": "在同一域内，若输出正距，则严格低于统一半径会导致输出为零。线序给出统一半径≤该输入距离。",
      "dependencies": [
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P18-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.separationWitness"
        }
      ],
      "representation": "对每个处于统一半径与有限正阈值之间的有限正 α，取得违反统一零距条件的输入点对。ε 取 1 与输出距离的较小者，始终有限且正，并涵盖输出距离为无穷的情形。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P19-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.thresholdBall"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.coverConstraint"
        }
      ],
      "representation": "当统一半径至少为阈值时，以 x∈A 为中心的严格阈值球交 A 全部属于以 f(x) 为目标的单分量纤维。",
      "dependencies": [
        "CH03-D02",
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.pushNet"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.pushCover"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.thresholdCover"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.coverConstraint"
        }
      ],
      "representation": "对任意 B⊆A，把每个输入内网的有限中心集映到 f(B)，得到任意正输出精度的内网且基数不增。对所有内网取下确界，同时涵盖空集和无有限输入内网。",
      "dependencies": [
        "CH03-D05",
        "CH03-D07",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.logStrict"
        },
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.entropyOrder"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.thresholdEntropy"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.coverConstraint"
        }
      ],
      "representation": "扩展二进对数在整个 ENNReal 上严格单调，包括 0 和无穷。因此覆盖数比较与熵比较等价，应用到非空 B 及其像。",
      "dependencies": [
        "CH03-D05",
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P20-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Step.lean",
          "name": "MG.Step.noUniformCover"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Step.pointwiseCoverFails"
        }
      ],
      "representation": "沿用同一阶跃算子和固定 U，对任意有限正 τ 显式取 a=min(1,τ.toReal/4)。证明 0<a≤1、2a<τ、两点集包含于 U，内部输入覆盖数为 1，像在 1/2 精度的内部覆盖数为 2。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-P10-01",
        "CH03-P10-02"
      ]
    },
    {
      "id": "CH03-P21-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Scale.lean",
          "name": "MG.smallDomain"
        }
      ],
      "representation": "在 diam(A)<τσ≤τN 下，逐对输入距离均受直径控制。阈值条件推出全体输出零距，反向由常值输出推出统一半径无穷。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P11-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P21-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.smallCover"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.constCover"
        }
      ],
      "representation": "在非空域的小直径和半径阈值条件下推出输出常值，以实际像点为内部中心给上界，非空性给下界，任意有限正精度的覆盖数等于 1。",
      "dependencies": [
        "CH03-D01",
        "CH03-D05",
        "CH03-D06",
        "CH03-D07",
        "CH03-P21-01"
      ]
    },
    {
      "id": "CH03-P22-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.finiteCover"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.finiteLog"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.finiteData"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.subfamilyData"
        }
      ],
      "representation": "对任意两个非空子族，取相应扩展伪度量。有限非空输入和像集均可由自身覆盖，覆盖数正且有限，两个熵各有实数值，且满足差值的良定条件。",
      "dependencies": [
        "CH03-D02",
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P23-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.constDelta"
        }
      ],
      "representation": "常值分量的非空像在任意正精度上覆盖数为 1，输出熵为 0。由输出端有限构造 good，差值等于输入熵，输入熵可无穷。",
      "dependencies": [
        "CH03-D01",
        "CH03-D07",
        "CH03-D08",
        "CH03-P21-02"
      ]
    },
    {
      "id": "CH03-P23-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.pushNet"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.pullNet"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.identCover"
        }
      ],
      "representation": "恒等分量保距。有限输入内网前推，反向为各输出中心选 U 中的代表元，两个方向中心基数不增，从而内覆盖数和熵相等。",
      "dependencies": [
        "CH03-D01",
        "CH03-D07",
        "CH03-P01-03"
      ]
    },
    {
      "id": "CH03-P23-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.identDelta"
        }
      ],
      "representation": "差值只对已给 good 的情形取值。由两端覆盖数相等推出输入端有限，在实数熵上相减得到零。",
      "dependencies": [
        "CH03-D01",
        "CH03-D07",
        "CH03-D08",
        "CH03-P23-02"
      ]
    },
    {
      "id": "CH03-P24-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.lipCenters"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.lipCover"
        }
      ],
      "representation": "任取 ε/L 精度的有限内部输入中心，用单通道界推出其像在 ε 精度严格覆盖实际像集。输出中心基数不增，取下确界即得覆盖数上界。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P24-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.divScale"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.lipDelta"
        }
      ],
      "representation": "正有限 L 保证 ε/L 仍正且有限。输入全有界与像覆盖数上界给出三个有限实数熵及 good，并证明差值≥输入 ε 熵减去输入 ε/L 熵。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P24-01"
      ]
    },
    {
      "id": "CH03-P25-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Correspondence.lean",
          "name": "MG.coCenters"
        },
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.coCover"
        }
      ],
      "representation": "对任意 ε 输出内网选内部原像，取 co-Lip 有限和中的指定正有限单项并除以该系数，得到 ε/K 的输入内网及基数界。覆盖数不等式也包括无有限输出内网。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P25-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Entropy.lean",
          "name": "MG.coDelta"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.coEntropyBound"
        }
      ],
      "representation": "输入全有界使两种输入精度的熵有限。由反向覆盖数界及减数的反单调性得规定的熵差上界；若输出覆盖数无穷，仍有 good 且差值为负无穷。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P25-01"
      ]
    },
    {
      "id": "CH03-P26-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readMetric"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.read_points"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.f"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.U"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.domain"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.firstStep"
        }
      ],
      "representation": "取绝对值读数诱导的扩展伪度量及保持 none 的仿射算子。对精确的 U={0,1} 验证域合法，两个输出为 −1、1，目标 φ(0) 的纤维等于 U，指标为常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P26-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.domain"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.secondStep"
        }
      ],
      "representation": "在同一 U 上，平方算子像的读数分别为 3、1。目标 φ²(0) 的纤维为 {0}，复合既非常值又不满足逐点零距，属于有效分量。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P26-01"
      ]
    },
    {
      "id": "CH03-P26-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Affine.sameValue"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Affine.commonFiber"
        }
      ],
      "representation": "任意算子若在 U 上取同一实数 c，平方后在两点均取 g(c)，对任意目标的纤维成员判断相同。证明 U 属于复合定义域当且仅当 g(c) 非吸收，若其为吸收元，U 与复合定义域不交。",
      "dependencies": [
        "CH03-D02",
        "CH03-P26-01"
      ]
    },
    {
      "id": "CH03-P27-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.pointGap"
        }
      ],
      "representation": "对正 co-Lip 条目允许取无穷，点态半径严格正时，(0,rN) 内的输入距离既由截断给出输出零距，又由 co-Lip 反射必须是零，故不可能出现。",
      "dependencies": [
        "CH03-D04",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P27-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Radius.lean",
          "name": "MG.uniformGap"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.gapDisjoint"
        }
      ],
      "representation": "对 U 内任意有序点对，距离若小于统一半径则由正 co-Lip 条目反射为零，否则至少等于统一半径。统一半径为正使两个分支不交。",
      "dependencies": [
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P28-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readMetric"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.f"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.U"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.domain"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.translated"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.partitionId"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.partitionShift"
        }
      ],
      "representation": "在绝对值读数空间，按实际输入列出去重纤维。恒等分划为 {−3}、{−2,2}、{0}，平移分划为 {−3}、{−2,0}、{2}。两个算子保持吸收元，并验证 U 在两定义域内。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P28-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.inputCount"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.outputCount"
        },
        {
          "file": "Ch3/Readout.lean",
          "name": "MG.Translation.entropyChange"
        }
      ],
      "representation": "在精度 3/2，输入内部中心 −2、0 可覆盖，又证明任一单中心均漏点，故覆盖数为 2。像用 −2 作内部中心即可覆盖，非空下界给 1。差值为 log₂2−log₂1=1。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P28-01"
      ]
    },
    {
      "id": "CH03-P29-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.f"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.domain"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Floor.fourDomains"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.channel_eq"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.firstInterval"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readMetric"
        }
      ],
      "representation": "在通常实距、取整算子、两个阈值均为 1 的设定中，[0,1/2] 非空且合法，直径 1/2，输出恒为 0，统一半径无穷。通道布尔值为 (1,1)。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P11-02"
      ]
    },
    {
      "id": "CH03-P29-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.crosses"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.jumpInterval"
        }
      ],
      "representation": "[9/10,11/10] 的直径为 1/5。在 1 的左侧可选任意近的异输出点，统一半径为 0，通道类型为 (1,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P18-02",
        "CH03-P29-01"
      ]
    },
    {
      "id": "CH03-P29-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.pairValue"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.pairType"
        }
      ],
      "representation": "在 {0,2} 上逐对检验严格小于 2 的输入距离只来自同一点，异输出点距离恰为 2 给反向界。直径与统一半径均为 2，类型为 (0,1)。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P14-02",
        "CH03-P18-02",
        "CH03-P29-01"
      ]
    },
    {
      "id": "CH03-P29-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.crosses"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.wholeInterval"
        }
      ],
      "representation": "[0,2] 的两端点给直径 2，跨越取整跳点 1 的点对给统一半径 0，类型为 (0,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P18-02",
        "CH03-P29-01"
      ]
    },
    {
      "id": "CH03-P29-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.counterexample"
        },
        {
          "file": "Ch3/Floor.lean",
          "name": "MG.Floor.pairValue"
        }
      ],
      "representation": "以 {0,2} 为非空合法域，统一半径 2 达到阈值 1，但 0 和 2 的取整输出正分离。正半径来自域中不同输入间距为 2。",
      "dependencies": [
        "CH03-D01",
        "CH03-P29-01",
        "CH03-P29-03"
      ]
    },
    {
      "id": "CH03-P30-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.S"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.U"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.carrier"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.size"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.countSmall"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.countMiddle"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.countLarge"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.counts"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.midpoint"
        },
        {
          "file": "Ch3/Models.lean",
          "name": "MG.readMetric"
        }
      ],
      "representation": "对四点集的所有有限正 ε，ε≤1 时需四中心，1<ε≤2 时恰需两中心，2<ε 时一中心即可。在 7/4 时，以 3/2 为中心的球覆盖点集，但 3/2 不在集合中，任何合法内网均不含它。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P30-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.f"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.g"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.outside"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Rearrange.table"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.domain"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.imageF"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.imageG"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.sameCounts"
        }
      ],
      "representation": "两个算子在 U 上按原表赋值，U 外均返回 none，定义域恰为 U。两像集均为 U，因此各有限正精度覆盖数相同；有限性保证两映射熵差均有定义且为零。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P30-01"
      ]
    },
    {
      "id": "CH03-P30-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.scalar"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.optimalF"
        },
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.optimalG"
        }
      ],
      "representation": "以冻结的单通道标量界为合法性谓词。证明 1 和 3 分别属于 f、g 的合法常数集，并用输入 0、1 证明任意合法常数至少达到相应值，以 IsLeast 表示最优性。",
      "dependencies": [
        "CH03-P30-01",
        "CH03-P30-02"
      ]
    },
    {
      "id": "CH03-P30-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch3/Rearrange.lean",
          "name": "MG.Rearrange.numericalBounds"
        },
        {
          "file": "Ch3/Chapter.lean",
          "name": "MG.Rearrange.scales"
        }
      ],
      "representation": "将最优常数 1、3 分别代入一般 Lip 覆盖上界。输出精度为 7/4，相应输入精度为 7/4 与 7/12。两实际像均需 2 中心，前一上界 2 取等，后一上界 4 为严格上界。",
      "dependencies": [
        "CH03-D07",
        "CH03-P24-01",
        "CH03-P30-01",
        "CH03-P30-02",
        "CH03-P30-03"
      ]
    }
  ]
}
```
