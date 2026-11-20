# MG-C003 v0.1.1 · 卷 1 第 3 章 Lean 答卷

92 项义务均已完成。Main.lean 导入全部目标模块。以下命名代码块是各交付文件的全文。

在题目冻结工作目录中解压项目并运行 `python3 build.py`，即可使用 environment.json 指定的编译器和本地依赖缓存重编译。构建产物写入 .lake/build/lib/lean。

数学原作出自 Zhe Li（Glen Li / glenzli，ORCID 0009-0006-6536-3453）的《The Operator Evolution Theory》卷 1。本答卷将指定章节与习题改写为 Lean 定义和证明。[原作](https://glenzli.com/books/oet/) · [冻结版本](https://doi.org/10.5281/zenodo.21457931) · [源代码仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

```lean filename=Main.lean
import Components
import Factors
import Radii
import Entropy
import Models
import RealExamples
import FiniteExamples
import Rearrangement
import Chapter
import Textbook
```

```lean filename=Components.lean
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_01_foundations.metric_entropy

/-! Formalization of Chapter 3 of The Operator Evolution Theory by Zhe Li
(Glen Li / glenzli), ORCID 0009-0006-6536-3453, https://glenzli.com/books/oet/,
https://gitlab.com/glenzli/oet-public, CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
The chapter statements and examples are reformulated in Lean. -/
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

abbrev D (X : Type) := X → X → ENNReal
abbrev Op (b : X) := Operator X b

def Const (p : D X) (f : X → X) (U : Set X) :=
  ∀ x ∈ U, ∀ y ∈ U, p (f x) (f y) = 0

def Ident (p : D X) (f : X → X) (U : Set X) :=
  ¬ Const p f U ∧ ∀ x ∈ U, p (f x) x = 0

def Active (p : D X) (f : X → X) (U : Set X) :=
  ¬ Const p f U ∧ ¬ Ident p f U

theorem partition {p : D X} {f : X → X} {U : Set X} :
    (Const p f U ∧ ¬ Ident p f U ∧ ¬ Active p f U) ∨
    (Ident p f U ∧ ¬ Const p f U ∧ ¬ Active p f U) ∨
    (Active p f U ∧ ¬ Const p f U ∧ ¬ Ident p f U) := by
  unfold Ident Active
  tauto

variable {d : I → D X} {p : D X} {f g : X → X} {U : Set X}
variable {x y z w : X}

theorem zero_left (h : ExtendedPseudoMetric X b p) (hz : p x y = 0) :
    p x z = p y z := by
  apply le_antisymm
  · simpa [hz] using h.triangle x y z
  · simpa [h.symm y x, hz] using h.triangle y x z

theorem zero_right (h : ExtendedPseudoMetric X b p) (hz : p x y = 0) :
    p z x = p z y := by rw [h.symm z x, h.symm z y, zero_left h hz]

theorem zero_row [Fintype I] {i : I} (hc : Const (d i) f U) (hx : x ∈ U) (hy : y ∈ U) :
    d i (f x) (f y) ≤ ∑ k, (0 : ENNReal) * d k x y := by simp [hc x hx y hy]

theorem zero_entry [Fintype I] {F : Op b} {k i : I} {K : I → I → ENNReal}
    (hc : Const (d i) F.func U) (hK : IsCoLipMatrix d F U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x,hx,y,hy,h⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d F U K k i x y hK hx hy (hc x hx y hy) h

theorem ident_dist (h : ExtendedPseudoMetric X b p) (hi : Ident p f U)
    (hx : x ∈ U) (hy : y ∈ U) : p (f x) (f y) = p x y :=
  (zero_left h (hi.2 x hx)).trans (zero_right h (hi.2 y hy))

theorem outer_const (hc : Const p g (f '' U)) : Const p (g ∘ f) U :=
  fun x hx y hy => hc _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩

theorem comp_ident (h : ExtendedPseudoMetric X b p) (h₁ : Ident p f U)
    (h₂ : Ident p g (f '' U)) : Ident p (g ∘ f) U := by
  constructor
  · intro hc
    apply h₁.1
    intro x hx y hy
    exact (ident_dist h h₂ (mem_image_of_mem f hx) (mem_image_of_mem f hy)).symm.trans (hc x hx y hy)
  · intro x hx
    exact (zero_left h (h₂.2 _ ⟨x,hx,rfl⟩)).trans (h₁.2 x hx)

theorem comp_active (h : ExtendedPseudoMetric X b p) (ha : Active p (g ∘ f) U) :
    Active p f U ∨ Active p g (f '' U) := by
  by_contra! hn
  have hg : ¬ Const p g (f '' U) := fun hc => ha.1 (outer_const hc)
  have hi : Ident p g (f '' U) := by by_contra hh; exact hn.2 ⟨hg,hh⟩
  have hf : ¬ Const p f U := by
    intro hc
    apply ha.1
    exact fun x hx y hy => (ident_dist h hi (mem_image_of_mem f hx)
      (mem_image_of_mem f hy)).trans (hc x hx y hy)
  apply hn.1
  exact ⟨hf, fun hh => ha.2 (comp_ident h hh hi)⟩

def stepActive (p : D X) : List (Op b) → Set X → Prop
  | [], _ => False
  | F :: tail, A => Active p F.func A ∨ stepActive p tail (F.func '' A)

theorem chain_active (h : ExtendedPseudoMetric X b p) (fs : List (Op b)) :
    Active p (OperatorChain fs.reverse).func U → stepActive p fs U := by
  induction fs generalizing U with
  | nil =>
    intro ha
    exact ha.2 ⟨ha.1, fun x _ => h.dist_self x⟩
  | cons F fs ih =>
    rw [List.reverse_cons, operator_chain_eq_prod, List.prod_append, List.prod_singleton,
      ← operator_chain_eq_prod]
    intro ha
    exact (comp_active (f := F.func) (g := (OperatorChain fs.reverse).func) h ha).imp_right ih

theorem diag_const [Fintype I] {F G : Op b} {L : I → I → ENNReal} {j : I}
    (hc : Const (d j) F.func U) (hl : IsLipMatrix d G (F.func '' U) L)
    (row : ∀ k, k ≠ j → L k j = 0) : Const (d j) (G.func ∘ F.func) U := by
  intro x hx y hy
  have hh := lip_bound_of_single_input_row d G _ L j j hl row _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  simpa [hc x hx y hy] using hh

def fiber (p : D X) (f : X → X) (U : Set X) (z : X) := {x ∈ U | p (f x) z = 0}
abbrev subD := @subfamily_pseudometric
theorem sub_zero {J : Set I} : subD d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  simp [subD, subfamily_pseudometric, ENNReal.iSup_eq_zero]

theorem fiber_target (h : ExtendedPseudoMetric X b p) (hz : p z w = 0) :
    fiber p f U z = fiber p f U w := by ext x; simp [fiber,zero_right h hz]

def blocks (p : D X) (f : X → X) (U : Set X) := fiber p f U '' (f '' U)

theorem fiber_cover (h : ExtendedPseudoMetric X b p) :
    (∀ S ∈ blocks p f U, Set.Nonempty S) ∧ ⋃₀ (blocks p f U) = U := by
  constructor
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,h.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_,⟨x,hx,rfl⟩,rfl⟩,hx,h.dist_self _⟩

theorem fiber_disjoint (h : ExtendedPseudoMetric X b p) :
    fiber p f U z = fiber p f U w ∨ Disjoint (fiber p f U z) (fiber p f U w) := by
  by_cases hd : Disjoint (fiber p f U z) (fiber p f U w)
  · exact Or.inr hd
  obtain ⟨a,ha,ha'⟩ := Set.not_disjoint_iff.mp hd
  exact Or.inl (fiber_target h ((zero_left h ha.2).symm.trans ha'.2))

theorem fiber_inter {J : Set I} (hj : J.Nonempty) :
    fiber (subD d J) f U z = ⋂ j ∈ J, fiber (d j) f U z := by
  obtain ⟨i,hi⟩ := hj
  ext x
  simp only [fiber, mem_setOf_eq, sub_zero, mem_iInter]
  grind

theorem fiber_anti {J K : Set I} (h : J ⊆ K) :
    fiber (subD d K) f U z ⊆ fiber (subD d J) f U z :=
  fun _ hx => ⟨hx.1,sub_zero.mpr fun j hj => sub_zero.mp hx.2 j (h hj)⟩

theorem fiber_edges (i : I) :
    fiber (subD d {i}) f U z = fiber (d i) f U z ∧
    fiber (subD d univ) f U z ⊆ fiber (d i) f U z :=
  ⟨by simp [subD, subfamily_pseudometric_singleton], fun _ hx => ⟨hx.1, sub_zero.mp hx.2 i trivial⟩⟩

theorem fiber_ident (h : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    fiber p f U z = {x ∈ U | p x z = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [zero_left h (hi.2 x hx)]

theorem fiber_const (h : ExtendedPseudoMetric X b p) (hc : Const p f U) (hz : z ∈ f '' U) :
    fiber p f U z = U ∧ (0 < p w z → fiber p f U w = ∅) := by
  obtain ⟨y,hy,rfl⟩ := hz
  constructor
  · exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx,hc x hx y hy⟩)
  · intro hp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hp.ne' ((zero_left h hx.2).symm.trans (hc x hx.1 y hy))

end
end C3
```

```lean filename=Factors.lean
import Components
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

variable {U : Set X} {f g : X → X} {d : I → D X}
def eqRel (U : Set X) (f : X → X) : Set (U × U) := {a | f a.1 = f a.2}
def zeroRel (d : I → D X) (U : Set X) (f : X → X) : Set (U × U) :=
  {a | GaugeZeroRelated d (f a.1) (f a.2)}
def finer (d : I → D X) (U : Set X) (f g : X → X) := zeroRel d U f ⊆ zeroRel d U g

theorem zeroRel_fiber (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (x y : U) :
    (x,y) ∈ zeroRel d U f ↔ (y : X) ∈ fiber (subD d univ) f U (f x) := by
  change (∀ i, d i (f x) (f y) = 0) ↔ _ ∧ _
  simp [y.property, sub_zero, fun i => (hd i).symm (f y) (f x)]

def img (U : Set X) (f : X → X) (x : U) : f '' U := ⟨_, x, x.property, rfl⟩
theorem img_onto : Function.Surjective (img U f) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem factor_iff {A B C : Type} (a : A → B) (ha : Function.Surjective a) (c : A → C) :
    (∃ T : B → C, ∀ x, T (a x) = c x) ↔ ∀ x y, a x = a y → c x = c y := by
  constructor
  · rintro ⟨T,hT⟩ x y h
    rw [← hT x, ← hT y,h]
  · intro h
    exact ⟨fun y => c ((ha y).choose), fun x => h _ _ (ha (a x)).choose_spec⟩

def Factor (U : Set X) (f g : X → X) :=
  ∃ T : f '' U → X, ∀ x : U, T (img U f x) = g x

theorem point_iff : Factor U f g ↔ eqRel U f ⊆ eqRel U g := by
  unfold Factor
  rw [factor_iff _ img_onto]
  exact ⟨fun h a ha => h a.1 a.2 (Subtype.ext ha),
    fun h x y he => h (show (x,y) ∈ eqRel U f from congrArg Subtype.val he)⟩

theorem point_both : Factor U f g ∧ Factor U g f ↔ eqRel U f = eqRel U g := by
  rw [point_iff,point_iff,Set.Subset.antisymm_iff]

def PosFin (r : ENNReal) := 0 < r ∧ r < ⊤

theorem factor_lip {p : D X} {K L : ENNReal} (hk : PosFin K) (_hl : L < ⊤)
    (T : f '' U → X) (ht : ∀ x : U, T (img U f x) = g x)
    (lo : ∀ x ∈ U, ∀ y ∈ U, K * p x y ≤ p (f x) (f y))
    (hi : ∀ x ∈ U, ∀ y ∈ U, p (g x) (g y) ≤ L * p x y) (u v : f '' U) :
    p (T u) (T v) ≤ (L / K) * p u v := by
  obtain ⟨x,rfl⟩ := img_onto u
  obtain ⟨y,rfl⟩ := img_onto v
  rw [ht,ht]
  calc
    _ ≤ L * p x y := hi x x.2 y y.2
    _ = (L / K) * (K * p x y) := by
      rw [← mul_assoc, ENNReal.div_mul_cancel hk.1.ne' hk.2.ne]
    _ ≤ _ := mul_le_mul_right (lo x x.2 y y.2) _

variable (hd : ∀ i, ExtendedPseudoMetric X b (d i))
def imageSetoid (f : X → X) (U : Set X) : Setoid (f '' U) where
  r x y := GaugeZeroRelated d x.val y.val
  iseqv := (gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
    (fun i => (hd i).symm) (fun i => (hd i).triangle)).comap Subtype.val

def cls (f : X → X) (U : Set X) (x : U) := Quotient.mk (imageSetoid hd f U) (img U f x)

theorem cls_onto : Function.Surjective (cls hd f U) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ u => obtain ⟨x,rfl⟩ := img_onto u; exact ⟨x,rfl⟩

theorem cls_eq {x y : U} : cls hd f U x = cls hd f U y ↔ (x,y) ∈ zeroRel d U f :=
  Quotient.eq

def QFactor (f g : X → X) (U : Set X) :=
  ∃ T : Quotient (imageSetoid hd f U) → Quotient (imageSetoid hd g U),
    ∀ x : U, T (cls hd f U x) = cls hd g U x

theorem quotient_iff : QFactor hd f g U ↔ finer d U f g := by
  unfold QFactor
  rw [factor_iff _ (cls_onto hd)]
  simp only [cls_eq]
  exact ⟨fun h a => h a.1 a.2, fun h x y => @h (x,y)⟩

theorem quotient_both : QFactor hd f g U ∧ QFactor hd g f U ↔
    zeroRel d U f = zeroRel d U g := by
  rw [quotient_iff,quotient_iff,Set.Subset.antisymm_iff]
  rfl

include hd in
theorem separated (hs : ∀ u ∈ f '' U, ∀ v ∈ f '' U, GaugeZeroRelated d u v → u = v) :
    eqRel U f = zeroRel d U f := by
  ext a
  constructor
  · intro h i
    change f a.1 = f a.2 at h
    rw [h,(hd i).dist_self]
  · exact hs _ (img U f a.1).2 _ (img U f a.2).2

theorem separated_criteria
    (hf : ∀ u ∈ f '' U, ∀ v ∈ f '' U, GaugeZeroRelated d u v → u = v)
    (hg : ∀ u ∈ g '' U, ∀ v ∈ g '' U, GaugeZeroRelated d u v → u = v) :
    (Factor U f g ↔ QFactor hd f g U) ∧
    ((Factor U f g ∧ Factor U g f) ↔ (QFactor hd f g U ∧ QFactor hd g f U)) := by
  simp only [point_iff, quotient_iff, finer, separated hd hf, separated hd hg, iff_self, and_self]

theorem finer_preorder : (∀ f, finer d U f f) ∧
    (∀ f g k, finer d U f g → finer d U g k → finer d U f k) :=
  ⟨fun _ => Subset.rfl, fun _ _ _ h h' => h.trans h'⟩

theorem finer_chain {n : ℕ} {F : Fin (n+1) → X → X}
    (hs : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) :
    Monotone (fun k => zeroRel d U (F k)) := Fin.monotone_iff_le_succ.mpr hs

theorem finer_strict {n : ℕ} {F : Fin (n+1) → X → X}
    (hs : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) (r : Fin n)
    (hr : zeroRel d U (F r.castSucc) ⊂ zeroRel d U (F r.succ)) :
    zeroRel d U (F 0) ⊂ zeroRel d U (F (Fin.last n)) ∧
    ∃ a ∈ zeroRel d U (F (Fin.last n)), a ∉ zeroRel d U (F 0) := by
  have H := finer_chain hs
  obtain ⟨a,ha,hb⟩ := Set.exists_of_ssubset hr
  have hx := H (Fin.le_last r.succ) ha
  have hn : a ∉ zeroRel d U (F 0) := fun hh => hb (H (Fin.zero_le _) hh)
  exact ⟨⟨H (Fin.zero_le _),fun h => hn (h hx)⟩,a,hx,hn⟩

end
end C3
```

```lean filename=Radii.lean
import Factors
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

def legal (p q : D X) (f : X → X) (U : Set X) (y : X) : Set ENNReal :=
  {r | PosFin r ∧ ∀ x ∈ U, p x y < r → q (f x) (f y) = 0}

def rad (p q : D X) (f : X → X) (U : Set X) (y : X) := sSup (legal p q f U y)
def uniform (p q : D X) (f : X → X) (A U : Set X) := ⨅ y : A, rad p q f U y
def N (d : I → D X) (f : X → X) (U : Set X) (j i : I) := uniform (d i) (d j) f U U

variable {p q s : D X} {f g : X → X} {U A B : Set X} {x y : X} {r L : ENNReal}
variable {d : I → D X} {J K : Set I}

theorem legal_ball : r ∈ legal p q f U y ↔
    PosFin r ∧ ball p y r ∩ U ⊆ fiber q f U (f y) :=
  ⟨fun h => ⟨h.1,fun x hx => ⟨hx.2,h.2 x hx.2 hx.1⟩⟩,
   fun h => ⟨h.1,fun _ hx hxy => (h.2 ⟨hxy,hx⟩).2⟩⟩

theorem below_rad (hx : x ∈ U) (hlt : p x y < rad p q f U y) : q (f x) (f y) = 0 := by
  obtain ⟨ρ,hρ,hlt'⟩ := lt_sSup_iff.mp hlt
  exact hρ.2 x hx hlt'

theorem le_rad : r ≤ rad p q f U y ↔ ∀ x ∈ U, p x y < r → q (f x) (f y) = 0 := by
  refine ⟨fun h _ hx hp => below_rad hx (hp.trans_le h), ?_⟩
  intro h
  by_contra! hr
  obtain ⟨t,ht,ht'⟩ := exists_between hr
  exact ht.not_ge (le_sSup (s := legal p q f U y) ⟨⟨(zero_le _).trans_lt ht,ht'.trans_le le_top⟩,
    fun x hx hp => h x hx (hp.trans ht')⟩)

theorem le_uniform : r ≤ uniform p q f A U ↔
    ∀ y ∈ A, ∀ x ∈ U, p x y < r → q (f x) (f y) = 0 := by
  simp [uniform, le_iInf_iff,le_rad]

theorem uniform_zero (hx : x ∈ U) (hy : y ∈ U) (h : p x y < uniform p q f U U) :
    q (f x) (f y) = 0 := le_uniform.mp le_rfl y hy x hx h

theorem positive_sep (hx : x ∈ U) (hy : y ∈ U) (h : 0 < q (f x) (f y)) :
    uniform p q f U U ≤ p x y := le_of_not_gt (fun hh => h.ne' (uniform_zero hx hy hh))

theorem uniform_witness (h : uniform p q f U U < r) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, PosFin ε ∧ p x y < r ∧ ε ≤ q (f x) (f y) := by
  have hn := mt le_uniform.mpr h.not_ge
  push Not at hn
  obtain ⟨y,hy,x,hx,hxy,hq⟩ := hn
  exact ⟨x,hx,y,hy,min 1 (q (f x) (f y)),⟨lt_min zero_lt_one (pos_iff_ne_zero.mpr hq),
    (min_le_left _ _).trans_lt ENNReal.one_lt_top⟩,hxy,min_le_right _ _⟩

theorem sub_const (hc : ∀ j ∈ J, Const (d j) f U) : Const (subD d J) f U :=
  fun x hx y hy => sub_zero.mpr fun j hj => hc j hj x hx y hy

theorem const_full (hc : Const q f U) (hy : y ∈ U) : fiber q f U (f y) = U :=
  Set.Subset.antisymm (fun _ h => h.1) (fun x hx => ⟨hx,hc x hx y hy⟩)

theorem const_top (hc : Const q f U) :
    (∀ y ∈ U, rad p q f U y = ⊤) ∧ uniform p q f U U = ⊤ :=
  ⟨fun y hy => top_unique (le_rad.mpr fun x hx _ => hc x hx y hy),
   top_unique (le_uniform.mpr fun y hy x hx _ => hc x hx y hy)⟩

theorem ident_base (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hy : y ∈ U) :
    fiber p f U (f y) = {x ∈ U | p x y = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [ident_dist hd hi hx hy]

theorem ident_rad (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hy : y ∈ U)
    (hr : PosFin r) (hh : ball p y r ∩ U ⊆ {x ∈ U | p x y = 0}) :
    r ≤ rad p p f U y ∧ 0 < r :=
  ⟨le_sSup (legal_ball.mpr ⟨hr,by rwa [ident_base hd hi hy]⟩),hr.1⟩

theorem rad_sub : rad p (subD d J) f U y = ⨅ j : J, rad p (d j) f U y := by
  apply le_antisymm
  · exact le_iInf fun j => le_rad.mpr fun x hx hp => sub_zero.mp (below_rad hx hp) j j.2
  · apply le_rad.mpr
    intro x hx hp
    exact sub_zero.mpr fun j hj => below_rad hx (hp.trans_le (iInf_le _ (⟨j,hj⟩ : J)))

theorem uniform_sub (i : I) :
    uniform (d i) (subD d J) f U U = ⨅ j : J, N d f U j i := by
  unfold uniform N
  simp only [rad_sub]
  exact iInf_comm

theorem attained_min [Finite I] (hj : J.Nonempty) (a : J → ENNReal) :
    ∃ j, a j = ⨅ k, a k := by
  letI : Nonempty J := hj.to_subtype
  exact exists_eq_ciInf_of_finite

theorem uniform_sub_anti (h : J ⊆ K) (i : I) :
    uniform (d i) (subD d K) f U U ≤ uniform (d i) (subD d J) f U U := by
  rw [uniform_sub,uniform_sub]
  exact le_iInf fun j => iInf_le _ (⟨j.1,h j.2⟩ : K)

theorem fiber_cut (hd : ExtendedPseudoMetric X b q) (h : x ∈ fiber q f U (f y)) :
    q (f y) (f x) = 0 := (hd.symm _ _).trans h.2

theorem point_cut (hp : ExtendedPseudoMetric X b p) (hq : ExtendedPseudoMetric X b q)
    (hx : x ∈ U) (h : p y x < rad p q f U y) : q (f y) (f x) = 0 :=
  (hq.symm _ _).trans (below_rad hx ((hp.symm x y) ▸ h))

theorem comp_cut {F G : Op b} (hq : ExtendedPseudoMetric X b q)
    (_hx : x ∈ dom F) (_hy : y ∈ dom F) (_hU : U ⊆ dom G)
    (_hxU : F.func x ∈ U) (_hyU : F.func y ∈ U)
    (hh : F.func y ∈ fiber q G.func U (G.func (F.func x))) :
    q ((G * F).func x) ((G * F).func y) = 0 := fiber_cut (f := G.func) (x := F.func y) (y := F.func x) hq hh

theorem comp_zero (hh : ∀ u ∈ f '' U, ∀ v ∈ f '' U, q u v = 0 → s (g u) (g v) = 0) :
    uniform p q f U U ≤ uniform p s (g ∘ f) U U :=
  le_uniform.mpr fun y hy x hx hp => hh _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (uniform_zero hx hy hp)

theorem scaled_lt (hL : PosFin L) {a e : ENNReal} : a < e / L ↔ L * a < e := by
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hL.1.ne') (Or.inl hL.2.ne), mul_comm]

theorem comp_lip (hL : PosFin L) (hl : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) ≤ L * p x y) :
    uniform q s g (f '' U) (f '' U) / L ≤ uniform p s (g ∘ f) U U :=
  le_uniform.mpr fun y hy x hx hp => uniform_zero (p := q) (f := g) (x := f x) (y := f y) (mem_image_of_mem f hx) (mem_image_of_mem f hy)
    ((hl x hx y hy).trans_lt ((scaled_lt hL).mp hp))

theorem rad_restrict (h : B ⊆ A) : rad p q f A y ≤ rad p q f B y :=
  le_rad.mpr fun _ hx hp => below_rad (h hx) hp

theorem uniform_restrict (h : B ⊆ A) : uniform p q f A A ≤ uniform p q f B B :=
  le_uniform.mpr fun _ hy _ hx hp => uniform_zero (h hx) (h hy) hp

theorem threshold_ball (hr : r ≤ uniform p q f U U) (hy : y ∈ U) :
    ball p y r ∩ U ⊆ fiber q f U (f y) :=
  fun _ hx => ⟨hx.2,uniform_zero hx.2 hy (lt_of_lt_of_le hx.1 hr)⟩

def diameter (p : D X) (A : Set X) := ⨆ x : A, ⨆ y : A, p x y

theorem le_diameter (hx : x ∈ U) (hy : y ∈ U) : p x y ≤ diameter p U :=
  le_iSup_of_le (⟨x,hx⟩ : U) (le_iSup_of_le (⟨y,hy⟩ : U) le_rfl)

theorem diameter_le : diameter p U ≤ r ↔ ∀ x ∈ U, ∀ y ∈ U, p x y ≤ r := by
  simp [diameter,iSup_le_iff]

structure Scale (X I : Type) where
  val : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → val i A ≤ val i B

def diamScale (d : I → D X) : Scale X I :=
  ⟨fun i A => diameter (d i) A,fun _ _ _ h => diameter_le.mpr fun _ hx _ hy => le_diameter (h hx) (h hy)⟩

def bits (a n t u : ENNReal) : Bool × Bool := (decide (a < t),decide (u ≤ n))
def channel (σ : Scale X I) (A : {A : Set X // A.Nonempty}) (d : I → D X) (f : X → X)
    (t u : ENNReal) (i j : I) := bits (σ.val i A) (N d f A j i) t u

theorem bits_cases (a n t u : ENNReal) :
    (bits a n t u = (true,true) ↔ a < t ∧ u ≤ n) ∧
    (bits a n t u = (true,false) ↔ a < t ∧ n < u) ∧
    (bits a n t u = (false,true) ↔ t ≤ a ∧ u ≤ n) ∧
    (bits a n t u = (false,false) ↔ t ≤ a ∧ n < u) := by simp [bits]

theorem scale_threshold {a n t t' u : ENNReal} (h : t ≤ t') :
    (bits a n t u).1 = true → (bits a n t' u).1 = true := by simpa [bits] using (fun hh => lt_of_lt_of_le hh h : a < t → a < t')
theorem null_threshold {a n t u u' : ENNReal} (h : u ≤ u') :
    (bits a n t u').2 = true → (bits a n t u).2 = true := by simpa [bits] using (fun hh => h.trans hh : u' ≤ n → u ≤ n)

theorem scale_restrict (σ : Scale X I) (i : I) {A B} (h : B.val ⊆ A.val) (t : ENNReal) :
    σ.val i B ≤ σ.val i A ∧ (σ.val i A < t → σ.val i B < t) :=
  ⟨σ.mono i B A h, fun hh => (σ.mono i B A h).trans_lt hh⟩

theorem small_iff {t u : ENNReal} (h : diameter p U < t) (ht : t ≤ u) :
    u ≤ uniform p q f U U ↔ Const q f U :=
  ⟨fun hn _ hx _ hy => uniform_zero hx hy ((le_diameter hx hy).trans_lt (h.trans_le (ht.trans hn))),
   fun hc => (const_top (p := p) hc).2 ▸ le_top⟩

theorem point_gap [Fintype I] {F : Op b} {K : I → I → ENNReal} {i j : I}
    (hk : IsCoLipMatrix d F U K) (hp : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y ∉ Ioo 0 (rad (d i) (d j) F.func U y) := by
  intro hh
  exact hh.1.ne' (positive_colip_entry_reflects_zero d F U K i j hk hp x hx y hy (below_rad hx hh.2))

theorem uniform_gap [Fintype I] {F : Op b} {K : I → I → ENNReal} {i j : I}
    (hk : IsCoLipMatrix d F U K) (hp : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ N d F.func U j i ≤ d i x y := by
  by_cases hh : N d F.func U j i ≤ d i x y
  · exact Or.inr hh
  · exact Or.inl (positive_colip_entry_reflects_zero d F U K i j hk hp x hx y hy
      (uniform_zero hx hy (lt_of_not_ge hh)))

end
end C3
```

```lean filename=Entropy.lean
import Radii
import Mathlib.Data.EReal.Operations
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

abbrev cov := @covering_number
abbrev ent := @metric_entropy
def TB (p : D X) (U : Set X) := ∀ r, PosFin r → cov p r U < ⊤
def Defined (p q : D X) (f : X → X) (U : Set X) (e : ENNReal) :=
  cov p e U < ⊤ ∨ cov q e (f '' U) < ⊤
def delta (p q : D X) (f : X → X) (U : Set X) (e : ENNReal) (_ : Defined p q f U e) :=
  ent p e U - ent q e (f '' U)

variable {p q : D X} {f : X → X} {U A B : Set X} {e r L : ENNReal}

theorem internal_spec (S : Finset X) :
    InternalEpsilonNet p e U S ↔ (S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball p c e := by
  simp [InternalEpsilonNet, Set.subset_def, ball]

theorem tb_spec : TB p U ↔ ∀ r, PosFin r → ∃ S, InternalEpsilonNet p r U S := by
  simp [TB,cov,lt_top_iff_ne_top,covering_number_eq_top_iff]

theorem net_bound {S : Finset X} (h : InternalEpsilonNet p e U S) : cov p e U ≤ S.card :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem push_net {S : Finset X} (hs : InternalEpsilonNet p r U S)
    (h : ∀ x ∈ U, ∀ y ∈ U, p x y < r → q (f x) (f y) < e) :
    InternalEpsilonNet q e (f '' U) (S.image f) ∧ (S.image f).card ≤ S.card := by
  refine ⟨⟨?_,?_⟩, Finset.card_image_le⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x,hs.1 hx,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := hs.2 x hx
    exact ⟨_,Finset.mem_image_of_mem _ hy,h x hx y (hs.1 hy) hxy⟩

theorem push_cover (h : ∀ x ∈ U, ∀ y ∈ U, p x y < r → q (f x) (f y) < e) :
    cov q e (f '' U) ≤ cov p r U := by
  refine le_iInf fun S => le_iInf fun hs => ?_
  obtain ⟨hnet,hcard⟩ := push_net hs h
  exact (net_bound hnet).trans (by exact_mod_cast hcard)

def repr (f : X → X) (U : Set X) (z : X) := if hz : z ∈ f '' U then hz.choose else z
theorem repr_spec (z : X) (hz : z ∈ f '' U) : repr f U z ∈ U ∧ f (repr f U z) = z := by
  simpa [repr,hz] using hz.choose_spec

theorem pull_net {T : Finset X} (ht : InternalEpsilonNet q e (f '' U) T)
    (h : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) < e → p x y < r) :
    InternalEpsilonNet p r U (T.image (repr f U)) ∧ (T.image (repr f U)).card ≤ T.card := by
  refine ⟨⟨?_,?_⟩,Finset.card_image_le⟩
  · intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    exact (repr_spec z (ht.1 hz)).1
  · intro x hx
    obtain ⟨z,hz,hxz⟩ := ht.2 _ ⟨x,hx,rfl⟩
    obtain ⟨hc,he⟩ := repr_spec z (ht.1 hz)
    exact ⟨_,Finset.mem_image_of_mem _ hz,h x hx _ hc (he.symm ▸ hxz)⟩

theorem pull_cover (h : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) < e → p x y < r) :
    cov p r U ≤ cov q e (f '' U) := by
  refine le_iInf fun T => le_iInf fun ht => ?_
  obtain ⟨hnet,hcard⟩ := pull_net ht h
  exact (net_bound hnet).trans (by exact_mod_cast hcard)

theorem log_mono : Monotone log2_ereal := by
  intro a b h
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal,hb]
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top hb h
  have hb' : b ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha) h).ne'
  simp [log2_ereal,ha,hb,ha',hb',Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha ha') (ENNReal.toReal_mono hb h)]

theorem threshold_cover (hBA : B ⊆ A) (hr : r ≤ uniform p q f A A) (he : 0 < e) :
    cov q e (f '' B) ≤ cov p r B :=
  push_cover fun _ hx _ hy hp => (uniform_zero (hBA hx) (hBA hy) (hp.trans_le hr)).symm ▸ he

theorem threshold_entropy (hBA : B ⊆ A) (hr : r ≤ uniform p q f A A) (he : 0 < e) :
    ent q e (f '' B) ≤ ent p r B := log_mono (threshold_cover hBA hr he)

theorem one_cover (hu : U.Nonempty) (hc : Const q f U) (he : 0 < e) :
    cov q e (f '' U) = 1 := by
  obtain ⟨y,hy⟩ := hu
  apply le_antisymm _ (one_le_covering_number_of_nonempty q e (f '' U) ⟨f y,y,hy,rfl⟩)
  have h : InternalEpsilonNet q e (f '' U) {f y} := by
    constructor
    · simpa using (mem_image_of_mem f hy)
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨_,Finset.mem_singleton_self _,(hc x hx y hy).symm ▸ he⟩
  simpa using net_bound h

theorem small_cover (hu : U.Nonempty) {t u : ENNReal} (hd : diameter p U < t)
    (ht : t ≤ u) (hn : u ≤ uniform p q f U U) (he : 0 < e) : cov q e (f '' U) = 1 :=
  one_cover hu ((small_iff hd ht).mp hn) he

theorem finite_entropy (hu : U.Nonempty) (h : cov p e U < ⊤) :
    ∃ a : ℝ, ent p e U = a := by
  have h0 := (zero_lt_one.trans_le (one_le_covering_number_of_nonempty p e U hu)).ne'
  exact ⟨Real.logb 2 (cov p e U).toReal,by simp [ent,metric_entropy,log2_ereal,h0,h.ne]⟩

theorem finite_cover (hd : ∀ x, p x x = 0) (hu : U.Finite) (he : 0 < e) : cov p e U < ⊤ := by
  have h : InternalEpsilonNet p e U hu.toFinset :=
    ⟨by simp,fun x hx => ⟨x,hu.mem_toFinset.mpr hx,(hd x).symm ▸ he⟩⟩
  exact (net_bound h).trans_lt (ENNReal.natCast_lt_top _)

theorem finite_ends {d : I → D X} (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    (J K : Set I) (hj : J.Nonempty) (hk : K.Nonempty) (hu : U.Nonempty) (hf : U.Finite)
    (f : X → X) (he : PosFin e) :
    (0 < cov (subD d J) e U ∧ cov (subD d J) e U < ⊤) ∧
    (0 < cov (subD d K) e (f '' U) ∧ cov (subD d K) e (f '' U) < ⊤) ∧
    (∃ a : ℝ, ent (subD d J) e U = a) ∧ (∃ a : ℝ, ent (subD d K) e (f '' U) = a) ∧
    Defined (subD d J) (subD d K) f U e := by
  have h₁ := finite_cover (subfamily_pseudometric_is_extended d J hj hd).dist_self hf he.1
  have h₂ := finite_cover (subfamily_pseudometric_is_extended d K hk hd).dist_self (hf.image f) he.1
  exact ⟨⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hu),h₁⟩,
    ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hu.image f)),h₂⟩,
    finite_entropy hu h₁,finite_entropy (hu.image f) h₂,Or.inl h₁⟩

theorem const_delta (hu : U.Nonempty) (hc : Const p f U) (he : 0 < e) :
    cov p e (f '' U) = 1 ∧ ent p e (f '' U) = 0 ∧
    ∃ h : Defined p p f U e, delta p p f U e h = ent p e U := by
  have hn := one_cover hu hc he
  have ho : ent p e (f '' U) = 0 := by simp [ent,metric_entropy,hn,log2_ereal]
  exact ⟨hn,ho,Or.inr (hn ▸ ENNReal.one_lt_top),by simp [delta,ho]⟩

theorem ident_cover (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    cov p e (f '' U) = cov p e U ∧ ent p e (f '' U) = ent p e U := by
  have h := fun {x y} (hx : x ∈ U) (hy : y ∈ U) => ident_dist hd hi hx hy
  have heq : cov p e (f '' U) = cov p e U :=
    le_antisymm (push_cover fun _ hx _ hy hh => (h hx hy).symm ▸ hh)
      (pull_cover fun _ hx _ hy hh => (h hx hy) ▸ hh)
  exact ⟨heq,congrArg log2_ereal heq⟩

theorem ident_delta (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U)
    (hu : U.Nonempty) (hw : Defined p p f U e) : delta p p f U e hw = 0 := by
  obtain ⟨hn,he⟩ := ident_cover (e := e) hd hi
  obtain ⟨a,ha⟩ := finite_entropy hu (hw.elim id (hn ▸ id))
  rw [delta,he,ha,← EReal.coe_sub,sub_self,EReal.coe_zero]

theorem div_pf (he : PosFin e) (hL : PosFin L) : PosFin (e / L) :=
  ⟨ENNReal.div_pos he.1.ne' hL.2.ne, ENNReal.div_lt_top he.2.ne hL.1.ne'⟩

theorem lip_cover (hl : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) ≤ L * p x y) (hL : PosFin L) :
    cov q e (f '' U) ≤ cov p (e / L) U :=
  push_cover fun x hx y hy h => (hl x hx y hy).trans_lt ((scaled_lt hL).mp h)

theorem lip_delta (hu : U.Nonempty) (ht : TB p U) (he : PosFin e) (hL : PosFin L)
    (hl : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) ≤ L * p x y) :
    (∃ a : ℝ, ent p e U = a) ∧ (∃ a : ℝ, ent q e (f '' U) = a) ∧
    ∃ hw, ent p e U - ent p (e/L) U ≤ delta p q f U e hw := by
  have hh := lip_cover (e := e) hl hL
  exact ⟨finite_entropy hu (ht e he),finite_entropy (hu.image f) (hh.trans_lt (ht _ (div_pf he hL))),
    Or.inl (ht e he), EReal.sub_le_sub le_rfl (log_mono hh)⟩

theorem colip_cover [Fintype I] {d : I → D X} {F : Op b} {K : I → I → ENNReal}
    (hk : IsCoLipMatrix d F U K) {i j : I} (hp : PosFin (K i j)) :
    cov (d i) (e / K i j) U ≤ cov (d j) e (F.func '' U) := by
  apply pull_cover
  intro x hx y hy h
  apply (scaled_lt hp).mpr
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
    (Finset.mem_univ i)).trans_lt ((hk.2.2 x hx y hy j).trans_lt h)

theorem colip_delta [Fintype I] {d : I → D X} {F : Op b} {K : I → I → ENNReal}
    (hk : IsCoLipMatrix d F U K) {i j : I} (hp : PosFin (K i j)) (ht : TB (d i) U)
    (he : PosFin e) : ∃ hw, delta (d i) (d j) F.func U e hw ≤
      ent (d i) e U - ent (d i) (e / K i j) U :=
  ⟨Or.inl (ht e he), EReal.sub_le_sub le_rfl (log_mono (colip_cover hk hp))⟩

theorem delta_cases (hu : U.Nonempty) (hw : Defined p q f U e) :
    (cov p e U = ⊤ → delta p q f U e hw = ⊤) ∧
    (cov q e (f '' U) = ⊤ → delta p q f U e hw = ⊥) ∧
    (cov p e U < ⊤ → cov q e (f '' U) < ⊤ → ∃ a : ℝ, delta p q f U e hw = a) := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := finite_entropy (hu.image f) (hw.resolve_left (by simp [h]))
    rw [delta,ha]
    simp [ent,metric_entropy,h,log2_ereal]
  constructor
  · intro h
    simp [delta,ent,metric_entropy,h,log2_ereal,EReal.sub_top]
  · intro h k
    obtain ⟨a,ha⟩ := finite_entropy hu h
    obtain ⟨c,hc⟩ := finite_entropy (hu.image f) k
    exact ⟨a-c,by rw [delta,ha,hc,EReal.coe_sub]⟩

end
end C3
```

```lean filename=Models.lean
import Entropy
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

def liftDist (p : D X) : D (Option X)
  | some x, some y => p x y
  | none, none => 0
  | _, _ => ⊤

theorem lift_metric [Nonempty X] {p : D X} (hr : ∀ x, p x x = 0)
    (hs : ∀ x y, p x y = p y x) (ht : ∀ x y z, p x z ≤ p x y + p y z) :
    ExtendedPseudoMetric (Option X) none (liftDist p) where
  nonabsorbing := ⟨some (Classical.arbitrary X), Option.some_ne_none _⟩
  dist_self x := by cases x <;> simp [liftDist,hr]
  symm x y := by cases x <;> cases y <;> simp [liftDist,hs]
  triangle x y z := by cases x <;> cases y <;> cases z <;> simp [liftDist,ht]
  isolate_bot x hx := by cases x <;> simp_all [liftDist]

def discrete {Y : Type} (v : X → Y) (c : ENNReal) (x y : X) : ENNReal :=
  if v x = v y then 0 else c

theorem discrete_metric [Nonempty X] {Y : Type} (v : X → Y) (c : ENNReal) :
    ExtendedPseudoMetric (Option X) none (liftDist (discrete v c)) := by
  apply lift_metric
  · simp [discrete]
  · intro x y
    simp [discrete,eq_comm]
  · intro x y z
    by_cases h : v x = v y <;> by_cases k : v y = v z <;> simp_all [discrete]
    split <;> simp

def run (f : X → X) : Op (none : Option X) := ⟨Option.map f,rfl⟩
def area (S : Set X) := some '' S
@[simp] theorem some_area {S : Set X} {x : X} : some x ∈ area S ↔ x ∈ S := by simp [area]
theorem area_dom (f : X → X) (S : Set X) : area S ⊆ dom (run f) := by
  rintro _ ⟨x,_,rfl⟩
  exact Option.some_ne_none _
theorem area_image (f : X → X) (S : Set X) : (run f).func '' area S = area (f '' S) := by
  simp [area,run,image_image]

def realDist (v : ℝ → ℝ) (x y : ℝ) := ENNReal.ofReal |v x - v y|
abbrev line (v : ℝ → ℝ) := liftDist (realDist v)
theorem line_metric (v : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (line v) := by
  apply lift_metric
  · simp [realDist]
  · intro x y
    rw [realDist,abs_sub_comm,realDist]
  · intro x y z
    rw [realDist,realDist,realDist,← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

@[simp] theorem line_some (v : ℝ → ℝ) (x y : ℝ) :
    line v (some x) (some y) = ENNReal.ofReal |v x-v y| := rfl
@[simp] theorem run_some (f : X → X) (x : X) : (run f).func (some x) = some (f x) := rfl

theorem area_diam {p : D X} {S : Set X} : diameter (liftDist p) (area S) = diameter p S := by
  apply le_antisymm
  · apply diameter_le.mpr
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact le_diameter hx hy
  · exact diameter_le.mpr fun x hx y hy => le_diameter (some_area.mpr hx) (some_area.mpr hy)

theorem area_rad {p q : D X} {f : X → X} {S : Set X} {y : X} :
    rad (liftDist p) (liftDist q) (run f).func (area S) (some y) = rad p q f S y := by
  apply le_antisymm
  · exact le_rad.mpr fun x hx hh => below_rad (p := liftDist p) (q := liftDist q) (f := (run f).func) (y := some y) (some_area.mpr hx) hh
  · apply le_rad.mpr
    rintro _ ⟨x,hx,rfl⟩ hh
    exact below_rad (p := p) (q := q) (f := f) (y := y) hx hh

theorem area_uniform {p q : D X} {f : X → X} {S : Set X} :
    uniform (liftDist p) (liftDist q) (run f).func (area S) (area S) = uniform p q f S S := by
  apply le_antisymm
  · apply le_uniform.mpr
    intro y hy x hx hp
    exact uniform_zero (p := liftDist p) (q := liftDist q) (f := (run f).func) (some_area.mpr hx) (some_area.mpr hy) hp
  · apply le_uniform.mpr
    rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩ hp
    exact uniform_zero (p := p) (q := q) (f := f) hx hy hp

namespace Swap
abbrev p := liftDist (discrete (id : Bool → Bool) 1)
def F := run Bool.not
def U := area (univ : Set Bool)
theorem model : ExtendedPseudoMetric _ none p := discrete_metric _ _
theorem image_dom : U ⊆ dom F ∧ F.func '' U = U := by
  refine ⟨area_dom _ _,?_⟩
  have hh : Function.Surjective Bool.not := fun x => ⟨!x,by simp⟩
  rw [U,F,area_image,Set.image_univ,Set.range_eq_univ.mpr hh]

theorem calc_swap : Active p F.func U ∧ ¬ Ident p F.func U ∧
    Ident p (F * F).func U ∧ ¬ Active p (F * F).func U := by
  have mem (x : Bool) : some x ∈ U := some_area.mpr trivial
  have hn : ¬ Const p F.func U := by
    intro h
    simpa [p,F,liftDist,discrete] using h _ (mem true) _ (mem false)
  have hi : ¬ Ident p F.func U := by
    intro h
    simpa [p,F,liftDist,discrete] using h.2 _ (mem true)
  have hid : Ident p (F * F).func U := by
    refine ⟨?_,?_⟩
    · intro h
      have hh := h _ (mem true) _ (mem false)
      change p (some true) (some false) = 0 at hh
      simp [p,liftDist,discrete] at hh
    · rintro _ ⟨x,_,rfl⟩
      cases x <;> exact (model.dist_self _)
  exact ⟨⟨hn,hi⟩,hi,hid,fun h => h.2 hid⟩
end Swap

namespace Seven
abbrev Pt := Fin 6
def readout (x : Pt) := if x = 3 then 2 else x
def p (j : Bool) := liftDist (discrete (if j then id else readout) 1)
def F : Op (none : Option Pt) :=
  ⟨fun x => if x = some 0 then some 2 else if x = some 1 then some 3 else none,by simp⟩
def G : Op (none : Option Pt) :=
  ⟨fun x => if x = some 2 then some 4 else if x = some 3 then some 5 else none,by simp⟩
def U : Set (Option Pt) := {some 0,some 1}
theorem model (j : Bool) : ExtendedPseudoMetric _ none (p j) := discrete_metric _ _
theorem example_seven : U ⊆ dom (G * F) ∧ Const (p false) F.func U ∧
    ¬ Const (p false) (G * F).func U ∧ p true (F.func (some 0)) (F.func (some 1)) = 1 := by
  have hf0 : F.func (some 0) = some 2 := by simp [F]
  have hf1 : F.func (some 1) = some 3 := by norm_num [F,Fin.ext_iff]
  have hg2 : G.func (some 2) = some 4 := by simp [G]
  have hg3 : G.func (some 3) = some 5 := by norm_num [G,Fin.ext_iff]
  have eval (x) : (G * F).func x = G.func (F.func x) := rfl
  simp only [U, Const, Set.mem_insert_iff,Set.mem_singleton_iff,
    forall_eq_or_imp,forall_eq] at *
  norm_num [Set.subset_def,dom,eval,hf0,hf1,hg2,hg3,p,liftDist,discrete,readout,Fin.ext_iff]
  simp

end Seven

namespace InfiniteInput
def d (j : Bool) := liftDist (discrete (id : Bool → Bool) (if j then 1 else ⊤))
theorem model (j : Bool) : ExtendedPseudoMetric _ none (d j) := discrete_metric _ _
theorem both (j : Bool) : N d (run id).func Swap.U j false = ⊤ ∧ ¬ Const (d j) (run id).func Swap.U := by
  constructor
  · apply top_unique
    apply le_uniform.mpr
    rintro _ ⟨y,_,rfl⟩ _ ⟨x,_,rfl⟩ hh
    by_cases he : x = y
    · subst x; exact (model j).dist_self _
    · simp [d,liftDist,discrete,he] at hh
  · intro hc
    have hh := hc (some true) (some_area.mpr trivial) (some false) (some_area.mpr trivial)
    cases j <;> simp [d,liftDist,discrete] at hh
end InfiniteInput

end
end C3
```

```lean filename=RealExamples.lean
import Models
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

abbrev usual := realDist id
abbrev pt := @some ℝ

theorem usual_eq {x y : ℝ} : usual x y = 0 ↔ x = y := by simp [usual,realDist,abs_nonpos_iff,sub_eq_zero]

theorem uniform_at (S : Set ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ S) :
    uniform usual usual f S S ≤ rad usual usual f S x := iInf_le _ (⟨x,hx⟩ : S)

theorem zero_tests {v : ENNReal} (h : ∀ t : ℝ, 0 < t → v < ENNReal.ofReal t) : v = 0 := by
  by_contra hn
  obtain ⟨r,hp,hr⟩ := exists_between (pos_iff_ne_zero.mpr hn)
  have ht : r ≠ ⊤ := (hr.trans_le le_top).ne
  have hh := h r.toReal (ENNReal.toReal_pos hp.ne' ht)
  rw [ENNReal.ofReal_toReal ht] at hh
  exact hr.asymm hh

def step (x : ℝ) : ℝ := if x < 0 then 0 else 1
def punct : Set ℝ := Ico (-1) 0 ∪ Ioc 0 1

theorem step_model : ExtendedPseudoMetric (Option ℝ) none (line id) ∧
    (area punct).Nonempty ∧ area punct ⊆ dom (run step) :=
  ⟨line_metric _,⟨pt 1,some_area.mpr (Or.inr ⟨by norm_num,le_rfl⟩)⟩,area_dom _ _⟩

theorem step_legal {y : ℝ} (hy : y ∈ punct) {r : ENNReal} :
    r ∈ legal usual usual step punct y ↔ PosFin r ∧ r ≤ ENNReal.ofReal |y| := by
  have hy' : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1) := hy
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    by_contra! hh
    have hd := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hr.2.ne).mp hh
    let a := min 1 ((r.toReal - |y|)/2)
    have ha : 0 < a := lt_min (by norm_num) (by linarith)
    have ha1 : a ≤ 1 := min_le_left _ _
    have har : a < r.toReal - |y| := (min_le_right _ _).trans_lt (by linarith)
    rcases hy' with hy | hy
    · have hp : a ∈ punct := Or.inr ⟨ha,ha1⟩
      have hlt : usual a y < r := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mpr
        simp only [id_eq,abs_of_nonneg (by linarith : 0 ≤ a-y)]
        rw [abs_of_neg hy.2] at har
        linarith
      have := usual_eq.mp (h a hp hlt)
      simp [step,ha.not_gt,hy.2] at this
    · have hp : -a ∈ punct := Or.inl ⟨by linarith,by linarith⟩
      have hlt : usual (-a) y < r := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mpr
        simp only [id_eq,abs_of_neg (by linarith : -a-y < 0)]
        rw [abs_of_pos hy.1] at har
        linarith
      have := usual_eq.mp (h (-a) hp hlt)
      simp [step,neg_lt_zero.mpr ha,hy.1.not_gt] at this
  · rintro ⟨hr,hle⟩
    refine ⟨hr,?_⟩
    intro x hx hxy
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).mp (hxy.trans_le hle)
    change |x-y| < |y| at h
    apply usual_eq.mpr
    rcases hy' with hy | hy
    · rw [abs_of_neg hy.2, abs_lt] at h
      simp [step,hy.2,show x < 0 by linarith]
    · rw [abs_of_pos hy.1, abs_lt] at h
      simp [step,hy.1.not_gt,show ¬ x < 0 by linarith]

theorem step_radius {y : ℝ} (hy : y ∈ punct) :
    rad (line id) (line id) (run step).func (area punct) (pt y) = ENNReal.ofReal |y| ∧
    0 < ENNReal.ofReal |y| := by
  have hn : y ≠ 0 := by rintro rfl; norm_num [punct] at hy
  have hp := ENNReal.ofReal_pos.mpr (abs_pos.mpr hn)
  rw [area_rad]
  exact ⟨le_antisymm (sSup_le fun _ hr => ((step_legal hy).mp hr).2)
    (le_sSup ((step_legal hy).mpr ⟨⟨hp,ENNReal.ofReal_lt_top⟩,le_rfl⟩)),hp⟩

theorem step_uniform : uniform (line id) (line id) (run step).func (area punct) (area punct) = 0 := by
  rw [area_uniform]
  apply zero_tests
  intro t ht
  let a := min 1 (t/2)
  have hp : 0 < a := lt_min (by norm_num) (by linarith)
  have ha : a ∈ punct := Or.inr ⟨hp,min_le_left _ _⟩
  have hr := (step_radius ha).1
  rw [area_rad,abs_of_pos hp] at hr
  exact (uniform_at punct step ha).trans_lt (hr ▸
    (ENNReal.ofReal_lt_ofReal_iff ht).mpr ((min_le_right _ _).trans_lt (by linarith)))

def floorF (x : ℝ) := (⌊x⌋ : ℝ)

theorem interval_diam {a c : ℝ} (h : a ≤ c) :
    diameter usual (Icc a c) = ENNReal.ofReal (c-a) := by
  apply le_antisymm
  · apply diameter_le.mpr
    intro x hx y hy
    apply ENNReal.ofReal_le_ofReal
    change |x-y| ≤ c-a
    exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2],by linarith [hx.1,hx.2,hy.1,hy.2]⟩
  · have hh := le_diameter (p := usual) (U := Icc a c) (right_mem_Icc.mpr h) (left_mem_Icc.mpr h)
    simpa [usual,realDist,abs_of_nonneg (sub_nonneg.mpr h)] using hh

theorem pair_diam {a c : ℝ} (h : a ≤ c) :
    diameter usual {a,c} = ENNReal.ofReal (c-a) := by
  apply le_antisymm
  · rw [← interval_diam h]
    exact diameter_le.mpr fun x hx y hy => le_diameter
      ((show ({a,c} : Set ℝ) ⊆ Icc a c by rintro z (rfl | hz); exact ⟨le_rfl,h⟩; rw [show z = c from hz]; exact ⟨h,le_rfl⟩) hx)
      ((show ({a,c} : Set ℝ) ⊆ Icc a c by rintro z (rfl | hz); exact ⟨le_rfl,h⟩; rw [show z = c from hz]; exact ⟨h,le_rfl⟩) hy)
  · have hh := le_diameter (p := usual) (U := {a,c}) (x := c) (y := a) (by simp) (by simp)
    simpa [usual,realDist,abs_of_nonneg (sub_nonneg.mpr h)] using hh

theorem scale_counter : diameter (line id) (area ({0} : Set ℝ)) = 0 ∧
    diameter (line id) (area ({0,1} : Set ℝ)) = 1 ∧
    diameter (line id) (area ({0} : Set ℝ)) < 1/2 ∧
    1/2 ≤ diameter (line id) (area ({0,1} : Set ℝ)) := by
  have ha := pair_diam (a := 0) (c := 1) (by norm_num)
  have hb := pair_diam (a := 0) (c := 0) le_rfl
  norm_num at ha hb
  simp only [area_diam,ha,hb]
  norm_num

theorem floor_cross {a c : ℝ} (ha : a < 1) (hc : 1 ≤ c) :
    uniform usual usual floorF (Icc a c) (Icc a c) = 0 := by
  apply zero_tests
  intro t ht
  let δ := min (min (1-a) (1/2)) (t/2)
  have hp : 0 < δ := lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  have h₁ : δ ≤ 1-a := (min_le_left _ _).trans (min_le_left _ _)
  have h₂ : δ ≤ 1/2 := (min_le_left _ _).trans (min_le_right _ _)
  have h₃ : δ < t := (min_le_right _ _).trans_lt (by linarith)
  have hx : 1-δ ∈ Icc a c := ⟨by linarith,by linarith⟩
  have hy : 1 ∈ Icc a c := ⟨ha.le,hc⟩
  have hz : ⌊1-δ⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
  have hs : 0 < usual (floorF 1) (floorF (1-δ)) := by norm_num [floorF,hz,usual,realDist]
  have hh := positive_sep (p := usual) hy hx hs
  apply hh.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff ht).mpr
  simpa [abs_of_pos hp] using h₃

def floorData (S : Set ℝ) :=
  (diameter (line id) (area S), uniform (line id) (line id) (run floorF).func (area S) (area S))
def floorType (S : Set ℝ) := bits (floorData S).1 (floorData S).2 1 1

theorem floor_model (S : Set ℝ) : ExtendedPseudoMetric _ none (line id) ∧
    area S ⊆ dom (run floorF) := ⟨line_metric _,area_dom _ _⟩

theorem floor_half : floorData (Icc 0 (1/2)) = (1/2,⊤) ∧ floorType (Icc 0 (1/2)) = (true,true) := by
  have H : Const usual floorF (Icc 0 (1/2)) := by
    intro x hx y hy
    have z (v : ℝ) (hv : v ∈ Icc 0 (1/2)) : ⌊v⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨hv.1,by linarith [hv.2]⟩
    simp [usual,realDist,floorF,z _ hx,z _ hy]
  have h := (const_top (p := usual) H).2
  norm_num [floorType,floorData,area_diam,area_uniform,interval_diam (by norm_num : (0:ℝ) ≤ 1/2),h,bits,ENNReal.ofReal_div_of_pos]

theorem floor_narrow : floorData (Icc (9/10) (11/10)) = (1/5,0) ∧
    floorType (Icc (9/10) (11/10)) = (true,false) := by
  norm_num [floorType,floorData,area_diam,area_uniform,
    interval_diam (by norm_num : (9/10:ℝ) ≤ 11/10),
    floor_cross (by norm_num : (9/10:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 11/10),
    bits,ENNReal.ofReal_div_of_pos]

theorem floor_pair : floorData {0,2} = (2,2) ∧ floorType {0,2} = (false,true) ∧
    ¬ Const (line id) (run floorF).func (area {0,2}) := by
  have lo : 2 ≤ uniform usual usual floorF {0,2} {0,2} := by
    apply le_uniform.mpr
    norm_num [usual,realDist,floorF]
  have hi := positive_sep (p := usual) (U := ({0,2} : Set ℝ)) (x := 0) (y := 2)
    (by simp) (by simp) (by norm_num [usual,realDist,floorF] : 0 < usual (floorF 0) (floorF 2))
  have eq : uniform usual usual floorF {0,2} {0,2} = 2 :=
    le_antisymm (by simpa [usual,realDist] using hi) lo
  have hn : ¬ Const (line id) (run floorF).func (area {0,2}) := by
    intro h
    have := h (pt 0) (some_area.mpr (by simp)) (pt 2) (some_area.mpr (by simp))
    norm_num [pt,floorF] at this
  norm_num [floorData,floorType,area_diam,area_uniform,pair_diam (by norm_num : (0:ℝ) ≤ 2),
    eq,bits,hn]

theorem floor_wide : floorData (Icc 0 2) = (2,0) ∧ floorType (Icc 0 2) = (false,false) := by
  norm_num [floorType,floorData,area_diam,area_uniform,interval_diam (by norm_num : (0:ℝ) ≤ 2),
    floor_cross (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 2),bits]

theorem floor_counter : 1 ≤ (floorData {0,2}).2 ∧ ¬ Const (line id) (run floorF).func (area {0,2}) :=
  ⟨by rw [floor_pair.1]; norm_num,floor_pair.2.2⟩

end
end C3
```

```lean filename=FiniteExamples.lean
import RealExamples
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

variable {p : D X} {U : Set X} {e : ENNReal}

theorem center_one {c : X} (hc : c ∈ U) (near : ∀ x ∈ U, p x c < e) : cov p e U = 1 := by
  have h : InternalEpsilonNet p e U {c} :=
    ⟨by simpa using hc, fun x hx => ⟨c,Finset.mem_singleton_self c,near x hx⟩⟩
  exact le_antisymm (by simpa using net_bound h) (one_le_covering_number_of_nonempty _ _ _ ⟨c,hc⟩)

theorem center_two {a b : X} (ha : a ∈ U) (hb : b ∈ U)
    (cover : ∀ x ∈ U, p x a < e ∨ p x b < e)
    (far : ∀ c ∈ U, ∃ x ∈ U, e ≤ p x c) : cov p e U = 2 := by
  have net : InternalEpsilonNet p e U {a,b} := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hh
      · exact ha
      · exact (Finset.mem_singleton.mp hh) ▸ hb
    · intro x hx
      rcases cover x hx with h | h
      · exact ⟨a,by simp,h⟩
      · exact ⟨b,by simp,h⟩
  apply le_antisymm
  · exact (net_bound net).trans (by exact_mod_cast Finset.card_le_two)
  · refine le_iInf fun S => le_iInf fun hs => ?_
    obtain ⟨c,hc,_⟩ := hs.2 a ha
    obtain ⟨x,hx,hfar⟩ := far c (hs.1 hc)
    obtain ⟨z,hz,hh⟩ := hs.2 x hx
    have hn : z ≠ c := fun he => (he ▸ hh).not_ge hfar
    exact_mod_cast (show 2 ≤ S.card from Finset.one_lt_card.mpr ⟨z,hz,c,hc,hn⟩)

theorem isolated_cover {S : Finset X} (he : 0 < e) (self : ∀ x ∈ S, p x x = 0)
    (far : ∀ x ∈ S, ∀ y ∈ S, p x y < e → x = y) : cov p e (S : Set X) = S.card := by
  have net : InternalEpsilonNet p e (S : Set X) S :=
    ⟨Subset.rfl,fun x hx => ⟨x,hx,(self x hx).symm ▸ he⟩⟩
  apply le_antisymm (net_bound net)
  refine le_iInf fun T => le_iInf fun ht => ?_
  have h : S ⊆ T := by
    intro x hx
    obtain ⟨y,hy,hh⟩ := ht.2 x hx
    exact (far x hx y (ht.1 hy) hh).symm ▸ hy
  exact_mod_cast Finset.card_le_card h

theorem step_two {τ : ENNReal} (hτ : PosFin τ) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
    ENNReal.ofReal (2*a) < τ ∧ {pt (-a),pt a} ⊆ area punct ∧
    cov (line id) τ {pt (-a),pt a} = 1 ∧
    cov (line id) (1/2) ((run step).func '' {pt (-a),pt a}) = 2 := by
  let a := min 1 (τ.toReal / 4)
  have ht := ENNReal.toReal_pos hτ.1.ne' hτ.2.ne
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha' : a ≤ 1 := min_le_left _ _
  have hb : a ≤ τ.toReal / 4 := min_le_right _ _
  have hh : ENNReal.ofReal (2*a) < τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hτ.2.ne).mpr (by linarith)
  refine ⟨a,ha,ha',hh,?_,?_,?_⟩
  · simp only [Set.insert_subset_iff,Set.singleton_subset_iff,some_area]
    exact ⟨Or.inl ⟨by linarith,by linarith⟩,Or.inr ⟨ha,ha'⟩⟩
  · apply center_one (c := pt (-a)) (by simp)
    simp [pt, ← two_mul, sub_neg_eq_add, hτ.1, abs_of_nonneg (by positivity : 0 ≤ 2*a)]
    simpa using hh
  · have hI : (run step).func '' {pt (-a),pt a} = {pt 0,pt 1} := by
      simp [pt,step,neg_lt_zero.mpr ha,ha.not_gt,image_insert_eq]
    rw [hI]
    apply center_two (a := pt 0) (b := pt 1) (by simp) (by simp)
    · norm_num [pt]
    · norm_num [pt]

def affine := run (fun x : ℝ => 2*x-1)
def pair01 : Set (Option ℝ) := {pt 0,pt 1}
abbrev magnitude := line abs
theorem affine_values :
    affine.func (pt 0) = pt (-1) ∧ affine.func (pt 1) = pt 1 ∧
    (affine * affine).func (pt 0) = pt (-3) ∧ (affine * affine).func (pt 1) = pt 1 := by
  change _ ∧ _ ∧ affine.func (affine.func (pt 0)) = _ ∧ affine.func (affine.func (pt 1)) = _
  norm_num [affine,pt]

theorem affine_first : ExtendedPseudoMetric _ none magnitude ∧ pair01 ⊆ dom affine ∧
    fiber magnitude affine.func pair01 (affine.func (pt 0)) = pair01 ∧
    Const magnitude affine.func pair01 := by
  have h : Const magnitude affine.func pair01 := by norm_num [Const,pair01,affine,pt]
  refine ⟨line_metric _,?_,const_full h (by simp [pair01]),h⟩
  norm_num [Set.subset_def,pair01,dom,affine,pt]
  simp

theorem affine_second : pair01 ⊆ dom (affine * affine) ∧
    fiber magnitude (affine * affine).func pair01 ((affine * affine).func (pt 0)) = {pt 0} ∧
    Active magnitude (affine * affine).func pair01 := by
  obtain ⟨_,_,h0,h1⟩ := affine_values
  have hc : ¬ Const magnitude (affine * affine).func pair01 := by
    intro h
    have := h _ (show pt 0 ∈ pair01 by simp [pair01]) _ (show pt 1 ∈ pair01 by simp [pair01])
    norm_num [h0,h1,pt] at this
  have hi : ¬ Ident magnitude (affine * affine).func pair01 := by
    intro h
    have := h.2 _ (show pt 0 ∈ pair01 by simp [pair01])
    norm_num [h0,pt] at this
  refine ⟨?_,?_,hc,hi⟩
  · norm_num [Set.subset_def,pair01,dom,h0,h1]
    simp [pt]
  · ext x
    constructor
    · rintro ⟨hx,hz⟩
      rcases (show x = pt 0 ∨ x = pt 1 from hx) with rfl | rfl
      · rfl
      · norm_num [h0,h1,pt] at hz
    · rintro rfl
      exact ⟨by simp [pair01],(line_metric abs).dist_self _⟩

theorem constant_twice (F : Op (none : Option ℝ)) (c : ℝ) (h : ∀ x ∈ pair01, F.func x = pt c) :
    (∀ x ∈ pair01, (F*F).func x = F.func (pt c)) ∧
    (pair01 ⊆ dom (F*F) ↔ F.func (pt c) ≠ none) ∧
    (F.func (pt c) = none → Disjoint pair01 (dom (F*F))) ∧
    (F.func (pt c) ≠ none → ∀ z, fiber magnitude (F*F).func pair01 z = pair01 ∨
       fiber magnitude (F*F).func pair01 z = ∅) := by
  have hh (x) (hx : x ∈ pair01) := congrArg F.func (h x hx)
  refine ⟨hh,⟨fun hd => (hh _ (by simp [pair01] : pt 0 ∈ pair01)) ▸
    hd (by simp [pair01] : pt 0 ∈ pair01),fun hn x hx hbot => hn ((hh x hx).symm.trans hbot)⟩,?_,?_⟩
  · intro hn
    exact Set.disjoint_left.mpr fun x hx hd => hd ((hh x hx).trans hn)
  · intro _ z
    by_cases hz : magnitude (F.func (pt c)) z = 0
    · left
      exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx,(hh x hx).symm ▸ hz⟩)
    · right
      exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => hz ((hh x hx.1) ▸ hx.2)

def transF := run (fun x : ℝ => x+1)
def fourMag : Set (Option ℝ) := {pt (-3),pt (-2),pt 0,pt 2}

theorem fiber_insert (p : D X) (f : X → X) (U : Set X) (a z : X) :
    fiber p f (insert a U) z =
      (if p (f a) z = 0 then insert a (fiber p f U z) else fiber p f U z) := by
  ext x
  by_cases h : p (f a) z = 0 <;> simp [fiber,h] <;> grind

theorem fiber_single (p : D X) (f : X → X) (a z : X) :
    fiber p f {a} z = (if p (f a) z = 0 then {a} else ∅) := by
  ext x
  by_cases h : p (f a) z = 0 <;> simp [fiber,h] <;> grind

theorem translate_blocks : ExtendedPseudoMetric _ none magnitude ∧ fourMag ⊆ dom transF ∧
    blocks magnitude id fourMag = {{pt (-3)},{pt (-2),pt 2},{pt 0}} ∧
    blocks magnitude transF.func fourMag = {{pt (-3)},{pt (-2),pt 0},{pt 2}} := by
  refine ⟨line_metric _,?_,?_,?_⟩
  · norm_num [fourMag,Set.subset_def,dom,transF,pt]
    simp
  · norm_num [blocks,fourMag,pt,fiber_insert,fiber_single,image_insert_eq,Set.insert_comm]
    ext z
    simp
    tauto
  · norm_num [blocks,fourMag,pt,transF,fiber_insert,fiber_single,image_insert_eq,Set.insert_comm]
    ext z
    simp [Set.pair_comm]

theorem threeHalves_gt_one : (1 : ENNReal) < 3/2 := by
  apply (scaled_lt (L := 2) ⟨by norm_num,by norm_num⟩).mpr
  norm_num

theorem threeHalves_le_two : (3/2 : ENNReal) ≤ 2 := by
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
  norm_num

theorem translate_cover : cov magnitude (3/2) fourMag = 2 ∧
    cov magnitude (3/2) (transF.func '' fourMag) = 1 ∧
    ∃ h, delta magnitude magnitude transF.func fourMag (3/2) h = 1 := by
  have hi : cov magnitude (3/2) fourMag = 2 := by
    apply center_two (a := pt (-2)) (b := pt 0) (by simp [fourMag]) (by simp [fourMag])
    · norm_num [fourMag,pt,threeHalves_gt_one,threeHalves_le_two,threeHalves_le_two.trans (by norm_num : (2:ENNReal) ≤ 3)]
    · norm_num [fourMag,pt,threeHalves_gt_one,threeHalves_le_two,threeHalves_le_two.trans (by norm_num : (2:ENNReal) ≤ 3)]
  have ho : cov magnitude (3/2) (transF.func '' fourMag) = 1 := by
    apply center_one (c := pt (-2))
    · norm_num [fourMag,pt,transF,image_insert_eq,threeHalves_gt_one]
    · norm_num [fourMag,pt,transF,image_insert_eq,threeHalves_gt_one]
  refine ⟨hi,ho,Or.inr (ho ▸ ENNReal.one_lt_top),?_⟩
  change log2_ereal (cov magnitude (3/2) fourMag) - log2_ereal (cov magnitude (3/2) _) = 1
  rw [hi,ho]
  norm_num [log2_ereal,Real.logb_self_eq_one]

end
end C3
```

```lean filename=Rearrangement.lean
import FiniteExamples
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

namespace Rearrange
def U : Set (Option ℝ) := {pt 0,pt 1,pt 2,pt 3}
def perm (x : Option ℝ) := if x = pt 1 then pt 3 else if x = pt 2 then pt 1 else
  if x = pt 3 then pt 2 else pt 0
def restrictOp (v : Option ℝ → Option ℝ) : Op (none : Option ℝ) :=
  ⟨fun x => if x ∈ U then v x else none,by simp [U,pt]⟩
def F := restrictOp id
def G := restrictOp perm
abbrev p := line id

theorem values :
    (∀ x ∈ U, F.func x = x) ∧ G.func (pt 0) = pt 0 ∧ G.func (pt 1) = pt 3 ∧
    G.func (pt 2) = pt 1 ∧ G.func (pt 3) = pt 2 ∧
    (∀ x ∉ U, F.func x = none ∧ G.func x = none) := by
  norm_num [F,G,restrictOp,U,perm,pt]
  grind

theorem images : dom F = U ∧ dom G = U ∧ F.func '' U = U ∧ G.func '' U = U := by
  obtain ⟨hf,h0,h1,h2,h3,hout⟩ := values
  have dm (H : Op (none : Option ℝ)) (h : ∀ x ∈ U, H.func x ≠ none)
      (ho : ∀ x ∉ U, H.func x = none) : dom H = U := by
    ext x
    change H.func x ≠ none ↔ _
    exact ⟨fun hh => by_contra fun hn => hh (ho x hn),h x⟩
  refine ⟨dm F ?_ (fun x hx => (hout x hx).1),dm G ?_ (fun x hx => (hout x hx).2),?_,?_⟩
  · simp [U,F,restrictOp,pt]
  · simp [U,h0,h1,h2,h3,pt]
  · simpa using (Set.EqOn.image_eq (show Set.EqOn F.func id U from hf))
  · rw [U]
    simp only [image_insert_eq,image_singleton,h0,h1,h2,h3]
    ext x
    simp only [mem_insert_iff,mem_singleton_iff]
    tauto

theorem cover (e : ENNReal) (he : PosFin e) :
    cov p e U = if e ≤ 1 then 4 else if e ≤ 2 then 2 else 1 := by
  by_cases h1 : e ≤ 1
  · rw [if_pos h1]
    let S : Finset (Option ℝ) := {pt 0,pt 1,pt 2,pt 3}
    have hs : (S : Set (Option ℝ)) = U := by simp [S,U]
    have hh : ∀ x ∈ S, ∀ y ∈ S, p x y < e → x = y := by
      have h2 : e ≤ 2 := h1.trans (by norm_num)
      have h3 : e ≤ 3 := h1.trans (by norm_num)
      norm_num [S,pt,not_lt_of_ge h1,not_lt_of_ge h2,not_lt_of_ge h3]
    rw [← hs,isolated_cover he.1 (fun x _ => (line_metric id).dist_self x) hh]
    norm_num [S,pt,Finset.card_insert_of_notMem]
  · rw [if_neg h1]
    have he1 := lt_of_not_ge h1
    by_cases h2 : e ≤ 2
    · rw [if_pos h2]
      have h3 : e ≤ 3 := h2.trans (by norm_num)
      apply center_two (a := pt 1) (b := pt 2) (by simp [U]) (by simp [U])
      · norm_num [U,pt,he1,he.1]
      · norm_num [U,pt,h2,h3]
    · rw [if_neg h2]
      have he2 := lt_of_not_ge h2
      apply center_one (c := pt 1) (by simp [U])
      norm_num [U,pt,he1,he2,he.1]

theorem midpoint : pt (3/2) ∉ U ∧ ∀ x ∈ U, p x (pt (3/2)) < 7/4 := by
  have h : ENNReal.ofReal (3/2) < (7/4 : ENNReal) := by
    have hh := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 7/4)).mpr (by norm_num : (3/2:ℝ) < 7/4)
    norm_num [ENNReal.ofReal_div_of_pos] at hh ⊢
    exact hh
  have h' : ENNReal.ofReal (1/2) < (7/4 : ENNReal) :=
    (ENNReal.ofReal_le_ofReal (by norm_num : (1/2:ℝ) ≤ 3/2)).trans_lt h
  norm_num [U,pt,ENNReal.ofReal_div_of_pos] at *
  exact ⟨h,h',h⟩

theorem image_delta (e : ENNReal) (he : PosFin e) :
    ∀ H ∈ ({F,G} : Set (Op (none : Option ℝ))), H.func '' U = U ∧
    cov p e (H.func '' U) = cov p e U ∧ ∃ hw, delta p p H.func U e hw = 0 := by
  have hu : U.Nonempty := ⟨pt 0,by simp [U]⟩
  have finite : cov p e U < ⊤ := finite_cover (line_metric id).dist_self
    (by simp [U]) he.1
  obtain ⟨a,ha⟩ := finite_entropy hu finite
  intro H hH
  have hI : H.func '' U = U := by
    rcases (show H = F ∨ H = G from hH) with rfl | rfl
    · exact images.2.2.1
    · exact images.2.2.2
  exact ⟨hI,by rw [hI],Or.inl finite,by rw [delta,hI,ha,← EReal.coe_sub,sub_self,EReal.coe_zero]⟩

def Lip (H : Op (none : Option ℝ)) (L : ENNReal) :=
  ∀ x ∈ U, ∀ y ∈ U, p (H.func x) (H.func y) ≤ L * p x y

theorem optimal : IsLeast {L | Lip F L} 1 ∧ IsLeast {L | Lip G L} 3 := by
  obtain ⟨hf,h0,h1,h2,h3,_⟩ := values
  have hu0 : pt 0 ∈ U := by simp [U]
  have hu1 : pt 1 ∈ U := by simp [U]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro x hx y hy
    simp [hf x hx,hf y hy]
  · intro L hL
    have hh := hL _ hu0 _ hu1
    simpa [hf _ hu0,hf _ hu1,pt] using hh
  · change Lip G 3
    norm_num [Lip,U,h0,h1,h2,h3,pt]
  · intro L hL
    have hh := hL _ hu0 _ hu1
    simpa [h0,h1,pt] using hh

theorem bounds :
    cov p (7/4) (F.func '' U) ≤ cov p ((7/4)/1) U ∧
    cov p (7/4) (G.func '' U) ≤ cov p ((7/4)/3) U ∧
    cov p (7/4) (F.func '' U) = 2 ∧ cov p ((7/4)/1) U = 2 ∧
    cov p (7/4) (G.func '' U) = 2 ∧ cov p ((7/4)/3) U = 4 := by
  have h₁ : PosFin 1 := ⟨by norm_num,by norm_num⟩
  have h₃ : PosFin 3 := ⟨by norm_num,by norm_num⟩
  have he : PosFin (7/4) := div_pf ⟨by norm_num,by norm_num⟩ ⟨by norm_num,by norm_num⟩
  have ha : (1:ENNReal) < 7/4 := (scaled_lt ⟨by norm_num,by norm_num⟩).mpr (by norm_num)
  have hb : (7/4:ENNReal) ≤ 2 := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc : (7/4:ENNReal)/3 ≤ 1 := (ENNReal.div_le_iff h₃.1.ne' h₃.2.ne).mpr
    (by simpa using hb.trans (by norm_num : (2:ENNReal) ≤ 3))
  refine ⟨lip_cover optimal.1.1 h₁,lip_cover optimal.2.1 h₃,?_⟩
  simp [images.2.2.1,images.2.2.2,cover _ he,cover _ (div_pf he h₃),ha.not_ge,hb,hc]
end Rearrange

end
end C3
```

```lean filename=Chapter.lean
import Rearrangement
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

variable {d : I → D X} {F G : Op b} {U : Set X}

def components (d : I → D X) (F : Op b) (U : Set X) (_ : U ⊆ dom F) :
    Set I × Set I × Set I :=
  ({i | Const (d i) F.func U},{i | Ident (d i) F.func U},{i | Active (d i) F.func U})

theorem component_sets (h : U ⊆ dom F) :
    (components d F U h).2.1 = {i | i ∉ (components d F U h).1 ∧
      ∀ x ∈ U, d i (F.func x) x = 0} ∧
    (components d F U h).2.2 = ((components d F U h).1 ∪ (components d F U h).2.1)ᶜ := by
  exact ⟨rfl,by ext i; exact not_or.symm⟩

theorem comp_domains (h : U ⊆ dom (G * F)) : U ⊆ dom F ∧ F.func '' U ⊆ dom G := by
  constructor
  · intro x hx hh
    apply h hx
    change G.func (F.func x) = b
    rw [hh,G.preserves_bot]
  · rintro _ ⟨x,hx,rfl⟩
    exact h hx

def stages : List (Op b) → Set X → List (Op b × Set X)
  | [], _ => []
  | F :: fs, A => (F,A) :: stages fs (F.func '' A)

theorem stages_spec (fs : List (Op b)) (p : D X) : stepActive p fs U ↔
    ∃ stage ∈ stages fs U, Active p stage.1.func stage.2 := by
  induction fs generalizing U with
  | nil => simp [stepActive,stages]
  | cons F tail ih => simp [stages, stepActive, ih]

theorem valid_stages (fs : List (Op b)) (hu : U ⊆ dom (OperatorChain fs.reverse)) :
    ∀ s ∈ stages fs U, s.2 ⊆ dom s.1 := by
  induction fs generalizing U with
  | nil => simp [stages]
  | cons F fs ih =>
    rw [List.reverse_cons, operator_chain_eq_prod, List.prod_append, List.prod_singleton,
      ← operator_chain_eq_prod] at hu
    obtain ⟨h₁,h₂⟩ := comp_domains hu
    simpa [stages] using And.intro h₁ (ih h₂)

theorem fiber_spec (J : Set I) (y x : X) : x ∈ fiber (subD d J) F.func U y ↔
    x ∈ U ∧ ∀ j ∈ J, d j (F.func x) y = 0 := and_congr_right fun _ => sub_zero

theorem finite_max [Finite I] {J : Set I} (hj : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subD d J x y = d j x y ∧ ∀ k ∈ J, d k x y ≤ d j x y := by
  letI : Nonempty J := hj.to_subtype
  obtain ⟨j,h⟩ := exists_eq_ciSup_of_finite (f := fun j : J => d j.val x y)
  exact ⟨j,j.2,h.symm,fun k hk => h ▸ le_iSup (fun j : J => d j.val x y) (⟨k,hk⟩ : J)⟩

theorem fiber_absent (p : D X) {z : X} (h : ∀ y ∈ F.func '' U, 0 < p y z) :
    fiber p F.func U z = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx => (h _ ⟨x,hx.1,rfl⟩).ne' hx.2

theorem relations_on (x y : X) :
    (∃ u v : U, u.val = x ∧ v.val = y ∧ (u,v) ∈ eqRel U F.func) ↔
      x ∈ U ∧ y ∈ U ∧ F.func x = F.func y := by
  constructor
  · rintro ⟨u,v,rfl,rfl,h⟩; exact ⟨u.2,v.2,h⟩
  · rintro ⟨hx,hy,h⟩; exact ⟨⟨x,hx⟩,⟨y,hy⟩,rfl,rfl,h⟩

theorem zero_relations_on (x y : X) :
    (∃ u v : U, u.val = x ∧ v.val = y ∧ (u,v) ∈ zeroRel d U F.func) ↔
      x ∈ U ∧ y ∈ U ∧ GaugeZeroRelated d (F.func x) (F.func y) := by
  constructor
  · rintro ⟨u,v,rfl,rfl,h⟩; exact ⟨u.2,v.2,h⟩
  · rintro ⟨hx,hy,h⟩; exact ⟨⟨x,hx⟩,⟨y,hy⟩,rfl,rfl,h⟩

theorem rad_empty {p q : D X} {y : X} (h : legal p q F.func U y = ∅) :
    rad p q F.func U y = 0 := by simp [rad,h]

theorem matrix_spec {i j : I} :
    N d F.func U j i = ⨅ y : U, rad (d i) (d j) F.func U y := rfl

theorem radius_notation (i j : I) :
    rad (d i) (subD d {j}) F.func U = rad (d i) (d j) F.func U ∧
    uniform (d i) (subD d {j}) F.func U U = N d F.func U j i := by
  simp only [subD,subfamily_pseudometric_singleton,N,and_self]

theorem area_legal {p q : D X} {f : X → X} {S : Set X} {y : X} :
    legal (liftDist p) (liftDist q) (run f).func (area S) (some y) = legal p q f S y := by
  ext r
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro _
  constructor
  · intro h x hx
    exact h (some x) (some_area.mpr hx)
  · rintro h _ ⟨x,hx,rfl⟩
    exact h x hx

theorem four_types (a n t u : ENNReal) : ∃! v : Bool × Bool,
    (v.1 = true ↔ a < t) ∧ (v.2 = true ↔ u ≤ n) := by
  refine ⟨bits a n t u,by simp [bits],?_⟩
  rintro ⟨v,w⟩ hw
  cases v <;> cases w <;> simp_all [bits]

def mappingEntropy (d : I → D X) (F : Op b) (U : Set X) (_ : U.Nonempty) (_ : U ⊆ dom F)
    (J K : Set I) (_ : J.Nonempty) (_ : K.Nonempty) (e : ENNReal) (_ : PosFin e)
    (hw : Defined (subD d J) (subD d K) F.func U e) :=
  delta (subD d J) (subD d K) F.func U e hw

theorem mapping_spec (hu : U.Nonempty) (hdom : U ⊆ dom F) {J K : Set I} (hj : J.Nonempty)
    (hk : K.Nonempty) {e : ENNReal} (he : PosFin e) (hw) :
    mappingEntropy d F U hu hdom J K hj hk e he hw =
    subfamily_metric_entropy d J e U - subfamily_metric_entropy d K e (F.func '' U) := rfl

theorem coverage_meaning (p : D X) (e : ENNReal) (A : Set X) :
    ((∃ S, InternalEpsilonNet p e A S) → ∃ S, InternalEpsilonNet p e A S ∧
      cov p e A = S.card ∧ ∀ T, InternalEpsilonNet p e A T → S.card ≤ T.card) ∧
    (cov p e A = ⊤ ↔ ¬ ∃ S, InternalEpsilonNet p e A S) ∧
    cov p e ∅ = 0 ∧ ent p e A = log2_ereal (cov p e A) :=
  ⟨covering_number_attained p e A,covering_number_eq_top_iff p e A,covering_number_empty p e,rfl⟩

theorem delta_signs {p q : D X} {e : ENNReal} (hu : U.Nonempty) (hw : Defined p q F.func U e) :
    let a := ent p e U
    let b := ent q e (F.func '' U)
    (0 < delta p q F.func U e hw ↔ b < a) ∧
    (delta p q F.func U e hw < 0 ↔ a < b) ∧
    (delta p q F.func U e hw = 0 ↔ a = b) := by
  dsimp only
  have ht : ent p e U ≠ ⊤ ∨ ent q e (F.func '' U) ≠ ⊤ := by
    rcases hw with h | h
    · obtain ⟨a,ha⟩ := finite_entropy hu h; simp [ha]
    · obtain ⟨a,ha⟩ := finite_entropy (hu.image _) h; simp [ha]
  have hb : ent p e U ≠ ⊥ :=
    ((show (⊥ : EReal) < 0 from EReal.bot_lt_zero).trans_le (metric_entropy_nonneg _ _ _ hu)).ne'
  have hp := @EReal.sub_pos (ent p e U) (ent q e (F.func '' U))
  have hn := EReal.sub_neg ht (Or.inl hb)
  refine ⟨hp,hn,?_⟩
  change _ - _ = 0 ↔ _
  exact ⟨fun h => le_antisymm (le_of_not_gt fun hl => (hp.mpr hl).ne' h)
    (le_of_not_gt fun hl => (hn.mpr hl).ne h),fun h => by
      rw [← h] at ht ⊢
      exact EReal.sub_self (ht.elim id id) hb⟩

theorem swap_strict :
    let act (f : Option Bool → Option Bool) (U : Set (Option Bool)) : Set Unit :=
      { _i | Active Swap.p f U }
    let ident (f : Option Bool → Option Bool) (U : Set (Option Bool)) : Set Unit :=
      { _i | Ident Swap.p f U }
    act (Swap.F * Swap.F).func Swap.U ⊂ act Swap.F.func Swap.U ∪ act Swap.F.func (Swap.F.func '' Swap.U) ∧
    ident Swap.F.func Swap.U ∩ ident Swap.F.func (Swap.F.func '' Swap.U) ⊂ ident (Swap.F * Swap.F).func Swap.U := by
  obtain ⟨a,b,c,d⟩ := Swap.calc_swap
  simp [Swap.image_dom.2,a,b,c,d]

theorem seven_readings :
    Seven.p false (some 2) (some 3) = 0 ∧ Seven.p true (some 2) (some 3) = 1 ∧
    Seven.p false (some 4) (some 5) = 1 := by norm_num [Seven.p,Seven.readout,liftDist,discrete,Fin.ext_iff]

theorem floor_type_spec {S : Set ℝ} (hs : S.Nonempty) :
    floorType S = channel (diamScale (fun _ : Unit => line id)) ⟨area S,hs.image some⟩
      (fun _ : Unit => line id) (run floorF).func 1 1 () () := rfl

theorem subfamily_partition (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    {J : Set I} (hj : J.Nonempty) :
    (∀ S ∈ blocks (subD d J) F.func U, S.Nonempty) ∧
    ⋃₀ (blocks (subD d J) F.func U) = U ∧
    ∀ S ∈ blocks (subD d J) F.func U, ∀ T ∈ blocks (subD d J) F.func U,
      S = T ∨ Disjoint S T := by
  have h := subfamily_pseudometric_is_extended d J hj hd
  obtain ⟨ha,hb⟩ := fiber_cover (f := F.func) (U := U) h
  refine ⟨ha,hb,?_⟩
  rintro _ ⟨y,_,rfl⟩ _ ⟨z,_,rfl⟩
  exact fiber_disjoint h

theorem step_interval (y : ℝ) (hy : y ∈ punct) :
    legal (line id) (line id) (run step).func (area punct) (pt y) =
      Ioc 0 (ENNReal.ofReal |y|) := by
  rw [area_legal]
  ext r
  exact (step_legal hy).trans ⟨fun h => ⟨h.1.1,h.2⟩,
    fun h => ⟨⟨h.1,h.2.trans_lt ENNReal.ofReal_lt_top⟩,h.2⟩⟩

theorem scale_counter_domains :
    (area ({0} : Set ℝ)).Nonempty ∧ area ({0} : Set ℝ) ⊆ area ({0,1} : Set ℝ) ∧
    area ({0,1} : Set ℝ) ⊆ dom (run id) :=
  ⟨⟨pt 0,some_area.mpr rfl⟩, Set.image_mono (by simp),area_dom _ _⟩

theorem singleton_channel (i j : I) (e : ENNReal) :
    Defined (subD d {i}) (subD d {j}) F.func U e ↔ Defined (d i) (d j) F.func U e := by
  simp [subD,subfamily_pseudometric_singleton]

theorem singleton_delta (i j : I) (e : ENNReal)
    (hw : Defined (subD d {i}) (subD d {j}) F.func U e) :
    delta (subD d {i}) (subD d {j}) F.func U e hw =
    delta (d i) (d j) F.func U e ((singleton_channel i j e).mp hw) := by
  simp [delta,subD,subfamily_pseudometric_singleton]

theorem threshold_spec {S : Scale X I} (A : {A : Set X // A.Nonempty}) (_hA : A.val ⊆ dom F)
    {t u : ENNReal} (_ht : PosFin t) (_hu : PosFin u) (i j : I) :
    ((channel S A d F.func t u i j).1 = true ↔ S.val i A < t) ∧
    ((channel S A d F.func t u i j).2 = true ↔ u ≤ uniform (d i) (d j) F.func A A) := by
  simp [channel,bits,N]

theorem rad_notation {p q : D X} {y : X} {r : ENNReal} :
    r < rad p q F.func U y ↔ ∃ ρ, ρ ∈ legal p q F.func U y ∧ r < ρ := lt_sSup_iff

theorem zero_step (hd : ExtendedPseudoMetric X b (d i)) :
    ¬ Active (d i) (OperatorChain ([] : List (Op b))).func U :=
  chain_active hd []

theorem id_on_option (x : Option X) : (run id).func x = x := by cases x <;> rfl

theorem cut_alternatives {p q : D X} (hp : ExtendedPseudoMetric X b p)
    (hq : ExtendedPseudoMetric X b q) {x y : X} (hx : x ∈ U)
    (h : x ∈ fiber q F.func U (F.func y) ∨ p y x < rad p q F.func U y) :
    q (F.func y) (F.func x) = 0 := h.elim (fiber_cut hq) (point_cut hp hq hx)

theorem scalar_spec {H : Op (none : Option ℝ)} (hd : Rearrange.U ⊆ dom H) (L : ENNReal) :
    Rearrange.Lip H L ↔ HasScalarLipBound (fun _ : Unit => line id) H Rearrange.U () () L :=
  ⟨fun h => ⟨hd,h⟩,And.right⟩

theorem subfamily_constant_radii {J : Set I} (_hj : J.Nonempty) (_hu : U.Nonempty)
    (_hdom : U ⊆ dom F) (h : ∀ j ∈ J, Const (d j) F.func U) (i : I) :
    (∀ y ∈ U, rad (d i) (subD d J) F.func U y = ⊤) ∧
    uniform (d i) (subD d J) F.func U U = ⊤ := const_top (sub_const h)

end
end C3
```

```lean filename=Textbook.lean
import Chapter

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
variable {X I : Type} {b : X} {d : I → D X} {U : Set X} {F G : Op b}

theorem row_constraints [Fintype I] (_hU : U ⊆ dom F) {i : I} (h : Const (d i) F.func U)
    (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
    d i (F.func x) (F.func y) ≤ ∑ k, (0 : ENNReal)*d k x y ∧
    ∑ k, (0 : ENNReal)*d k x y = 0 :=
  ⟨zero_row h hx hy,by simp⟩

theorem composition_sets (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (hU : U ⊆ dom (G*F)) :
    let C := components d (G*F) U hU
    let A := components d F U (comp_domains hU).1
    let B := components d G (F.func '' U) (comp_domains hU).2
    C.2.2 ⊆ A.2.2 ∪ B.2.2 ∧ A.2.1 ∩ B.2.1 ⊆ C.2.1 :=
  ⟨fun i hi => comp_active (f := F.func) (g := G.func) (hd i) hi,
   fun i hi => comp_ident (f := F.func) (g := G.func) (hd i) hi.1 hi.2⟩

theorem chain_sets (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (fs : List (Op b))
    (hU : U ⊆ dom (OperatorChain fs.reverse)) :
    (components d (OperatorChain fs.reverse) U hU).2.2 ⊆
      ⋃ stage ∈ stages fs U, {i | Active (d i) stage.1.func stage.2} := by
  intro i hi
  obtain ⟨s,hs,h⟩ := (stages_spec fs (d i)).mp (chain_active (hd i) fs hi)
  exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨hs,h⟩⟩

def pointRadius (p q : D X) (F : Op b) (U : Set X) (_ : U ⊆ dom F) (y : U) :=
  rad p q F.func U y
def uniformRadius (p q : D X) (F : Op b) (A U : Set X) (_ : A.Nonempty)
    (_ : A ⊆ U) (_ : U ⊆ dom F) := uniform p q F.func A U

theorem radius_representations (p q : D X) {A : Set X} (ha : A.Nonempty) (h : A ⊆ U)
    (hU : U ⊆ dom F) :
    uniformRadius p q F A U ha h hU = ⨅ y : A, pointRadius p q F U hU ⟨y,h y.2⟩ := rfl

theorem matrix_composition (_hn : U.Nonempty) (_hU : U ⊆ dom (G*F)) (i j l : I) :
    ((∀ a ∈ F.func '' U, ∀ c ∈ F.func '' U, d l a c = 0 → d j (G.func a) (G.func c) = 0) →
       N d F.func U l i ≤ N d (G*F).func U j i) ∧
    (∀ L, PosFin L → (∀ x ∈ U, ∀ y ∈ U, d l (F.func x) (F.func y) ≤ L*d i x y) →
       N d G.func (F.func '' U) j l / L ≤ N d (G*F).func U j i) :=
  ⟨fun hz => comp_zero (f := F.func) (g := G.func) hz,
   fun _ hl h => comp_lip (f := F.func) (g := G.func) hl h⟩

theorem threshold_sets (S : Scale X I) (A : {A : Set X // A.Nonempty}) (_hA : A.val ⊆ dom F)
    {t u t' u' : ENNReal} (_ht : PosFin t) (_hu : PosFin u) (_ht' : PosFin t') (_hu' : PosFin u')
    (ht : t ≤ t') (hu : u ≤ u') :
    {ij : I × I | (channel S A d F.func t u ij.1 ij.2).1 = true} ⊆
      {ij | (channel S A d F.func t' u ij.1 ij.2).1 = true} ∧
    {ij : I × I | (channel S A d F.func t u' ij.1 ij.2).2 = true} ⊆
      {ij | (channel S A d F.func t u ij.1 ij.2).2 = true} :=
  ⟨fun _ => scale_threshold ht,fun _ => null_threshold hu⟩

theorem separation_witness (_hn : U.Nonempty) (_hU : U ⊆ dom F) (i j : I) {τ : ENNReal}
    (_ht : PosFin τ) (_small : N d F.func U j i < τ) (α : ENNReal) (_hα : PosFin α)
    (h₁ : N d F.func U j i < α) (_h₂ : α < τ) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, PosFin ε ∧ d i x y < α ∧ ε ≤ d j (F.func x) (F.func y) :=
  uniform_witness h₁

theorem cover_constraints (_hn : U.Nonempty) (_hU : U ⊆ dom F) (i j : I) {τ : ENNReal}
    (_ht : PosFin τ) (h : τ ≤ N d F.func U j i) {B : Set X} (hb : B ⊆ U) {ε : ENNReal}
    (he : PosFin ε) :
    (∀ x ∈ U, ball (d i) x τ ∩ U ⊆ fiber (d j) F.func U (F.func x)) ∧
    cov (d j) ε (F.func '' B) ≤ cov (d i) τ B ∧
    (B.Nonempty → ent (d j) ε (F.func '' B) ≤ ent (d i) τ B) :=
  ⟨fun _ hx => threshold_ball h hx,threshold_cover hb h he.1,fun _ => threshold_entropy hb h he.1⟩

theorem small_image (_hU : U ⊆ dom F) (hn : U.Nonempty) (i j : I) {t u : ENNReal}
    (_ht : PosFin t) (_hu : PosFin u) (h : diameter (d i) U < t) (hh : t ≤ u) :
    (u ≤ N d F.func U j i ↔ Const (d j) F.func U) ∧
    (u ≤ N d F.func U j i → ∀ e, PosFin e → cov (d j) e (F.func '' U) = 1) :=
  ⟨small_iff h hh,fun hr _ he => small_cover hn h hh hr he.1⟩

theorem distance_gap [Fintype I] {K : I → I → ENNReal} (hK : IsCoLipMatrix d F U K)
    {i j : I} (h : 0 < K i j) (hr : 0 < N d F.func U j i) :
    Disjoint ({0} : Set ENNReal) (Ici (N d F.func U j i)) ∧
    ∀ x ∈ U, ∀ y ∈ U, d i x y ∈ ({0} : Set ENNReal) ∪ Ici (N d F.func U j i) :=
  ⟨by simp [hr.not_ge],fun _ hx _ hy => uniform_gap hK h hx hy⟩

end
end C3
```

```toml filename=lakefile.toml
name = "mg_c003"
version = "0.1.1"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "Main"
roots = ["Main", "Textbook", "Chapter", "Components", "Factors", "Radii", "Entropy", "Models",
         "RealExamples", "FiniteExamples", "Rearrangement",
         "formal_oet.vol_01.ch_01_foundations.gauge_space",
         "formal_oet.vol_01.ch_01_foundations.operator_space",
         "formal_oet.vol_01.ch_01_foundations.metric_entropy",
         "formal_oet.vol_01.ch_02_operator_bounds.lip_matrix",
         "formal_oet.vol_01.ch_02_operator_bounds.decoupling",
         "formal_oet.vol_01.ch_02_operator_bounds.single_channel"]
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
      "url": "https://github.com/leanprover-community/mathlib4.git",
      "type": "git",
      "subDir": null,
      "scope": "",
      "rev": "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
      "name": "mathlib",
      "manifestFile": "lake-manifest.json",
      "inputRev": "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
      "inherited": false,
      "configFile": "lakefile.lean"
    }
  ],
  "name": "mg_c003",
  "lakeDir": ".lake"
}
```

```python filename=build.py
"""Build against the public package caches listed in the supplied environment.json."""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LEAN_COMMIT = "f72c35b3f637c8c6571d353742168ab66cc22c00"
MATHLIB_COMMIT = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"


def main():
    config = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "environment.json"
    env = json.loads(config.read_text())
    compiler = env["compiler"]
    version = subprocess.check_output([compiler, "--version"], text=True)
    if LEAN_COMMIT not in version or "4.29.1" not in version:
        raise ValueError(version)
    packages = env["public_packages"]
    mathlib = next(pkg for pkg in packages if pkg["name"] == "mathlib")
    if mathlib["revision"] != MATHLIB_COMMIT:
        raise ValueError(mathlib["revision"])

    output = ROOT / ".lake/build/lib/lean"
    search = [str(output), *(pkg["olean_root"] for pkg in packages)]
    child_env = dict(os.environ, LEAN_PATH=os.pathsep.join(search))
    built = set()

    def build(module):
        if module in built:
            return
        rel = Path(*module.split("."))
        source = ROOT / rel.with_suffix(".lean")
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                dep = line.split()[1]
                if not dep.startswith("Mathlib"):
                    build(dep)
        target = output / rel.with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        print(module, flush=True)
        subprocess.run([compiler, "-o", target, source], cwd=ROOT, env=child_env, check=True)
        built.add(module)

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
          "file": "Chapter.lean",
          "name": "C3.components"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.component_sets"
        },
        {
          "file": "Components.lean",
          "name": "C3.Const"
        },
        {
          "file": "Components.lean",
          "name": "C3.Ident"
        },
        {
          "file": "Components.lean",
          "name": "C3.Active"
        },
        {
          "file": "Components.lean",
          "name": "C3.partition"
        }
      ],
      "representation": "给定算子和合法限制域，三元组按常值、排除常值后的逐点零移、其余指标构成三个集合。partition 证明每个分量恰属一类，取 U=dom F 即全域情形。",
      "dependencies": []
    },
    {
      "id": "CH03-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.subD"
        },
        {
          "file": "Components.lean",
          "name": "C3.sub_zero"
        },
        {
          "file": "Components.lean",
          "name": "C3.fiber"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.fiber_spec"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.finite_max"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.fiber_absent"
        },
        {
          "file": "Components.lean",
          "name": "C3.blocks"
        }
      ],
      "representation": "fiber 对任意目标取 U 内输出零距的原像。对非空有限 J，subD 的上确界由分量取得，零值等价于逐分量零距。像目标经 Set.image 自动去重。",
      "dependencies": []
    },
    {
      "id": "CH03-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.eqRel"
        },
        {
          "file": "Factors.lean",
          "name": "C3.zeroRel"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.relations_on"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.zero_relations_on"
        },
        {
          "file": "Factors.lean",
          "name": "C3.zeroRel_fiber"
        },
        {
          "file": "Factors.lean",
          "name": "C3.imageSetoid"
        },
        {
          "file": "Factors.lean",
          "name": "C3.cls"
        },
        {
          "file": "Factors.lean",
          "name": "C3.finer"
        }
      ],
      "representation": "U×U 用子类型的积，两个 relations_on 定理给出到原空间中受限点对的对应。零距关系等价于全子族纤维成员关系。实际像上的 setoid、商类和关系包含分别表示像商及预序。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Textbook.lean",
          "name": "C3.pointRadius"
        },
        {
          "file": "Radii.lean",
          "name": "C3.legal"
        },
        {
          "file": "Radii.lean",
          "name": "C3.rad"
        },
        {
          "file": "Radii.lean",
          "name": "C3.legal_ball"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.rad_empty"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.rad_notation"
        }
      ],
      "representation": "合法参数是有限正 ENNReal，开球与 U 的交须包含于输出零距纤维。rad 取 sSup，空集取零，rad_notation 给出严格低于上确界的见证。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Textbook.lean",
          "name": "C3.uniformRadius"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.radius_representations"
        },
        {
          "file": "Radii.lean",
          "name": "C3.uniform"
        },
        {
          "file": "Radii.lean",
          "name": "C3.N"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.matrix_spec"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.radius_notation"
        }
      ],
      "representation": "uniform p q f A U 的下确界指标为基点子类型 A，球始终在 U 内评估。N 的参数先输出行 j 后输入列 i，取 A=U。单元素子族与单分量相同，取 U=dom F 即全域记法。",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.Scale"
        },
        {
          "file": "Radii.lean",
          "name": "C3.diameter"
        },
        {
          "file": "Radii.lean",
          "name": "C3.diamScale"
        },
        {
          "file": "Radii.lean",
          "name": "C3.bits"
        },
        {
          "file": "Radii.lean",
          "name": "C3.channel"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.threshold_spec"
        }
      ],
      "representation": "Scale 的定义域是非空子集，mono 表示逐分量包含单调性。diamScale 用点对上确界实现直径。有限正阈值下，两个布尔值分别表示输入尺度严格小于阈值、矩阵条目大于等于阈值。",
      "dependencies": [
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.internal_spec"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.coverage_meaning"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.cov"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.ent"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.TB"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.tb_spec"
        }
      ],
      "representation": "中心 Finset 包含在原集合中，严格距离不等式等价于内部开球覆盖。存在有限覆盖时得到最小基数，无覆盖时为顶，空集为零。熵是冻结的扩展二进制对数，全有界对每个有限正尺度量化。",
      "dependencies": []
    },
    {
      "id": "CH03-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.Defined"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.delta"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.mappingEntropy"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.mapping_spec"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.delta_cases"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.delta_signs"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.singleton_delta"
        }
      ],
      "representation": "mappingEntropy 要求非空合法域、两端非空子族、有限正精度及至少一端覆盖数有限。差值为输入熵减像熵；证得两种无穷分支、双有限分支、符号判据和单通道化简。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P01-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.zero_row"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.row_constraints"
        }
      ],
      "representation": "对任意受限点对，常值输出距离为零，以有限和表示的全零行同样为零。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.zero_entry"
        }
      ],
      "representation": "对存在正输入距离点对的任意源分量，把该见证和常值输出等式代入冻结的 co-Lip 条目判据。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.ident_dist"
        },
        {
          "file": "Components.lean",
          "name": "C3.zero_left"
        },
        {
          "file": "Components.lean",
          "name": "C3.zero_right"
        }
      ],
      "representation": "同一分量零距的两个点与第三点等距。对恒等分量分别替换两个端点得到所需等式，允许距离无穷。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P02-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.comp_active"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.comp_domains"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.composition_sets"
        }
      ],
      "representation": "复合有效蕴含内侧在 U 有效或外侧在 f 的实际像集有效。comp_domains 从复合域条件推出两步各自合法。",
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
          "file": "Components.lean",
          "name": "C3.stepActive"
        },
        {
          "file": "Components.lean",
          "name": "C3.chain_active"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.stages"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.stages_spec"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.valid_stages"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.zero_step"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.chain_sets"
        }
      ],
      "representation": "列表按作用次序排列，冻结 OperatorChain 接收反转列表。每一阶段的域递推为前一步的像；有效分量属于某个实际阶段，空列表没有有效分量。",
      "dependencies": [
        "CH03-P02-01"
      ]
    },
    {
      "id": "CH03-P02-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.comp_ident"
        }
      ],
      "representation": "逐点传递零距；外侧恒等保距把假设的复合常值传回内侧，排除常值优先分支。",
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
          "file": "Models.lean",
          "name": "C3.Swap.model"
        },
        {
          "file": "Models.lean",
          "name": "C3.Swap.image_dom"
        },
        {
          "file": "Models.lean",
          "name": "C3.Swap.calc_swap"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.swap_strict"
        }
      ],
      "representation": "Option Bool 表示两点和吸收元。换位保持两点域，每步有效且非恒等，复合恒等且非有效。单指标的两个真包含同时否定逆命题。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.outer_const"
        }
      ],
      "representation": "外侧在 f '' U 上两两零距，代入 U 中两点的像即得复合常值。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Models.lean",
          "name": "C3.Seven.p"
        },
        {
          "file": "Models.lean",
          "name": "C3.Seven.F"
        },
        {
          "file": "Models.lean",
          "name": "C3.Seven.G"
        },
        {
          "file": "Models.lean",
          "name": "C3.Seven.model"
        },
        {
          "file": "Models.lean",
          "name": "C3.Seven.example_seven"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.seven_readings"
        }
      ],
      "representation": "Option (Fin 6) 的 0 至 5 依次代表 a,b,p,q,r,s。Bool 的两个读数给出合并 p,q 和完全离散两分量；两个偏定义算子、复合域及距离 0、1 均已验证。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P05-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.diag_const"
        }
      ],
      "representation": "在内侧实际像上使用外层 Lip 矩阵的指定单输入行；对角系数乘零为零，包括系数取顶。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P06-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.fiber_target"
        }
      ],
      "representation": "对任意两个目标，零距允许在到任一点的距离中替换目标，故纤维集合相等。子族距离由冻结构造给出。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.fiber_cover"
        }
      ],
      "representation": "每个像目标由 U 中的原像提供纤维成员；所有去重后的像目标纤维的集合并为 U。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.fiber_disjoint"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.subfamily_partition"
        }
      ],
      "representation": "若两个纤维有公共成员则目标间零距，进而纤维相同。非空性、覆盖和相等或不交合并为子族纤维分划定理。",
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
          "file": "Components.lean",
          "name": "C3.fiber_inter"
        },
        {
          "file": "Components.lean",
          "name": "C3.sub_zero"
        }
      ],
      "representation": "把子族上确界为零展开为对每个 j∈J 的零距。J 非空保证交集中的点属于 U。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.fiber_anti"
        }
      ],
      "representation": "J 包含于 K 时，限制 K 的逐分量条件到 J 即得反向纤维包含。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-06",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.fiber_edges"
        }
      ],
      "representation": "单元素子族的距离化为该分量；全子族的零距蕴含任意指定分量的零距。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-07",
      "status": "complete",
      "declarations": [
        {
          "file": "Components.lean",
          "name": "C3.fiber_ident"
        }
      ],
      "representation": "对任意目标，替换与输入零距的输出，得到 U 中的输入零距类。",
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
          "file": "Components.lean",
          "name": "C3.fiber_const"
        }
      ],
      "representation": "选取像目标的原像证明该纤维为 U；若另一目标与它距离为正，共有纤维成员将导致矛盾。",
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
          "file": "Factors.lean",
          "name": "C3.Factor"
        },
        {
          "file": "Factors.lean",
          "name": "C3.point_iff"
        }
      ],
      "representation": "T 的定义域是实际像。以同一像点的两个输入表示代入 T 的规定值，得到点值关系包含。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.factor_iff"
        },
        {
          "file": "Factors.lean",
          "name": "C3.img"
        },
        {
          "file": "Factors.lean",
          "name": "C3.img_onto"
        },
        {
          "file": "Factors.lean",
          "name": "C3.point_iff"
        }
      ],
      "representation": "对每个实际像点从满射选择代表元，并以另一个算子的值定义 T，关系包含保证赋值公式。该构造也适用于空 U。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.point_both"
        }
      ],
      "representation": "对调 f、g 应用点值因子化等价式，并以集合反对称性得到关系相等。",
      "dependencies": [
        "CH03-P07-01",
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P07-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.factor_lip"
        }
      ],
      "representation": "对任意给定的 T 和两个实际像点选择原像。有限正 K 的逆消去单通道 co-Lip 系数，再用有限 L 的上界得到 L/K。",
      "dependencies": [
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P08-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.QFactor"
        },
        {
          "file": "Factors.lean",
          "name": "C3.cls_onto"
        },
        {
          "file": "Factors.lean",
          "name": "C3.cls_eq"
        },
        {
          "file": "Factors.lean",
          "name": "C3.quotient_iff"
        }
      ],
      "representation": "实际像集按照族零距取 Quotient。从输入到像商的满射和商类相等判据构造指定赋值的商映射，并推出其必要条件。",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P08-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.quotient_both"
        }
      ],
      "representation": "把单向商映射判据应用于两个方向，得到零距点对集合相等。",
      "dependencies": [
        "CH03-P08-01"
      ]
    },
    {
      "id": "CH03-P08-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.separated"
        },
        {
          "file": "Factors.lean",
          "name": "C3.separated_criteria"
        }
      ],
      "representation": "仅假定两个实际像集各自在族零距下分离，证明各自两种关系相等，并据此替换单向、双向判据。",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-01",
        "CH03-P07-02",
        "CH03-P08-01"
      ]
    },
    {
      "id": "CH03-P09-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.finer_preorder"
        }
      ],
      "representation": "固定公共域，包含关系的自反性和传递性给出纤维预序。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.finer_chain"
        }
      ],
      "representation": "长度 n 的相邻比较在 Fin (n+1) 上推出 Monotone，因而任意有序的两层满足包含。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Factors.lean",
          "name": "C3.finer_strict"
        }
      ],
      "representation": "从某一步的真包含选取新增点对，沿单调链证明它在末层而不在首层，并给出首末真包含。",
      "dependencies": [
        "CH03-P09-02"
      ]
    },
    {
      "id": "CH03-P10-01",
      "status": "complete",
      "declarations": [
        {
          "file": "RealExamples.lean",
          "name": "C3.step_model"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.step"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.punct"
        },
        {
          "file": "Models.lean",
          "name": "C3.liftDist"
        },
        {
          "file": "Models.lean",
          "name": "C3.lift_metric"
        },
        {
          "file": "Models.lean",
          "name": "C3.run"
        },
        {
          "file": "Models.lean",
          "name": "C3.line_metric"
        }
      ],
      "representation": "Option ℝ 的 none 是吸收元，两种混合距离为顶。实点取通常距离，run step 实现指定阶跃，开闭端点、域包含与非空性均在声明中。",
      "dependencies": []
    },
    {
      "id": "CH03-P10-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter.lean",
          "name": "C3.step_interval"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.step_legal"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.step_radius"
        }
      ],
      "representation": "每个固定 y 的实际合法半径集是 Ioc 0 (ofReal |y|)。大于边界时从异侧选点，等号处开球仍合法；由上确界得到 |y|>0。",
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
          "file": "RealExamples.lean",
          "name": "C3.step_uniform"
        }
      ],
      "representation": "对每个实数 t>0 在同一个 punct 中选 min(1,t/2)，以此基点的半径压住下确界并推出零。",
      "dependencies": [
        "CH03-D05",
        "CH03-P10-02"
      ]
    },
    {
      "id": "CH03-P11-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.sub_const"
        },
        {
          "file": "Radii.lean",
          "name": "C3.const_full"
        }
      ],
      "representation": "输出子族逐分量常值给出复合距离的两两零距，所以以任意 f(y)、y∈U 为目标的纤维等于 U。",
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
          "file": "Radii.lean",
          "name": "C3.const_top"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.subfamily_constant_radii"
        }
      ],
      "representation": "常值使任意有限正半径合法，点态上确界和统一下确界均为顶；输入距离任意。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P11-01"
      ]
    },
    {
      "id": "CH03-P11-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Models.lean",
          "name": "C3.InfiniteInput.d"
        },
        {
          "file": "Models.lean",
          "name": "C3.InfiniteInput.model"
        },
        {
          "file": "Models.lean",
          "name": "C3.InfiniteInput.both"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.id_on_option"
        }
      ],
      "representation": "两点域用恒等算子，输入分量的不同点距离为顶。输出指标 j 遍历 Bool，覆盖同指标和不同指标，两种情形的条目均为顶而输出非常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P12-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.ident_base"
        }
      ],
      "representation": "把恒等分量的保距公式用于两个输入，将目标 f(y) 的纤维写为 y 在 U 内的零距类。",
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
          "file": "Radii.lean",
          "name": "C3.ident_rad"
        }
      ],
      "representation": "借助像目标纤维等式，把给定有限正 r 的球包含转成合法半径见证，得到 r≤rad 与 0<r。",
      "dependencies": [
        "CH03-D04",
        "CH03-P12-01"
      ]
    },
    {
      "id": "CH03-P13-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.rad_sub"
        },
        {
          "file": "Radii.lean",
          "name": "C3.attained_min"
        }
      ],
      "representation": "用严格距离判据证明点态子族半径等于单分量半径的 iInf；有限非空子类型保证该下确界由某个分量取得。",
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
          "file": "Radii.lean",
          "name": "C3.uniform_sub"
        },
        {
          "file": "Radii.lean",
          "name": "C3.attained_min"
        }
      ],
      "representation": "交换基点子类型和输出子族子类型的两个 iInf，再用有限非空性得到矩阵列中实际取得的最小条目。",
      "dependencies": [
        "CH03-D05",
        "CH03-P13-01"
      ]
    },
    {
      "id": "CH03-P13-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.uniform_sub_anti"
        }
      ],
      "representation": "把小子族的每个分量嵌入大子族，比较同一列条目的下确界。",
      "dependencies": [
        "CH03-P13-02"
      ]
    },
    {
      "id": "CH03-P14-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.fiber_cut"
        }
      ],
      "representation": "纤维成员给出反向输出距离为零，利用对称性得到原文方向。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P14-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.below_rad"
        },
        {
          "file": "Radii.lean",
          "name": "C3.point_cut"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.rad_notation"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.cut_alternatives"
        }
      ],
      "representation": "严格低于 sSup 时提取更大的合法有限正半径，结合点的域成员条件及两端对称性；另给出两个前提的析取形式。",
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
          "file": "Radii.lean",
          "name": "C3.comp_cut"
        }
      ],
      "representation": "两个输入均在上游定义域，两个像点均在下游评估域，后者包含于下游定义域；代入下游纤维命题得到复合输出零距。",
      "dependencies": [
        "CH03-P14-01"
      ]
    },
    {
      "id": "CH03-P15-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.comp_zero"
        }
      ],
      "representation": "将内层统一半径的严格阈值送入实际像域的零距保持假设，再用统一半径的双向判据证明复合下界。",
      "dependencies": [
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P15-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.comp_lip"
        },
        {
          "file": "Radii.lean",
          "name": "C3.scaled_lt"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.matrix_composition"
        }
      ],
      "representation": "有限正 L 给出 a<M/L 与 L*a<M 等价；在内层实际像域应用外层统一半径判据。M 取零或顶仍适用。",
      "dependencies": [
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P16-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.bits_cases"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.four_types"
        }
      ],
      "representation": "四对布尔值分别等价于表中四组不等式，两个比较同时确定唯一的布尔对。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.scale_threshold"
        }
      ],
      "representation": "任意通道中，第一位在较小输入阈值取真时，在较大输入阈值仍取真。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.null_threshold"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.threshold_sets"
        }
      ],
      "representation": "任意通道中，第二位在较大零化阈值取真时，在较小阈值仍取真。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.scale_restrict"
        }
      ],
      "representation": "对任意 Scale 的两个非空域使用包含单调性，同时推出严格小于固定阈值的传递。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.rad_restrict"
        }
      ],
      "representation": "固定基点缩小开球评估域后，先前保证输出零距的全部严格输入距离仍满足判据。",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-P17-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.uniform_restrict"
        }
      ],
      "representation": "基点和比较点都属于 B 时也都属于 A，用 A 上的统一判据推出 B 上的下界。",
      "dependencies": [
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P17-04",
      "status": "complete",
      "declarations": [
        {
          "file": "RealExamples.lean",
          "name": "C3.scale_counter"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.scale_counter_domains"
        }
      ],
      "representation": "在加吸收元实线和恒等算子上核实 B={0} 非空且包含于 A={0,1}。两直径分别为 0 和 1，阈值 1/2 给出逆向判断的反例。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P18-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.uniform_zero"
        },
        {
          "file": "Radii.lean",
          "name": "C3.le_uniform"
        }
      ],
      "representation": "对每个基点使用严格半径判据并取下确界，得到 A 内输入点对距离严格低于统一半径时输出零距。",
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
          "file": "Radii.lean",
          "name": "C3.positive_sep"
        }
      ],
      "representation": "输出正距离排除严格低于统一半径的输入距离，包括无穷输入或输出距离。",
      "dependencies": [
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P18-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.uniform_witness"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.separation_witness"
        }
      ],
      "representation": "对每个大于统一半径的 α 反用全点对判据构造见证。取 ε=min(1,输出距离)，即使输出为顶也是有限正数；可直接限制 α<τN。",
      "dependencies": [
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.threshold_ball"
        }
      ],
      "representation": "对球与 A 的交中的任意点使用严格距离和非严格阈值界，得到以中心像为目标的纤维成员关系。",
      "dependencies": [
        "CH03-D02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.push_net"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.push_cover"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.threshold_cover"
        }
      ],
      "representation": "把 B 的任一内部中心集 S 送到 Finset.image f S 并验证覆盖和基数界。对中心集取下确界包含空 B 及没有有限中心集的情形。",
      "dependencies": [
        "CH03-D07",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.log_mono"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.threshold_entropy"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.cover_constraints"
        }
      ],
      "representation": "证明冻结扩展二进制对数单调，作用于真实内部覆盖数不等式，包含非空 B 的原文结论。",
      "dependencies": [
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P20-01",
      "status": "complete",
      "declarations": [
        {
          "file": "FiniteExamples.lean",
          "name": "C3.step_two"
        }
      ],
      "representation": "同一个阶跃域上，对每个有限正 τ 选 a=min(1,τ.toReal/4)。证明异号点集包含于该域，2a<τ，输入一中心足够，输出半径 1/2 恰需两个内部中心。",
      "dependencies": [
        "CH03-D07",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P21-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.small_iff"
        }
      ],
      "representation": "在 diam<t≤u 下，每个输入距离均低于 t。由统一阈值得到全部输出零距，反向由常值的无穷统一半径推出。",
      "dependencies": [
        "CH03-D01",
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
          "file": "Entropy.lean",
          "name": "C3.small_cover"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.one_cover"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.small_image"
        }
      ],
      "representation": "非空域取一个实际像点作为中心，全部输出零距给上界 1，非空给下界 1。",
      "dependencies": [
        "CH03-D07",
        "CH03-P21-01"
      ]
    },
    {
      "id": "CH03-P22-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.finite_ends"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.finite_cover"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.finite_entropy"
        }
      ],
      "representation": "任意两端非空子族上，用非空有限集合及其像各自作自己的内部覆盖，证明两端覆盖数正且有限、熵各为实数，差值满足定义域条件。",
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
          "file": "Entropy.lean",
          "name": "C3.const_delta"
        }
      ],
      "representation": "常值非空像的覆盖数为 1、熵为 0，输出端有限即保证差值有定义。所得等式允许输入熵为顶。",
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
          "file": "Entropy.lean",
          "name": "C3.ident_cover"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.pull_net"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.push_net"
        }
      ],
      "representation": "恒等分量保距，一向取中心的像，一向为每个内部像中心选原像。两个覆盖数相等，应用同一对数得熵相等。",
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
          "file": "Entropy.lean",
          "name": "C3.ident_delta"
        }
      ],
      "representation": "以 Defined 为差值存在的前提；相等的覆盖数因此都有限，非空性给实熵，再作实数自减。",
      "dependencies": [
        "CH03-D08",
        "CH03-P23-02"
      ]
    },
    {
      "id": "CH03-P24-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.lip_cover"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.push_net"
        },
        {
          "file": "Radii.lean",
          "name": "C3.scaled_lt"
        }
      ],
      "representation": "L 有限正时，输入距离严格小于 ε/L 保证输出距离严格小于 ε；内部中心的像仍内部且基数不增。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P24-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.lip_delta"
        }
      ],
      "representation": "全有界性在 ε 及 ε/L 给出有限输入覆盖，像覆盖受控从而也有限。对数单调，再从输入熵中减去得到下界。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P19-03",
        "CH03-P24-01"
      ]
    },
    {
      "id": "CH03-P25-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.colip_cover"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.pull_net"
        },
        {
          "file": "Entropy.lean",
          "name": "C3.pull_cover"
        }
      ],
      "representation": "从冻结 co-Lip 矩阵的有限非负和取正有限条目，对内部像中心选择原像，证明 ε/K 内覆盖及中心数不增，右端为顶也成立。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P25-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Entropy.lean",
          "name": "C3.colip_delta"
        }
      ],
      "representation": "输入全有界保证差值的定义前提。用覆盖数下界和扩展实数减法的单调性证明上界，允许输出熵为顶。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P19-03",
        "CH03-P25-01"
      ]
    },
    {
      "id": "CH03-P26-01",
      "status": "complete",
      "declarations": [
        {
          "file": "FiniteExamples.lean",
          "name": "C3.affine"
        },
        {
          "file": "FiniteExamples.lean",
          "name": "C3.affine_values"
        },
        {
          "file": "FiniteExamples.lean",
          "name": "C3.affine_first"
        },
        {
          "file": "Models.lean",
          "name": "C3.line_metric"
        }
      ],
      "representation": "用绝对值读数的拉回距离和保吸收元仿射算子，证明定义域包含 U={0,1}。两像为 -1、1，所求纤维为 U，该分量为常值。",
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
          "file": "FiniteExamples.lean",
          "name": "C3.affine_second"
        },
        {
          "file": "FiniteExamples.lean",
          "name": "C3.affine_values"
        }
      ],
      "representation": "在同一 U 核实复合定义域，二次值为 -3、1，目标 -3 的纤维为 {0}。排除常值与恒等，得到有效分量。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P26-03",
      "status": "complete",
      "declarations": [
        {
          "file": "FiniteExamples.lean",
          "name": "C3.constant_twice"
        }
      ],
      "representation": "对 U 上同取实值 c 的任意算子，二次输出都等于 F(c)。若 F(c) 为吸收元，复合定义域与 U 不交；否则所有目标纤维为 U 或空。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P27-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Radii.lean",
          "name": "C3.point_gap"
        }
      ],
      "representation": "对任意正 co-Lip 条目，将严格小于点态半径的输出零距反射到输入，排除开区间中的距离；条目可为顶。",
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
          "file": "Radii.lean",
          "name": "C3.uniform_gap"
        },
        {
          "file": "Textbook.lean",
          "name": "C3.distance_gap"
        }
      ],
      "representation": "低于统一半径时由正条目反射出输入零距，其余输入距离至少为统一半径；特别适用于题设正统一半径。",
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
          "file": "FiniteExamples.lean",
          "name": "C3.translate_blocks"
        },
        {
          "file": "FiniteExamples.lean",
          "name": "C3.transF"
        },
        {
          "file": "Models.lean",
          "name": "C3.line_metric"
        }
      ],
      "representation": "绝对值读数模型上的恒等纤维块为 {-3}、{-2,2}、{0}，平移块为 {-3}、{-2,0}、{2}。用 blocks 的集合相等列出全部块并核实平移域。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P28-02",
      "status": "complete",
      "declarations": [
        {
          "file": "FiniteExamples.lean",
          "name": "C3.translate_cover"
        },
        {
          "file": "FiniteExamples.lean",
          "name": "C3.center_one"
        },
        {
          "file": "FiniteExamples.lean",
          "name": "C3.center_two"
        }
      ],
      "representation": "精度 3/2 的输入用 -2、0 两中心且任一内部单中心均失败；像用 -2 一中心足够。覆盖数为 2 和 1，二进制熵差为 1。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P29-01",
      "status": "complete",
      "declarations": [
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_model"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_half"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.floor_type_spec"
        }
      ],
      "representation": "带吸收元实线上取整，D=[0,1/2] 直径 1/2，输出全零使统一半径为顶，分类为 (1,1)。",
      "dependencies": [
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
          "file": "RealExamples.lean",
          "name": "C3.floor_model"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_narrow"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_cross"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.floor_type_spec"
        }
      ],
      "representation": "D=[9/10,11/10] 直径 1/5。从整数 1 左侧任意逼近，输入距离趋零而取整值不同，故统一半径 0、分类 (1,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P18-02"
      ]
    },
    {
      "id": "CH03-P29-03",
      "status": "complete",
      "declarations": [
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_model"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_pair"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.floor_type_spec"
        }
      ],
      "representation": "D={0,2} 的直径为 2，严格低于 2 的输入只可能是同一点，距离 2 的点对输出不同。统一半径为 2，分类 (0,1)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P18-02"
      ]
    },
    {
      "id": "CH03-P29-04",
      "status": "complete",
      "declarations": [
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_model"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_wide"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_cross"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.floor_type_spec"
        }
      ],
      "representation": "D=[0,2] 的直径是 2，跨越整数 1 的任意近点对使统一半径为 0，分类 (0,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P18-02"
      ]
    },
    {
      "id": "CH03-P29-05",
      "status": "complete",
      "declarations": [
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_counter"
        },
        {
          "file": "RealExamples.lean",
          "name": "C3.floor_pair"
        }
      ],
      "representation": "两点域的统一半径 2 大于等于 1，但取整输出在这两点不同；下界来自不同输入间的距离间隙。",
      "dependencies": [
        "CH03-P29-03"
      ]
    },
    {
      "id": "CH03-P30-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.cover"
        },
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.midpoint"
        }
      ],
      "representation": "所有有限正 ε 分为 ε≤1、1<ε≤2、2<ε 三段，覆盖数依次为 4、2、1。半径 7/4 的外部点 3/2 虽能覆盖所有点却不属于 U。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P30-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.restrictOp"
        },
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.values"
        },
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.images"
        },
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.image_delta"
        }
      ],
      "representation": "两张值表各给出合法算子，域外输出吸收元。两定义域和像集均为 U，因此任意有限正精度像覆盖数等于源覆盖数且两个差值都为 0。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P30-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.Lip"
        },
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.optimal"
        },
        {
          "file": "Chapter.lean",
          "name": "C3.scalar_spec"
        }
      ],
      "representation": "在指定四点域上验证 F 的 1-Lip 和 G 的 3-Lip，并以输入 0、1 的像距证明任一合法系数至少为 1、3，写成 IsLeast。",
      "dependencies": [
        "CH03-P30-02"
      ]
    },
    {
      "id": "CH03-P30-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Rearrangement.lean",
          "name": "C3.Rearrange.bounds"
        }
      ],
      "representation": "以两个最小系数实际调用单通道覆盖上界，在 ε=7/4 得 2≤2 和 2≤4；两个实际像覆盖数均为 2。",
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
