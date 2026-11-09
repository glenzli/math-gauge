本答卷尚未完成整章要求：80 项 complete，12 项 incomplete。以下源码已在指定 Lean 4.29.1 环境统一编译；180 个声明的公理审计仅包含 `propext`、`Classical.choice`、`Quot.sound`。

数学来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，CC BY 4.0；以下为新增形式化。

```lean filename=lakefile.lean
import Lake
open Lake DSL
package «mg-c003»
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "5e932f97dd25535344f80f9dd8da3aab83df0fe6"
lean_lib Frozen where
  roots := #[]
  globs := #[.submodules `formal_oet]
@[default_target] lean_lib Main where
  roots := #[`Main]
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import Mathlib.Data.EReal.Operations

/- Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
https://glenzli.com/books/oet/, CC BY 4.0. New Lean formalization. -/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

@[simp] theorem mul_func (f g : Operator X bot) (x : X) :
    (f*g).func x = f.func (g.func x) := rfl
@[simp] theorem one_func (x : X) :
    (1 : Operator X bot).func x = x := rfl

def Const (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}
def Ident (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Const d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}
def Active (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (Const d f U ∪ Ident d f U)ᶜ

theorem component_partition (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    Disjoint (Const d f U) (Ident d f U) ∧
    Disjoint (Const d f U ∪ Ident d f U) (Active d f U) ∧
    Const d f U ∪ Ident d f U ∪ Active d f U = univ := by
  simp only [Ident, Active, disjoint_left, mem_setOf_eq, mem_union, mem_compl_iff]
  constructor
  · intro i hi h
    exact h.1 hi
  constructor
  · tauto
  · exact union_compl_self _

theorem zero_transport (d : X → X → ENNReal)
    (hd : ExtendedPseudoMetric X bot d) {a b c : X} (h : d a b = 0) :
    d a c = d b c := by
  apply le_antisymm
  · simpa [h] using hd.triangle a b c
  · have hs : d b a = 0 := (hd.symm b a).trans h
    simpa [hs] using hd.triangle b a c

theorem zero_trans (d : X → X → ENNReal)
    (hd : ExtendedPseudoMetric X bot d) {a b c : X}
    (hab : d a b = 0) (hbc : d b c = 0) : d a c = 0 :=
  (zero_transport d hd hab).trans hbc

theorem ident_distance (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ Ident d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) = d i x y := by
  rw [zero_transport (d i) (hd i) (hi.2 x hx), (hd i).symm x,
    zero_transport (d i) (hd i) (hi.2 y hy), (hd i).symm y x]

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ Const d f U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (f.func x) (f.func y) ≤ ∑ k : I, 0 * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {i k : I} {K : I → I → ENNReal}
    (hi : i ∈ Const d f U) (hK : IsCoLipMatrix d f U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x,hx,y,hy,hp⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hp

theorem outer_const (d : I → X → X → ENNReal)
    {f g : Operator X bot} {U : Set X} {i : I}
    (hi : i ∈ Const d g (f.func '' U)) : i ∈ Const d (g * f) U := by
  intro x hx y hy
  exact hi _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

theorem compose_ident (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f g : Operator X bot} {U : Set X} {i : I}
    (hf : i ∈ Ident d f U) (hg : i ∈ Ident d g (f.func '' U)) :
    i ∈ Ident d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    rw [← ident_distance d hd hg (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)]
    exact hc x hx y hy
  · intro x hx
    exact zero_trans (d i) (hd i) (hg.2 _ (mem_image_of_mem _ hx)) (hf.2 x hx)

theorem compose_active (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    Active d (g * f) U ⊆ Active d f U ∪ Active d g (f.func '' U) := by
  classical
  intro i hi
  by_contra hn
  have hf : i ∈ Const d f U ∪ Ident d f U := by
    exact Classical.not_not.mp (not_or.mp hn).1
  have hg : i ∈ Const d g (f.func '' U) ∪ Ident d g (f.func '' U) := by
    exact Classical.not_not.mp (not_or.mp hn).2
  apply hi
  rcases hg with hg | hg
  · exact Or.inl (outer_const d hg)
  · rcases hf with hf | hf
    · left
      intro x hx y hy
      change d i (g.func (f.func x)) (g.func (f.func y)) = 0
      rw [ident_distance d hd hg (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)]
      exact hf x hx y hy
    · exact Or.inr (compose_ident d hd hf hg)

def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => chain fs * f
def activeSteps (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => Active d f U ∪ activeSteps d fs (f.func '' U)

theorem chain_active (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (fs : List (Operator X bot)) (U : Set X) :
    Active d (chain fs) U ⊆ activeSteps d fs U := by
  classical
  induction fs generalizing U with
  | nil =>
    intro i hi
    apply hi
    by_cases hc : i ∈ Const d (1 : Operator X bot) U
    · exact Or.inl hc
    · exact Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩
  | cons f fs ih =>
    exact (compose_active d hd f (chain fs) U).trans
      (union_subset_union_right _ (ih _))

theorem chain_domain (fs : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain fs)) :
    ∀ f ∈ fs.head?, U ⊆ dom f := by
  cases fs with
  | nil => simp
  | cons f fs =>
    intro g hg
    have he : g = f := by simpa using hg.symm
    subst g
    intro x hx hn
    have h := hU hx
    apply h
    change (chain fs).func (f.func x) = bot
    rw [hn, (chain fs).preserves_bot]

theorem inner_const_lip [Fintype I] (d : I → X → X → ENNReal)
    {f g : Operator X bot} {U : Set X} {j : I} {L : I → I → ENNReal}
    (hc : j ∈ Const d f U) (hL : IsLipMatrix d g (f.func '' U) L)
    (hr : ∀ k, k ≠ j → L k j = 0) : j ∈ Const d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  simpa [hc x hx y hy] using
    lip_bound_of_single_input_row d g (f.func '' U) L j j hL hr
      _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

def Fiber (d : I → X → X → ENNReal) (f : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ ∀ j ∈ J, d j (f.func x) y = 0}
def SingleFiber (d : I → X → X → ENNReal) (f : Operator X bot) (j : I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ d j (f.func x) y = 0}

theorem subfamily_zero (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact le_antisymm (h ▸ le_iSup (fun k : J => d k.1 x y) ⟨j,hj⟩) (zero_le _)
  · intro h
    apply le_antisymm _ (zero_le _)
    exact iSup_le (fun j => le_of_eq (h j.1 j.2))

theorem fiber_representation (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    Fiber d f J y U = {x ∈ U | subfamily_pseudometric d J (f.func x) y = 0} := by
  ext x
  simp [Fiber, subfamily_zero]

theorem fiber_target (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {J : Set I}
    {U : Set X} {y y' : X} (h : ∀ j ∈ J, d j y y' = 0) :
    Fiber d f J y U = Fiber d f J y' U := by
  ext x
  constructor <;> rintro ⟨hx,hz⟩ <;> refine ⟨hx, ?_⟩ <;> intro j hj
  · exact zero_trans (d j) (hd j) (hz j hj) (h j hj)
  · exact zero_trans (d j) (hd j) (hz j hj)
      (((hd j).symm y' y).trans (h j hj))

theorem fiber_cover (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (J : Set I) (U : Set X) :
    (∀ y ∈ f.func '' U, (Fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, Fiber d f J y U) = U := by
  constructor
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨x,hx,fun j _ => (hd j).dist_self _⟩
  · ext x
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_,_,h⟩
      exact h.1
    · intro hx
      exact ⟨f.func x, mem_image_of_mem _ hx, hx,
        fun j _ => (hd j).dist_self _⟩

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (J : Set I) (U : Set X) (y z : X) :
    Fiber d f J y U = Fiber d f J z U ∨
      Disjoint (Fiber d f J y U) (Fiber d f J z U) := by
  classical
  by_cases h : Disjoint (Fiber d f J y U) (Fiber d f J z U)
  · exact Or.inr h
  · left
    obtain ⟨x,hx,hy⟩ := not_disjoint_iff.mp h
    apply fiber_target d hd
    intro j hj
    exact zero_trans (d j) (hd j)
      (((hd j).symm _ _).trans (hx.2 j hj)) (hy.2 j hj)

theorem fiber_intersection (d : I → X → X → ENNReal) (f : Operator X bot)
    {J : Set I} (hJ : J.Nonempty) (y : X) (U : Set X) :
    Fiber d f J y U = ⋂ j ∈ J, SingleFiber d f j y U := by
  ext x
  simp only [Fiber, SingleFiber, mem_setOf_eq, mem_iInter]
  constructor
  · rintro ⟨hx,h⟩ j hj
    exact ⟨hx,h j hj⟩
  · intro h
    obtain ⟨j,hj⟩ := hJ
    exact ⟨(h j hj).1, fun k hk => (h k hk).2⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    {J K : Set I} (h : J ⊆ K) (y : X) (U : Set X) :
    Fiber d f K y U ⊆ Fiber d f J y U :=
  fun _ hx => ⟨hx.1, fun j hj => hx.2 j (h hj)⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    Fiber d f {i} y U = SingleFiber d f i y U := by
  ext x
  simp [Fiber, SingleFiber]

theorem fiber_all_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    Fiber d f univ y U ⊆ SingleFiber d f i y U :=
  fun _ hx => ⟨hx.1, hx.2 i (mem_univ _)⟩

theorem ident_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ Ident d f U) (y : X) :
    SingleFiber d f i y U = {x ∈ U | d i x y = 0} := by
  ext x
  constructor <;> rintro ⟨hx,h⟩ <;> refine ⟨hx, ?_⟩
  · rwa [zero_transport (d i) (hd i) (hi.2 x hx)] at h
  · rwa [zero_transport (d i) (hd i) (hi.2 x hx)]

theorem const_fiber (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ Const d f U) {y : X}
    (hy : y ∈ f.func '' U) : SingleFiber d f i y U = U := by
  obtain ⟨z,hz,rfl⟩ := hy
  ext x
  exact ⟨fun h => h.1, fun hx => ⟨hx, hi x hx z hz⟩⟩

theorem const_fiber_empty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ Const d f U) {y y₀ : X}
    (hy₀ : y₀ ∈ f.func '' U) (hy : 0 < d i y y₀) :
    SingleFiber d f i y U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx,hxy⟩
  have hx₀ : x ∈ SingleFiber d f i y₀ U := by
    rw [const_fiber d hi hy₀]
    exact hx
  exact (ne_of_gt hy)
    (zero_trans (d i) (hd i) (((hd i).symm _ _).trans hxy) hx₀.2)

def PointRel (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}
def ZeroRel (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}
def FiberLE (d : I → X → X → ENNReal) (U : Set X) (f g : Operator X bot) : Prop :=
  ZeroRel d f U ⊆ ZeroRel d g U

theorem zeroRel_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ ZeroRel d f U ↔ y ∈ Fiber d f univ (f.func x) U := by
  constructor
  · intro h
    exact ⟨hy, fun j _ => ((hd j).symm _ _).trans (h.2.2 j)⟩
  · intro h
    exact ⟨hx,hy,fun j => ((hd j).symm _ _).trans (h.2 j (mem_univ _))⟩

def Factors (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U) → X,
    ∀ x (hx : x ∈ U), T ⟨f.func x, mem_image_of_mem _ hx⟩ = g.func x

theorem factors_iff (f g : Operator X bot) (U : Set X) :
    Factors f g U ↔ PointRel f U ⊆ PointRel g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,he⟩
    refine ⟨hx,hy, ?_⟩
    rw [← hT x hx, ← hT y hy]
    congr 1
    exact Subtype.ext he
  · intro h
    let rep : (f.func '' U) → X := fun y => Classical.choose y.2
    have hr (y : f.func '' U) : rep y ∈ U ∧ f.func (rep y) = y :=
      Classical.choose_spec y.2
    refine ⟨fun y => g.func (rep y), ?_⟩
    intro x hx
    exact (h (a := (rep ⟨f.func x,mem_image_of_mem _ hx⟩,x))
      ⟨(hr ⟨f.func x,mem_image_of_mem _ hx⟩).1,hx,
        (hr ⟨f.func x,mem_image_of_mem _ hx⟩).2⟩).2.2

theorem factors_both (f g : Operator X bot) (U : Set X) :
    Factors f g U ∧ Factors g f U ↔ PointRel f U = PointRel g U := by
  rw [factors_iff, factors_iff]
  exact subset_antisymm_iff.symm

theorem factor_lip (d : X → X → ENNReal) {f g : Operator X bot} {U : Set X}
    (T : (f.func '' U) → X)
    (hT : ∀ x (hx : x ∈ U), T ⟨f.func x, mem_image_of_mem _ hx⟩ = g.func x)
    {K L : ENNReal} (hK : K ≠ 0) (hK' : K ≠ ⊤) (_hL : L ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (f.func x) (f.func y))
    (hli : ∀ x ∈ U, ∀ y ∈ U, d (g.func x) (g.func y) ≤ L * d x y) :
    ∀ a b : f.func '' U, d (T a) (T b) ≤ (L / K) * d a b := by
  rintro ⟨a,x,hx,rfl⟩ ⟨b,y,hy,rfl⟩
  rw [hT x hx, hT y hy]
  calc
    d (g.func x) (g.func y) ≤ L * d x y := hli x hx y hy
    _ = (L / K) * (K * d x y) := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_assoc L,
        ENNReal.inv_mul_cancel hK hK', mul_one]
    _ ≤ _ := mul_le_mul_left' (hco x hx y hy) _

theorem fiberLE_refl (d : I → X → X → ENNReal) (U : Set X) (f : Operator X bot) :
    FiberLE d U f f := subset_rfl
theorem fiberLE_trans (d : I → X → X → ENNReal) (U : Set X)
    {f g h : Operator X bot} (hfg : FiberLE d U f g) (hgh : FiberLE d U g h) :
    FiberLE d U f h := hfg.trans hgh

theorem relation_chain {α : Type} (R : ℕ → Set α) (hs : ∀ k, R k ⊆ R (k+1))
    {a b : ℕ} (hab : a ≤ b) : R a ⊆ R b := by
  induction hab with
  | refl => exact subset_rfl
  | @step b h ih => exact ih.trans (hs b)

theorem relation_chain_strict {α : Type} (R : ℕ → Set α)
    (hs : ∀ k, R k ⊆ R (k+1)) {r m : ℕ}
    (hr : r < m) (hstrict : R r ⊂ R (r+1)) :
    R 0 ⊂ R m ∧ ∃ p, p ∈ R m ∧ p ∉ R 0 := by
  obtain ⟨p,hp,hpn⟩ := exists_of_ssubset hstrict
  have hp' := relation_chain R hs (Nat.succ_le_of_lt hr) hp
  have hpn' : p ∉ R 0 :=
    fun h => hpn (relation_chain R hs (Nat.zero_le r) h)
  exact ⟨(relation_chain R hs (Nat.zero_le m)).ssubset_of_mem_notMem hp' hpn',
    p,hp',hpn'⟩
end Chapter3

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
variable {X I : Type} {bot : X}

def imageSetoid (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Setoid (f.func '' U) where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have he := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun _ => he.refl _, fun h => he.symm h, fun h k => he.trans h k⟩
def ImageQuotient (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid d hd f U)
def imageClass (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    {U : Set X} (x : X) (hx : x ∈ U) : ImageQuotient d hd f U :=
  Quotient.mk _ ⟨f.func x, mem_image_of_mem _ hx⟩
def QuotientFactors (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuotient d hd f U → ImageQuotient d hd g U,
    ∀ x (hx : x ∈ U), T (imageClass d hd f x hx) = imageClass d hd g x hx

theorem quotient_factors_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    QuotientFactors d hd f g U ↔ ZeroRel d f U ⊆ ZeroRel d g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,hxy⟩
    refine ⟨hx,hy,?_⟩
    have he : imageClass d hd f x hx = imageClass d hd f y hy :=
      Quotient.sound hxy
    have he' := congrArg T he
    rw [hT x hx, hT y hy] at he'
    exact Quotient.exact he'
  · intro h
    let rep : (f.func '' U) → X := fun y => Classical.choose y.2
    have hr (y : f.func '' U) : rep y ∈ U ∧ f.func (rep y) = y :=
      Classical.choose_spec y.2
    let v (y : f.func '' U) : ImageQuotient d hd g U :=
      imageClass d hd g (rep y) (hr y).1
    have hv : ∀ a b : f.func '' U,
        (imageSetoid d hd f U).r a b → v a = v b := by
      intro a b hab
      apply Quotient.sound
      apply (h (a := (rep a,rep b)) ⟨(hr a).1,(hr b).1,?_⟩).2.2
      intro i
      rw [(hr a).2, (hr b).2]
      exact hab i
    refine ⟨Quotient.lift v hv, ?_⟩
    intro x hx
    change v ⟨f.func x,mem_image_of_mem _ hx⟩ = imageClass d hd g x hx
    apply Quotient.sound
    apply (h (a := (rep ⟨f.func x,mem_image_of_mem _ hx⟩, x))
      ⟨(hr _).1,hx,?_⟩).2.2
    intro i
    rw [(hr _).2]
    exact (hd i).dist_self _

theorem quotient_factors_both (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U ↔
      ZeroRel d f U = ZeroRel d g U := by
  rw [quotient_factors_iff, quotient_factors_iff]
  exact subset_antisymm_iff.symm

def SeparatesOn (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

theorem relations_equal_on_separated_image (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hs : SeparatesOn d (f.func '' U)) : PointRel f U = ZeroRel d f U := by
  ext p
  constructor
  · rintro ⟨hx,hy,he⟩
    exact ⟨hx,hy,fun i => by rw [he]; exact (hd i).dist_self _⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨hx,hy,hs _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy) he⟩

theorem separated_factor_criteria (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (hf : SeparatesOn d (f.func '' U)) (hg : SeparatesOn d (g.func '' U)) :
    (Factors f g U ↔ QuotientFactors d hd f g U) ∧
    ((Factors f g U ∧ Factors g f U) ↔
      (QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U)) := by
  have hf' := relations_equal_on_separated_image d hd f U hf
  have hg' := relations_equal_on_separated_image d hd g U hg
  simp only [factors_iff, quotient_factors_iff, hf',hg', iff_self, and_self]
end Chapter3

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def Legal (f : Operator X bot) (a b : X → X → ENNReal) (U : Set X) (y : X)
    (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, a x y < r → b (f.func x) (f.func y) = 0
noncomputable def radius (f : Operator X bot) (a b : X → X → ENNReal)
    (U : Set X) (y : X) : ENNReal := sSup {r | Legal f a b U y r}
noncomputable def uniform (f : Operator X bot) (a b : X → X → ENNReal)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, radius f a b U y
noncomputable def N (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j i : I) : ENNReal := uniform f (d i) (d j) U U

theorem legal_ball (f : Operator X bot) (a b : X → X → ENNReal)
    (U : Set X) (y : X) (r : ENNReal) :
    Legal f a b U y r ↔ 0 < r ∧ r < ⊤ ∧
      ball a y r ∩ U ⊆ {x ∈ U | b (f.func x) (f.func y) = 0} := by
  simp only [Legal, ball, mem_inter_iff, mem_setOf_eq, subset_def]
  aesop

theorem legal_le_radius {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {y : X} {r : ENNReal} (h : Legal f a b U y r) :
    r ≤ radius f a b U y := le_sSup h

theorem below_radius {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {x y : X} (hx : x ∈ U) (h : a x y < radius f a b U y) :
    b (f.func x) (f.func y) = 0 := by
  obtain ⟨r,hr,hlt⟩ := lt_sSup_iff.mp h
  exact hr.2.2 x hx hlt

theorem le_radius_iff {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {y : X} {r : ENNReal} :
    r ≤ radius f a b U y ↔
      ∀ x ∈ U, a x y < r → b (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx hlt
    exact below_radius hx (hlt.trans_le h)
  · intro h
    by_contra hn
    obtain ⟨q,hq,hqr⟩ :=
      ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hl : Legal f a b U y q :=
      ⟨lt_of_le_of_lt (zero_le _) hq, ENNReal.coe_lt_top,
        fun x hx hxq => h x hx (hxq.trans hqr)⟩
    exact (not_lt_of_ge (legal_le_radius hl)) hq

theorem uniform_le_point {f : Operator X bot} {a b : X → X → ENNReal}
    {A U : Set X} {y : X} (hy : y ∈ A) :
    uniform f a b A U ≤ radius f a b U y :=
  iInf_le_of_le y (iInf_le _ hy)

theorem below_uniform {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : a x y < uniform f a b U U) : b (f.func x) (f.func y) = 0 :=
  below_radius hx (h.trans_le (uniform_le_point hy))

theorem separated_input {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : 0 < b (f.func x) (f.func y)) :
    uniform f a b U U ≤ a x y := by
  by_contra hn
  exact (ne_of_gt h) (below_uniform hx hy (lt_of_not_ge hn))

theorem radius_restrict {f : Operator X bot} {a b : X → X → ENNReal}
    {A B : Set X} (h : B ⊆ A) (y : X) :
    radius f a b A y ≤ radius f a b B y := by
  apply le_radius_iff.mpr
  intro x hx hlt
  exact below_radius (h hx) hlt

theorem uniform_restrict {f : Operator X bot} {a b : X → X → ENNReal}
    {A B : Set X} (h : B ⊆ A) :
    uniform f a b A A ≤ uniform f a b B B := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (uniform_le_point (h hy)).trans (radius_restrict h y)

theorem radius_top {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {y : X} (h : ∀ x ∈ U, b (f.func x) (f.func y) = 0) :
    radius f a b U y = ⊤ :=
  top_unique (le_radius_iff.mpr (fun x hx _ => h x hx))

theorem uniform_top {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} (h : ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) = 0) :
    uniform f a b U U = ⊤ := by
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  rw [radius_top (fun x hx => h x hx y hy)]

theorem const_subfamily_fiber (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {J : Set I} (hJ : J ⊆ Const d f U) {y : X} (hy : y ∈ U) :
    Fiber d f J (f.func y) U = U := by
  ext x
  exact ⟨fun h => h.1, fun hx => ⟨hx, fun j hj => hJ hj x hx y hy⟩⟩

theorem const_subfamily_radius (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {J : Set I} (hJ : J ⊆ Const d f U) (i : I) :
    (∀ y ∈ U, radius f (d i) (subfamily_pseudometric d J) U y = ⊤) ∧
    uniform f (d i) (subfamily_pseudometric d J) U U = ⊤ := by
  have h : ∀ x ∈ U, ∀ y ∈ U,
      subfamily_pseudometric d J (f.func x) (f.func y) = 0 :=
    fun x hx y hy => (subfamily_zero d J _ _).mpr
      (fun j hj => hJ hj x hx y hy)
  exact ⟨fun y hy => radius_top (fun x hx => h x hx y hy), uniform_top h⟩

theorem ident_image_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ Ident d f U) {y : X} (hy : y ∈ U) :
    SingleFiber d f i (f.func y) U = {x ∈ U | d i x y = 0} := by
  ext x
  constructor <;> rintro ⟨hx,h⟩ <;> refine ⟨hx, ?_⟩
  · rwa [ident_distance d hd hi hx hy] at h
  · rwa [ident_distance d hd hi hx hy]

theorem ident_radius_lower (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ Ident d f U) {y : X} (hy : y ∈ U)
    {r : ENNReal} (hr : 0 < r) (hrt : r < ⊤)
    (h : ∀ x ∈ U, d i x y < r → d i x y = 0) :
    r ≤ radius f (d i) (d i) U y ∧ 0 < r := by
  refine ⟨legal_le_radius ⟨hr,hrt,?_⟩,hr⟩
  intro x hx hlt
  rw [ident_distance d hd hi hx hy]
  exact h x hx hlt

theorem radius_subfamily (d : I → X → X → ENNReal) (f : Operator X bot)
    (a : X → X → ENNReal) (U : Set X) (y : X) (J : Set I) :
    radius f a (subfamily_pseudometric d J) U y =
      ⨅ j ∈ J, radius f a (d j) U y := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    apply le_radius_iff.mpr
    intro x hx hlt
    exact ((subfamily_zero d J _ _).mp (below_radius hx hlt)) j hj
  · apply le_radius_iff.mpr
    intro x hx hlt
    apply (subfamily_zero d J _ _).mpr
    intro j hj
    exact below_radius hx (hlt.trans_le (iInf_le_of_le j (iInf_le _ hj)))

theorem uniform_subfamily (d : I → X → X → ENNReal) (f : Operator X bot)
    (a : X → X → ENNReal) (U : Set X) (J : Set I) :
    uniform f a (subfamily_pseudometric d J) U U =
      ⨅ j ∈ J, uniform f a (d j) U U := by
  simp only [uniform, radius_subfamily]
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    apply iInf_mono
    intro y
    apply iInf_mono
    intro hy
    exact iInf_le_of_le j (iInf_le _ hj)
  · apply le_iInf
    intro y
    apply le_iInf
    intro hy
    apply le_iInf
    intro j
    apply le_iInf
    intro hj
    exact (iInf_le_of_le j (iInf_le _ hj)).trans
      (iInf_le_of_le y (iInf_le _ hy))

theorem uniform_subfamily_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (a : X → X → ENNReal) (U : Set X) {J K : Set I} (h : J ⊆ K) :
    uniform f a (subfamily_pseudometric d K) U U ≤
      uniform f a (subfamily_pseudometric d J) U U := by
  rw [uniform_subfamily, uniform_subfamily]
  apply le_iInf
  intro j
  apply le_iInf
  intro hj
  exact iInf_le_of_le j (iInf_le _ (h hj))

theorem fiber_truncate (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {j : I} {x y : X}
    (h : y ∈ SingleFiber d f j (f.func x) U) :
    d j (f.func x) (f.func y) = 0 := ((hd j).symm _ _).trans h.2

theorem radius_compose (f g : Operator X bot) (a b c : X → X → ENNReal)
    (U : Set X)
    (h : ∀ y ∈ f.func '' U, ∀ z ∈ f.func '' U,
      b y z = 0 → c (g.func y) (g.func z) = 0) :
    uniform f a b U U ≤ uniform (g*f) a c U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply le_radius_iff.mpr
  intro x hx hlt
  exact h _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
    (below_uniform hx hy hlt)

theorem radius_compose_lip (f g : Operator X bot) (a b c : X → X → ENNReal)
    (U : Set X) {L : ENNReal} (_hL : 0 < L) (_hLt : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) ≤ L * a x y) :
    uniform g b c (f.func '' U) (f.func '' U) / L ≤
      uniform (g*f) a c U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply le_radius_iff.mpr
  intro x hx hlt
  exact below_uniform (f := g) (a := b) (b := c)
    (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
    ((h x hx y hy).trans_lt (ENNReal.mul_lt_of_lt_div' hlt))

theorem separation_witness {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {α τ : ENNReal} (h : uniform f a b U U < α)
    (hα : 0 < α) (hαt : α < ⊤) (_hτ : α < τ) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ a x y < α ∧ ε ≤ b (f.func x) (f.func y) := by
  classical
  have hn : ¬ ∀ y ∈ U, α ≤ radius f a b U y := by
    intro hn
    exact not_le_of_gt h (le_iInf fun y => le_iInf (hn y))
  push_neg at hn
  obtain ⟨y,hy,hyr⟩ := hn
  have hn' : ¬ ∀ x ∈ U, a x y < α → b (f.func x) (f.func y) = 0 := by
    intro hn'
    exact not_le_of_gt hyr (legal_le_radius ⟨hα,hαt,hn'⟩)
  push_neg at hn'
  obtain ⟨x,hx,hxy,hb⟩ := hn'
  obtain ⟨ε,hε,hεb⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hb)
  exact ⟨x,hx,y,hy,ε,hε,ENNReal.coe_lt_top,hxy,hεb.le⟩

noncomputable def diameter (a : X → X → ENNReal) (U : Set X) : ENNReal :=
  ⨆ x ∈ U, ⨆ y ∈ U, a x y
def Scale (X I : Type) :=
  {σ : I → {A : Set X // A.Nonempty} → ENNReal //
    ∀ i A B, A.1 ⊆ B.1 → σ i A ≤ σ i B}
noncomputable def diameterScale (d : I → X → X → ENNReal) : Scale X I :=
  ⟨fun i A => diameter (d i) A, by
    intro i A B h
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le x (le_iSup_of_le (h hx)
      (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))⟩
noncomputable def thresholdType (s r τs τr : ENNReal) : Bool × Bool :=
  (decide (s < τs), decide (τr ≤ r))

theorem threshold_cases (s r τs τr : ENNReal) :
    (s < τs ∧ τr ≤ r) ∨ (s < τs ∧ r < τr) ∨
    (τs ≤ s ∧ τr ≤ r) ∨ (τs ≤ s ∧ r < τr) := by
  rcases lt_or_ge s τs with hs | hs <;>
    rcases le_or_gt τr r with hr | hr <;> tauto
theorem threshold_scale_mono {s τ τ' : ENNReal} (h : τ ≤ τ') :
    s < τ → s < τ' := fun hs => hs.trans_le h
theorem threshold_radius_antitone {r τ τ' : ENNReal} (h : τ ≤ τ') :
    τ' ≤ r → τ ≤ r := fun hr => h.trans hr
theorem scale_restrict (σ : Scale X I) (i : I)
    (A B : {A : Set X // A.Nonempty}) (h : B.1 ⊆ A.1) (τ : ENNReal) :
    σ.1 i B ≤ σ.1 i A ∧ (σ.1 i A < τ → σ.1 i B < τ) :=
  ⟨σ.2 i B A h, fun hτ => (σ.2 i B A h).trans_lt hτ⟩

theorem small_domain (f : Operator X bot) (a b : X → X → ENNReal)
    (U : Set X) {τs τr : ENNReal} (hd : diameter a U < τs) (hτ : τs ≤ τr) :
    τr ≤ uniform f a b U U ↔
      ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) = 0 := by
  constructor
  · intro hr x hx y hy
    have hxy : a x y ≤ diameter a U :=
      le_iSup_of_le x (le_iSup_of_le hx
        (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    exact below_uniform hx hy (hxy.trans_lt (hd.trans_le (hτ.trans hr)))
  · intro h
    rw [uniform_top h]
    exact le_top

theorem colip_radius_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius f (d i) (d j) U y) := by
  rintro ⟨hpos,hlt⟩
  exact (ne_of_gt hpos)
    (positive_colip_entry_reflects_zero d f U K i j hK hp x hx y hy
      (below_radius hx hlt))

theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniform f (d i) (d j) U U ≤ d i x y := by
  by_cases h : uniform f (d i) (d j) U U ≤ d i x y
  · exact Or.inr h
  · exact Or.inl (positive_colip_entry_reflects_zero d f U K i j hK hp x hx y hy
      (below_uniform hx hy (lt_of_not_ge h)))
end Chapter3

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def TotallyBoundedFor (a : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number a r U < ⊤

theorem covering_representation (a : X → X → ENNReal) (ε : ENNReal) (U : Set X) :
    (covering_number a ε U = ⊤ ↔
      ¬ ∃ S : Finset X, InternalEpsilonNet a ε U S) ∧
    (∀ S : Finset X, InternalEpsilonNet a ε U S ↔
      (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball a c ε) := by
  refine ⟨covering_number_eq_top_iff a ε U, ?_⟩
  intro S
  simp [InternalEpsilonNet, ball, subset_def]

theorem push_net (f : X → X) {a b : X → X → ENNReal} {δ ε : ENNReal}
    {U : Set X} {S : Finset X} (hS : InternalEpsilonNet a δ U S)
    (h : ∀ x ∈ U, ∀ y ∈ U, a x y < δ → b (f x) (f y) < ε) :
    ∃ T : Finset X, InternalEpsilonNet b ε (f '' U) T ∧ T.card ≤ S.card := by
  classical
  refine ⟨S.image f, ⟨?_,?_⟩,Finset.card_image_le⟩
  · intro t ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
    exact mem_image_of_mem _ (hS.1 hx)
  · rintro t ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := hS.2 x hx
    exact ⟨f y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,h x hx y (hS.1 hy) hxy⟩

theorem push_cover (f : X → X) {a b : X → X → ENNReal} {δ ε : ENNReal}
    {U : Set X}
    (h : ∀ x ∈ U, ∀ y ∈ U, a x y < δ → b (f x) (f y) < ε) :
    covering_number b ε (f '' U) ≤ covering_number a δ U := by
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  obtain ⟨T,hT,hcard⟩ := push_net f hS h
  exact (iInf_le_of_le T (iInf_le_of_le hT le_rfl)).trans (by exact_mod_cast hcard)

theorem pull_net (f : Operator X bot) {a b : X → X → ENNReal} {δ ε : ENNReal}
    {U : Set X} {T : Finset X} (hT : InternalEpsilonNet b ε (f.func '' U) T)
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) < ε → a x y < δ) :
    ∃ S : Finset X, InternalEpsilonNet a δ U S ∧ S.card ≤ T.card := by
  classical
  let rep : X → X :=
    fun t => if ht : t ∈ f.func '' U then Classical.choose ht else bot
  have hr (t : X) (ht : t ∈ f.func '' U) :
      rep t ∈ U ∧ f.func (rep t) = t := by
    dsimp [rep]
    rw [dif_pos ht]
    exact Classical.choose_spec ht
  refine ⟨T.image rep,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro s hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact (hr t (hT.1 ht)).1
  · intro x hx
    obtain ⟨t,ht,hxt⟩ := hT.2 _ (mem_image_of_mem _ hx)
    refine ⟨rep t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
    apply h x hx _ (hr t (hT.1 ht)).1
    rwa [(hr t (hT.1 ht)).2]

theorem pull_cover (f : Operator X bot) {a b : X → X → ENNReal} {δ ε : ENNReal}
    {U : Set X}
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) < ε → a x y < δ) :
    covering_number a δ U ≤ covering_number b ε (f.func '' U) := by
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  obtain ⟨S,hS,hcard⟩ := pull_net f hT h
  exact (iInf_le_of_le S (iInf_le_of_le hS le_rfl)).trans (by exact_mod_cast hcard)

theorem zero_cover_one {a : X → X → ENNReal} {U : Set X} (hU : U.Nonempty)
    {ε : ENNReal} (hε : 0 < ε) (h : ∀ x ∈ U, ∀ y ∈ U, a x y = 0) :
    covering_number a ε U = 1 := by
  classical
  apply le_antisymm _ (one_le_covering_number_of_nonempty a ε U hU)
  obtain ⟨c,hc⟩ := hU
  have hnet : InternalEpsilonNet a ε U {c} := by
    refine ⟨by simpa,?_⟩
    intro x hx
    exact ⟨c,by simp,by rw [h x hx c hc]; exact hε⟩
  simpa using
    (iInf_le_of_le ({c} : Finset X) (iInf_le_of_le hnet le_rfl) :
      covering_number a ε U ≤ (({c} : Finset X).card : ENNReal))

theorem log2_mono {a b : ENNReal} (ha : 0 < a) (hab : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  have hb : b ≠ 0 := ne_of_gt (ha.trans_le hab)
  by_cases hbt : b = ⊤
  · simp [log2_ereal,hbt]
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt hab
  simp only [log2_ereal,if_neg (ne_of_gt ha),if_neg hb,if_neg hbt,if_neg hat]
  apply EReal.coe_le_coe_iff.mpr
  exact Real.logb_le_logb_of_le (by norm_num)
    (ENNReal.toReal_pos (ne_of_gt ha) hat) (ENNReal.toReal_mono hbt hab)

theorem entropy_mono_cover {a b : X → X → ENNReal} {U V : Set X} {δ ε : ENNReal}
    (hU : U.Nonempty) (h : covering_number a δ U ≤ covering_number b ε V) :
    metric_entropy a δ U ≤ metric_entropy b ε V :=
  log2_mono
    (zero_lt_one.trans_le (one_le_covering_number_of_nonempty a δ U hU)) h

theorem finite_cover {a : X → X → ENNReal} (hself : ∀ x, a x x = 0)
    {U : Set X} (hU : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    covering_number a ε U < ⊤ := by
  classical
  have hn : InternalEpsilonNet a ε U hU.toFinset := by
    refine ⟨by simp,?_⟩
    intro x hx
    exact ⟨x,by simpa,hself x ▸ hε⟩
  exact (iInf_le_of_le hU.toFinset (iInf_le_of_le hn le_rfl)).trans_lt
    (ENNReal.natCast_lt_top _)

theorem finite_entropy {a : X → X → ENNReal} {U : Set X} (hU : U.Nonempty)
    {ε : ENNReal} (hf : covering_number a ε U < ⊤) :
    ∃ e : ℝ, metric_entropy a ε U = (e : EReal) := by
  have hz : covering_number a ε U ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_covering_number_of_nonempty a ε U hU))
  exact ⟨Real.logb 2 (covering_number a ε U).toReal,
    by simp [metric_entropy,log2_ereal,hz,hf.ne]⟩

def DeltaDefined (f : Operator X bot) (a b : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) : Prop :=
  covering_number a ε U < ⊤ ∨ covering_number b ε (f.func '' U) < ⊤
noncomputable def delta (f : Operator X bot) (a b : X → X → ENNReal) (ε : ENNReal)
    (U : Set X) (_h : DeltaDefined f a b ε U) : EReal :=
  metric_entropy a ε U - metric_entropy b ε (f.func '' U)

theorem delta_defined_finite (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    {U : Set X} (hne : U.Nonempty) (hU : U.Finite) {J K : Set I}
    (hJ : J.Nonempty) (hK : K.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    let a := subfamily_pseudometric d J
    let b := subfamily_pseudometric d K
    covering_number a ε U < ⊤ ∧ covering_number b ε (f.func '' U) < ⊤ ∧
      (∃ e : ℝ, metric_entropy a ε U = (e : EReal)) ∧
      (∃ e : ℝ, metric_entropy b ε (f.func '' U) = (e : EReal)) ∧
      DeltaDefined f a b ε U := by
  dsimp
  have ha :=
    finite_cover (subfamily_pseudometric_is_extended d J hJ hd).dist_self hU hε
  have hb := finite_cover (subfamily_pseudometric_is_extended d K hK hd).dist_self
    (hU.image f.func) hε
  exact ⟨ha,hb,finite_entropy hne ha,finite_entropy (hne.image _) hb,Or.inl ha⟩

theorem threshold_fiber (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {i j : I} {τ : ENNReal} (hτ : τ ≤ N d f U j i)
    {x : X} (hx : x ∈ U) :
    ball (d i) x τ ∩ U ⊆ SingleFiber d f j (f.func x) U := by
  rintro y ⟨hlt,hy⟩
  exact ⟨hy,below_uniform hy hx (hlt.trans_le hτ)⟩

theorem threshold_cover (f : Operator X bot) {a b : X → X → ENNReal}
    {A B : Set X} (hBA : B ⊆ A) {τ ε : ENNReal}
    (hτ : τ ≤ uniform f a b A A) (hε : 0 < ε) :
    covering_number b ε (f.func '' B) ≤ covering_number a τ B := by
  apply push_cover
  intro x hx y hy hxy
  rw [below_uniform (hBA hx) (hBA hy) (hxy.trans_le hτ)]
  exact hε

theorem threshold_entropy (f : Operator X bot) {a b : X → X → ENNReal}
    {A B : Set X} (hBA : B ⊆ A) (hB : B.Nonempty) {τ ε : ENNReal}
    (hτ : τ ≤ uniform f a b A A) (hε : 0 < ε) :
    metric_entropy b ε (f.func '' B) ≤ metric_entropy a τ B :=
  entropy_mono_cover (hB.image _) (threshold_cover f hBA hτ hε)

theorem small_domain_cover (f : Operator X bot) {a b : X → X → ENNReal}
    {U : Set X} (hne : U.Nonempty) {τs τr ε : ENNReal}
    (hd : diameter a U < τs) (hτ : τs ≤ τr)
    (hr : τr ≤ uniform f a b U U) (hε : 0 < ε) :
    covering_number b ε (f.func '' U) = 1 := by
  apply zero_cover_one (hne.image _) hε
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact (small_domain f a b U hd hτ).mp hr x hx y hy

theorem const_entropy (d : I → X → X → ENNReal) {f : Operator X bot} {U : Set X}
    (hne : U.Nonempty) {j : I} (hc : j ∈ Const d f U)
    {ε : ENNReal} (hε : 0 < ε) :
    covering_number (d j) ε (f.func '' U) = 1 ∧
    metric_entropy (d j) ε (f.func '' U) = 0 ∧
    ∃ h : DeltaDefined f (d j) (d j) ε U,
      delta f (d j) (d j) ε U h = metric_entropy (d j) ε U := by
  have hcov : covering_number (d j) ε (f.func '' U) = 1 := by
    apply zero_cover_one (hne.image _) hε
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact hc x hx y hy
  have he : metric_entropy (d j) ε (f.func '' U) = 0 := by
    simp [metric_entropy, hcov,log2_ereal,Real.logb]
  refine ⟨hcov,he,Or.inr (by rw [hcov]; exact ENNReal.one_lt_top),?_⟩
  simp [delta,he]

theorem ident_cover (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {U : Set X}
    {j : I} (hi : j ∈ Ident d f U) (ε : ENNReal) :
    covering_number (d j) ε (f.func '' U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (f.func '' U) = metric_entropy (d j) ε U := by
  have hcov : covering_number (d j) ε (f.func '' U) = covering_number (d j) ε U := by
    apply le_antisymm
    · exact push_cover f.func
        (fun x hx y hy h => by rwa [ident_distance d hd hi hx hy])
    · exact pull_cover f
        (fun x hx y hy h => by rwa [ident_distance d hd hi hx hy] at h)
  exact ⟨hcov,congrArg log2_ereal hcov⟩

theorem ident_delta (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {U : Set X}
    (hne : U.Nonempty) {j : I} (hi : j ∈ Ident d f U) {ε : ENNReal}
    (h : DeltaDefined f (d j) (d j) ε U) :
    delta f (d j) (d j) ε U h = 0 := by
  have hc := (ident_cover d hd hi ε).1
  have hf : covering_number (d j) ε U < ⊤ := by
    rcases h with h | h
    · exact h
    · rwa [hc] at h
  obtain ⟨e,he⟩ := finite_entropy hne hf
  simp [delta,(ident_cover d hd hi ε).2,he,← EReal.coe_sub]

theorem lip_cover (f : Operator X bot) {a b : X → X → ENNReal} {U : Set X}
    {L ε : ENNReal} (_hL : 0 < L) (_hLt : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) ≤ L * a x y) :
    covering_number b ε (f.func '' U) ≤ covering_number a (ε/L) U :=
  push_cover f.func
    (fun x hx y hy hxy => (h x hx y hy).trans_lt (ENNReal.mul_lt_of_lt_div' hxy))

theorem lip_delta (f : Operator X bot) {a b : X → X → ENNReal} {U : Set X}
    (hne : U.Nonempty) (htb : TotallyBoundedFor a U) {L ε : ENNReal}
    (hL : 0 < L) (hLt : L < ⊤) (hε : 0 < ε) (hεt : ε < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f.func x) (f.func y) ≤ L * a x y) :
    ∃ hh : DeltaDefined f a b ε U,
      (∃ e : ℝ, metric_entropy a ε U = (e : EReal)) ∧
      (∃ e : ℝ, metric_entropy b ε (f.func '' U) = (e : EReal)) ∧
      metric_entropy a ε U - metric_entropy a (ε/L) U ≤ delta f a b ε U hh := by
  have hδ : 0 < ε/L := ENNReal.div_pos (ne_of_gt hε) hLt.ne
  have hδt : ε/L < ⊤ := ENNReal.div_lt_top hεt.ne (ne_of_gt hL)
  have hf := htb ε hε hεt
  have hf' := htb (ε/L) hδ hδt
  have hc := lip_cover f (ε := ε) hL hLt h
  have ho := hc.trans_lt hf'
  exact ⟨Or.inl hf, finite_entropy hne hf,finite_entropy (hne.image _) ho,
    EReal.sub_le_sub le_rfl (entropy_mono_cover (hne.image _) hc)⟩

theorem colip_cover [Fintype I] (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (hpt : K i j < ⊤) (ε : ENNReal) :
    covering_number (d i) (ε / K i j) U ≤
      covering_number (d j) ε (f.func '' U) := by
  apply pull_cover f
  intro x hx y hy hout
  have hb : K i j * d i x y ≤ d j (f.func x) (f.func y) :=
    (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans
      (hK.2.2 x hx y hy j)
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hp)) (Or.inl hpt.ne)).mpr
    (by simpa [mul_comm] using hb.trans_lt hout)

theorem colip_delta [Fintype I] (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {K : I → I → ENNReal} {i j : I}
    (htb : TotallyBoundedFor (d i) U)
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (hpt : K i j < ⊤)
    {ε : ENNReal} (hε : 0 < ε) (hεt : ε < ⊤) :
    ∃ hh : DeltaDefined f (d i) (d j) ε U,
      delta f (d i) (d j) ε U hh ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hf := htb ε hε hεt
  exact ⟨Or.inl hf, EReal.sub_le_sub le_rfl
    (entropy_mono_cover hK.1 (colip_cover d hK hp hpt ε))⟩
end Chapter3

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set

def liftDist {A : Type} (d : A → A → ENNReal) : Option A → Option A → ENNReal
  | none, none => 0
  | some x, some y => d x y
  | _, _ => ⊤

theorem liftDist_valid {A : Type} [Nonempty A] (d : A → A → ENNReal)
    (h₁ : ∀ x, d x x = 0) (h₂ : ∀ x y, d x y = d y x)
    (h₃ : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (liftDist d) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨a⟩ := ‹Nonempty A›
    exact ⟨some a,by simp⟩
  · intro x
    cases x <;> simp [liftDist,h₁]
  · intro x y
    cases x <;> cases y <;> simp [liftDist,h₂]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [liftDist,h₃]
  · intro x hx
    cases x <;> simp_all [liftDist]

def realGauge (q : ℝ → ℝ) : Option ℝ → Option ℝ → ENNReal :=
  liftDist (fun x y => ENNReal.ofReal |q x - q y|)
theorem realGauge_valid (q : ℝ → ℝ) :
    ExtendedPseudoMetric (Option ℝ) none (realGauge q) := by
  apply liftDist_valid
  · intro x
    simp
  · intro x y
    rw [abs_sub_comm]
  · intro x y z
    exact (ENNReal.ofReal_le_ofReal (abs_sub_le (q x) (q y) (q z))).trans
      ENNReal.ofReal_add_le

def realOp (f : ℝ → ℝ) : Operator (Option ℝ) none := ⟨Option.map f,rfl⟩
def realSet (S : Set ℝ) : Set (Option ℝ) := some '' S
theorem realSet_domain (f : ℝ → ℝ) (S : Set ℝ) :
    realSet S ⊆ dom (realOp f) := by
  rintro _ ⟨x,hx,rfl⟩
  simp [dom,realOp]
theorem realSet_nonempty {S : Set ℝ} (h : S.Nonempty) :
    (realSet S).Nonempty := h.image _

def disc {A B : Type} [DecidableEq B] (q : A → B) (x y : A) : ENNReal :=
  if q x = q y then 0 else 1
theorem disc_valid {A B : Type} [Nonempty A] [DecidableEq B] (q : A → B) :
    ExtendedPseudoMetric (Option A) none (liftDist (disc q)) := by
  apply liftDist_valid
  · intro x
    simp [disc]
  · intro x y
    simp [disc,eq_comm]
  · intro x y z
    by_cases hxy : q x = q y <;> by_cases hyz : q y = q z <;>
      by_cases hxz : q x = q z <;> simp_all [disc]

namespace Swap
abbrev P := Fin 2
def d : Unit → Option P → Option P → ENNReal := fun _ => liftDist (disc id)
def f : Operator (Option P) none := ⟨Option.map (fun x => 1-x),rfl⟩
def U : Set (Option P) := {some 0,some 1}
theorem valid : ExtendedPseudoMetric (Option P) none (d ()) := disc_valid id
theorem domain : U ⊆ dom (f*f) := by
  intro x hx
  simp only [U,mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;>
    norm_num [dom,f,operator_monoid,operator_compose] <;> decide
theorem image : f.func '' U = U := by
  ext x
  simp [U,f,Set.image_insert_eq,Set.image_singleton,or_comm]
theorem active : Active d f U = univ ∧ Ident d f U = ∅ := by
  have hc : () ∉ Const d f U := by
    intro h
    have hh := h (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,f,liftDist,disc] at hh
  have hi : () ∉ Ident d f U := by
    intro h
    have hh := h.2 (some 0) (by simp [U])
    norm_num [d,f,liftDist,disc] at hh
  constructor <;> ext i <;> cases i <;> simp [Active,hc,hi]
theorem composite : Ident d (f*f) U = univ ∧ Active d (f*f) U = ∅ := by
  have hc : () ∉ Const d (f*f) U := by
    intro h
    have hh := h (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,f,liftDist,disc,operator_monoid,operator_compose] at hh
  have hi : () ∈ Ident d (f*f) U := by
    refine ⟨hc,?_⟩
    intro x hx
    simp only [U,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;>
      norm_num [d,f,liftDist,disc,operator_monoid,operator_compose]
  constructor <;> ext i <;> cases i <;> simp [Active,hi]
theorem reverse_failures :
    ¬ (Active d f U ∪ Active d f (f.func '' U) ⊆ Active d (f*f) U) ∧
    ¬ (Ident d (f*f) U ⊆ Ident d f U ∩ Ident d f (f.func '' U)) := by
  simp [image,active.1,active.2,composite.1,composite.2]
end Swap

namespace Seven
/- some 0=a, 1=b, 2=p, 3=q, 4=r, 5=s; none is the absorber. -/
def q (x : Fin 6) : Fin 6 := if x = 3 then 2 else x
def d (i : Fin 2) : Option (Fin 6) → Option (Fin 6) → ENNReal :=
  if i = 0 then liftDist (disc q) else liftDist (disc id)
def f : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some a => if a = 0 then some 2 else if a = 1 then some 3 else none
    | none => none,rfl⟩
def g : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some a => if a = 2 then some 4 else if a = 3 then some 5 else none
    | none => none,rfl⟩
def U : Set (Option (Fin 6)) := {some 0,some 1}
theorem valid (i : Fin 2) :
    ExtendedPseudoMetric (Option (Fin 6)) none (d i) := by
  dsimp [d]
  split <;> apply disc_valid
theorem domain : U ⊆ dom (g*f) := by
  intro x hx
  simp only [U,mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · change (some (4 : Fin 6)) ≠ none
    simp
  · change (some (5 : Fin 6)) ≠ none
    simp
theorem inner : (0 : Fin 2) ∈ Const d f U := by
  intro x hx y hy
  simp only [U,mem_insert_iff,mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [d,f,liftDist,disc,q]
theorem outer_fails :
    (0 : Fin 2) ∉ Const d (g*f) U ∧ d 1 (some 2) (some 3) = 1 := by
  constructor
  · intro h
    have hh := h (some 0) (by simp [U]) (some 1) (by simp [U])
    change (1 : ENNReal) = 0 at hh
    norm_num at hh
  · norm_num [d,liftDist,disc]
    decide
end Seven

namespace Infinite
def d (i : Fin 2) : Option (Fin 2) → Option (Fin 2) → ENNReal :=
  liftDist (fun x y => if x = y then 0 else if i = 0 then ⊤ else 1)
def U : Set (Option (Fin 2)) := {some 0,some 1}
theorem valid (i : Fin 2) :
    ExtendedPseudoMetric (Option (Fin 2)) none (d i) := by
  apply liftDist_valid
  · intro x
    simp
  · intro x y
    simp [eq_comm]
  · intro x y z
    by_cases hxy : x=y <;> by_cases hyz : y=z <;>
      by_cases hxz : x=z <;> simp_all
theorem domain : U ⊆ dom (1 : Operator (Option (Fin 2)) none) := by
  intro x hx
  rcases hx with rfl | rfl <;> simp [dom,operator_monoid,operator_identity]
theorem uniform_infinite (j : Fin 2) :
    uniform (1 : Operator (Option (Fin 2)) none) (d 0) (d j) U U = ⊤ := by
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply le_radius_iff.mpr
  intro x hx hlt
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp_all [d,liftDist,operator_monoid,operator_identity]
theorem not_const (j : Fin 2) :
    j ∉ Const d (1 : Operator (Option (Fin 2)) none) U := by
  intro h
  have hh := h (some 0) (by simp [U]) (some 1) (by simp [U])
  fin_cases j <;> norm_num [d,liftDist,operator_monoid,operator_identity] at hh
end Infinite

namespace Affine
def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => realGauge abs
def f := realOp (fun x => 2*x-1)
def U : Set (Option ℝ) := {some 0,some 1}
theorem valid : ExtendedPseudoMetric (Option ℝ) none (d ()) := realGauge_valid _
theorem domain : U ⊆ dom (f*f) := by
  intro x hx
  rcases hx with rfl | rfl <;>
    simp [dom,f,realOp,operator_monoid,operator_compose]
theorem first_fiber : SingleFiber d f () (f.func (some 0)) U = U := by
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx,?_⟩
    rcases hx with rfl | rfl <;> norm_num [d,f,realOp,realGauge,liftDist]
theorem first_const : () ∈ Const d f U := by
  intro x hx y hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [d,f,realOp,realGauge,liftDist]
theorem second_fiber :
    SingleFiber d (f*f) () ((f*f).func (some 0)) U = {some 0} := by
  ext x
  constructor
  · rintro ⟨hx,he⟩
    rcases hx with rfl | rfl
    · simp
    · norm_num [d,f,realOp,realGauge,liftDist,operator_monoid,operator_compose] at he
  · rintro rfl
    norm_num [SingleFiber,U,d,f,realOp,realGauge,liftDist,operator_monoid,operator_compose]
theorem second_active : () ∈ Active d (f*f) U := by
  have hc : () ∉ Const d (f*f) U := by
    intro h
    have hh := h (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,f,realOp,realGauge,liftDist,operator_monoid,operator_compose] at hh
  have hi : () ∉ Ident d (f*f) U := by
    intro h
    have hh := h.2 (some 0) (by simp [U])
    norm_num [d,f,realOp,realGauge,liftDist,operator_monoid,operator_compose] at hh
  exact fun h => h.elim hc hi
end Affine

theorem point_constant_square {X : Type} {bot : X} (f : Operator X bot) {U : Set X}
    {v : X} (h : ∀ x ∈ U, f.func x = v) :
    (∀ x ∈ U, (f*f).func x = f.func v) ∧
    ((U ⊆ dom (f*f)) ↔ (U = ∅ ∨ f.func v ≠ bot)) := by
  have he : ∀ x ∈ U, (f*f).func x = f.func v :=
    fun x hx => congrArg f.func (h x hx)
  refine ⟨he,?_⟩
  classical
  constructor
  · intro hu
    by_cases hU : U = ∅
    · exact Or.inl hU
    · obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hU
      right
      have hh := hu hx
      change f.func (f.func x) ≠ bot at hh
      rwa [h x hx] at hh
  · rintro (rfl | hv)
    · exact empty_subset _
    · intro x hx
      change (f*f).func x ≠ bot
      rwa [he x hx]
end Chapter3

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
variable {X I : Type} {bot : X}

theorem composite_truncate (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot)
    {U : Set X} {x y : X} {j : I} (_hx : x ∈ dom f) (_hy : y ∈ dom f)
    (_hfx : f.func x ∈ U) (_hfy : f.func y ∈ U)
    (h : f.func y ∈ SingleFiber d g j (g.func (f.func x)) U) :
    d j ((g*f).func x) ((g*f).func y) = 0 :=
  fiber_truncate d hd (f := g) (x := f.func x) (y := f.func y) h

theorem finite_delta {f : Operator X bot} {a b : X → X → ENNReal}
    {U : Set X} {ε : ENNReal} (h : DeltaDefined f a b ε U)
    (ha : ∃ e : ℝ, metric_entropy a ε U = (e : EReal))
    (hb : ∃ e : ℝ, metric_entropy b ε (f.func '' U) = (e : EReal)) :
    ∃ e : ℝ, delta f a b ε U h = (e : EReal) := by
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := hb
  exact ⟨u-v,by simp [delta,hu,hv]⟩

def ValidChain : List (Operator X bot) → Set X → Prop
  | [], _ => True
  | f :: fs, U => U ⊆ dom f ∧ ValidChain fs (f.func '' U)
theorem chain_domains (fs : List (Operator X bot)) {U : Set X}
    (h : U ⊆ dom (chain fs)) : ValidChain fs U := by
  induction fs generalizing U with
  | nil => trivial
  | cons f fs ih =>
    refine ⟨?_,ih ?_⟩
    · intro x hx hn
      apply h hx
      change (chain fs).func (f.func x) = bot
      rw [hn,(chain fs).preserves_bot]
    · rintro _ ⟨x,hx,rfl⟩
      exact h hx

noncomputable def channelType (σ : Scale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty})
    (τs τr : ENNReal) (i j : I) :=
  thresholdType (σ.1 i A) (N d f A.1 j i) τs τr
theorem threshold_bits (s r τs τr : ENNReal) :
    (thresholdType s r τs τr = (true,true) ↔ s < τs ∧ τr ≤ r) ∧
    (thresholdType s r τs τr = (true,false) ↔ s < τs ∧ r < τr) ∧
    (thresholdType s r τs τr = (false,true) ↔ τs ≤ s ∧ τr ≤ r) ∧
    (thresholdType s r τs τr = (false,false) ↔ τs ≤ s ∧ r < τr) := by
  simp [thresholdType,Prod.ext_iff,not_lt,not_le]

theorem finite_inf_attained [Fintype I] (J : Set I) (hJ : J.Nonempty)
    (v : I → ENNReal) : ∃ j ∈ J, (⨅ k ∈ J, v k) = v j := by
  classical
  obtain ⟨j,hj,hmin⟩ := J.exists_min_image v J.toFinite hJ
  refine ⟨j,hj,le_antisymm (iInf_le_of_le j (iInf_le _ hj)) ?_⟩
  exact le_iInf fun k => le_iInf fun hk => hmin k hk

theorem entropy_top_iff {a : X → X → ENNReal} {U : Set X} (hne : U.Nonempty)
    (ε : ENNReal) :
    metric_entropy a ε U = ⊤ ↔ covering_number a ε U = ⊤ := by
  have hz : covering_number a ε U ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_covering_number_of_nonempty a ε U hne))
  by_cases ht : covering_number a ε U = ⊤ <;>
    simp [metric_entropy,log2_ereal,hz,ht]
theorem delta_guard (f : Operator X bot) (a b : X → X → ENNReal) {U : Set X}
    (hne : U.Nonempty) {ε : ENNReal} (h : DeltaDefined f a b ε U) :
    ¬ (metric_entropy a ε U = ⊤ ∧ metric_entropy b ε (f.func '' U) = ⊤) := by
  rintro ⟨ha,hb⟩
  rw [entropy_top_iff hne] at ha
  rw [entropy_top_iff (hne.image _)] at hb
  rcases h with h | h <;> simp_all

theorem diameter_pair {a : X → X → ENNReal} (hself : ∀ x, a x x = 0)
    (hsym : ∀ x y, a x y = a y x) (x y : X) :
    diameter a {x,y} = a x y := by
  apply le_antisymm
  · apply iSup_le
    intro z
    apply iSup_le
    intro hz
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> simp [hself,hsym]
  · exact le_iSup_of_le x (le_iSup_of_le (by simp)
      (le_iSup_of_le y (le_iSup_of_le (by simp) le_rfl)))

theorem scale_reverse_counterexample :
    let a := realGauge id
    let A : Set (Option ℝ) := {some 0,some 1}
    let B : Set (Option ℝ) := {some 0}
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (1 : Operator (Option ℝ) none) ∧
      diameter a B = 0 ∧ diameter a A = 1 ∧
      diameter a B < (1/2 : ENNReal) ∧ (1/2 : ENNReal) ≤ diameter a A := by
  dsimp
  have hA : diameter (realGauge id) {some 0,some 1} = 1 := by
    rw [diameter_pair (realGauge_valid id).dist_self (realGauge_valid id).symm]
    norm_num [realGauge,liftDist]
  have hB : diameter (realGauge id) {some 0} = 0 := by
    simp [diameter,realGauge,liftDist]
  refine ⟨by simp,by simp,?_,hB,hA,?_,?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom]
  · rw [hB]
    norm_num
  · rw [hA]
    norm_num

namespace Step
def a := realGauge id
noncomputable def f := realOp (fun x => if x < 0 then 0 else 1)
def U : Set (Option ℝ) :=
  realSet {x | (-1 ≤ x ∧ x < 0) ∨ (0 < x ∧ x ≤ 1)}
theorem valid : ExtendedPseudoMetric (Option ℝ) none a := realGauge_valid id
theorem domain : U.Nonempty ∧ U ⊆ dom f := by
  refine ⟨⟨some 1,?_⟩,realSet_domain _ _⟩
  exact ⟨1,by norm_num,rfl⟩

theorem point_radius {y : ℝ} (hy : some y ∈ U) :
    radius f a a U (some y) = ENNReal.ofReal |y| ∧ 0 < ENNReal.ofReal |y| := by
  have hyU : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1) := by
    obtain ⟨z,hz,he⟩ := hy
    cases Option.some.inj he
    exact hz
  have hyne : y ≠ 0 := by
    rcases hyU with h | h <;> linarith
  have hyp : 0 < |y| := abs_pos.mpr hyne
  refine ⟨le_antisymm ?_ ?_,by simpa using hyp⟩
  · by_contra hn
    obtain ⟨q,hq,hqr⟩ :=
      ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hqy : |y| < (q : ℝ) := by
      have he : ENNReal.ofReal (q : ℝ) = (q : ENNReal) := by simp
      have hqp : 0 < (q : ℝ) := by
        have hh : 0 < (q : ENNReal) := (zero_le _).trans_lt hq
        exact_mod_cast hh
      rw [← he] at hq
      exact (ENNReal.ofReal_lt_ofReal_iff hqp).mp hq
    let t : ℝ := min (((q : ℝ)-|y|)/2) (1/2)
    have ht : 0 < t := lt_min (by linarith) (by norm_num)
    have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have htq : t + |y| < (q : ℝ) := by
      have hh := min_le_left (((q : ℝ)-|y|)/2) (1/2)
      dsimp [t]
      linarith
    by_cases hy0 : y < 0
    · have hx : some t ∈ U := ⟨t,Or.inr ⟨ht,ht1⟩,rfl⟩
      have hd : a (some t) (some y) < (q : ENNReal) := by
        change ENNReal.ofReal |t-y| < (q : ENNReal)
        rw [abs_of_nonneg (by linarith)]
        have he : ENNReal.ofReal (q : ℝ) = (q : ENNReal) := by simp
        rw [← he]
        apply (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg y])).mpr
        rw [abs_of_neg hy0] at htq
        linarith
      have hb := below_radius (f := f) (a := a) (b := a) hx (hd.trans hqr)
      norm_num [a,f,realOp,realGauge,liftDist,hy0,not_lt.mpr ht.le] at hb
    · have hypos : 0 < y :=
        lt_of_le_of_ne (not_lt.mp hy0) (Ne.symm hyne)
      have hx : some (-t) ∈ U :=
        ⟨-t,Or.inl ⟨by linarith,by linarith⟩,rfl⟩
      have hd : a (some (-t)) (some y) < (q : ENNReal) := by
        change ENNReal.ofReal |(-t)-y| < (q : ENNReal)
        rw [abs_of_nonpos (by linarith)]
        have he : ENNReal.ofReal (q : ℝ) = (q : ENNReal) := by simp
        rw [← he]
        apply (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg y])).mpr
        rw [abs_of_pos hypos] at htq
        linarith
      have hb := below_radius (f := f) (a := a) (b := a) hx (hd.trans hqr)
      norm_num [a,f,realOp,realGauge,liftDist,hy0,show -t < 0 by linarith] at hb
  · apply le_radius_iff.mpr
    rintro _ ⟨x,hx,rfl⟩ hxy
    have hr : |x-y| < |y| := (ENNReal.ofReal_lt_ofReal_iff hyp).mp hxy
    by_cases hx0 : x < 0 <;> by_cases hy0 : y < 0
    · simp [a,f,realOp,realGauge,liftDist,hx0,hy0]
    · exfalso
      rw [abs_of_nonpos (by linarith),abs_of_nonneg (not_lt.mp hy0)] at hr
      linarith
    · exfalso
      rw [abs_of_nonneg (by linarith),abs_of_neg hy0] at hr
      linarith
    · simp [a,f,realOp,realGauge,liftDist,hx0,hy0]

theorem legal_radii {y : ℝ} (hy : some y ∈ U) (r : ENNReal) :
    Legal f a a U (some y) r ↔
      0 < r ∧ r < ⊤ ∧ r ≤ ENNReal.ofReal |y| := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,(legal_le_radius h).trans_eq (point_radius hy).1⟩
  · rintro ⟨h,hf,hr⟩
    refine ⟨h,hf,le_radius_iff.mp ?_⟩
    rwa [(point_radius hy).1]

theorem uniform_zero : uniform f a a U U = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  obtain ⟨q,hq,hqr⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  let t : ℝ := min ((q : ℝ)/4) (1/2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htq : 2*t < (q : ℝ) := by
    have := min_le_left ((q : ℝ)/4) (1/2)
    dsimp [t]
    linarith
  have hx : some (-t) ∈ U := ⟨-t,Or.inl ⟨by linarith,by linarith⟩,rfl⟩
  have hy : some t ∈ U := ⟨t,Or.inr ⟨ht,ht1⟩,rfl⟩
  have hsep : 0 < a (f.func (some (-t))) (f.func (some t)) := by
    norm_num [a,f,realOp,realGauge,liftDist,
      show -t < 0 by linarith,not_lt.mpr ht.le]
  have hd : a (some (-t)) (some t) < (q : ENNReal) := by
    change ENNReal.ofReal |(-t)-t| < (q : ENNReal)
    rw [abs_of_nonpos (by linarith)]
    rw [show -(-t-t) = 2*t by ring]
    have he : ENNReal.ofReal (q : ℝ) = (q : ENNReal) := by simp
    rw [← he]
    exact (ENNReal.ofReal_lt_ofReal_iff hqreal).mpr htq
  exact not_lt_of_ge (separated_input hx hy hsep) (hd.trans hqr)
end Step
end Chapter3
```

```json filename=alignment.json
{
  "case_id": "MG-C003",
  "version": "0.1.1",
  "items": [
    {"id":"CH03-D01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Const"},{"file":"Main.lean","name":"Chapter3.Ident"},{"file":"Main.lean","name":"Chapter3.Active"},{"file":"Main.lean","name":"Chapter3.component_partition"}],"representation":"任意分量按常值优先定义三类；证明互斥及覆盖。","dependencies":[]},
    {"id":"CH03-D02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Fiber"},{"file":"Main.lean","name":"Chapter3.SingleFiber"},{"file":"Main.lean","name":"Chapter3.subfamily_zero"},{"file":"Main.lean","name":"Chapter3.fiber_representation"}],"representation":"子族逐分量零距定义纤维；证明等价于复合伪度量零距。","dependencies":[]},
    {"id":"CH03-D03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.PointRel"},{"file":"Main.lean","name":"Chapter3.ZeroRel"},{"file":"Main.lean","name":"Chapter3.imageSetoid"},{"file":"Main.lean","name":"Chapter3.ImageQuotient"},{"file":"Main.lean","name":"Chapter3.imageClass"},{"file":"Main.lean","name":"Chapter3.FiberLE"},{"file":"Main.lean","name":"Chapter3.zeroRel_fiber"}],"representation":"点对关系限于U×U；实际像集取零距商；预序为关系包含，并证明纤维对应。","dependencies":["CH03-D02"]},
    {"id":"CH03-D04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Legal"},{"file":"Main.lean","name":"Chapter3.radius"},{"file":"Main.lean","name":"Chapter3.legal_ball"},{"file":"Main.lean","name":"Chapter3.le_radius_iff"}],"representation":"半径为合法有限正半径的上确界；球包含与逐点公式等价。","dependencies":[]},
    {"id":"CH03-D05","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.uniform"},{"file":"Main.lean","name":"Chapter3.N"}],"representation":"uniform在指定基点集合取下确界；N的首指标为输出行。","dependencies":["CH03-D04"]},
    {"id":"CH03-D06","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Scale"},{"file":"Main.lean","name":"Chapter3.diameter"},{"file":"Main.lean","name":"Chapter3.diameterScale"},{"file":"Main.lean","name":"Chapter3.thresholdType"},{"file":"Main.lean","name":"Chapter3.channelType"},{"file":"Main.lean","name":"Chapter3.threshold_bits"}],"representation":"尺度定义在非空集合且单调；默认直径；Bool对精确表示两个阈值判断。","dependencies":["CH03-D05"]},
    {"id":"CH03-D07","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.TotallyBoundedFor"},{"file":"Main.lean","name":"Chapter3.covering_representation"}],"representation":"复用冻结内部中心覆盖数和熵；证明球并集表述对应；全有界遍历有限正精度。","dependencies":[]},
    {"id":"CH03-D08","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.DeltaDefined"},{"file":"Main.lean","name":"Chapter3.delta"},{"file":"Main.lean","name":"Chapter3.delta_guard"},{"file":"Main.lean","name":"Chapter3.finite_delta"}],"representation":"两端至少一覆盖数有限才定义EReal熵差；证明排除双无穷及有限实数差对应。","dependencies":["CH03-D07"]},
    {"id":"CH03-P01-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_zero_row"}],"representation":"常值条件给全部点对零行求和上界。","dependencies":["CH03-D01"]},
    {"id":"CH03-P01-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_colip_zero"}],"representation":"任意正输入距离见证迫使指定co-Lip条目为零。","dependencies":["CH03-D01"]},
    {"id":"CH03-P01-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.ident_distance"}],"representation":"由逐点零距双向传递证明所有输入点对保距。","dependencies":["CH03-D01"]},
    {"id":"CH03-P02-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.compose_active"}],"representation":"在实际中间像域证明两步有效分量包含。","dependencies":["CH03-D01","CH03-P01-03","CH03-P02-03","CH03-P04-01"]},
    {"id":"CH03-P02-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.chain"},{"file":"Main.lean","name":"Chapter3.activeSteps"},{"file":"Main.lean","name":"Chapter3.chain_active"},{"file":"Main.lean","name":"Chapter3.ValidChain"},{"file":"Main.lean","name":"Chapter3.chain_domains"}],"representation":"列表按时间顺序复合；递推实际像域，证明全部域合法及任意长度包含，含零步。","dependencies":["CH03-D01","CH03-P02-01"]},
    {"id":"CH03-P02-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.compose_ident"}],"representation":"复合逐点零距且排除常值优先分支。","dependencies":["CH03-D01","CH03-P01-03"]},
    {"id":"CH03-P03-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Swap.d"},{"file":"Main.lean","name":"Chapter3.Swap.f"},{"file":"Main.lean","name":"Chapter3.Swap.U"},{"file":"Main.lean","name":"Chapter3.Swap.valid"},{"file":"Main.lean","name":"Chapter3.Swap.domain"},{"file":"Main.lean","name":"Chapter3.Swap.image"},{"file":"Main.lean","name":"Chapter3.Swap.active"},{"file":"Main.lean","name":"Chapter3.Swap.composite"},{"file":"Main.lean","name":"Chapter3.Swap.reverse_failures"}],"representation":"Option(Fin2)表示三点空间；完整验证换位及两条逆包含失败。","dependencies":["CH03-D01"]},
    {"id":"CH03-P04-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.outer_const"}],"representation":"外侧在实际像域常值，代入像点得复合常值。","dependencies":["CH03-D01"]},
    {"id":"CH03-P04-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Seven.d"},{"file":"Main.lean","name":"Chapter3.Seven.f"},{"file":"Main.lean","name":"Chapter3.Seven.g"},{"file":"Main.lean","name":"Chapter3.Seven.U"},{"file":"Main.lean","name":"Chapter3.Seven.valid"},{"file":"Main.lean","name":"Chapter3.Seven.domain"},{"file":"Main.lean","name":"Chapter3.Seven.inner"},{"file":"Main.lean","name":"Chapter3.Seven.outer_fails"}],"representation":"Option(Fin6)表示七点；0,1为a,b，2,3为p,q，4,5为r,s；双分量合法并给出反例。","dependencies":["CH03-D01"]},
    {"id":"CH03-P05-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.inner_const_lip"}],"representation":"指定输出行仅同分量输入时内侧常值传给复合；不要求系数有限。","dependencies":["CH03-D01"]},
    {"id":"CH03-P06-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_target"}],"representation":"任意零距目标对应的子族纤维相等。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_cover"}],"representation":"证明每个像目标纤维非空且纤维并集恰为U。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_equal_or_disjoint"},{"file":"Main.lean","name":"Chapter3.fiber_cover"}],"representation":"全部纤维相等或不交；连同非空和覆盖给出去重分划。","dependencies":["CH03-D02","CH03-P06-01"]},
    {"id":"CH03-P06-04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_intersection"}],"representation":"非空子族纤维等于全部单分量纤维的交。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-05","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_antitone"}],"representation":"更多输出分量要求给出更小纤维。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-06","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_singleton"},{"file":"Main.lean","name":"Chapter3.fiber_all_subset"}],"representation":"单元素子族等式及全子族向每分量的包含。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-07","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.ident_fiber"}],"representation":"恒等分量对任意目标的纤维等于输入零距类。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P06-08","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_fiber"},{"file":"Main.lean","name":"Chapter3.const_fiber_empty"}],"representation":"像内目标纤维为U；与之正距离的任意目标纤维为空。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P07-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Factors"},{"file":"Main.lean","name":"Chapter3.factors_iff"}],"representation":"实际像域上的因子映射存在推出点值关系包含。","dependencies":["CH03-D03"]},
    {"id":"CH03-P07-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Factors"},{"file":"Main.lean","name":"Chapter3.factors_iff"}],"representation":"从实际像点选择输入代表元构造因子映射并验证公式；空像域也适用。","dependencies":["CH03-D03"]},
    {"id":"CH03-P07-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.factors_both"}],"representation":"双向点值变换等价于点值关系相等。","dependencies":["CH03-D03","CH03-P07-01","CH03-P07-02"]},
    {"id":"CH03-P07-04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.factor_lip"}],"representation":"在实际像域证明任意规定T的L/K界；K正有限且L有限。","dependencies":["CH03-D03"]},
    {"id":"CH03-P08-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.QuotientFactors"},{"file":"Main.lean","name":"Chapter3.quotient_factors_iff"}],"representation":"实际像零距商；构造代表元无关的Quotient.lift并双向验证规定公式。","dependencies":["CH03-D03"]},
    {"id":"CH03-P08-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.quotient_factors_both"}],"representation":"双向规定商映射等价于零距关系相等。","dependencies":["CH03-D03","CH03-P08-01"]},
    {"id":"CH03-P08-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.SeparatesOn"},{"file":"Main.lean","name":"Chapter3.relations_equal_on_separated_image"},{"file":"Main.lean","name":"Chapter3.separated_factor_criteria"}],"representation":"分别假设两个实际像集分离，证明两种关系及单向、双向判据一致。","dependencies":["CH03-D03","CH03-P07-01","CH03-P07-02","CH03-P08-01"]},
    {"id":"CH03-P09-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiberLE_refl"},{"file":"Main.lean","name":"Chapter3.fiberLE_trans"}],"representation":"固定U，关系包含给出预序的自反及传递。","dependencies":["CH03-D03"]},
    {"id":"CH03-P09-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.relation_chain"}],"representation":"对任意自然数端点a≤b归纳证明逐步包含的复合；适用于任意有限截断。","dependencies":[]},
    {"id":"CH03-P09-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.relation_chain_strict"}],"representation":"任一步真包含给端点真包含，并实际给出端点差集元素。","dependencies":["CH03-P09-02"]},
    {"id":"CH03-P10-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.realGauge"},{"file":"Main.lean","name":"Chapter3.realOp"},{"file":"Main.lean","name":"Chapter3.realSet"},{"file":"Main.lean","name":"Chapter3.Step.a"},{"file":"Main.lean","name":"Chapter3.Step.f"},{"file":"Main.lean","name":"Chapter3.Step.U"},{"file":"Main.lean","name":"Chapter3.Step.valid"},{"file":"Main.lean","name":"Chapter3.Step.domain"}],"representation":"Option实线以none为吸收元；通常距离及阶跃算子；验证固定U非空且在定义域内。","dependencies":[]},
    {"id":"CH03-P10-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Step.point_radius"},{"file":"Main.lean","name":"Chapter3.Step.legal_radii"}],"representation":"固定U中每个实基点，合法有限正半径恰满足r≤|y|，上确界等于|y|且正。","dependencies":["CH03-D04","CH03-P10-01"]},
    {"id":"CH03-P10-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Step.uniform_zero"}],"representation":"在同一固定U构造任意接近零的异号基点，证明统一半径为零。","dependencies":["CH03-D04","CH03-D05","CH03-P10-01","CH03-P18-02"]},
    {"id":"CH03-P11-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_subfamily_fiber"}],"representation":"子族各分量常值时任一输入基点的像目标纤维为U。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P11-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_subfamily_radius"}],"representation":"子族输出两两零距，证明所有基点及统一半径均为无穷。","dependencies":["CH03-D01","CH03-D04","CH03-D05","CH03-D02"]},
    {"id":"CH03-P11-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Infinite.d"},{"file":"Main.lean","name":"Chapter3.Infinite.U"},{"file":"Main.lean","name":"Chapter3.Infinite.valid"},{"file":"Main.lean","name":"Chapter3.Infinite.domain"},{"file":"Main.lean","name":"Chapter3.Infinite.uniform_infinite"},{"file":"Main.lean","name":"Chapter3.Infinite.not_const"}],"representation":"合法两点无穷输入距离模型；输入0、输出j遍历Fin2，涵盖同分量与异分量两分支。","dependencies":["CH03-D01","CH03-D04","CH03-D05"]},
    {"id":"CH03-P12-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.ident_image_fiber"}],"representation":"利用恒等分量保距，像目标纤维恰为输入基点零距类。","dependencies":["CH03-D01","CH03-D02","CH03-P01-03"]},
    {"id":"CH03-P12-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.ident_radius_lower"}],"representation":"有限正r的球中只有输入零距点时，证明r是合法半径并给出下界。","dependencies":["CH03-D01","CH03-D04","CH03-P01-03"]},
    {"id":"CH03-P13-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.radius_subfamily"},{"file":"Main.lean","name":"Chapter3.finite_inf_attained"}],"representation":"点态子族半径为各单分量半径下确界；有限非空时证明最小值取得。","dependencies":["CH03-D02","CH03-D04"]},
    {"id":"CH03-P13-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.uniform_subfamily"},{"file":"Main.lean","name":"Chapter3.finite_inf_attained"}],"representation":"交换基点和分量下确界，结合最小值取得给出统一半径最小值公式。","dependencies":["CH03-D04","CH03-D05","CH03-P13-01"]},
    {"id":"CH03-P13-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.uniform_subfamily_antitone"}],"representation":"子族包含经分量下确界公式推出统一半径反单调。","dependencies":["CH03-D05","CH03-P13-02"]},
    {"id":"CH03-P14-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_truncate"}],"representation":"纤维成员的输出零距由对称性转为原文方向。","dependencies":["CH03-D02"]},
    {"id":"CH03-P14-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.below_radius"}],"representation":"严格小于上确界时从合法集提取更大的有限正半径，再应用球内条件。","dependencies":["CH03-D04"]},
    {"id":"CH03-P14-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.composite_truncate"}],"representation":"显式保留上游定义域、两像点在下游域及纤维条件，证明复合输出零距。","dependencies":["CH03-D02","CH03-P14-01"]},
    {"id":"CH03-P15-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.radius_compose"}],"representation":"下游在实际像域保持零距时，给出复合统一半径下界。","dependencies":["CH03-D04","CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P15-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.radius_compose_lip"}],"representation":"有限正L拉回下游实际像域的统一半径；扩展数除法涵盖右端0及无穷。","dependencies":["CH03-D04","CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P16-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.threshold_cases"},{"file":"Main.lean","name":"Chapter3.threshold_bits"}],"representation":"四种Bool组合逐一等价于互补不等式，故互斥且穷尽。","dependencies":["CH03-D06"]},
    {"id":"CH03-P16-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.threshold_scale_mono"}],"representation":"尺度严格小于阈值的判断随尺度阈值增大保持。","dependencies":[]},
    {"id":"CH03-P16-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.threshold_radius_antitone"}],"representation":"半径大于等于阈值的判断随零化阈值增大反单调。","dependencies":[]},
    {"id":"CH03-P17-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.scale_restrict"}],"representation":"任意单调尺度在非空域缩小时不增，并保留严格阈值判断。","dependencies":["CH03-D06"]},
    {"id":"CH03-P17-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.radius_restrict"}],"representation":"固定任意基点，限制评估域使合法半径上确界不减。","dependencies":["CH03-D04"]},
    {"id":"CH03-P17-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.uniform_restrict"}],"representation":"同时缩小评估域及下确界基点集合，统一半径不减。","dependencies":["CH03-D04","CH03-D05","CH03-P17-02"]},
    {"id":"CH03-P17-04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.scale_reverse_counterexample"}],"representation":"带吸收元通常实线，A={0,1}、B={0}及阈值1/2，证明域条件、两直径及反向失败。","dependencies":["CH03-D06"]},
    {"id":"CH03-P18-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.below_uniform"}],"representation":"输入距离严格小于统一下确界则小于该基点半径，输出归零。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02"]},
    {"id":"CH03-P18-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.separated_input"}],"representation":"由正输出距离及单步判据逆否得到输入距离下界。","dependencies":["CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P18-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.separation_witness"}],"representation":"每个规定有限正α，从下确界及非法球提取两点，再取有限正ε；输出无穷亦适用。","dependencies":["CH03-D04","CH03-D05"]},
    {"id":"CH03-P19-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.threshold_fiber"}],"representation":"统一半径达到阈值时，任意基点的阈值球交评估域包含在纤维中。","dependencies":["CH03-D02","CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P19-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.push_net"},{"file":"Main.lean","name":"Chapter3.push_cover"},{"file":"Main.lean","name":"Chapter3.threshold_cover"}],"representation":"任意B子集的内部输入中心映到内部输出中心且基数不增；下确界证明涵盖空集及无有限覆盖。","dependencies":["CH03-D07","CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P19-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.log2_mono"},{"file":"Main.lean","name":"Chapter3.entropy_mono_cover"},{"file":"Main.lean","name":"Chapter3.threshold_entropy"}],"representation":"非空B下证明扩展对数单调，从覆盖数界得到熵界，允许无穷。","dependencies":["CH03-D07","CH03-P19-02"]},
    {"id":"CH03-P20-01","status":"incomplete","declarations":[],"representation":"未完成：在固定阶跃U中，对每个有限正τ构造二点B并计算输入、输出覆盖数1与2。","dependencies":[]},
    {"id":"CH03-P21-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.small_domain"}],"representation":"精确直径<τσ≤τN条件下，双向证明半径阈值与整体输出零距等价。","dependencies":["CH03-D04","CH03-D05","CH03-D06","CH03-P18-01"]},
    {"id":"CH03-P21-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.zero_cover_one"},{"file":"Main.lean","name":"Chapter3.small_domain_cover"}],"representation":"非空像域以一个内部中心覆盖；非空覆盖数下界给出恰为1。","dependencies":["CH03-D07","CH03-P21-01"]},
    {"id":"CH03-P22-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.finite_cover"},{"file":"Main.lean","name":"Chapter3.finite_entropy"},{"file":"Main.lean","name":"Chapter3.delta_defined_finite"},{"file":"Main.lean","name":"Chapter3.finite_delta"}],"representation":"非空有限输入及实际像，任意两端非空子族的覆盖数有限，熵及其差表示为实数。","dependencies":["CH03-D07","CH03-D08"]},
    {"id":"CH03-P23-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_entropy"}],"representation":"常值分量像覆盖数1、熵0，存在合法熵差且等于输入熵，输入允许无穷。","dependencies":["CH03-D01","CH03-D07","CH03-D08","CH03-P21-02"]},
    {"id":"CH03-P23-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.ident_cover"},{"file":"Main.lean","name":"Chapter3.push_net"},{"file":"Main.lean","name":"Chapter3.pull_net"}],"representation":"恒等分量通过前向映中心与反向选代表元证明内部覆盖数和熵相等。","dependencies":["CH03-D01","CH03-D07","CH03-P01-03"]},
    {"id":"CH03-P23-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.ident_delta"}],"representation":"显式要求熵差良定；由覆盖数相等推出有限并证明熵差0。","dependencies":["CH03-D08","CH03-P23-02"]},
    {"id":"CH03-P24-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.push_net"},{"file":"Main.lean","name":"Chapter3.lip_cover"}],"representation":"有限正L将ε/L内部中心映为ε输出内部中心，基数不增。","dependencies":["CH03-D07"]},
    {"id":"CH03-P24-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.lip_delta"}],"representation":"输入全有界给两端有限实熵及良定熵差，再由覆盖数界证明原文下界。","dependencies":["CH03-D07","CH03-D08","CH03-P24-01","CH03-P19-03"]},
    {"id":"CH03-P25-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.pull_net"},{"file":"Main.lean","name":"Chapter3.colip_cover"}],"representation":"正有限co-Lip单条目将内部输出中心的代表元拉回为ε/K输入覆盖，中心数不增。","dependencies":["CH03-D07"]},
    {"id":"CH03-P25-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.colip_delta"}],"representation":"全有界输入保证熵差良定；允许输出无穷，用扩展实数减法单调性证明原文上界。","dependencies":["CH03-D07","CH03-D08","CH03-P25-01","CH03-P19-03"]},
    {"id":"CH03-P26-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Affine.d"},{"file":"Main.lean","name":"Chapter3.Affine.f"},{"file":"Main.lean","name":"Chapter3.Affine.U"},{"file":"Main.lean","name":"Chapter3.Affine.valid"},{"file":"Main.lean","name":"Chapter3.Affine.domain"},{"file":"Main.lean","name":"Chapter3.Affine.first_fiber"},{"file":"Main.lean","name":"Chapter3.Affine.first_const"}],"representation":"绝对值读数伪度量及2x-1算子合法；U={0,1}，第一纤维为U且分量常值。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P26-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.Affine.second_fiber"},{"file":"Main.lean","name":"Chapter3.Affine.second_active"}],"representation":"精确保留U={0,1}，自复合指定纤维={0}，分量有效。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P26-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.point_constant_square"}],"representation":"U上点值常算子的自复合仍点值常；域合法等价于U为空或再次像不是吸收元。","dependencies":[]},
    {"id":"CH03-P27-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.colip_radius_gap"}],"representation":"正co-Lip通道和点态零化判据排除(0,rN)内输入距离；K可无穷。","dependencies":["CH03-D04","CH03-P14-02"]},
    {"id":"CH03-P27-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.colip_uniform_gap"}],"representation":"全部输入点对要么零距要么达到统一半径；无需额外假设K有限。","dependencies":["CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P28-01","status":"incomplete","declarations":[],"representation":"未完成：恒等及平移算子在指定四点U上的完整纤维分划及结构验证。","dependencies":[]},
    {"id":"CH03-P28-02","status":"incomplete","declarations":[],"representation":"未完成：精确3/2半径下两端内部覆盖数及熵差的上下界计算。","dependencies":[]},
    {"id":"CH03-P29-01","status":"incomplete","declarations":[],"representation":"未完成：取整算子在[0,1/2]上的直径、统一半径及阈值类型。","dependencies":[]},
    {"id":"CH03-P29-02","status":"incomplete","declarations":[],"representation":"未完成：取整算子在[9/10,11/10]上的直径、统一半径及阈值类型。","dependencies":[]},
    {"id":"CH03-P29-03","status":"incomplete","declarations":[],"representation":"未完成：取整算子在{0,2}上的直径、统一半径及阈值类型。","dependencies":[]},
    {"id":"CH03-P29-04","status":"incomplete","declarations":[],"representation":"未完成：取整算子在[0,2]上的直径、统一半径及阈值类型。","dependencies":[]},
    {"id":"CH03-P29-05","status":"incomplete","declarations":[],"representation":"未完成：由取整算子的合法局部域反例否定无直径条件时的整体零化蕴含。","dependencies":[]},
    {"id":"CH03-P30-01","status":"incomplete","declarations":[],"representation":"未完成：指定四点集所有有限正精度的内部覆盖数分段、端点及3/2中心非法性。","dependencies":[]},
    {"id":"CH03-P30-02","status":"incomplete","declarations":[],"representation":"未完成：两指定算子的像集、各精度覆盖数及映射熵差。","dependencies":[]},
    {"id":"CH03-P30-03","status":"incomplete","declarations":[],"representation":"未完成：两指定算子的最优标量Lip常数及必要下界。","dependencies":[]},
    {"id":"CH03-P30-04","status":"incomplete","declarations":[],"representation":"未完成：在ε=7/4代入一般覆盖数上界并与真实覆盖数逐项比较。","dependencies":[]}
  ]
}
```