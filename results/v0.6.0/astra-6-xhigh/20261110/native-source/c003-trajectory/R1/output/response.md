FULL

上一版尚有 10 项未完成。本轮已补齐，并补充定义域合法性、纤维及有限链域递推证明；更新后的 92 项均为 `complete`。

项目在指定 Lean 4.29.1 和 mathlib 提交下编译通过。公理审计覆盖 340 个自建常量及 119 个冻结背景常量（含生成声明），依赖仅有 `propext`、`Classical.choice`、`Quot.sound`。原始规格和冻结背景逐字节未变。语义对应见完整对齐表；尚未经独立人工复核。

数学来源：Zhe Li（Glen Li / glenzli），[ORCID](https://orcid.org/0009-0006-6536-3453)，《[The Operator Evolution Theory](https://glenzli.com/books/oet/)》，[原仓库](https://gitlab.com/glenzli/oet-public)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下是基于原文的新 Lean 形式化。

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

[[lean_lib]]
name = "Chapter3"

[[lean_lib]]
name = "formal_oet"
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=Main.lean
import Chapter3.Core
import Chapter3.Radius
import Chapter3.Cover
import Chapter3.Examples
import Chapter3.MoreExamples
import Chapter3.Correspondence
import Chapter3.Completion
import Chapter3.FourPoint
```

```lean filename=Chapter3/Core.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/- Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
   Volume I, Chapter 3. https://glenzli.com/books/oet/ . CC BY 4.0.
   This file is a new Lean formalization, not the author's implementation. -/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def constComp (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}
def idComp (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComp d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}
def activeComp (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (constComp d f U ∪ idComp d f U)ᶜ

theorem component_partition (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    constComp d f U ∪ idComp d f U ∪ activeComp d f U = univ ∧
    Disjoint (constComp d f U) (idComp d f U) ∧
    Disjoint (constComp d f U) (activeComp d f U) ∧
    Disjoint (idComp d f U) (activeComp d f U) := by
  classical
  constructor
  · exact Set.union_compl_self _
  · refine ⟨?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun _ hc hi => hi.1 hc)
    · exact Set.disjoint_left.mpr (fun _ hc ha => ha (Or.inl hc))
    · exact Set.disjoint_left.mpr (fun _ hi ha => ha (Or.inr hi))

theorem zero_left {d : X → X → ENNReal} (h : ExtendedPseudoMetric X bot d)
    {a b : X} (hab : d a b = 0) (c : X) : d a c = d b c := by
  apply le_antisymm
  · simpa [hab] using h.triangle a b c
  · simpa [h.symm b a, hab] using h.triangle b a c

theorem zero_trans {d : X → X → ENNReal} (h : ExtendedPseudoMetric X bot d)
    {a b c : X} (hab : d a b = 0) (hbc : d b c = 0) : d a c = 0 := by
  rw [zero_left h hab, hbc]

theorem id_distance (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ idComp d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) = d i x y := by
  rw [zero_left (hd i) (hi.2 x hx), (hd i).symm x,
    zero_left (hd i) (hi.2 y hy), (hd i).symm y]

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ constComp d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ ∑ k : I, 0 * d k x y := by
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {i k : I} {K : I → I → ENNReal}
    (hi : i ∈ constComp d f U) (hK : IsCoLipMatrix d f U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hp⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hp

theorem outer_const (d : I → X → X → ENNReal)
    {f g : Operator X bot} {U : Set X} {i : I}
    (hi : i ∈ constComp d g (f.func '' U)) : i ∈ constComp d (g * f) U := by
  intro x hx y hy
  exact hi _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem compose_id (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f g : Operator X bot} {U : Set X} {i : I}
    (hf : i ∈ idComp d f U) (hg : i ∈ idComp d g (f.func '' U)) :
    i ∈ idComp d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    have he := id_distance d hd hg (show f.func x ∈ f.func '' U from ⟨x,hx,rfl⟩)
      (show f.func y ∈ f.func '' U from ⟨y,hy,rfl⟩)
    exact he.symm.trans (hc x hx y hy)
  · intro x hx
    exact zero_trans (hd i) (hg.2 _ ⟨x,hx,rfl⟩) (hf.2 x hx)

theorem compose_active (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    activeComp d (g * f) U ⊆ activeComp d f U ∪ activeComp d g (f.func '' U) := by
  intro i hi
  by_contra hn
  have hf : i ∈ constComp d f U ∨ i ∈ idComp d f U := by
    simpa only [activeComp, mem_compl_iff, not_not] using (show i ∉ activeComp d f U from fun h => hn (Or.inl h))
  have hg : i ∈ constComp d g (f.func '' U) ∨ i ∈ idComp d g (f.func '' U) := by
    simpa only [activeComp, mem_compl_iff, not_not] using (show i ∉ activeComp d g (f.func '' U) from fun h => hn (Or.inr h))
  rcases hg with hg | hg
  · exact hi (Or.inl (outer_const d hg))
  · rcases hf with hf | hf
    · apply hi; left; intro x hx y hy
      exact (id_distance d hd hg ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩).trans (hf x hx y hy)
    · exact hi (Or.inr (compose_id d hd hf hg))

def run : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => run fs * f
def stageActive (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => activeComp d f U ∪ stageActive d fs (f.func '' U)

theorem run_active (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (fs : List (Operator X bot)) (U : Set X) :
    activeComp d (run fs) U ⊆ stageActive d fs U := by
  induction fs generalizing U with
  | nil =>
      intro i hi
      apply hi
      by_cases hc : i ∈ constComp d (run (bot := bot) []) U
      · exact Or.inl hc
      · exact Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩
  | cons f fs ih =>
      exact (compose_active d hd f (run fs) U).trans (Set.union_subset_union_right _ (ih _))

theorem run_domains (f : Operator X bot) (fs : List (Operator X bot)) (U : Set X)
    (hU : U ⊆ dom (run (f :: fs))) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom (run fs) := by
  constructor
  · intro x hx he
    have h := hU hx
    change (run fs).func (f.func x) ≠ bot at h
    exact h (by rw [he, (run fs).preserves_bot])
  · rintro _ ⟨x,hx,rfl⟩; exact hU hx

theorem const_diagonal [Fintype I] (d : I → X → X → ENNReal)
    {f g : Operator X bot} {U : Set X} {j : I} {L : I → I → ENNReal}
    (hf : j ∈ constComp d f U) (hL : IsLipMatrix d g (f.func '' U) L)
    (hz : ∀ k, k ≠ j → L k j = 0) : j ∈ constComp d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hz
    _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  simpa [hf x hx y hy] using h

def fiber (d : I → X → X → ENNReal) (f : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ ∀ j ∈ J, d j (f.func x) y = 0}

theorem subfamily_zero (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact le_antisymm (h ▸ le_iSup (fun k : J => d k x y) ⟨j,hj⟩) (zero_le _)
  · intro h
    exact le_antisymm (iSup_le (fun j => le_of_eq (h j j.property))) (zero_le _)

theorem fiber_representation (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    fiber d f J y U = {x ∈ U | subfamily_pseudometric d J (f.func x) y = 0} := by
  ext x; simp [fiber, subfamily_zero]

theorem fiber_target (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (U : Set X) {y z : X} (hyz : ∀ j ∈ J, d j y z = 0) :
    fiber d f J y U = fiber d f J z U := by
  ext x; simp only [fiber, mem_setOf_eq]
  constructor
  · rintro ⟨hx,h⟩; exact ⟨hx, fun j hj => zero_trans (hd j) (h j hj) (hyz j hj)⟩
  · rintro ⟨hx,h⟩
    exact ⟨hx, fun j hj => zero_trans (hd j) (h j hj) ((hd j).symm z y |>.trans (hyz j hj))⟩

theorem fiber_cover (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (J : Set I) (U : Set X) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  constructor
  · rintro y ⟨x,hx,rfl⟩; exact ⟨x,hx,fun j _ => (hd j).dist_self _⟩
  · ext x; simp only [mem_iUnion]
    constructor
    · rintro ⟨y,hy,h⟩; exact h.1
    · intro hx; exact ⟨f.func x, ⟨x,hx,rfl⟩, hx, fun j _ => (hd j).dist_self _⟩

theorem fiber_disjoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (J : Set I)
    (U : Set X) (y z : X) :
    fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U) := by
  by_cases h : ∃ x, x ∈ fiber d f J y U ∧ x ∈ fiber d f J z U
  · obtain ⟨x,hx,hz⟩ := h
    left; apply fiber_target d hd; intro j hj
    exact zero_trans (hd j) ((hd j).symm y _ |>.trans (hx.2 j hj)) (hz.2 j hj)
  · right; rw [Set.disjoint_left]; aesop

theorem fiber_inter (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    fiber d f J y U = ⋂ j ∈ J, fiber d f {j} y U := by
  ext x; simp only [fiber, mem_setOf_eq, mem_iInter, mem_singleton_iff, forall_eq]
  obtain ⟨j,hj⟩ := hJ
  constructor
  · rintro ⟨hx,h⟩ k hk; exact ⟨hx,h k hk⟩
  · intro h; exact ⟨(h j hj).1, fun k hk => (h k hk).2⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    {J K : Set I} (h : J ⊆ K) (y : X) (U : Set X) :
    fiber d f K y U ⊆ fiber d f J y U := fun _ hx => ⟨hx.1, fun j hj => hx.2 j (h hj)⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f {i} y U = {x ∈ U | d i (f.func x) y = 0} := by ext; simp [fiber]

theorem fiber_full (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) : fiber d f univ y U ⊆ fiber d f {i} y U :=
  fiber_antitone d f (Set.subset_univ _) y U

theorem fiber_id (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ idComp d f U) (y : X) :
    fiber d f {i} y U = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]; ext x
  constructor <;> rintro ⟨hx,h⟩ <;> refine ⟨hx, ?_⟩
  · rwa [zero_left (hd i) (hi.2 x hx)] at h
  · rwa [zero_left (hd i) (hi.2 x hx)]

theorem fiber_const (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {J : Set I} (h : J ⊆ constComp d f U) {y : X} (hy : y ∈ f.func '' U) :
    fiber d f J y U = U := by
  obtain ⟨z,hz,rfl⟩ := hy
  ext x; exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun j hj => h hj x hx z hz⟩⟩

theorem fiber_const_empty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ constComp d f U) {y z : X}
    (hz : z ∈ f.func '' U) (hy : 0 < d i y z) : fiber d f {i} y U = ∅ := by
  obtain ⟨a,ha,rfl⟩ := hz
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (ne_of_gt hy) (zero_trans (hd i)
    ((hd i).symm y _ |>.trans (hx.2 i (by simp))) (hi x hx.1 a ha))

def eqRel (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}
def zeroRel (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}
def fiberPreorder (d : I → X → X → ENNReal) (U : Set X) (f g : Operator X bot) : Prop :=
  zeroRel d f U ⊆ zeroRel d g U

theorem zeroRel_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) :
    (x,y) ∈ zeroRel d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRel, fiber, GaugeZeroRelated, mem_setOf_eq, mem_univ, forall_true_left]
  constructor
  · rintro ⟨_,hy,h⟩; exact ⟨hy, fun i => (hd i).symm _ _ |>.trans (h i)⟩
  · rintro ⟨hy,h⟩; exact ⟨hx,hy,fun i => (hd i).symm _ _ |>.trans (h i)⟩

def imagePoint (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, x, x.property, rfl⟩
def Factors (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U) → X, ∀ x : U, T (imagePoint f U x) = g.func x

theorem factor_iff (f g : Operator X bot) (U : Set X) :
    Factors f g U ↔ eqRel f U ⊆ eqRel g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,he⟩
    refine ⟨hx,hy,?_⟩
    rw [← hT ⟨x,hx⟩, ← hT ⟨y,hy⟩]
    congr 1; exact Subtype.ext he
  · intro h
    let pick : (f.func '' U) → X := fun z => Classical.choose z.property
    have hp : ∀ z : f.func '' U, pick z ∈ U ∧ f.func (pick z) = z :=
      fun z => Classical.choose_spec z.property
    refine ⟨fun z => g.func (pick z), ?_⟩
    intro x
    exact (h (show (pick (imagePoint f U x),(x : X)) ∈ eqRel f U from
      ⟨(hp _).1,x.property,(hp _).2⟩)).2.2

theorem factors_both (f g : Operator X bot) (U : Set X) :
    Factors f g U ∧ Factors g f U ↔ eqRel f U = eqRel g U := by
  rw [factor_iff, factor_iff]; exact Set.Subset.antisymm_iff.symm

def imageSetoid (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Setoid (f.func '' U) where
  r a b := GaugeZeroRelated d a b
  iseqv :=
    ⟨fun a i => (hd i).dist_self a,
     fun h i => (hd i).symm _ _ |>.trans (h i),
     fun h h' i => zero_trans (hd i) (h i) (h' i)⟩
abbrev ImageQuotient (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid d hd f U)
def quotientPoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) (x : U) :
    ImageQuotient d hd f U := Quotient.mk _ (imagePoint f U x)
def QuotientFactors (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuotient d hd f U → ImageQuotient d hd g U,
    ∀ x : U, T (quotientPoint d hd f U x) = quotientPoint d hd g U x

theorem quotient_factor_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    QuotientFactors d hd f g U ↔ zeroRel d f U ⊆ zeroRel d g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,h⟩
    refine ⟨hx,hy,?_⟩
    have he : quotientPoint d hd f U ⟨x,hx⟩ = quotientPoint d hd f U ⟨y,hy⟩ :=
      Quotient.sound h
    exact Quotient.exact (show quotientPoint d hd g U ⟨x,hx⟩ = quotientPoint d hd g U ⟨y,hy⟩ by
      rw [← hT, ← hT, he])
  · intro h
    let pick : (f.func '' U) → U := fun z =>
      ⟨Classical.choose z.property, (Classical.choose_spec z.property).1⟩
    have hp : ∀ z : f.func '' U, f.func (pick z) = z :=
      fun z => (Classical.choose_spec z.property).2
    let F : (f.func '' U) → ImageQuotient d hd g U := fun z => quotientPoint d hd g U (pick z)
    have hF : ∀ a b, (imageSetoid d hd f U).r a b → F a = F b := by
      intro a b hab
      apply Quotient.sound
      apply (h (show ((pick a : X), (pick b : X)) ∈ zeroRel d f U from
        ⟨(pick a).property, (pick b).property, by simpa [hp] using hab⟩)).2.2
    refine ⟨Quotient.lift F hF, ?_⟩
    intro x
    apply Quotient.sound
    apply (h (show ((pick (imagePoint f U x) : X),(x : X)) ∈ zeroRel d f U from
      ⟨(pick _).property,x.property,?_⟩)).2.2
    intro i
    rw [hp]; exact (hd i).dist_self _

theorem quotient_factors_both (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U ↔ zeroRel d f U = zeroRel d g U := by
  rw [quotient_factor_iff, quotient_factor_iff]; exact Set.Subset.antisymm_iff.symm

theorem separated_rel (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hs : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b) :
    eqRel f U = zeroRel d f U := by
  ext ⟨x,y⟩; constructor
  · rintro ⟨hx,hy,h⟩; exact ⟨hx,hy,fun i => by rw [h]; exact (hd i).dist_self _⟩
  · rintro ⟨hx,hy,h⟩; exact ⟨hx,hy,hs _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ h⟩

theorem separated_criteria (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (hf : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b)
    (hg : ∀ a ∈ g.func '' U, ∀ b ∈ g.func '' U, GaugeZeroRelated d a b → a = b) :
    (Factors f g U ↔ QuotientFactors d hd f g U) ∧
    (Factors f g U ∧ Factors g f U ↔ QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U) := by
  simp only [factor_iff, quotient_factor_iff, separated_rel d hd f U hf, separated_rel d hd g U hg]
  exact ⟨trivial,trivial⟩

theorem fiber_preorder_refl (d : I → X → X → ENNReal) (U : Set X) (f : Operator X bot) :
    fiberPreorder d U f f := Set.Subset.rfl
theorem fiber_preorder_trans (d : I → X → X → ENNReal) (U : Set X) {f g h : Operator X bot}
    (hfg : fiberPreorder d U f g) (hgh : fiberPreorder d U g h) : fiberPreorder d U f h := hfg.trans hgh

theorem relation_chain {α : Type} (R : ℕ → Set α) (m : ℕ)
    (h : ∀ k < m, R k ⊆ R (k+1)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : R a ⊆ R b := by
  induction b, hab using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ b hab ih => exact (ih (by omega)).trans (h b (by omega))

theorem relation_chain_strict {α : Type} (R : ℕ → Set α) (m : ℕ)
    (h : ∀ k < m, R k ⊆ R (k+1)) {k : ℕ} (hk : k < m) (hs : R k ⊂ R (k+1)) :
    R 0 ⊂ R m ∧ ∃ z, z ∈ R m ∧ z ∉ R 0 := by
  obtain ⟨z,hz,hz'⟩ := Set.exists_of_ssubset hs
  have hm : z ∈ R m := relation_chain R m h (by omega) le_rfl hz
  have h0 : z ∉ R 0 := fun hh => hz' (relation_chain R m h (by omega) (by omega) hh)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨relation_chain R m h (by omega) le_rfl,
    fun he => h0 (he ▸ hm)⟩, z, hm, h0⟩

end Chapter3
```

```lean filename=Chapter3/Radius.lean
import Chapter3.Core

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def GoodRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0
noncomputable def radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) : ENNReal := sSup {r | GoodRadius din dout f U y r}
noncomputable def uniformRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, radius din dout f U y
noncomputable def nullMatrix (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j i : I) : ENNReal := uniformRadius (d i) (d j) f U U

theorem radius_representation (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) : radius din dout f U y =
    sSup {r | 0 < r ∧ r < ⊤ ∧ ball din y r ∩ U ⊆ {x ∈ U | dout (f.func x) (f.func y) = 0}} := by
  unfold radius
  congr 1; ext r
  simp only [GoodRadius, mem_setOf_eq, Set.subset_def, mem_inter_iff, ball]
  aesop

theorem radius_witness {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {y : X} {a : ENNReal} (h : a < radius din dout f U y) :
    ∃ r, GoodRadius din dout f U y r ∧ a < r := lt_sSup_iff.mp h

theorem below_radius {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {x y : X} (hx : x ∈ U) (h : din x y < radius din dout f U y) :
    dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r,hr,har⟩ := radius_witness h
  exact hr.2.2 x hx har

theorem le_radius_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (a : ENNReal) :
    a ≤ radius din dout f U y ↔ ∀ x ∈ U, din x y < a → dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx hxy; exact below_radius hx (hxy.trans_le h)
  · intro h
    apply le_of_forall_lt
    intro b hb
    obtain ⟨r,hbr,hra⟩ := exists_between hb
    exact hbr.trans_le (le_sSup (show GoodRadius din dout f U y r from
      ⟨lt_of_le_of_lt (zero_le b) hbr, hra.trans_le le_top,
        fun x hx hxr => h x hx (hxr.trans hra)⟩))

theorem goodRadius_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) :
    GoodRadius din dout f U y r ↔ 0 < r ∧ r < ⊤ ∧ r ≤ radius din dout f U y := by
  rw [le_radius_iff]; rfl

theorem le_uniform_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) (a : ENNReal) :
    a ≤ uniformRadius din dout f A U ↔
      ∀ y ∈ A, ∀ x ∈ U, din x y < a → dout (f.func x) (f.func y) = 0 := by
  simp only [uniformRadius, le_iInf_iff, le_radius_iff]

theorem uniform_le_point (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) {y : X} (hy : y ∈ A) : uniformRadius din dout f A U ≤ radius din dout f U y :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem constant_radii (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    (∀ y ∈ U, radius din dout f U y = ⊤) ∧ uniformRadius din dout f U U = ⊤ := by
  constructor
  · intro y hy; apply top_unique
    exact (le_radius_iff _ _ _ _ _ _).mpr (fun x hx _ => h x hx y hy)
  · apply top_unique
    exact (le_uniform_iff _ _ _ _ _ _).mpr (fun y hy x hx _ => h x hx y hy)

theorem constant_subfamily_radii (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (i : I) (h : J ⊆ constComp d f U) :
    (∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f U y = ⊤) ∧
    uniformRadius (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  apply constant_radii
  intro x hx y hy
  exact (subfamily_zero d J _ _).mpr (fun j hj => h hj x hx y hy)

theorem id_image_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ idComp d f U) {y : X} (hy : y ∈ U) :
    fiber d f {i} (f.func y) U = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]; ext x
  constructor <;> rintro ⟨hx,h⟩ <;> refine ⟨hx, ?_⟩
  · rwa [id_distance d hd hi hx hy] at h
  · rwa [id_distance d hd hi hx hy]

theorem id_radius_lower (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ idComp d f U) {y : X} (hy : y ∈ U)
    {r : ENNReal} (hr : 0 < r) (hfin : r < ⊤)
    (hball : ball (d i) y r ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r ≤ radius (d i) (d i) f U y ∧ 0 < r := by
  refine ⟨(le_radius_iff _ _ _ _ _ _).mpr ?_,hr⟩
  intro x hx hxy
  rw [id_distance d hd hi hx hy]
  exact (hball ⟨hxy,hx⟩).2

theorem radius_subfamily (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (U : Set X) (y : X) (J : Set I) :
    radius din (subfamily_pseudometric d J) f U y = ⨅ j ∈ J, radius din (d j) f U y := by
  apply le_antisymm
  · apply le_iInf; intro j; apply le_iInf; intro hj
    apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    exact (subfamily_zero d J _ _).mp (below_radius hx hxy) j hj
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    apply (subfamily_zero d J _ _).mpr
    intro j hj
    exact below_radius hx (hxy.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_subfamily (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (A U : Set X) (J : Set I) :
    uniformRadius din (subfamily_pseudometric d J) f A U =
      ⨅ j ∈ J, uniformRadius din (d j) f A U := by
  have he : ∀ a, a ≤ uniformRadius din (subfamily_pseudometric d J) f A U ↔
      a ≤ ⨅ j ∈ J, uniformRadius din (d j) f A U := by
    intro a
    simp only [le_iInf_iff, le_uniform_iff, subfamily_zero]
    constructor
    · intro h j hj y hy x hx hxy; exact h y hy x hx hxy j hj
    · intro h y hy x hx hxy j hj; exact h j hj y hy x hx hxy
  exact le_antisymm ((he _).mp le_rfl) ((he _).mpr le_rfl)

theorem uniform_subfamily_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (A U : Set X) {J K : Set I} (h : J ⊆ K) :
    uniformRadius din (subfamily_pseudometric d K) f A U ≤
      uniformRadius din (subfamily_pseudometric d J) f A U := by
  rw [uniform_subfamily, uniform_subfamily]
  exact iInf_mono' (fun j => ⟨j, iInf_mono' (fun hj => ⟨h hj,le_rfl⟩)⟩)

theorem fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {U : Set X}
    {j : I} {y z : X} (h : z ∈ fiber d f {j} (f.func y) U) : d j (f.func y) (f.func z) = 0 :=
  (hd j).symm _ _ |>.trans (h.2 j (by simp))

theorem radius_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {U : Set X}
    {i j : I} {y z : X} (hz : z ∈ U)
    (h : d i y z < radius (d i) (d j) f U y) : d j (f.func y) (f.func z) = 0 := by
  rw [(hd j).symm]
  exact below_radius (din := d i) hz (by rwa [(hd i).symm])

theorem composition_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (j : I) {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hfx : f.func x ∈ U) (hfy : f.func y ∈ U)
    (h : f.func y ∈ fiber d g {j} (g.func (f.func x)) U) :
    d j ((g * f).func x) ((g * f).func y) = 0 :=
  fiber_truncation d hd (f := g) (y := f.func x) (z := f.func y) h

theorem uniform_zero {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : din x y < uniformRadius din dout f U U) : dout (f.func x) (f.func y) = 0 :=
  below_radius hx (h.trans_le (uniform_le_point _ _ _ _ _ hy))

theorem output_separation {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : 0 < dout (f.func x) (f.func y)) : uniformRadius din dout f U U ≤ din x y := by
  by_contra hn
  exact (ne_of_gt h) (uniform_zero hx hy (lt_of_not_ge hn))

theorem separation_witness {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {a : ENNReal} (ha : uniformRadius din dout f U U < a) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ din x y < a ∧ ε ≤ dout (f.func x) (f.func y) := by
  classical
  have hn : ¬ ∀ y ∈ U, ∀ x ∈ U, din x y < a → dout (f.func x) (f.func y) = 0 :=
    fun h => (not_le_of_gt ha) ((le_uniform_iff _ _ _ _ _ _).mpr h)
  push_neg at hn
  obtain ⟨y,hy,x,hx,hxy,hout⟩ := hn
  exact ⟨x,hx,y,hy,min 1 (dout (f.func x) (f.func y)),
    lt_min zero_lt_one (pos_iff_ne_zero.mpr hout),
    (min_le_left _ _).trans_lt ENNReal.one_lt_top,hxy,min_le_right _ _⟩

theorem radius_domain_mono (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) (y : X) : radius din dout f A y ≤ radius din dout f B y := by
  exact (le_radius_iff _ _ _ _ _ _).mpr (fun x hx hxy => below_radius (h hx) hxy)

theorem uniform_domain_mono (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) : uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  exact (le_uniform_iff _ _ _ _ _ _).mpr (fun y hy x hx hxy => uniform_zero (h hx) (h hy) hxy)

theorem compose_radius_zero (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (h : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U,
      dmid a b = 0 → dout (g.func a) (g.func b) = 0) :
    uniformRadius din dmid f U U ≤ uniformRadius din dout (g * f) U U := by
  apply (le_uniform_iff _ _ _ _ _ _).mpr
  intro y hy x hx hxy
  exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (uniform_zero hx hy hxy)

theorem compose_radius_lip (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) {L : ENNReal} (hL : L ≠ 0) (hLt : L ≠ ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dmid (f.func x) (f.func y) ≤ L * din x y) :
    uniformRadius dmid dout g (f.func '' U) (f.func '' U) / L ≤
      uniformRadius din dout (g * f) U U := by
  apply (le_uniform_iff _ _ _ _ _ _).mpr
  intro y hy x hx hxy
  apply uniform_zero (show f.func x ∈ f.func '' U from ⟨x,hx,rfl⟩)
    (show f.func y ∈ f.func '' U from ⟨y,hy,rfl⟩)
  exact (h x hx y hy).trans_lt (by
    simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl hLt)).mp hxy)

noncomputable def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y
theorem le_diameter (d : X → X → ENNReal) {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
theorem diameter_mono (d : X → X → ENNReal) {A B : Set X} (h : A ⊆ B) :
    diameter d A ≤ diameter d B := by
  apply iSup_le; intro x; apply iSup_le; intro hx
  apply iSup_le; intro y; apply iSup_le; intro hy
  exact le_diameter d (h hx) (h hy)

structure InputScale (X I : Type) where
  value : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → value i A ≤ value i B
noncomputable def diameterScale (d : I → X → X → ENNReal) : InputScale X I :=
  ⟨fun i A => diameter (d i) A, fun i _ _ h => diameter_mono (d i) h⟩
noncomputable def thresholdType (s n τs τn : ENNReal) : Bool × Bool :=
  (decide (s < τs), decide (τn ≤ n))
noncomputable def channelType (σ : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (τs τn : ENNReal) (i j : I) : Bool × Bool :=
  thresholdType (σ.value i A) (nullMatrix d f A j i) τs τn

theorem threshold_cases (s n τs τn : ENNReal) :
    (thresholdType s n τs τn = (true,true) ↔ s < τs ∧ τn ≤ n) ∧
    (thresholdType s n τs τn = (true,false) ↔ s < τs ∧ n < τn) ∧
    (thresholdType s n τs τn = (false,true) ↔ τs ≤ s ∧ τn ≤ n) ∧
    (thresholdType s n τs τn = (false,false) ↔ τs ≤ s ∧ n < τn) := by
  simp [thresholdType, not_le, not_lt]

theorem threshold_scale_mono {s τ τ' : ENNReal} (h : τ ≤ τ') (hs : s < τ) : s < τ' := hs.trans_le h
theorem threshold_null_antitone {n τ τ' : ENNReal} (h : τ ≤ τ') (hn : τ' ≤ n) : τ ≤ n := h.trans hn
theorem scale_domain_mono (σ : InputScale X I) (i : I)
    (A B : {A : Set X // A.Nonempty}) (h : B.val ⊆ A.val) (τ : ENNReal) :
    σ.value i B ≤ σ.value i A ∧ (σ.value i A < τ → σ.value i B < τ) :=
  ⟨σ.mono i B A h, fun ht => (σ.mono i B A h).trans_lt ht⟩

theorem threshold_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) {τ : ENNReal} (h : τ ≤ nullMatrix d f A j i) {y : X} (hy : y ∈ A) :
    ball (d i) y τ ∩ A ⊆ fiber d f {j} (f.func y) A := by
  intro x hx; refine ⟨hx.2, ?_⟩
  intro k hk; have : k = j := hk; subst k
  exact uniform_zero hx.2 hy (hx.1.trans_le h)

theorem small_domain_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {τs τn : ENNReal} (hs : diameter din A < τs) (hst : τs ≤ τn) :
    τn ≤ uniformRadius din dout f A A ↔ ∀ x ∈ A, ∀ y ∈ A, dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro hn x hx y hy
    exact uniform_zero hx hy ((le_diameter din hx hy).trans_lt (hs.trans_le (hst.trans hn)))
  · intro h; rw [(constant_radii din dout f A h).2]; exact le_top

theorem colip_point_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius (d i) (d j) f U y) := by
  rintro ⟨hpos,hlt⟩
  exact (ne_of_gt hpos) (positive_colip_entry_reflects_zero d f U K i j hK hp x hx y hy
    (below_radius hx hlt))

theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ nullMatrix d f U j i ≤ d i x y := by
  by_cases hz : d i x y = 0
  · exact Or.inl hz
  · right; by_contra hn
    exact colip_point_gap d hK hp hx hy ⟨pos_iff_ne_zero.mpr hz,
      (lt_of_not_ge hn).trans_le (uniform_le_point _ _ _ _ _ hy)⟩

end Chapter3
```

```lean filename=Chapter3/Cover.lean
import Chapter3.Radius
import Mathlib.Data.EReal.Operations

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def TotallyBoundedAt (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

theorem covering_interface (d : X → X → ENNReal) (r : ENNReal) (U : Set X) :
    (covering_number d r U = ⊤ ↔ ¬ ∃ S, InternalEpsilonNet d r U S) ∧
    (∀ S, InternalEpsilonNet d r U S →
      ∃ T, InternalEpsilonNet d r U T ∧ covering_number d r U = (T.card : ENNReal) ∧
        ∀ V, InternalEpsilonNet d r U V → T.card ≤ V.card) :=
  ⟨covering_number_eq_top_iff d r U, fun S hS => covering_number_attained d r U ⟨S,hS⟩⟩

theorem cover_push (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (ri ro : ENNReal) (h : ∀ x ∈ U, ∀ y ∈ U, din x y < ri → dout (f x) (f y) < ro) :
    covering_number dout ro (f '' U) ≤ covering_number din ri U := by
  classical
  apply le_iInf; intro S; apply le_iInf; intro hS
  have hT : InternalEpsilonNet dout ro (f '' U) (S.image f) := by
    constructor
    · intro z hz; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨x,hS.1 hx,rfl⟩
    · rintro z ⟨x,hx,rfl⟩
      obtain ⟨c,hc,hd⟩ := hS.2 x hx
      exact ⟨f c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,h x hx c (hS.1 hc) hd⟩
  exact (iInf_le_of_le (S.image f) (iInf_le_of_le hT le_rfl)).trans
    (by exact_mod_cast Finset.card_image_le)

theorem cover_pull (din dout : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (ri ro : ENNReal) (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) < ro → din x y < ri) :
    covering_number din ri U ≤ covering_number dout ro (f.func '' U) := by
  classical
  apply le_iInf; intro T; apply le_iInf; intro hT
  let pick : X → X := fun t => if ht : t ∈ f.func '' U then Classical.choose ht else bot
  have hp : ∀ t ∈ T, pick t ∈ U ∧ f.func (pick t) = t := by
    intro t ht
    have him := hT.1 ht
    dsimp only [pick]
    rw [dif_pos him]
    exact Classical.choose_spec him
  have hS : InternalEpsilonNet din ri U (T.image pick) := by
    constructor
    · intro z hz; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz; exact (hp t ht).1
    · intro x hx
      obtain ⟨t,ht,hdt⟩ := hT.2 (f.func x) ⟨x,hx,rfl⟩
      refine ⟨pick t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,h x hx _ (hp t ht).1 ?_⟩
      rwa [(hp t ht).2]
  exact (iInf_le_of_le (T.image pick) (iInf_le_of_le hS le_rfl)).trans
    (by exact_mod_cast Finset.card_image_le)

theorem log2_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  have hb : b ≠ 0 := fun hb => ha (le_antisymm (hb ▸ hab) (zero_le _))
  by_cases hbt : b = ⊤
  · simp [log2_ereal,hb,hbt]
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt hab
  simp only [log2_ereal,if_neg ha,if_neg hb,if_neg hat,if_neg hbt]
  exact EReal.coe_le_coe_iff.mpr (Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha hat) (ENNReal.toReal_mono hbt hab))

theorem cover_zero_class (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    {ε : ENNReal} (hε : 0 < ε) (h : ∀ x ∈ U, ∀ y ∈ U, d x y = 0) :
    covering_number d ε U = 1 := by
  classical
  apply le_antisymm _ (one_le_covering_number_of_nonempty d ε U hU)
  obtain ⟨c,hc⟩ := hU
  have hn : InternalEpsilonNet d ε U {c} := by
    constructor
    · simpa
    · intro x hx; exact ⟨c,by simp,by rw [h x hx c hc]; exact hε⟩
  exact iInf_le_of_le {c} (iInf_le_of_le hn (by simp))

theorem threshold_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (hBA : B ⊆ A) {τ ε : ENNReal}
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    covering_number dout ε (f.func '' B) ≤ covering_number din τ B := by
  apply cover_push
  intro x hx y hy hxy
  rw [uniform_zero (hBA hx) (hBA hy) (hxy.trans_le hτ)]
  exact hε

theorem threshold_entropy (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (hBA : B ⊆ A) {τ ε : ENNReal}
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    metric_entropy dout ε (f.func '' B) ≤ metric_entropy din τ B :=
  log2_mono (threshold_cover din dout f hBA hτ hε)

theorem constant_cover (d : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε)
    (h : ∀ x ∈ U, ∀ y ∈ U, d (f.func x) (f.func y) = 0) :
    covering_number d ε (f.func '' U) = 1 := by
  apply cover_zero_class d _ (hU.image _) hε
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; exact h x hx y hy

def EntropyDefined (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (ε : ENNReal) : Prop :=
  covering_number din ε U < ⊤ ∨ covering_number dout ε (f.func '' U) < ⊤
noncomputable def entropyDifference (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (ε : ENNReal) (_ : EntropyDefined din dout f U ε) : EReal :=
  metric_entropy din ε U - metric_entropy dout ε (f.func '' U)

theorem entropy_finite (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    (ε : ENNReal) (hf : covering_number d ε U < ⊤) :
    metric_entropy d ε U = (Real.logb 2 (covering_number d ε U).toReal : EReal) := by
  have hz := ne_of_gt (zero_lt_one.trans_le (one_le_covering_number_of_nonempty d ε U hU))
  simp [metric_entropy,log2_ereal,hz,ne_of_lt hf]

theorem entropy_top (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (h : covering_number d ε U = ⊤) : metric_entropy d ε U = ⊤ := by
  simp [metric_entropy,log2_ereal,h]

theorem entropy_difference_infinite (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal) (hD : EntropyDefined din dout f U ε) :
    (covering_number din ε U = ⊤ → entropyDifference din dout f U ε hD = ⊤) ∧
    (covering_number dout ε (f.func '' U) = ⊤ → entropyDifference din dout f U ε hD = ⊥) := by
  constructor
  · intro hin
    have hf : covering_number dout ε (f.func '' U) < ⊤ := hD.resolve_left (by simp [hin])
    simp [entropyDifference,entropy_top din U ε hin,entropy_finite dout _ (hU.image _) ε hf]
  · intro hout
    have hf : covering_number din ε U < ⊤ := hD.resolve_right (by simp [hout])
    simp [entropyDifference,entropy_top dout _ ε hout,entropy_finite din U hU ε hf]

theorem finite_cover (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hU : U.Finite) {ε : ENNReal} (hε : 0 < ε) : covering_number d ε U < ⊤ := by
  classical
  have hnet : InternalEpsilonNet d ε U hU.toFinset := by
    constructor
    · simp
    · intro x hx; exact ⟨x,by simpa,by rw [hself]; exact hε⟩
  exact lt_of_le_of_lt (iInf_le_of_le hU.toFinset (iInf_le_of_le hnet le_rfl))
    (ENNReal.natCast_lt_top _)

theorem finite_entropy_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (hfin : U.Finite) (J K : Set I)
    {ε : ENNReal} (hε : 0 < ε) :
    (1 ≤ covering_number (subfamily_pseudometric d J) ε U ∧
      covering_number (subfamily_pseudometric d J) ε U < ⊤) ∧
    (1 ≤ covering_number (subfamily_pseudometric d K) ε (f.func '' U) ∧
      covering_number (subfamily_pseudometric d K) ε (f.func '' U) < ⊤) ∧
    ∃ hD : EntropyDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε,
      ∃ a b : ℝ, metric_entropy (subfamily_pseudometric d J) ε U = a ∧
        metric_entropy (subfamily_pseudometric d K) ε (f.func '' U) = b ∧
        entropyDifference (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε hD = (a-b : ℝ) := by
  have hs : ∀ L x, subfamily_pseudometric d L x x = 0 :=
    fun L x => (subfamily_zero d L x x).mpr (fun i _ => (hd i).dist_self x)
  have hi := finite_cover _ (hs J) U hfin hε
  have ho := finite_cover _ (hs K) _ (hfin.image f.func) hε
  refine ⟨⟨one_le_covering_number_of_nonempty _ _ _ hU,hi⟩,
    ⟨one_le_covering_number_of_nonempty _ _ _ (hU.image _),ho⟩,Or.inl hi,_,_,
    entropy_finite _ _ hU ε hi,entropy_finite _ _ (hU.image _) ε ho,?_⟩
  simp [entropyDifference,entropy_finite _ _ hU ε hi,entropy_finite _ _ (hU.image _) ε ho]

theorem const_entropy (d : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε)
    (h : ∀ x ∈ U, ∀ y ∈ U, d (f.func x) (f.func y) = 0) :
    covering_number d ε (f.func '' U) = 1 ∧ metric_entropy d ε (f.func '' U) = 0 ∧
    ∃ hD : EntropyDefined d d f U ε, entropyDifference d d f U ε hD = metric_entropy d ε U := by
  have hc := constant_cover d f U hU hε h
  have he : metric_entropy d ε (f.func '' U) = 0 := by simp [metric_entropy,log2_ereal,hc]
  refine ⟨hc,he,Or.inr (hc ▸ ENNReal.one_lt_top),?_⟩
  simp [entropyDifference,he]

theorem isometric_cover (d : X → X → ENNReal) (f : Operator X bot) (U : Set X) (ε : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, d (f.func x) (f.func y) = d x y) :
    covering_number d ε (f.func '' U) = covering_number d ε U := by
  apply le_antisymm
  · exact cover_push d d f.func U ε ε (fun x hx y hy ht => by rwa [h x hx y hy])
  · exact cover_pull d d f U ε ε (fun x hx y hy ht => by rwa [h x hx y hy] at ht)

theorem id_entropy (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (ε : ENNReal) {j : I} (hj : j ∈ idComp d f U) :
    covering_number (d j) ε (f.func '' U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (f.func '' U) = metric_entropy (d j) ε U := by
  have hc := isometric_cover (d j) f U ε (fun _ hx _ hy => id_distance d hd hj hx hy)
  exact ⟨hc,congrArg log2_ereal hc⟩

theorem id_entropy_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (ε : ENNReal) {j : I} (hj : j ∈ idComp d f U)
    (hD : EntropyDefined (d j) (d j) f U ε) : entropyDifference (d j) (d j) f U ε hD = 0 := by
  have hh := id_entropy d hd f U ε hj
  have hf : covering_number (d j) ε U < ⊤ := by
    rcases hD with h | h
    · exact h
    · rwa [hh.1] at h
  simp [entropyDifference,hh.2,entropy_finite (d j) U hU ε hf,← EReal.coe_sub]

theorem scalar_factor_lip (d : X → X → ENNReal) (f g : Operator X bot) (U : Set X)
    (T : (f.func '' U) → X) (hT : ∀ x : U, T (imagePoint f U x) = g.func x)
    {K L : ENNReal} (hK : K ≠ 0) (hKt : K ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (f.func x) (f.func y))
    (hli : ∀ x ∈ U, ∀ y ∈ U, d (g.func x) (g.func y) ≤ L * d x y) :
    ∀ a b : f.func '' U, d (T a) (T b) ≤ (L/K) * d a b := by
  intro ⟨a,ha⟩ ⟨b,hb⟩
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  change d (T (imagePoint f U ⟨x,hx⟩)) (T (imagePoint f U ⟨y,hy⟩)) ≤ _
  rw [hT,hT]
  calc
    _ ≤ L * d x y := hli x hx y hy
    _ ≤ L * (d (f.func x) (f.func y) / K) := by
      apply mul_le_mul_left'
      exact (ENNReal.le_div_iff_mul_le (Or.inl hK) (Or.inl hKt)).mpr (by simpa [mul_comm] using hco x hx y hy)
    _ = _ := by simp [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

theorem lip_cover (din dout : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (ε : ENNReal) {L : ENNReal} (hL : L ≠ 0) (hLt : L ≠ ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    covering_number dout ε (f.func '' U) ≤ covering_number din (ε/L) U := by
  apply cover_push
  intro x hx y hy hxy
  apply (h x hx y hy).trans_lt
  simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl hLt)).mp hxy

theorem colip_cover [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (ε : ENNReal) {K : I → I → ENNReal} (hK : IsCoLipMatrix d f U K)
    {i j : I} (hp : K i j ≠ 0) (ht : K i j ≠ ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (f.func '' U) := by
  apply cover_pull
  intro x hx y hy hxy
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl ht)).mpr
  rw [mul_comm]
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans_lt
    ((hK.2.2 x hx y hy j).trans_lt hxy)

theorem lip_entropy_bound (din dout : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hTB : TotallyBoundedAt din U) {ε L : ENNReal}
    (he : 0 < ε) (het : ε < ⊤) (hL : L ≠ 0) (hLt : L ≠ ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    covering_number dout ε (f.func '' U) < ⊤ ∧
    ∃ hD : EntropyDefined din dout f U ε,
      metric_entropy din ε U - metric_entropy din (ε/L) U ≤ entropyDifference din dout f U ε hD := by
  have hr : 0 < ε/L := ENNReal.div_pos (ne_of_gt he) hLt
  have hrt : ε/L < ⊤ := ENNReal.div_lt_top (ne_of_lt het) hL
  have hc := lip_cover din dout f U ε hL hLt h
  exact ⟨hc.trans_lt (hTB _ hr hrt),Or.inl (hTB ε he het),EReal.sub_le_sub le_rfl (log2_mono hc)⟩

theorem colip_entropy_bound [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) {ε : ENNReal} (he : 0 < ε) (het : ε < ⊤)
    {K : I → I → ENNReal} (hK : IsCoLipMatrix d f U K) {i j : I}
    (hp : K i j ≠ 0) (ht : K i j ≠ ⊤) (hTB : TotallyBoundedAt (d i) U) :
    ∃ hD : EntropyDefined (d i) (d j) f U ε,
      entropyDifference (d i) (d j) f U ε hD ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U :=
  ⟨Or.inl (hTB ε he het),EReal.sub_le_sub le_rfl (log2_mono (colip_cover d f U ε hK hp ht))⟩

end Chapter3
```

```lean filename=Chapter3/Examples.lean
import Chapter3.Cover

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
open scoped Classical

@[simp] theorem compose_apply {X : Type} {bot : X} (f g : Operator X bot) (x : X) :
    (g * f).func x = g.func (f.func x) := rfl
@[simp] theorem one_apply {X : Type} {bot : X} (x : X) :
    (1 : Operator X bot).func x = x := rfl

noncomputable def liftDistance {A : Type} (d : A → A → ENNReal) : Option A → Option A → ENNReal
  | none, none => 0
  | some x, some y => d x y
  | _, _ => ⊤

theorem liftDistance_valid {A : Type} [Nonempty A] (d : A → A → ENNReal)
    (hs : ∀ x, d x x = 0) (hc : ∀ x y, d x y = d y x)
    (ht : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (liftDistance d) := by
  refine ⟨⟨some (Classical.choice inferInstance),by simp⟩,?_,?_,?_,?_⟩
  · intro x; cases x <;> simp [liftDistance,hs]
  · intro x y; cases x <;> cases y <;> simp [liftDistance,hc]
  · intro x y z; cases x <;> cases y <;> cases z <;> simp [liftDistance,ht]
  · intro x hx; cases x <;> simp_all [liftDistance]

noncomputable def discreteRead {A B : Type} (q : A → B) (c : ENNReal) (x y : A) : ENNReal :=
  if q x = q y then 0 else c

theorem discreteRead_valid {A B : Type} [Nonempty A] (q : A → B) (c : ENNReal) :
    ExtendedPseudoMetric (Option A) none (liftDistance (discreteRead q c)) := by
  apply liftDistance_valid
  · intro x; simp [discreteRead]
  · intro x y; simp [discreteRead,eq_comm]
  · intro x y z
    by_cases hxy : q x = q y <;> by_cases hyz : q y = q z <;>
      by_cases hxz : q x = q z <;> simp_all [discreteRead]

def liftOperator {A : Type} (f : A → A) : Operator (Option A) none := ⟨Option.map f,rfl⟩

noncomputable def realGauge (q : ℝ → ℝ) : Option ℝ → Option ℝ → ENNReal :=
  liftDistance (fun x y => ENNReal.ofReal |q x-q y|)
theorem realGauge_valid (q : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (realGauge q) := by
  apply liftDistance_valid
  · intro x; simp
  · intro x y; rw [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

theorem liftOperator_domain (f : ℝ → ℝ) : dom (liftOperator f) = Set.range some := by
  ext x; cases x <;> simp [dom,liftOperator]

def two : Set (Option Bool) := {some false, some true}
noncomputable def twoD : Option Bool → Option Bool → ENNReal := liftDistance (discreteRead id 1)
def swap : Operator (Option Bool) none := liftOperator Bool.not

theorem swap_example :
    ExtendedPseudoMetric (Option Bool) none twoD ∧
    two ⊆ dom swap ∧ swap.func '' two = two ∧
    activeComp (fun _ : Unit => twoD) swap two = univ ∧
    idComp (fun _ : Unit => twoD) swap two = ∅ ∧
    idComp (fun _ : Unit => twoD) (swap * swap) two = univ ∧
    activeComp (fun _ : Unit => twoD) (swap * swap) two = ∅ := by
  refine ⟨discreteRead_valid id 1,?_,?_,?_,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx; · simp [dom,swap,liftOperator]
    have : x = some true := hx; subst x; simp [dom,swap,liftOperator]
  · ext x; simp [two,swap,liftOperator,or_comm,eq_comm]
  all_goals
    ext i
    simp [activeComp,idComp,constComp,two,twoD,swap,liftOperator,
      operator_monoid,operator_compose,Function.comp_def,liftDistance,discreteRead]

def sevenU : Set (Option (Fin 6)) := {some 0,some 1}
def sevenPhi : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some 0 => some 2
    | some 1 => some 3
    | _ => none, rfl⟩
def sevenPsi : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some 2 => some 4
    | some 3 => some 5
    | _ => none, rfl⟩
noncomputable def sevenGauge (i : Bool) : Option (Fin 6) → Option (Fin 6) → ENNReal :=
  if i then liftDistance (discreteRead id 1)
  else liftDistance (discreteRead (fun x : Fin 6 => if x = 3 then 2 else x) 1)

theorem seven_example :
    (∀ i, ExtendedPseudoMetric (Option (Fin 6)) none (sevenGauge i)) ∧
    sevenU ⊆ dom (sevenPsi * sevenPhi) ∧
    false ∈ constComp sevenGauge sevenPhi sevenU ∧
    false ∉ constComp sevenGauge (sevenPsi * sevenPhi) sevenU ∧
    sevenGauge true (some 2) (some 3) = 1 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; cases i <;> apply discreteRead_valid
  · intro x hx; rcases hx with rfl | hx
    · norm_num [dom,operator_monoid,operator_compose,sevenPsi,sevenPhi] <;> decide
    · have : x = some 1 := hx; subst x
      norm_num [dom,operator_monoid,operator_compose,sevenPsi,sevenPhi] <;> decide
  all_goals norm_num [constComp,sevenU,sevenPhi,sevenPsi,sevenGauge,
    operator_monoid,operator_compose,Function.comp_def,liftDistance,discreteRead] <;> decide

noncomputable def infiniteGauge {I : Type} [DecidableEq I] (i k : I) :
    Option Bool → Option Bool → ENNReal :=
  liftDistance (discreteRead id (if k = i then ⊤ else 1))

theorem infinite_radius_example {I : Type} [DecidableEq I] (i j : I) :
    (∀ k, ExtendedPseudoMetric (Option Bool) none (infiniteGauge i k)) ∧
    two ⊆ dom (1 : Operator (Option Bool) none) ∧
    nullMatrix (infiniteGauge i) (1 : Operator (Option Bool) none) two j i = ⊤ ∧
    j ∉ constComp (infiniteGauge i) (1 : Operator (Option Bool) none) two := by
  refine ⟨fun k => discreteRead_valid id _,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · simp [dom,operator_monoid,operator_identity]
    · have : x = some true := hx; subst x; simp [dom,operator_monoid,operator_identity]
  · apply top_unique; apply (le_uniform_iff _ _ _ _ _ _).mpr
    intro y hy x hx hxy
    have he : x = y := by
      rcases hx with rfl | hx <;> rcases hy with rfl | hy <;>
        simp_all [infiniteGauge,liftDistance,discreteRead]
    subst x
    exact (discreteRead_valid id _).dist_self _
  · intro h
    have hh := h (some false) (by simp [two]) (some true) (by simp [two])
    by_cases he : j = i <;>
      simp_all [infiniteGauge,liftDistance,discreteRead,operator_monoid,operator_identity]

def realTwo : Set (Option ℝ) := {some 0,some 1}
def affine : Operator (Option ℝ) none := liftOperator (fun x => 2*x-1)
noncomputable def absGauge : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => realGauge abs

theorem affine_example :
    (∀ i, ExtendedPseudoMetric (Option ℝ) none (absGauge i)) ∧
    realTwo ⊆ dom (affine * affine) ∧
    fiber absGauge affine {()} (affine.func (some 0)) realTwo = realTwo ∧
    () ∈ constComp absGauge affine realTwo ∧
    fiber absGauge (affine * affine) {()} ((affine * affine).func (some 0)) realTwo = {some 0} ∧
    () ∈ activeComp absGauge (affine * affine) realTwo := by
  refine ⟨fun _ => realGauge_valid abs,?_,?_,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · norm_num [dom,operator_monoid,operator_compose,affine,liftOperator] <;> simp
    · have : x = some 1 := hx; subst x
      norm_num [dom,operator_monoid,operator_compose,affine,liftOperator] <;> simp
  · ext x
    simp only [fiber,mem_setOf_eq,Set.mem_singleton_iff,forall_eq]
    constructor
    · exact And.left
    · intro hx; refine ⟨hx,?_⟩
      rcases hx with rfl | hx
      · norm_num [affine,liftOperator,absGauge,realGauge,liftDistance]
      · have : x = some 1 := hx; subst x
        norm_num [affine,liftOperator,absGauge,realGauge,liftDistance]
  · norm_num [constComp,realTwo,affine,liftOperator,absGauge,realGauge,liftDistance]
  · ext x
    simp only [fiber,mem_setOf_eq,Set.mem_singleton_iff,forall_eq]
    constructor
    · rintro ⟨hx,h⟩; rcases hx with rfl | hx
      · rfl
      · have : x = some 1 := hx; subst x
        norm_num [affine,liftOperator,absGauge,realGauge,liftDistance,
          operator_monoid,operator_compose] at h
    · rintro rfl
      norm_num [realTwo,affine,liftOperator,absGauge,realGauge,liftDistance,
        operator_monoid,operator_compose]
  · norm_num [activeComp,idComp,constComp,realTwo,affine,liftOperator,absGauge,realGauge,
      liftDistance,operator_monoid,operator_compose,Function.comp_def]

theorem point_constant_iteration {X : Type} {bot : X} (f : Operator X bot) (U : Set X)
    {c : X} (h : ∀ x ∈ U, f.func x = c) :
    (∀ x ∈ U, (f * f).func x = f.func c) ∧
    (f.func c ≠ bot → U ⊆ dom (f * f)) ∧
    (f.func c = bot → U ∩ dom (f * f) = ∅) := by
  have he : ∀ x ∈ U, (f * f).func x = f.func c := fun x hx => congrArg f.func (h x hx)
  refine ⟨he,?_,?_⟩
  · intro hc x hx; change (f*f).func x ≠ bot; rwa [he x hx]
  · intro hc; apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hd⟩; exact hd ((he x hx).trans hc)

theorem real_diameter_pair (a b : ℝ) :
    diameter (realGauge id) ({some a,some b} : Set (Option ℝ)) = ENNReal.ofReal |a-b| := by
  apply le_antisymm
  · apply iSup_le; intro x; apply iSup_le; intro hx
    apply iSup_le; intro y; apply iSup_le; intro hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy <;>
      simp_all [realGauge,liftDistance,abs_sub_comm]
  · exact le_diameter _ (x := some a) (y := some b) (by simp) (by simp)

theorem scale_counterexample :
    ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ {some 0,some 1} ∧
    diameter (realGauge id) ({some (0 : ℝ)} : Set (Option ℝ)) < (1/2 : ENNReal) ∧
    (1/2 : ENNReal) ≤ diameter (realGauge id) ({some (0 : ℝ),some 1} : Set (Option ℝ)) := by
  have hs := real_diameter_pair 0 0
  have hp := real_diameter_pair 0 1
  norm_num at hs hp
  simp [hs,hp]

end Chapter3
```

```lean filename=Chapter3/MoreExamples.lean
import Chapter3.Examples

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
open scoped Classical

theorem uniform_pair {X : Type} {bot : X} (din dout : X → X → ENNReal)
    (hi : ExtendedPseudoMetric X bot din) (ho : ExtendedPseudoMetric X bot dout)
    (f : Operator X bot) (a b : X) (hab : 0 < dout (f.func a) (f.func b)) :
    uniformRadius din dout f {a,b} {a,b} = din a b := by
  apply le_antisymm (output_separation (by simp) (by simp) hab)
  apply (le_uniform_iff _ _ _ _ _ _).mpr
  intro y hy x hx hxy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact ho.dist_self _
  · have : y = b := hy; subst y; exact (lt_irrefl _ hxy).elim
  · have : x = b := hx; subst x
    rw [hi.symm] at hxy; exact (lt_irrefl _ hxy).elim
  · have hx' : x = b := hx; have hy' : y = b := hy; subst x; subst y
    exact ho.dist_self _

noncomputable def step : Operator (Option ℝ) none := liftOperator (fun x => if x < 0 then 0 else 1)
def stepDomain : Set (Option ℝ) := some '' (Ico (-1 : ℝ) 0 ∪ Ioc 0 1)
theorem step_valid :
    ExtendedPseudoMetric (Option ℝ) none (realGauge id) ∧
    stepDomain.Nonempty ∧ stepDomain ⊆ dom step := by
  refine ⟨realGauge_valid id,⟨some 1,1,by norm_num,rfl⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩; simp [dom,step,liftOperator]

noncomputable def floorOperator : Operator (Option ℝ) none := liftOperator (fun x => (⌊x⌋ : ℤ))
def floorPair : Set (Option ℝ) := {some 0,some 2}

theorem floor_pair :
    floorPair.Nonempty ∧ floorPair ⊆ dom floorOperator ∧
    diameter (realGauge id) floorPair = 2 ∧
    uniformRadius (realGauge id) (realGauge id) floorOperator floorPair floorPair = 2 ∧
    thresholdType (diameter (realGauge id) floorPair)
      (uniformRadius (realGauge id) (realGauge id) floorOperator floorPair floorPair) 1 1 = (false,true) ∧
    ¬ (∀ x ∈ floorPair, ∀ y ∈ floorPair, realGauge id (floorOperator.func x) (floorOperator.func y) = 0) := by
  have hd : diameter (realGauge id) floorPair = 2 := by
    simpa [floorPair] using real_diameter_pair 0 2
  have hp : 0 < realGauge id (floorOperator.func (some 0)) (floorOperator.func (some 2)) := by
    norm_num [floorOperator,liftOperator,realGauge,liftDistance]
  have hr : uniformRadius (realGauge id) (realGauge id) floorOperator floorPair floorPair = 2 := by
    simpa [floorPair,realGauge,liftDistance] using
      uniform_pair (realGauge id) (realGauge id) (realGauge_valid id) (realGauge_valid id) floorOperator
        (some 0) (some 2) hp
  refine ⟨⟨some 0,by simp [floorPair]⟩,?_,hd,hr,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · simp [dom,floorOperator,liftOperator]
    · have : x = some 2 := hx; subst x; simp [dom,floorOperator,liftOperator]
  · norm_num [thresholdType,hd,hr]
  · intro h; exact (ne_of_gt hp) (h _ (by simp [floorPair]) _ (by simp [floorPair]))

def translate : Operator (Option ℝ) none := liftOperator (fun x => x+1)
def translateDomain : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
def translateImage : Set (Option ℝ) := {some (-2),some (-1),some 1,some 3}

theorem translate_image : translate.func '' translateDomain = translateImage := by
  ext x
  norm_num [translate,translateDomain,translateImage,liftOperator,eq_comm]

theorem translate_fibers :
    translateDomain ⊆ dom translate ∧
    (∀ x ∈ translateDomain,
      fiber absGauge (1 : Operator (Option ℝ) none) univ x translateDomain =
        if x = some (-3) then {some (-3)} else if x = some 0 then {some 0} else {some (-2),some 2}) ∧
    (∀ x ∈ translateDomain,
      fiber absGauge translate univ (translate.func x) translateDomain =
        if x = some (-3) then {some (-3)} else if x = some 2 then {some 2} else {some (-2),some 0}) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [dom,translate,liftOperator]
  all_goals
    intro x hx
    simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals
      ext y
      simp only [fiber,mem_setOf_eq]
      by_cases hy : y ∈ translateDomain
      · simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;>
          norm_num [translateDomain,translate,liftOperator,absGauge,realGauge,liftDistance]
      · simp only [translateDomain,mem_insert_iff,mem_singleton_iff,not_or] at hy
        norm_num [hy,translateDomain]

theorem cover_two_lower {X : Type} (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    (ε : ENNReal) (h : ∀ c ∈ U, ∃ x ∈ U, ε ≤ d x c) : 2 ≤ covering_number d ε U := by
  classical
  apply le_iInf; intro S; apply le_iInf; intro hS
  obtain ⟨a,ha⟩ := hU
  obtain ⟨c,hc,_⟩ := hS.2 a ha
  obtain ⟨x,hx,hd⟩ := h c (hS.1 hc)
  obtain ⟨c',hc',hd'⟩ := hS.2 x hx
  have hne : c ≠ c' := by intro he; subst c'; exact (not_lt_of_ge hd) hd'
  have hsub : ({c,c'} : Finset X) ⊆ S := by simp [Finset.insert_subset_iff,hc,hc']
  have hcard := Finset.card_le_card hsub
  simp [hne] at hcard
  exact_mod_cast hcard

theorem translate_cover :
    covering_number (realGauge abs) (3/2) translateDomain = 2 ∧
    covering_number (realGauge abs) (3/2) (translate.func '' translateDomain) = 1 ∧
    ∃ hD : EntropyDefined (realGauge abs) (realGauge abs) translate translateDomain (3/2),
      entropyDifference (realGauge abs) (realGauge abs) translate translateDomain (3/2) hD = 1 := by
  have h15 : (1 : ENNReal) < 3/2 := by
    apply (ENNReal.lt_div_iff_mul_lt (by simp) (by simp)).mpr
    norm_num
  have h152 : (3/2 : ENNReal) ≤ 2 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
    norm_num
  have h153 : (3/2 : ENNReal) ≤ 3 := h152.trans (by norm_num)
  have hn : InternalEpsilonNet (realGauge abs) (3/2) translateDomain {some (-2),some 0} := by
    constructor
    · intro x hx; simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [translateDomain]
    · intro x hx
      simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2),by simp,by norm_num [realGauge,liftDistance]; exact h15⟩
      · exact ⟨some (-2),by simp,by norm_num [realGauge,liftDistance]⟩
      · exact ⟨some 0,by simp,by norm_num [realGauge,liftDistance]⟩
      · exact ⟨some (-2),by simp,by norm_num [realGauge,liftDistance]⟩
  have hi : covering_number (realGauge abs) (3/2) translateDomain = 2 := by
    apply le_antisymm
    · exact iInf_le_of_le {some (-2),some 0} (iInf_le_of_le hn (by norm_num))
    apply cover_two_lower _ _ ⟨some 0,by norm_num [translateDomain]⟩
    intro c hc
    simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h153⟩
    · exact ⟨some 0,by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h152⟩
    · exact ⟨some (-2),by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h152⟩
    · exact ⟨some 0,by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h152⟩
  have ho : covering_number (realGauge abs) (3/2) (translate.func '' translateDomain) = 1 := by
    rw [translate_image]
    apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some 1,by norm_num [translateImage]⟩)
    have hnet : InternalEpsilonNet (realGauge abs) (3/2) translateImage {some (-2)} := by
      constructor
      · simp [translateImage]
      · intro x hx
        refine ⟨some (-2),by simp,?_⟩
        simp only [translateImage,mem_insert_iff,mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> norm_num [realGauge,liftDistance] <;> exact h15
    exact iInf_le_of_le _ (iInf_le_of_le hnet (by simp))
  refine ⟨hi,ho,Or.inr (ho ▸ ENNReal.one_lt_top),?_⟩
  norm_num [entropyDifference,metric_entropy,log2_ereal,hi,ho,Real.logb]

end Chapter3
```

```lean filename=Chapter3/Correspondence.lean
import Chapter3.MoreExamples

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
variable {X I : Type} {bot : X}

theorem finite_inf_attained [Fintype I] (a : I → ENNReal) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, (⨅ k ∈ J, a k) = a j := by
  letI : Nonempty J := hJ.to_subtype
  obtain ⟨j,hj⟩ := exists_eq_ciInf_of_finite (f := fun j : J => a j)
  exact ⟨j,j.property,by simpa only [iInf_subtype] using hj.symm⟩

theorem radius_min_attained [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (U : Set X) (y : X) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, radius din (subfamily_pseudometric d J) f U y = radius din (d j) f U y := by
  rw [radius_subfamily]; exact finite_inf_attained _ J hJ

theorem uniform_min_attained [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, uniformRadius (d i) (subfamily_pseudometric d J) f U U = nullMatrix d f U j i := by
  rw [uniform_subfamily]; exact finite_inf_attained _ J hJ

noncomputable def subfamilyEntropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J K : Set I) (ε : ENNReal)
    (h : EntropyDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε) : EReal :=
  entropyDifference (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε h

theorem subfamily_difference_representation (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J K : Set I) (ε : ENNReal)
    (h : EntropyDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε) :
    subfamilyEntropyDifference d f U J K ε h =
      subfamily_metric_entropy d J ε U - subfamily_metric_entropy d K ε (f.func '' U) := rfl

theorem entropy_difference_finite (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal)
    (hi : covering_number din ε U < ⊤) (ho : covering_number dout ε (f.func '' U) < ⊤)
    (hD : EntropyDefined din dout f U ε) :
    entropyDifference din dout f U ε hD =
      ((Real.logb 2 (covering_number din ε U).toReal -
        Real.logb 2 (covering_number dout ε (f.func '' U)).toReal : ℝ) : EReal) := by
  simp [entropyDifference,entropy_finite din U hU ε hi,entropy_finite dout _ (hU.image _) ε ho]

theorem entropy_difference_signs (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal) (hD : EntropyDefined din dout f U ε) :
    (0 < entropyDifference din dout f U ε hD ↔ metric_entropy dout ε (f.func '' U) < metric_entropy din ε U) ∧
    (entropyDifference din dout f U ε hD < 0 ↔ metric_entropy din ε U < metric_entropy dout ε (f.func '' U)) ∧
    (entropyDifference din dout f U ε hD = 0 ↔ metric_entropy din ε U = metric_entropy dout ε (f.func '' U)) := by
  have ht : metric_entropy din ε U ≠ ⊤ ∨ metric_entropy dout ε (f.func '' U) ≠ ⊤ := by
    rcases hD with hi | ho
    · left; rw [entropy_finite din U hU ε hi]; simp
    · right; rw [entropy_finite dout _ (hU.image _) ε ho]; simp
  have hb : metric_entropy din ε U ≠ ⊥ ∨ metric_entropy dout ε (f.func '' U) ≠ ⊥ := by
    left; exact ne_of_gt (lt_of_lt_of_le (by simp) (metric_entropy_nonneg din ε U hU))
  refine ⟨EReal.sub_pos,EReal.sub_neg ht hb,?_⟩
  change _ - _ = 0 ↔ _ = _
  constructor
  · intro h
    exact le_antisymm (EReal.sub_nonpos.mp h.le) ((EReal.sub_nonneg ht hb).mp h.ge)
  · intro h
    exact le_antisymm (EReal.sub_nonpos.mpr h.le) ((EReal.sub_nonneg ht hb).mpr h.ge)

theorem swap_nonreverse :
    ¬ (activeComp (fun _ : Unit => twoD) swap two ∪
      activeComp (fun _ : Unit => twoD) swap (swap.func '' two) ⊆
      activeComp (fun _ : Unit => twoD) (swap * swap) two) ∧
    ¬ (idComp (fun _ : Unit => twoD) (swap * swap) two ⊆
      idComp (fun _ : Unit => twoD) swap two ∩
      idComp (fun _ : Unit => twoD) swap (swap.func '' two)) := by
  obtain ⟨_,_,him,ha,hi,hci,hca⟩ := swap_example
  simp [him,ha,hi,hci,hca]

theorem small_domain_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (hA : A.Nonempty) {τs τn ε : ENNReal}
    (hs : diameter din A < τs) (hst : τs ≤ τn)
    (hn : τn ≤ uniformRadius din dout f A A) (he : 0 < ε) :
    covering_number dout ε (f.func '' A) = 1 :=
  constant_cover dout f A hA he ((small_domain_iff din dout f A hs hst).mp hn)

end Chapter3
```

```lean filename=Chapter3/Completion.lean
import Chapter3.Correspondence

/- Additional proofs based on Zhe Li, The Operator Evolution Theory, vol. I,
   chapter 3, CC BY 4.0. https://glenzli.com/books/oet/ -/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
open scoped Classical

@[simp] theorem realGauge_some (q : ℝ → ℝ) (x y : ℝ) :
    realGauge q (some x) (some y) = ENNReal.ofReal |q x - q y| := rfl

theorem step_near {y r : ℝ} (hy : y ∈ Ico (-1 : ℝ) 0 ∪ Ioc 0 1)
    (hr : |y| < r) :
    ∃ x ∈ Ico (-1 : ℝ) 0 ∪ Ioc 0 1, |x-y| < r ∧
      realGauge id (step.func (some x)) (step.func (some y)) = 1 := by
  let t := min (1/2 : ℝ) ((r - |y|)/2)
  have ht : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1/2 := min_le_left _ _
  have htr : t ≤ (r - |y|)/2 := min_le_right _ _
  rcases hy with hy | hy
  · have hy0 := hy.2
    refine ⟨t, Or.inr ⟨ht,by linarith⟩, ?_, ?_⟩
    · rw [abs_of_neg hy0] at htr hr
      rw [abs_of_pos (by linarith : 0 < t-y)]
      linarith
    · simp [step,liftOperator,hy0,not_lt.mpr ht.le,realGauge,liftDistance]
  · have hy0 := hy.1
    refine ⟨-t, Or.inl ⟨by linarith,by linarith⟩, ?_, ?_⟩
    · rw [abs_of_pos hy0] at htr hr
      rw [abs_of_neg (by linarith : -t-y < 0)]
      linarith
    · simp [step,liftOperator,not_lt.mpr hy0.le,show -t < 0 by linarith,
        realGauge,liftDistance]

theorem step_radius {y : ℝ} (hy : y ∈ Ico (-1 : ℝ) 0 ∪ Ioc 0 1) :
    radius (realGauge id) (realGauge id) step stepDomain (some y) = ENNReal.ofReal |y| ∧
    0 < ENNReal.ofReal |y| := by
  have hyne : y ≠ 0 := by rcases hy with hy | hy <;> linarith [hy.2,hy.1]
  refine ⟨le_antisymm ?_ ?_,ENNReal.ofReal_pos.mpr (abs_pos.mpr hyne)⟩
  · apply sSup_le
    intro r hr
    by_contra hn
    have hyr : |y| < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y)
      (ne_of_lt hr.2.1)).mp (lt_of_not_ge hn)
    obtain ⟨x,hx,hxy,hout⟩ := step_near hy hyr
    have hz := hr.2.2 (some x) ⟨x,hx,rfl⟩
      ((ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg (x-y)) (ne_of_lt hr.2.1)).mpr hxy)
    rw [hout] at hz
    exact one_ne_zero hz
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    rintro _ ⟨x,hx,rfl⟩ hxy
    have hdist : |x-y| < |y| := (ENNReal.ofReal_lt_ofReal_iff (abs_pos.mpr hyne)).mp hxy
    have hs : (x < 0) ↔ (y < 0) := by
      rw [abs_lt] at hdist
      rcases hy with hy | hy
      · rw [abs_of_neg hy.2] at hdist
        constructor <;> intro h <;> linarith [hy.2]
      · rw [abs_of_pos hy.1] at hdist
        constructor <;> intro h <;> linarith [hy.1]
    simp [step,liftOperator,hs,realGauge,liftDistance]

theorem step_good_radius {y : ℝ} (hy : y ∈ Ico (-1 : ℝ) 0 ∪ Ioc 0 1) (r : ENNReal) :
    GoodRadius (realGauge id) (realGauge id) step stepDomain (some y) r ↔
      0 < r ∧ r < ⊤ ∧ r ≤ ENNReal.ofReal |y| := by
  rw [goodRadius_iff, (step_radius hy).1]

theorem uniform_zero_of_small {X : Type} {bot : X} (din dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (h : ∀ t : ℝ, 0 < t → ∃ x ∈ U, ∃ y ∈ U,
      din x y < ENNReal.ofReal t ∧ 0 < dout (f.func x) (f.func y)) :
    uniformRadius din dout f U U = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b,hb,hba⟩ := exists_between ha
  have hbt : b ≠ ⊤ := ne_of_lt (hba.trans_le le_top)
  obtain ⟨x,hx,y,hy,hxy,hout⟩ := h b.toReal (ENNReal.toReal_pos (ne_of_gt hb) hbt)
  rw [ENNReal.ofReal_toReal hbt] at hxy
  exact (output_separation hx hy hout).trans_lt (hxy.trans hba)

theorem step_uniform_zero :
    uniformRadius (realGauge id) (realGauge id) step stepDomain stepDomain = 0 := by
  apply uniform_zero_of_small
  intro t ht
  let a := min (1/2 : ℝ) (t/4)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have hat : a ≤ t/4 := min_le_right _ _
  refine ⟨some (-a),⟨-a,Or.inl ⟨by linarith,by linarith⟩,rfl⟩,
    some a,⟨a,Or.inr ⟨ha,by linarith⟩,rfl⟩,?_,?_⟩
  · apply (ENNReal.ofReal_lt_ofReal_iff ht).mpr
    dsimp only [id]
    rw [abs_of_neg (by linarith : -a-a < 0)]
    linarith
  · norm_num [step,liftOperator,show -a < 0 by linarith,not_lt.mpr ha.le,
      realGauge,liftDistance]

theorem cover_pair_small {X : Type} (d : X → X → ENNReal) (hs : ∀ x, d x x = 0)
    (a b : X) {ε : ENNReal} (he : 0 < ε) (hab : d b a < ε) :
    covering_number d ε {a,b} = 1 := by
  apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨a,by simp⟩)
  have hn : InternalEpsilonNet d ε {a,b} {a} := by
    constructor
    · simp
    · intro x hx
      refine ⟨a,by simp,?_⟩
      rcases hx with rfl | hx
      · simpa [hs] using he
      · have : x = b := hx; subst x; exact hab
  exact iInf_le_of_le _ (iInf_le_of_le hn (by simp))

theorem cover_pair_large {X : Type} (d : X → X → ENNReal) (hs : ∀ x, d x x = 0)
    (a b : X) {ε : ENNReal} (he : 0 < ε) (hab : ε ≤ d a b) (hba : ε ≤ d b a) :
    covering_number d ε {a,b} = 2 := by
  have hne : a ≠ b := by intro h; subst b; rw [hs] at hab; exact (not_le_of_gt he) hab
  apply le_antisymm
  · have hn : InternalEpsilonNet d ε {a,b} {a,b} := by
      constructor
      · simp
      · intro x hx; exact ⟨x,by simpa using hx,by simpa [hs] using he⟩
    exact iInf_le_of_le _ (iInf_le_of_le hn (by simp [hne]))
  · apply cover_two_lower _ _ ⟨a,by simp⟩
    intro c hc
    rcases hc with rfl | hc
    · exact ⟨b,by simp,hba⟩
    · have : c = b := hc; subst c; exact ⟨a,by simp,hab⟩

theorem step_cover_counterexample (τ : ENNReal) (hτ : 0 < τ) (hτt : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < τ ∧
      ({some (-a),some a} : Set (Option ℝ)) ⊆ stepDomain ∧
      covering_number (realGauge id) τ {some (-a),some a} = 1 ∧
      covering_number (realGauge id) (1/2) (step.func '' {some (-a),some a}) = 2 := by
  let a := min (1/2 : ℝ) (τ.toReal/4)
  have ht : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ) (ne_of_lt hτt)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have hat : a ≤ τ.toReal/4 := min_le_right _ _
  have hlt : ENNReal.ofReal (2*a) < τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (ne_of_lt hτt)).mpr (by linarith)
  refine ⟨a,ha,by linarith,hlt,?_,?_,?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨-a,Or.inl ⟨by linarith,by linarith⟩,rfl⟩
    · have : x = some a := hx; subst x
      exact ⟨a,Or.inr ⟨ha,by linarith⟩,rfl⟩
  · apply cover_pair_small _ (realGauge_valid id).dist_self _ _ hτ
    simpa [realGauge,liftDistance,abs_of_nonneg (show 0 ≤ a+a by linarith),two_mul] using hlt
  · have him : step.func '' {some (-a),some a} = {some (0 : ℝ),some 1} := by
      ext z
      simp [step,liftOperator,show -a < 0 by linarith,not_lt.mpr ha.le,eq_comm]
    rw [him]
    apply cover_pair_large _ (realGauge_valid id).dist_self <;>
      norm_num [realGauge,liftDistance]

def realInterval (a b : ℝ) : Set (Option ℝ) := some '' Icc a b

theorem interval_valid {a b : ℝ} (hab : a ≤ b) :
    (realInterval a b).Nonempty ∧ realInterval a b ⊆ dom floorOperator := by
  refine ⟨⟨some a,a,⟨le_rfl,hab⟩,rfl⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩; simp [dom,floorOperator,liftOperator]

theorem interval_diameter {a b : ℝ} (hab : a ≤ b) :
    diameter (realGauge id) (realInterval a b) = ENNReal.ofReal (b-a) := by
  apply le_antisymm
  · apply iSup_le; intro x; apply iSup_le; rintro ⟨x,hx,rfl⟩
    apply iSup_le; intro y; apply iSup_le; rintro ⟨y,hy,rfl⟩
    apply ENNReal.ofReal_le_ofReal
    dsimp only [id]
    exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2],by linarith [hx.1,hx.2,hy.1,hy.2]⟩
  · have h := le_diameter (realGauge id) (A := realInterval a b)
      (x := some b) (y := some a) ⟨b,⟨hab,le_rfl⟩,rfl⟩ ⟨a,⟨le_rfl,hab⟩,rfl⟩
    simpa [realGauge,liftDistance,abs_of_nonneg (sub_nonneg.mpr hab)] using h

theorem floor_interval_small :
    diameter (realGauge id) (realInterval 0 (1/2)) = 1/2 ∧
    uniformRadius (realGauge id) (realGauge id) floorOperator
      (realInterval 0 (1/2)) (realInterval 0 (1/2)) = ⊤ ∧
    thresholdType (diameter (realGauge id) (realInterval 0 (1/2)))
      (uniformRadius (realGauge id) (realGauge id) floorOperator
        (realInterval 0 (1/2)) (realInterval 0 (1/2))) 1 1 = (true,true) := by
  have hd : diameter (realGauge id) (realInterval 0 (1/2)) = 1/2 := by
    rw [interval_diameter (by norm_num)]; norm_num
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]; norm_num
  have hr : uniformRadius (realGauge id) (realGauge id) floorOperator
      (realInterval 0 (1/2)) (realInterval 0 (1/2)) = ⊤ := by
    apply (constant_radii _ _ _ _ ?_).2
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    have fx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hx.1,by norm_num; linarith [hx.2]⟩
    have fy : ⌊y⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hy.1,by norm_num; linarith [hy.2]⟩
    simp [floorOperator,liftOperator,fx,fy,realGauge,liftDistance]
  exact ⟨hd,hr,by norm_num [thresholdType,hd,hr]⟩

theorem floor_interval_cross :
    diameter (realGauge id) (realInterval (9/10) (11/10)) = 1/5 ∧
    uniformRadius (realGauge id) (realGauge id) floorOperator
      (realInterval (9/10) (11/10)) (realInterval (9/10) (11/10)) = 0 ∧
    thresholdType (diameter (realGauge id) (realInterval (9/10) (11/10)))
      (uniformRadius (realGauge id) (realGauge id) floorOperator
        (realInterval (9/10) (11/10)) (realInterval (9/10) (11/10))) 1 1 = (true,false) := by
  have hd : diameter (realGauge id) (realInterval (9/10) (11/10)) = 1/5 := by
    rw [interval_diameter (by norm_num)]; norm_num
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 5 by norm_num)]; norm_num
  have hr : uniformRadius (realGauge id) (realGauge id) floorOperator
      (realInterval (9/10) (11/10)) (realInterval (9/10) (11/10)) = 0 := by
    apply uniform_zero_of_small
    intro t ht
    let δ := min (1/10 : ℝ) (t/2)
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
    have hδ1 : δ ≤ 1/10 := min_le_left _ _
    have hδt : δ ≤ t/2 := min_le_right _ _
    have hf : ⌊1-δ⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
    refine ⟨some (1-δ),⟨1-δ,⟨by linarith,by linarith⟩,rfl⟩,
      some 1,⟨1,by norm_num,rfl⟩,?_,?_⟩
    · apply (ENNReal.ofReal_lt_ofReal_iff ht).mpr
      dsimp only [id]
      rw [abs_of_neg (by linarith : 1-δ-1 < 0)]
      linarith
    · norm_num [floorOperator,liftOperator,hf,realGauge,liftDistance]
  exact ⟨hd,hr,by norm_num [thresholdType,hd,hr]⟩

theorem floor_interval_large :
    diameter (realGauge id) (realInterval 0 2) = 2 ∧
    uniformRadius (realGauge id) (realGauge id) floorOperator
      (realInterval 0 2) (realInterval 0 2) = 0 ∧
    thresholdType (diameter (realGauge id) (realInterval 0 2))
      (uniformRadius (realGauge id) (realGauge id) floorOperator
        (realInterval 0 2) (realInterval 0 2)) 1 1 = (false,false) := by
  have hd : diameter (realGauge id) (realInterval 0 2) = 2 := by
    rw [interval_diameter (by norm_num)]; norm_num
  have hr : uniformRadius (realGauge id) (realGauge id) floorOperator
      (realInterval 0 2) (realInterval 0 2) = 0 := by
    apply le_antisymm _ (zero_le _)
    rw [← floor_interval_cross.2.1]
    apply uniform_domain_mono
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,⟨by linarith [hx.1],by linarith [hx.2]⟩,rfl⟩
  exact ⟨hd,hr,by norm_num [thresholdType,hd,hr]⟩

def StagesValid {X : Type} {bot : X} : List (Operator X bot) → Set X → Prop
  | [], _ => True
  | f :: fs, U => U ⊆ dom f ∧ StagesValid fs (f.func '' U)

theorem scale_counterexample_domain :
    ({some (0 : ℝ)} : Set (Option ℝ)).Nonempty ∧ realTwo.Nonempty ∧
    realTwo ⊆ dom (1 : Operator (Option ℝ) none) ∧
    ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ realTwo ∧
    diameter (realGauge id) ({some (0 : ℝ)} : Set (Option ℝ)) = 0 ∧
    diameter (realGauge id) realTwo = 1 ∧
    diameter (realGauge id) ({some (0 : ℝ)} : Set (Option ℝ)) < (1/2 : ENNReal) ∧
    (1/2 : ENNReal) ≤ diameter (realGauge id) realTwo := by
  have h0 := real_diameter_pair 0 0
  have h1 := real_diameter_pair 0 1
  norm_num at h0 h1
  refine ⟨⟨some 0,rfl⟩,⟨some 0,by simp [realTwo]⟩,?_,?_,h0,?_,
    scale_counterexample.2.1,scale_counterexample.2.2⟩
  · intro x hx
    rcases hx with rfl | hx
    · simp [dom]
    · have : x = some 1 := hx; subst x; simp [dom]
  · simp [realTwo]
  · exact h1

theorem floor_intervals_valid :
    ((realInterval 0 (1/2)).Nonempty ∧ realInterval 0 (1/2) ⊆ dom floorOperator) ∧
    ((realInterval (9/10) (11/10)).Nonempty ∧ realInterval (9/10) (11/10) ⊆ dom floorOperator) ∧
    ((realInterval 0 2).Nonempty ∧ realInterval 0 2 ⊆ dom floorOperator) :=
  ⟨interval_valid (by norm_num),interval_valid (by norm_num),interval_valid (by norm_num)⟩

theorem run_stages_valid {X : Type} {bot : X} (fs : List (Operator X bot))
    (U : Set X) (hU : U ⊆ dom (run fs)) : StagesValid fs U := by
  induction fs generalizing U with
  | nil => trivial
  | cons f fs ih =>
      have h := run_domains f fs U hU
      exact ⟨h.1, ih _ h.2⟩

theorem point_constant_fibers {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) (J : Set I) {c : X}
    (h : ∀ x ∈ U, f.func x = c) :
    (∀ y ∈ U, fiber d (f * f) J ((f * f).func y) U = U) ∧
    (f.func c ≠ bot → U ⊆ dom (f * f)) ∧
    (f.func c = bot → U ∩ dom (f * f) = ∅) := by
  have hi := point_constant_iteration f U h
  refine ⟨?_,hi.2⟩
  intro y hy
  apply fiber_const d (fun j hj x hx z hz => ?_) ⟨y,hy,rfl⟩
  rw [hi.1 x hx, hi.1 z hz]
  exact (hd j).dist_self _

end Chapter3
```

```lean filename=Chapter3/FourPoint.lean
import Chapter3.Completion

/- Exercise 3.5 of Zhe Li, The Operator Evolution Theory, vol. I.
   CC BY 4.0. https://glenzli.com/books/oet/ -/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
open scoped Classical

def fourU : Set (Option ℝ) := {some 0,some 1,some 2,some 3}
noncomputable def fourF : Operator (Option ℝ) none :=
  ⟨fun x => if x ∈ fourU then x else none, by simp [fourU]⟩
noncomputable def fourG : Operator (Option ℝ) none :=
  ⟨fun x => if x = some 0 then some 0 else if x = some 1 then some 3
    else if x = some 2 then some 1 else if x = some 3 then some 2 else none,by simp⟩

theorem four_operators :
    dom fourF = fourU ∧ dom fourG = fourU ∧
    fourF.func '' fourU = fourU ∧ fourG.func '' fourU = fourU ∧
    (∀ x ∉ fourU, fourF.func x = none ∧ fourG.func x = none) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · ext x
    by_cases hx : x ∈ fourU
    · have hn : x ≠ none := by
        simp only [fourU,mem_insert_iff,mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp
      simp [dom,fourF,hx,hn]
    · simp [dom,fourF,hx]
  · ext x
    by_cases h0 : x = some 0 <;> by_cases h1 : x = some 1 <;>
      by_cases h2 : x = some 2 <;> by_cases h3 : x = some 3 <;>
      simp [dom,fourG,fourU,h0,h1,h2,h3]
  · ext x; norm_num [fourU,fourF,eq_comm]
  · ext x; norm_num [fourU,fourG,eq_comm]; tauto
  · intro x hx
    simp only [fourU,mem_insert_iff,mem_singleton_iff,not_or] at hx
    simp [fourF,fourG,fourU,hx]

theorem cover_one_center {X : Type} (d : X → X → ENNReal) (U : Set X)
    (c : X) (hc : c ∈ U) (ε : ENNReal) (h : ∀ x ∈ U, d x c < ε) :
    covering_number d ε U = 1 := by
  apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨c,hc⟩)
  have hn : InternalEpsilonNet d ε U {c} := ⟨by simpa,fun x hx => ⟨c,by simp,h x hx⟩⟩
  exact iInf_le_of_le _ (iInf_le_of_le hn (by simp))

theorem separated_finite_cover {X : Type} (d : X → X → ENNReal)
    (hs : ∀ x, d x x = 0) (S : Finset X) {ε : ENNReal} (he : 0 < ε)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ d x y) :
    covering_number d ε (S : Set X) = (S.card : ENNReal) := by
  have hn : InternalEpsilonNet d ε (S : Set X) S :=
    ⟨Subset.rfl,fun x hx => ⟨x,hx,by simpa [hs] using he⟩⟩
  apply le_antisymm
  · exact iInf_le_of_le S (iInf_le_of_le hn le_rfl)
  apply le_iInf; intro T; apply le_iInf; intro hT
  have hST : S ⊆ T := by
    intro x hx
    obtain ⟨c,hc,hd⟩ := hT.2 x hx
    have heq : x = c := by
      by_contra hh
      exact (not_lt_of_ge (hsep x hx c (hT.1 hc) hh)) hd
    rwa [heq]
  exact_mod_cast Finset.card_le_card hST

theorem four_cover (ε : ENNReal) (he : 0 < ε) :
    covering_number (realGauge id) ε fourU =
      if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1 := by
  by_cases h1 : ε ≤ 1
  · rw [if_pos h1]
    have hsep : ∀ x ∈ ({some (0 : ℝ),some 1,some 2,some 3} : Finset (Option ℝ)),
        ∀ y ∈ ({some (0 : ℝ),some 1,some 2,some 3} : Finset (Option ℝ)),
          x ≠ y → ε ≤ realGauge id x y := by
      intro x hx y hy hne
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
      all_goals first | exact (hne rfl).elim | exact h1.trans (by norm_num [realGauge,liftDistance])
    simpa [fourU] using separated_finite_cover (realGauge id) (realGauge_valid id).dist_self
      {some 0,some 1,some 2,some 3} he hsep
  · rw [if_neg h1]
    have h1' : 1 < ε := lt_of_not_ge h1
    by_cases h2 : ε ≤ 2
    · rw [if_pos h2]
      apply le_antisymm
      · have hn : InternalEpsilonNet (realGauge id) ε fourU {some 1,some 2} := by
          constructor
          · intro x hx
            simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> norm_num [fourU]
          · intro x hx
            simp only [fourU,mem_insert_iff,mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact ⟨some 1,by simp,by simpa [realGauge,liftDistance] using h1'⟩
            · exact ⟨some 1,by simp,by simpa [realGauge,liftDistance] using he⟩
            · exact ⟨some 2,by simp,by simpa [realGauge,liftDistance] using he⟩
            · exact ⟨some 2,by simp,by norm_num [realGauge,liftDistance]; exact h1'⟩
        exact iInf_le_of_le _ (iInf_le_of_le hn (by norm_num))
      · apply cover_two_lower _ _ ⟨some 0,by norm_num [fourU]⟩
        intro c hc
        simp only [fourU,mem_insert_iff,mem_singleton_iff] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact ⟨some 3,by norm_num [fourU],h2.trans (by norm_num [realGauge,liftDistance])⟩
        · exact ⟨some 3,by norm_num [fourU],by norm_num [realGauge,liftDistance]; exact h2⟩
        · exact ⟨some 0,by norm_num [fourU],by simpa [realGauge,liftDistance] using h2⟩
        · exact ⟨some 0,by norm_num [fourU],h2.trans (by norm_num [realGauge,liftDistance])⟩
    · rw [if_neg h2]
      apply cover_one_center _ _ (some 1) (by norm_num [fourU])
      intro x hx
      apply lt_of_le_of_lt _ (lt_of_not_ge h2)
      simp only [fourU,mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [realGauge,liftDistance]

theorem four_center_exclusion :
    some (3/2 : ℝ) ∉ fourU ∧
    ¬ InternalEpsilonNet (realGauge id) (7/4) fourU {some (3/2 : ℝ)} := by
  have hn : some (3/2 : ℝ) ∉ fourU := by norm_num [fourU]
  exact ⟨hn,fun h => hn (h.1 (by simp))⟩

theorem four_entropy (ε : ENNReal) (he : 0 < ε) (f : Operator (Option ℝ) none)
    (hf : f = fourF ∨ f = fourG) :
    f.func '' fourU = fourU ∧
    covering_number (realGauge id) ε (f.func '' fourU) =
      (if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1) ∧
    ∃ hD : EntropyDefined (realGauge id) (realGauge id) f fourU ε,
      entropyDifference (realGauge id) (realGauge id) f fourU ε hD = 0 := by
  have him : f.func '' fourU = fourU := by
    rcases hf with rfl | rfl
    · exact four_operators.2.2.1
    · exact four_operators.2.2.2.1
  have hfin : fourU.Finite := by simp [fourU]
  have hU : fourU.Nonempty := ⟨some 0,by norm_num [fourU]⟩
  have hc := finite_cover (realGauge id) (realGauge_valid id).dist_self fourU hfin he
  refine ⟨him,by rw [him]; exact four_cover ε he,Or.inl hc,?_⟩
  simp [entropyDifference,him,entropy_finite _ _ hU ε hc,← EReal.coe_sub]

def ScalarBound (f : Operator (Option ℝ) none) (L : ENNReal) : Prop :=
  ∀ x ∈ fourU, ∀ y ∈ fourU, realGauge id (f.func x) (f.func y) ≤ L * realGauge id x y

theorem four_lip_bounds : ScalarBound fourF 1 ∧ ScalarBound fourG 3 := by
  constructor <;> intro x hx y hy
  all_goals
    simp only [fourU,mem_insert_iff,mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [fourF,fourG,fourU,realGauge,liftDistance]

theorem four_lip_optimal (L : ENNReal) :
    (ScalarBound fourF L ↔ 1 ≤ L) ∧ (ScalarBound fourG L ↔ 3 ≤ L) := by
  constructor <;> constructor
  · intro h
    have hh := h (some 0) (by norm_num [fourU]) (some 1) (by norm_num [fourU])
    simpa [fourF,fourU,realGauge,liftDistance] using hh
  · intro h x hx y hy
    exact (four_lip_bounds.1 x hx y hy).trans (mul_le_mul_right' h _)
  · intro h
    have hh := h (some 0) (by norm_num [fourU]) (some 1) (by norm_num [fourU])
    simpa [fourG,realGauge,liftDistance] using hh
  · intro h x hx y hy
    exact (four_lip_bounds.2 x hx y hy).trans (mul_le_mul_right' h _)

theorem four_lip_cover_comparison :
    covering_number (realGauge id) (7/4) (fourF.func '' fourU) ≤
      covering_number (realGauge id) ((7/4)/1) fourU ∧
    covering_number (realGauge id) (7/4) (fourG.func '' fourU) ≤
      covering_number (realGauge id) ((7/4)/3) fourU ∧
    covering_number (realGauge id) ((7/4)/1) fourU = 2 ∧
    covering_number (realGauge id) ((7/4)/3) fourU = 4 ∧
    covering_number (realGauge id) (7/4) (fourF.func '' fourU) = 2 ∧
    covering_number (realGauge id) (7/4) (fourG.func '' fourU) = 2 := by
  have hp : (0 : ENNReal) < 7/4 := ENNReal.div_pos (by norm_num) (by norm_num)
  have hp' : (0 : ENNReal) < (7/4)/3 := ENNReal.div_pos (ne_of_gt hp) (by norm_num)
  have h1 : (1 : ENNReal) < 7/4 := by
    apply (ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num)).mpr
    norm_num
  have h2 : (7/4 : ENNReal) ≤ 2 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
    norm_num
  have h3 : ((7/4)/3 : ENNReal) ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
    norm_num
    exact h2.trans (by norm_num)
  have hc : covering_number (realGauge id) (7/4) fourU = 2 := by
    rw [four_cover _ hp,if_neg (not_le_of_gt h1),if_pos h2]
  refine ⟨lip_cover _ _ fourF fourU (7/4) (by norm_num) (by norm_num) four_lip_bounds.1,
    lip_cover _ _ fourG fourU (7/4) (by norm_num) (by norm_num) four_lip_bounds.2,
    by simpa using hc,?_,?_,?_⟩
  · rw [four_cover _ hp',if_pos h3]
  · rw [four_operators.2.2.1]; exact hc
  · rw [four_operators.2.2.2.1]; exact hc

end Chapter3
```

```lean filename=Audit.lean
import Main
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if (`Chapter3).isPrefixOf n || (`formal_oet).isPrefixOf n then
      let axs ← Lean.collectAxioms n
      for ax in axs do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {n}"
      let refs := ci.type.getUsedConstants ++
        (match ci.value? with | some v => v.getUsedConstants | none => #[])
      let j := Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString)),
        ("refs", toJson (refs.map Name.toString))]
      logInfo j.compress
```

```json filename=alignment.json
{"case_id":"MG-C003","version":"0.1.1","items":[
{"id":"CH03-D01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.constComp"},{"file":"Chapter3/Core.lean","name":"Chapter3.idComp"},{"file":"Chapter3/Core.lean","name":"Chapter3.activeComp"},{"file":"Chapter3/Core.lean","name":"Chapter3.component_partition"}],"representation":"按常值优先定义三个指标集合，证明覆盖全指标集且两两不交；全域取U=dom。","dependencies":[]},
{"id":"CH03-D02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_representation"},{"file":"Chapter3/Core.lean","name":"Chapter3.subfamily_zero"}],"representation":"计算纤维用所有j∈J的零距合取表示，证明等价于冻结复合伪度量为零；允许任意目标。","dependencies":["CH03-D07"]},
{"id":"CH03-D03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.eqRel"},{"file":"Chapter3/Core.lean","name":"Chapter3.zeroRel"},{"file":"Chapter3/Core.lean","name":"Chapter3.imageSetoid"},{"file":"Chapter3/Core.lean","name":"Chapter3.ImageQuotient"},{"file":"Chapter3/Core.lean","name":"Chapter3.quotientPoint"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiberPreorder"},{"file":"Chapter3/Core.lean","name":"Chapter3.zeroRel_fiber"}],"representation":"点对集合保留两点属于U；像商是实际像集子类型上的Quotient；证明零距点对与全纤维成员对应。","dependencies":["CH03-D02"]},
{"id":"CH03-D04","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.GoodRadius"},{"file":"Chapter3/Radius.lean","name":"Chapter3.radius"},{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_representation"},{"file":"Chapter3/Radius.lean","name":"Chapter3.goodRadius_iff"}],"representation":"点态半径为全部有限正合法半径的sSup，球与评估域相交；证明集合包含表述对应。","dependencies":["CH03-P14-02"]},
{"id":"CH03-D05","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniformRadius"},{"file":"Chapter3/Radius.lean","name":"Chapter3.nullMatrix"}],"representation":"任意基点集A上的双重iInf；矩阵参数顺序为输出j、输入i，取A=U。","dependencies":["CH03-D04"]},
{"id":"CH03-D06","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.InputScale"},{"file":"Chapter3/Radius.lean","name":"Chapter3.diameter"},{"file":"Chapter3/Radius.lean","name":"Chapter3.diameterScale"},{"file":"Chapter3/Radius.lean","name":"Chapter3.channelType"},{"file":"Chapter3/Radius.lean","name":"Chapter3.threshold_cases"},{"file":"Chapter3/Radius.lean","name":"Chapter3.diameter_mono"},{"file":"Chapter3/Radius.lean","name":"Chapter3.thresholdType"}],"representation":"尺度定义在非空集合子类型上并要求包含单调；直径为点对上确界；Bool对精确编码两项阈值。","dependencies":["CH03-D05"]},
{"id":"CH03-D07","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.TotallyBoundedAt"},{"file":"Chapter3/Cover.lean","name":"Chapter3.covering_interface"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number_attained"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number_eq_top_iff"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.metric_entropy"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_pseudometric"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy_eq_metric_entropy"},{"file":"Chapter3/Cover.lean","name":"Chapter3.entropy_finite"}],"representation":"直接导入冻结内部覆盖数与熵；证明最小中心数取得及无有限覆盖等价于无穷，全有界量化所有有限正半径。","dependencies":[]},
{"id":"CH03-D08","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.EntropyDefined"},{"file":"Chapter3/Cover.lean","name":"Chapter3.entropyDifference"},{"file":"Chapter3/Cover.lean","name":"Chapter3.entropy_difference_infinite"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.subfamilyEntropyDifference"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.subfamily_difference_representation"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.entropy_difference_finite"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.entropy_difference_signs"}],"representation":"熵差需一端覆盖数有限的证明参数；输入输出可取任意复合子族度量；证明有限值、两种无穷分支及符号解释。","dependencies":["CH03-D07"]},
{"id":"CH03-P01-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_zero_row"}],"representation":"常值输出距离等于零，有限指标求和的零行也等于零。","dependencies":["CH03-D01"]},
{"id":"CH03-P01-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_colip_zero"}],"representation":"任意源k和正输入距离见证，调用冻结co-Lip单项退化定理推出K k i=0。","dependencies":["CH03-D01"]},
{"id":"CH03-P01-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.id_distance"}],"representation":"输出与输入逐点零距，利用两次零距换端点证明输出点对距离等于输入距离。","dependencies":["CH03-D01"]},
{"id":"CH03-P02-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.compose_active"}],"representation":"在实际像域f(U)上分类外算子，四种非有效组合推出复合非有效。","dependencies":["CH03-D01","CH03-P01-03","CH03-P02-03","CH03-P04-01"]},
{"id":"CH03-P02-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.run"},{"file":"Chapter3/Core.lean","name":"Chapter3.stageActive"},{"file":"Chapter3/Core.lean","name":"Chapter3.run_active"},{"file":"Chapter3/Core.lean","name":"Chapter3.run_domains"},{"file":"Chapter3/Completion.lean","name":"Chapter3.StagesValid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.run_stages_valid"}],"representation":"列表按作用顺序递归复合；stageActive递归使用每一步实际像域，空列表有效集为空，并证明域递推合法。另以递归StagesValid证明全部阶段的实际域合法性。","dependencies":["CH03-D01","CH03-P02-01"]},
{"id":"CH03-P02-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.compose_id"}],"representation":"逐点零距传递，且用外层保距排除复合常值分支。","dependencies":["CH03-D01","CH03-P01-03"]},
{"id":"CH03-P03-01","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.two"},{"file":"Chapter3/Examples.lean","name":"Chapter3.twoD"},{"file":"Chapter3/Examples.lean","name":"Chapter3.swap"},{"file":"Chapter3/Examples.lean","name":"Chapter3.swap_example"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.swap_nonreverse"}],"representation":"Option Bool编码吸收元和两点，验证扩展伪度量、域和像，计算两步有效与复合恒等，并明确否定两条逆包含。","dependencies":["CH03-D01"]},
{"id":"CH03-P04-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.outer_const"}],"representation":"将U中两点的像代入外算子在实际像集上的常值条件。","dependencies":["CH03-D01"]},
{"id":"CH03-P04-02","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.sevenGauge"},{"file":"Chapter3/Examples.lean","name":"Chapter3.sevenPhi"},{"file":"Chapter3/Examples.lean","name":"Chapter3.sevenPsi"},{"file":"Chapter3/Examples.lean","name":"Chapter3.seven_example"}],"representation":"Option(Fin 6)编码原七点；Bool给两分量，第一分量仅合并p,q；证明合法度量、复合域及内常值而复合非常值。","dependencies":["CH03-D01"]},
{"id":"CH03-P05-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_diagonal"}],"representation":"使用冻结单输入行化简；L可为无穷，ENNReal的乘零律给复合常值。","dependencies":["CH03-D01"]},
{"id":"CH03-P06-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_target"}],"representation":"任意目标在J中零距时，用三角不等式双向传递得到纤维相等。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_cover"}],"representation":"每个像目标纤维含一个原像，所有像目标纤维的并等于U，含空域。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_disjoint"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_cover"}],"representation":"任意两纤维有交点则目标零距并使纤维相等；结合非空及覆盖给去重分划。","dependencies":["CH03-D02","CH03-P06-01"]},
{"id":"CH03-P06-04","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_inter"}],"representation":"对非空J证明纤维等于所有单分量纤维之交，非空性用于恢复U条件。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-05","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_antitone"}],"representation":"J包含于K时，K的全部零距条件蕴含J的条件。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-06","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_singleton"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_full"}],"representation":"单元素纤维化为相应距离等于零；全指标纤维包含每个单分量纤维。","dependencies":["CH03-D02","CH03-P06-05"]},
{"id":"CH03-P06-07","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_id"}],"representation":"对任意目标y，恒等分量的输出零距条件等价于输入点与y零距。","dependencies":["CH03-D01","CH03-D02","CH03-P06-06"]},
{"id":"CH03-P06-08","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_const"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_const_empty"}],"representation":"像目标纤维等于U；与该目标正距离的目标纤维为空。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P07-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.Factors"},{"file":"Chapter3/Core.lean","name":"Chapter3.factor_iff"}],"representation":"实际像集到X的映射满足逐输入赋值公式时，输入等像关系包含于另一关系。","dependencies":["CH03-D03"]},
{"id":"CH03-P07-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.Factors"},{"file":"Chapter3/Core.lean","name":"Chapter3.factor_iff"}],"representation":"按实际像点存在的原像作选择并用关系包含证明赋值公式；空U无需选择任何点。","dependencies":["CH03-D03"]},
{"id":"CH03-P07-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.factors_both"}],"representation":"双向映射存在等价于双向关系包含，再由反对称性得到关系相等。","dependencies":["CH03-D03","CH03-P07-01"]},
{"id":"CH03-P07-04","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.scalar_factor_lip"}],"representation":"对实际像子类型的任意两点选原像，用正有限K的除法和L上界得到L/K；结论还允许L无穷。","dependencies":[]},
{"id":"CH03-P08-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.QuotientFactors"},{"file":"Chapter3/Core.lean","name":"Chapter3.quotient_factor_iff"}],"representation":"实际像集上的零距Setoid商；用Quotient.lift构造代表元无关映射，证明规定公式及必要性，包含空域。","dependencies":["CH03-D03"]},
{"id":"CH03-P08-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.quotient_factors_both"}],"representation":"双向商映射等价于两个零距关系集合相等。","dependencies":["CH03-D03","CH03-P08-01"]},
{"id":"CH03-P08-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.separated_rel"},{"file":"Chapter3/Core.lean","name":"Chapter3.separated_criteria"}],"representation":"分别仅假定两个实际像集上分离，证明点值关系等于零距关系并得到单向和双向判据一致。","dependencies":["CH03-D03","CH03-P07-01","CH03-P08-01"]},
{"id":"CH03-P09-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_preorder_refl"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_preorder_trans"}],"representation":"固定U的零距关系包含具有自反性和传递性。","dependencies":["CH03-D03"]},
{"id":"CH03-P09-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.relation_chain"}],"representation":"对任意有限m、a≤b≤m，从逐步集合包含归纳得到任意两层包含；实例R为各算子的zeroRel。","dependencies":[]},
{"id":"CH03-P09-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.relation_chain_strict"}],"representation":"从某一步真包含提取差集点，证明它在末层而不在首层，得到端点真包含。","dependencies":["CH03-P09-02"]},
{"id":"CH03-P10-01","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge"},{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/Examples.lean","name":"Chapter3.liftOperator_domain"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.step"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.stepDomain"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.step_valid"}],"representation":"Option实数编码吸收元，通常距离为ofReal绝对差，阶跃保持吸收元；原U非空且包含于定义域。","dependencies":[]},
{"id":"CH03-P10-02","status":"complete","declarations":[{"file":"Chapter3/Completion.lean","name":"Chapter3.step_near"},{"file":"Chapter3/Completion.lean","name":"Chapter3.step_radius"},{"file":"Chapter3/Completion.lean","name":"Chapter3.step_good_radius"}],"representation":"原固定U上每个实基点y的合法半径恰为0<r<∞且r≤|y|；证明点态半径=ofReal|y|>0，覆盖两个符号分支。","dependencies":["CH03-D04","CH03-P10-01","CH03-P14-02"]},
{"id":"CH03-P10-03","status":"complete","declarations":[{"file":"Chapter3/Completion.lean","name":"Chapter3.step_uniform_zero"}],"representation":"在同一固定阶跃评估域内，构造趋近零的异号点对；任意正尺度内输出距离仍为1，故统一半径为0。","dependencies":["CH03-D05","CH03-P10-01","CH03-P18-02"]},
{"id":"CH03-P11-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_const"}],"representation":"任意输出子族包含于常值分量时，每个像目标的子族纤维等于U。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P11-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.constant_radii"},{"file":"Chapter3/Radius.lean","name":"Chapter3.constant_subfamily_radii"}],"representation":"所有输出点对零距使任意有限正半径合法，从上确界得到点态无穷和统一无穷。","dependencies":["CH03-D01","CH03-D02","CH03-D04","CH03-D05","CH03-D07","CH03-P14-02"]},
{"id":"CH03-P11-03","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.infiniteGauge"},{"file":"Chapter3/Examples.lean","name":"Chapter3.infinite_radius_example"}],"representation":"任意指定i,j的Option Bool例；输入i的异点距离无穷，其余分量距离1，含i=j和i≠j；恒等算子统一半径无穷但输出分量非常值。","dependencies":["CH03-D01","CH03-D04","CH03-D05","CH03-P03-01","CH03-P14-02"]},
{"id":"CH03-P12-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.id_image_fiber"}],"representation":"基点y在U，用恒等分量点对保距证明以f(y)为目标的纤维等于输入零距类。","dependencies":["CH03-D01","CH03-D02","CH03-P01-03","CH03-P06-06"]},
{"id":"CH03-P12-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.id_radius_lower"}],"representation":"有限正r的输入球内只有输入零距点时，证明r合法并得到半径≥r>0。","dependencies":["CH03-D01","CH03-D04","CH03-P01-03","CH03-P14-02"]},
{"id":"CH03-P13-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_subfamily"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.radius_min_attained"}],"representation":"证明子族点态半径等于分量半径iInf，并在有限非空J上证明某个分量取得该最小值。","dependencies":["CH03-D02","CH03-D04","CH03-D07","CH03-P14-02"]},
{"id":"CH03-P13-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_subfamily"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.uniform_min_attained"}],"representation":"通过任意下界的等价式交换基点与分量量词，得到统一半径iInf公式并证明有限非空最小值取得。","dependencies":["CH03-D02","CH03-D04","CH03-D05","CH03-D07","CH03-P14-02"]},
{"id":"CH03-P13-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_subfamily_antitone"}],"representation":"对扩大后的输出子族取更多下确界，统一半径不增。","dependencies":["CH03-D05","CH03-D07","CH03-P13-02"]},
{"id":"CH03-P14-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.fiber_truncation"}],"representation":"纤维成员条件给反向输出零距，再以对称性改为原文方向。","dependencies":["CH03-D02"]},
{"id":"CH03-P14-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_witness"},{"file":"Chapter3/Radius.lean","name":"Chapter3.below_radius"},{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_truncation"}],"representation":"严格小于sSup时实际提取大于输入距离的有限正合法半径，应用其球包含条件和对称性。","dependencies":["CH03-D04"]},
{"id":"CH03-P14-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.composition_truncation"}],"representation":"显式保留输入属于上游定义域、两像点属于下游域；将像点代入纤维判据。","dependencies":["CH03-D02","CH03-P14-01"]},
{"id":"CH03-P15-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.compose_radius_zero"}],"representation":"下游零距保持仅在实际像域要求；以所有严格小于上游统一半径的点对归零推出复合下界。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02","CH03-P18-01"]},
{"id":"CH03-P15-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.compose_radius_lip"}],"representation":"有限非零L的标量上界与ENNReal严格除法不等式拉回下游实际像域半径，统一涵盖右端零及无穷。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02","CH03-P18-01"]},
{"id":"CH03-P16-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.thresholdType"},{"file":"Chapter3/Radius.lean","name":"Chapter3.threshold_cases"}],"representation":"Bool对取四个不同值，逐个证明值与原文四组互补不等式等价。","dependencies":[]},
{"id":"CH03-P16-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.threshold_scale_mono"}],"representation":"尺度小于旧阈值且旧阈值不大于新阈值，推出小于新阈值。","dependencies":[]},
{"id":"CH03-P16-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.threshold_null_antitone"}],"representation":"新零化阈值不大于半径时，旧阈值也不大于半径。","dependencies":[]},
{"id":"CH03-P17-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.scale_domain_mono"}],"representation":"任意InputScale的包含单调公理推出缩域尺度不增及严格阈值结论。","dependencies":["CH03-D06"]},
{"id":"CH03-P17-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_domain_mono"}],"representation":"固定基点时，将大域上每个严格半径内零距条件限制到小域，证明点态半径不减。","dependencies":["CH03-D04","CH03-P14-02"]},
{"id":"CH03-P17-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_domain_mono"}],"representation":"同时将两点量词从A限制到B，得到基点集和评估域同时缩小的统一下界。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02","CH03-P18-01"]},
{"id":"CH03-P17-04","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/Examples.lean","name":"Chapter3.real_diameter_pair"},{"file":"Chapter3/Examples.lean","name":"Chapter3.scale_counterexample"},{"file":"Chapter3/Completion.lean","name":"Chapter3.scale_counterexample_domain"}],"representation":"带吸收元实线上A={0,1}、B={0}，直径分别1和0，阈值1/2，且B包含于A。","dependencies":["CH03-D06","CH03-P10-01"]},
{"id":"CH03-P18-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_le_point"},{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_zero"}],"representation":"统一下确界不大于每个基点半径，严格输入距离条件推出输出零距。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02"]},
{"id":"CH03-P18-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.output_separation"}],"representation":"取严格低于统一半径必归零的逆否，得到正输出分离的输入距离下界。","dependencies":["CH03-D05","CH03-P18-01"]},
{"id":"CH03-P18-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.separation_witness"}],"representation":"对每个大于统一半径的alpha提取失败点对；取epsilon=min(1,输出距离)，证明有限正且不超过输出距离，包括无穷输出。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02"]},
{"id":"CH03-P19-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.threshold_fiber"}],"representation":"统一半径大于等于阈值时，将开球成员的严格距离代入统一归零判据。","dependencies":["CH03-D02","CH03-D05","CH03-P18-01"]},
{"id":"CH03-P19-02","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.cover_push"},{"file":"Chapter3/Cover.lean","name":"Chapter3.threshold_cover"}],"representation":"将每个内部有限中心集S映为f(S)，证明仍为内部中心且基数不增；对所有S取iInf，覆盖空集和无有限覆盖。","dependencies":["CH03-D05","CH03-D07","CH03-P18-01"]},
{"id":"CH03-P19-03","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.log2_mono"},{"file":"Chapter3/Cover.lean","name":"Chapter3.threshold_entropy"}],"representation":"证明冻结扩展log2单调，再应用覆盖数不等式；非空B为其特例。","dependencies":["CH03-D05","CH03-D07","CH03-P19-02"]},
{"id":"CH03-P20-01","status":"complete","declarations":[{"file":"Chapter3/Completion.lean","name":"Chapter3.step_cover_counterexample"}],"representation":"对每个有限正τ取a=min(1/2,τ.toReal/4)，证明0<a≤1、2a<τ、B={-a,a}包含于原U；内部输入覆盖数为1，输出在1/2尺度的内部覆盖数为2。","dependencies":["CH03-D07","CH03-P10-01","CH03-P28-02"]},
{"id":"CH03-P21-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.small_domain_iff"}],"representation":"精确保留diam<tauS≤tauN；正向以直径控制每对距离，反向由所有输出零距得到统一半径无穷。","dependencies":["CH03-D04","CH03-D05","CH03-D06","CH03-P11-02","CH03-P18-01"]},
{"id":"CH03-P21-02","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.cover_zero_class"},{"file":"Chapter3/Cover.lean","name":"Chapter3.constant_cover"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.small_domain_cover"}],"representation":"非空像集用单内部中心覆盖，配合非空覆盖数至少1，得到任意正精度覆盖数恰为1。","dependencies":["CH03-D05","CH03-D06","CH03-D07","CH03-P21-01"]},
{"id":"CH03-P22-01","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.finite_cover"},{"file":"Chapter3/Cover.lean","name":"Chapter3.finite_entropy_difference"}],"representation":"有限集合以自身作内部中心；两端子族覆盖数≥1且有限，熵为实数嵌入并给实数差值。","dependencies":["CH03-D02","CH03-D07","CH03-D08"]},
{"id":"CH03-P23-01","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.const_entropy"}],"representation":"常值输出内部覆盖数1、熵0，输出有限保证差值定义，差等于输入熵且允许其无穷。","dependencies":["CH03-D07","CH03-D08","CH03-P21-02"]},
{"id":"CH03-P23-02","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.cover_push"},{"file":"Chapter3/Cover.lean","name":"Chapter3.cover_pull"},{"file":"Chapter3/Cover.lean","name":"Chapter3.isometric_cover"},{"file":"Chapter3/Cover.lean","name":"Chapter3.id_entropy"}],"representation":"前向映射内部中心，反向为输出中心选择原像，证明恒等分量两端覆盖数及熵相等。","dependencies":["CH03-D01","CH03-D07","CH03-P01-03"]},
{"id":"CH03-P23-03","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.id_entropy_difference"}],"representation":"假定差值定义且U非空，由两端覆盖数相等推出有限，消去有限自差得到0。","dependencies":["CH03-D01","CH03-D07","CH03-D08","CH03-P23-02"]},
{"id":"CH03-P24-01","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.cover_push"},{"file":"Chapter3/Cover.lean","name":"Chapter3.lip_cover"}],"representation":"有限正L将epsilon/L输入内覆盖推为epsilon输出内覆盖，Finset.image基数不增。","dependencies":["CH03-D07"]},
{"id":"CH03-P24-02","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.lip_entropy_bound"},{"file":"Chapter3/Cover.lean","name":"Chapter3.entropy_finite"}],"representation":"全有界给两输入精度的有限覆盖，像覆盖也有限；扩展实数减法单调给所述熵差下界。","dependencies":["CH03-D07","CH03-D08","CH03-P19-03","CH03-P24-01"]},
{"id":"CH03-P25-01","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.cover_pull"},{"file":"Chapter3/Cover.lean","name":"Chapter3.colip_cover"}],"representation":"选取每个内部输出中心的原像，co-Lip求和单项下界和正有限K除法给输入内覆盖；无输出有限覆盖也适用。","dependencies":["CH03-D07"]},
{"id":"CH03-P25-02","status":"complete","declarations":[{"file":"Chapter3/Cover.lean","name":"Chapter3.colip_entropy_bound"}],"representation":"输入全有界提供差值定义，输出熵可无穷；扩展实数减法单调推出熵差上界。","dependencies":["CH03-D07","CH03-D08","CH03-P19-03","CH03-P25-01"]},
{"id":"CH03-P26-01","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/Examples.lean","name":"Chapter3.absGauge"},{"file":"Chapter3/Examples.lean","name":"Chapter3.affine"},{"file":"Chapter3/Examples.lean","name":"Chapter3.affine_example"}],"representation":"Option实数上绝对值读数伪度量和仿射算子合法；U={0,1}上phi的指定纤维为U，分量为常值。","dependencies":["CH03-D01","CH03-D02","CH03-P10-01"]},
{"id":"CH03-P26-02","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.affine_example"}],"representation":"同一U上phi平方的指定纤维为{0}，分量为有效，且U属于复合定义域。","dependencies":["CH03-D01","CH03-D02","CH03-P10-01","CH03-P26-01"]},
{"id":"CH03-P26-03","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.point_constant_iteration"},{"file":"Chapter3/Completion.lean","name":"Chapter3.point_constant_fibers"}],"representation":"若f在U点值常为c，则平方在U常为f(c)；f(c)非吸收时U仍合法，为吸收时U与复合定义域不交。明确证明平方算子的每个像目标子族纤维均为U，并区分定义域合法与再次输出吸收元分支。","dependencies":["CH03-D02","CH03-P06-08"]},
{"id":"CH03-P27-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.colip_point_gap"}],"representation":"正co-Lip条目反射输出零距，故输入正距离不可能严格小于点态半径；不要求系数有限。","dependencies":["CH03-D04","CH03-P14-02"]},
{"id":"CH03-P27-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.colip_uniform_gap"}],"representation":"每个输入距离为零，或不小于统一半径；下确界与点态间隙给出二择。","dependencies":["CH03-D04","CH03-D05","CH03-P18-01","CH03-P27-01"]},
{"id":"CH03-P28-01","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.translate"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.translateDomain"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.translate_fibers"}],"representation":"完整按四个输入代表列出恒等和平移纤维，包含重复块去重对应；证明平移域条件。","dependencies":["CH03-D02","CH03-P10-01","CH03-P26-01"]},
{"id":"CH03-P28-02","status":"complete","declarations":[{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.translate_image"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.cover_two_lower"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.translate_cover"}],"representation":"精确半径3/2时用双内部中心及排除单中心证明输入覆盖数2，单内部中心证明输出覆盖数1，熵差1。","dependencies":["CH03-D07","CH03-D08","CH03-P10-01","CH03-P28-01"]},
{"id":"CH03-P29-01","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.floor_intervals_valid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.floor_interval_small"}],"representation":"原带吸收元实线及取整算子；非空合法域[0,1/2]的直径1/2，输出常值，统一半径∞，阈值(1,1)得到(true,true)。","dependencies":["CH03-D04","CH03-D05","CH03-D06","CH03-P10-01","CH03-P11-02","CH03-P29-03"]},
{"id":"CH03-P29-02","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.floor_intervals_valid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.floor_interval_cross"}],"representation":"非空合法域[9/10,11/10]的直径1/5；在1附近构造任意近且输出不同的点对，统一半径0，类型(true,false)。","dependencies":["CH03-D05","CH03-D06","CH03-P10-01","CH03-P18-02","CH03-P29-03"]},
{"id":"CH03-P29-03","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.floorOperator"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.floorPair"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.uniform_pair"},{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.floor_pair"}],"representation":"通常实线取整算子在D={0,2}上合法；直径2、统一半径2、阈值类型(false,true)，半径来自输入两点间隙。","dependencies":["CH03-D04","CH03-D05","CH03-D06","CH03-P10-01","CH03-P14-02","CH03-P17-04","CH03-P18-02"]},
{"id":"CH03-P29-04","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.floor_intervals_valid"},{"file":"Chapter3/Completion.lean","name":"Chapter3.floor_interval_large"}],"representation":"非空合法域[0,2]的直径2；由跨越1的小区间包含及统一半径域单调性证明半径0，类型(false,false)。","dependencies":["CH03-D05","CH03-D06","CH03-P10-01","CH03-P17-03","CH03-P29-02","CH03-P29-03"]},
{"id":"CH03-P29-05","status":"complete","declarations":[{"file":"Chapter3/MoreExamples.lean","name":"Chapter3.floor_pair"}],"representation":"同一合法二点D具有半径2≥1但输出0和2仍正分离，否定无直径条件的整体零化蕴含。","dependencies":["CH03-D05","CH03-D06","CH03-P10-01","CH03-P17-04","CH03-P29-03"]},
{"id":"CH03-P30-01","status":"complete","declarations":[{"file":"Chapter3/Examples.lean","name":"Chapter3.realGauge_valid"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.fourU"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_cover"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_center_exclusion"}],"representation":"原四点实集U={0,1,2,3}，任意ε>0的内部覆盖数：ε≤1时4，1<ε≤2时2，ε>2时1；分别证明上下界，包含两个开球端点；3/2不属于U，不能充当内部中心。","dependencies":["CH03-D07","CH03-P10-01","CH03-P28-02"]},
{"id":"CH03-P30-02","status":"complete","declarations":[{"file":"Chapter3/FourPoint.lean","name":"Chapter3.fourF"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.fourG"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_operators"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_entropy"}],"representation":"两个算子按题表取值并在U外为吸收元，证明定义域及像均为U；任意正精度像覆盖数同于输入的完整分段，有限熵差为0。","dependencies":["CH03-D07","CH03-D08","CH03-P10-01","CH03-P22-01","CH03-P30-01"]},
{"id":"CH03-P30-03","status":"complete","declarations":[{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_operators"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.ScalarBound"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_lip_bounds"},{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_lip_optimal"}],"representation":"逐对证明f的标量Lip界1与g的界3；由输入点0和1推出任意合法系数分别≥1和≥3，故最优值为1和3。","dependencies":["CH03-P10-01","CH03-P30-01","CH03-P30-02"]},
{"id":"CH03-P30-04","status":"complete","declarations":[{"file":"Chapter3/FourPoint.lean","name":"Chapter3.four_lip_cover_comparison"}],"representation":"实际调用一般Lip覆盖上界，在ε=7/4用常数1、3；右侧输入覆盖数分别2、4，两算子真实输出覆盖数均为2，故第一界取等、第二界宽松。","dependencies":["CH03-D07","CH03-P10-01","CH03-P24-01","CH03-P30-01","CH03-P30-02","CH03-P30-03"]}
]}
```