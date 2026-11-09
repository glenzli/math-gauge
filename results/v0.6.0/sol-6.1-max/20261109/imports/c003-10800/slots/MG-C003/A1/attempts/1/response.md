92 项均已完成；项目已在指定环境编译通过，并通过公理依赖审计。保留冻结附件目录，运行 `python3 build.py`。

数学来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下为新增 Lean 形式化。

```lean filename=Main.lean
import Chapter3.Correspondence
import Audit
```

```lean filename=Chapter3/Core.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/-
Mathematical source: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, Chapter 3, https://glenzli.com/books/oet/, CC BY 4.0.
ORCID https://orcid.org/0009-0006-6536-3453.
This file is a new Lean formalization of that source.
-/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
variable {X I : Type} {bot : X}

def constComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}
def idComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}
def actComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (constComponents d f U ∪ idComponents d f U)ᶜ

theorem component_partition (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    constComponents d f U ∪ idComponents d f U ∪ actComponents d f U = univ ∧
    Disjoint (constComponents d f U) (idComponents d f U) ∧
    Disjoint (constComponents d f U ∪ idComponents d f U) (actComponents d f U) := by
  classical
  simp only [actComponents, union_compl_self, true_and]
  constructor
  · exact disjoint_left.mpr (by intro i hi hj; exact hj.1 hi)
  · exact disjoint_compl_right

theorem zero_trans {d : X → X → ENNReal}
    (tri : ∀ x y z, d x z ≤ d x y + d y z) {x y z : X}
    (hxy : d x y = 0) (hyz : d y z = 0) : d x z = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa [hxy, hyz] using tri x y z

theorem zero_replace {d : X → X → ENNReal}
    (sym : ∀ x y, d x y = d y x)
    (tri : ∀ x y z, d x z ≤ d x y + d y z)
    {a b c e : X} (hab : d a b = 0) (hce : d c e = 0) : d a c = d b e := by
  apply le_antisymm
  · calc
      d a c ≤ d a b + d b c := tri _ _ _
      _ ≤ d a b + (d b e + d e c) := add_le_add le_rfl (tri _ _ _)
      _ = d b e := by rw [hab, sym e c, hce]; simp
  · calc
      d b e ≤ d b a + d a e := tri _ _ _
      _ ≤ d b a + (d a c + d c e) := add_le_add le_rfl (tri _ _ _)
      _ = d a c := by rw [sym b a, hab, hce]; simp

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) {i : I} (hi : i ∈ constComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (f.func x) (f.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) {i k : I}
    (hi : i ∈ constComponents d f U) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hpos
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hxy

theorem id_isometry (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) {i : I} (hi : i ∈ idComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact zero_replace (hd i).symm (hd i).triangle (hi.2 x hx) (hi.2 y hy)

theorem outer_const (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) :
    constComponents d g (f.func '' U) ⊆ constComponents d (g * f) U := by
  intro i hi x hx y hy
  exact hi _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

theorem id_comp (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) :
    idComponents d f U ∩ idComponents d g (f.func '' U) ⊆ idComponents d (g * f) U := by
  intro i hi
  constructor
  · intro hc
    apply hi.1.1
    intro x hx y hy
    rw [← id_isometry d hd g (f.func '' U) hi.2 _ (mem_image_of_mem _ hx)
      _ (mem_image_of_mem _ hy)]
    exact hc x hx y hy
  · intro x hx
    exact zero_trans (hd i).triangle
      (hi.2.2 _ (mem_image_of_mem _ hx)) (hi.1.2 x hx)

theorem act_comp (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) :
    actComponents d (g * f) U ⊆ actComponents d f U ∪ actComponents d g (f.func '' U) := by
  classical
  intro i hi
  by_contra hn
  have hf : i ∈ constComponents d f U ∪ idComponents d f U := by
    exact Classical.not_not.mp ((not_or.mp hn).1)
  have hg : i ∈ constComponents d g (f.func '' U) ∪ idComponents d g (f.func '' U) := by
    exact Classical.not_not.mp ((not_or.mp hn).2)
  apply hi
  rcases hg with hgc | hgi
  · exact Or.inl (outer_const d f g U hgc)
  · rcases hf with hfc | hfi
    · left
      intro x hx y hy
      change d i (g.func (f.func x)) (g.func (f.func y)) = 0
      rw [id_isometry d hd g (f.func '' U) hgi _ (mem_image_of_mem _ hx)
        _ (mem_image_of_mem _ hy)]
      exact hfc x hx y hy
    · exact Or.inr (id_comp d hd f g U ⟨hfi, hgi⟩)

def run : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => run fs * f
def chainActs (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => actComponents d f U ∪ chainActs d fs (f.func '' U)
def chainDomains : List (Operator X bot) → Set X → Prop
  | [], U => U ⊆ dom (1 : Operator X bot)
  | f :: fs, U => U ⊆ dom f ∧ chainDomains fs (f.func '' U)

theorem dom_comp (f g : Operator X bot) :
    dom (g * f) = {x | x ∈ dom f ∧ f.func x ∈ dom g} := by
  ext x
  change g.func (f.func x) ≠ bot ↔ f.func x ≠ bot ∧ g.func (f.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro he
    apply h
    rw [he, g.preserves_bot]
  · exact And.right

theorem chain_domains (fs : List (Operator X bot)) (U : Set X)
    (h : U ⊆ dom (run fs)) : chainDomains fs U := by
  induction fs generalizing U with
  | nil => exact h
  | cons f fs ih =>
    have hh : ∀ x ∈ U, x ∈ dom f ∧ f.func x ∈ dom (run fs) := by
      intro x hx
      exact (Set.ext_iff.mp (dom_comp f (run fs)) x).mp (h hx)
    exact ⟨fun x hx => (hh x hx).1, ih _ (by
      rintro _ ⟨x, hx, rfl⟩; exact (hh x hx).2)⟩

theorem act_identity (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (U : Set X) :
    actComponents d (1 : Operator X bot) U = ∅ := by
  classical
  ext i
  simp only [mem_empty_iff_false, iff_false]
  intro h
  apply h
  by_cases hc : i ∈ constComponents d (1 : Operator X bot) U
  · exact Or.inl hc
  · exact Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩

theorem act_chain (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (fs : List (Operator X bot)) (U : Set X) :
    actComponents d (run fs) U ⊆ chainActs d fs U := by
  induction fs generalizing U with
  | nil => simp [run, chainActs, act_identity d hd]
  | cons f fs ih =>
    exact (act_comp d hd f (run fs) U).trans (union_subset_union subset_rfl (ih _))

theorem const_comp_diagonal [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) {j : I}
    (hc : j ∈ constComponents d f U) (L : I → I → ENNReal)
    (hL : IsLipMatrix d g (f.func '' U) L) (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ constComponents d (g * f) U := by
  intro x hx y hy
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
    _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
  exact le_antisymm (by simpa [hc x hx y hy] using h) (zero_le _)

def fiber (d : I → X → X → ENNReal) (f : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}
def componentFiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) : Set X := {x | x ∈ U ∧ d i (f.func x) y = 0}

theorem sup_zero_iff (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact le_antisymm ((le_iSup (fun k : J => d k.1 x y) ⟨j,hj⟩).trans (le_of_eq h)) (zero_le _)
  · intro h
    apply le_antisymm _ (zero_le _)
    exact iSup_le (fun j => le_of_eq (h j.1 j.2))

theorem fiber_inter (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    fiber d f J y U = ⋂ j ∈ J, componentFiber d f j y U := by
  ext x
  simp only [fiber, componentFiber, mem_setOf_eq, sup_zero_iff, mem_iInter]
  constructor
  · exact fun h j hj => ⟨h.1, h.2 j hj⟩
  · intro h
    exact ⟨(h hJ.choose hJ.choose_spec).1, fun j hj => (h j hj).2⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    {J K : Set I} (h : J ⊆ K) (y : X) (U : Set X) :
    fiber d f K y U ⊆ fiber d f J y U := by
  intro x hx
  exact ⟨hx.1, (sup_zero_iff _ _ _ _).mpr
    (fun j hj => (sup_zero_iff _ _ _ _).mp hx.2 j (h hj))⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f {i} y U = componentFiber d f i y U := by
  simp [fiber, componentFiber, subfamily_pseudometric_singleton]

theorem fiber_full_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f univ y U ⊆ componentFiber d f i y U := by
  rw [← fiber_singleton]
  exact fiber_antitone d f (subset_univ _) y U

theorem fiber_target (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) {y z : X} (h : subfamily_pseudometric d J y z = 0) (U : Set X) :
    fiber d f J y U = fiber d f J z U := by
  have hz := (sup_zero_iff _ _ _ _).mp h
  ext x
  simp only [fiber, mem_setOf_eq, sup_zero_iff]
  constructor
  · intro hx
    exact ⟨hx.1, fun j hj => zero_trans (hd j).triangle (hx.2 j hj) (hz j hj)⟩
  · intro hx
    exact ⟨hx.1, fun j hj => zero_trans (hd j).triangle (hx.2 j hj)
      (by rw [(hd j).symm]; exact hz j hj)⟩

theorem fiber_nonempty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (U : Set X) {y : X} (hy : y ∈ f.func '' U) :
    (fiber d f J y U).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, (sup_zero_iff _ _ _ _).mpr (fun j _ => (hd j).dist_self _)⟩

theorem fiber_cover (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (U : Set X) : (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨y, _, hx⟩; exact hx.1
  · intro hx
    exact ⟨f.func x, mem_image_of_mem _ hx, hx,
      (sup_zero_iff _ _ _ _).mpr (fun j _ => (hd j).dist_self _)⟩

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X) :
    fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U) := by
  classical
  by_cases hh : Disjoint (fiber d f J y U) (fiber d f J z U)
  · exact Or.inr hh
  · left
    obtain ⟨x, hx, hz⟩ := not_disjoint_iff.mp hh
    apply fiber_target d hd
    apply (sup_zero_iff _ _ _ _).mpr
    intro j hj
    exact zero_trans (hd j).triangle
      (by rw [(hd j).symm]; exact (sup_zero_iff _ _ _ _).mp hx.2 j hj)
      ((sup_zero_iff _ _ _ _).mp hz.2 j hj)

theorem id_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ idComponents d f U) (y : X) :
    componentFiber d f i y U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, by
      rw [← zero_replace (hd i).symm (hd i).triangle (hi.2 x hx.1) ((hd i).dist_self y)]
      exact hx.2⟩
  · intro hx
    exact ⟨hx.1, by
      rw [zero_replace (hd i).symm (hd i).triangle (hi.2 x hx.1) ((hd i).dist_self y)]
      exact hx.2⟩

theorem const_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ constComponents d f U)
    {y : X} (hy : y ∈ f.func '' U) : componentFiber d f i y U = U := by
  obtain ⟨a, ha, rfl⟩ := hy
  ext x
  exact ⟨And.left, fun hx => ⟨hx, hi x hx a ha⟩⟩

theorem const_fiber_empty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ constComponents d f U)
    {y z : X} (hz : z ∈ f.func '' U) (hy : 0 < d i y z) :
    componentFiber d f i y U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh : d i (f.func x) z = 0 := by
    have hm : x ∈ componentFiber d f i z U := (const_fiber d f U hi hz).symm ▸ hx.1
    exact hm.2
  exact (ne_of_gt hy) (zero_trans (hd i).triangle
    (by rw [(hd i).symm]; exact hx.2) hh)

def pointRelation (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}
def zeroRelation (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}
def fiberPreorder (d : I → X → X → ENNReal) (U : Set X)
    (f g : Operator X bot) : Prop := zeroRelation d f U ⊆ zeroRelation d g U

theorem zeroRelation_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ zeroRelation d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRelation, mem_setOf_eq, hx, hy, true_and, fiber, sup_zero_iff]
  constructor <;> intro h i
  · intro _; rw [(hd i).symm]; exact h i
  · rw [(hd i).symm]; exact h i (mem_univ _)

theorem factor_surjective {S A B : Type} (a : S → A) (b : S → B)
    (hs : Function.Surjective a) :
    (∃ T : A → B, ∀ x, T (a x) = b x) ↔
      ∀ x y, a x = a y → b x = b y := by
  constructor
  · rintro ⟨T, hT⟩ x y hxy
    rw [← hT x, ← hT y, hxy]
  · intro h
    refine ⟨fun z => b (Classical.choose (hs z)), ?_⟩
    intro x
    exact h _ x (Classical.choose_spec (hs (a x)))

def imageInclusion (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, mem_image_of_mem _ x.2⟩
theorem imageInclusion_surjective (f : Operator X bot) (U : Set X) :
    Function.Surjective (imageInclusion f U) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem point_factor_iff (f g : Operator X bot) (U : Set X) :
    (∃ T : (f.func '' U) → X, ∀ x : U, T (imageInclusion f U x) = g.func x) ↔
      pointRelation f U ⊆ pointRelation g U := by
  rw [factor_surjective _ _ (imageInclusion_surjective f U)]
  constructor
  · intro h p hp
    exact ⟨hp.1, hp.2.1, h ⟨p.1, hp.1⟩ ⟨p.2, hp.2.1⟩ (Subtype.ext hp.2.2)⟩
  · intro h x y hxy
    exact (h (show (x.val,y.val) ∈ pointRelation f U from
      ⟨x.2, y.2, congrArg Subtype.val hxy⟩)).2.2

theorem point_factor_both_iff (f g : Operator X bot) (U : Set X) :
    ((∃ T : (f.func '' U) → X, ∀ x : U, T (imageInclusion f U x) = g.func x) ∧
     (∃ T : (g.func '' U) → X, ∀ x : U, T (imageInclusion g U x) = f.func x)) ↔
      pointRelation f U = pointRelation g U := by
  rw [point_factor_iff, point_factor_iff, subset_antisymm_iff]

def imageSetoid (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Setoid (f.func '' U) where
  r a b := GaugeZeroRelated d a.val b.val
  iseqv := by
    have h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun _ => h.refl _, fun hxy => h.symm hxy, fun hxy hyz => h.trans hxy hyz⟩
def imageQuotient (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid d hd f U)
def imageClass (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (x : U) : imageQuotient d hd f U := Quotient.mk _ (imageInclusion f U x)

theorem imageClass_surjective (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Function.Surjective (imageClass d hd f U) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    obtain ⟨x, rfl⟩ := imageInclusion_surjective f U a
    exact ⟨x, rfl⟩

theorem quotient_factor_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    (∃ T : imageQuotient d hd f U → imageQuotient d hd g U,
      ∀ x : U, T (imageClass d hd f U x) = imageClass d hd g U x) ↔
      zeroRelation d f U ⊆ zeroRelation d g U := by
  rw [factor_surjective _ _ (imageClass_surjective d hd f U)]
  constructor
  · intro h p hp
    exact ⟨hp.1, hp.2.1, Quotient.exact
      (h ⟨p.1, hp.1⟩ ⟨p.2, hp.2.1⟩ (Quotient.sound hp.2.2))⟩
  · intro h x y hxy
    exact Quotient.sound (h (show (x.val,y.val) ∈ zeroRelation d f U from
      ⟨x.2, y.2, Quotient.exact hxy⟩)).2.2

theorem quotient_factor_both_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    ((∃ T : imageQuotient d hd f U → imageQuotient d hd g U,
      ∀ x : U, T (imageClass d hd f U x) = imageClass d hd g U x) ∧
     (∃ T : imageQuotient d hd g U → imageQuotient d hd f U,
      ∀ x : U, T (imageClass d hd g U x) = imageClass d hd f U x)) ↔
      zeroRelation d f U = zeroRelation d g U := by
  rw [quotient_factor_iff, quotient_factor_iff, subset_antisymm_iff]

theorem separated_relations (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hs : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b) :
    pointRelation f U = zeroRelation d f U := by
  ext ⟨x,y⟩
  constructor
  · rintro ⟨hx, hy, he⟩
    exact ⟨hx, hy, fun i => by rw [he]; exact (hd i).dist_self _⟩
  · rintro ⟨hx, hy, he⟩
    exact ⟨hx, hy, hs _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy) he⟩

theorem fiber_preorder_refl (d : I → X → X → ENNReal) (U : Set X) (f : Operator X bot) :
    fiberPreorder d U f f := subset_rfl
theorem fiber_preorder_trans (d : I → X → X → ENNReal) (U : Set X)
    {f g h : Operator X bot} (hfg : fiberPreorder d U f g) (hgh : fiberPreorder d U g h) :
    fiberPreorder d U f h := hfg.trans hgh

theorem relation_chain {A : Type} (R : ℕ → Set A) {m : ℕ}
    (h : ∀ k < m, R k ⊆ R (k+1)) {a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) : R a ⊆ R b := by
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | @succ b hab ih => exact (ih (by omega)).trans (h b (by omega))

theorem relation_chain_strict {A : Type} (R : ℕ → Set A) {m r : ℕ}
    (h : ∀ k < m, R k ⊆ R (k+1)) (hr : r < m) (hs : R r ⊂ R (r+1)) :
    R 0 ⊂ R m ∧ ∃ p, p ∈ R m ∧ p ∉ R 0 := by
  obtain ⟨p, hp, hn⟩ := exists_of_ssubset hs
  have hp' := relation_chain R h (a := r+1) (b := m) (by omega) le_rfl hp
  have hn' : p ∉ R 0 := fun hh => hn (relation_chain R h (Nat.zero_le r) (by omega) hh)
  exact ⟨ssubset_iff_subset_ne.mpr ⟨relation_chain R h (Nat.zero_le m) le_rfl,
    fun he => hn' (he.symm ▸ hp')⟩, p, hp', hn'⟩

end
end Chapter3
```

```lean filename=Chapter3/Radius.lean
import Chapter3.Core

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
variable {X I : Type} {bot : X}

/-- Distance to the complement of the output zero class; see `radius_eq_sSup`. -/
def radius (din dout : X → X → ENNReal) (f : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  ⨅ x ∈ U, ⨅ (_ : dout (f.func x) (f.func y) ≠ 0), din x y
def admissible (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0
def uniformRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, radius din dout f y U
def nullMatrix (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (j i : I) : ENNReal := uniformRadius (d i) (d j) f U U

theorem le_radius_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) :
    r ≤ radius din dout f y U ↔ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0 := by
  classical
  constructor
  · intro h x hx hd
    by_contra hn
    have hh : radius din dout f y U ≤ din x y :=
      iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le hn le_rfl))
    exact (not_lt_of_ge (h.trans hh)) hd
  · intro h
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    apply le_iInf
    intro hn
    by_contra hh
    exact hn (h x hx (lt_of_not_ge hh))

theorem radius_rule (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) {x : X} (hx : x ∈ U)
    (h : din x y < radius din dout f y U) : dout (f.func x) (f.func y) = 0 :=
  (le_radius_iff din dout f y U _).mp le_rfl x hx h

theorem radius_eq_sSup (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) :
    radius din dout f y U = sSup {r | admissible din dout f y U r} := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hlt
    apply le_sSup
    exact ⟨by exact_mod_cast hr, ENNReal.coe_lt_top,
      (le_radius_iff din dout f y U _).mp (le_of_lt hlt)⟩
  · apply sSup_le
    intro r hr
    exact (le_radius_iff din dout f y U r).mpr hr.2.2

theorem extract_admissible (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) {a : ENNReal} (h : a < radius din dout f y U) :
    ∃ r, a < r ∧ admissible din dout f y U r := by
  obtain ⟨r, har, hrr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  exact ⟨r, har, (zero_le a).trans_lt har, ENNReal.coe_lt_top,
    (le_radius_iff din dout f y U _).mp hrr.le⟩

theorem admissible_le_radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) {r : ENNReal} (h : admissible din dout f y U r) :
    r ≤ radius din dout f y U ∧ 0 < r :=
  ⟨(le_radius_iff din dout f y U r).mpr h.2.2, h.1⟩

theorem uniform_le_point (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) {y : X} (hy : y ∈ A) :
    uniformRadius din dout f A U ≤ radius din dout f y U :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem uniform_rule (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ A)
    (h : din x y < uniformRadius din dout f A U) : dout (f.func x) (f.func y) = 0 :=
  radius_rule din dout f y U hx (h.trans_le (uniform_le_point din dout f A U hy))

theorem radius_top_of_const (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0)
    {y : X} (hy : y ∈ U) : radius din dout f y U = ⊤ := by
  apply top_unique
  exact (le_radius_iff din dout f y U ⊤).mpr (fun x hx _ => hc x hx y hy)

theorem uniform_top_of_const (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    uniformRadius din dout f U U = ⊤ := by
  apply top_unique
  exact le_iInf (fun y => le_iInf (fun hy => le_of_eq (radius_top_of_const din dout f U hc hy).symm))

theorem const_subfamily_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (hc : J ⊆ constComponents d f U) {y : X} (hy : y ∈ U) :
    fiber d f J (f.func y) U = U := by
  ext x
  exact ⟨And.left, fun hx => ⟨hx, (sup_zero_iff _ _ _ _).mpr (fun j hj => hc hj x hx y hy)⟩⟩

theorem const_subfamily_radii (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (hc : J ⊆ constComponents d f U) (i : I) :
    (∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f y U = ⊤) ∧
    uniformRadius (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  have h : ∀ x ∈ U, ∀ y ∈ U, subfamily_pseudometric d J (f.func x) (f.func y) = 0 :=
    fun x hx y hy => (sup_zero_iff _ _ _ _).mpr (fun j hj => hc hj x hx y hy)
  exact ⟨fun _ hy => radius_top_of_const _ _ _ _ h hy, uniform_top_of_const _ _ _ _ h⟩

theorem id_image_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ idComponents d f U) {y : X} (hy : y ∈ U) :
    componentFiber d f i (f.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  constructor <;> intro hx
  · exact ⟨hx.1, (id_isometry d hd f U hi x hx.1 y hy) ▸ hx.2⟩
  · exact ⟨hx.1, (id_isometry d hd f U hi x hx.1 y hy).symm ▸ hx.2⟩

theorem id_radius_lower (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ idComponents d f U) {y : X} (hy : y ∈ U)
    {r : ENNReal} (hr : 0 < r) (hfin : r < ⊤)
    (h : ball (d i) y r ∩ U ⊆ {x | x ∈ U ∧ d i x y = 0}) :
    r ≤ radius (d i) (d i) f y U ∧ 0 < r := by
  apply admissible_le_radius
  refine ⟨hr, hfin, ?_⟩
  intro x hx hxy
  rw [id_isometry d hd f U hi x hx y hy]
  exact (h ⟨hxy, hx⟩).2

theorem radius_subfamily (d : I → X → X → ENNReal) (din : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (y : X) :
    radius din (subfamily_pseudometric d J) f y U = ⨅ j ∈ J, radius din (d j) f y U := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    exact (sup_zero_iff _ _ _ _).mp (radius_rule _ _ _ _ _ hx hxy) j hj
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    apply (sup_zero_iff _ _ _ _).mpr
    intro j hj
    exact radius_rule _ _ _ _ _ hx (hxy.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_subfamily (d : I → X → X → ENNReal) (din : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) :
    uniformRadius din (subfamily_pseudometric d J) f U U =
      ⨅ j ∈ J, uniformRadius din (d j) f U U := by
  simp only [uniformRadius, radius_subfamily]
  apply le_antisymm
  · exact le_iInf (fun j => le_iInf (fun hj => le_iInf (fun y => le_iInf (fun hy =>
      iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))))))
  · exact le_iInf (fun y => le_iInf (fun hy => le_iInf (fun j => le_iInf (fun hj =>
      iInf_le_of_le j (iInf_le_of_le hj (iInf_le_of_le y (iInf_le_of_le hy le_rfl)))))))

theorem uniform_subfamily_antitone (d : I → X → X → ENNReal)
    (din : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    {J K : Set I} (h : J ⊆ K) :
    uniformRadius din (subfamily_pseudometric d K) f U U ≤
      uniformRadius din (subfamily_pseudometric d J) f U U := by
  rw [uniform_subfamily, uniform_subfamily]
  exact le_iInf (fun j => le_iInf (fun hj => iInf_le_of_le j (iInf_le_of_le (h hj) le_rfl)))

theorem fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (j : I) {y z : X} (h : z ∈ componentFiber d f j (f.func y) U) :
    d j (f.func y) (f.func z) = 0 := by
  rw [(hd j).symm]
  exact h.2

theorem radius_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (i j : I) {y z : X} (hz : z ∈ U)
    (h : d i y z < radius (d i) (d j) f y U) : d j (f.func y) (f.func z) = 0 := by
  rw [(hd j).symm]
  apply radius_rule (d i) (d j) f y U hz
  rwa [(hd i).symm]

theorem composite_fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot)
    (V : Set X) (j : I) {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hfx : f.func x ∈ V) (hfy : f.func y ∈ V)
    (h : f.func y ∈ componentFiber d g j (g.func (f.func x)) V) :
    d j ((g*f).func x) ((g*f).func y) = 0 :=
  fiber_truncation d hd g V j h

theorem radius_domain_antitone (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) (y : X) : radius din dout f y A ≤ radius din dout f y B := by
  apply (le_radius_iff _ _ _ _ _ _).mpr
  intro x hx hxy
  exact radius_rule _ _ _ _ _ (h hx) hxy

theorem uniform_domain_antitone (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) : uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (uniform_le_point _ _ _ _ _ (h hy)).trans (radius_domain_antitone din dout f h y)

theorem uniform_comp_zero (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X)
    (h : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, dmid a b = 0 → dout (g.func a) (g.func b) = 0) :
    uniformRadius din dmid f U U ≤ uniformRadius din dout (g*f) U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply (le_radius_iff _ _ _ _ _ _).mpr
  intro x hx hxy
  exact h _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
    (uniform_rule din dmid f U U hx hy hxy)

theorem uniform_comp_lip (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) {L : ENNReal} (hL : 0 < L) (hLf : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dmid (f.func x) (f.func y) ≤ L * din x y) :
    uniformRadius dmid dout g (f.func '' U) (f.func '' U) / L ≤
      uniformRadius din dout (g*f) U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply (le_radius_iff _ _ _ _ _ _).mpr
  intro x hx hxy
  exact uniform_rule dmid dout g _ _ (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
    ((h x hx y hy).trans_lt (ENNReal.mul_lt_of_lt_div' hxy))

theorem output_separation (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (h : 0 < dout (f.func x) (f.func y)) : uniformRadius din dout f A A ≤ din x y := by
  by_contra hh
  exact (ne_of_gt h) (uniform_rule din dout f A A hx hy (lt_of_not_ge hh))

theorem separation_witness (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {alpha tau : ENNReal} (ha : 0 < alpha) (haf : alpha < ⊤)
    (hlo : uniformRadius din dout f A A < alpha) (hhi : alpha < tau) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ eps : ENNReal,
      0 < eps ∧ eps < ⊤ ∧ din x y < alpha ∧ eps ≤ dout (f.func x) (f.func y) := by
  classical
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hlo
  obtain ⟨hyA, hyr⟩ := iInf_lt_iff.mp hy
  have hbad : ∃ x ∈ A, din x y < alpha ∧ dout (f.func x) (f.func y) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hle : alpha ≤ radius din dout f y A :=
      (le_radius_iff _ _ _ _ _ _).mpr (fun x hx hxy => hh x hx hxy)
    exact not_lt_of_ge hle hyr
  obtain ⟨x, hx, hxy, hout⟩ := hbad
  obtain ⟨eps, heps, hepsout⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hout)
  exact ⟨x, hx, y, hyA, eps, heps, ENNReal.coe_lt_top, hxy, hepsout.le⟩

def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal := ⨆ x ∈ A, ⨆ y ∈ A, d x y
structure InputScales (X I : Type) where
  scale : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.1 ⊆ B.1 → scale i A ≤ scale i B
def diameterScales (d : I → X → X → ENNReal) : InputScales X I where
  scale i A := diameter (d i) A.1
  mono i A B h := iSup_le (fun x => iSup_le (fun hx => iSup_le (fun y => iSup_le (fun hy =>
    le_iSup_of_le x (le_iSup_of_le (h hx) (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))))))
def thresholdType (sigma n ts tn : ENNReal) : Bool × Bool := (decide (sigma < ts), decide (tn ≤ n))

theorem threshold_four (sigma n ts tn : ENNReal) :
    (thresholdType sigma n ts tn = (true,true) ↔ sigma < ts ∧ tn ≤ n) ∧
    (thresholdType sigma n ts tn = (true,false) ↔ sigma < ts ∧ n < tn) ∧
    (thresholdType sigma n ts tn = (false,true) ↔ ts ≤ sigma ∧ tn ≤ n) ∧
    (thresholdType sigma n ts tn = (false,false) ↔ ts ≤ sigma ∧ n < tn) := by
  simp [thresholdType, Prod.ext_iff, not_lt, not_le]
theorem threshold_scale_mono {sigma ts ts' : ENNReal} (h : ts ≤ ts') :
    sigma < ts → sigma < ts' := fun hh => hh.trans_le h
theorem threshold_radius_antitone {n tn tn' : ENNReal} (h : tn ≤ tn') :
    tn' ≤ n → tn ≤ n := fun hh => h.trans hh
theorem scale_domain_mono (s : InputScales X I) (i : I)
    (A B : {A : Set X // A.Nonempty}) (h : B.1 ⊆ A.1) (tau : ENNReal) :
    s.scale i B ≤ s.scale i A ∧ (s.scale i A < tau → s.scale i B < tau) :=
  ⟨s.mono i B A h, fun hh => (s.mono i B A h).trans_lt hh⟩

theorem dist_le_diameter (d : X → X → ENNReal) {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

theorem small_domain_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {ts tn : ENNReal} (hs : diameter din A < ts) (hst : ts ≤ tn) :
    tn ≤ uniformRadius din dout f A A ↔ ∀ x ∈ A, ∀ y ∈ A, dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro hn x hx y hy
    exact uniform_rule din dout f A A hx hy
      ((dist_le_diameter din hx hy).trans_lt (hs.trans_le (hst.trans hn)))
  · intro h
    rw [uniform_top_of_const din dout f A h]
    exact le_top

theorem colip_point_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius (d i) (d j) f y U) := by
  rintro ⟨hxy, hr⟩
  exact (ne_of_gt hxy) (positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
    (radius_rule _ _ _ _ _ hx hr))

theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformRadius (d i) (d j) f U U ≤ d i x y := by
  by_cases hz : d i x y = 0
  · exact Or.inl hz
  · right
    by_contra hn
    exact colip_point_gap d f U K i j hK hpos hx hy
      ⟨pos_iff_ne_zero.mpr hz, (lt_of_not_ge hn).trans_le (uniform_le_point _ _ _ _ _ hy)⟩

end
end Chapter3
```

```lean filename=Chapter3/Entropy.lean
import Chapter3.Radius
import Mathlib.Data.EReal.Operations

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
variable {X I : Type} {bot : X}

def internallyTotallyBounded (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

theorem internal_cover_correspondence (d : X → X → ENNReal) (r : ENNReal)
    (U : Set X) (S : Finset X) :
    InternalEpsilonNet d r U S ↔ (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ (↑S : Set X), ball d c r := by
  simp [InternalEpsilonNet, ball, subset_def]

theorem covering_minimum (d : X → X → ENNReal) (r : ENNReal) (U : Set X) :
    (covering_number d r U = ⊤ ↔ ¬ ∃ S, InternalEpsilonNet d r U S) ∧
    ((∃ S, InternalEpsilonNet d r U S) → ∃ S, InternalEpsilonNet d r U S ∧
      covering_number d r U = (S.card : ENNReal) ∧
      ∀ T, InternalEpsilonNet d r U T → S.card ≤ T.card) :=
  ⟨covering_number_eq_top_iff d r U, covering_number_attained d r U⟩

theorem cover_push (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (delta eps : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, din x y < delta → dout (f x) (f y) < eps) :
    covering_number dout eps (f '' U) ≤ covering_number din delta U := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  have hnet : InternalEpsilonNet dout eps (f '' U) (S.image f) := by
    constructor
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact mem_image_of_mem _ (hS.1 hx)
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨c,hc,hd⟩ := hS.2 x hx
      exact ⟨f c, Finset.mem_image.mpr ⟨c,hc,rfl⟩, h x hx c (hS.1 hc) hd⟩
  calc
    covering_number dout eps (f '' U) ≤ ((S.image f).card : ENNReal) :=
      iInf_le_of_le (S.image f) (iInf_le_of_le hnet le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le

def preimagePoint (f : X → X) (U : Set X) (fallback : X) (z : X) : X :=
  by classical exact if h : z ∈ f '' U then Classical.choose h else fallback
theorem preimagePoint_spec (f : X → X) (U : Set X) (fallback : X) {z : X}
    (hz : z ∈ f '' U) : preimagePoint f U fallback z ∈ U ∧ f (preimagePoint f U fallback z) = z := by
  simp only [preimagePoint, dif_pos hz]
  exact Classical.choose_spec hz

theorem cover_pull (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (fallback : X) (delta eps : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) < eps → din x y < delta) :
    covering_number din delta U ≤ covering_number dout eps (f '' U) := by
  classical
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  let p := preimagePoint f U fallback
  have hp : ∀ t ∈ T, p t ∈ U ∧ f (p t) = t :=
    fun t ht => preimagePoint_spec f U fallback (hT.1 ht)
  have hnet : InternalEpsilonNet din delta U (T.image p) := by
    constructor
    · intro c hc
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc
      exact (hp t ht).1
    · intro x hx
      obtain ⟨t,ht,hclose⟩ := hT.2 (f x) (mem_image_of_mem _ hx)
      refine ⟨p t, Finset.mem_image.mpr ⟨t,ht,rfl⟩, h x hx _ (hp t ht).1 ?_⟩
      rwa [(hp t ht).2]
  calc
    covering_number din delta U ≤ ((T.image p).card : ENNReal) :=
      iInf_le_of_le (T.image p) (iInf_le_of_le hnet le_rfl)
    _ ≤ (T.card : ENNReal) := by exact_mod_cast Finset.card_image_le

theorem cover_image_isometry (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (fallback : X) (eps : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) = din x y) :
    covering_number dout eps (f '' U) = covering_number din eps U := by
  apply le_antisymm
  · apply cover_push
    intro x hx y hy hxy
    rwa [h x hx y hy]
  · apply cover_pull _ _ _ _ fallback
    intro x hx y hy hxy
    rwa [h x hx y hy] at hxy

theorem cover_one_of_zero (d : X → X → ENNReal) (U : Set X)
    (hne : U.Nonempty) {eps : ENNReal} (heps : 0 < eps)
    (hz : ∀ x ∈ U, ∀ y ∈ U, d x y = 0) : covering_number d eps U = 1 := by
  classical
  obtain ⟨c,hc⟩ := hne
  apply le_antisymm _ (one_le_covering_number_of_nonempty d eps U ⟨c,hc⟩)
  have hnet : InternalEpsilonNet d eps U {c} := by
    constructor
    · simpa using hc
    · intro x hx
      exact ⟨c, Finset.mem_singleton_self c, by rwa [hz x hx c hc]⟩
  exact iInf_le_of_le {c} (iInf_le_of_le hnet (by simp))

theorem threshold_fiber (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {tau : ENNReal} (h : tau ≤ uniformRadius din dout f A A)
    {y : X} (hy : y ∈ A) :
    ball din y tau ∩ A ⊆ {x | x ∈ A ∧ dout (f.func x) (f.func y) = 0} := by
  rintro x ⟨hxy,hx⟩
  exact ⟨hx, uniform_rule din dout f A A hx hy (hxy.trans_le h)⟩

theorem threshold_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {B : Set X} (hBA : B ⊆ A) {tau eps : ENNReal}
    (heps : 0 < eps) (hr : tau ≤ uniformRadius din dout f A A) :
    covering_number dout eps (f.func '' B) ≤ covering_number din tau B := by
  apply cover_push
  intro x hx y hy hxy
  rwa [uniform_rule din dout f A A (hBA hx) (hBA hy) (hxy.trans_le hr)]

theorem small_domain_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (hne : A.Nonempty) {ts tn eps : ENNReal}
    (hs : diameter din A < ts) (hst : ts ≤ tn)
    (hn : tn ≤ uniformRadius din dout f A A) (he : 0 < eps) :
    covering_number dout eps (f.func '' A) = 1 := by
  apply cover_one_of_zero _ _ (hne.image _) he
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact (small_domain_iff din dout f A hs hst).mp hn x hx y hy

theorem log2_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal,hb]
  have hb0 : b ≠ 0 := fun hz => ha (le_antisymm (hz ▸ hab) (zero_le _))
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
  simp only [log2_ereal, if_neg ha, if_neg hb0, if_neg hb, if_neg hat]
  exact EReal.coe_le_coe_iff.mpr (Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha hat) (ENNReal.toReal_mono hb hab))

@[simp] theorem log2_one : log2_ereal 1 = 0 := by
  norm_num [log2_ereal]

theorem threshold_entropy (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {B : Set X} (hBA : B ⊆ A) {tau eps : ENNReal}
    (heps : 0 < eps) (hr : tau ≤ uniformRadius din dout f A A) :
    metric_entropy dout eps (f.func '' B) ≤ metric_entropy din tau B :=
  log2_mono (threshold_cover din dout f A hBA heps hr)

theorem finite_cover (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hfin : U.Finite) {eps : ENNReal} (heps : 0 < eps) :
    covering_number d eps U < ⊤ := by
  classical
  have hnet : InternalEpsilonNet d eps U hfin.toFinset := by
    constructor
    · simp
    · intro x hx
      exact ⟨x, hfin.mem_toFinset.mpr hx, by rwa [hself]⟩
  exact (iInf_le_of_le hfin.toFinset (iInf_le_of_le hnet le_rfl)).trans_lt
    (ENNReal.natCast_lt_top _)

theorem entropy_finite (d : X → X → ENNReal) (eps : ENNReal) (U : Set X)
    (hne : U.Nonempty) (hfin : covering_number d eps U < ⊤) :
    ∃ r : ℝ, metric_entropy d eps U = (r : EReal) := by
  have hz : covering_number d eps U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty d eps U hne))
  exact ⟨Real.logb 2 (covering_number d eps U).toReal,
    by simp [metric_entropy,log2_ereal,hz,ne_of_lt hfin]⟩

def entropyDifferenceDefined (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ 0 < eps ∧ eps < ⊤ ∧
    (covering_number din eps U < ⊤ ∨ covering_number dout eps (f.func '' U) < ⊤)
def entropyDifference (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (_h : entropyDifferenceDefined din dout f eps U) : EReal :=
  metric_entropy din eps U - metric_entropy dout eps (f.func '' U)

theorem finite_entropy_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) (hdom : U ⊆ dom f) (hfin : U.Finite)
    (J K : Set I) {eps : ENNReal} (heps : 0 < eps) (hef : eps < ⊤) :
    entropyDifferenceDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U ∧
    (∃ r : ℝ, metric_entropy (subfamily_pseudometric d J) eps U = (r : EReal)) ∧
    (∃ r : ℝ, metric_entropy (subfamily_pseudometric d K) eps (f.func '' U) = (r : EReal)) := by
  have hself : ∀ H x, subfamily_pseudometric d H x x = 0 :=
    fun H x => (sup_zero_iff _ _ _ _).mpr (fun j _ => (hd j).dist_self x)
  have h1 := finite_cover _ (hself J) U hfin heps
  have h2 := finite_cover _ (hself K) (f.func '' U) (hfin.image f.func) heps
  exact ⟨⟨hne,hdom,heps,hef,Or.inl h1⟩, entropy_finite _ _ _ hne h1,
    entropy_finite _ _ _ (hne.image _) h2⟩

theorem constant_entropy (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) {j : I} (hj : j ∈ constComponents d f U)
    {eps : ENNReal} (he : 0 < eps) :
    covering_number (d j) eps (f.func '' U) = 1 ∧ metric_entropy (d j) eps (f.func '' U) = 0 := by
  have hc : covering_number (d j) eps (f.func '' U) = 1 :=
    cover_one_of_zero _ _ (hne.image _) he (by
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; exact hj x hx y hy)
  exact ⟨hc, by simp [metric_entropy,hc]⟩

theorem constant_difference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) {j : I} (hj : j ∈ constComponents d f U)
    {eps : ENNReal} (h : entropyDifferenceDefined (d j) (d j) f eps U) :
    entropyDifference (d j) (d j) f eps U h = metric_entropy (d j) eps U := by
  simp [entropyDifference, (constant_entropy d f U h.1 hj h.2.2.1).2]

theorem identity_entropy (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {j : I} (hj : j ∈ idComponents d f U) (eps : ENNReal) :
    covering_number (d j) eps (f.func '' U) = covering_number (d j) eps U ∧
    metric_entropy (d j) eps (f.func '' U) = metric_entropy (d j) eps U := by
  have hc := cover_image_isometry (d j) (d j) f.func U bot eps (id_isometry d hd f U hj)
  exact ⟨hc, congrArg log2_ereal hc⟩

theorem identity_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {j : I} (hj : j ∈ idComponents d f U) {eps : ENNReal}
    (h : entropyDifferenceDefined (d j) (d j) f eps U) :
    entropyDifference (d j) (d j) f eps U h = 0 := by
  have hc := (identity_entropy d hd f U hj eps).1
  have he := (identity_entropy d hd f U hj eps).2
  have hf : covering_number (d j) eps U < ⊤ :=
    h.2.2.2.2.elim id (fun hh => by rwa [hc] at hh)
  obtain ⟨r,hr⟩ := entropy_finite (d j) eps U h.1 hf
  simp [entropyDifference,he,hr]

theorem scalar_cover_lip (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    {L eps : ENNReal} (hL : 0 < L) (hLf : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) ≤ L * din x y) :
    covering_number dout eps (f '' U) ≤ covering_number din (eps/L) U := by
  apply cover_push
  intro x hx y hy hxy
  exact (h x hx y hy).trans_lt (ENNReal.mul_lt_of_lt_div' hxy)

theorem scalar_cover_colip (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (fallback : X) {K eps : ENNReal} (hK : 0 < K) (hKf : K < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, K * din x y ≤ dout (f x) (f y)) :
    covering_number din (eps/K) U ≤ covering_number dout eps (f '' U) := by
  apply cover_pull _ _ _ _ fallback
  intro x hx y hy hxy
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hK)) (Or.inl (ne_of_lt hKf))).mpr
  simpa [mul_comm] using (h x hx y hy).trans_lt hxy

theorem matrix_cover_colip [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (hf : K i j < ⊤) (eps : ENNReal) :
    covering_number (d i) (eps / K i j) U ≤ covering_number (d j) eps (f.func '' U) := by
  apply scalar_cover_colip _ _ _ _ bot hp hf
  intro x hx y hy
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (hK.2.2 x hx y hy j)

theorem lip_entropy_bound (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) (hdom : U ⊆ dom f)
    (htb : internallyTotallyBounded din U) {eps L : ENNReal}
    (he : 0 < eps) (hef : eps < ⊤) (hL : 0 < L) (hLf : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    ∃ hdef : entropyDifferenceDefined din dout f eps U,
      (∃ a : ℝ, metric_entropy din eps U = (a : EReal)) ∧
      (∃ b : ℝ, metric_entropy dout eps (f.func '' U) = (b : EReal)) ∧
      metric_entropy din eps U - metric_entropy din (eps/L) U ≤
        entropyDifference din dout f eps U hdef := by
  have hi := htb eps he hef
  have hs := htb (eps/L) (ENNReal.div_pos (ne_of_gt he) (ne_of_lt hLf))
    (lt_top_iff_ne_top.mpr (ENNReal.div_ne_top (ne_of_lt hef) (ne_of_gt hL)))
  have hc := scalar_cover_lip din dout f.func U (eps := eps) hL hLf h
  have ho := hc.trans_lt hs
  exact ⟨⟨hne,hdom,he,hef,Or.inl hi⟩, entropy_finite _ _ _ hne hi,
    entropy_finite _ _ _ (hne.image _) ho, EReal.sub_le_sub le_rfl (log2_mono hc)⟩

theorem colip_entropy_bound [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (hf : K i j < ⊤)
    (htb : internallyTotallyBounded (d i) U) {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    ∃ hdef : entropyDifferenceDefined (d i) (d j) f eps U,
      entropyDifference (d i) (d j) f eps U hdef ≤
        metric_entropy (d i) eps U - metric_entropy (d i) (eps/K i j) U := by
  exact ⟨⟨hK.1,hK.2.1,he,hef,Or.inl (htb eps he hef)⟩,
    EReal.sub_le_sub le_rfl (log2_mono (matrix_cover_colip d f U K i j hK hp hf eps))⟩

theorem factor_scalar_bound (d : X → X → ENNReal) (f g : Operator X bot) (U : Set X)
    (T : (f.func '' U) → X) (hT : ∀ x : U, T (imageInclusion f U x) = g.func x)
    {K L : ENNReal} (hK : 0 < K) (hKf : K < ⊤) (hLf : L < ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (f.func x) (f.func y))
    (hli : ∀ x ∈ U, ∀ y ∈ U, d (g.func x) (g.func y) ≤ L * d x y) :
    ∀ a b : f.func '' U, d (T a) (T b) ≤ (L/K) * d a b := by
  rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩
  rw [show T ⟨f.func x,mem_image_of_mem _ hx⟩ = g.func x from hT ⟨x,hx⟩,
      show T ⟨f.func y,mem_image_of_mem _ hy⟩ = g.func y from hT ⟨y,hy⟩]
  have hd : d x y ≤ d (f.func x) (f.func y) / K :=
    (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hK)) (Or.inl (ne_of_lt hKf))).mpr
      (by simpa [mul_comm] using hco x hx y hy)
  calc
    d (g.func x) (g.func y) ≤ L * d x y := hli x hx y hy
    _ ≤ L * (d (f.func x) (f.func y) / K) := mul_le_mul_left' hd L
    _ = (L/K) * d (f.func x) (f.func y) := by simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end
end Chapter3
```

```lean filename=Chapter3/Models.lean
import Chapter3.Entropy
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Powerset

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section

@[simp] theorem op_mul_apply {A : Type} {b : A} (f g : Operator A b) (x : A) :
    (g*f).func x = g.func (f.func x) := rfl
@[simp] theorem op_one_apply {A : Type} {b : A} (x : A) :
    (1 : Operator A b).func x = x := rfl

def pointedDist {A : Type} (d : A → A → ENNReal) : Option A → Option A → ENNReal
  | none, none => 0
  | some a, some b => d a b
  | _, _ => ⊤
def pointedOp {A : Type} (f : A → A) : Operator (Option A) none :=
  ⟨Option.map f, rfl⟩

theorem pointed_metric {A : Type} [Nonempty A] (d : A → A → ENNReal)
    (hs : ∀ x, d x x = 0) (hy : ∀ x y, d x y = d y x)
    (ht : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (pointedDist d) := by
  refine ⟨⟨some (Classical.arbitrary A), by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x; cases x <;> simp [pointedDist,hs]
  · intro x y; cases x <;> cases y <;> simp [pointedDist,hy]
  · intro x y z; cases x <;> cases y <;> cases z <;> simp [pointedDist,ht]
  · intro x hx; cases x <;> simp_all [pointedDist]

def realReadout (q : ℝ → ℝ) : Option ℝ → Option ℝ → ENNReal :=
  pointedDist (fun x y => edist (q x) (q y))
def realDistance := realReadout id
def absDistance := realReadout (fun x => |x|)

theorem realReadout_metric (q : ℝ → ℝ) :
    ExtendedPseudoMetric (Option ℝ) none (realReadout q) :=
  pointed_metric _ (fun _ => edist_self _) (fun _ _ => edist_comm _ _) (fun _ _ _ => edist_triangle _ _ _)
theorem realDistance_metric : ExtendedPseudoMetric (Option ℝ) none realDistance := realReadout_metric id
theorem absDistance_metric : ExtendedPseudoMetric (Option ℝ) none absDistance := realReadout_metric _

@[simp] theorem realReadout_some (q : ℝ → ℝ) (x y : ℝ) :
    realReadout q (some x) (some y) = ENNReal.ofReal |q x-q y| := by
  exact edist_dist _ _
@[simp] theorem realDistance_some (x y : ℝ) :
    realDistance (some x) (some y) = ENNReal.ofReal |x-y| := realReadout_some _ _ _
@[simp] theorem absDistance_some (x y : ℝ) :
    absDistance (some x) (some y) = ENNReal.ofReal (abs (abs x-abs y)) := realReadout_some _ _ _
@[simp] theorem pointedOp_some (f : ℝ → ℝ) (x : ℝ) :
    (pointedOp f).func (some x) = some (f x) := rfl
@[simp] theorem realDistance_zero (x y : ℝ) : realDistance (some x) (some y) = 0 ↔ x = y := by
  change edist x y = 0 ↔ x = y
  exact edist_eq_zero

theorem real_domain (f : ℝ → ℝ) : dom (pointedOp f) = range some := by
  ext x; cases x <;> simp [dom,pointedOp]

theorem diameter_pair (d : Option ℝ → Option ℝ → ENNReal)
    (hd : ExtendedPseudoMetric (Option ℝ) none d) (x y : ℝ) :
    diameter d ({some x, some y} : Set (Option ℝ)) = d (some x) (some y) := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    apply iSup_le
    intro b
    apply iSup_le
    intro hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [hd.dist_self,hd.symm]
  · exact dist_le_diameter d (by simp) (by simp)

theorem diameter_real_interval {a b : ℝ} (hab : a ≤ b) :
    diameter realDistance (some '' Icc a b) = ENNReal.ofReal (b-a) := by
  apply le_antisymm
  · apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨x,hx,rfl⟩
    apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨y,hy,rfl⟩
    rw [realDistance_some]
    apply ENNReal.ofReal_le_ofReal
    exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2], by linarith [hx.1,hx.2,hy.1,hy.2]⟩
  · have h := dist_le_diameter realDistance
      (mem_image_of_mem some (show a ∈ Icc a b from ⟨le_rfl,hab⟩))
      (mem_image_of_mem some (show b ∈ Icc a b from ⟨hab,le_rfl⟩))
    simpa [realDistance_some,abs_of_nonpos (sub_nonpos.mpr hab)] using h

theorem cover_finset_lower {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (S : Finset X) (n : ℕ)
    (h : ∀ T ∈ S.powerset, InternalEpsilonNet d eps (↑S) T → n ≤ T.card) :
    (n : ENNReal) ≤ covering_number d eps (↑S : Set X) := by
  classical
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  exact_mod_cast h T (Finset.mem_powerset.mpr (fun _ ht => hT.1 ht)) hT

theorem cover_le_net {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (U : Set X) (S : Finset X) (h : InternalEpsilonNet d eps U S) :
    covering_number d eps U ≤ (S.card : ENNReal) :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem cover_separated {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (S : Finset X) (he : 0 < eps) (hself : ∀ x, d x x = 0)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, d x y < eps → x=y) :
    covering_number d eps (↑S : Set X) = (S.card : ENNReal) := by
  classical
  apply le_antisymm
  · apply cover_le_net
    exact ⟨subset_rfl,fun x hx => ⟨x,hx,by rwa [hself]⟩⟩
  · apply le_iInf
    intro T
    apply le_iInf
    intro hT
    have hsub : S ⊆ T := by
      intro x hx
      obtain ⟨c,hc,hd⟩ := hT.2 x hx
      have hh := hsep x hx c (hT.1 hc) hd
      rwa [← hh] at hc
    exact_mod_cast Finset.card_le_card hsub

theorem cover_two_lower {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (U : Set X) (hne : U.Nonempty)
    (hfar : ∀ c ∈ U, ∃ x ∈ U, eps ≤ d x c) : (2 : ENNReal) ≤ covering_number d eps U := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  have hn : S.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨c,hc,_⟩ := hS.2 x hx
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hn
  obtain ⟨x,hx,hd⟩ := hfar c (hS.1 hc)
  obtain ⟨a,ha,hda⟩ := hS.2 x hx
  have hneac : a ≠ c := fun he => not_lt_of_ge hd (he ▸ hda)
  have hcard : 2 ≤ S.card := by
    have hsub : ({a,c} : Finset X) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z <;> assumption
    have hh := Finset.card_le_card hsub
    simpa [hneac] using hh
  exact_mod_cast hcard

theorem cover_pair {X : Type} (d : X → X → ENNReal)
    (hs : ∀ x, d x x = 0) (hy : ∀ x y, d x y = d y x)
    {a b : X} (hab : a ≠ b) {eps : ENNReal} (he : 0 < eps) :
    covering_number d eps ({a,b} : Set X) = if d a b < eps then 1 else 2 := by
  classical
  by_cases h : d a b < eps
  · rw [if_pos h]
    apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨a,by simp⟩)
    have hn : InternalEpsilonNet d eps ({a,b} : Set X) {a} := by
      refine ⟨by simp,?_⟩
      intro x hx
      rcases hx with hx | hx
      · subst x; exact ⟨a,by simp,by rwa [hs]⟩
      · subst x; exact ⟨a,by simp,by rwa [hy]⟩
    simpa using cover_le_net d eps ({a,b} : Set X) {a} hn
  · rw [if_neg h]
    apply le_antisymm
    · have hn : InternalEpsilonNet d eps ({a,b} : Set X) {a,b} := by
        refine ⟨by simp,fun x hx => ⟨x,by simpa using hx,by rwa [hs]⟩⟩
      simpa [hab] using cover_le_net d eps ({a,b} : Set X) {a,b} hn
    · apply cover_two_lower _ _ _ ⟨a,by simp⟩
      intro c hc
      rcases hc with hc | hc
      · subst c; exact ⟨b,by simp,by rw [hy]; exact le_of_not_gt h⟩
      · subst c; exact ⟨a,by simp,le_of_not_gt h⟩

def discreteReadout {A B : Type} (q : A → B) (x y : A) : ENNReal :=
  by classical exact if q x = q y then 0 else 1
theorem discreteReadout_metric {A B : Type} [Nonempty A] (q : A → B) :
    ExtendedPseudoMetric (Option A) none (pointedDist (discreteReadout q)) := by
  classical
  apply pointed_metric
  · intro x; simp [discreteReadout]
  · intro x y; simp [discreteReadout,eq_comm]
  · intro x y z
    by_cases hxy : q x = q y <;> by_cases hyz : q y = q z <;>
      by_cases hxz : q x = q z <;> simp_all [discreteReadout]

namespace Swap
abbrev X := Option Bool
def d : Unit → X → X → ENNReal := fun _ => pointedDist (discreteReadout id)
def U : Set X := {some false, some true}
def f : Operator X none := pointedOp Bool.not
theorem legal : ExtendedPseudoMetric X none (d ()) := discreteReadout_metric id
theorem image : f.func '' U = U := by
  ext x
  simp [U,f,pointedOp,Set.image_insert_eq,Set.image_singleton]
  tauto
theorem types :
    constComponents d f U = ∅ ∧ idComponents d f U = ∅ ∧ actComponents d f U = univ ∧
    idComponents d (f*f) U = univ ∧ actComponents d (f*f) U = ∅ := by
  have hc : constComponents d f U = ∅ := by
    ext i; cases i
    norm_num [constComponents,U,d,f,pointedOp,pointedDist,discreteReadout]
  have hi : idComponents d f U = ∅ := by
    ext i; cases i
    norm_num [idComponents,constComponents,U,d,f,pointedOp,pointedDist,discreteReadout]
  refine ⟨hc,hi,by simp [actComponents,hc,hi],?_,?_⟩
  · ext i; cases i
    norm_num [idComponents,constComponents,U,d,f,pointedOp,pointedDist,discreteReadout,
      operator_monoid,operator_compose]
  · ext i; cases i
    norm_num [actComponents,idComponents,constComponents,U,d,f,pointedOp,pointedDist,discreteReadout,
      operator_monoid,operator_compose]
theorem reverse_failures :
    ¬ (actComponents d f U ∪ actComponents d f (f.func '' U) ⊆ actComponents d (f*f) U) ∧
    ¬ (idComponents d (f*f) U ⊆ idComponents d f U ∩ idComponents d f (f.func '' U)) := by
  simp [image,types.1,types.2.1,types.2.2.1,types.2.2.2.1,types.2.2.2.2]
end Swap

namespace Inner
inductive A | a | b | p | q | r | s deriving DecidableEq, Fintype, Inhabited
open A
def read : A → A | q => p | x => x
def d (i : Bool) : Option A → Option A → ENNReal :=
  pointedDist (discreteReadout (if i then id else read))
def f : Operator (Option A) none := ⟨fun x => match x with
  | some a => some p | some b => some q | _ => none, rfl⟩
def g : Operator (Option A) none := ⟨fun x => match x with
  | some p => some r | some q => some s | _ => none, rfl⟩
def U : Set (Option A) := {some a,some b}
theorem legal : ∀ i, ExtendedPseudoMetric (Option A) none (d i) :=
  fun i => discreteReadout_metric _
theorem domain : U ⊆ dom (g*f) := by
  intro x hx
  rcases hx with rfl | rfl <;> simp [dom,g,f,operator_monoid,operator_compose]
theorem calculation :
    false ∈ constComponents d f U ∧ false ∉ constComponents d (g*f) U ∧
    d true (some p) (some q) = 1 ∧ d false (some r) (some s) = 1 := by
  norm_num [constComponents,U,d,f,g,pointedDist,discreteReadout,read,
    operator_monoid,operator_compose,show p ≠ q by decide,show r ≠ s by decide]
end Inner

namespace Infinite
def d (i : Bool) : Option Bool → Option Bool → ENNReal :=
  if i then pointedDist (discreteReadout id) else
    pointedDist (fun x y => if x = y then 0 else ⊤)
def U : Set (Option Bool) := Swap.U
theorem legal : ∀ i, ExtendedPseudoMetric (Option Bool) none (d i) := by
  intro i
  cases i
  · apply pointed_metric
    · intro x; simp
    · intro x y; simp [eq_comm]
    · intro x y z
      by_cases hxy : x=y <;> by_cases hyz : y=z <;> by_cases hxz : x=z <;> simp_all
  · exact discreteReadout_metric id
theorem radii (j : Bool) :
    uniformRadius (d false) (d j) (1 : Operator (Option Bool) none) U U = ⊤ ∧
    j ∉ constComponents d (1 : Operator (Option Bool) none) U := by
  constructor
  · apply top_unique
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      cases j <;> norm_num [d,pointedDist,discreteReadout] at *
  · intro hc
    have hh := hc (some false) (by simp [U,Swap.U]) (some true) (by simp [U,Swap.U])
    cases j <;> norm_num [d,pointedDist,discreteReadout] at hh
end Infinite

end
end Chapter3
```

```lean filename=Chapter3/Step.lean
import Chapter3.Models

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section

theorem uniform_zero_of_close (din dout : Option ℝ → Option ℝ → ENNReal)
    (f : Operator (Option ℝ) none) (U : Set (Option ℝ))
    (h : ∀ r : ℝ, 0 < r → ∃ x ∈ U, ∃ y ∈ U,
      din x y < ENNReal.ofReal r ∧ 0 < dout (f.func x) (f.func y)) :
    uniformRadius din dout f U U = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  obtain ⟨r,hr,hrn⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
  obtain ⟨x,hx,y,hy,hd,ho⟩ := h r (by exact_mod_cast hr)
  have hh := output_separation din dout f U hx hy ho
  have hrr : ENNReal.ofReal (r : ℝ) = (r : ENNReal) := ENNReal.ofReal_coe_nnreal
  exact not_lt_of_ge hh (hd.trans_le (by rw [hrr]; exact hrn.le))

namespace Step
def value (x : ℝ) : ℝ := if x < 0 then 0 else 1
def f := pointedOp value
def U : Set (Option ℝ) := some '' {y : ℝ | -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0}

theorem source_domain : U = some '' (Ico (-1 : ℝ) 0 ∪ Ioc 0 1) ∧ U ⊆ dom f := by
  constructor
  · apply congrArg (fun S : Set ℝ => some '' S)
    ext y
    simp only [mem_setOf_eq,mem_union,mem_Ico,mem_Ioc]
    constructor
    · rintro ⟨h1,h2,h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨h1,h⟩
      · exact Or.inr ⟨h,h2⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩) <;> exact ⟨by linarith,by linarith,by linarith⟩
  · rintro _ ⟨y,hy,rfl⟩
    simp [f,dom]

theorem opposite (y R : ℝ) (hy : -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0) (hR : |y| < R) :
    ∃ x : ℝ, (-1 ≤ x ∧ x ≤ 1 ∧ x ≠ 0) ∧ |x-y| < R ∧ value x ≠ value y := by
  let t := min (1/2 : ℝ) ((R-|y|)/2)
  have ht : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1/2 := min_le_left _ _
  have htR : t ≤ (R-|y|)/2 := min_le_right _ _
  by_cases hys : y < 0
  · refine ⟨t,⟨by linarith,by linarith,ne_of_gt ht⟩,?_,?_⟩
    · rw [abs_of_pos (by linarith : 0 < t-y)]
      rw [abs_of_neg hys] at htR
      linarith
    · simp [value,hys,not_lt_of_ge ht.le]
  · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hys) (Ne.symm hy.2.2)
    refine ⟨-t,⟨by linarith,by linarith,by linarith⟩,?_,?_⟩
    · rw [abs_of_neg (by linarith : -t-y < 0)]
      rw [abs_of_pos hyp] at htR
      linarith
    · simp [value,hys,show -t < 0 by linarith]

theorem point_radius {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0) :
    radius realDistance realDistance f (some y) U = ENNReal.ofReal |y| := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨R,hR,hRn⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hRy : |y| < (R : ℝ) := by
      rw [← ENNReal.ofReal_coe_nnreal] at hR
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg y)).mp hR
    obtain ⟨x,hx,hxy,hout⟩ := opposite y R hy hRy
    have hd : realDistance (some x) (some y) < radius realDistance realDistance f (some y) U := by
      rw [realDistance_some]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg y] : 0 < (R : ℝ))).mpr hxy |>.trans
        (by simpa using hRn)
    have hz := radius_rule realDistance realDistance f (some y) U (mem_image_of_mem _ hx) hd
    exact hout (realDistance_zero _ _ |>.mp hz)
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    rintro _ ⟨x,hx,rfl⟩ hxy
    have hay : 0 < |y| := abs_pos.mpr hy.2.2
    have hab : |x-y| < |y| :=
      (ENNReal.ofReal_lt_ofReal_iff hay).mp (by simpa using hxy)
    have hs : (x < 0) ↔ (y < 0) := by
      by_cases hys : y < 0
      · rw [abs_of_neg hys] at hab
        exact iff_of_true (by have hh := le_abs_self (x-y); linarith) hys
      · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hys) (Ne.symm hy.2.2)
        rw [abs_of_pos hyp] at hab
        exact iff_of_false (by have hh := neg_le_abs (x-y); linarith) hys
    simp [f,value,hs]

theorem admissible_exact {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0)
    {r : ENNReal} (hr : 0 < r) (hrf : r < ⊤) :
    admissible realDistance realDistance f (some y) U r ↔ r ≤ ENNReal.ofReal |y| := by
  rw [← point_radius hy,le_radius_iff]
  exact ⟨fun h => h.2.2,fun h => ⟨hr,hrf,h⟩⟩

theorem all_positive : ∀ y ∈ U, 0 < radius realDistance realDistance f y U := by
  rintro _ ⟨y,hy,rfl⟩
  rw [point_radius hy]
  exact ENNReal.ofReal_pos.mpr (abs_pos.mpr hy.2.2)

theorem uniform_zero : uniformRadius realDistance realDistance f U U = 0 := by
  apply uniform_zero_of_close
  intro r hr
  let a := min (1/2 : ℝ) (r/4)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have har : a ≤ r/4 := min_le_right _ _
  refine ⟨some (-a),mem_image_of_mem _ ⟨by linarith,by linarith,by linarith⟩,
    some a,mem_image_of_mem _ ⟨by linarith,by linarith,ne_of_gt ha⟩,?_,?_⟩
  · rw [realDistance_some]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    rw [abs_of_neg (by linarith : -a-a<0)]
    linarith
  · norm_num [f,value,show -a<0 by linarith,not_lt_of_ge ha.le]

theorem no_uniform_cover {tau : ENNReal} (ht : 0 < tau) (htf : tau < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < tau ∧
      ({some (-a),some a} : Set (Option ℝ)) ⊆ U ∧
      covering_number realDistance tau ({some (-a),some a} : Set (Option ℝ)) = 1 ∧
      covering_number realDistance (1/2) (f.func '' ({some (-a),some a} : Set (Option ℝ))) = 2 := by
  let a := min (1/2 : ℝ) (tau.toReal/4)
  have htr : 0 < tau.toReal := ENNReal.toReal_pos (ne_of_gt ht) (ne_of_lt htf)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have har : a ≤ tau.toReal/4 := min_le_right _ _
  have hclose : ENNReal.ofReal (2*a) < tau := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt htf)]
    apply (ENNReal.ofReal_lt_ofReal_iff htr).mpr
    linarith
  refine ⟨a,ha,by linarith,hclose,?_,?_,?_⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact mem_image_of_mem _ ⟨by linarith,by linarith,by linarith⟩
    · exact mem_image_of_mem _ ⟨by linarith,by linarith,ne_of_gt ha⟩
  · rw [cover_pair realDistance realDistance_metric.dist_self realDistance_metric.symm
      (by simp; linarith : some (-a) ≠ some a) ht]
    have hh : realDistance (some (-a)) (some a) < tau := by
      simpa [abs_of_neg (show -a-a<0 by linarith),show -(-a-a)=2*a by ring] using hclose
    rw [if_pos hh]
  · have himage : f.func '' ({some (-a),some a} : Set (Option ℝ)) = {some 0,some 1} := by
      simp [f,value,Set.image_insert_eq,Set.image_singleton,show -a<0 by linarith,not_lt_of_ge ha.le]
    rw [himage,cover_pair realDistance realDistance_metric.dist_self realDistance_metric.symm
      (by norm_num : some (0 : ℝ) ≠ some 1) (by norm_num)]
    norm_num
end Step

theorem reverse_scale_example :
    diameter realDistance ({some (0 : ℝ)} : Set (Option ℝ)) = 0 ∧
    diameter realDistance ({some (0 : ℝ),some 1} : Set (Option ℝ)) = 1 ∧
    ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ {some 0,some 1} ∧
    diameter realDistance ({some (0 : ℝ)} : Set (Option ℝ)) < 1/2 ∧
    1/2 ≤ diameter realDistance ({some (0 : ℝ),some 1} : Set (Option ℝ)) := by
  have h1 : diameter realDistance ({some (0 : ℝ)} : Set (Option ℝ)) = 0 := by
    simpa using diameter_pair realDistance realDistance_metric 0 0
  have h2 : diameter realDistance ({some (0 : ℝ),some 1} : Set (Option ℝ)) = 1 := by
    simpa using diameter_pair realDistance realDistance_metric 0 1
  norm_num [h1,h2]

end
end Chapter3
```

```lean filename=Chapter3/Floor.lean
import Chapter3.Step

namespace Chapter3.Floor
open Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section
def value (x : ℝ) : ℝ := (⌊x⌋ : ℤ)
def f := pointedOp value
def D1 : Set (Option ℝ) := some '' Icc (0 : ℝ) (1/2)
def D2 : Set (Option ℝ) := some '' Icc (9/10 : ℝ) (11/10)
def D3 : Set (Option ℝ) := {some 0,some 2}
def D4 : Set (Option ℝ) := some '' Icc (0 : ℝ) 2

theorem domains : D1 ⊆ dom f ∧ D2 ⊆ dom f ∧ D3 ⊆ dom f ∧ D4 ⊆ dom f := by
  have him : ∀ S : Set ℝ, some '' S ⊆ dom f := by
    intro S
    rintro _ ⟨x,hx,rfl⟩
    simp [f,dom]
  refine ⟨him _,him _,?_,him _⟩
  intro x hx
  rcases hx with rfl | rfl <;> simp [f,dom]

theorem diameters : diameter realDistance D1 = 1/2 ∧ diameter realDistance D2 = 1/5 ∧
    diameter realDistance D3 = 2 ∧ diameter realDistance D4 = 2 := by
  constructor
  · norm_num [D1,diameter_real_interval (by norm_num : (0 : ℝ) ≤ 1/2),ENNReal.ofReal_div_of_pos]
  constructor
  · norm_num [D2,diameter_real_interval (by norm_num : (9/10 : ℝ) ≤ 11/10),ENNReal.ofReal_div_of_pos]
  constructor
  · norm_num [D3,diameter_pair realDistance realDistance_metric]
  · norm_num [D4,diameter_real_interval (by norm_num : (0 : ℝ) ≤ 2)]

theorem first_radius : uniformRadius realDistance realDistance f D1 D1 = ⊤ := by
  apply uniform_top_of_const
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  have hfx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hx.1,by linarith [hx.2]⟩
  have hfy : ⌊y⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hy.1,by linarith [hy.2]⟩
  simp [f,value,hfx,hfy]

theorem jump {r : ℝ} (hr : 0 < r) :
    ∃ x : ℝ, 9/10 ≤ x ∧ x < 1 ∧ |x-1| < r ∧ value x = 0 := by
  let t := min (1/20 : ℝ) (r/2)
  have ht : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1/20 := min_le_left _ _
  have htr : t ≤ r/2 := min_le_right _ _
  refine ⟨1-t,by linarith,by linarith,?_,?_⟩
  · rw [abs_of_neg (by linarith : 1-t-1<0)]
    linarith
  · have hf : ⌊1-t⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
    simp [value,hf]

theorem second_radius : uniformRadius realDistance realDistance f D2 D2 = 0 := by
  apply uniform_zero_of_close
  intro r hr
  obtain ⟨x,hx,hx1,hxr,hfx⟩ := jump hr
  refine ⟨some x,mem_image_of_mem _ ⟨hx,by linarith⟩,
    some 1,mem_image_of_mem _ ⟨by norm_num,by norm_num⟩,?_,?_⟩
  · rw [realDistance_some]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hxr
  · simp only [f,pointedOp_some]
    rw [hfx]
    norm_num [value]

theorem third_radius : uniformRadius realDistance realDistance f D3 D3 = 2 := by
  simp only [uniformRadius,D3,iInf_pair,radius]
  norm_num [f,value]

theorem fourth_radius : uniformRadius realDistance realDistance f D4 D4 = 0 := by
  apply uniform_zero_of_close
  intro r hr
  obtain ⟨x,hx,hx1,hxr,hfx⟩ := jump hr
  refine ⟨some x,mem_image_of_mem _ ⟨by linarith,by linarith⟩,
    some 1,mem_image_of_mem _ ⟨by norm_num,by norm_num⟩,?_,?_⟩
  · rw [realDistance_some]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hxr
  · simp only [f,pointedOp_some]
    rw [hfx]
    norm_num [value]

theorem types :
    thresholdType (diameter realDistance D1) (uniformRadius realDistance realDistance f D1 D1) 1 1 = (true,true) ∧
    thresholdType (diameter realDistance D2) (uniformRadius realDistance realDistance f D2 D2) 1 1 = (true,false) ∧
    thresholdType (diameter realDistance D3) (uniformRadius realDistance realDistance f D3 D3) 1 1 = (false,true) ∧
    thresholdType (diameter realDistance D4) (uniformRadius realDistance realDistance f D4 D4) 1 1 = (false,false) := by
  norm_num [diameters.1,diameters.2.1,diameters.2.2.1,diameters.2.2.2,
    first_radius,second_radius,third_radius,fourth_radius,thresholdType]

theorem counterexample :
    (1 : ENNReal) ≤ uniformRadius realDistance realDistance f D3 D3 ∧
    ¬ (∀ x ∈ D3, ∀ y ∈ D3, realDistance (f.func x) (f.func y) = 0) ∧
    (∀ x ∈ D3, ∀ y ∈ D3, realDistance x y < 2 → x=y) := by
  refine ⟨by rw [third_radius]; norm_num,?_,?_⟩
  · intro h
    have hh := h (some 0) (by simp [D3]) (some 2) (by simp [D3])
    norm_num [f,value] at hh
  · intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num at *

end
end Chapter3.Floor
```

```lean filename=Chapter3/FiniteExercises.lean
import Chapter3.Models

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section

def componentPartition {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (f : Operator X bot) (i : I) (U : Set X) : Set (Set X) :=
  (fun x => componentFiber d f i (f.func x) U) '' U
theorem componentPartition_targets {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (f : Operator X bot) (i : I) (U : Set X) :
    componentPartition d f i U = (fun y => componentFiber d f i y U) '' (f.func '' U) := by
  simp [componentPartition,image_image]

namespace Affine
def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => absDistance
def f := pointedOp (fun x : ℝ => 2*x-1)
def U : Set (Option ℝ) := {some 0,some 1}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (d ()) ∧ U ⊆ dom f ∧ U ⊆ dom (f*f) := by
  refine ⟨absDistance_metric,?_,?_⟩ <;>
    intro x hx <;> rcases hx with rfl | rfl <;> simp [f,dom]
theorem fibers :
    componentFiber d f () (f.func (some 0)) U = U ∧
    componentFiber d (f*f) () ((f*f).func (some 0)) U = {some 0} := by
  constructor
  · ext x
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx,?_⟩
      rcases hx with rfl | rfl <;> norm_num [d,f]
  · ext x
    constructor
    · rintro ⟨hx,hd⟩
      rcases hx with rfl | rfl <;> norm_num [d,f] at *
    · intro hx
      rcases hx with rfl
      norm_num [componentFiber,U,d,f]
theorem types :
    constComponents d f U = univ ∧ idComponents d f U = ∅ ∧ actComponents d f U = ∅ ∧
    actComponents d (f*f) U = univ := by
  have hc : constComponents d f U = univ := by
    ext i; cases i
    norm_num [constComponents,U,d,f]
  refine ⟨hc,by simp [idComponents,hc],by simp [actComponents,idComponents,hc],?_⟩
  ext i; cases i
  norm_num [actComponents,idComponents,constComponents,U,d,f]

theorem same_value_square (g : Operator (Option ℝ) none) (c : ℝ)
    (h0 : g.func (some 0) = some c) (h1 : g.func (some 1) = some c) :
    (g*g).func (some 0) = (g*g).func (some 1) ∧
    absDistance ((g*g).func (some 0)) ((g*g).func (some 1)) = 0 ∧
    (U ⊆ dom (g*g) ↔ g.func (some c) ≠ none) := by
  have he : (g*g).func (some 0) = (g*g).func (some 1) := by simp [h0,h1]
  refine ⟨he,by rw [he]; exact absDistance_metric.dist_self _,?_⟩
  constructor
  · intro h
    simpa [dom,h0] using h (by simp [U] : some (0 : ℝ) ∈ U)
  · intro h x hx
    rcases hx with rfl | rfl <;> simpa [dom,h0,h1] using h
end Affine

namespace Translation
def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => absDistance
def f := pointedOp (fun x : ℝ => x+1)
def U : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
def V : Set (Option ℝ) := {some (-2),some (-1),some 1,some 3}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (d ()) ∧ U ⊆ dom f := by
  refine ⟨absDistance_metric,?_⟩
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [f,dom]
theorem image : f.func '' U = V := by
  norm_num [f,U,V,image_insert_eq,image_singleton]

theorem id_fibers :
    componentFiber d (1 : Operator (Option ℝ) none) () (some (-3)) U = {some (-3)} ∧
    componentFiber d (1 : Operator (Option ℝ) none) () (some (-2)) U = {some (-2),some 2} ∧
    componentFiber d (1 : Operator (Option ℝ) none) () (some 0) U = {some 0} ∧
    componentFiber d (1 : Operator (Option ℝ) none) () (some 2) U = {some (-2),some 2} := by
  repeat' constructor
  all_goals
    ext x
    constructor
    · rintro ⟨hx,hd⟩
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [d] at *
    · intro hx
      rcases hx with rfl | rfl <;> norm_num [componentFiber,U,d]

theorem translated_fibers :
    componentFiber d f () (f.func (some (-3))) U = {some (-3)} ∧
    componentFiber d f () (f.func (some (-2))) U = {some (-2),some 0} ∧
    componentFiber d f () (f.func (some 0)) U = {some (-2),some 0} ∧
    componentFiber d f () (f.func (some 2)) U = {some 2} := by
  repeat' constructor
  all_goals
    ext x
    constructor
    · rintro ⟨hx,hd⟩
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [d,f] at *
    · intro hx
      rcases hx with rfl | rfl <;> norm_num [componentFiber,U,d,f]

theorem partitions :
    componentPartition d (1 : Operator (Option ℝ) none) () U =
      {{some (-3)}, {some (-2),some 2}, {some 0}} ∧
    componentPartition d f () U = {{some (-3)}, {some (-2),some 0}, {some 2}} := by
  simp only [componentPartition,U,image_insert_eq,image_singleton,op_one_apply]
  rw [show ({some (-3),some (-2),some 0,some 2} : Set (Option ℝ)) = U from rfl]
  simp only [id_fibers.1,id_fibers.2.1,id_fibers.2.2.1,id_fibers.2.2.2,
    translated_fibers.1,translated_fibers.2.1,translated_fibers.2.2.1,translated_fibers.2.2.2]
  constructor <;> ext S <;> simp <;> tauto

theorem input_cover : covering_number absDistance (3/2) U = 2 := by
  classical
  apply le_antisymm
  · have hn : InternalEpsilonNet absDistance (3/2) U {some 0,some 2} := by
      norm_num [InternalEpsilonNet,U,Set.insert_subset_iff,ENNReal.lt_div_iff_mul_lt]
    simpa using cover_le_net _ _ _ _ hn
  · apply cover_two_lower _ _ _ ⟨some 0,by simp [U]⟩
    intro c hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by simp [U],by norm_num [ENNReal.div_le_iff]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ENNReal.div_le_iff]⟩
    · exact ⟨some 2,by simp [U],by norm_num [ENNReal.div_le_iff]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ENNReal.div_le_iff]⟩

theorem output_cover : covering_number absDistance (3/2) (f.func '' U) = 1 := by
  classical
  rw [image]
  apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some (-2),by simp [V]⟩)
  have hn : InternalEpsilonNet absDistance (3/2) V {some (-2)} := by
    norm_num [InternalEpsilonNet,V,Set.insert_subset_iff,ENNReal.lt_div_iff_mul_lt]
  simpa using cover_le_net _ _ _ _ hn

theorem entropy_difference :
    ∃ h : entropyDifferenceDefined absDistance absDistance f (3/2) U,
      entropyDifference absDistance absDistance f (3/2) U h = 1 := by
  have hd : entropyDifferenceDefined absDistance absDistance f (3/2) U :=
    ⟨⟨some 0,by simp [U]⟩,legal.2,ENNReal.div_pos (by norm_num) (by norm_num),
      by finiteness,Or.inr (by rw [output_cover]; norm_num)⟩
  refine ⟨hd,?_⟩
  norm_num [entropyDifference,metric_entropy,input_cover,output_cover,log2_ereal]
end Translation

end
end Chapter3
```

```lean filename=Chapter3/Rearrangement.lean
import Chapter3.Models

namespace Chapter3.Rearrangement
open Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
open scoped Classical
def U : Set (Option ℝ) := {some 0,some 1,some 2,some 3}
def f : Operator (Option ℝ) none := ⟨fun x =>
  if x ∈ U then x else none, by simp [U]⟩
def g : Operator (Option ℝ) none := ⟨fun x =>
  if x = some 0 then some 0 else if x = some 1 then some 3 else
  if x = some 2 then some 1 else if x = some 3 then some 2 else none, by simp⟩

theorem domain : U ⊆ dom f ∧ U ⊆ dom g := by
  constructor <;> intro x hx <;> rcases hx with rfl | rfl | rfl | rfl <;> simp [dom,f,g,U]
theorem outside : ∀ x ∉ U, f.func x = none ∧ g.func x = none := by
  intro x hx
  have hh : x ≠ some 0 ∧ x ≠ some 1 ∧ x ≠ some 2 ∧ x ≠ some 3 := by simpa [U] using hx
  simp [f,g,hx,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
theorem images : f.func '' U = U ∧ g.func '' U = U := by
  constructor
  · norm_num [f,U,image_insert_eq,image_singleton]
  · norm_num [g,U,image_insert_eq,image_singleton]
    ext x; simp; tauto

theorem covers {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    covering_number realDistance eps U = if eps ≤ 1 then 4 else if eps ≤ 2 then 2 else 1 := by
  classical
  by_cases h1 : eps ≤ 1
  · rw [if_pos h1]
    have hc := cover_separated realDistance eps ({some 0,some 1,some 2,some 3} : Finset (Option ℝ))
      he realDistance_metric.dist_self (by
        intro x hx y hy hxy
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl | rfl <;> norm_num at *
        all_goals exfalso; exact (not_lt_of_ge (h1.trans (by norm_num))) hxy)
    simpa [U] using hc
  · rw [if_neg h1]
    have he1 : (1 : ENNReal) < eps := lt_of_not_ge h1
    by_cases h2 : eps ≤ 2
    · rw [if_pos h2]
      apply le_antisymm
      · have hn : InternalEpsilonNet realDistance eps U {some 1,some 2} := by
          norm_num [InternalEpsilonNet,U,Set.insert_subset_iff,he1,he]
        simpa using cover_le_net _ _ _ _ hn
      · apply cover_two_lower _ _ _ ⟨some 0,by simp [U]⟩
        intro c hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact ⟨some 3,by simp [U],h2.trans (by norm_num)⟩
        · exact ⟨some 3,by simp [U],h2.trans (by norm_num)⟩
        · exact ⟨some 0,by simp [U],h2.trans (by norm_num)⟩
        · exact ⟨some 0,by simp [U],h2.trans (by norm_num)⟩
    · rw [if_neg h2]
      have he2 : (2 : ENNReal) < eps := lt_of_not_ge h2
      apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some 0,by simp [U]⟩)
      have hn : InternalEpsilonNet realDistance eps U {some 1} := by
        norm_num [InternalEpsilonNet,U,Set.insert_subset_iff,he1,he2,he]
      simpa using cover_le_net _ _ _ _ hn

theorem internal_center : some (3/2 : ℝ) ∉ U ∧
    ¬ InternalEpsilonNet realDistance (7/4) U {some (3/2)} ∧
    (∀ x ∈ U, realDistance x (some (3/2)) < 7/4) := by
  have hc : (7 : ENNReal)/4 = ENNReal.ofReal ((7 : ℝ)/4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  refine ⟨by norm_num [U],?_,?_⟩
  · norm_num [InternalEpsilonNet,U]
  · rw [hc]
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      norm_num [ENNReal.ofReal_lt_ofReal_iff]

theorem lip_constants :
    HasScalarLipBound (fun _ : Unit => realDistance) f U () () 1 ∧
    HasScalarLipBound (fun _ : Unit => realDistance) g U () () 3 ∧
    (∀ L, HasScalarLipBound (fun _ : Unit => realDistance) f U () () L → 1 ≤ L) ∧
    (∀ L, HasScalarLipBound (fun _ : Unit => realDistance) g U () () L → 3 ≤ L) := by
  refine ⟨⟨domain.1,?_⟩,⟨domain.2,?_⟩,?_,?_⟩
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [f,U]
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [g,U]
  · intro L h
    have hh := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    simpa [f,U] using hh
  · intro L h
    have hh := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    simpa [g,U] using hh

theorem equal_covers {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    covering_number realDistance eps (f.func '' U) = covering_number realDistance eps U ∧
    covering_number realDistance eps (g.func '' U) = covering_number realDistance eps U := by
  rw [images.1,images.2]
  exact ⟨rfl,rfl⟩

theorem differences {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    (∃ h : entropyDifferenceDefined realDistance realDistance f eps U,
      entropyDifference realDistance realDistance f eps U h = 0) ∧
    (∃ h : entropyDifferenceDefined realDistance realDistance g eps U,
      entropyDifference realDistance realDistance g eps U h = 0) := by
  have hne : U.Nonempty := ⟨some 0,by simp [U]⟩
  have hfin := finite_cover realDistance realDistance_metric.dist_self U (by simp [U]) he
  obtain ⟨r,hr⟩ := entropy_finite realDistance eps U hne hfin
  exact ⟨⟨⟨hne,domain.1,he,hef,Or.inl hfin⟩,by simp [entropyDifference,images.1,hr]⟩,
    ⟨⟨hne,domain.2,he,hef,Or.inl hfin⟩,by simp [entropyDifference,images.2,hr]⟩⟩

theorem bounds_at_seven_fourths :
    covering_number realDistance (7/4) (f.func '' U) = 2 ∧
    covering_number realDistance (7/4) (g.func '' U) = 2 ∧
    covering_number realDistance ((7/4)/1) U = 2 ∧
    covering_number realDistance ((7/4)/3) U = 4 ∧
    covering_number realDistance (7/4) (f.func '' U) ≤ covering_number realDistance ((7/4)/1) U ∧
    covering_number realDistance (7/4) (g.func '' U) ≤ covering_number realDistance ((7/4)/3) U := by
  have h1 : covering_number realDistance (7/4) U = 2 := by
    rw [covers (ENNReal.div_pos (by norm_num) (by norm_num)) (by finiteness)]
    norm_num [ENNReal.div_le_iff]
  have h3 : covering_number realDistance ((7/4)/3) U = 4 := by
    rw [covers (ENNReal.div_pos (ne_of_gt (ENNReal.div_pos (by norm_num) (by norm_num)))
      (by norm_num)) (by finiteness)]
    norm_num [ENNReal.div_le_iff]
  refine ⟨by simpa [images.1] using h1,by simpa [images.2] using h1,
    by simpa using h1,h3,?_,?_⟩
  · exact scalar_cover_lip realDistance realDistance f.func U (by norm_num) (by norm_num) lip_constants.1.2
  · exact scalar_cover_lip realDistance realDistance g.func U (by norm_num) (by norm_num) lip_constants.2.1.2

end
end Chapter3.Rearrangement
```

```lean filename=Chapter3/Correspondence.lean
import Chapter3.Floor
import Chapter3.FiniteExercises
import Chapter3.Rearrangement

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section
variable {X I : Type} {bot : X}

def actualSteps : List (Operator X bot) → Set X → List (Operator X bot × Set X)
  | [], _ => []
  | f::fs, U => (f,U) :: actualSteps fs (f.func '' U)
def finalImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | f::fs, U => finalImage fs (f.func '' U)
theorem run_image (fs : List (Operator X bot)) (U : Set X) : (run fs).func '' U = finalImage fs U := by
  induction fs generalizing U with
  | nil => change id '' U = U; simp
  | cons f fs ih => simpa [run,finalImage,image_image,Function.comp_def] using ih (f.func '' U)
theorem chainActs_union (d : I → X → X → ENNReal) (fs : List (Operator X bot)) (U : Set X) :
    chainActs d fs U = ⋃ p ∈ actualSteps fs U, actComponents d p.1 p.2 := by
  induction fs generalizing U with
  | nil => simp [actualSteps,chainActs]
  | cons f fs ih =>
    rw [chainActs,ih]
    ext i
    simp [actualSteps]

theorem finite_inf_attained {J : Set I} (hfin : J.Finite) (hne : J.Nonempty) (a : I → ENNReal) :
    ∃ j ∈ J, (⨅ k ∈ J, a k) = a j ∧ ∀ k ∈ J, a j ≤ a k := by
  obtain ⟨j,hj,hmin⟩ := Set.exists_min_image J a hfin hne
  exact ⟨j,hj,le_antisymm (iInf_le_of_le j (iInf_le_of_le hj le_rfl))
    (le_iInf (fun k => le_iInf (fun hk => hmin k hk))),hmin⟩
theorem finite_sup_attained {J : Set I} (hfin : J.Finite) (hne : J.Nonempty) (a : I → ENNReal) :
    ∃ j ∈ J, (⨆ k : J, a k.1) = a j ∧ ∀ k ∈ J, a k ≤ a j := by
  obtain ⟨j,hj,hmax⟩ := Set.exists_max_image J a hfin hne
  exact ⟨j,hj,le_antisymm (iSup_le (fun k => hmax k.1 k.2))
    (le_iSup (fun k : J => a k.1) ⟨j,hj⟩),hmax⟩

theorem subfamily_is_max [Fintype I] (d : I → X → X → ENNReal)
    (J : Set I) (hne : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subfamily_pseudometric d J x y = d j x y ∧ ∀ k ∈ J, d k x y ≤ d j x y :=
  finite_sup_attained (Set.toFinite J) hne (fun j => d j x y)

theorem fiber_partition (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (J : Set I) (U : Set X) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U ∧
    (∀ y ∈ f.func '' U, ∀ z ∈ f.func '' U,
      fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U)) :=
  ⟨fun _ hy => fiber_nonempty d hd f J U hy, fiber_cover d hd f J U,
    fun y _ z _ => fiber_equal_or_disjoint d hd f J y z U⟩
theorem point_minimum [Fintype I] (d : I → X → X → ENNReal) (din : X → X → ENNReal)
    (f : Operator X bot) (J : Set I) (hne : J.Nonempty) (y : X) (U : Set X) :
    ∃ j ∈ J, radius din (subfamily_pseudometric d J) f y U = radius din (d j) f y U ∧
      ∀ k ∈ J, radius din (d j) f y U ≤ radius din (d k) f y U := by
  rw [radius_subfamily]
  exact finite_inf_attained (Set.toFinite J) hne _
theorem uniform_minimum [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (J : Set I) (hne : J.Nonempty) (i : I) (U : Set X) :
    ∃ j ∈ J, uniformRadius (d i) (subfamily_pseudometric d J) f U U = nullMatrix d f U j i ∧
      ∀ k ∈ J, nullMatrix d f U j i ≤ nullMatrix d f U k i := by
  rw [uniform_subfamily]
  exact finite_inf_attained (Set.toFinite J) hne _

def channelType (s : InputScales X I) (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : {A : Set X // A.Nonempty}) (ts tn : ENNReal) (i j : I) : Bool × Bool :=
  thresholdType (s.scale i A) (nullMatrix d f A.1 j i) ts tn
theorem channelType_correspondence (s : InputScales X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (ts tn : ENNReal) (i j : I) :
    channelType s d f A ts tn i j =
      (decide (s.scale i A < ts), decide (tn ≤ uniformRadius (d i) (d j) f A.1 A.1)) := rfl
theorem threshold_exhaustive (s n ts tn : ENNReal) :
    thresholdType s n ts tn = (true,true) ∨ thresholdType s n ts tn = (true,false) ∨
    thresholdType s n ts tn = (false,true) ∨ thresholdType s n ts tn = (false,false) := by
  cases h : thresholdType s n ts tn with
  | mk a b => cases a <;> cases b <;> simp
theorem threshold_unique (s n ts tn : ENNReal) : ∃! p : Bool × Bool, thresholdType s n ts tn = p :=
  ⟨thresholdType s n ts tn,rfl,fun _ h => h.symm⟩

theorem scale_threshold_channels_mono (s : InputScales X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (tn : ENNReal)
    {ts ts' : ENNReal} (h : ts ≤ ts') :
    {p : I × I | (channelType s d f A ts tn p.1 p.2).1 = true} ⊆
      {p : I × I | (channelType s d f A ts' tn p.1 p.2).1 = true} := by
  intro p hp
  simp only [channelType,thresholdType,mem_setOf_eq,decide_eq_true_eq] at *
  exact hp.trans_le h
theorem null_threshold_channels_antitone (s : InputScales X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (ts : ENNReal)
    {tn tn' : ENNReal} (h : tn ≤ tn') :
    {p : I × I | (channelType s d f A ts tn' p.1 p.2).2 = true} ⊆
      {p : I × I | (channelType s d f A ts tn p.1 p.2).2 = true} := by
  intro p hp
  simp only [channelType,thresholdType,mem_setOf_eq,decide_eq_true_eq] at *
  exact h.trans hp

theorem separated_criteria (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (hf : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a=b)
    (hg : ∀ a ∈ g.func '' U, ∀ b ∈ g.func '' U, GaugeZeroRelated d a b → a=b) :
    (pointRelation f U ⊆ pointRelation g U ↔ zeroRelation d f U ⊆ zeroRelation d g U) ∧
    (pointRelation f U = pointRelation g U ↔ zeroRelation d f U = zeroRelation d g U) := by
  rw [separated_relations d hd f U hf,separated_relations d hd g U hg]
  exact ⟨Iff.rfl,Iff.rfl⟩

theorem fiber_chain (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) {m a b : ℕ}
    (h : ∀ k < m, fiberPreorder d U (f k) (f (k+1))) (hab : a ≤ b) (hbm : b ≤ m) :
    fiberPreorder d U (f a) (f b) := relation_chain (fun k => zeroRelation d (f k) U) h hab hbm
theorem fiber_chain_strict (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) {m r : ℕ}
    (h : ∀ k < m, fiberPreorder d U (f k) (f (k+1))) (hr : r < m)
    (hs : zeroRelation d (f r) U ⊂ zeroRelation d (f (r+1)) U) :
    zeroRelation d (f 0) U ⊂ zeroRelation d (f m) U ∧
      ∃ x y, (x,y) ∈ zeroRelation d (f m) U ∧ (x,y) ∉ zeroRelation d (f 0) U := by
  obtain ⟨hh,⟨x,y⟩,hp,hn⟩ := relation_chain_strict (fun k => zeroRelation d (f k) U) h hr hs
  exact ⟨hh,x,y,hp,hn⟩

theorem log2_top_iff (x : ENNReal) : log2_ereal x = ⊤ ↔ x = ⊤ := by
  by_cases hz : x=0
  · simp [hz,log2_ereal]
  by_cases ht : x=⊤ <;> simp [log2_ereal,hz,ht]

def subfamilyEntropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (J K : Set I) (_hJ : J.Nonempty) (_hK : K.Nonempty)
    (h : entropyDifferenceDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U) :
    EReal := entropyDifference (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U h
theorem subfamily_difference_correspondence (d : I → X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (J K : Set I) (hJ : J.Nonempty) (hK : K.Nonempty)
    (h : entropyDifferenceDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U) :
    subfamilyEntropyDifference d f eps U J K hJ hK h =
      subfamily_metric_entropy d J eps U - subfamily_metric_entropy d K eps (f.func '' U) := rfl
theorem difference_excludes_indeterminate (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U) :
    ¬ (metric_entropy din eps U = ⊤ ∧ metric_entropy dout eps (f.func '' U) = ⊤) := by
  rintro ⟨hi,ho⟩
  have hic := (log2_top_iff _).mp hi
  have hoc := (log2_top_iff _).mp ho
  rcases h.2.2.2.2 with hfin | hfin
  · exact (ne_of_lt hfin) hic
  · exact (ne_of_lt hfin) hoc
theorem difference_finite (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U)
    (hi : covering_number din eps U < ⊤) (ho : covering_number dout eps (f.func '' U) < ⊤) :
    ∃ r : ℝ, entropyDifference din dout f eps U h = (r : EReal) := by
  obtain ⟨a,ha⟩ := entropy_finite din eps U h.1 hi
  obtain ⟨b,hb⟩ := entropy_finite dout eps _ (h.1.image _) ho
  exact ⟨a-b,by simp [entropyDifference,ha,hb]⟩
theorem difference_top (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U)
    (hi : covering_number din eps U = ⊤) (ho : covering_number dout eps (f.func '' U) < ⊤) :
    entropyDifference din dout f eps U h = ⊤ := by
  obtain ⟨b,hb⟩ := entropy_finite dout eps _ (h.1.image _) ho
  have hh : metric_entropy din eps U = ⊤ := (log2_top_iff _).mpr hi
  simp [entropyDifference,hh,hb]
theorem difference_bot (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U)
    (hi : covering_number din eps U < ⊤) (ho : covering_number dout eps (f.func '' U) = ⊤) :
    entropyDifference din dout f eps U h = ⊥ := by
  obtain ⟨a,ha⟩ := entropy_finite din eps U h.1 hi
  have hh : metric_entropy dout eps (f.func '' U) = ⊤ := (log2_top_iff _).mpr ho
  simp [entropyDifference,hh,ha]

theorem constant_difference_exists (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) (hdom : U ⊆ dom f) {j : I}
    (hj : j ∈ constComponents d f U) {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    ∃ h : entropyDifferenceDefined (d j) (d j) f eps U,
      entropyDifference (d j) (d j) f eps U h = metric_entropy (d j) eps U := by
  have h : entropyDifferenceDefined (d j) (d j) f eps U :=
    ⟨hne,hdom,he,hef,Or.inr (by rw [(constant_entropy d f U hne hj he).1]; norm_num)⟩
  exact ⟨h,constant_difference d f U hj h⟩

theorem swap_domain : Swap.U ⊆ dom Swap.f ∧ Swap.U ⊆ dom (Swap.f*Swap.f) := by
  constructor <;> intro x hx <;> rcases hx with rfl | rfl <;> simp [Swap.f,pointedOp,dom]
theorem infinite_domain : Infinite.U.Nonempty ∧ Infinite.U ⊆ dom (1 : Operator (Option Bool) none) := by
  exact ⟨⟨some false,by simp [Infinite.U,Swap.U]⟩,by
    intro x hx; rcases hx with rfl | rfl <;> simp [dom]⟩
theorem reverse_scale_domain :
    ({some (0 : ℝ),some 1} : Set (Option ℝ)) ⊆ dom (1 : Operator (Option ℝ) none) := by
  intro x hx; rcases hx with rfl | rfl <;> simp [dom]

theorem pointwise_not_uniform_cover :
    (∀ y ∈ Step.U, 0 < radius realDistance realDistance Step.f y Step.U) ∧
    ∀ tau : ENNReal, 0 < tau → tau < ⊤ → ∃ B : Set (Option ℝ),
      B ⊆ Step.U ∧ B.Nonempty ∧ covering_number realDistance tau B = 1 ∧
        covering_number realDistance (1/2) (Step.f.func '' B) = 2 := by
  refine ⟨Step.all_positive,?_⟩
  intro tau ht htf
  obtain ⟨a,ha,ha1,hclose,hsub,hin,hout⟩ := Step.no_uniform_cover ht htf
  exact ⟨{some (-a),some a},hsub,⟨some a,by simp⟩,hin,hout⟩

theorem same_value_square_fibers (g : Operator (Option ℝ) none) (c : ℝ)
    (h0 : g.func (some 0) = some c) (h1 : g.func (some 1) = some c) (y : Option ℝ) :
    some 0 ∈ componentFiber Affine.d (g*g) () y Affine.U ↔
      some 1 ∈ componentFiber Affine.d (g*g) () y Affine.U := by
  have hh := (Affine.same_value_square g c h0 h1).1
  simp only [componentFiber,mem_setOf_eq]
  rw [hh]
  simp [Affine.U]

end
end Chapter3
```

```lean filename=Audit.lean
import Chapter3.Correspondence
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    let selected := (env.getModuleIdxFor? name).any fun idx =>
      (`Chapter3).isPrefixOf env.header.moduleNames[idx.toNat]!
    if selected then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {name}"
  logInfo m!"Audited {count} Chapter3 declarations: only propext, Classical.choice, Quot.sound."
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```python filename=build.py
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
os.chdir(root)
compiler = os.environ.get("LEAN", "/Users/g4i/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lean")
package_root = Path("/Users/g4i/lab/oet-dev/the-operator-evolution-theory/formal-oet/.lake/packages")
packages = ["Cli", "LeanSearchClient", "Qq", "aesop", "batteries", "importGraph",
            "mathlib", "plausible", "proofwidgets"]
lean_path = os.environ.get("LEAN_PATH", ":".join([str(root)] +
    [str(package_root / p / ".lake/build/lib/lean") for p in packages]))
version = subprocess.check_output([compiler, "--version"], text=True)
assert "4.29.1" in version and "f72c35b3" in version, version
build = root / ".build"
env = dict(os.environ, LEAN_PATH=str(build) + ":" + lean_path)
files = [
    "formal_oet/vol_01/ch_01_foundations/gauge_space.lean",
    "formal_oet/vol_01/ch_01_foundations/operator_space.lean",
    "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
    "formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean",
    "formal_oet/vol_01/ch_02_operator_bounds/decoupling.lean",
    "formal_oet/vol_01/ch_02_operator_bounds/single_channel.lean",
    "Chapter3/Core.lean", "Chapter3/Radius.lean", "Chapter3/Entropy.lean",
    "Chapter3/Models.lean", "Chapter3/Step.lean", "Chapter3/Floor.lean",
    "Chapter3/FiniteExercises.lean", "Chapter3/Rearrangement.lean",
    "Chapter3/Correspondence.lean", "Audit.lean", "Main.lean",
]
ledger = json.loads((root / "obligations.json").read_text())
alignment = json.loads((root / "alignment.json").read_text())
ids = [item["id"] for item in ledger["obligations"]]
actual = [item["id"] for item in alignment["items"]]
assert len(actual) == 92 and len(set(actual)) == 92 and set(actual) == set(ids)
assert alignment["case_id"] == "MG-C003" and alignment["version"] == "0.1.1"
for item in alignment["items"]:
    assert item["status"] == "complete" and item["representation"] and item["declarations"]
    assert set(item["dependencies"]) <= set(ids)
for file in files:
    target = build / Path(file).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    print("Checking", file, flush=True)
    subprocess.run([compiler, "-o", str(target), str(root / file)], env=env, check=True)
print("All modules compiled; 92 alignment entries checked.")
```

```json filename=alignment.json
{"case_id":"MG-C003","version":"0.1.1","items":[
{"id":"CH03-D01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.constComponents"},{"file":"Chapter3/Core.lean","name":"Chapter3.idComponents"},{"file":"Chapter3/Core.lean","name":"Chapter3.actComponents"},{"file":"Chapter3/Core.lean","name":"Chapter3.component_partition"}],"representation":"三集合逐字表示常值优先的常值、恒等、有效分量；证明覆盖指标集及互斥。","dependencies":[]},
{"id":"CH03-D02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber"},{"file":"Chapter3/Core.lean","name":"Chapter3.componentFiber"},{"file":"Chapter3/Core.lean","name":"Chapter3.sup_zero_iff"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_singleton"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.subfamily_is_max"}],"representation":"fiber使用冻结子族复合伪度量；证明零距等价于各分量同时零距及单元素子族对应。","dependencies":["CH03-D07"]},
{"id":"CH03-D03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.pointRelation"},{"file":"Chapter3/Core.lean","name":"Chapter3.zeroRelation"},{"file":"Chapter3/Core.lean","name":"Chapter3.imageSetoid"},{"file":"Chapter3/Core.lean","name":"Chapter3.imageQuotient"},{"file":"Chapter3/Core.lean","name":"Chapter3.imageClass"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiberPreorder"},{"file":"Chapter3/Core.lean","name":"Chapter3.zeroRelation_fiber"}],"representation":"关系包含公共域的两个成员条件；商是实际像集子类型的零距商，证明与全纤维对应。","dependencies":["CH03-D02","CH03-D07"]},
{"id":"CH03-D04","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius"},{"file":"Chapter3/Radius.lean","name":"Chapter3.admissible"},{"file":"Chapter3/Radius.lean","name":"Chapter3.le_radius_iff"},{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_eq_sSup"}],"representation":"以输出非零距点的输入距离下确界表示半径，证明等于全部有限正合法半径的上确界，含空集和无穷边界。","dependencies":[]},
{"id":"CH03-D05","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniformRadius"},{"file":"Chapter3/Radius.lean","name":"Chapter3.nullMatrix"},{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_le_point"}],"representation":"统一半径按基点集合取下确界；矩阵参数顺序为输出j、输入i，评估域和基点域分别保留。","dependencies":["CH03-D04"]},
{"id":"CH03-D06","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.channelType"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.channelType_correspondence"},{"file":"Chapter3/Radius.lean","name":"Chapter3.InputScales"},{"file":"Chapter3/Radius.lean","name":"Chapter3.diameter"},{"file":"Chapter3/Radius.lean","name":"Chapter3.diameterScales"},{"file":"Chapter3/Radius.lean","name":"Chapter3.thresholdType"}],"representation":"结合Radius.lean中的InputScales、diameterScales和thresholdType，将两个布尔位分别对应尺度严格阈值及统一半径非严格阈值。","dependencies":["CH03-D05"]},
{"id":"CH03-D07","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.internallyTotallyBounded"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.internal_cover_correspondence"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.covering_minimum"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.metric_entropy"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_pseudometric"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy_eq_metric_entropy"}],"representation":"直接使用冻结内部覆盖数及度量熵；证明内部球覆盖和最小中心数对应；全有界量化全部有限正精度。","dependencies":[]},
{"id":"CH03-D08","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.entropyDifferenceDefined"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.entropyDifference"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.subfamilyEntropyDifference"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.subfamily_difference_correspondence"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.difference_excludes_indeterminate"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.difference_finite"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.difference_top"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.difference_bot"}],"representation":"差值必须附带非空、定义域、有限正精度及至少一端覆盖数有限的证明；两端子族由复合伪度量代入。","dependencies":["CH03-D07","CH03-P22-01"]},
{"id":"CH03-P01-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_zero_row"}],"representation":"常值输出行的每个点对距离和零系数有限和均为零。","dependencies":["CH03-D01"]},
{"id":"CH03-P01-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_colip_zero"}],"representation":"对任意源分量，从指定正输入距离见证推出所有合法co-Lip证书的该条目为零。","dependencies":["CH03-D01"]},
{"id":"CH03-P01-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.id_isometry"}],"representation":"恒等分量逐点零距通过双向三角不等式给出全部受限点对的保距等式。","dependencies":["CH03-D01"]},
{"id":"CH03-P02-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.act_comp"}],"representation":"两步包含使用内侧实际像集，四种非有效分支均由常值或恒等结论排除有效性。","dependencies":["CH03-D01","CH03-P01-03","CH03-P02-03","CH03-P04-01"]},
{"id":"CH03-P02-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.run"},{"file":"Chapter3/Core.lean","name":"Chapter3.chainActs"},{"file":"Chapter3/Core.lean","name":"Chapter3.chainDomains"},{"file":"Chapter3/Core.lean","name":"Chapter3.chain_domains"},{"file":"Chapter3/Core.lean","name":"Chapter3.act_identity"},{"file":"Chapter3/Core.lean","name":"Chapter3.act_chain"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.actualSteps"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.finalImage"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.run_image"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.chainActs_union"}],"representation":"List按先头后尾执行，链域随实际像递推；包含空链基例及任意有限长度。","dependencies":["CH03-D01","CH03-P02-01"]},
{"id":"CH03-P02-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.id_comp"}],"representation":"证明逐点恒等零距，并以单步保距排除复合常值，保留常值优先约定。","dependencies":["CH03-D01","CH03-P01-03"]},
{"id":"CH03-P03-01","status":"complete","declarations":[{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.d"},{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.U"},{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.f"},{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.legal"},{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.image"},{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.types"},{"file":"Chapter3/Models.lean","name":"Chapter3.Swap.reverse_failures"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.swap_domain"}],"representation":"Option Bool精确表示吸收元加两点；计算换位、实际像域、两步有效和复合恒等，并同时否定两条逆向包含。","dependencies":["CH03-D01"]},
{"id":"CH03-P04-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.outer_const"}],"representation":"外侧在内侧实际像集常值时，直接代入像点得到复合常值。","dependencies":["CH03-D01"]},
{"id":"CH03-P04-02","status":"complete","declarations":[{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.A"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.d"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.f"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.g"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.U"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.legal"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.domain"},{"file":"Chapter3/Models.lean","name":"Chapter3.Inner.calculation"}],"representation":"六个非吸收点加none构成七点；false分量仅合并p,q，true分量离散；计算内侧常值而复合距离为1。","dependencies":["CH03-D01"]},
{"id":"CH03-P05-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_comp_diagonal"}],"representation":"调用冻结单输入行界，以同分量输入零距和ENNReal乘零证明结论，允许系数无穷。","dependencies":["CH03-D01"]},
{"id":"CH03-P06-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_target"}],"representation":"任意目标零距时，按各分量三角不等式双向证明纤维相等。","dependencies":["CH03-D02","CH03-D07"]},
{"id":"CH03-P06-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_nonempty"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_cover"}],"representation":"每个实际像目标有原像见证；纤维并集精确等于U，允许U为空。","dependencies":["CH03-D02","CH03-D07"]},
{"id":"CH03-P06-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_equal_or_disjoint"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.fiber_partition"}],"representation":"交点给出两个目标的子族零距，故纤维相等，否则不交；结合非空与覆盖得到去重分划。","dependencies":["CH03-D02","CH03-D07","CH03-P06-01","CH03-P06-02"]},
{"id":"CH03-P06-04","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_inter"}],"representation":"对非空J证明纤维等于全部单分量纤维的集合交。","dependencies":["CH03-D02","CH03-D07"]},
{"id":"CH03-P06-05","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_antitone"}],"representation":"J包含于K时，K的零距要求逐分量蕴含J要求。","dependencies":["CH03-D02","CH03-D07"]},
{"id":"CH03-P06-06","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_singleton"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_full_subset"}],"representation":"证明单元素子族等式及全指标子族向任意单分量的包含。","dependencies":["CH03-D02","CH03-D07","CH03-P06-05"]},
{"id":"CH03-P06-07","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.id_fiber"}],"representation":"恒等分量下，对任意目标证明输出纤维等于输入零距类。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P06-08","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.const_fiber"},{"file":"Chapter3/Core.lean","name":"Chapter3.const_fiber_empty"}],"representation":"常值分量在任一实际像目标的纤维为U；与该目标正分离的任意目标纤维为空。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P07-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.point_factor_iff"}],"representation":"存在定义在实际像集上的T并满足全部赋值公式，推出点值关系包含。","dependencies":["CH03-D03"]},
{"id":"CH03-P07-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.point_factor_iff"}],"representation":"利用满射代表元选择实际构造T并证明赋值独立于代表；源子类型为空的情况亦覆盖。","dependencies":["CH03-D03"]},
{"id":"CH03-P07-03","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.point_factor_both_iff"}],"representation":"双向应用实际像映射存在判据，并以双包含刻画关系相等。","dependencies":["CH03-D03","CH03-P07-01","CH03-P07-02"]},
{"id":"CH03-P07-04","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.factor_scalar_bound"}],"representation":"对实际像集任意两点选代表，有限正K的co-Lip与有限非负L的Lip推出L/K界。","dependencies":[]},
{"id":"CH03-P08-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.quotient_factor_iff"}],"representation":"实际像集零距商的满射类映射经通用因子化构造商映射；证明规定赋值与关系包含的充要条件。","dependencies":["CH03-D03"]},
{"id":"CH03-P08-02","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.quotient_factor_both_iff"}],"representation":"两个方向按输入诱导的商映射同时存在，当且仅当两零距点对集相等。","dependencies":["CH03-D03","CH03-P08-01"]},
{"id":"CH03-P08-03","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.separated_criteria"},{"file":"Chapter3/Core.lean","name":"Chapter3.separated_relations"}],"representation":"分别仅假设两个实际像集内部族分离，证明点值关系等于零距关系并改写单双向判据。","dependencies":["CH03-D03"]},
{"id":"CH03-P09-01","status":"complete","declarations":[{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_preorder_refl"},{"file":"Chapter3/Core.lean","name":"Chapter3.fiber_preorder_trans"}],"representation":"固定公共U时，零距关系包含给出纤维预序的自反性与传递性。","dependencies":["CH03-D03"]},
{"id":"CH03-P09-02","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.fiber_chain"}],"representation":"任意有限步数m及0≤a≤b≤m，逐步包含推出任意两层的关系包含。","dependencies":["CH03-D03"]},
{"id":"CH03-P09-03","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.fiber_chain_strict"}],"representation":"任一严格步骤传播到链端，显式给出属于末端关系而不属于首端关系的点对。","dependencies":["CH03-D03"]},
{"id":"CH03-P10-01","status":"complete","declarations":[{"file":"Chapter3/Step.lean","name":"Chapter3.Step.value"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.f"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.U"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.source_domain"},{"file":"Chapter3/Models.lean","name":"Chapter3.realDistance_metric"}],"representation":"Option实线隔离none；U证明等于[-1,0)并(0,1]，阶跃算子保持吸收元且U包含于其定义域。","dependencies":[]},
{"id":"CH03-P10-02","status":"complete","declarations":[{"file":"Chapter3/Step.lean","name":"Chapter3.Step.opposite"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.point_radius"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.admissible_exact"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.all_positive"}],"representation":"逐点构造异号近零见证，证明合法有限正半径恰为(0,|y|]，半径等于|y|且处处正。","dependencies":["CH03-D04","CH03-P10-01","CH03-P14-02"]},
{"id":"CH03-P10-03","status":"complete","declarations":[{"file":"Chapter3/Step.lean","name":"Chapter3.Step.uniform_zero"}],"representation":"在同一固定U中用任意小的异号点对证明统一半径为零。","dependencies":["CH03-D05","CH03-P10-01","CH03-P18-02"]},
{"id":"CH03-P11-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.const_subfamily_fiber"}],"representation":"J的每个输出分量均常值时，各基点实际像目标的整个J纤维等于U。","dependencies":["CH03-D01","CH03-D02","CH03-D07"]},
{"id":"CH03-P11-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_top_of_const"},{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_top_of_const"},{"file":"Chapter3/Radius.lean","name":"Chapter3.const_subfamily_radii"}],"representation":"所有有限正半径均合法，因而每点及统一半径为无穷；不假定域有无穷直径。","dependencies":["CH03-D01","CH03-D02","CH03-D04","CH03-D05","CH03-D07"]},
{"id":"CH03-P11-03","status":"complete","declarations":[{"file":"Chapter3/Models.lean","name":"Chapter3.Infinite.d"},{"file":"Chapter3/Models.lean","name":"Chapter3.Infinite.U"},{"file":"Chapter3/Models.lean","name":"Chapter3.Infinite.legal"},{"file":"Chapter3/Models.lean","name":"Chapter3.Infinite.radii"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.infinite_domain"}],"representation":"两点的输入距离为无穷；j=false覆盖i=j，j=true覆盖i≠j，两种输出均非常值而统一半径无穷。","dependencies":["CH03-D01","CH03-D04","CH03-D05","CH03-P03-01"]},
{"id":"CH03-P12-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.id_image_fiber"}],"representation":"以phi(y)为目标，受限点对保距将纤维精确化为y的输入零距类。","dependencies":["CH03-D01","CH03-D02","CH03-P01-03"]},
{"id":"CH03-P12-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.id_radius_lower"}],"representation":"有限正r0的输入零距球包含条件转为合法半径，从而半径≥r0>0。","dependencies":["CH03-D01","CH03-D04","CH03-P01-03"]},
{"id":"CH03-P13-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_subfamily"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.point_minimum"}],"representation":"点态半径等于全部单分量半径下确界；Correspondence.point_minimum在有限非空J上证明最小值取得。","dependencies":["CH03-D02","CH03-D04","CH03-D07","CH03-P14-02"]},
{"id":"CH03-P13-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_subfamily"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.uniform_minimum"}],"representation":"交换两个受限下确界得到统一半径公式；有限非空J上的最小条目由uniform_minimum取得。","dependencies":["CH03-D04","CH03-D05","CH03-D07","CH03-P13-01"]},
{"id":"CH03-P13-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_subfamily_antitone"}],"representation":"J包含于K时，对更多输出分量取下确界使统一半径不增。","dependencies":["CH03-D05","CH03-D07","CH03-P13-02"]},
{"id":"CH03-P14-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.fiber_truncation"}],"representation":"纤维成员定义加输出分量对称性推出规定方向的零距。","dependencies":["CH03-D02"]},
{"id":"CH03-P14-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_rule"},{"file":"Chapter3/Radius.lean","name":"Chapter3.extract_admissible"},{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_truncation"}],"representation":"严格小于半径时提取更大的有限正合法半径；证明对应输出零距，不扩展到等号边界。","dependencies":["CH03-D04"]},
{"id":"CH03-P14-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.composite_fiber_truncation"}],"representation":"保留两输入在上游定义域及两像点在指定下游域的条件，代入单步纤维判据。","dependencies":["CH03-D02","CH03-P14-01"]},
{"id":"CH03-P15-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_comp_zero"}],"representation":"下游仅在实际像域保持指定零距时，将上游统一零化尺度传给复合。","dependencies":["CH03-D04","CH03-D05","CH03-P18-01"]},
{"id":"CH03-P15-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_comp_lip"}],"representation":"保留有限正L及实际像域；ENNReal除法与严格阈值证明复合半径≥下游半径/L，含0及无穷。","dependencies":["CH03-D04","CH03-D05","CH03-P18-01"]},
{"id":"CH03-P16-01","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.threshold_exhaustive"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.threshold_unique"},{"file":"Chapter3/Radius.lean","name":"Chapter3.threshold_four"}],"representation":"Bool乘积的四种值穷尽且唯一；threshold_four逐一证明与四组互补不等式对应。","dependencies":["CH03-D06"]},
{"id":"CH03-P16-02","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.scale_threshold_channels_mono"}],"representation":"固定其余数据，尺度阈值增大时第一位为true的通道集按包含增大。","dependencies":["CH03-D06"]},
{"id":"CH03-P16-03","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.null_threshold_channels_antitone"}],"representation":"固定其余数据，零化阈值增大时第二位为true的通道集按包含缩小。","dependencies":["CH03-D05","CH03-D06"]},
{"id":"CH03-P17-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.scale_domain_mono"}],"representation":"任意满足原文单调公理的尺度函数在子域上不增，并保留严格阈值判断。","dependencies":["CH03-D06"]},
{"id":"CH03-P17-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.radius_domain_antitone"}],"representation":"评估域B包含于A时，固定基点的每个A合法尺度对B仍合法，点态半径不减。","dependencies":["CH03-D04","CH03-P14-02"]},
{"id":"CH03-P17-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_domain_antitone"}],"representation":"同时缩小评估域及下确界基点集合，证明B的统一半径不小于A的。","dependencies":["CH03-D04","CH03-D05","CH03-P17-02"]},
{"id":"CH03-P17-04","status":"complete","declarations":[{"file":"Chapter3/Step.lean","name":"Chapter3.reverse_scale_example"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.reverse_scale_domain"}],"representation":"通常实线A={0,1}、B={0}的直径分别为1和0，在1/2阈值否定反向判断。","dependencies":["CH03-D06","CH03-P10-01"]},
{"id":"CH03-P18-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.uniform_rule"}],"representation":"输入距离严格小于基点半径下确界时，利用该基点的点态判据使输出归零。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02"]},
{"id":"CH03-P18-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.output_separation"}],"representation":"取严格零化判据的逆否命题，输出正距离推出输入距离≥统一半径。","dependencies":["CH03-D05","CH03-P18-01"]},
{"id":"CH03-P18-03","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.separation_witness"}],"representation":"对每个规定的有限正alpha，取半径不足的基点和球内非零输出点，再提取有限正eps；输出为无穷亦覆盖。","dependencies":["CH03-D04","CH03-D05"]},
{"id":"CH03-P19-01","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.threshold_fiber"}],"representation":"统一半径≥阈值时，对每个中心证明开球与A之交包含于指定输出零距纤维。","dependencies":["CH03-D05","CH03-P18-01"]},
{"id":"CH03-P19-02","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.cover_push"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.threshold_cover"}],"representation":"将任意内部输入中心集映到输出内部中心集且基数不增；下确界证明含B空及无有限输入覆盖。","dependencies":["CH03-D05","CH03-D07","CH03-P18-01"]},
{"id":"CH03-P19-03","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.log2_mono"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.threshold_entropy"}],"representation":"证明冻结扩展对数单调，应用覆盖数界得到所需熵界，尤其覆盖非空B。","dependencies":["CH03-D05","CH03-D07","CH03-P19-02"]},
{"id":"CH03-P20-01","status":"complete","declarations":[{"file":"Chapter3/Correspondence.lean","name":"Chapter3.pointwise_not_uniform_cover"},{"file":"Chapter3/Step.lean","name":"Chapter3.Step.no_uniform_cover"}],"representation":"在同一阶跃U上同时保留处处正半径，并对任意有限正tau构造二点B使输入覆盖1而输出1/2覆盖2。","dependencies":["CH03-D04","CH03-D07","CH03-P10-01","CH03-P10-02"]},
{"id":"CH03-P21-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.small_domain_iff"}],"representation":"在直径严格小于ts且ts≤tn的条件下，统一半径≥tn当且仅当全部输出点对零距。","dependencies":["CH03-D05","CH03-D06","CH03-P11-02","CH03-P18-01"]},
{"id":"CH03-P21-02","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.small_domain_cover"}],"representation":"在同一条件下利用非空像集和内部单中心，证明任意有限正精度的覆盖数恰为1。","dependencies":["CH03-D05","CH03-D06","CH03-D07","CH03-P21-01"]},
{"id":"CH03-P22-01","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.finite_cover"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.entropy_finite"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.finite_entropy_difference"}],"representation":"有限非空U及其像以自身作内部中心；两端任意非空子族熵均为有限实数，差值前提成立。","dependencies":["CH03-D02","CH03-D07","CH03-D08"]},
{"id":"CH03-P23-01","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.constant_entropy"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.constant_difference"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.constant_difference_exists"}],"representation":"常值分量输出覆盖数1、熵0；差值等于输入熵，输入熵允许为无穷。","dependencies":["CH03-D01","CH03-D07","CH03-D08"]},
{"id":"CH03-P23-02","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.cover_pull"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.cover_image_isometry"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.identity_entropy"}],"representation":"恒等分量保距允许前向映中心及反向选择U内代表，两方向覆盖数及熵均相等。","dependencies":["CH03-D01","CH03-D07","CH03-P01-03","CH03-P19-02"]},
{"id":"CH03-P23-03","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.identity_difference"}],"representation":"仅在差值有定义前提下，两端相等迫使共同熵有限，继而差值为0。","dependencies":["CH03-D01","CH03-D07","CH03-D08","CH03-P22-01","CH03-P23-02"]},
{"id":"CH03-P24-01","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.scalar_cover_lip"}],"representation":"有限正L把eps/L的内部覆盖推到eps输出内部覆盖，中心像基数不增。","dependencies":["CH03-D07","CH03-P19-02"]},
{"id":"CH03-P24-02","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.lip_entropy_bound"}],"representation":"输入全有界使两个输入尺度及输出熵有限，证明差值良定并给出原文下界。","dependencies":["CH03-D07","CH03-D08","CH03-P19-03","CH03-P22-01","CH03-P24-01"]},
{"id":"CH03-P25-01","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.scalar_cover_colip"},{"file":"Chapter3/Entropy.lean","name":"Chapter3.matrix_cover_colip"}],"representation":"co-Lip矩阵单项控制输入距离，内部输出中心选U内原像得到eps/K输入覆盖，含无有限输出覆盖。","dependencies":["CH03-D07","CH03-P23-02"]},
{"id":"CH03-P25-02","status":"complete","declarations":[{"file":"Chapter3/Entropy.lean","name":"Chapter3.colip_entropy_bound"}],"representation":"输入全有界保证差值有定义；扩展实数减法反单调给上界，允许输出熵无穷。","dependencies":["CH03-D07","CH03-D08","CH03-P19-03","CH03-P25-01"]},
{"id":"CH03-P26-01","status":"complete","declarations":[{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.d"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.f"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.U"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.legal"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.fibers"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.types"}],"representation":"绝对值读数伪度量合法；phi(x)=2x-1在U={0,1}的目标phi(0)纤维为U，类型为常值。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P26-02","status":"complete","declarations":[{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.fibers"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.types"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.legal"}],"representation":"精确保留U，phi平方的目标phi平方(0)纤维为{0}，分量为有效；同时验证平方定义域条件。","dependencies":["CH03-D01","CH03-D02","CH03-P26-01"]},
{"id":"CH03-P26-03","status":"complete","declarations":[{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Affine.same_value_square"},{"file":"Chapter3/Correspondence.lean","name":"Chapter3.same_value_square_fibers"}],"representation":"U上两输出为同一实数c时平方输出仍相同；U包含于平方定义域当且仅当再次像不是吸收元。","dependencies":["CH03-D02","CH03-P26-01"]},
{"id":"CH03-P27-01","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.colip_point_gap"}],"representation":"正co-Lip通道反射输出零距，结合点态零化判据排除输入距离位于(0,rN)，无需K有限。","dependencies":["CH03-D04","CH03-P14-02"]},
{"id":"CH03-P27-02","status":"complete","declarations":[{"file":"Chapter3/Radius.lean","name":"Chapter3.colip_uniform_gap"}],"representation":"所有点对输入距离要么零，要么至少统一半径；原文正统一半径情形作为特例。","dependencies":["CH03-D04","CH03-D05","CH03-P27-01"]},
{"id":"CH03-P28-01","status":"complete","declarations":[{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.d"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.f"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.U"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.legal"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.id_fibers"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.translated_fibers"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.partitions"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.componentPartition"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.componentPartition_targets"}],"representation":"验证绝对值读数空间及平移域条件；完整列出恒等分划{-3},{-2,2},{0}和平移分划{-3},{-2,0},{2}。","dependencies":["CH03-D02"]},
{"id":"CH03-P28-02","status":"complete","declarations":[{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.input_cover"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.output_cover"},{"file":"Chapter3/FiniteExercises.lean","name":"Chapter3.Translation.entropy_difference"}],"representation":"精确3/2开球下内部覆盖数分别2、1，给出中心与下界，差值为1。","dependencies":["CH03-D07","CH03-D08","CH03-P28-01"]},
{"id":"CH03-P29-01","status":"complete","declarations":[{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.value"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.f"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.D1"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.domains"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.diameters"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.first_radius"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.types"}],"representation":"floor合法；D=[0,1/2]直径1/2、统一半径无穷，类型(true,true)。","dependencies":["CH03-D05","CH03-D06","CH03-P10-01","CH03-P11-02","CH03-P29-02","CH03-P29-03","CH03-P29-04"]},
{"id":"CH03-P29-02","status":"complete","declarations":[{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.D2"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.domains"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.diameters"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.second_radius"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.types"}],"representation":"D=[9/10,11/10]直径1/5；在1处构造任意近异值点证明统一半径0，类型(true,false)。","dependencies":["CH03-D05","CH03-D06","CH03-P10-01","CH03-P18-02","CH03-P29-01","CH03-P29-03","CH03-P29-04"]},
{"id":"CH03-P29-03","status":"complete","declarations":[{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.D3"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.domains"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.diameters"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.third_radius"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.types"}],"representation":"D={0,2}直径2、统一半径2；开球严格边界保留，类型(false,true)。","dependencies":["CH03-D04","CH03-D05","CH03-D06","CH03-P10-01","CH03-P29-01","CH03-P29-02","CH03-P29-04"]},
{"id":"CH03-P29-04","status":"complete","declarations":[{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.D4"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.domains"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.diameters"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.fourth_radius"},{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.types"}],"representation":"D=[0,2]直径2；在1处的左近点证明统一半径0，类型(false,false)。","dependencies":["CH03-D05","CH03-D06","CH03-P10-01","CH03-P18-02","CH03-P29-01","CH03-P29-02","CH03-P29-03"]},
{"id":"CH03-P29-05","status":"complete","declarations":[{"file":"Chapter3/Floor.lean","name":"Chapter3.Floor.counterexample"}],"representation":"D={0,2}的统一半径≥1但输出距离2非零；任意输入距离<2的点相等，说明正半径来自距离间隙。","dependencies":["CH03-D05","CH03-P29-01","CH03-P29-03"]},
{"id":"CH03-P30-01","status":"complete","declarations":[{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.U"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.covers"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.internal_center"}],"representation":"全部有限正eps分为eps≤1时4、1<eps≤2时2、eps>2时1；证明3/2虽然外覆盖可行却不是合法内部中心。","dependencies":["CH03-D07","CH03-P10-01"]},
{"id":"CH03-P30-02","status":"complete","declarations":[{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.f"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.g"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.domain"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.outside"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.images"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.equal_covers"},{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.differences"}],"representation":"两个部分算子均在U外取none，像集都为U，因此每个有限正精度覆盖数相同、两映射熵差均0。","dependencies":["CH03-D07","CH03-D08","CH03-P10-01","CH03-P22-01","CH03-P30-01"]},
{"id":"CH03-P30-03","status":"complete","declarations":[{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.lip_constants"}],"representation":"分别给出合法标量Lip常数1、3，并以0,1点对证明任意证书必须至少为1、3。","dependencies":["CH03-P30-01","CH03-P30-02"]},
{"id":"CH03-P30-04","status":"complete","declarations":[{"file":"Chapter3/Rearrangement.lean","name":"Chapter3.Rearrangement.bounds_at_seven_fourths"}],"representation":"eps=7/4时两真实覆盖均2；应用一般Lip推覆盖，f给2而g给4，并逐项比较。","dependencies":["CH03-D07","CH03-P24-01","CH03-P30-01","CH03-P30-02","CH03-P30-03"]}
]}
```