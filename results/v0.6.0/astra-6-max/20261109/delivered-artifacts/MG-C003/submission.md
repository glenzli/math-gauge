已在附件指定Lean 4.29.1、固定mathlib环境中编译Main.lean；359个自建声明的公理依赖审计通过。alignment.json恰含92个ID。冻结formal_oet模块作为外部输入保留，不复制或改写。

原数学内容：Zhe Li（Glen Li / glenzli），ORCID https://orcid.org/0009-0006-6536-3453，The Operator Evolution Theory，https://glenzli.com/books/oet/ ，CC BY 4.0 https://creativecommons.org/licenses/by/4.0/ 。本项目为新写Lean形式化。

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import Mathlib.Data.EReal.Operations


/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory, Volume I.
https://glenzli.com/books/oet/ ; https://creativecommons.org/licenses/by/4.0/
This is a new Lean formalization, not the author's implementation.
-/
namespace MG
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def Const (d : I → X → X → ENNReal) (f : X → X) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f x) (f y) = 0}
def Ident (d : I → X → X → ENNReal) (f : X → X) (U : Set X) : Set I :=
  {i | i ∉ Const d f U ∧ ∀ x ∈ U, d i (f x) x = 0}
def Active (d : I → X → X → ENNReal) (f : X → X) (U : Set X) : Set I :=
  (Const d f U ∪ Ident d f U)ᶜ

theorem component_partition (d : I → X → X → ENNReal) (f : X → X) (U : Set X) :
    Const d f U ∪ Ident d f U ∪ Active d f U = univ ∧
    Disjoint (Const d f U) (Ident d f U) ∧
    Disjoint (Const d f U) (Active d f U) ∧
    Disjoint (Ident d f U) (Active d f U) := by
  refine ⟨Set.union_compl_self _, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun _ hc hi => hi.1 hc)
  · exact Set.disjoint_left.mpr (fun _ hc ha => ha (Or.inl hc))
  · exact Set.disjoint_left.mpr (fun _ hi ha => ha (Or.inr hi))

theorem zero_transport {d : X → X → ENNReal}
    (hd : ExtendedPseudoMetric X bot d) {a b c e : X}
    (hab : d a b = 0) (hce : d c e = 0) : d a c = d b e := by
  apply le_antisymm
  · calc
      d a c ≤ d a b + d b c := hd.triangle _ _ _
      _ ≤ d a b + (d b e + d e c) := add_le_add le_rfl (hd.triangle _ _ _)
      _ = d b e := by rw [hab, hd.symm e c, hce]; simp
  · calc
      d b e ≤ d b a + d a e := hd.triangle _ _ _
      _ ≤ d b a + (d a c + d c e) := add_le_add le_rfl (hd.triangle _ _ _)
      _ = d a c := by rw [hd.symm b a, hab, hce]; simp

theorem zero_trans {d : X → X → ENNReal}
    (hd : ExtendedPseudoMetric X bot d) {a b c : X}
    (hab : d a b = 0) (hbc : d b c = 0) : d a c = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa [hab, hbc] using hd.triangle a b c

section Components
variable (d : I → X → X → ENNReal)
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
variable {f g : X → X} {U : Set X} {i : I}

theorem const_zero_row [Fintype I] (hi : i ∈ Const d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f x) (f y) ≤ ∑ k : I, 0 * d k x y := by
  intro x hx y hy; simp [hi x hx y hy]

theorem const_colip [Fintype I] {f : Operator X bot} {K : I → I → ENNReal}
    (hi : i ∈ Const d f.func U) (hK : IsCoLipMatrix d f U K)
    {k : I} (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hxy

include hd in
theorem ident_isometry (hi : i ∈ Ident d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f x) (f y) = d i x y := by
  intro x hx y hy
  exact zero_transport (hd i) (hi.2 x hx) (hi.2 y hy)

theorem outer_const (hi : i ∈ Const d g (f '' U)) :
    i ∈ Const d (g ∘ f) U := by
  intro x hx y hy
  exact hi _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

include hd in
theorem ident_comp (hf : i ∈ Ident d f U) (hg : i ∈ Ident d g (f '' U)) :
    i ∈ Ident d (g ∘ f) U := by
  constructor
  · intro hc; apply hf.1; intro x hx y hy
    rw [← ident_isometry d hd hg (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩]
    exact hc x hx y hy
  · intro x hx
    exact zero_trans (hd i) (hg.2 _ ⟨x, hx, rfl⟩) (hf.2 x hx)

include hd in
theorem active_comp : Active d (g ∘ f) U ⊆ Active d f U ∪ Active d g (f '' U) := by
  intro i hi
  by_contra hn
  have h : (i ∈ Const d f U ∨ i ∈ Ident d f U) ∧
      (i ∈ Const d g (f '' U) ∨ i ∈ Ident d g (f '' U)) := by
    change ¬ (_ ∨ _) at hn
    simp only [Active, mem_compl_iff, mem_union] at hn
    tauto
  apply hi
  rcases h with ⟨hf | hf, hg | hg⟩
  · exact Or.inl (outer_const d hg)
  · left; intro x hx y hy
    exact (ident_isometry d hd hg _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩).trans (hf x hx y hy)
  · exact Or.inl (outer_const d hg)
  · exact Or.inr (ident_comp d hd hf hg)

theorem inner_const_lip [Fintype I] {f g : Operator X bot} {L : I → I → ENNReal}
    (hf : i ∈ Const d f.func U) (hL : IsLipMatrix d g (f.func '' U) L)
    (hz : ∀ k, k ≠ i → L k i = 0) : i ∈ Const d (g.func ∘ f.func) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  simpa [hf x hx y hy] using lip_bound_of_single_input_row d g (f.func '' U) L i i
    hL hz _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩

def run : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => run fs * f
def stepActive (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => Active d f.func U ∪ stepActive d fs (f.func '' U)
def LegalChain : List (Operator X bot) → Set X → Prop
  | [], U => U ⊆ dom (1 : Operator X bot)
  | f :: fs, U => U ⊆ dom f ∧ LegalChain fs (f.func '' U)

theorem chain_domains (fs : List (Operator X bot)) (U : Set X)
    (h : U ⊆ dom (run fs)) : LegalChain fs U := by
  induction fs generalizing U with
  | nil => exact h
  | cons f fs ih =>
    constructor
    · intro x hx he
      apply h hx
      change (run fs).func (f.func x) = bot
      rw [he, (run fs).preserves_bot]
    · apply ih
      rintro z ⟨x,hx,rfl⟩
      exact h hx

include hd in
theorem active_chain (fs : List (Operator X bot)) (U : Set X) :
    Active d (run fs).func U ⊆ stepActive d fs U := by
  induction fs generalizing U with
  | nil =>
    intro i hi
    apply hi
    by_cases hc : i ∈ Const d id U
    · exact Or.inl hc
    · exact Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩
  | cons f fs ih =>
    intro i hi
    rcases active_comp d hd (f := f.func) (g := (run fs).func) hi with h | h
    · exact Or.inl h
    · exact Or.inr (ih _ h)
end Components

def Fiber (d : I → X → X → ENNReal) (f : X → X) (U : Set X)
    (J : Set I) (y : X) : Set X := {x | x ∈ U ∧ ∀ j ∈ J, d j (f x) y = 0}

theorem subfamily_zero (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  simp only [subfamily_pseudometric, ← nonpos_iff_eq_zero, iSup_le_iff, Subtype.forall]

theorem fiber_representation (d : I → X → X → ENNReal) (f : X → X)
    (U : Set X) (J : Set I) (y : X) :
    Fiber d f U J y = {x ∈ U | subfamily_pseudometric d J (f x) y = 0} := by
  ext x; simp [Fiber, subfamily_zero]

section Fibers
variable (d : I → X → X → ENNReal)
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
variable {f : X → X} {U : Set X} {J K : Set I} {y z : X}

include hd in
theorem fiber_target (hyz : ∀ j ∈ J, d j y z = 0) :
    Fiber d f U J y = Fiber d f U J z := by
  ext x; constructor
  · rintro ⟨hx,hh⟩; exact ⟨hx, fun j hj => zero_trans (hd j) (hh j hj) (hyz j hj)⟩
  · rintro ⟨hx,hh⟩
    exact ⟨hx, fun j hj => zero_trans (hd j) (hh j hj)
      (by rw [(hd j).symm]; exact hyz j hj)⟩

include hd in
theorem fiber_nonempty (hy : y ∈ f '' U) : (Fiber d f U J y).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hy
  exact ⟨x,hx,fun j _ => (hd j).dist_self _⟩

include hd in
theorem fiber_cover : (⋃ y ∈ f '' U, Fiber d f U J y) = U := by
  ext x; simp only [mem_iUnion]
  constructor
  · rintro ⟨y,_,hx,_⟩; exact hx
  · intro hx
    exact ⟨f x, ⟨x,hx,rfl⟩,hx,fun j _ => (hd j).dist_self _⟩

include hd in
theorem fiber_equal_or_disjoint :
    Fiber d f U J y = Fiber d f U J z ∨ Disjoint (Fiber d f U J y) (Fiber d f U J z) := by
  by_cases h : ∃ x, x ∈ Fiber d f U J y ∧ x ∈ Fiber d f U J z
  · obtain ⟨x,hx,hz⟩ := h
    left; apply fiber_target d hd
    intro j hj
    exact zero_trans (hd j) (by rw [(hd j).symm]; exact hx.2 j hj) (hz.2 j hj)
  · right; exact Set.disjoint_left.mpr (by aesop)

theorem fiber_inter (hJ : J.Nonempty) :
    Fiber d f U J y = ⋂ j ∈ J, Fiber d f U {j} y := by
  ext x; simp only [Fiber, mem_setOf_eq, mem_iInter, mem_singleton_iff,
    forall_eq]
  obtain ⟨j,hj⟩ := hJ
  constructor
  · rintro ⟨hx,h⟩ k hk; exact ⟨hx,h k hk⟩
  · intro h; exact ⟨(h j hj).1,fun k hk => (h k hk).2⟩

theorem fiber_antitone (h : J ⊆ K) : Fiber d f U K y ⊆ Fiber d f U J y :=
  fun _ hx => ⟨hx.1, fun j hj => hx.2 j (h hj)⟩

theorem fiber_singleton (i : I) : Fiber d f U {i} y = {x ∈ U | d i (f x) y = 0} := by
  ext x; simp [Fiber]

theorem fiber_full (i : I) : Fiber d f U univ y ⊆ Fiber d f U {i} y :=
  fiber_antitone d (subset_univ _)

include hd in
theorem fiber_ident {i : I} (hi : i ∈ Ident d f U) :
    Fiber d f U {i} y = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]; ext x
  constructor <;> rintro ⟨hx,hh⟩ <;> refine ⟨hx,?_⟩
  · rwa [zero_transport (hd i) (hi.2 x hx) ((hd i).dist_self y)] at hh
  · rwa [zero_transport (hd i) (hi.2 x hx) ((hd i).dist_self y)]

include hd in
theorem fiber_const {i : I} (hi : i ∈ Const d f U) (hz : z ∈ f '' U) :
    Fiber d f U {i} z = U ∧
    (0 < d i y z → Fiber d f U {i} y = ∅) := by
  obtain ⟨w,hw,rfl⟩ := hz
  constructor
  · ext x; simp only [fiber_singleton, mem_setOf_eq]
    exact ⟨And.left, fun hx => ⟨hx,hi x hx w hw⟩⟩
  · intro hp; apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hh⟩
    have he := zero_trans (hd i)
      (by rw [(hd i).symm]; exact hh i (mem_singleton i)) (hi x hx w hw)
    exact (ne_of_gt hp) he

theorem fiber_const_family (h : J ⊆ Const d f U) (hy : y ∈ U) :
    Fiber d f U J (f y) = U := by
  ext x; exact ⟨And.left, fun hx => ⟨hx, fun j hj => h hj x hx y hy⟩⟩

include hd in
theorem fiber_ident_image {i : I} (hi : i ∈ Ident d f U) (hy : y ∈ U) :
    Fiber d f U {i} (f y) = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]; ext x
  constructor <;> rintro ⟨hx,hh⟩ <;> refine ⟨hx,?_⟩
  · rwa [ident_isometry d hd hi x hx y hy] at hh
  · rwa [ident_isometry d hd hi x hx y hy]
end Fibers

def EqRel (f : X → X) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f p.1 = f p.2}
def ZeroRel (d : I → X → X → ENNReal) (f : X → X) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f p.1) (f p.2)}
def FiberLE (d : I → X → X → ENNReal) (U : Set X) (f g : X → X) : Prop :=
  ZeroRel d f U ⊆ ZeroRel d g U

theorem relation_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : X → X) (U : Set X)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ ZeroRel d f U ↔ y ∈ Fiber d f U univ (f x) := by
  simp only [ZeroRel, Fiber, mem_setOf_eq, hx, hy, true_and, mem_univ,
    forall_const, GaugeZeroRelated]
  constructor <;> intro h i <;> rw [(hd i).symm] <;> exact h i

theorem factor_surjective {A B C : Type} (f : A → B) (g : A → C)
    (hf : Function.Surjective f) :
    (∃ T : B → C, ∀ x, T (f x) = g x) ↔
      ∀ x y, f x = f y → g x = g y := by
  constructor
  · rintro ⟨T,hT⟩ x y h; rw [← hT x, ← hT y, h]
  · intro h
    classical
    let r : B → A := fun b => Classical.choose (hf b)
    have hr : ∀ b, f (r b) = b := fun b => Classical.choose_spec (hf b)
    exact ⟨g ∘ r, fun x => h _ x (hr (f x))⟩

def imageMap (f : X → X) (U : Set X) : U → (f '' U) :=
  fun x => ⟨f x, x, x.property, rfl⟩
theorem imageMap_surjective (f : X → X) (U : Set X) : Function.Surjective (imageMap f U) := by
  rintro ⟨z,x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
def Factors (f g : X → X) (U : Set X) : Prop :=
  ∃ T : (f '' U) → X, ∀ x : U, T (imageMap f U x) = g x

theorem factors_iff (f g : X → X) (U : Set X) : Factors f g U ↔ EqRel f U ⊆ EqRel g U := by
  rw [Factors, factor_surjective _ _ (imageMap_surjective f U)]
  constructor
  · intro h p hp
    exact ⟨hp.1,hp.2.1,h ⟨p.1,hp.1⟩ ⟨p.2,hp.2.1⟩ (Subtype.ext hp.2.2)⟩
  · intro h x y he
    exact (h (show (x.val,y.val) ∈ EqRel f U from ⟨x.property,y.property,congrArg Subtype.val he⟩)).2.2

theorem factors_both (f g : X → X) (U : Set X) :
    Factors f g U ∧ Factors g f U ↔ EqRel f U = EqRel g U := by
  rw [factors_iff, factors_iff]; exact le_antisymm_iff.symm

def imageSetoid (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : X → X) (U : Set X) : Setoid (f '' U) where
  r x y := GaugeZeroRelated d x.val y.val
  iseqv := by
    have h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun x => h.refl x.val, fun hxy => h.symm hxy, fun hxy hyz => h.trans hxy hyz⟩
def ImageQuotient (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : X → X) (U : Set X) :=
  Quotient (imageSetoid d hd f U)
def quotientMap (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : X → X) (U : Set X) :
    U → ImageQuotient d hd f U := fun x => Quotient.mk _ (imageMap f U x)
theorem quotientMap_surjective (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : X → X) (U : Set X) :
    Function.Surjective (quotientMap d hd f U) := by
  intro q
  induction q using Quotient.inductionOn with
  | h z =>
    obtain ⟨x,rfl⟩ := imageMap_surjective f U z
    exact ⟨x,rfl⟩
def QuotientFactors (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : X → X) (U : Set X) : Prop :=
  ∃ T : ImageQuotient d hd f U → ImageQuotient d hd g U,
    ∀ x, T (quotientMap d hd f U x) = quotientMap d hd g U x

theorem quotient_factors_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : X → X) (U : Set X) :
    QuotientFactors d hd f g U ↔ FiberLE d U f g := by
  rw [QuotientFactors, factor_surjective _ _ (quotientMap_surjective d hd f U)]
  constructor
  · intro h p hp
    refine ⟨hp.1,hp.2.1,?_⟩
    exact Quotient.exact (h ⟨p.1,hp.1⟩ ⟨p.2,hp.2.1⟩ (Quotient.sound hp.2.2))
  · intro h x y he
    exact Quotient.sound (h (show (x.val,y.val) ∈ ZeroRel d f U from ⟨x.property,y.property,Quotient.exact he⟩)).2.2

theorem quotient_factors_both (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : X → X) (U : Set X) :
    QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U ↔
      ZeroRel d f U = ZeroRel d g U := by
  rw [quotient_factors_iff, quotient_factors_iff, FiberLE, FiberLE]
  exact le_antisymm_iff.symm

theorem separated_relations (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : X → X) (U : Set X)
    (hs : ∀ x ∈ f '' U, ∀ y ∈ f '' U, GaugeZeroRelated d x y → x = y) :
    EqRel f U = ZeroRel d f U := by
  ext p; constructor
  · rintro ⟨hx,hy,he⟩
    exact ⟨hx,hy,fun i => by rw [he]; exact (hd i).dist_self _⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨hx,hy,hs _ ⟨_,hx,rfl⟩ _ ⟨_,hy,rfl⟩ he⟩

theorem fiberLE_refl (d : I → X → X → ENNReal) (U : Set X) (f : X → X) :
    FiberLE d U f f := Subset.rfl
theorem fiberLE_trans (d : I → X → X → ENNReal) (U : Set X) {f g h : X → X}
    (hfg : FiberLE d U f g) (hgh : FiberLE d U g h) : FiberLE d U f h := hfg.trans hgh

theorem relation_chain {A : Type} (R : ℕ → Set A) {m : ℕ}
    (h : ∀ k < m, R k ⊆ R (k+1)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : R a ⊆ R b := by
  induction b, hab using Nat.le_induction with
  | base => exact Subset.rfl
  | succ b hab ih => exact (ih (by omega)).trans (h b (by omega))

theorem relation_chain_strict {A : Type} (R : ℕ → Set A) {m r : ℕ}
    (h : ∀ k < m, R k ⊆ R (k+1)) (hr : r < m) (hs : R r ⊂ R (r+1)) :
    R 0 ⊂ R m ∧ ∃ z, z ∈ R m ∧ z ∉ R 0 := by
  obtain ⟨z,hz,hn⟩ := Set.exists_of_ssubset hs
  have hz' := relation_chain R h (by omega : r+1 ≤ m) le_rfl hz
  have hn' : z ∉ R 0 := fun hz0 => hn (relation_chain R h (Nat.zero_le r) (by omega) hz0)
  exact ⟨⟨relation_chain R h (Nat.zero_le m) le_rfl, fun hm => hn' (hm hz')⟩,z,hz',hn'⟩
end MG

namespace MG
open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
variable {X I : Type} {bot : X}

noncomputable def radius (a b : X → X → ENNReal) (f : X → X) (U : Set X) (y : X) : ENNReal :=
  ⨅ x ∈ U, ⨅ (_ : b (f x) (f y) ≠ 0), a x y
def LegalRadius (a b : X → X → ENNReal) (f : X → X) (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, a x y < r → b (f x) (f y) = 0
noncomputable def uniform (a b : X → X → ENNReal) (f : X → X) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, radius a b f U y
noncomputable def nullMatrix (d : I → X → X → ENNReal) (f : X → X) (U : Set X) : I → I → ENNReal :=
  fun j i => uniform (d i) (d j) f U U

theorem le_radius_iff {a b : X → X → ENNReal} {f : X → X} {U : Set X} {y : X} {r : ENNReal} :
    r ≤ radius a b f U y ↔ ∀ x ∈ U, b (f x) (f y) ≠ 0 → r ≤ a x y := by
  simp only [radius, le_iInf_iff]
theorem le_radius_zero {a b : X → X → ENNReal} {f : X → X} {U : Set X} {y : X} {r : ENNReal} :
    r ≤ radius a b f U y ↔ ∀ x ∈ U, a x y < r → b (f x) (f y) = 0 := by
  rw [le_radius_iff]; constructor
  · intro h x hx hlt
    by_contra hn
    exact (not_lt_of_ge (h x hx hn)) hlt
  · intro h x hx hn
    exact le_of_not_gt (fun hlt => hn (h x hx hlt))
theorem radius_zero {a b : X → X → ENNReal} {f : X → X} {U : Set X} {x y : X}
    (hx : x ∈ U) (h : a x y < radius a b f U y) : b (f x) (f y) = 0 :=
  le_radius_zero.mp le_rfl x hx h
theorem legal_radius_iff {a b : X → X → ENNReal} {f : X → X} {U : Set X} {y : X} {r : ENNReal} :
    LegalRadius a b f U y r ↔ 0 < r ∧ r < ⊤ ∧ r ≤ radius a b f U y := by
  rw [LegalRadius, le_radius_zero]

theorem radius_sup (a b : X → X → ENNReal) (f : X → X) (U : Set X) (y : X) :
    radius a b f U y = sSup {r | LegalRadius a b f U y r} := by
  apply le_antisymm
  · apply le_of_not_gt; intro h
    obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hm : (r : ENNReal) ∈ {r | LegalRadius a b f U y r} :=
      legal_radius_iff.mpr ⟨lt_of_le_of_lt (zero_le _) hr, ENNReal.coe_lt_top, hr'.le⟩
    exact (not_lt_of_ge (le_sSup hm)) hr
  · apply sSup_le; intro r hr
    exact (legal_radius_iff.mp hr).2.2

theorem legal_ball (a b : X → X → ENNReal) (f : X → X) (U : Set X) (y : X) (r : ENNReal) :
    LegalRadius a b f U y r ↔ 0 < r ∧ r < ⊤ ∧
      ball a y r ∩ U ⊆ {x ∈ U | b (f x) (f y) = 0} := by
  simp only [LegalRadius, ball, Set.subset_def, mem_inter_iff, mem_setOf_eq]
  aesop

theorem extract_legal_radius {a b : X → X → ENNReal} {f : X → X} {U : Set X} {y : X} {t : ENNReal}
    (h : t < radius a b f U y) : ∃ r, LegalRadius a b f U y r ∧ t < r := by
  obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  exact ⟨r,legal_radius_iff.mpr ⟨lt_of_le_of_lt (zero_le _) hr,ENNReal.coe_lt_top,hr'.le⟩,hr⟩

theorem uniform_le_point {a b : X → X → ENNReal} {f : X → X} {A U : Set X} {y : X}
    (hy : y ∈ A) : uniform a b f A U ≤ radius a b f U y :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)
theorem uniform_zero {a b : X → X → ENNReal} {f : X → X} {A U : Set X} {x y : X}
    (hx : x ∈ U) (hy : y ∈ A) (h : a x y < uniform a b f A U) : b (f x) (f y) = 0 :=
  radius_zero hx (h.trans_le (uniform_le_point hy))
theorem le_uniform_zero {a b : X → X → ENNReal} {f : X → X} {A U : Set X} {r : ENNReal} :
    r ≤ uniform a b f A U ↔ ∀ y ∈ A, ∀ x ∈ U, a x y < r → b (f x) (f y) = 0 := by
  simp only [uniform, le_iInf_iff, le_radius_zero]

theorem radius_top {a b : X → X → ENNReal} {f : X → X} {U : Set X} {y : X}
    (h : ∀ x ∈ U, b (f x) (f y) = 0) : radius a b f U y = ⊤ := by
  apply top_unique; exact le_radius_zero.mpr (fun x hx _ => h x hx)
theorem uniform_top {a b : X → X → ENNReal} {f : X → X} {U : Set X}
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) = 0) : uniform a b f U U = ⊤ := by
  apply top_unique; exact le_uniform_zero.mpr (fun y hy x hx _ => h x hx y hy)

theorem const_family_radius (d : I → X → X → ENNReal) (f : X → X) (U : Set X) (J : Set I)
    (h : J ⊆ Const d f U) (i : I) :
    (∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f U y = ⊤) ∧
    uniform (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  have hz : ∀ x ∈ U, ∀ y ∈ U, subfamily_pseudometric d J (f x) (f y) = 0 :=
    fun x hx y hy => (subfamily_zero d J _ _).mpr (fun j hj => h hj x hx y hy)
  exact ⟨fun y hy => radius_top (fun x hx => hz x hx y hy),uniform_top hz⟩

theorem ident_radius_lower (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : X → X} {U : Set X} {y : X} {i : I}
    (hi : i ∈ Ident d f U) (hy : y ∈ U) {r : ENNReal} (hr : 0 < r) (hrt : r < ⊤)
    (hb : ball (d i) y r ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r ≤ radius (d i) (d i) f U y ∧ 0 < r := by
  refine ⟨le_radius_zero.mpr ?_,hr⟩
  intro x hx hxy
  rw [ident_isometry d hd hi x hx y hy]
  exact (hb ⟨hxy,hx⟩).2

theorem radius_family (a : X → X → ENNReal) (d : I → X → X → ENNReal)
    (f : X → X) (U : Set X) (J : Set I) (y : X) :
    radius a (subfamily_pseudometric d J) f U y = ⨅ j ∈ J, radius a (d j) f U y := by
  apply le_antisymm
  · refine le_iInf (fun j => le_iInf (fun hj => le_radius_zero.mpr ?_))
    intro x hx hxy
    exact (subfamily_zero d J _ _).mp (radius_zero hx hxy) j hj
  · apply le_radius_zero.mpr
    intro x hx hxy
    apply (subfamily_zero d J _ _).mpr
    intro j hj
    exact radius_zero hx (hxy.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_family (a : X → X → ENNReal) (d : I → X → X → ENNReal)
    (f : X → X) (A U : Set X) (J : Set I) :
    uniform a (subfamily_pseudometric d J) f A U = ⨅ j ∈ J, uniform a (d j) f A U := by
  apply le_antisymm
  · refine le_iInf (fun j => le_iInf (fun hj => le_uniform_zero.mpr ?_))
    intro y hy x hx hxy
    exact (subfamily_zero d J _ _).mp (uniform_zero hx hy hxy) j hj
  · apply le_uniform_zero.mpr
    intro y hy x hx hxy
    apply (subfamily_zero d J _ _).mpr
    intro j hj
    exact uniform_zero hx hy (hxy.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_family_antitone (a : X → X → ENNReal) (d : I → X → X → ENNReal)
    (f : X → X) (A U : Set X) {J K : Set I} (h : J ⊆ K) :
    uniform a (subfamily_pseudometric d K) f A U ≤ uniform a (subfamily_pseudometric d J) f A U := by
  rw [uniform_family,uniform_family]
  exact le_iInf (fun j => le_iInf (fun hj => iInf_le_of_le j (iInf_le_of_le (h hj) le_rfl)))

theorem fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : X → X} {U : Set X} {y z : X} {i j : I}
    (hy : y ∈ U) (hz : z ∈ U)
    (h : z ∈ Fiber d f U {j} (f y) ∨ d i y z < radius (d i) (d j) f U y) :
    d j (f y) (f z) = 0 := by
  rw [(hd j).symm]
  rcases h with h | h
  · exact h.2 j (mem_singleton j)
  · apply radius_zero (a := d i) hz
    rwa [(hd i).symm]

theorem composite_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f g : Operator X bot}
    {U : Set X} {x y : X} {j : I} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hfx : f.func x ∈ U) (hfy : f.func y ∈ U)
    (hf : f.func y ∈ Fiber d g.func U {j} (g.func (f.func x))) :
    d j ((g*f).func x) ((g*f).func y) = 0 := by
  rw [(hd j).symm]; exact hf.2 j (mem_singleton j)

theorem uniform_comp_zero {a b c : X → X → ENNReal} {f g : X → X} {U : Set X}
    (h : ∀ y ∈ f '' U, ∀ z ∈ f '' U, b y z = 0 → c (g y) (g z) = 0) :
    uniform a b f U U ≤ uniform a c (g ∘ f) U U := by
  apply le_uniform_zero.mpr
  intro y hy x hx hxy
  exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (uniform_zero hx hy hxy)

theorem uniform_comp_lip {a b c : X → X → ENNReal} {f g : X → X} {U : Set X}
    {L : ENNReal} (hL : 0 < L) (hLt : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) ≤ L * a x y) :
    uniform b c g (f '' U) (f '' U) / L ≤ uniform a c (g ∘ f) U U := by
  apply le_uniform_zero.mpr
  intro y hy x hx hxy
  have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hL.ne') (Or.inl hLt.ne)).mp hxy
  exact uniform_zero (a := b) (b := c) (f := g) (A := f '' U) (U := f '' U)
    ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩ ((h x hx y hy).trans_lt (by simpa [mul_comm] using hmul))

theorem radius_restrict {a b : X → X → ENNReal} {f : X → X} {A B : Set X} {y : X}
    (h : B ⊆ A) : radius a b f A y ≤ radius a b f B y :=
  le_radius_zero.mpr (fun _ hx hxy => radius_zero (h hx) hxy)
theorem uniform_restrict {a b : X → X → ENNReal} {f : X → X} {A B : Set X}
    (h : B ⊆ A) : uniform a b f A A ≤ uniform a b f B B :=
  le_uniform_zero.mpr (fun _ hy _ hx hxy => uniform_zero (h hx) (h hy) hxy)

theorem separation_lower {a b : X → X → ENNReal} {f : X → X} {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (hp : 0 < b (f x) (f y)) : uniform a b f A A ≤ a x y :=
  le_of_not_gt (fun h => hp.ne' (uniform_zero hx hy h))

theorem separation_witness {a b : X → X → ENNReal} {f : X → X} {A : Set X} {α : ENNReal}
    (h : uniform a b f A A < α) :
    ∃ x ∈ A, ∃ y ∈ A, a x y < α ∧ ∃ ε : ENNReal, 0 < ε ∧ ε < ⊤ ∧ ε ≤ b (f x) (f y) := by
  have hn : ¬ ∀ y ∈ A, ∀ x ∈ A, a x y < α → b (f x) (f y) = 0 :=
    fun hz => (not_le_of_gt h) (le_uniform_zero.mpr hz)
  push_neg at hn
  obtain ⟨y,hy,x,hx,hxy,hout⟩ := hn
  obtain ⟨ε,hε,hε'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hout)
  exact ⟨x,hx,y,hy,hxy,ε,hε,ENNReal.coe_lt_top,hε'.le⟩

theorem threshold_fiber (d : I → X → X → ENNReal) {f : X → X} {A : Set X} {i j : I}
    {τ : ENNReal} (h : τ ≤ uniform (d i) (d j) f A A) {y : X} (hy : y ∈ A) :
    ball (d i) y τ ∩ A ⊆ Fiber d f A {j} (f y) := by
  rintro x ⟨hxy,hx⟩
  exact ⟨hx,fun k hk => by
    have : k = j := hk
    subst k
    exact uniform_zero hx hy (hxy.trans_le h)⟩

theorem colip_point_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius (d i) (d j) f.func U y) := by
  rintro ⟨hpos,hlt⟩
  exact hpos.ne' (positive_colip_entry_reflects_zero d f U K i j hK hp x hx y hy (radius_zero hx hlt))
theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniform (d i) (d j) f.func U U ≤ d i x y := by
  by_cases hz : d i x y = 0
  · exact Or.inl hz
  · right; apply le_of_not_gt; intro hlt
    exact colip_point_gap d hK hp hx hy ⟨pos_iff_ne_zero.mpr hz,hlt.trans_le (uniform_le_point hy)⟩
end MG

namespace MG
open Set
variable {X I : Type}

structure InputScale (X I : Type) where
  value : I → Set X → ENNReal
  mono : ∀ i A B, A.Nonempty → B.Nonempty → A ⊆ B → value i A ≤ value i B

noncomputable def diameter (a : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, a x y
theorem le_diameter {a : X → X → ENNReal} {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    a x y ≤ diameter a A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
theorem diameter_mono {a : X → X → ENNReal} {A B : Set X} (h : A ⊆ B) :
    diameter a A ≤ diameter a B := by
  exact iSup_le (fun x => iSup_le (fun hx => iSup_le (fun y => iSup_le (fun hy => le_diameter (h hx) (h hy)))))
noncomputable def diameterScale (d : I → X → X → ENNReal) : InputScale X I :=
  ⟨fun i => diameter (d i),fun _ _ _ _ _ h => diameter_mono h⟩
noncomputable def threshold (s r τs τn : ENNReal) : Bool × Bool :=
  (decide (s < τs),decide (τn ≤ r))
noncomputable def channelType (σ : InputScale X I) (d : I → X → X → ENNReal)
    (f : X → X) (A : Set X) (τs τn : ENNReal) (i j : I) : Bool × Bool :=
  threshold (σ.value i A) (uniform (d i) (d j) f A A) τs τn

theorem threshold_cases (s r τs τn : ENNReal) :
    (threshold s r τs τn = (true,true) ↔ s < τs ∧ τn ≤ r) ∧
    (threshold s r τs τn = (true,false) ↔ s < τs ∧ r < τn) ∧
    (threshold s r τs τn = (false,true) ↔ τs ≤ s ∧ τn ≤ r) ∧
    (threshold s r τs τn = (false,false) ↔ τs ≤ s ∧ r < τn) := by
  simp [threshold,Prod.mk.injEq,not_lt,not_le]
theorem threshold_exhaustive (s r τs τn : ENNReal) :
    ∃! p : Bool × Bool, threshold s r τs τn = p := ⟨_,rfl,fun _ h => h.symm⟩
theorem scale_threshold_mono {s τ τ' : ENNReal} (h : τ ≤ τ') : s < τ → s < τ' :=
  fun hs => hs.trans_le h
theorem null_threshold_antitone {r τ τ' : ENNReal} (h : τ ≤ τ') : τ' ≤ r → τ ≤ r :=
  fun hr => h.trans hr
theorem scale_restrict (σ : InputScale X I) {A B : Set X} (hB : B.Nonempty) (h : B ⊆ A)
    (i : I) (τ : ENNReal) : σ.value i B ≤ σ.value i A ∧ (σ.value i A < τ → σ.value i B < τ) := by
  have hm := σ.mono i B A hB (hB.mono h) h
  exact ⟨hm,fun ht => hm.trans_lt ht⟩

theorem small_domain_iff {a b : X → X → ENNReal} {f : X → X} {A : Set X}
    {τs τn : ENNReal} (hs : diameter a A < τs) (ht : τs ≤ τn) :
    τn ≤ uniform a b f A A ↔ ∀ x ∈ A, ∀ y ∈ A, b (f x) (f y) = 0 := by
  constructor
  · intro h x hx y hy
    exact uniform_zero hx hy ((le_diameter hx hy).trans_lt (hs.trans_le (ht.trans h)))
  · intro h; rw [uniform_top h]; exact le_top

theorem finite_inf_min [Fintype I] (v : I → ENNReal) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, v j = ⨅ k ∈ J, v k := by
  classical
  let s := Finset.univ.filter (fun j => j ∈ J)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := hJ
    exact ⟨j,by simp [s,hj]⟩
  obtain ⟨j,hj,hm⟩ := s.exists_min_image v hs
  have hj' : j ∈ J := (Finset.mem_filter.mp hj).2
  refine ⟨j,hj',le_antisymm ?_ (iInf_le_of_le j (iInf_le_of_le hj' le_rfl))⟩
  exact le_iInf (fun k => le_iInf (fun hk => hm k (by simp [s,hk])))
end MG

namespace MG
open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
variable {X I : Type} {bot : X}

def TotallyBounded (a : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number a r U < ⊤
def DeltaDefined (a b : X → X → ENNReal) (f : X → X) (ε : ENNReal) (U : Set X) : Prop :=
  covering_number a ε U < ⊤ ∨ covering_number b ε (f '' U) < ⊤
noncomputable def delta (a b : X → X → ENNReal) (f : X → X) (ε : ENNReal) (U : Set X)
    (_h : DeltaDefined a b f ε U) : EReal := metric_entropy a ε U - metric_entropy b ε (f '' U)

theorem net_push {a b : X → X → ENNReal} {f : X → X} {U : Set X} {δ ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, a x y < δ → b (f x) (f y) < ε)
    {S : Finset X} (hS : InternalEpsilonNet a δ U S) :
    ∃ T : Finset X, InternalEpsilonNet b ε (f '' U) T ∧ T.card ≤ S.card := by
  classical
  refine ⟨S.image f,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x,hS.1 hx,rfl⟩
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := hS.2 x hx
    exact ⟨f y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,h x hx y (hS.1 hy) hxy⟩

theorem net_pull {a b : X → X → ENNReal} {f : X → X} {U : Set X} {δ ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) < ε → a x y < δ)
    {T : Finset X} (hT : InternalEpsilonNet b ε (f '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet a δ U S ∧ S.card ≤ T.card := by
  classical
  let r : {t // t ∈ T} → X := fun t => Classical.choose (hT.1 t.property)
  have hr : ∀ t, r t ∈ U ∧ f (r t) = t.val := fun t => Classical.choose_spec (hT.1 t.property)
  refine ⟨T.attach.image r,⟨?_,?_⟩,?_⟩
  · intro x hx
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hx
    exact (hr t).1
  · intro x hx
    obtain ⟨t,ht,hxt⟩ := hT.2 (f x) ⟨x,hx,rfl⟩
    refine ⟨r ⟨t,ht⟩,Finset.mem_image.mpr ⟨⟨t,ht⟩,Finset.mem_attach _ _,rfl⟩,?_⟩
    apply h x hx _ (hr ⟨t,ht⟩).1
    simpa [(hr ⟨t,ht⟩).2] using hxt
  · exact (Finset.card_image_le).trans (by simp)

theorem cover_push {a b : X → X → ENNReal} {f : X → X} {U : Set X} {δ ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, a x y < δ → b (f x) (f y) < ε) :
    covering_number b ε (f '' U) ≤ covering_number a δ U := by
  apply le_iInf; intro S; apply le_iInf; intro hS
  obtain ⟨T,hT,hcard⟩ := net_push h hS
  exact (iInf_le_of_le T (iInf_le_of_le hT le_rfl)).trans (by exact_mod_cast hcard)
theorem cover_pull {a b : X → X → ENNReal} {f : X → X} {U : Set X} {δ ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) < ε → a x y < δ) :
    covering_number a δ U ≤ covering_number b ε (f '' U) := by
  apply le_iInf; intro T; apply le_iInf; intro hT
  obtain ⟨S,hS,hcard⟩ := net_pull h hT
  exact (iInf_le_of_le S (iInf_le_of_le hS le_rfl)).trans (by exact_mod_cast hcard)

theorem log_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal,hb]
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
  have hb0 : b ≠ 0 := fun h => ha (le_antisymm (h ▸ hab) (zero_le _))
  simp only [log2_ereal,if_neg ha,if_neg hb,if_neg hat,if_neg hb0]
  apply EReal.coe_le_coe_iff.mpr
  exact (Real.strictMonoOn_logb one_lt_two).monotoneOn
    (ENNReal.toReal_pos ha hat) (ENNReal.toReal_pos hb0 hb) (ENNReal.toReal_mono hb hab)

theorem entropy_mono {a b : X → X → ENNReal} {A B : Set X} {ε δ : ENNReal}
    (h : covering_number a ε A ≤ covering_number b δ B) :
    metric_entropy a ε A ≤ metric_entropy b δ B := log_mono h

theorem threshold_cover {a b : X → X → ENNReal} {f : X → X} {A B : Set X} {τ ε : ENNReal}
    (hr : τ ≤ uniform a b f A A) (hB : B ⊆ A) (hε : 0 < ε) :
    covering_number b ε (f '' B) ≤ covering_number a τ B := by
  apply cover_push
  intro x hx y hy hxy
  rw [uniform_zero (hB hx) (hB hy) (hxy.trans_le hr)]
  exact hε
theorem threshold_entropy {a b : X → X → ENNReal} {f : X → X} {A B : Set X} {τ ε : ENNReal}
    (hr : τ ≤ uniform a b f A A) (hB : B ⊆ A) (hε : 0 < ε) :
    metric_entropy b ε (f '' B) ≤ metric_entropy a τ B := entropy_mono (threshold_cover hr hB hε)

theorem cover_one {b : X → X → ENNReal} {V : Set X} (hV : V.Nonempty) {ε : ENNReal}
    (hε : 0 < ε) (h : ∀ x ∈ V, ∀ y ∈ V, b x y = 0) : covering_number b ε V = 1 := by
  classical
  apply le_antisymm _ (one_le_covering_number_of_nonempty b ε V hV)
  obtain ⟨z,hz⟩ := hV
  have hn : InternalEpsilonNet b ε V {z} := by
    constructor
    · simpa using (singleton_subset_iff.mpr hz)
    · intro x hx; exact ⟨z,by simp,by simpa [h x hx z hz] using hε⟩
  exact iInf_le_of_le {z} (iInf_le_of_le hn (by simp))

theorem const_cover {b : X → X → ENNReal} {f : X → X} {U : Set X} (hU : U.Nonempty)
    {ε : ENNReal} (hε : 0 < ε) (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) = 0) :
    covering_number b ε (f '' U) = 1 := by
  apply cover_one (hU.image f) hε
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; exact h x hx y hy

theorem finite_cover {a : X → X → ENNReal} (ha : ∀ x, a x x = 0)
    {U : Set X} (hU : U.Finite) {ε : ENNReal} (hε : 0 < ε) : covering_number a ε U < ⊤ := by
  classical
  have hn : InternalEpsilonNet a ε U hU.toFinset := by
    constructor
    · simp
    · intro x hx; exact ⟨x,by simpa using hx,by simpa [ha] using hε⟩
  exact lt_of_le_of_lt (iInf_le_of_le hU.toFinset (iInf_le_of_le hn le_rfl)) (ENNReal.natCast_lt_top _)

theorem entropy_finite {a : X → X → ENNReal} {U : Set X} {ε : ENNReal}
    (hU : U.Nonempty) (hf : covering_number a ε U < ⊤) : ∃ t : ℝ, metric_entropy a ε U = t := by
  have hz : covering_number a ε U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty a ε U hU))
  exact ⟨Real.logb 2 (covering_number a ε U).toReal,by simp [metric_entropy,log2_ereal,hz,hf.ne]⟩

theorem finite_delta {a b : X → X → ENNReal} (ha : ∀ x, a x x = 0) (hb : ∀ x, b x x = 0)
    {f : X → X} {U : Set X} (hU : U.Nonempty) (hfin : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    1 ≤ covering_number a ε U ∧ covering_number a ε U < ⊤ ∧
    1 ≤ covering_number b ε (f '' U) ∧ covering_number b ε (f '' U) < ⊤ ∧
    ∃ h : DeltaDefined a b f ε U, ∃ s t : ℝ,
      metric_entropy a ε U = s ∧ metric_entropy b ε (f '' U) = t ∧ delta a b f ε U h = (s-t : ℝ) := by
  have h1 := finite_cover ha hfin hε
  have h2 := finite_cover hb (hfin.image f) hε
  obtain ⟨s,hs⟩ := entropy_finite hU h1
  obtain ⟨t,ht⟩ := entropy_finite (hU.image f) h2
  refine ⟨one_le_covering_number_of_nonempty _ _ _ hU,h1,
    one_le_covering_number_of_nonempty _ _ _ (hU.image f),h2,Or.inl h1,s,t,hs,ht,?_⟩
  simp [delta,hs,ht]

theorem const_entropy_delta {a b : X → X → ENNReal} {f : X → X} {U : Set X}
    (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε)
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) = 0) :
    covering_number b ε (f '' U) = 1 ∧ metric_entropy b ε (f '' U) = 0 ∧
    ∃ hd : DeltaDefined a b f ε U, delta a b f ε U hd = metric_entropy a ε U := by
  have hc := const_cover hU hε h
  have he : metric_entropy b ε (f '' U) = 0 := by simp [metric_entropy,hc,log2_ereal]
  exact ⟨hc,he,Or.inr (by rw [hc]; exact ENNReal.one_lt_top),by simp [delta,he]⟩

theorem isometry_cover {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) = a x y) :
    covering_number b ε (f '' U) = covering_number a ε U ∧
    metric_entropy b ε (f '' U) = metric_entropy a ε U := by
  have hc : covering_number b ε (f '' U) = covering_number a ε U := by
    apply le_antisymm
    · exact cover_push (fun x hx y hy hh => by rwa [h x hx y hy])
    · exact cover_pull (fun x hx y hy hh => by rwa [h x hx y hy] at hh)
  exact ⟨hc,congrArg log2_ereal hc⟩

theorem isometry_delta {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε : ENNReal}
    (hU : U.Nonempty) (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) = a x y)
    (hd : DeltaDefined a b f ε U) : delta a b f ε U hd = 0 := by
  obtain ⟨hc,he⟩ := isometry_cover (ε := ε) h
  have hf : covering_number a ε U < ⊤ := hd.elim id (fun h => hc ▸ h)
  obtain ⟨s,hs⟩ := entropy_finite hU hf
  simp [delta,he,hs,← EReal.coe_sub]

theorem lip_cover {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε L : ENNReal}
    (hL : 0 < L) (hLt : L < ⊤) (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) ≤ L*a x y) :
    covering_number b ε (f '' U) ≤ covering_number a (ε/L) U := by
  apply cover_push; intro x hx y hy hxy
  apply (h x hx y hy).trans_lt
  simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hL.ne') (Or.inl hLt.ne)).mp hxy

theorem colip_cover {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε K : ENNReal}
    (hK : 0 < K) (hKt : K < ⊤) (h : ∀ x ∈ U, ∀ y ∈ U, K*a x y ≤ b (f x) (f y)) :
    covering_number a (ε/K) U ≤ covering_number b ε (f '' U) := by
  apply cover_pull; intro x hx y hy hxy
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hK.ne') (Or.inl hKt.ne)).mpr
  simpa [mul_comm] using (h x hx y hy).trans_lt hxy

theorem matrix_colip_cover [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I} {ε : ENNReal}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (ht : K i j < ⊤) :
    covering_number (d i) (ε/K i j) U ≤ covering_number (d j) ε (f.func '' U) := by
  apply colip_cover hp ht
  intro x hx y hy
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j*d k x y)) (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)

theorem lip_delta {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε L : ENNReal}
    (hU : U.Nonempty) (hTB : TotallyBounded a U) (hε : 0 < ε) (hεt : ε < ⊤)
    (hL : 0 < L) (hLt : L < ⊤) (h : ∀ x ∈ U, ∀ y ∈ U, b (f x) (f y) ≤ L*a x y) :
    covering_number b ε (f '' U) < ⊤ ∧
    ∃ hd : DeltaDefined a b f ε U,
      metric_entropy a ε U - metric_entropy a (ε/L) U ≤ delta a b f ε U hd := by
  have hp : 0 < ε/L := ENNReal.div_pos hε.ne' hLt.ne
  have ht : ε/L < ⊤ := ENNReal.div_lt_top hεt.ne hL.ne'
  have hc := lip_cover (ε := ε) hL hLt h
  exact ⟨hc.trans_lt (hTB _ hp ht),Or.inl (hTB _ hε hεt),EReal.sub_le_sub le_rfl (entropy_mono hc)⟩

theorem colip_delta {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε K : ENNReal}
    (hTB : TotallyBounded a U) (hε : 0 < ε) (hεt : ε < ⊤)
    (hK : 0 < K) (hKt : K < ⊤) (h : ∀ x ∈ U, ∀ y ∈ U, K*a x y ≤ b (f x) (f y)) :
    ∃ hd : DeltaDefined a b f ε U,
      delta a b f ε U hd ≤ metric_entropy a ε U - metric_entropy a (ε/K) U := by
  exact ⟨Or.inl (hTB _ hε hεt),EReal.sub_le_sub le_rfl (entropy_mono (colip_cover hK hKt h))⟩

theorem factor_lip (a : X → X → ENNReal) {f g : X → X} {U : Set X}
    (T : (f '' U) → X) (hT : ∀ x : U, T (imageMap f U x) = g x)
    {K L : ENNReal} (hK : 0 < K) (hKt : K < ⊤) (hLt : L < ⊤)
    (hA : ∀ x ∈ U, ∀ y ∈ U, K*a x y ≤ a (f x) (f y))
    (hB : ∀ x ∈ U, ∀ y ∈ U, a (g x) (g y) ≤ L*a x y) :
    ∀ z w : (f '' U), a (T z) (T w) ≤ (L/K)*a z.val w.val := by
  intro z w
  obtain ⟨x,rfl⟩ := imageMap_surjective f U z
  obtain ⟨y,rfl⟩ := imageMap_surjective f U w
  rw [hT x,hT y]
  have hxy : a x y ≤ a (f x) (f y)/K :=
    (ENNReal.le_div_iff_mul_le (Or.inl hK.ne') (Or.inl hKt.ne)).mpr (by simpa [mul_comm] using hA x x.property y y.property)
  calc
    a (g x) (g y) ≤ L*a x y := hB x x.property y y.property
    _ ≤ L*(a (f x) (f y)/K) := mul_le_mul_left' hxy L
    _ = (L/K)*a (imageMap f U x).val (imageMap f U y).val := by
      dsimp [imageMap]; simp only [div_eq_mul_inv]; ac_rfl
end MG

namespace MG
open Set
open scoped Classical
open formal_oet.vol_01.ch_01_foundations
variable {A B : Type}

def extend (a : A → A → ENNReal) : Option A → Option A → ENNReal
  | none,none => 0
  | some x,some y => a x y
  | _,_ => ⊤
theorem extend_legal [Nonempty A] (a : A → A → ENNReal)
    (hs : ∀ x, a x x = 0) (hc : ∀ x y, a x y = a y x)
    (ht : ∀ x y z, a x z ≤ a x y + a y z) :
    ExtendedPseudoMetric (Option A) none (extend a) where
  nonabsorbing := ⟨some (Classical.choice inferInstance),Option.some_ne_none _⟩
  dist_self x := by cases x <;> simp [extend,hs]
  symm x y := by cases x <;> cases y <;> simp [extend,hc]
  triangle x y z := by cases x <;> cases y <;> cases z <;> simp [extend,ht]
  isolate_bot x hx := by cases x <;> simp_all [extend]

noncomputable def discrete (q : A → B) (c : ENNReal) : Option A → Option A → ENNReal :=
  extend (fun x y => if q x = q y then 0 else c)
theorem discrete_legal [Nonempty A] (q : A → B) (c : ENNReal) :
    ExtendedPseudoMetric (Option A) none (discrete q c) := by
  classical
  apply extend_legal
  · intro x; simp
  · intro x y; simp [eq_comm]
  · intro x y z
    by_cases hxy : q x = q y <;> by_cases hyz : q y = q z <;>
      by_cases hxz : q x = q z <;> simp_all

def liftOp (f : A → A) : Operator (Option A) none := ⟨Option.map f,rfl⟩
noncomputable def realD (q : ℝ → ℝ) : Option ℝ → Option ℝ → ENNReal :=
  extend (fun x y => edist (q x) (q y))
theorem realD_apply (q : ℝ → ℝ) (x y : ℝ) :
    realD q (some x) (some y) = ENNReal.ofReal |q x-q y| := by
  simp [realD,extend,edist_dist,Real.dist_eq]
theorem realD_legal (q : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (realD q) :=
  extend_legal _ (fun x => edist_self _) (fun x y => edist_comm _ _) (fun x y z => edist_triangle _ _ _)

namespace Swap
noncomputable def d : Unit → Option Bool → Option Bool → ENNReal := fun _ => discrete id 1
def U : Set (Option Bool) := {some false,some true}
def f : Operator (Option Bool) none := liftOp Bool.not
theorem legal : ExtendedPseudoMetric (Option Bool) none (d ()) := discrete_legal id 1
theorem data : U ⊆ dom f ∧ f.func '' U = U ∧
    Active d f.func U = univ ∧ Ident d f.func U = ∅ ∧
    Ident d (f*f).func U = univ ∧ Active d (f*f).func U = ∅ := by
  have he : f.func '' U = U := by ext x; simp [U,f,liftOp]; aesop
  refine ⟨?_,he,?_,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · simp [dom,f,liftOp]
    · have : x = some true := hx; subst x; simp [dom,f,liftOp]
  all_goals ext i; cases i; norm_num [Active,Ident,Const,d,discrete,extend,U,f,liftOp,
    operator_compose,HMul.hMul,Mul.mul,operator_monoid]
theorem reverse_inclusions_fail :
    ¬ (Active d f.func U ∪ Active d f.func (f.func '' U) ⊆ Active d (f*f).func U) ∧
    ¬ (Ident d (f*f).func U ⊆ Ident d f.func U ∩ Ident d f.func (f.func '' U)) := by
  obtain ⟨_,hi,ha,hn,hc,hz⟩ := data
  simp [hi,ha,hn,hc,hz]
end Swap

namespace Seven
def U : Set (Option (Fin 6)) := {some 0,some 1}
def q (x : Fin 6) : ℕ := if x = 3 then 2 else x.val
noncomputable def d (i : Bool) : Option (Fin 6) → Option (Fin 6) → ENNReal :=
  if i then discrete id 1 else discrete q 1
def f : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some 0 => some 2
    | some 1 => some 3
    | _ => none, rfl⟩
def g : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some 2 => some 4
    | some 3 => some 5
    | _ => none, rfl⟩
theorem legal (i : Bool) : ExtendedPseudoMetric (Option (Fin 6)) none (d i) := by
  cases i
  · exact discrete_legal q 1
  · exact discrete_legal id 1
theorem data : U ⊆ dom (g*f) ∧ false ∈ Const d f.func U ∧
    false ∉ Const d (g*f).func U ∧ d true (some 2) (some 3) = 1 := by
  norm_num [U,dom,Const,d,discrete,extend,q,f,g,operator_compose,HMul.hMul,Mul.mul,operator_monoid,
    Set.insert_subset_iff,Set.singleton_subset_iff,Option.some_ne_none]
  norm_num [Fin.ext_iff]
end Seven

namespace Infinite
def U : Set (Option Bool) := {some false,some true}
noncomputable def d (i : Bool) : Option Bool → Option Bool → ENNReal := discrete id (if i then 1 else ⊤)
theorem legal (i : Bool) : ExtendedPseudoMetric (Option Bool) none (d i) := discrete_legal id _
theorem data (j : Bool) : U ⊆ dom (1 : Operator (Option Bool) none) ∧
    uniform (d false) (d j) id U U = ⊤ ∧ j ∉ Const d id U := by
  refine ⟨?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · change some false ≠ (none : Option Bool); exact Option.some_ne_none _
    · have : x = some true := hx; subst x; change some true ≠ (none : Option Bool); exact Option.some_ne_none _
  · apply top_unique; apply le_uniform_zero.mpr
    intro y hy x hx hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals simp_all [d,discrete,extend]
  · cases j <;> norm_num [Const,U,d,discrete,extend]
end Infinite

namespace Affine
noncomputable def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => realD abs
def f : Operator (Option ℝ) none := liftOp (fun x => 2*x-1)
def U : Set (Option ℝ) := {some 0,some 1}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (d ()) := realD_legal abs
theorem first : U ⊆ dom f ∧ Fiber d f.func U {()} (f.func (some 0)) = U ∧
    () ∈ Const d f.func U := by
  have hc : () ∈ Const d f.func U := by
    norm_num [Const,U,d,realD,extend,f,liftOp,edist_dist,Real.dist_eq]
  refine ⟨?_,?_,hc⟩
  · intro x hx; rcases hx with rfl | hx
    · simp [dom,f,liftOp]
    · have : x = some 1 := hx; subst x; simp [dom,f,liftOp]
  · exact (fiber_const d (fun _ => legal) (y := f.func (some 0)) hc ⟨some 0,by simp [U],rfl⟩).1
theorem second : U ⊆ dom (f*f) ∧ Fiber d (f*f).func U {()} ((f*f).func (some 0)) = {some 0} ∧
    () ∈ Active d (f*f).func U := by
  have eval (x : ℝ) : (f*f).func (some x) = some (2*(2*x-1)-1) := rfl
  refine ⟨?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · rw [dom]; simp only [mem_setOf_eq,eval,ne_eq,Option.some_ne_none,not_false_eq_true]
    · have : x = some 1 := hx; subst x; rw [dom]; simp only [mem_setOf_eq,eval,ne_eq,Option.some_ne_none,not_false_eq_true]
  · ext x; simp only [Fiber,mem_setOf_eq,mem_singleton_iff,forall_eq,U,mem_insert_iff]
    constructor
    · rintro ⟨rfl | rfl,h⟩
      · rfl
      · norm_num [eval,d,realD,extend,edist_dist,Real.dist_eq] at h
    · rintro rfl; norm_num [eval,d,realD,extend,edist_dist,Real.dist_eq]
  · norm_num [Active,Ident,Const,U,eval,d,realD,extend,edist_dist,Real.dist_eq]
end Affine

theorem point_constant_square {X : Type} {bot : X} (f : Operator X bot) (U : Set X)
    (c : X) (hc : c ≠ bot) (h : ∀ x ∈ U, f.func x = c) :
    (∀ x ∈ U, (f*f).func x = f.func c) ∧
    (f.func c ≠ bot → U ⊆ dom (f*f)) ∧
    (f.func c = bot → U ∩ dom (f*f) = ∅) := by
  have he : ∀ x ∈ U, (f*f).func x = f.func c := by
    intro x hx; change f.func (f.func x) = f.func c; rw [h x hx]
  refine ⟨he,fun hn x hx => ?_,?_⟩
  · change (f*f).func x ≠ bot; rwa [he x hx]
  · intro hb; apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hd⟩; exact hd ((he x hx).trans hb)
end MG

namespace MG
open Set
open formal_oet.vol_01.ch_01_foundations
open scoped Classical

@[simp] theorem real_distance (x y : ℝ) : realD id (some x) (some y) = ENNReal.ofReal |x-y| := by
  simp [realD,extend,edist_dist,Real.dist_eq]

theorem diameter_interval {l u : ℝ} (hlu : l ≤ u) :
    diameter (realD id) (some '' Icc l u) = ENNReal.ofReal (u-l) := by
  apply le_antisymm
  · apply iSup_le; rintro _; apply iSup_le; rintro ⟨x,hx,rfl⟩
    apply iSup_le; rintro _; apply iSup_le; rintro ⟨y,hy,rfl⟩
    rw [real_distance]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]; constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  · have h := le_diameter (a := realD id) (A := some '' Icc l u)
      (show some u ∈ some '' Icc l u from ⟨u,⟨hlu,le_rfl⟩,rfl⟩)
      (show some l ∈ some '' Icc l u from ⟨l,⟨le_rfl,hlu⟩,rfl⟩)
    simpa [real_distance,abs_of_nonneg (sub_nonneg.mpr hlu)] using h

theorem diameter_two {x y : ℝ} (hxy : x ≤ y) :
    diameter (realD id) {some x,some y} = ENNReal.ofReal (y-x) := by
  apply le_antisymm
  · rw [← diameter_interval hxy]
    apply diameter_mono
    intro z hz; rcases hz with rfl | rfl
    · exact ⟨x,⟨le_rfl,hxy⟩,rfl⟩
    · exact ⟨y,⟨hxy,le_rfl⟩,rfl⟩
  · have h := le_diameter (a := realD id) (A := {some x,some y})
      (show some y ∈ ({some x,some y} : Set (Option ℝ)) by simp)
      (show some x ∈ ({some x,some y} : Set (Option ℝ)) by simp)
    simpa [real_distance,abs_of_nonneg (sub_nonneg.mpr hxy)] using h

theorem scale_reverse_counterexample :
    ({some (0:ℝ)} : Set (Option ℝ)).Nonempty ∧
    ({some (0:ℝ)} : Set (Option ℝ)) ⊆ {some 0,some 1} ∧
    diameter (realD id) {some 0} < (1/2 : ENNReal) ∧
    (1/2 : ENNReal) ≤ diameter (realD id) {some 0,some 1} := by
  rw [diameter_two (by norm_num)]
  norm_num [diameter,real_distance,Set.subset_def]

theorem scale_reverse_domain :
    ({some (0:ℝ),some 1} : Set (Option ℝ)) ⊆ dom (1 : Operator (Option ℝ) none) := by
  intro x hx; rcases hx with rfl | rfl <;> exact Option.some_ne_none _

theorem uniform_le_bad_pair {X : Type} {a b : X → X → ENNReal} {f : X → X}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hn : b (f x) (f y) ≠ 0) :
    uniform a b f U U ≤ a x y :=
  (uniform_le_point hy).trans (iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le hn le_rfl)))

namespace Floor
noncomputable def f : Operator (Option ℝ) none := liftOp (fun x => (⌊x⌋ : ℝ))
def interval (l u : ℝ) : Set (Option ℝ) := some '' Icc l u
def pair : Set (Option ℝ) := {some 0,some 2}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (realD id) := realD_legal id
theorem domain (D : Set ℝ) : some '' D ⊆ dom f := by
  rintro _ ⟨x,_,rfl⟩; exact Option.some_ne_none _
theorem jump {l u : ℝ} (hl : l < 1) (hu : 1 ≤ u) :
    uniform (realD id) (realD id) f.func (interval l u) (interval l u) = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_not_gt; intro hp
  obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  let t : ℝ := min ((1-l)/2) (min (1/2) (r/2))
  have ht : 0 < t := lt_min (by linarith) (lt_min (by norm_num) (by linarith))
  have ht1 : t ≤ (1-l)/2 := min_le_left _ _
  have ht2 : t ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have ht3 : t ≤ (r:ℝ)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hfloor : ⌊1-t⌋ = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr; constructor <;> norm_num <;> linarith
  have hx : some (1-t) ∈ interval l u := ⟨1-t,⟨by linarith,by linarith⟩,rfl⟩
  have hy : some (1:ℝ) ∈ interval l u := ⟨1,⟨hl.le,hu⟩,rfl⟩
  have hdist : realD id (some (1-t)) (some 1) < (r:ENNReal) := by
    rw [real_distance,ENNReal.ofReal_lt_coe_iff (abs_nonneg _)]
    rw [show 1-t-1 = -t by ring,abs_neg,abs_of_pos ht]
    linarith
  have hz := uniform_zero (a := realD id) (b := realD id) (f := f.func) hx hy (hdist.trans hr')
  norm_num [f,liftOp,hfloor,real_distance] at hz

theorem first : diameter (realD id) (interval 0 (1/2)) = 1/2 ∧
    uniform (realD id) (realD id) f.func (interval 0 (1/2)) (interval 0 (1/2)) = ⊤ ∧
    threshold (diameter (realD id) (interval 0 (1/2)))
      (uniform (realD id) (realD id) f.func (interval 0 (1/2)) (interval 0 (1/2))) 1 1 = (true,true) := by
  have hd : diameter (realD id) (interval 0 (1/2)) = 1/2 := by
    rw [interval,diameter_interval (by norm_num)]; norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hf : ∀ x ∈ interval 0 (1/2), f.func x = some 0 := by
    rintro _ ⟨x,hx,rfl⟩
    have he : ⌊x⌋ = (0:ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hx.1,by norm_num; linarith [hx.2]⟩
    simp [f,liftOp,he]
  have hr : uniform (realD id) (realD id) f.func (interval 0 (1/2)) (interval 0 (1/2)) = ⊤ :=
    uniform_top (fun x hx y hy => by rw [hf x hx,hf y hy]; norm_num)
  exact ⟨hd,hr,by norm_num [hd,hr,threshold]⟩

theorem second : diameter (realD id) (interval (9/10) (11/10)) = 1/5 ∧
    uniform (realD id) (realD id) f.func (interval (9/10) (11/10)) (interval (9/10) (11/10)) = 0 ∧
    threshold (diameter (realD id) (interval (9/10) (11/10)))
      (uniform (realD id) (realD id) f.func (interval (9/10) (11/10)) (interval (9/10) (11/10))) 1 1 = (true,false) := by
  have hd : diameter (realD id) (interval (9/10) (11/10)) = 1/5 := by
    rw [interval,diameter_interval (by norm_num)]; norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hr := jump (l := 9/10) (u := 11/10) (by norm_num) (by norm_num)
  exact ⟨hd,hr,by norm_num [hd,hr,threshold]⟩

theorem third : diameter (realD id) pair = 2 ∧
    uniform (realD id) (realD id) f.func pair pair = 2 ∧
    threshold (diameter (realD id) pair) (uniform (realD id) (realD id) f.func pair pair) 1 1 = (false,true) := by
  have hd : diameter (realD id) pair = 2 := by rw [pair,diameter_two (by norm_num)]; norm_num
  have hr : uniform (realD id) (realD id) f.func pair pair = 2 := by
    apply le_antisymm
    · have h := uniform_le_bad_pair (a := realD id) (b := realD id) (f := f.func)
        (U := pair) (x := some 0) (y := some 2) (by simp [pair]) (by simp [pair])
        (by norm_num [f,liftOp,real_distance])
      simpa using h
    · apply le_uniform_zero.mpr
      intro y hy x hx hxy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      all_goals (try norm_num [real_distance,f,liftOp] at hxy) <;> norm_num [real_distance,f,liftOp]
  exact ⟨hd,hr,by norm_num [hd,hr,threshold]⟩

theorem fourth : diameter (realD id) (interval 0 2) = 2 ∧
    uniform (realD id) (realD id) f.func (interval 0 2) (interval 0 2) = 0 ∧
    threshold (diameter (realD id) (interval 0 2))
      (uniform (realD id) (realD id) f.func (interval 0 2) (interval 0 2)) 1 1 = (false,false) := by
  have hd : diameter (realD id) (interval 0 2) = 2 := by rw [interval,diameter_interval (by norm_num)]; norm_num
  have hr := jump (l := 0) (u := 2) (by norm_num) (by norm_num)
  exact ⟨hd,hr,by norm_num [hd,hr,threshold]⟩

theorem counterexample : pair.Nonempty ∧ pair ⊆ dom f ∧
    1 ≤ uniform (realD id) (realD id) f.func pair pair ∧
    ¬ (∀ x ∈ pair, ∀ y ∈ pair, realD id (f.func x) (f.func y) = 0) := by
  refine ⟨⟨some 0,by simp [pair]⟩,?_,by rw [third.2.1]; norm_num,?_⟩
  · intro x hx; rcases hx with rfl | rfl <;> exact Option.some_ne_none _
  · intro h
    have he := h (some 0) (by simp [pair]) (some 2) (by simp [pair])
    norm_num [f,liftOp,real_distance] at he
end Floor
end MG

namespace MG.Step
open Set
open formal_oet.vol_01.ch_01_foundations
open scoped Classical
noncomputable def s (x : ℝ) : ℝ := if x < 0 then 0 else 1
noncomputable def f : Operator (Option ℝ) none := liftOp s
def U : Set (Option ℝ) := some '' {x : ℝ | |x| ≤ 1 ∧ x ≠ 0}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (realD id) := realD_legal id
theorem domain : U.Nonempty ∧ U ⊆ dom f ∧ U = some '' (Ico (-1) 0 ∪ Ioc 0 1) := by
  refine ⟨⟨some 1,1,by norm_num,rfl⟩,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩; exact Option.some_ne_none _
  · unfold U; congr 1; ext x
    simp only [mem_setOf_eq,abs_le,mem_union,mem_Ico,mem_Ioc]
    constructor
    · rintro ⟨⟨h1,h2⟩,hn⟩; rcases lt_or_gt_of_ne hn with hx | hx
      · exact Or.inl ⟨h1,hx⟩
      · exact Or.inr ⟨hx,h2⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩) <;> constructor
      · exact ⟨h1,h2.le.trans (by norm_num)⟩
      · exact ne_of_lt h2
      · exact ⟨(by linarith),h2⟩
      · exact ne_of_gt h1

theorem same_sign {x y : ℝ} (hy : y ≠ 0) (h : |x-y| < |y|) : s x = s y := by
  by_cases hx : x < 0 <;> by_cases hy' : y < 0
  · simp [s,hx,hy']
  · have yp : 0 < y := lt_of_le_of_ne (not_lt.mp hy') (Ne.symm hy)
    rw [abs_of_pos yp,abs_of_neg (by linarith : x-y < 0)] at h
    linarith
  · rw [abs_of_neg hy',abs_of_pos (by linarith [not_lt.mp hx] : 0 < x-y)] at h
    linarith [not_lt.mp hx]
  · simp [s,hx,hy']

theorem opposite {y t : ℝ} (hy : y ≠ 0) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ x : ℝ, some x ∈ U ∧ |x-y| = |y|+t ∧ |s x-s y| = 1 := by
  by_cases hn : y < 0
  · refine ⟨t,⟨t,⟨by simpa [abs_of_pos ht] using ht1,ht.ne'⟩,rfl⟩,?_,?_⟩
    · rw [abs_of_pos (by linarith : 0 < t-y),abs_of_neg hn]; ring
    · simp [s,hn,not_lt.mpr ht.le]
  · have hp : 0 < y := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hy)
    refine ⟨-t,⟨-t,⟨by simpa [abs_neg,abs_of_pos ht] using ht1,neg_ne_zero.mpr ht.ne'⟩,rfl⟩,?_,?_⟩
    · rw [abs_of_neg (by linarith : -t-y < 0),abs_of_pos hp]; ring
    · norm_num [s,hn,show -t < 0 by linarith]

theorem point {y : ℝ} (hy : some y ∈ U) :
    radius (realD id) (realD id) f.func U (some y) = ENNReal.ofReal |y| ∧
    0 < radius (realD id) (realD id) f.func U (some y) := by
  have hy' : |y| ≤ 1 ∧ y ≠ 0 := by simpa [U] using hy
  have habs : 0 < |y| := abs_pos.mpr hy'.2
  have he : radius (realD id) (realD id) f.func U (some y) = ENNReal.ofReal |y| := by
    apply le_antisymm
    · apply le_of_not_gt; intro h
      obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
      have hrr : |y| < (r:ℝ) := (ENNReal.ofReal_lt_coe_iff (abs_nonneg y)).mp hr
      let t : ℝ := min 1 (((r:ℝ)-|y|)/2)
      have ht : 0 < t := lt_min (by norm_num) (by linarith)
      have ht1 : t ≤ 1 := min_le_left _ _
      have htr : t ≤ ((r:ℝ)-|y|)/2 := min_le_right _ _
      obtain ⟨x,hx,hd,ho⟩ := opposite hy'.2 ht ht1
      have hdist : realD id (some x) (some y) < (r:ENNReal) := by
        rw [real_distance,ENNReal.ofReal_lt_coe_iff (abs_nonneg _),hd]; linarith
      have hz := radius_zero (b := realD id) (f := f.func) hx (hdist.trans hr')
      norm_num [f,liftOp,real_distance,ho] at hz
    · apply le_radius_zero.mpr
      rintro _ ⟨x,hx,rfl⟩ hdist
      have hxy : |x-y| < |y| := (ENNReal.ofReal_lt_ofReal_iff habs).mp (by simpa using hdist)
      change realD id (some (s x)) (some (s y)) = 0
      rw [same_sign hy'.2 hxy]; simp
  exact ⟨he,by rw [he]; exact ENNReal.ofReal_pos.mpr habs⟩

theorem legal_radii {y : ℝ} (hy : some y ∈ U) (r : ENNReal) :
    LegalRadius (realD id) (realD id) f.func U (some y) r ↔
      0 < r ∧ r < ⊤ ∧ r ≤ ENNReal.ofReal |y| := by
  rw [legal_radius_iff,(point hy).1]

theorem uniform_zero : uniform (realD id) (realD id) f.func U U = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_not_gt; intro hp
  obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  let t : ℝ := min 1 ((r:ℝ)/2)
  have ht : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htr : t ≤ (r:ℝ)/2 := min_le_right _ _
  have hm : some t ∈ U := ⟨t,⟨by simpa [abs_of_pos ht] using ht1,ht.ne'⟩,rfl⟩
  have hh := uniform_le_point (a := realD id) (b := realD id) (f := f.func) (U := U) hm
  rw [(point hm).1] at hh
  have : ENNReal.ofReal |t| < (r:ENNReal) := by
    rw [ENNReal.ofReal_lt_coe_iff (abs_nonneg _),abs_of_pos ht]; linarith
  exact (not_lt_of_ge hh) (this.trans hr')
end MG.Step

namespace MG
open Set
open formal_oet.vol_01.ch_01_foundations
open scoped Classical
variable {X : Type}

theorem net_card_bound {a : X → X → ENNReal} {ε : ENNReal} {U : Set X} {n : ℕ}
    (h : ∀ S, InternalEpsilonNet a ε U S → n ≤ S.card) : (n:ENNReal) ≤ covering_number a ε U := by
  apply le_iInf; intro S; apply le_iInf; intro hS; exact_mod_cast h S hS

theorem cover_le_net {a : X → X → ENNReal} {ε : ENNReal} {U : Set X} {S : Finset X}
    (h : InternalEpsilonNet a ε U S) : covering_number a ε U ≤ S.card :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem two_le_cover {a : X → X → ENNReal} {ε : ENNReal} {U : Set X} (hU : U.Nonempty)
    (h : ∀ c ∈ U, ∃ x ∈ U, ε ≤ a x c) : 2 ≤ covering_number a ε U := by
  apply net_card_bound (n := 2)
  intro S hS
  by_contra hn
  have hc : S.card ≤ 1 := by omega
  obtain ⟨z,hz⟩ := hU
  obtain ⟨c,hcS,_⟩ := hS.2 z hz
  obtain ⟨x,hx,hxc⟩ := h c (hS.1 hcS)
  obtain ⟨c',hc'S,hlt⟩ := hS.2 x hx
  have he : c' = c := Finset.card_le_one.mp hc c' hc'S c hcS
  exact (not_lt_of_ge hxc) (he ▸ hlt)

theorem separated_cover {a : X → X → ENNReal} {ε : ENNReal} (hε : 0 < ε)
    (hs : ∀ x, a x x = 0) (S : Finset X)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ a x y) :
    covering_number a ε (S : Set X) = S.card := by
  classical
  apply le_antisymm
  · apply cover_le_net
    exact ⟨Subset.rfl,fun x hx => ⟨x,hx,by simpa [hs] using hε⟩⟩
  · apply net_card_bound
    intro T hT
    apply Finset.card_le_card
    intro x hx
    obtain ⟨c,hc,hlt⟩ := hT.2 x hx
    by_cases he : x = c
    · exact he ▸ hc
    · exact False.elim ((not_lt_of_ge (h x hx c (hT.1 hc) he)) hlt)

@[simp] theorem lt_div_two (a b : ENNReal) : a < b/2 ↔ a*2 < b :=
  ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))
@[simp] theorem div_two_le (a b : ENNReal) : a/2 ≤ b ↔ a ≤ b*2 :=
  ENNReal.div_le_iff (by norm_num) (by norm_num)

namespace Translation
noncomputable def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => realD abs
def f : Operator (Option ℝ) none := liftOp (fun x => x+1)
def U : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (d ()) := realD_legal abs
theorem domain : U ⊆ dom f := by
  intro x hx; simp only [U,mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _
theorem fibers :
    (Fiber d id U univ '' (id '' U)) = {{some (-3)},{some (-2),some 2},{some 0}} ∧
    (Fiber d f.func U univ '' (f.func '' U)) = {{some (-3)},{some (-2),some 0},{some 2}} := by
  have a0 : Fiber d id U univ (some (-3)) = {some (-3)} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have a1 : Fiber d id U univ (some (-2)) = {some (-2),some 2} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have a2 : Fiber d id U univ (some (0)) = {some 0} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have a3 : Fiber d id U univ (some (2)) = {some (-2),some 2} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have b0 : Fiber d f.func U univ (some (-2)) = {some (-3)} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have b1 : Fiber d f.func U univ (some (-1)) = {some (-2),some 0} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have b2 : Fiber d f.func U univ (some (1)) = {some (-2),some 0} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  have b3 : Fiber d f.func U univ (some (3)) = {some 2} := by
    ext x
    by_cases h0 : x = some (-3)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h1 : x = some (-2)
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h2 : x = some 0
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    by_cases h3 : x = some 2
    · subst x; norm_num [Fiber,U,f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simp [Fiber,U,h0,h1,h2,h3]
  constructor
  · rw [Set.image_id]
    change Fiber d id U univ '' {some (-3),some (-2),some 0,some 2} = _
    simp only [Set.image_insert_eq,Set.image_singleton,a0,a1,a2,a3]
    ext S; simp <;> tauto
  · have he : f.func '' U = {some (-2),some (-1),some 1,some 3} := by
      norm_num [U,f,liftOp,Set.image_insert_eq,Set.image_singleton]
    rw [he]
    simp only [Set.image_insert_eq,Set.image_singleton,b0,b1,b2,b3]
    ext S; simp <;> tauto

theorem covers : covering_number (d ()) (3/2) U = 2 ∧
    covering_number (d ()) (3/2) (f.func '' U) = 1 := by
  have hn : InternalEpsilonNet (d ()) (3/2) U {some (-2),some 0} := by
    norm_num [InternalEpsilonNet,U,Set.subset_def,d,realD,extend,edist_dist,Real.dist_eq]
  have hmiss : ∀ c ∈ U, ∃ x ∈ U, (3/2:ENNReal) ≤ d () x c := by
    intro c hc; simp only [U,mem_insert_iff,mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by simp [U],by norm_num [d,realD,extend,edist_dist,Real.dist_eq]⟩
    · exact ⟨some 0,by simp [U],by norm_num [d,realD,extend,edist_dist,Real.dist_eq]⟩
    · exact ⟨some (-3),by simp [U],by norm_num [d,realD,extend,edist_dist,Real.dist_eq]⟩
    · exact ⟨some 0,by simp [U],by norm_num [d,realD,extend,edist_dist,Real.dist_eq]⟩
  have hu : U.Nonempty := ⟨some 0,by simp [U]⟩
  constructor
  · exact le_antisymm (by simpa using cover_le_net hn) (two_le_cover hu hmiss)
  · apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ (hu.image f.func))
    have ho : InternalEpsilonNet (d ()) (3/2) (f.func '' U) {some (-2)} := by
      norm_num [InternalEpsilonNet,U,Set.image_insert_eq,Set.image_singleton,Set.subset_def,
        f,liftOp,d,realD,extend,edist_dist,Real.dist_eq]
    simpa using cover_le_net ho
theorem entropy : ∃ h : DeltaDefined (d ()) (d ()) f.func (3/2) U,
    delta (d ()) (d ()) f.func (3/2) U h = 1 := by
  refine ⟨Or.inl (by rw [covers.1]; norm_num),?_⟩
  norm_num [delta,metric_entropy,covers.1,covers.2,log2_ereal,Real.logb_self_eq_one]
end Translation
end MG

namespace MG
open Set
open formal_oet.vol_01.ch_01_foundations
open scoped Classical

theorem Step.cover_counterexample (τ : ENNReal) (hτ : 0 < τ) (hτt : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < τ ∧
      ({some (-a),some a} : Set (Option ℝ)) ⊆ Step.U ∧
      covering_number (realD id) τ {some (-a),some a} = 1 ∧
      covering_number (realD id) (1/2) (Step.f.func '' {some (-a),some a}) = 2 := by
  obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hτ
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr
  let a : ℝ := min 1 ((r:ℝ)/4)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1 := min_le_left _ _
  have har : a ≤ (r:ℝ)/4 := min_le_right _ _
  have hd : ENNReal.ofReal (2*a) < τ := by
    apply lt_trans _ hr'
    rw [ENNReal.ofReal_lt_coe_iff (by positivity)]; linarith
  have hB : ({some (-a),some a} : Set (Option ℝ)) ⊆ Step.U := by
    intro x hx; rcases hx with rfl | rfl
    · exact ⟨-a,⟨by simpa [abs_neg,abs_of_pos ha] using ha1,neg_ne_zero.mpr ha.ne'⟩,rfl⟩
    · exact ⟨a,⟨by simpa [abs_of_pos ha] using ha1,ha.ne'⟩,rfl⟩
  refine ⟨a,ha,ha1,hd,hB,?_,?_⟩
  · apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some a,by simp⟩)
    have hn : InternalEpsilonNet (realD id) τ {some (-a),some a} {some (-a)} := by
      constructor
      · simp
      · intro x hx; rcases hx with rfl | rfl
        · exact ⟨some (-a),by simp,by simpa using hτ⟩
        · refine ⟨some (-a),by simp,?_⟩
          simpa [real_distance,show a-(-a)=2*a by ring,abs_of_pos (by positivity : 0 < 2*a)] using hd
    simpa using cover_le_net hn
  · have hi : Step.f.func '' ({some (-a),some a} : Set (Option ℝ)) = {some 0,some 1} := by
      simp [Set.image_insert_eq,Set.image_singleton,Step.f,liftOp,Step.s,show -a<0 by linarith,not_lt.mpr ha.le]
    rw [hi]
    have hc := separated_cover (a := realD id) (ε := 1/2) (by norm_num)
      (realD_legal id).dist_self ({some (0:ℝ),some 1} : Finset (Option ℝ))
      (by norm_num [real_distance])
    simpa using hc

namespace Four
def U : Set (Option ℝ) := {some 0,some 1,some 2,some 3}
noncomputable def f : Operator (Option ℝ) none :=
  ⟨fun x => if x ∈ U then x else none,by simp [U]⟩
noncomputable def g : Operator (Option ℝ) none :=
  ⟨fun x => if x=some 0 then some 0 else if x=some 1 then some 3 else
    if x=some 2 then some 1 else if x=some 3 then some 2 else none,by simp⟩
theorem legal : ExtendedPseudoMetric (Option ℝ) none (realD id) := realD_legal id
theorem data : U.Nonempty ∧ U.Finite ∧ U ⊆ dom f ∧ U ⊆ dom g ∧ f.func '' U = U ∧ g.func '' U = U := by
  refine ⟨⟨some 0,by simp [U]⟩,by simp [U],?_,?_,?_,?_⟩
  · intro x hx; change (if x ∈ U then x else none) ≠ none
    rw [if_pos hx]; simp only [U,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _
  · norm_num [U,Set.subset_def,dom,g,Option.some_ne_none]
  · norm_num [U,f,Set.image_insert_eq,Set.image_singleton]
  · norm_num [U,g,Set.image_insert_eq,Set.image_singleton]
    ext x; simp; tauto

theorem cover (ε : ENNReal) (hε : 0 < ε) :
    covering_number (realD id) ε U = if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1 := by
  by_cases h1 : ε ≤ 1
  · rw [if_pos h1]
    have h2 : ε ≤ 2 := h1.trans (by norm_num)
    have h3 : ε ≤ 3 := h1.trans (by norm_num)
    have hc := separated_cover hε legal.dist_self
      ({some (0:ℝ),some 1,some 2,some 3} : Finset (Option ℝ))
      (by norm_num [real_distance]; aesop)
    simpa [U] using hc
  · rw [if_neg h1]
    have hp : 1 < ε := lt_of_not_ge h1
    by_cases h2 : ε ≤ 2
    · rw [if_pos h2]
      have hn : InternalEpsilonNet (realD id) ε U {some 1,some 2} := by
        norm_num [InternalEpsilonNet,U,Set.subset_def,real_distance]; aesop
      apply le_antisymm (by simpa using cover_le_net hn)
      apply two_le_cover data.1
      intro c hc; simp only [U,mem_insert_iff,mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨some 3,by simp [U],by simpa using h2.trans (by norm_num : (2:ENNReal) ≤ 3)⟩
      · exact ⟨some 3,by simp [U],by norm_num [real_distance]; exact h2⟩
      · exact ⟨some 0,by simp [U],by norm_num [real_distance]; exact h2⟩
      · exact ⟨some 0,by simp [U],by simpa using h2.trans (by norm_num : (2:ENNReal) ≤ 3)⟩
    · rw [if_neg h2]
      have hp2 : 2 < ε := lt_of_not_ge h2
      have hn : InternalEpsilonNet (realD id) ε U {some 1} := by
        norm_num [InternalEpsilonNet,U,Set.subset_def,real_distance]; aesop
      exact le_antisymm (by simpa using cover_le_net hn) (one_le_covering_number_of_nonempty _ _ _ data.1)

theorem external_center : some (3/2:ℝ) ∉ U := by norm_num [U]
theorem same_images (ε : ENNReal) (hε : 0 < ε) :
    covering_number (realD id) ε (f.func '' U) = covering_number (realD id) ε U ∧
    covering_number (realD id) ε (g.func '' U) = covering_number (realD id) ε U ∧
    ∃ hf : DeltaDefined (realD id) (realD id) f.func ε U,
    ∃ hg : DeltaDefined (realD id) (realD id) g.func ε U,
      delta (realD id) (realD id) f.func ε U hf = 0 ∧ delta (realD id) (realD id) g.func ε U hg = 0 := by
  have hf := data.2.2.2.2.1
  have hg := data.2.2.2.2.2
  have hfin := finite_cover legal.dist_self data.2.1 hε
  obtain ⟨t,ht⟩ := entropy_finite data.1 hfin
  refine ⟨by rw [hf],by rw [hg],Or.inl hfin,Or.inl hfin,?_,?_⟩
  · simp [delta,hf,ht,← EReal.coe_sub]
  · simp [delta,hg,ht,← EReal.coe_sub]

theorem lips :
    (∀ x ∈ U, ∀ y ∈ U, realD id (f.func x) (f.func y) ≤ 1*realD id x y) ∧
    (∀ x ∈ U, ∀ y ∈ U, realD id (g.func x) (g.func y) ≤ 3*realD id x y) ∧
    (∀ L : ENNReal, (∀ x ∈ U, ∀ y ∈ U, realD id (f.func x) (f.func y) ≤ L*realD id x y) → 1 ≤ L) ∧
    (∀ L : ENNReal, (∀ x ∈ U, ∀ y ∈ U, realD id (g.func x) (g.func y) ≤ L*realD id x y) → 3 ≤ L) := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [U,f,real_distance]
  · norm_num [U,g,real_distance]
  · intro L h; have he := h (some 0) (by simp [U]) (some 1) (by simp [U])
    simpa [f,U,real_distance] using he
  · intro L h; have he := h (some 0) (by simp [U]) (some 1) (by simp [U])
    simpa [g,U,real_distance] using he

theorem estimates :
    covering_number (realD id) (7/4) (f.func '' U) = 2 ∧
    covering_number (realD id) (7/4) (g.func '' U) = 2 ∧
    covering_number (realD id) ((7/4)/1) U = 2 ∧
    covering_number (realD id) ((7/4)/3) U = 4 ∧
    covering_number (realD id) (7/4) (f.func '' U) ≤ covering_number (realD id) ((7/4)/1) U ∧
    covering_number (realD id) (7/4) (g.func '' U) ≤ covering_number (realD id) ((7/4)/3) U := by
  have hpos : (0:ENNReal) < 7/4 := ENNReal.div_pos (by norm_num) (by norm_num)
  have hn1 : ¬ (7/4:ENNReal) ≤ 1 := by rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num
  have hn2 : (7/4:ENNReal) ≤ 2 := by rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num
  have hn3 : ((7/4)/3:ENNReal) ≤ 1 := by
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num),ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_,?_,?_,?_,lip_cover (by norm_num) (by norm_num) lips.1,
    lip_cover (by norm_num) (by norm_num) lips.2.1⟩
  · rw [data.2.2.2.2.1,cover _ hpos,if_neg hn1,if_pos hn2]
  · rw [data.2.2.2.2.2,cover _ hpos,if_neg hn1,if_pos hn2]
  · simpa using (cover (7/4) hpos).trans (by rw [if_neg hn1,if_pos hn2])
  · rw [cover _ (ENNReal.div_pos hpos.ne' (by norm_num)),if_pos hn3]
end Four
end MG

namespace MG
open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
variable {X I : Type} {bot : X}

open scoped Classical

noncomputable def scaleFromNonempty
    (σ : I → {A : Set X // A.Nonempty} → ENNReal)
    (hσ : ∀ i (A B : {A : Set X // A.Nonempty}), A.val ⊆ B.val → σ i A ≤ σ i B) :
    InputScale X I where
  value i A := if h : A.Nonempty then σ i ⟨A,h⟩ else 0
  mono i A B hA hB h := by simpa only [dif_pos hA,dif_pos hB] using hσ i ⟨A,hA⟩ ⟨B,hB⟩ h
theorem scaleFromNonempty_eq
    (σ : I → {A : Set X // A.Nonempty} → ENNReal)
    (hσ : ∀ i (A B : {A : Set X // A.Nonempty}), A.val ⊆ B.val → σ i A ≤ σ i B)
    (i : I) (A : Set X) (hA : A.Nonempty) :
    (scaleFromNonempty σ hσ).value i A = σ i ⟨A,hA⟩ := by
  simp [scaleFromNonempty,hA]

theorem internal_ball_iff (a : X → X → ENNReal) (ε : ENNReal) (U : Set X) (S : Finset X) :
    InternalEpsilonNet a ε U S ↔ (S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball a c ε := by
  simp [InternalEpsilonNet,Set.subset_def,ball]

noncomputable def subfamilyDelta (d : I → X → X → ENNReal) (f : X → X)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : DeltaDefined (subfamily_pseudometric d Jin) (subfamily_pseudometric d Jout) f ε U) : EReal :=
  delta (subfamily_pseudometric d Jin) (subfamily_pseudometric d Jout) f ε U h
theorem subfamilyDelta_eq (d : I → X → X → ENNReal) (f : X → X)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : DeltaDefined (subfamily_pseudometric d Jin) (subfamily_pseudometric d Jout) f ε U) :
    subfamilyDelta d f U Jin Jout ε h = subfamily_metric_entropy d Jin ε U -
      subfamily_metric_entropy d Jout ε (f '' U) := rfl

theorem entropy_top_iff {a : X → X → ENNReal} {U : Set X} {ε : ENNReal} (hU : U.Nonempty) :
    metric_entropy a ε U = ⊤ ↔ covering_number a ε U = ⊤ := by
  have h0 : covering_number a ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty a ε U hU))
  by_cases ht : covering_number a ε U = ⊤ <;> simp [metric_entropy,log2_ereal,h0,ht]

theorem delta_infinite_input {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε : ENNReal}
    (hU : U.Nonempty) (ha : covering_number a ε U = ⊤) (hb : covering_number b ε (f '' U) < ⊤) :
    delta a b f ε U (Or.inr hb) = ⊤ := by
  obtain ⟨t,ht⟩ := entropy_finite (hU.image f) hb
  simp [delta,(entropy_top_iff hU).mpr ha,ht]
theorem delta_infinite_output {a b : X → X → ENNReal} {f : X → X} {U : Set X} {ε : ENNReal}
    (hU : U.Nonempty) (ha : covering_number a ε U < ⊤) (hb : covering_number b ε (f '' U) = ⊤) :
    delta a b f ε U (Or.inl ha) = ⊥ := by
  simp [delta,(entropy_top_iff (hU.image f)).mpr hb]

theorem separated_criteria (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : X → X) (U : Set X)
    (hf : ∀ x ∈ f '' U, ∀ y ∈ f '' U, GaugeZeroRelated d x y → x = y)
    (hg : ∀ x ∈ g '' U, ∀ y ∈ g '' U, GaugeZeroRelated d x y → x = y) :
    (Factors f g U ↔ QuotientFactors d hd f g U) ∧
    (Factors f g U ∧ Factors g f U ↔ QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U) := by
  have he1 := separated_relations d hd f U hf
  have he2 := separated_relations d hd g U hg
  constructor
  · rw [factors_iff,quotient_factors_iff,FiberLE,he1,he2]
  · rw [factors_both,quotient_factors_both,he1,he2]

theorem matrix_colip_delta [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I} {ε : ENNReal}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (ht : K i j < ⊤)
    (hTB : TotallyBounded (d i) U) (hε : 0 < ε) (hεt : ε < ⊤) :
    ∃ h : DeltaDefined (d i) (d j) f.func ε U,
      delta (d i) (d j) f.func ε U h ≤ metric_entropy (d i) ε U - metric_entropy (d i) (ε/K i j) U := by
  exact ⟨Or.inl (hTB _ hε hεt),EReal.sub_le_sub le_rfl (entropy_mono (matrix_colip_cover d hK hp ht))⟩
end MG
```

```toml filename=lakefile.toml
name = "mg_c003"
version = "0.1.1"
defaultTargets = ["Answer"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "formal_oet"
globs = ["formal_oet.+"]

[[lean_lib]]
name = "Answer"
roots = ["Main"]
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```python filename=build.py
import json, os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
cfg = json.loads((root / 'environment.json').read_text())
out = root / '.build'
out.mkdir(exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = str(out) + ':' + cfg['LEAN_PATH']
def run(f):
    p = pathlib.Path(f)
    target = out / p.with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    return subprocess.run([cfg['compiler'], '-o', str(target), str(p)], env=env).returncode
if not sys.argv[1:] or sys.argv[1:] == ['background']:
    files = ['ch_01_foundations/gauge_space', 'ch_01_foundations/operator_space',
             'ch_01_foundations/metric_entropy', 'ch_02_operator_bounds/lip_matrix',
             'ch_02_operator_bounds/decoupling', 'ch_02_operator_bounds/single_channel']
    for f in files:
        if run('formal_oet/vol_01/' + f + '.lean'): sys.exit(1)
    if not sys.argv[1:]: sys.exit(run('Main.lean'))
else:
    for f in sys.argv[1:]:
        if run(f): sys.exit(1)
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
          "file": "Main.lean",
          "name": "MG.Const"
        },
        {
          "file": "Main.lean",
          "name": "MG.Ident"
        },
        {
          "file": "Main.lean",
          "name": "MG.Active"
        },
        {
          "file": "Main.lean",
          "name": "MG.component_partition"
        }
      ],
      "representation": "以任意函数推广算子作用；代入Operator.func及U⊆dom即为正文。Ident显式排除Const，证明三集合覆盖且两两不交。",
      "dependencies": []
    },
    {
      "id": "CH03-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Fiber"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiber_representation"
        },
        {
          "file": "Main.lean",
          "name": "MG.subfamily_zero"
        }
      ],
      "representation": "Fiber使用各j∈J输出零距的合取；证明与冻结d_J上确界的零距定义相等，任意目标及空纤维均保留。",
      "dependencies": []
    },
    {
      "id": "CH03-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.EqRel"
        },
        {
          "file": "Main.lean",
          "name": "MG.ZeroRel"
        },
        {
          "file": "Main.lean",
          "name": "MG.imageSetoid"
        },
        {
          "file": "Main.lean",
          "name": "MG.ImageQuotient"
        },
        {
          "file": "Main.lean",
          "name": "MG.FiberLE"
        },
        {
          "file": "Main.lean",
          "name": "MG.relation_fiber"
        }
      ],
      "representation": "点对集包含两点属于U；像商是实际像集子类型上的Quotient，零距等价性由规范公理证明；预序为零距点对集包含。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.radius"
        },
        {
          "file": "Main.lean",
          "name": "MG.LegalRadius"
        },
        {
          "file": "Main.lean",
          "name": "MG.radius_sup"
        },
        {
          "file": "Main.lean",
          "name": "MG.legal_ball"
        }
      ],
      "representation": "先取输出非零距输入点的输入距离下确界，再证明恰等于全部有限正合法开球半径的上确界；空上确界为0，无上界可为top。",
      "dependencies": []
    },
    {
      "id": "CH03-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.uniform"
        },
        {
          "file": "Main.lean",
          "name": "MG.nullMatrix"
        }
      ],
      "representation": "uniform对A中的基点取点态半径下确界，U独立指定评估域；nullMatrix的参数顺序为输出行j、输入列i。",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.InputScale"
        },
        {
          "file": "Main.lean",
          "name": "MG.scaleFromNonempty"
        },
        {
          "file": "Main.lean",
          "name": "MG.scaleFromNonempty_eq"
        },
        {
          "file": "Main.lean",
          "name": "MG.diameter"
        },
        {
          "file": "Main.lean",
          "name": "MG.diameterScale"
        },
        {
          "file": "Main.lean",
          "name": "MG.threshold"
        },
        {
          "file": "Main.lean",
          "name": "MG.channelType"
        },
        {
          "file": "Main.lean",
          "name": "MG.threshold_cases"
        }
      ],
      "representation": "尺度在非空集合上的单调性为数据条件；给出从原文非空集合子类型到本表示的扩展及对应等式；Bool对表示两项0/1指标。",
      "dependencies": [
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.TotallyBounded"
        },
        {
          "file": "Main.lean",
          "name": "MG.internal_ball_iff"
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
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"
        }
      ],
      "representation": "直接采用冻结内部覆盖数和以2为底的EReal熵；internal_ball_iff证明有限内网等于内部开球覆盖，全有界量化所有有限正半径。",
      "dependencies": []
    },
    {
      "id": "CH03-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.DeltaDefined"
        },
        {
          "file": "Main.lean",
          "name": "MG.delta"
        },
        {
          "file": "Main.lean",
          "name": "MG.subfamilyDelta"
        },
        {
          "file": "Main.lean",
          "name": "MG.subfamilyDelta_eq"
        },
        {
          "file": "Main.lean",
          "name": "MG.entropy_top_iff"
        },
        {
          "file": "Main.lean",
          "name": "MG.delta_infinite_input"
        },
        {
          "file": "Main.lean",
          "name": "MG.delta_infinite_output"
        }
      ],
      "representation": "熵差要求至少一端覆盖数有限的证明参数；子族表示等于原文两熵相减，并证明单端无穷时分别为正、负无穷。",
      "dependencies": [
        "CH03-D07",
        "CH03-P22-01"
      ]
    },
    {
      "id": "CH03-P01-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.const_zero_row"
        }
      ],
      "representation": "常值输出为0，任意有限指标集的零行求和为0。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.const_colip"
        }
      ],
      "representation": "在U中的正输入距离见证上应用冻结co-Lip单条目零值引理，系数允许无穷。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.ident_isometry"
        },
        {
          "file": "Main.lean",
          "name": "MG.zero_transport"
        }
      ],
      "representation": "由输出与输入逐点零距和双向三角不等式证明每个点对距离相等。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P02-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.active_comp"
        }
      ],
      "representation": "两步复合的有效集合包含于内步U及外步f(U)的有效集合之并；逐一处理常值/恒等分支。",
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
          "file": "Main.lean",
          "name": "MG.run"
        },
        {
          "file": "Main.lean",
          "name": "MG.stepActive"
        },
        {
          "file": "Main.lean",
          "name": "MG.LegalChain"
        },
        {
          "file": "Main.lean",
          "name": "MG.chain_domains"
        },
        {
          "file": "Main.lean",
          "name": "MG.active_chain"
        }
      ],
      "representation": "列表按实际执行顺序表示任意有限链；递归像域，证明全部中间域合法以及有效集合包含，空列表是恒等且有效集合为空。",
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
          "file": "Main.lean",
          "name": "MG.ident_comp"
        }
      ],
      "representation": "输出到输入的零距由传递性得到，借外侧保距排除复合常值，保留常值优先规则。",
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
          "file": "Main.lean",
          "name": "MG.Swap.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Swap.data"
        },
        {
          "file": "Main.lean",
          "name": "MG.Swap.reverse_inclusions_fail"
        }
      ],
      "representation": "Option Bool编码bot,a,b；合法离散扩展距离、两步换位及像域U，完整计算分量集合并证明两条反向包含均失败。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.outer_const"
        }
      ],
      "representation": "对两个U中输入，外侧常值条件直接用于实际像域中的像点。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Seven.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Seven.data"
        }
      ],
      "representation": "Option(Fin 6)编码七点；false分量只合并p=2,q=3，true为离散分量，验证复合域、内侧常值、复合非恒零及另一分量可区分。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P05-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.inner_const_lip"
        }
      ],
      "representation": "实际像域上的Lip矩阵指定行仅含对角输入；通过冻结单行化简及ENNReal乘零，允许无限系数。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P06-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_target"
        },
        {
          "file": "Main.lean",
          "name": "MG.subfamily_zero"
        }
      ],
      "representation": "任意目标在d_J下零距等价于全部J分量零距，双向传递得到纤维相等。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiber_cover"
        }
      ],
      "representation": "像点作为目标的纤维含相应原像，全部这些纤维之并恰为U，包括U空集。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_equal_or_disjoint"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiber_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiber_cover"
        }
      ],
      "representation": "交点使两个目标在J中零距，故相等，否则不交；加上非空与覆盖构成去重后的分划。",
      "dependencies": [
        "CH03-D02",
        "CH03-P06-01"
      ]
    },
    {
      "id": "CH03-P06-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_inter"
        }
      ],
      "representation": "J非空保证交集中仍包含U条件，得到单分量纤维交集等式；适用于有限非空子族。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_antitone"
        }
      ],
      "representation": "从K中的各分量零距限制到J⊆K，得到反向纤维包含。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-06",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_singleton"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiber_full"
        }
      ],
      "representation": "证明singleton子族的原始距离集合公式及全子族向每个单分量的包含。",
      "dependencies": [
        "CH03-D02",
        "CH03-P06-05"
      ]
    },
    {
      "id": "CH03-P06-07",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_ident"
        }
      ],
      "representation": "对任意目标，用恒等分量的逐点零距证明输出零距等价于输入零距。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P01-03",
        "CH03-P06-06"
      ]
    },
    {
      "id": "CH03-P06-08",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_const"
        }
      ],
      "representation": "像目标的纤维为U；距该目标严格为正的任意目标纤维为空，涵盖无限正距离。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P06-06"
      ]
    },
    {
      "id": "CH03-P07-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.factors_iff"
        }
      ],
      "representation": "Factors是实际像子类型到X的函数满足规定赋值；必要性由同一函数保相等得到。",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P07-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.factor_surjective"
        },
        {
          "file": "Main.lean",
          "name": "MG.imageMap"
        },
        {
          "file": "Main.lean",
          "name": "MG.imageMap_surjective"
        },
        {
          "file": "Main.lean",
          "name": "MG.factors_iff"
        }
      ],
      "representation": "从像映射的满射性选择原像，关系包含保证赋值与代表元无关；无Nonempty U假设，空像也构造函数。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.factors_both"
        }
      ],
      "representation": "两个方向分别应用构造判据，再用集合反对称性得到关系相等充要条件。",
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
          "file": "Main.lean",
          "name": "MG.factor_lip"
        }
      ],
      "representation": "T取实际像子类型为定义域，任取两像点选原像；正有限K可除，有限非负L给出L/K的像域Lip界。",
      "dependencies": [
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P08-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.quotientMap"
        },
        {
          "file": "Main.lean",
          "name": "MG.quotientMap_surjective"
        },
        {
          "file": "Main.lean",
          "name": "MG.quotient_factors_iff"
        }
      ],
      "representation": "在实际像零距商中构造满射并应用选代表元的因子化；Quotient.sound/exact证明规定赋值与关系包含的双向等价。",
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
          "file": "Main.lean",
          "name": "MG.quotient_factors_both"
        }
      ],
      "representation": "双向商映射的规定公式存在当且仅当两个零距点对集相等。",
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
          "file": "Main.lean",
          "name": "MG.separated_relations"
        },
        {
          "file": "Main.lean",
          "name": "MG.separated_criteria"
        }
      ],
      "representation": "只要求f(U)、g(U)各自在规范族中分离；证明各自点值关系等于零距关系以及单、双向判据一致。",
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
          "file": "Main.lean",
          "name": "MG.fiberLE_refl"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiberLE_trans"
        }
      ],
      "representation": "固定同一U，零距点对集包含的自反性与传递性。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.relation_chain"
        }
      ],
      "representation": "对任意有限长度m及0≤a≤b≤m证明逐步集合包含传至R_a⊆R_b；取R_k=ZeroRel即原文。",
      "dependencies": []
    },
    {
      "id": "CH03-P09-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.relation_chain_strict"
        }
      ],
      "representation": "任一步严格包含的差集点传至R_m\\R_0，同时证明端点严格包含；有限链长度和步号均量化。",
      "dependencies": [
        "CH03-P09-02"
      ]
    },
    {
      "id": "CH03-P10-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Step.f"
        },
        {
          "file": "Main.lean",
          "name": "MG.Step.U"
        },
        {
          "file": "Main.lean",
          "name": "MG.Step.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Step.domain"
        }
      ],
      "representation": "Option ℝ表示带吸收元实线；阶跃函数保持none，证明U等于原文两个半开区间的像、非空且属于定义域。",
      "dependencies": [
        "CH03-P17-04"
      ]
    },
    {
      "id": "CH03-P10-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Step.point"
        },
        {
          "file": "Main.lean",
          "name": "MG.Step.legal_radii"
        }
      ],
      "representation": "对同一U每个some y，证明半径=ofReal|y|且正，合法有限正r恰满足r≤|y|；上界用异号且接近零的显式点。",
      "dependencies": [
        "CH03-D04",
        "CH03-P10-01",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P10-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Step.uniform_zero"
        }
      ],
      "representation": "选择min(1,r/2)的趋零正基点，利用点态半径公式证明固定U上的下确界为0。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P10-01",
        "CH03-P10-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P11-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_const_family"
        }
      ],
      "representation": "J中每个输出分量常值时，对每个y∈U证明以f(y)为目标的J纤维等于U。",
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
          "file": "Main.lean",
          "name": "MG.const_family_radius"
        },
        {
          "file": "Main.lean",
          "name": "MG.radius_top"
        },
        {
          "file": "Main.lean",
          "name": "MG.uniform_top"
        }
      ],
      "representation": "全部输出零距使所有有限正半径合法；任意输入分量的每点半径和统一半径均为top。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-D04",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P11-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Infinite.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Infinite.data"
        }
      ],
      "representation": "合法Option Bool两点域：输入false分量距离top，输出j=false或true分别覆盖i=j与i≠j；恒等算子统一半径top而非常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P12-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_ident_image"
        }
      ],
      "representation": "恒等分量保距给出像目标纤维正是基点的输入零距类。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P01-03",
        "CH03-P06-06"
      ]
    },
    {
      "id": "CH03-P12-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.ident_radius_lower"
        }
      ],
      "representation": "原文有限正r及受限球包含输入零距类，结合保距，证明r≤点态零化半径并保留r>0。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-P01-03"
      ]
    },
    {
      "id": "CH03-P13-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.radius_family"
        },
        {
          "file": "Main.lean",
          "name": "MG.finite_inf_min"
        }
      ],
      "representation": "证明子族点态半径等于各单分量半径的下确界，有限非空J上该值由某个分量取得，因此是最小值。",
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
          "file": "Main.lean",
          "name": "MG.uniform_family"
        },
        {
          "file": "Main.lean",
          "name": "MG.finite_inf_min"
        },
        {
          "file": "Main.lean",
          "name": "MG.nullMatrix"
        }
      ],
      "representation": "证明基点与输出子族两重下确界可交换，并用有限非空最小值的取得性对应零化矩阵指定列的最小条目。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04",
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P13-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.uniform_family_antitone"
        }
      ],
      "representation": "由统一子族公式，对更大输出指标集取下确界不会增大。",
      "dependencies": [
        "CH03-D05",
        "CH03-P13-02"
      ]
    },
    {
      "id": "CH03-P14-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.fiber_truncation"
        }
      ],
      "representation": "纤维成员的输出反向零距经对称性得到所需顺序的输出零距。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P14-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.extract_legal_radius"
        },
        {
          "file": "Main.lean",
          "name": "MG.radius_zero"
        },
        {
          "file": "Main.lean",
          "name": "MG.fiber_truncation"
        }
      ],
      "representation": "严格小于点态半径时选取夹在其间的有限NNReal半径，验证合法，再由球包含及输入/输出对称性得到零距。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-P14-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.composite_truncation"
        }
      ],
      "representation": "保留上游定义域及两像点属于指定下游U的条件，在复合算子中代入单分量纤维判据。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P15-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.uniform_comp_zero"
        }
      ],
      "representation": "下游零距保持只量化实际像f(U)，统一半径以下的上游零距传至复合，得到原文下界。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P15-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.uniform_comp_lip"
        }
      ],
      "representation": "正有限ENNReal L下直接证明所有严格低于下游统一半径/L的输入对零化；0与top右端由同一有序代数证明涵盖。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P16-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.threshold_cases"
        },
        {
          "file": "Main.lean",
          "name": "MG.threshold_exhaustive"
        }
      ],
      "representation": "给出Bool×Bool四个值与原文四组互补不等式的充要条件及分类值唯一性。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.scale_threshold_mono"
        }
      ],
      "representation": "对所有s及τ≤τ′证明s<τ推出s<τ′，逐通道给出第一项为1的集合单调不减。",
      "dependencies": []
    },
    {
      "id": "CH03-P16-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.null_threshold_antitone"
        }
      ],
      "representation": "对所有r及τ≤τ′证明τ′≤r推出τ≤r，逐通道给出第二项为1的集合单调不增。",
      "dependencies": []
    },
    {
      "id": "CH03-P17-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.scale_restrict"
        }
      ],
      "representation": "任意输入尺度族，在非空B⊆A时尺度不增并传递严格阈值判断。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.radius_restrict"
        }
      ],
      "representation": "固定任意基点，A上每个零化输入球在B⊆A上仍零化，证明点态半径不减；特别涵盖基点在B。",
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
          "file": "Main.lean",
          "name": "MG.uniform_restrict"
        }
      ],
      "representation": "同时缩小评估域及基点集合，由严格阈值的零距刻画证明统一半径不减。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P17-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.realD_legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.scale_reverse_counterexample"
        },
        {
          "file": "Main.lean",
          "name": "MG.scale_reverse_domain"
        }
      ],
      "representation": "合法带吸收元实线上，B={0}⊆A={0,1}的直径分别为0、1，阈值1/2否定反向判断；恒等算子的作用不影响该尺度计算。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P18-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.uniform_zero"
        },
        {
          "file": "Main.lean",
          "name": "MG.uniform_le_point"
        }
      ],
      "representation": "统一下确界不超过指定基点半径，因此严格低于统一半径的输入距离对应输出零距。",
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
          "file": "Main.lean",
          "name": "MG.separation_lower"
        }
      ],
      "representation": "输出严格正距离与零距结论矛盾，推出输入距离至少为统一半径。",
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
          "file": "Main.lean",
          "name": "MG.separation_witness"
        }
      ],
      "representation": "每个α大于统一半径即存在违反零距球条件的两点，再在0与正输出距离间选有限NNReal ε，涵盖输出top。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P19-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.threshold_fiber"
        }
      ],
      "representation": "对y∈A及半径τ≤统一半径，严格输入球与A的交集逐点属于以f(y)为目标的单分量纤维。",
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
          "file": "Main.lean",
          "name": "MG.net_push"
        },
        {
          "file": "Main.lean",
          "name": "MG.cover_push"
        },
        {
          "file": "Main.lean",
          "name": "MG.threshold_cover"
        }
      ],
      "representation": "任意B⊆A的有限内部中心S推至f(S)，证明合法输出内覆盖及card不增，取下确界统一包含B空集和无有限输入覆盖。",
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
          "file": "Main.lean",
          "name": "MG.log_mono"
        },
        {
          "file": "Main.lean",
          "name": "MG.entropy_mono"
        },
        {
          "file": "Main.lean",
          "name": "MG.threshold_entropy"
        }
      ],
      "representation": "证明扩展log2单调，由阈值覆盖数不等式推出原文熵不等式，特别适用于非空B。",
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
          "file": "Main.lean",
          "name": "MG.Step.cover_counterexample"
        }
      ],
      "representation": "对每个正有限τ显式选择a=min(1,r/4)，同一阶跃U内B={-a,a}满足2a<τ；内部输入覆盖数恰1，输出在1/2处恰2。",
      "dependencies": [
        "CH03-D07",
        "CH03-P10-01",
        "CH03-P17-04"
      ]
    },
    {
      "id": "CH03-P21-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.small_domain_iff"
        }
      ],
      "representation": "精确使用diam(A)<τs≤τn；统一半径阈值推出所有输出零距，反向证明半径top，结论双向。",
      "dependencies": [
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
          "file": "Main.lean",
          "name": "MG.const_cover"
        },
        {
          "file": "Main.lean",
          "name": "MG.cover_one"
        }
      ],
      "representation": "对非空像集构造单点内部中心及非空覆盖数下界；将等价条件的输出零距代入，任意正ε覆盖数为1。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P22-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.finite_cover"
        },
        {
          "file": "Main.lean",
          "name": "MG.entropy_finite"
        },
        {
          "file": "Main.lean",
          "name": "MG.finite_delta"
        }
      ],
      "representation": "非空有限集及像集由自身中心覆盖；证明覆盖数≥1且有限、两熵为实数及差值等于实数差，复合子族伪度量自距零后即可代入。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P23-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.const_entropy_delta"
        }
      ],
      "representation": "输出常值分量以1个内部中心覆盖，输出熵0，差值定义前提自动成立且差值等于任意有限或无穷输入熵。",
      "dependencies": [
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
          "file": "Main.lean",
          "name": "MG.ident_isometry"
        },
        {
          "file": "Main.lean",
          "name": "MG.net_push"
        },
        {
          "file": "Main.lean",
          "name": "MG.net_pull"
        },
        {
          "file": "Main.lean",
          "name": "MG.isometry_cover"
        }
      ],
      "representation": "恒等分量先导出点对保距；前向推中心，反向逐输出中心选原像，得到两覆盖数及熵相等。",
      "dependencies": [
        "CH03-D01",
        "CH03-D07",
        "CH03-P01-03",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P23-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.isometry_delta"
        }
      ],
      "representation": "在DeltaDefined前提下，覆盖数相等迫使两端均有限；用实数表示证明差0，不采用top-top。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P22-01",
        "CH03-P23-02"
      ]
    },
    {
      "id": "CH03-P24-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.lip_cover"
        },
        {
          "file": "Main.lean",
          "name": "MG.net_push"
        }
      ],
      "representation": "正有限L保证距离<ε/L推出像距<ε；内部中心的像给出输出覆盖且基数不增，得到原文覆盖数上界。",
      "dependencies": [
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P24-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.lip_delta"
        },
        {
          "file": "Main.lean",
          "name": "MG.entropy_finite"
        }
      ],
      "representation": "全有界保证ε及ε/L输入覆盖数有限，Lip覆盖界保证输出有限；扩展实数减法单调性给出原文熵差下界。",
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
          "file": "Main.lean",
          "name": "MG.matrix_colip_cover"
        },
        {
          "file": "Main.lean",
          "name": "MG.colip_cover"
        },
        {
          "file": "Main.lean",
          "name": "MG.net_pull"
        }
      ],
      "representation": "从合法co-Lip矩阵取指定单项下界，正有限条目允许除法；选每个输出内中心的输入代表元，证明输入覆盖及基数不增。",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P25-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.matrix_colip_delta"
        },
        {
          "file": "Main.lean",
          "name": "MG.colip_delta"
        },
        {
          "file": "Main.lean",
          "name": "MG.entropy_finite"
        }
      ],
      "representation": "输入全有界保证定义熵差所需的有限输入端；允许输出top，原文上界由覆盖数下界和EReal减法单调性推出。",
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
          "file": "Main.lean",
          "name": "MG.Affine.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Affine.first"
        },
        {
          "file": "Main.lean",
          "name": "MG.realD_apply"
        }
      ],
      "representation": "Option ℝ和绝对值读数的合法扩展伪度量；φ(x)=2x-1，原U={0,1}内首步目标纤维为U且分量常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P06-08",
        "CH03-P17-04"
      ]
    },
    {
      "id": "CH03-P26-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Affine.second"
        }
      ],
      "representation": "仍在原U={0,1}上，φ²(0)目标纤维为{0}，两个输出读数为3与1，分量为有效；证明复合域合法。",
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
          "file": "Main.lean",
          "name": "MG.point_constant_square"
        }
      ],
      "representation": "对任意在U点值恒为非吸收c的算子，自复合统一取f(c)；若f(c)非吸收则U仍合法，若吸收则U与复合定义域不交。",
      "dependencies": []
    },
    {
      "id": "CH03-P27-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.colip_point_gap"
        }
      ],
      "representation": "正co-Lip条目反射输出零距，与点态半径以下归零合用，排除任何严格介于0与点态半径的输入距离；K允许top。",
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
          "file": "Main.lean",
          "name": "MG.colip_uniform_gap"
        }
      ],
      "representation": "任意输入点对距离为0或至少统一半径；由点态间隙及统一半径≤每点半径证明，特别适用正统一半径。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P18-01",
        "CH03-P27-01"
      ]
    },
    {
      "id": "CH03-P28-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Translation.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Translation.domain"
        },
        {
          "file": "Main.lean",
          "name": "MG.Translation.fibers"
        },
        {
          "file": "Main.lean",
          "name": "MG.realD_apply"
        }
      ],
      "representation": "合法绝对值读数实线与平移x+1；完整去重纤维分划分别为{-3},{-2,2},{0}和{-3},{-2,0},{2}。",
      "dependencies": [
        "CH03-D02",
        "CH03-P17-04"
      ]
    },
    {
      "id": "CH03-P28-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Translation.covers"
        },
        {
          "file": "Main.lean",
          "name": "MG.Translation.entropy"
        }
      ],
      "representation": "精确3/2处输入内部覆盖数2、输出1；构造中心及逐中心不能单覆盖的下界，熵差为1。",
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
          "file": "Main.lean",
          "name": "MG.Floor.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.domain"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.first"
        }
      ],
      "representation": "合法通常实线与取整算子，[0,1/2]直径1/2、统一半径top，分类(true,true)=(1,1)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P11-02",
        "CH03-P17-04"
      ]
    },
    {
      "id": "CH03-P29-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Floor.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.domain"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.second"
        }
      ],
      "representation": "[9/10,11/10]直径1/5；从1左侧趋近的跨取整点对使统一半径0，分类(1,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P17-04",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P29-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Floor.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.domain"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.third"
        }
      ],
      "representation": "{0,2}直径2，正输入距离间隙给统一半径下界2，实际非零输出点对给上界2，分类(0,1)。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P17-04",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P29-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Floor.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.domain"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.fourth"
        }
      ],
      "representation": "[0,2]直径2；跨整数1的任意小距离点对使统一半径0，分类(0,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P17-04",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P29-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Floor.counterexample"
        },
        {
          "file": "Main.lean",
          "name": "MG.Floor.third"
        }
      ],
      "representation": "非空合法域{0,2}具有半径2≥1而输出0、2不零距；third的下界证明展示输入距离间隙是正半径来源。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P30-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Four.legal"
        },
        {
          "file": "Main.lean",
          "name": "MG.Four.cover"
        },
        {
          "file": "Main.lean",
          "name": "MG.Four.external_center"
        }
      ],
      "representation": "所有正ε的内部覆盖数：ε≤1为4，1<ε≤2为2，ε>2为1；包含开球端点，并证明3/2不属于U故不能作为内部中心。",
      "dependencies": [
        "CH03-D07",
        "CH03-P17-04",
        "CH03-P30-02"
      ]
    },
    {
      "id": "CH03-P30-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Four.data"
        },
        {
          "file": "Main.lean",
          "name": "MG.Four.same_images"
        }
      ],
      "representation": "构造原文两张取值表，域外均吸收，验证两像集均为U；全部正精度覆盖数相同且两熵差均0。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P22-01",
        "CH03-P30-01"
      ]
    },
    {
      "id": "CH03-P30-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Four.lips"
        }
      ],
      "representation": "逐点验证f,g的标量Lip界1、3，再用0与1这对输入分别证明任意合法L≥1、L≥3，得到最优值。",
      "dependencies": []
    },
    {
      "id": "CH03-P30-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "MG.Four.estimates"
        }
      ],
      "representation": "在7/4将通用lip_cover分别代入L=1与3，真实两输出覆盖数均2；输入上界分别2与4，故前者取等，后者严格宽松。",
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

