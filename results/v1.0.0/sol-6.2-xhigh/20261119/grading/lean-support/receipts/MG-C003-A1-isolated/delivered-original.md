# MG-C003 v0.1.1 · 第 3 章 Lean 答卷

入口为 `Main.lean`。项目在 Lean 4.29.1 （`f72c35b3f637c8c6571d353742168ab66cc22c00`）与 mathlib （`5e932f97dd25535344f80f9dd8da3aab83df0fe6`）下完整编译。对项目与冻结依赖的声明递归检查公理，所用逻辑公理仅有 `propext`、`Classical.choice`、`Quot.sound`。`alignment.json` 的依赖根据编译后声明实际引用的常量提取。

```lean filename=Main.lean
/-
Formalization of Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, v1.0.0, Chapter 3. ORCID 0009-0006-6536-3453.
https://glenzli.com/books/oet/
https://gitlab.com/glenzli/oet-public
https://doi.org/10.5281/zenodo.21457931
Source licensed under CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
This project reformulates the chapter in Lean and supplies machine-checked proofs.
-/
import Chapter.Components
import Chapter.Fibers
import Chapter.Radius
import Chapter.Cover
import Chapter.Models
import Chapter.Step
import Chapter.Floor
import Chapter.Readouts
import Chapter.Rearrange
import Chapter.Representations
```

```lean filename=Chapter/Components.lean
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U : Set X} {i j : I}

def Const (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def Ident (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Const d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def Active (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Set I :=
  (Const d f U ∪ Ident d f U)ᶜ

theorem partition (_hU : U ⊆ dom f) :
    Const d f U ∪ Ident d f U ∪ Active d f U = Set.univ ∧
    Disjoint (Const d f U) (Ident d f U) ∧
    Disjoint (Const d f U) (Active d f U) ∧
    Disjoint (Ident d f U) (Active d f U) := by
  classical
  refine ⟨Set.union_compl_self _, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun _ hc hi => hi.1 hc
  · exact Set.disjoint_left.mpr fun _ hc ha => ha (Or.inl hc)
  · exact Set.disjoint_left.mpr fun _ hi ha => ha (Or.inr hi)

theorem const_zero_row [Fintype I] (_hU : U ⊆ dom f) (hc : i ∈ Const d f U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (f.func x) (f.func y) ≤ ∑ k : I, 0 * d k x y := by
  intro x hx y hy
  simp [hc x hx y hy]

theorem const_colip [Fintype I] {K : I → I → ℝ≥0∞}
    (hc : i ∈ Const d f U) (hK : IsCoLipMatrix d f U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d j x y) : K j i = 0 := by
  obtain ⟨x, hx, y, hy, h⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K j i x y hK hx hy (hc x hx y hy) h

theorem zero_left {D : X → X → ℝ≥0∞} (hD : ExtendedPseudoMetric X bot D)
    {a b : X} (h : D a b = 0) (c : X) : D a c = D b c := by
  have p := hD.triangle a b c
  have q := hD.triangle b a c
  rw [h, zero_add] at p
  rw [hD.symm b a, h, zero_add] at q
  exact le_antisymm p q

theorem ident_distance (hd : ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f) (hi : i ∈ Ident d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  rw [zero_left hd (hi.2 x hx), hd.symm x, zero_left hd (hi.2 y hy), hd.symm y]

@[simp] theorem mul_func (f g : Operator X bot) (x : X) :
    (g * f).func x = g.func (f.func x) := rfl

theorem stage_domains (hU : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx h
    exact hU hx (show g.func (f.func x) = bot by rw [h, g.preserves_bot])
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem outer_const (_hU : U ⊆ dom (g * f)) (hc : i ∈ Const d g (f.func '' U)) :
    i ∈ Const d (g * f) U :=
  fun x hx y hy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem ident_comp (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom (g * f)) :
    Ident d f U ∩ Ident d g (f.func '' U) ⊆ Ident d (g * f) U := by
  rintro i ⟨hf, hg⟩
  have himg (x : X) (hx : x ∈ U) : f.func x ∈ f.func '' U := ⟨x, hx, rfl⟩
  refine ⟨fun hc => hf.1 ?_, ?_⟩
  · intro x hx y hy
    rw [← ident_distance (hd i) (stage_domains hU).2 hg _ (himg x hx) _ (himg y hy)]
    exact hc x hx y hy
  · intro x hx
    exact (zero_left (hd i) (hg.2 _ (himg x hx)) x).trans (hf.2 x hx)

theorem active_comp (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom (g * f)) :
    Active d (g * f) U ⊆ Active d f U ∪ Active d g (f.func '' U) := by
  classical
  intro i ha
  by_contra h
  have hf : i ∈ Const d f U ∨ i ∈ Ident d f U := by
    by_contra hh
    exact h (Or.inl hh)
  have hg : i ∈ Const d g (f.func '' U) ∨ i ∈ Ident d g (f.func '' U) := by
    by_contra hh
    exact h (Or.inr hh)
  rcases hg with hg | hg
  · exact ha (Or.inl (outer_const hU hg))
  · rcases hf with hf | hf
    · apply ha
      left
      intro x hx y hy
      exact (ident_distance (hd i) (stage_domains hU).2 hg _ ⟨x, hx, rfl⟩
        _ ⟨y, hy, rfl⟩).trans (hf x hx y hy)
    · exact ha (Or.inr (ident_comp hd hU ⟨hf, hg⟩))

def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: tail => chain tail * f

def stepActive (d : I → X → X → ℝ≥0∞) :
    List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: tail, U => Active d f U ∪ stepActive d tail (f.func '' U)

theorem chain_representation (fs : List (Operator X bot)) :
    chain fs = OperatorChain fs.reverse := by
  rw [operator_chain_eq_prod]
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [chain, ih, List.reverse_cons, List.prod_append]

theorem chain_active (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (fs : List (Operator X bot)) (U : Set X) (hU : U ⊆ dom (chain fs)) :
    Active d (chain fs) U ⊆ stepActive d fs U := by
  classical
  induction fs generalizing U with
  | nil =>
    intro i ha
    by_cases hc : i ∈ Const d (chain ([] : List (Operator X bot))) U
    · exact False.elim (ha (Or.inl hc))
    · exact False.elim (ha (Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩))
  | cons f fs ih =>
    intro i hi
    rcases active_comp hd hU hi with h | h
    · exact Or.inl h
    · exact Or.inr (ih _ (stage_domains hU).2 h)

theorem inner_const_of_row [Fintype I] {L : I → I → ℝ≥0∞}
    (_hU : U ⊆ dom (g * f)) (hc : j ∈ Const d f U)
    (hL : IsLipMatrix d g (f.func '' U) L) (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ Const d (g * f) U := by
  intro x hx y hy
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
    _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [hc x hx y hy, mul_zero] at h
  exact nonpos_iff_eq_zero.mp h

end Chapter
```

```lean filename=Chapter/Cover.lean
import Chapter.Radius
import Mathlib.Data.EReal.Operations

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f : Operator X bot} {U A B : Set X} {i j : I}
variable {P Q : X → X → ℝ≥0∞} {r s : ℝ≥0∞}

theorem net_iff_ball_cover {S : Finset X} :
    InternalEpsilonNet P r U S ↔ ↑S ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball P c r := by
  simp [InternalEpsilonNet, Set.subset_def, ball]

def TotallyBoundedAt (P : X → X → ℝ≥0∞) (U : Set X) : Prop :=
  ∀ r, FinitePositive r → covering_number P r U < ⊤

theorem total_iff_nets :
    TotallyBoundedAt P U ↔ ∀ r, FinitePositive r →
      ∃ S, InternalEpsilonNet P r U S := by
  classical
  unfold TotallyBoundedAt
  constructor <;> intro h r hr
  · by_contra hn
    exact (h r hr).ne ((covering_number_eq_top_iff P r U).mpr hn)
  · exact lt_top_iff_ne_top.mpr fun he => (covering_number_eq_top_iff P r U).mp he (h r hr)

theorem cover_le_card {S : Finset X} (h : InternalEpsilonNet P r U S) :
    covering_number P r U ≤ S.card :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem card_lower_cover {n : ℕ} (h : ∀ S, InternalEpsilonNet P r U S → n ≤ S.card) :
    (n : ℝ≥0∞) ≤ covering_number P r U :=
  le_iInf fun S => le_iInf fun hs => by exact_mod_cast h S hs

theorem cover_single_center (hy : ∃ y ∈ U, ∀ x ∈ U, P x y < r) :
    covering_number P r U = 1 := by
  classical
  obtain ⟨y,hy,h⟩ := hy
  have hn : InternalEpsilonNet P r U {y} := by
    refine ⟨by simpa, fun x hx => ⟨y,Finset.mem_singleton_self _, h x hx⟩⟩
  apply le_antisymm
  · simpa using cover_le_card hn
  · exact one_le_covering_number_of_nonempty _ _ _ ⟨y,hy⟩

theorem cover_finite (hU : U.Finite) (hP : ∀ x ∈ U, P x x = 0) (hr : 0 < r) :
    covering_number P r U < ⊤ := by
  classical
  have hn : InternalEpsilonNet P r U hU.toFinset := by
    refine ⟨by simp, fun x hx => ⟨x, hU.mem_toFinset.mpr hx, ?_⟩⟩
    rwa [hP x hx]
  exact (cover_le_card hn).trans_lt (ENNReal.natCast_lt_top _)

theorem cover_push (F : X → X)
    (h : ∀ x ∈ U, ∀ c ∈ U, P x c < r → Q (F x) (F c) < s) :
    covering_number Q s (F '' U) ≤ covering_number P r U := by
  classical
  refine le_iInf fun S => le_iInf fun hS => ?_
  have hn : InternalEpsilonNet Q s (F '' U) (S.image F) := by
    constructor
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x,hS.1 hx,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨c,hc,hxc⟩ := hS.2 x hx
      exact ⟨F c,Finset.mem_image_of_mem _ hc,h x hx c (hS.1 hc) hxc⟩
  exact (cover_le_card hn).trans (by exact_mod_cast Finset.card_image_le)

theorem cover_pull (F : X → X)
    (h : ∀ x ∈ U, ∀ c ∈ U, Q (F x) (F c) < s → P x c < r) :
    covering_number P r U ≤ covering_number Q s (F '' U) := by
  classical
  refine le_iInf fun T => le_iInf fun hT => ?_
  have pre (t : T) : ∃ x ∈ U, F x = (t : X) := hT.1 t.2
  let pick (t : T) := (pre t).choose
  have pick_mem (t : T) : pick t ∈ U := (pre t).choose_spec.1
  have pick_eq (t : T) : F (pick t) = (t : X) := (pre t).choose_spec.2
  have hn : InternalEpsilonNet P r U (T.attach.image pick) := by
    constructor
    · intro c hc
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hc
      exact pick_mem t
    · intro x hx
      obtain ⟨t,ht,hxt⟩ := hT.2 (F x) ⟨x,hx,rfl⟩
      refine ⟨pick ⟨t,ht⟩,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),
        h x hx _ (pick_mem ⟨t,ht⟩) ?_⟩
      rwa [pick_eq]
  exact (cover_le_card hn).trans (by
    exact_mod_cast (Finset.card_image_le (s := T.attach) (f := pick)).trans_eq Finset.card_attach)

theorem log2_mono : Monotone log2_ereal := by
  intro a b h
  by_cases ha : a = 0
  · simp [log2_ereal, ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal, hb]
  have hb0 : b ≠ 0 := fun he => ha (nonpos_iff_eq_zero.mp (he ▸ h))
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hb h
  simp only [log2_ereal, if_neg ha, if_neg hb0, if_neg hat, if_neg hb, EReal.coe_le_coe_iff]
  exact Real.logb_le_logb_of_le (by norm_num) (ENNReal.toReal_pos ha hat)
    (ENNReal.toReal_mono hb h)

theorem metric_entropy_mono_cover (h : covering_number P r U ≤ covering_number Q s B) :
    metric_entropy P r U ≤ metric_entropy Q s B := log2_mono h

theorem entropy_eq_coe (hn : U.Nonempty) (hf : covering_number P r U < ⊤) :
    metric_entropy P r U = (Real.logb 2 (covering_number P r U).toReal : EReal) := by
  have h0 := (zero_lt_one.trans_le (one_le_covering_number_of_nonempty P r U hn)).ne'
  simp [metric_entropy, log2_ereal, h0, hf.ne]

theorem entropy_top_iff (hn : U.Nonempty) :
    metric_entropy P r U = ⊤ ↔ covering_number P r U = ⊤ := by
  constructor
  · intro h
    by_contra ht
    rw [entropy_eq_coe hn (lt_top_iff_ne_top.mpr ht)] at h
    exact EReal.coe_ne_top _ h
  · intro h
    simp [metric_entropy, log2_ereal, h]

def GapDefined (f : Operator X bot) (P Q : X → X → ℝ≥0∞) (U : Set X)
    (r : ℝ≥0∞) : Prop :=
  covering_number P r U < ⊤ ∨ covering_number Q r (f.func '' U) < ⊤

noncomputable def entropyGap (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (U : Set X) (r : ℝ≥0∞) (_h : GapDefined f P Q U r) : EReal :=
  metric_entropy P r U - metric_entropy Q r (f.func '' U)

theorem entropyGap_cases (hn : U.Nonempty) (h : GapDefined f P Q U r) :
    (covering_number P r U = ⊤ → entropyGap f P Q U r h = ⊤) ∧
    (covering_number Q r (f.func '' U) = ⊤ → entropyGap f P Q U r h = ⊥) ∧
    (covering_number P r U < ⊤ → covering_number Q r (f.func '' U) < ⊤ →
      ∃ a : ℝ, entropyGap f P Q U r h = a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    have hq := h.resolve_left (fun hl => hl.ne hp)
    rw [entropyGap, (entropy_top_iff hn).mpr hp, entropy_eq_coe (hn.image _) hq]
    exact EReal.top_sub_coe _
  · intro hq
    rw [entropyGap, (entropy_top_iff (hn.image _)).mpr hq, EReal.sub_top]
  · intro hp hq
    rw [entropyGap, entropy_eq_coe hn hp, entropy_eq_coe (hn.image _) hq, ← EReal.coe_sub]
    exact ⟨_, rfl⟩

theorem entropyGap_sign (hn : U.Nonempty) (h : GapDefined f P Q U r) :
    let e := entropyGap f P Q U r h
    let a := metric_entropy P r U
    let b := metric_entropy Q r (f.func '' U)
    (0 < e ↔ b < a) ∧ (e < 0 ↔ a < b) ∧ (e = 0 ↔ a = b) := by
  dsimp
  by_cases hp : covering_number P r U = ⊤
  · have hq := h.resolve_left fun hl => hl.ne hp
    rw [(entropyGap_cases hn h).1 hp, (entropy_top_iff hn).mpr hp, entropy_eq_coe (hn.image _) hq]
    simp
  · by_cases hq : covering_number Q r (f.func '' U) = ⊤
    · rw [(entropyGap_cases hn h).2.1 hq, (entropy_top_iff (hn.image _)).mpr hq,
        entropy_eq_coe hn (lt_top_iff_ne_top.mpr hp)]
      simp
    · rw [entropyGap, entropy_eq_coe hn (lt_top_iff_ne_top.mpr hp),
        entropy_eq_coe (hn.image _) (lt_top_iff_ne_top.mpr hq), ← EReal.coe_sub]
      rw [← EReal.coe_zero]
      simp only [EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff, sub_pos, sub_neg, sub_eq_zero, and_self]

theorem threshold_cover (hA : A ⊆ dom f) (hn : A.Nonempty) (hBA : B ⊆ A)
    (hr : FinitePositive r) (hs : FinitePositive s) (h : r ≤ uniform f P Q A A) :
    covering_number Q s (f.func '' B) ≤ covering_number P r B := by
  apply cover_push
  intro x hx c hc hxc
  have hm := threshold_fiber hA hn hr h (hBA hc) (show x ∈ ball P c r ∩ A from ⟨hxc,hBA hx⟩)
  exact hm.2.trans_lt hs.1

theorem threshold_entropy (hA : A ⊆ dom f) (hn : A.Nonempty) (hBA : B ⊆ A)
    (_hB : B.Nonempty) (hr : FinitePositive r) (hs : FinitePositive s)
    (h : r ≤ uniform f P Q A A) :
    metric_entropy Q s (f.func '' B) ≤ metric_entropy P r B :=
  metric_entropy_mono_cover (threshold_cover hA hn hBA hr hs h)

theorem cover_const_image (hn : U.Nonempty) (hr : 0 < r)
    (h : ∀ x ∈ U, ∀ y ∈ U, Q (f.func x) (f.func y) = 0) :
    covering_number Q r (f.func '' U) = 1 := by
  obtain ⟨c,hc⟩ := hn
  refine cover_single_center ⟨f.func c,⟨c,hc,rfl⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact (h x hx c hc).trans_lt hr

theorem small_cover (hA : A ⊆ dom f) (hn : A.Nonempty)
    {s t : ℝ≥0∞} (hs : FinitePositive s) (ht : FinitePositive t)
    (hd : diameter P A < s) (hst : s ≤ t) (h : t ≤ uniform f P Q A A)
    (hr : FinitePositive r) : covering_number Q r (f.func '' A) = 1 :=
  cover_const_image hn hr.1 ((small_iff hA hn hs ht hd hst).mp h)

theorem finite_gap (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {J K : Set I}
    (hJ : J.Nonempty) (hK : K.Nonempty) (_hU : U ⊆ dom f) (hn : U.Nonempty)
    (hf : U.Finite) (hr : FinitePositive r) :
    let P := subfamily_pseudometric d J
    let Q := subfamily_pseudometric d K
    let V := f.func '' U
    0 < covering_number P r U ∧ 0 < covering_number Q r V ∧
    covering_number P r U < ⊤ ∧ covering_number Q r V < ⊤ ∧
    (∃ a : ℝ, metric_entropy P r U = a) ∧
    (∃ b : ℝ, metric_entropy Q r V = b) ∧ GapDefined f P Q U r := by
  dsimp
  have hp := cover_finite hf (fun x _ => (subfamily_pseudometric_is_extended d J hJ hd).dist_self x) hr.1
  have hq := cover_finite (hf.image f.func)
    (fun x _ => (subfamily_pseudometric_is_extended d K hK hd).dist_self x) hr.1
  exact ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hn),
    zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hn.image _)),
    hp, hq, ⟨_,entropy_eq_coe hn hp⟩, ⟨_,entropy_eq_coe (hn.image _) hq⟩, Or.inl hp⟩

theorem const_gap (_hU : U ⊆ dom f) (hn : U.Nonempty) (hr : FinitePositive r)
    (hc : j ∈ Const d f U) :
    covering_number (d j) r (f.func '' U) = 1 ∧
    metric_entropy (d j) r (f.func '' U) = 0 ∧
    ∃ h : GapDefined f (d j) (d j) U r,
      entropyGap f (d j) (d j) U r h = metric_entropy (d j) r U := by
  have hc' := cover_const_image hn hr.1 hc
  have he : metric_entropy (d j) r (f.func '' U) = 0 := by
    simp [metric_entropy, log2_ereal, hc', Real.logb_one]
  refine ⟨hc', he, Or.inr (hc'.trans_lt (by simp)), ?_⟩
  simp [entropyGap, he, sub_eq_add_neg]

theorem ident_cover (hd : ExtendedPseudoMetric X bot (d j))
    (hU : U ⊆ dom f) (_hn : U.Nonempty) (_hr : FinitePositive r)
    (hi : j ∈ Ident d f U) :
    covering_number (d j) r (f.func '' U) = covering_number (d j) r U ∧
    metric_entropy (d j) r (f.func '' U) = metric_entropy (d j) r U := by
  have he := ident_distance hd hU hi
  have hc : covering_number (d j) r (f.func '' U) = covering_number (d j) r U :=
    le_antisymm (cover_push f.func fun x hx c hc h => (he x hx c hc).trans_lt h)
      (cover_pull f.func fun x hx c hc h => (he x hx c hc).symm.trans_lt h)
  exact ⟨hc,congrArg log2_ereal hc⟩

theorem equal_cover_gap (hn : U.Nonempty)
    (he : covering_number P r U = covering_number Q r (f.func '' U))
    (hg : GapDefined f P Q U r) : entropyGap f P Q U r hg = 0 := by
  have hp : covering_number P r U < ⊤ := hg.elim id (fun h => he ▸ h)
  have he' : metric_entropy P r U = metric_entropy Q r (f.func '' U) :=
    congrArg log2_ereal he
  rw [entropyGap, ← he', entropy_eq_coe hn hp, ← EReal.coe_sub, sub_self]
  rfl

theorem ident_gap (hd : ExtendedPseudoMetric X bot (d j)) (hU : U ⊆ dom f)
    (hn : U.Nonempty) (hr : FinitePositive r) (hi : j ∈ Ident d f U)
    (hg : GapDefined f (d j) (d j) U r) : entropyGap f (d j) (d j) U r hg = 0 :=
  equal_cover_gap hn (ident_cover hd hU hn hr hi).1.symm hg

theorem lip_cover {L : ℝ≥0∞} (hL : FinitePositive L)
    (h : ∀ x ∈ U, ∀ y ∈ U, Q (f.func x) (f.func y) ≤ L * P x y) :
    covering_number Q r (f.func '' U) ≤ covering_number P (r / L) U := by
  apply cover_push
  intro x hx y hy he
  have hm := (ENNReal.lt_div_iff_mul_lt (Or.inl hL.1.ne') (Or.inl hL.2.ne)).mp he
  exact (h x hx y hy).trans_lt (by simpa [mul_comm] using hm)

theorem finitePositive_div {L : ℝ≥0∞} (hr : FinitePositive r) (hL : FinitePositive L) :
    FinitePositive (r / L) :=
  ⟨ENNReal.div_pos hr.1.ne' hL.2.ne, ENNReal.div_lt_top hr.2.ne hL.1.ne'⟩

theorem lip_gap {L : ℝ≥0∞} (_hU : U ⊆ dom f) (hn : U.Nonempty)
    (ht : TotallyBoundedAt P U) (hr : FinitePositive r) (hL : FinitePositive L)
    (h : ∀ x ∈ U, ∀ y ∈ U, Q (f.func x) (f.func y) ≤ L * P x y) :
    (∃ a : ℝ, metric_entropy P r U = a) ∧ (∃ b : ℝ, metric_entropy Q r (f.func '' U) = b) ∧
    ∃ hg : GapDefined f P Q U r,
      metric_entropy P r U - metric_entropy P (r / L) U ≤ entropyGap f P Q U r hg := by
  have hc := lip_cover (r := r) hL h
  have hf := hc.trans_lt (ht _ (finitePositive_div hr hL))
  exact ⟨⟨_,entropy_eq_coe hn (ht r hr)⟩,⟨_,entropy_eq_coe (hn.image _) hf⟩,
    Or.inl (ht r hr), EReal.sub_le_sub le_rfl (metric_entropy_mono_cover hc)⟩

theorem colip_cover [Fintype I] {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : FinitePositive (K i j)) :
    covering_number (d i) (r / K i j) U ≤ covering_number (d j) r (f.func '' U) := by
  apply cover_pull
  intro x hx c hc hxc
  have h := (Finset.single_le_sum (f := fun k => K k j * d k x c)
    (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (hK.2.2 x hx c hc j)
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hpos.1.ne') (Or.inl hpos.2.ne)).mpr
  simpa [mul_comm] using h.trans_lt hxc

theorem colip_gap [Fintype I] {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : FinitePositive (K i j))
    (hr : FinitePositive r) (ht : TotallyBoundedAt (d i) U) :
    (∃ a : ℝ, metric_entropy (d i) r U = a) ∧
    (∃ b : ℝ, metric_entropy (d i) (r / K i j) U = b) ∧
    ∃ hg : GapDefined f (d i) (d j) U r,
      entropyGap f (d i) (d j) U r hg ≤
        metric_entropy (d i) r U - metric_entropy (d i) (r / K i j) U := by
  exact ⟨⟨_,entropy_eq_coe hK.1 (ht r hr)⟩,
    ⟨_,entropy_eq_coe hK.1 (ht _ (finitePositive_div hr hpos))⟩, Or.inl (ht r hr),
    EReal.sub_le_sub le_rfl (metric_entropy_mono_cover (colip_cover hK hpos))⟩

end Chapter
```

```lean filename=Chapter/Fibers.lean
import Chapter.Components
import formal_oet.vol_01.ch_01_foundations.metric_entropy

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U : Set X} {J K : Set I} {i : I}

def fiber (D : X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) (y : X) : Set X :=
  {x ∈ U | D (f.func x) y = 0}

theorem subfamily_zero (d : I → X → X → ℝ≥0∞) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact nonpos_iff_eq_zero.mp (h ▸ le_iSup (fun k : J => d k.1 x y) ⟨j, hj⟩)
  · intro h
    exact nonpos_iff_eq_zero.mp (iSup_le fun j : J => (h j.1 j.2).le)

theorem subfamily_max [Finite I] (hJ : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subfamily_pseudometric d J x y = d j x y := by
  haveI : Nonempty J := hJ.to_subtype
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j : J => d j.1 x y)
  exact ⟨j, j.2, le_antisymm (iSup_le hj) (le_iSup (fun j : J => d j.1 x y) j)⟩

variable {D : X → X → ℝ≥0∞} {y z : X}

theorem fiber_target (_hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D)
    (h : D y z = 0) : fiber D f U y = fiber D f U z := by
  ext x
  have he : D (f.func x) y = D (f.func x) z := by
    rw [hD.symm (f.func x) y, zero_left hD h, hD.symm z]
  simp [fiber, he]

def fiberBlocks (D : X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) :
    Set (Set X) := (fun y => fiber D f U y) '' (f.func '' U)

theorem fiber_cover (_hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D) :
    (∀ B ∈ fiberBlocks D f U, B.Nonempty) ∧ ⋃₀ fiberBlocks D f U = U := by
  constructor
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, hD.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, hx, hD.dist_self _⟩

theorem fiber_eq_or_disjoint (hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D)
    (_hy : y ∈ f.func '' U) (_hz : z ∈ f.func '' U) :
    fiber D f U y = fiber D f U z ∨ Disjoint (fiber D f U y) (fiber D f U z) := by
  classical
  by_cases h : D y z = 0
  · exact Or.inl (fiber_target hU hD h)
  · right
    exact Set.disjoint_left.mpr fun x (hx : x ∈ fiber D f U y) (hx' : x ∈ fiber D f U z) =>
      h ((zero_left hD ((hD.symm y _).trans hx.2) z).trans hx'.2)

theorem fiber_partition (hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D) :
    (∀ B ∈ fiberBlocks D f U, B.Nonempty) ∧
    ⋃₀ fiberBlocks D f U = U ∧ (fiberBlocks D f U).PairwiseDisjoint id := by
  refine ⟨(fiber_cover hU hD).1, (fiber_cover hU hD).2, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
  exact (fiber_eq_or_disjoint hU hD hy hz).resolve_left h

theorem fiber_inter (_hU : U ⊆ dom f) (hJ : J.Nonempty) :
    fiber (subfamily_pseudometric d J) f U y = ⋂ j ∈ J, fiber (d j) f U y := by
  ext x
  simp only [fiber, Set.mem_iInter, Set.mem_setOf_eq, subfamily_zero]
  exact ⟨fun h j hj => ⟨h.1, h.2 j hj⟩, fun h =>
    ⟨(h hJ.choose hJ.choose_spec).1, fun j hj => (h j hj).2⟩⟩

theorem fiber_antitone (_hU : U ⊆ dom f) (_hJ : J.Nonempty) (hJK : J ⊆ K) :
    fiber (subfamily_pseudometric d K) f U y ⊆ fiber (subfamily_pseudometric d J) f U y :=
  fun _ hx => ⟨hx.1, (subfamily_zero _ _ _ _).mpr fun j hj =>
    (subfamily_zero _ _ _ _).mp hx.2 j (hJK hj)⟩

theorem fiber_singleton :
    fiber (subfamily_pseudometric d {i}) f U y = fiber (d i) f U y := by
  rw [subfamily_pseudometric_singleton]

theorem fiber_full (hU : U ⊆ dom f) :
    fiber (subfamily_pseudometric d Set.univ) f U y ⊆ fiber (d i) f U y := by
  rw [← fiber_singleton (d := d) (i := i)]
  exact fiber_antitone hU (Set.singleton_nonempty _) (Set.subset_univ _)

theorem fiber_ident (hd : ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    (hi : i ∈ Ident d f U) : fiber (d i) f U y = {x ∈ U | d i x y = 0} := by
  ext x
  constructor <;> intro h
  · exact ⟨h.1, (zero_left hd (hi.2 x h.1) y).symm.trans h.2⟩
  · exact ⟨h.1, (zero_left hd (hi.2 x h.1) y).trans h.2⟩

theorem fiber_const (hd : ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    (hc : i ∈ Const d f U) (hy : y ∈ f.func '' U) :
    fiber (d i) f U y = U ∧ (0 < d i z y → fiber (d i) f U z = ∅) := by
  obtain ⟨a, ha, rfl⟩ := hy
  have he : fiber (d i) f U (f.func a) = U :=
    Set.Subset.antisymm (fun _ h => h.1) (fun x hx => ⟨hx, hc x hx a ha⟩)
  refine ⟨he, fun hp => Set.eq_empty_iff_forall_notMem.mpr fun x hx => hp.ne' ?_⟩
  exact (zero_left hd ((hd.symm z _).trans hx.2) _).trans (hc x hx.1 a ha)

def pointPairs (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}

def zeroPairs (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) :
    Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}

theorem zeroPairs_fiber (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) :
    (x, x') ∈ zeroPairs d f U ↔ x' ∈ fiber (subfamily_pseudometric d Set.univ) f U (f.func x) := by
  constructor
  · intro h
    exact ⟨hx', (subfamily_zero _ _ _ _).mpr fun j _ =>
      ((hd j).symm _ _).trans (h.2.2 j)⟩
  · intro h
    exact ⟨hx, hx', fun j => ((hd j).symm _ _).trans
      ((subfamily_zero _ _ _ _).mp h.2 j (Set.mem_univ _))⟩

def imagePoint (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, x, x.property, rfl⟩

def PointFactor (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U : Set X) → X, ∀ x : U, T (imagePoint f U x) = g.func x

theorem point_factor_necessary (_hU : U ⊆ dom f ∩ dom g) (h : PointFactor f g U) :
    pointPairs f U ⊆ pointPairs g U := by
  obtain ⟨T, hT⟩ := h
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  rw [← hT ⟨x,hx⟩, ← hT ⟨y,hy⟩]
  exact congrArg T (Subtype.ext hxy)

noncomputable def representative (f : Operator X bot) (U : Set X)
    (z : (f.func '' U : Set X)) : U :=
  ⟨z.property.choose, z.property.choose_spec.1⟩

theorem representative_spec (z : (f.func '' U : Set X)) :
    f.func (representative f U z) = z := z.property.choose_spec.2

theorem point_factor_sufficient (_hU : U ⊆ dom f ∩ dom g)
    (h : pointPairs f U ⊆ pointPairs g U) : PointFactor f g U := by
  refine ⟨fun z => g.func (representative f U z), fun x => ?_⟩
  let r := representative f U (imagePoint f U x)
  exact (h (show ((r : X), (x : X)) ∈ pointPairs f U from
    ⟨r.property, x.property, representative_spec _⟩)).2.2

theorem point_factor_both (hU : U ⊆ dom f ∩ dom g) :
    (PointFactor f g U ∧ PointFactor g f U) ↔ pointPairs f U = pointPairs g U := by
  have hU' : U ⊆ dom g ∩ dom f := fun _ hx => ⟨(hU hx).2, (hU hx).1⟩
  exact ⟨fun h => Set.Subset.antisymm (point_factor_necessary hU h.1)
    (point_factor_necessary hU' h.2),
    fun h => ⟨point_factor_sufficient hU h.le, point_factor_sufficient hU' h.ge⟩⟩

theorem point_factor_lip (_hU : U ⊆ dom f ∩ dom g)
    (T : (f.func '' U : Set X) → X) (hT : ∀ x : U, T (imagePoint f U x) = g.func x)
    {K L : ℝ≥0∞} (hK : 0 < K) (hKt : K < ⊤) (_hLt : L < ⊤)
    (hf : ∀ x ∈ U, ∀ y ∈ U, K * D x y ≤ D (f.func x) (f.func y))
    (hg : ∀ x ∈ U, ∀ y ∈ U, D (g.func x) (g.func y) ≤ L * D x y) :
    ∀ z z' : (f.func '' U : Set X), D (T z) (T z') ≤ L / K * D z z' := by
  rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩
  change D (T (imagePoint f U ⟨x,hx⟩)) (T (imagePoint f U ⟨y,hy⟩)) ≤ _
  rw [hT, hT, div_eq_mul_inv, mul_assoc]
  refine (hg x hx y hy).trans (mul_le_mul_right ?_ L)
  rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hK.ne') (Or.inl hKt.ne)]
  simpa [mul_comm] using hf x hx y hy

def imageSetoid (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) : Setoid (f.func '' U : Set X) where
  r x y := GaugeZeroRelated d x y
  iseqv :=
    let h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    ⟨fun x => h.refl x, fun hxy => h.symm hxy, fun hxy hyz => h.trans hxy hyz⟩

def imageQuot (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid hd f U)

def quotientPoint (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) (x : U) : imageQuot hd f U :=
  Quotient.mk _ (imagePoint f U x)

def QuotFactor (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : imageQuot hd f U → imageQuot hd g U,
    ∀ x : U, T (quotientPoint hd f U x) = quotientPoint hd g U x

theorem quot_factor (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f ∩ dom g) :
    QuotFactor hd f g U ↔ zeroPairs d f U ⊆ zeroPairs d g U := by
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,hxy⟩
    refine ⟨hx,hy,?_⟩
    have eq : quotientPoint hd f U ⟨x,hx⟩ = quotientPoint hd f U ⟨y,hy⟩ :=
      Quotient.sound hxy
    exact @Quotient.exact _ (imageSetoid hd g U) (imagePoint g U ⟨x,hx⟩)
      (imagePoint g U ⟨y,hy⟩) ((hT _).symm.trans ((congrArg T eq).trans (hT _)))
  · intro h
    let T : (f.func '' U : Set X) → imageQuot hd g U :=
      fun z => quotientPoint hd g U (representative f U z)
    refine ⟨Quotient.lift T ?_, fun x => ?_⟩
    · intro z z' hzz
      apply Quotient.sound
      let r := representative f U z
      let s := representative f U z'
      apply (h (show ((r : X), (s : X)) ∈ zeroPairs d f U from
        ⟨r.property,s.property,?_⟩)).2.2
      simpa only [show f.func r = z from representative_spec z,
        show f.func s = z' from representative_spec z'] using hzz
    · apply Quotient.sound
      let r := representative f U (imagePoint f U x)
      apply (h (show ((r : X), (x : X)) ∈ zeroPairs d f U from
        ⟨r.property,x.property,?_⟩)).2.2
      intro i
      rw [show f.func r = f.func x from representative_spec (imagePoint f U x)]
      exact (hd i).dist_self _

theorem quot_factor_both (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) :
    (QuotFactor hd f g U ∧ QuotFactor hd g f U) ↔ zeroPairs d f U = zeroPairs d g U := by
  rw [quot_factor hd hU, quot_factor hd (f := g) (g := f)
    (fun _ hx => ⟨(hU hx).2, (hU hx).1⟩)]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => ⟨h.le,h.ge⟩⟩

def SeparatesImage (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Prop :=
  ∀ x ∈ f.func '' U, ∀ y ∈ f.func '' U, GaugeZeroRelated d x y → x = y

theorem pairs_of_separated (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (h : SeparatesImage d f U) : pointPairs f U = zeroPairs d f U := by
  apply Set.Subset.antisymm
  · rintro ⟨x,y⟩ ⟨hx,hy,he⟩
    exact ⟨hx,hy,fun i => he ▸ (hd i).dist_self _⟩
  · rintro ⟨x,y⟩ ⟨hx,hy,he⟩
    exact ⟨hx,hy,h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he⟩

theorem factor_of_separated (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) (hf : SeparatesImage d f U) (hg : SeparatesImage d g U) :
    (PointFactor f g U ↔ QuotFactor hd f g U) ∧
    ((PointFactor f g U ∧ PointFactor g f U) ↔
      (QuotFactor hd f g U ∧ QuotFactor hd g f U)) := by
  constructor
  · rw [quot_factor hd hU, ← pairs_of_separated hd hf, ← pairs_of_separated hd hg]
    exact ⟨point_factor_necessary hU, point_factor_sufficient hU⟩
  · rw [point_factor_both hU, quot_factor_both hd hU,
      pairs_of_separated hd hf, pairs_of_separated hd hg]

def FiberFiner (d : I → X → X → ℝ≥0∞) (U : Set X) (f g : Operator X bot) : Prop :=
  zeroPairs d f U ⊆ zeroPairs d g U

theorem fiber_preorder (d : I → X → X → ℝ≥0∞) (U : Set X) :
    Reflexive (FiberFiner (bot := bot) d U) ∧
    (∀ f g h : Operator X bot, FiberFiner d U f g → FiberFiner d U g h → FiberFiner d U f h) :=
  ⟨fun _ => Set.Subset.rfl, fun _ _ _ h h' => h.trans h'⟩

theorem fiber_finite_chain {m : ℕ} (fs : ℕ → Operator X bot)
    (_hU : ∀ k ≤ m, U ⊆ dom (fs k))
    (h : ∀ k < m, FiberFiner d U (fs k) (fs (k + 1))) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ m) : FiberFiner d U (fs a) (fs b) := by
  induction b, hab using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ k hak ih => exact (ih (by omega)).trans (h k (by omega))

theorem fiber_strict_chain {m : ℕ} (fs : ℕ → Operator X bot)
    (hU : ∀ k ≤ m, U ⊆ dom (fs k))
    (h : ∀ k < m, FiberFiner d U (fs k) (fs (k + 1))) {r : ℕ} (hr : r < m)
    (hs : zeroPairs d (fs r) U ⊂ zeroPairs d (fs (r+1)) U) :
    zeroPairs d (fs 0) U ⊂ zeroPairs d (fs m) U ∧
    (zeroPairs d (fs m) U \ zeroPairs d (fs 0) U).Nonempty := by
  obtain ⟨p,hp,hpn⟩ := Set.exists_of_ssubset hs
  have hmem := fiber_finite_chain fs hU h (a := r+1) (b := m) (by omega) le_rfl hp
  have hn : p ∉ zeroPairs d (fs 0) U := fun h0 =>
    hpn (fiber_finite_chain fs hU h (Nat.zero_le r) (by omega) h0)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨fiber_finite_chain fs hU h (Nat.zero_le m) le_rfl,
    fun eq => hn (eq ▸ hmem)⟩, p, hmem, hn⟩

end Chapter
```

```lean filename=Chapter/Floor.lean
import Chapter.Step

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter.FloorExample

noncomputable def f := liftRealMap (fun x => (⌊x⌋ : ℝ))
noncomputable def d : Unit → Option ℝ → Option ℝ → ℝ≥0∞ := fun _ => realDist

def D1 : Set (Option ℝ) := realSet (Set.Icc 0 (1/2))
def D2 : Set (Option ℝ) := realSet (Set.Icc (9/10) (11/10))
def D3 : Set (Option ℝ) := realSet ({0,2} : Set ℝ)
def D4 : Set (Option ℝ) := realSet (Set.Icc 0 2)

theorem domain (S : Set ℝ) : realSet S ⊆ dom f := realSet_domain _ _

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := read_legal id

theorem floor_zero {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) : ⌊x⌋ = 0 :=
  Int.floor_eq_iff.mpr (by simpa using And.intro hx hx')

theorem one_value : f.func (some 1) = some 1 := by simp [f]

theorem zero_value : f.func (some 0) = some 0 := by simp [f]

theorem two_value : f.func (some 2) = some 2 := by simp [f]

noncomputable def kind (D : Set (Option ℝ)) (hn : D.Nonempty) : Bool × Bool :=
  thresholdType (diameterScale d) d f D hn 1 1 () ()

theorem kind_iff (D : Set (Option ℝ)) (hn : D.Nonempty) :
    kind D hn = (decide (diameter realDist D < 1),
      decide (1 ≤ uniform f realDist realDist D D)) := rfl

theorem interval_diameter (a b : ℝ) (hab : a ≤ b) :
    diameter realDist (realSet (Set.Icc a b)) = ENNReal.ofReal (b-a) :=
  realSet_diameter a b hab ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ (fun _ h => h)

theorem at_boundary_zero {D : Set (Option ℝ)} (hD : D ⊆ dom f)
    (h1 : some (1 : ℝ) ∈ D)
    (hleft : ∀ a : ℝ, 0 < a → a ≤ 1/10 → some (1-a) ∈ D) :
    uniform f realDist realDist D D = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra! h
  obtain ⟨r,hr,hr'⟩ := exists_between h
  have ht : r < ⊤ := hr'.trans_le le_top
  have hpos : 0 < r.toReal := ENNReal.toReal_pos hr.ne' ht.ne
  let a := min (r.toReal/2) (1/10)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have ha1 : a ≤ 1/10 := min_le_right _ _
  have har : a ≤ r.toReal/2 := min_le_left _ _
  have hx := hleft a ha ha1
  have hm : realDist (some (1-a)) (some 1) < r := by
    rw [real_some, ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) ht.ne,
      show 1-a-1 = -a by ring, abs_neg, abs_of_pos ha]
    linarith
  have he := uniform_zero hD ⟨_,h1⟩ hx h1 (hm.trans hr')
  have hf : f.func (some (1-a)) = some 0 := by
    simp [f, floor_zero (show 0 ≤ 1-a by linarith) (show 1-a < 1 by linarith)]
  rw [hf, one_value, real_zero] at he
  norm_num at he

theorem first :
    ∃ hn : D1.Nonempty, D1 ⊆ dom f ∧ diameter realDist D1 = ENNReal.ofReal (1/2) ∧
      uniform f realDist realDist D1 D1 = ⊤ ∧ kind D1 hn = (true,true) := by
  have hD : D1 ⊆ dom f := domain _
  have hd : diameter realDist D1 = ENNReal.ofReal (1/2) := by
    unfold D1
    rw [interval_diameter _ _ (by norm_num)]
    simp
  have he : ∀ x ∈ D1, f.func x = some 0 := by
    rintro _ ⟨a,ha,rfl⟩
    have h : a ∈ Set.Icc (0 : ℝ) (1/2) := ha
    simp [f, floor_zero h.1 (h.2.trans_lt (by norm_num))]
  have hu : uniform f realDist realDist D1 D1 = ⊤ := by
    apply top_unique
    exact le_uniform_iff.mpr fun y hy x hx _ => by simp [he x hx, he y hy]
  refine ⟨⟨some 0,by simp [D1]⟩,hD,hd,hu,?_⟩
  rw [kind_iff, hd, hu]
  norm_num [ENNReal.ofReal_lt_one]

theorem second :
    ∃ hn : D2.Nonempty, D2 ⊆ dom f ∧ diameter realDist D2 = ENNReal.ofReal (1/5) ∧
      uniform f realDist realDist D2 D2 = 0 ∧ kind D2 hn = (true,false) := by
  have hD : D2 ⊆ dom f := domain _
  have h1 : some (1 : ℝ) ∈ D2 := by norm_num [D2]
  have hd : diameter realDist D2 = ENNReal.ofReal (1/5) := by
    unfold D2
    rw [interval_diameter _ _ (by norm_num)]
    norm_num
  have hu := at_boundary_zero hD h1 (fun a ha ha1 => by
    rw [D2, mem_realSet]
    exact ⟨by linarith,by linarith⟩)
  refine ⟨⟨_,h1⟩,hD,hd,hu,?_⟩
  rw [kind_iff, hd, hu]
  norm_num [ENNReal.ofReal_lt_one]

theorem third :
    ∃ hn : D3.Nonempty, D3 ⊆ dom f ∧ diameter realDist D3 = 2 ∧
      uniform f realDist realDist D3 D3 = 2 ∧ kind D3 hn = (false,true) := by
  have hD : D3 ⊆ dom f := domain _
  have h0 : some (0 : ℝ) ∈ D3 := by simp [D3]
  have h2 : some (2 : ℝ) ∈ D3 := by simp [D3]
  have hd : diameter realDist D3 = 2 := by
    unfold D3
    rw [realSet_diameter 0 2 (by norm_num) (by simp) (by simp) (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> exact ⟨by norm_num,by norm_num⟩)]
    norm_num
  have hm : realDist (some 2) (some 0) = 2 := by norm_num
  have hm' : realDist (some 0) (some 2) = 2 := by norm_num
  have hn : D3.Nonempty := ⟨_,h0⟩
  have hu : uniform f realDist realDist D3 D3 = 2 := by
    apply le_antisymm
    · rw [← hm]
      apply uniform_separation hD hn h2 h0
      rw [two_value, zero_value, hm]
      norm_num
    · apply le_uniform_iff.mpr
      rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩ h
      change y ∈ ({0,2} : Set ℝ) at hy
      change x ∈ ({0,2} : Set ℝ) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hx
      rcases hy with rfl | rfl <;> rcases hx with rfl | rfl
      · exact (gauge ()).dist_self _
      · rw [hm] at h; exact (lt_irrefl _ h).elim
      · rw [hm'] at h; exact (lt_irrefl _ h).elim
      · exact (gauge ()).dist_self _
  refine ⟨hn,hD,hd,hu,?_⟩
  rw [kind_iff,hd,hu]
  norm_num

theorem fourth :
    ∃ hn : D4.Nonempty, D4 ⊆ dom f ∧ diameter realDist D4 = 2 ∧
      uniform f realDist realDist D4 D4 = 0 ∧ kind D4 hn = (false,false) := by
  have hD : D4 ⊆ dom f := domain _
  have h1 : some (1 : ℝ) ∈ D4 := by norm_num [D4]
  have hd : diameter realDist D4 = 2 := by
    unfold D4
    rw [interval_diameter _ _ (by norm_num)]
    norm_num
  have hu := at_boundary_zero hD h1 (fun a ha ha1 => by
    rw [D4, mem_realSet]
    exact ⟨by linarith,by linarith⟩)
  refine ⟨⟨_,h1⟩, hD, hd, hu, ?_⟩
  rw [kind_iff,hd,hu]
  norm_num

theorem large_without_collapse :
    D3.Nonempty ∧ D3 ⊆ dom f ∧ 1 ≤ uniform f realDist realDist D3 D3 ∧
      ∃ x ∈ D3, ∃ y ∈ D3, 0 < realDist (f.func x) (f.func y) := by
  obtain ⟨hn,hD,_,hu,_⟩ := third
  refine ⟨hn,hD,by rw [hu]; norm_num,some 0,by simp [D3],some 2,by simp [D3],?_⟩
  rw [zero_value,two_value]
  norm_num

end Chapter.FloorExample
```

```lean filename=Chapter/Models.lean
import Chapter.Cover

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

variable {Y Z : Type}

def extendDistance (D : Y → Y → ℝ≥0∞) : Option Y → Option Y → ℝ≥0∞
  | none, none => 0
  | some x, some y => D x y
  | _, _ => ⊤

theorem extend_legal [Nonempty Y] {D : Y → Y → ℝ≥0∞}
    (hs : ∀ x, D x x = 0) (hm : ∀ x y, D x y = D y x)
    (ht : ∀ x y z, D x z ≤ D x y + D y z) :
    ExtendedPseudoMetric (Option Y) none (extendDistance D) where
  nonabsorbing := Nonempty.elim inferInstance fun y : Y => ⟨some y, Option.some_ne_none _⟩
  dist_self x := by cases x <;> simp [extendDistance, hs]
  symm x y := by cases x <;> cases y <;> simp [extendDistance, hm]
  triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp [extendDistance, ht]
  isolate_bot x hx := by cases x <;> simp_all [extendDistance]

noncomputable def discreteReadout [DecidableEq Z] (q : Y → Z) (a : ℝ≥0∞) (x y : Y) :
    ℝ≥0∞ := if q x = q y then 0 else a

theorem discrete_legal [Nonempty Y] [DecidableEq Z] (q : Y → Z) (a : ℝ≥0∞) :
    ExtendedPseudoMetric (Option Y) none (extendDistance (discreteReadout q a)) := by
  apply extend_legal
  · simp [discreteReadout]
  · intro x y
    simp [discreteReadout, eq_comm]
  · intro x y z
    by_cases h : q x = q y
    · simp [discreteReadout, h]
    · simpa only [discreteReadout, if_neg h] using
        (le_add_right (show (if q x = q z then 0 else a) ≤ a by split <;> simp) :
          (if q x = q z then 0 else a) ≤ a + (if q y = q z then 0 else a))

def liftRealMap (F : ℝ → ℝ) : Operator (Option ℝ) none :=
  ⟨Option.map F, rfl⟩

theorem liftReal_domain (F : ℝ → ℝ) :
    dom (liftRealMap F) = Set.range (some : ℝ → Option ℝ) := by
  ext x
  cases x <;> simp [dom, liftRealMap]

noncomputable def readDistance (q : ℝ → ℝ) : Option ℝ → Option ℝ → ℝ≥0∞ :=
  extendDistance fun x y => ENNReal.ofReal |q x - q y|

@[simp] theorem read_some (q : ℝ → ℝ) (x y : ℝ) :
    readDistance q (some x) (some y) = ENNReal.ofReal |q x - q y| := rfl

theorem read_legal (q : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (readDistance q) := by
  apply extend_legal
  · simp
  · intro x y
    rw [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

@[simp] theorem read_zero_iff (q : ℝ → ℝ) (x y : ℝ) :
    readDistance q (some x) (some y) = 0 ↔ q x = q y := by
  rw [read_some, ENNReal.ofReal_eq_zero]
  exact ⟨fun h => sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _))),
    fun h => by simp [h]⟩

noncomputable def realDist := readDistance id
noncomputable def absDist := readDistance abs

@[simp] theorem real_some (x y : ℝ) : realDist (some x) (some y) = ENNReal.ofReal |x-y| := rfl

@[simp] theorem real_zero (x y : ℝ) : realDist (some x) (some y) = 0 ↔ x = y :=
  read_zero_iff id x y

@[simp] theorem abs_zero (x y : ℝ) : absDist (some x) (some y) = 0 ↔ |x| = |y| :=
  read_zero_iff abs x y

@[simp] theorem liftReal_some (F : ℝ → ℝ) (x : ℝ) :
    (liftRealMap F).func (some x) = some (F x) := rfl

def realSet (S : Set ℝ) : Set (Option ℝ) := some '' S

theorem realSet_domain (F : ℝ → ℝ) (S : Set ℝ) : realSet S ⊆ dom (liftRealMap F) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Option.some_ne_none _

@[simp] theorem mem_realSet (S : Set ℝ) (x : ℝ) :
    some x ∈ realSet S ↔ x ∈ S := by simp [realSet]

theorem realSet_diameter (a b : ℝ) (hab : a ≤ b) {S : Set ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hS : S ⊆ Set.Icc a b) :
    diameter realDist (realSet S) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · refine iSup_le fun x : realSet S => iSup_le fun y : realSet S => ?_
    obtain ⟨x',hx,hex⟩ := x.2
    obtain ⟨y',hy,hey⟩ := y.2
    rw [← hex, ← hey, real_some]
    apply ENNReal.ofReal_le_ofReal
    have hx' := hS hx
    have hy' := hS hy
    exact abs_le.mpr ⟨by linarith [hx'.1,hy'.2], by linarith [hx'.2,hy'.1]⟩
  · simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using
      (le_diameter (P := realDist) ((mem_realSet S b).mpr hb) ((mem_realSet S a).mpr ha))

namespace Swap

def U : Set (Option Bool) := {some false, some true}
noncomputable def d : Unit → Option Bool → Option Bool → ℝ≥0∞ :=
  fun _ => extendDistance (discreteReadout id 1)
def f : Operator (Option Bool) none := ⟨Option.map not, rfl⟩

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := discrete_legal id 1

theorem calculations :
    U ⊆ dom f ∧ U ⊆ dom (f*f) ∧ f.func '' U = U ∧
    Active d f U = {()} ∧ Ident d f U = ∅ ∧ Ident d (f*f) U = {()} ∧
    Active d (f*f) U = ∅ := by
  have mem (x : Option Bool) : x ∈ U ↔ x ≠ none := by
    cases x with
    | none => simp [U]
    | some b => cases b <;> simp [U]
  have dom1 : U ⊆ dom f := by
    rintro (_ | x) h
    · simp [U] at h
    · exact Option.some_ne_none _
  have dom2 : U ⊆ dom (f*f) := by
    rintro (_ | x) h
    · simp [U] at h
    · exact Option.some_ne_none _
  have hi : f.func '' U = U := by
    ext x
    constructor
    · rintro ⟨y, hy,rfl⟩
      exact (mem _).mpr (dom1 hy)
    · intro hx
      cases x with
      | none => simp [U] at hx
      | some b => exact ⟨some (!b), (mem _).mpr (Option.some_ne_none _), by simp [f]⟩
  have hc : () ∉ Const d f U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    norm_num [d, f, extendDistance, discreteReadout] at h'
  have hn : () ∉ Ident d f U := by
    intro h
    have h' := h.2 (some false) (by simp [U])
    norm_num [d, f, extendDistance, discreteReadout] at h'
  have hc2 : () ∉ Const d (f*f) U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    norm_num [d, f, extendDistance, discreteReadout] at h'
  have hi2 : () ∈ Ident d (f*f) U := by
    refine ⟨hc2, fun x _ => ?_⟩
    have hx : (f*f).func x = x := by cases x <;> simp [f]
    rw [hx]
    exact (gauge ()).dist_self _
  refine ⟨dom1, dom2, hi, ?_, ?_, ?_, ?_⟩ <;> ext i <;> cases i
  · simp [Active, hc, hn]
  · simp [hn]
  · simp [hi2]
  · simp [Active, hi2]

theorem reverse_failures :
    ¬ (Active d f U ∪ Active d f (f.func '' U) ⊆ Active d (f*f) U) ∧
    ¬ (Ident d (f*f) U ⊆ Ident d f U ∩ Ident d f (f.func '' U)) := by
  obtain ⟨_,_,hi,ha,hid,hid2,ha2⟩ := calculations
  rw [hi, ha, hid, hid2, ha2, Set.union_self, Set.inter_self]
  simp

end Swap

namespace Inner

inductive Pt | a | b | p | q | r | s deriving DecidableEq
open Pt

def q : Pt → Pt | Pt.q => p | x => x
noncomputable def d (i : Bool) : Option Pt → Option Pt → ℝ≥0∞ :=
  extendDistance (discreteReadout (if i then id else q) 1)
def f : Operator (Option Pt) none :=
  ⟨fun | some a => some p | some b => some Pt.q | _ => none, rfl⟩
def g : Operator (Option Pt) none :=
  ⟨fun | some p => some r | some Pt.q => some s | _ => none, rfl⟩
def U : Set (Option Pt) := {some a, some b}

theorem gauge (i : Bool) : ExtendedPseudoMetric _ none (d i) := by
  haveI : Nonempty Pt := ⟨a⟩
  exact discrete_legal _ _

theorem counterexample : U ⊆ dom (g*f) ∧ f.func '' U = {some p, some Pt.q} ∧
    false ∈ Const d f U ∧ false ∉ Const d (g*f) U ∧ d true (some p) (some Pt.q) = 1 ∧
    d false ((g*f).func (some a)) ((g*f).func (some b)) = 1 := by
  have mem (x : Option Pt) : x ∈ U ↔ x = some a ∨ x = some b := by simp [U]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases (mem x).mp hx with rfl | rfl <;> exact Option.some_ne_none _
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rcases (mem y).mp hy with rfl | rfl <;> simp [f]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨some a,by simp [U],rfl⟩
      · exact ⟨some b,by simp [U],rfl⟩
  · intro x hx y hy
    rcases (mem x).mp hx with rfl | rfl <;> rcases (mem y).mp hy with rfl | rfl <;>
      simp [d, f, q, extendDistance, discreteReadout]
  · intro h
    have he := h (some a) (by simp [U]) (some b) (by simp [U])
    norm_num [d, f, g, q, extendDistance, discreteReadout] at he
    cases he
  · simp [d, extendDistance, discreteReadout]
  · simp [d, f, g, q, extendDistance, discreteReadout]

end Inner

namespace InfiniteGap

noncomputable def d {I : Type} [DecidableEq I] (i k : I) : Option Bool → Option Bool → ℝ≥0∞ :=
  extendDistance (discreteReadout id (if k = i then ⊤ else 1))

theorem gauge {I : Type} [DecidableEq I] (i k : I) :
    ExtendedPseudoMetric _ none (d i k) := discrete_legal _ _

theorem counterexample {I : Type} [Fintype I] [DecidableEq I] (i j : I) :
    let U := Swap.U
    let f : Operator (Option Bool) none := 1
    U.Nonempty ∧ U ⊆ dom f ∧ nullMatrix (d i) f U j i = ⊤ ∧
      j ∉ Const (d i) f U ∧ d i i (some false) (some true) = ⊤ ∧
      (i = j → d i j (some false) (some true) = ⊤) ∧
      (i ≠ j → d i j (some false) (some true) = 1) := by
  dsimp
  have mem (x : Option Bool) : x ∈ Swap.U ↔ x = some false ∨ x = some true := by simp [Swap.U]
  refine ⟨⟨some false,by simp [Swap.U]⟩,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases (mem x).mp hx with rfl | rfl <;> exact Option.some_ne_none _
  · apply top_unique
    apply le_uniform_iff.mpr
    intro y hy x hx h
    rcases (mem y).mp hy with rfl | rfl <;> rcases (mem x).mp hx with rfl | rfl
    · exact (gauge i j).dist_self _
    · simp [d, extendDistance, discreteReadout] at h
    · simp [d, extendDistance, discreteReadout] at h
    · exact (gauge i j).dist_self _
  · intro h
    have he := h (some false) (by simp [Swap.U]) (some true) (by simp [Swap.U])
    change d i j (some false) (some true) = 0 at he
    by_cases hji : j = i <;> norm_num [d, extendDistance, discreteReadout, hji] at he
  · simp [d, extendDistance, discreteReadout]
  · rintro rfl
    simp [d, extendDistance, discreteReadout]
  · intro h
    simp [d, extendDistance, discreteReadout, Ne.symm h]

end InfiniteGap

theorem diameter_counterexample :
    let A := realSet ({0,1} : Set ℝ)
    let B := realSet ({0} : Set ℝ)
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (1 : Operator (Option ℝ) none) ∧
    diameter realDist B = 0 ∧ diameter realDist A = 1 ∧
    diameter realDist B < ENNReal.ofReal (1/2) ∧
    ENNReal.ofReal (1/2) ≤ diameter realDist A := by
  have ha : diameter realDist (realSet ({0,1} : Set ℝ)) = 1 := by
    rw [realSet_diameter 0 1 (by norm_num) (by simp) (by simp) (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> exact ⟨by norm_num,by norm_num⟩)]
    norm_num
  have hb : diameter realDist (realSet ({0} : Set ℝ)) = 0 := by
    rw [realSet_diameter 0 0 le_rfl (by simp) (by simp) (by simp)]
    simp
  refine ⟨⟨some 0,by simp⟩,Set.image_mono (by simp),?_,hb,ha,?_,?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Option.some_ne_none _
  · rw [hb]
    simp
  · rw [ha, ENNReal.ofReal_le_one]
    norm_num

end Chapter
```

```lean filename=Chapter/Radius.lean
import Chapter.Fibers

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U A B : Set X} {i j k : I}
variable {P Q : X → X → ℝ≥0∞} {y x : X} {r : ℝ≥0∞}

def FinitePositive (r : ℝ≥0∞) : Prop := 0 < r ∧ r < ⊤

def admissible (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (U : Set X) (y : X) : Set ℝ≥0∞ :=
  {r | FinitePositive r ∧ ball P y r ∩ U ⊆ fiber Q f U (f.func y)}

noncomputable def radius (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (U : Set X) (y : X) : ℝ≥0∞ := sSup (admissible f P Q U y)

noncomputable def uniform (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (A U : Set X) : ℝ≥0∞ := ⨅ y : A, radius f P Q U y

noncomputable def nullMatrix (d : I → X → X → ℝ≥0∞)
    (f : Operator X bot) (U : Set X) (j i : I) : ℝ≥0∞ :=
  uniform f (d i) (d j) U U

theorem admissible_iff :
    r ∈ admissible f P Q U y ↔ FinitePositive r ∧
      ∀ x ∈ U, P x y < r → Q (f.func x) (f.func y) = 0 :=
  ⟨fun h => ⟨h.1, fun _ hx hd => (h.2 ⟨hd,hx⟩).2⟩,
   fun h => ⟨h.1, fun _ hx => ⟨hx.2, h.2 _ hx.2 hx.1⟩⟩⟩

theorem radius_empty (h : admissible f P Q U y = ∅) : radius f P Q U y = 0 := by
  simp [radius, h]

theorem radius_witness (h : r < radius f P Q U y) :
    ∃ s ∈ admissible f P Q U y, r < s := by
  by_contra! hn
  exact h.not_ge (sSup_le hn)

theorem radius_zero (hx : x ∈ U) (h : P x y < radius f P Q U y) :
    Q (f.func x) (f.func y) = 0 := by
  obtain ⟨s, hs, hlt⟩ := radius_witness h
  exact (admissible_iff.mp hs).2 _ hx hlt

theorem le_radius_iff :
    r ≤ radius f P Q U y ↔ ∀ x ∈ U, P x y < r → Q (f.func x) (f.func y) = 0 := by
  constructor
  · exact fun h _ hx hd => radius_zero hx (hd.trans_le h)
  · intro h
    by_contra! he
    obtain ⟨s, hs, ht⟩ := exists_between he
    have ha : s ∈ admissible f P Q U y :=
      admissible_iff.mpr ⟨⟨(zero_le _).trans_lt hs, ht.trans_le le_top⟩,
        fun x hx hd => h x hx (hd.trans ht)⟩
    exact hs.not_ge (le_sSup ha)

theorem uniform_le_point (hy : y ∈ A) : uniform f P Q A U ≤ radius f P Q U y :=
  iInf_le (fun z : A => radius f P Q U z) ⟨y,hy⟩

theorem le_uniform_iff :
    r ≤ uniform f P Q A U ↔ ∀ y ∈ A, ∀ x ∈ U, P x y < r → Q (f.func x) (f.func y) = 0 := by
  constructor
  · exact fun h y hy => le_radius_iff.mp (h.trans (uniform_le_point hy))
  · exact fun h => le_iInf fun y : A => le_radius_iff.mpr (h y y.2)

theorem uniform_eq_inf_separated :
    uniform f P Q U U =
      ⨅ y : U, ⨅ x : U, ⨅ _ : Q (f.func x) (f.func y) ≠ 0, P x y := by
  apply le_antisymm
  · refine le_iInf fun y => le_iInf fun x => le_iInf fun hn => ?_
    exact le_of_not_gt fun h => hn (le_uniform_iff.mp (le_refl (uniform f P Q U U)) (y : X) y.2 (x : X) x.2 h)
  · refine le_uniform_iff.mpr fun y hy x hx h => ?_
    by_contra hn
    have hi : (⨅ y : U, ⨅ x : U, ⨅ _ : Q (f.func x) (f.func y) ≠ 0, P x y) ≤ P x y :=
      iInf_le_of_le ⟨y,hy⟩ (iInf_le_of_le ⟨x,hx⟩ (iInf_le_of_le hn le_rfl))
    exact h.not_ge hi

theorem radius_top (h : ∀ x ∈ U, P x y < ⊤ → Q (f.func x) (f.func y) = 0) :
    radius f P Q U y = ⊤ := top_unique (le_radius_iff.mpr h)

theorem const_subfamily_fiber {J : Set I} (_hU : U ⊆ dom f) (_hJ : J.Nonempty)
    (hc : J ⊆ Const d f U) (hy : y ∈ U) :
    fiber (subfamily_pseudometric d J) f U (f.func y) = U := by
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, (subfamily_zero _ _ _ _).mpr
    fun j hj => hc hj x hx y hy⟩⟩

theorem const_subfamily_radii {J : Set I} (hU : U ⊆ dom f) (_hne : U.Nonempty)
    (hJ : J.Nonempty) (hc : J ⊆ Const d f U) (i : I) :
    (∀ y ∈ U, radius f (d i) (subfamily_pseudometric d J) U y = ⊤) ∧
    uniform f (d i) (subfamily_pseudometric d J) U U = ⊤ := by
  have hp : ∀ y ∈ U, radius f (d i) (subfamily_pseudometric d J) U y = ⊤ := by
    intro y hy
    apply radius_top
    intro x hx _
    have hm : x ∈ fiber (subfamily_pseudometric d J) f U (f.func y) :=
      (const_subfamily_fiber hU hJ hc hy).symm ▸ hx
    exact hm.2
  exact ⟨hp, top_unique (le_iInf fun y : U => (hp y y.2).ge)⟩

theorem ident_fiber_self (hd : ExtendedPseudoMetric X bot (d i)) (hU : U ⊆ dom f)
    (hi : i ∈ Ident d f U) (hy : y ∈ U) :
    fiber (d i) f U (f.func y) = {x ∈ U | d i x y = 0} := by
  ext x
  constructor <;> intro h
  · exact ⟨h.1, (ident_distance hd hU hi x h.1 y hy).symm.trans h.2⟩
  · exact ⟨h.1, (ident_distance hd hU hi x h.1 y hy).trans h.2⟩

theorem ident_radius (hd : ExtendedPseudoMetric X bot (d i)) (hU : U ⊆ dom f)
    (hi : i ∈ Ident d f U) (hy : y ∈ U) (hr : FinitePositive r)
    (h : ball (d i) y r ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r ≤ radius f (d i) (d i) U y ∧ 0 < r := by
  rw [← ident_fiber_self hd hU hi hy] at h
  exact ⟨le_sSup ⟨hr,h⟩, hr.1⟩

theorem radius_subfamily {J : Set I} (_hJ : J.Nonempty) (_hU : U ⊆ dom f) (_hy : y ∈ U) :
    radius f P (subfamily_pseudometric d J) U y = ⨅ j : J, radius f P (d j.1) U y := by
  apply le_antisymm
  · refine le_iInf fun j => le_radius_iff.mpr fun x hx hxlt => ?_
    exact (subfamily_zero _ _ _ _).mp (radius_zero hx hxlt) j.1 j.2
  · refine le_radius_iff.mpr fun x hx hxlt => (subfamily_zero _ _ _ _).mpr fun j hj => ?_
    exact radius_zero hx (hxlt.trans_le (iInf_le (fun j : J => radius f P (d j) U y) ⟨j,hj⟩))

theorem iInf_attains [Finite I] {J : Set I} (hJ : J.Nonempty) (a : J → ℝ≥0∞) :
    ∃ j : J, (⨅ k : J, a k) = a j := by
  haveI : Nonempty J := hJ.to_subtype
  obtain ⟨j,hj⟩ := Finite.exists_min a
  exact ⟨j, le_antisymm (iInf_le a j) (le_iInf hj)⟩

theorem uniform_subfamily {J : Set I} (hJ : J.Nonempty) (hU : U ⊆ dom f) :
    uniform f (d i) (subfamily_pseudometric d J) U U = ⨅ j : J, nullMatrix d f U j i := by
  unfold uniform nullMatrix
  calc
    _ = (⨅ y : U, ⨅ j : J, radius f (d i) (d j) U y) := by
      congr 1
      funext y
      exact radius_subfamily hJ hU y.2
    _ = _ := iInf_comm

theorem uniform_subfamily_antitone {J K : Set I} (hJ : J.Nonempty) (hK : K.Nonempty)
    (hU : U ⊆ dom f) (h : J ⊆ K) :
    uniform f (d i) (subfamily_pseudometric d K) U U ≤
      uniform f (d i) (subfamily_pseudometric d J) U U := by
  rw [uniform_subfamily hK hU, uniform_subfamily hJ hU]
  exact le_iInf fun j : J => iInf_le (fun k : K => nullMatrix d f U k i) ⟨j,h j.2⟩

theorem fiber_step (hQ : ExtendedPseudoMetric X bot Q) (_hU : U ⊆ dom f)
    (_hy : y ∈ U) (_hx : x ∈ U) (h : x ∈ fiber Q f U (f.func y)) :
    Q (f.func y) (f.func x) = 0 := (hQ.symm _ _).trans h.2

theorem radius_step (hP : ExtendedPseudoMetric X bot P) (hQ : ExtendedPseudoMetric X bot Q)
    (hU : U ⊆ dom f) (hy : y ∈ U) (hx : x ∈ U) (h : P y x < radius f P Q U y) :
    Q (f.func y) (f.func x) = 0 :=
  fiber_step hQ hU hy hx ⟨hx, radius_zero hx ((hP.symm x y).trans_lt h)⟩

theorem fiber_comp (hQ : ExtendedPseudoMetric X bot Q) (hU : U ⊆ dom g)
    {x y : X} (_hx : x ∈ dom f) (_hy : y ∈ dom f)
    (hx' : f.func x ∈ U) (hy' : f.func y ∈ U)
    (h : f.func y ∈ fiber Q g U (g.func (f.func x))) :
    Q ((g * f).func x) ((g * f).func y) = 0 :=
  fiber_step (f := g) hQ hU hx' hy' h

theorem radius_comp_zero (_hU : U ⊆ dom (g * f)) (_hne : U.Nonempty)
    (h : ∀ x ∈ f.func '' U, ∀ y ∈ f.func '' U,
      d k x y = 0 → d j (g.func x) (g.func y) = 0) :
    nullMatrix d f U k i ≤ nullMatrix d (g * f) U j i :=
  le_uniform_iff.mpr fun y hy x hx hxy =>
    h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (le_uniform_iff.mp le_rfl y hy x hx hxy)

theorem radius_comp_lip (_hU : U ⊆ dom (g * f)) (_hne : U.Nonempty)
    {L : ℝ≥0∞} (hL : FinitePositive L)
    (h : ∀ x ∈ U, ∀ y ∈ U, d k (f.func x) (f.func y) ≤ L * d i x y) :
    nullMatrix d g (f.func '' U) j k / L ≤ nullMatrix d (g * f) U j i := by
  refine le_uniform_iff.mpr fun y hy x hx hxy => ?_
  have hm := (ENNReal.lt_div_iff_mul_lt (Or.inl hL.1.ne') (Or.inl hL.2.ne)).mp hxy
  rw [mul_comm] at hm
  exact le_uniform_iff.mp (le_refl (nullMatrix d g (f.func '' U) j k)) (f.func y) ⟨y,hy,rfl⟩ (f.func x) ⟨x,hx,rfl⟩
    ((h x hx y hy).trans_lt hm)

theorem radius_restrict (hBA : B ⊆ A) (_hy : y ∈ B) :
    radius f P Q A y ≤ radius f P Q B y :=
  le_radius_iff.mpr fun _ hx h => radius_zero (hBA hx) h

theorem uniform_restrict (hBA : B ⊆ A) (_hA : A ⊆ dom f) (_hn : B.Nonempty) :
    uniform f P Q A A ≤ uniform f P Q B B :=
  le_iInf fun y : B => (uniform_le_point (hBA y.2)).trans (radius_restrict hBA y.2)

theorem uniform_zero (_hA : A ⊆ dom f) (_hn : A.Nonempty)
    (hx : x ∈ A) (hy : y ∈ A) (h : P x y < uniform f P Q A A) :
    Q (f.func x) (f.func y) = 0 := le_uniform_iff.mp le_rfl y hy x hx h

theorem uniform_separation (hA : A ⊆ dom f) (hn : A.Nonempty)
    (hx : x ∈ A) (hy : y ∈ A) (h : 0 < Q (f.func x) (f.func y)) :
    uniform f P Q A A ≤ P x y :=
  le_of_not_gt fun he => h.ne' (uniform_zero hA hn hx hy he)

theorem uniform_failure (_hA : A ⊆ dom f) (_hn : A.Nonempty)
    {τ α : ℝ≥0∞} (_ht : FinitePositive τ) (_ha : FinitePositive α)
    (h : uniform f P Q A A < α) (_haτ : α < τ) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε, FinitePositive ε ∧ P x y < α ∧ ε ≤ Q (f.func x) (f.func y) := by
  classical
  have hbad := mt (le_uniform_iff (f := f) (P := P) (Q := Q) (A := A) (U := A) (r := α)).mpr h.not_ge
  push Not at hbad
  obtain ⟨y,hy,x,hx,hxy,hnz⟩ := hbad
  obtain ⟨ε,hε,hε'⟩ := exists_between (pos_iff_ne_zero.mpr hnz)
  exact ⟨x,hx,y,hy,ε,⟨hε,hε'.trans_le le_top⟩,hxy,hε'.le⟩

theorem threshold_fiber (hA : A ⊆ dom f) (hn : A.Nonempty)
    (_hr : FinitePositive r) (h : r ≤ uniform f P Q A A) (hy : y ∈ A) :
    ball P y r ∩ A ⊆ fiber Q f A (f.func y) :=
  fun _ hx => ⟨hx.2, uniform_zero hA hn hx.2 hy (hx.1.trans_le h)⟩

theorem point_gap [Fintype I] (_hP : ExtendedPseudoMetric X bot (d i))
    (_hQ : ExtendedPseudoMetric X bot (d j)) {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) (hy : y ∈ U)
    (_hr : 0 < radius f (d i) (d j) U y) (hx : x ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius f (d i) (d j) U y) := by
  intro h
  exact h.1.ne' (positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
    (radius_zero hx h.2))

theorem uniform_gap [Fintype I] {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (_hr : 0 < nullMatrix d f U j i) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ nullMatrix d f U j i ≤ d i x y := by
  by_cases h : nullMatrix d f U j i ≤ d i x y
  · exact Or.inr h
  · exact Or.inl (positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
      (uniform_zero hK.2.1 hK.1 hx hy (lt_of_not_ge h)))

noncomputable def diameter (P : X → X → ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨆ x : A, ⨆ y : A, P x y

theorem le_diameter (hx : x ∈ A) (hy : y ∈ A) : P x y ≤ diameter P A :=
  le_iSup_of_le ⟨x,hx⟩ (le_iSup_of_le ⟨y,hy⟩ le_rfl)

structure ScaleFamily (X I : Type) where
  scale : I → {A : Set X // A.Nonempty} → ℝ≥0∞
  monotone : ∀ i A B, A.val ⊆ B.val → scale i A ≤ scale i B

noncomputable def diameterScale (d : I → X → X → ℝ≥0∞) : ScaleFamily X I where
  scale i A := diameter (d i) A.1
  monotone _i A _B h := iSup_le fun x : A.1 => iSup_le fun y : A.1 =>
    le_diameter (h x.2) (h y.2)

noncomputable def thresholdType (σ : ScaleFamily X I) (d : I → X → X → ℝ≥0∞)
    (f : Operator X bot) (A : Set X) (hn : A.Nonempty) (s t : ℝ≥0∞) (i j : I) :
    Bool × Bool := (decide (σ.scale i ⟨A,hn⟩ < s), decide (t ≤ nullMatrix d f A j i))

theorem threshold_four (σ : ScaleFamily X I) (_hA : A ⊆ dom f) (hn : A.Nonempty)
    {s t : ℝ≥0∞} (_hs : FinitePositive s) (_ht : FinitePositive t) :
    let q := thresholdType σ d f A hn s t i j
    let a := σ.scale i ⟨A,hn⟩
    let n := nullMatrix d f A j i
    ((q = (true,true) ↔ a < s ∧ t ≤ n) ∧
     (q = (true,false) ↔ a < s ∧ n < t) ∧
     (q = (false,true) ↔ s ≤ a ∧ t ≤ n) ∧
     (q = (false,false) ↔ s ≤ a ∧ n < t)) ∧
    (q = (true,true) ∨ q = (true,false) ∨ q = (false,true) ∨ q = (false,false)) := by
  dsimp
  constructor
  · simp [thresholdType, not_le, not_lt]
  · rcases thresholdType σ d f A hn s t i j with ⟨a,b⟩
    cases a <;> cases b <;> simp

theorem threshold_scale_mono (σ : ScaleFamily X I) (hn : A.Nonempty)
    {s s' t : ℝ≥0∞} (h : s ≤ s') :
    {p : I × I | (thresholdType σ d f A hn s t p.1 p.2).1 = true} ⊆
      {p : I × I | (thresholdType σ d f A hn s' t p.1 p.2).1 = true} := by
  intro p hp
  simp only [Set.mem_setOf_eq, thresholdType, decide_eq_true_eq] at hp ⊢
  exact hp.trans_le h

theorem threshold_null_antitone (σ : ScaleFamily X I) (hn : A.Nonempty)
    {s t t' : ℝ≥0∞} (h : t ≤ t') :
    {p : I × I | (thresholdType σ d f A hn s t' p.1 p.2).2 = true} ⊆
      {p : I × I | (thresholdType σ d f A hn s t p.1 p.2).2 = true} := by
  intro p hp
  simp only [Set.mem_setOf_eq, thresholdType, decide_eq_true_eq] at hp ⊢
  exact h.trans hp

theorem scale_restrict (σ : ScaleFamily X I) (hn : A.Nonempty) (hb : B.Nonempty)
    (hBA : B ⊆ A) (_hA : A ⊆ dom f) {s : ℝ≥0∞} :
    σ.scale i ⟨B,hb⟩ ≤ σ.scale i ⟨A,hn⟩ ∧
    (σ.scale i ⟨A,hn⟩ < s → σ.scale i ⟨B,hb⟩ < s) :=
  ⟨σ.monotone i _ _ hBA, fun h => (σ.monotone i _ _ hBA).trans_lt h⟩

theorem small_iff (hA : A ⊆ dom f) (hn : A.Nonempty)
    {s t : ℝ≥0∞} (_hs : FinitePositive s) (_ht : FinitePositive t)
    (hdiam : diameter P A < s) (hst : s ≤ t) :
    t ≤ uniform f P Q A A ↔ ∀ x ∈ A, ∀ y ∈ A, Q (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx y hy
    exact uniform_zero hA hn hx hy ((le_diameter hx hy).trans_lt (hdiam.trans_le (hst.trans h)))
  · exact fun h => le_uniform_iff.mpr fun y hy x hx _ => h x hx y hy

end Chapter
```

```lean filename=Chapter/Readouts.lean
import Chapter.Step

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

namespace Affine

noncomputable def d : Unit → Option ℝ → Option ℝ → ℝ≥0∞ := fun _ => absDist
def f := liftRealMap (fun x => 2*x-1)
def U : Set (Option ℝ) := {some 0, some 1}

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := read_legal abs

theorem values :
    f.func (some 0) = some (-1) ∧ f.func (some 1) = some 1 ∧
    (f*f).func (some 0) = some (-3) ∧ (f*f).func (some 1) = some 1 := by
  norm_num [f]

theorem first :
    U ⊆ dom f ∧ fiber absDist f U (f.func (some 0)) = U ∧
      Const d f U = {()} ∧ Ident d f U = ∅ ∧ Active d f U = ∅ := by
  obtain ⟨h0,h1,_,_⟩ := values
  have hc : () ∈ Const d f U := by
    intro x hx y hy
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [d,h0,h1]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact Option.some_ne_none _
  · exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx,hc x hx _ (by simp [U])⟩)
  all_goals
    ext i
    cases i
    simp [Active, Ident, hc]

theorem second :
    U ⊆ dom (f*f) ∧ fiber absDist (f*f) U ((f*f).func (some 0)) = {some 0} ∧
      Const d (f*f) U = ∅ ∧ Ident d (f*f) U = ∅ ∧ Active d (f*f) U = {()} := by
  obtain ⟨_,_,h0,h1⟩ := values
  have hne : () ∉ Const d (f*f) U := by
    intro h
    have he := h (some 0) (by simp [U]) (some 1) (by simp [U])
    change absDist ((f*f).func (some 0)) ((f*f).func (some 1)) = 0 at he
    norm_num [h0,h1,abs_zero] at he
  have hni : () ∉ Ident d (f*f) U := by
    intro h
    have he := h.2 (some 0) (by simp [U])
    change absDist ((f*f).func (some 0)) (some 0) = 0 at he
    norm_num [h0,abs_zero] at he
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact Option.some_ne_none _
  · apply Set.Subset.antisymm
    · rintro x ⟨hx,he⟩
      simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp
      · norm_num [h0,h1,abs_zero] at he
    · intro x hx
      have he : x = some (0 : ℝ) := hx
      subst x
      exact ⟨by simp [U], (gauge ()).dist_self _⟩
  all_goals
    ext i
    cases i
    simp [Active, hne, hni]

theorem literal_constant (g : Operator (Option ℝ) none) (a : ℝ)
    (h : ∀ x ∈ U, g.func x = some a) :
    (∀ x ∈ U, (g*g).func x = g.func (some a)) ∧
    (U ⊆ dom (g*g) ↔ g.func (some a) ≠ none) ∧
    (U ⊆ dom (g*g) → fiber absDist (g*g) U ((g*g).func (some 0)) = U) ∧
    (g.func (some a) = none → U ∩ dom (g*g) = ∅) := by
  have he (x : Option ℝ) (hx : x ∈ U) : (g*g).func x = g.func (some a) := by
    rw [mul_func, h x hx]
  have h0 : some (0 : ℝ) ∈ U := by simp [U]
  refine ⟨he,⟨fun hd => (he _ h0) ▸ hd h0,
    fun hn x hx => show (g*g).func x ≠ none from (he x hx).symm ▸ hn⟩,?_ ,?_⟩
  · intro hd
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, by rw [he x hx, he _ h0]; exact (gauge ()).dist_self _⟩⟩
  · intro hb
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hd⟩
    exact hd ((he x hx).trans hb)

end Affine

namespace Translation

def f := liftRealMap (fun x => x + 1)
def U : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
def V : Set (Option ℝ) := {some (-2),some (-1),some 1,some 3}

theorem gauge : ExtendedPseudoMetric (Option ℝ) none absDist := read_legal abs

theorem domains : U ⊆ dom f ∧ U ⊆ dom (1 : Operator (Option ℝ) none) := by
  have h : U ⊆ {x | x ≠ none} := by
    intro x hx
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _
  refine ⟨?_,h⟩
  intro x hx
  cases x with
  | none => exact (h hx rfl).elim
  | some a => exact Option.some_ne_none _

theorem image : f.func '' U = V := by
  norm_num [f,U,V,Set.image_insert_eq]

theorem fiber_table (g : Operator (Option ℝ) none) (y : Option ℝ) (B : Set (Option ℝ))
    (hs : B ⊆ U)
    (h0 : absDist (g.func (some (-3))) y = 0 ↔ some (-3) ∈ B)
    (h1 : absDist (g.func (some (-2))) y = 0 ↔ some (-2) ∈ B)
    (h2 : absDist (g.func (some 0)) y = 0 ↔ some 0 ∈ B)
    (h3 : absDist (g.func (some 2)) y = 0 ↔ some 2 ∈ B) :
    fiber absDist g U y = B := by
  ext x
  by_cases h : x ∈ U
  · have he : x = some (-3) ∨ x = some (-2) ∨ x = some 0 ∨ x = some 2 := by
      simpa only [U,Set.mem_insert_iff,Set.mem_singleton_iff] using h
    rcases he with rfl | rfl | rfl | rfl
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h0
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h1
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h2
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h3
  · exact ⟨fun hx => (h hx.1).elim, fun hx => (h (hs hx)).elim⟩

@[simp] theorem identity_value (x : Option ℝ) : (1 : Operator (Option ℝ) none).func x = x := rfl

theorem partitions :
    fiberBlocks absDist (1 : Operator (Option ℝ) none) U =
      {{some (-3)}, {some (-2), some 2}, {some 0}} ∧
    fiberBlocks absDist f U =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  have a : fiber absDist (1 : Operator (Option ℝ) none) U (some (-3)) = {some (-3)} := by
    apply fiber_table <;> norm_num [U]
  have b : fiber absDist (1 : Operator (Option ℝ) none) U (some (-2)) = {some (-2),some 2} := by
    apply fiber_table <;> norm_num [U, Set.insert_subset_iff]
  have c : fiber absDist (1 : Operator (Option ℝ) none) U (some 0) = {some 0} := by
    apply fiber_table <;> norm_num [U]
  have e : fiber absDist (1 : Operator (Option ℝ) none) U (some 2) = {some (-2),some 2} := by
    apply fiber_table <;> norm_num [U, Set.insert_subset_iff]
  have a' : fiber absDist f U (some (-2)) = {some (-3)} := by
    apply fiber_table <;> norm_num [U,f]
  have b' : fiber absDist f U (some (-1)) = {some (-2),some 0} := by
    apply fiber_table <;> norm_num [U,f, Set.insert_subset_iff]
  have c' : fiber absDist f U (some 1) = {some (-2),some 0} := by
    apply fiber_table <;> norm_num [U,f, Set.insert_subset_iff]
  have e' : fiber absDist f U (some 3) = {some 2} := by
    apply fiber_table <;> norm_num [U,f]
  constructor
  · have hid : (1 : Operator (Option ℝ) none).func '' U = U := by simp
    rw [fiberBlocks,hid]
    conv_lhs => arg 2; unfold U
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [a,b,c,e]
    ext S
    simp
    tauto
  · rw [fiberBlocks,image]
    simp only [V, Set.image_insert_eq, Set.image_singleton,a',b',c',e']
    ext S
    simp

noncomputable def ε : ℝ≥0∞ := ENNReal.ofReal (3/2)

theorem cover_U : covering_number absDist ε U = 2 := by
  apply le_antisymm
  · apply two_center_upper (some (-2)) (some 0) (by simp [U]) (by simp [U])
    intro x hx
    simp only [U,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · left; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
    · left; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
    · right; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
    · left; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
  · apply two_center_lower ⟨some 0,by simp [U]⟩
    intro x hx
    simp only [U,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    have hε : 0 ≤ (3/2 : ℝ) := by norm_num
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩
    · exact ⟨some 2,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩

theorem cover_V : covering_number absDist ε V = 1 := by
  apply cover_single_center
  refine ⟨some (-2),by simp [V],?_⟩
  intro x hx
  simp only [V,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']

theorem covering_and_gap :
    covering_number absDist ε U = 2 ∧ covering_number absDist ε (f.func '' U) = 1 ∧
      ∃ h : GapDefined f absDist absDist U ε, entropyGap f absDist absDist U ε h = 1 := by
  have he : covering_number absDist ε (f.func '' U) = 1 := image.symm ▸ cover_V
  refine ⟨cover_U,he,Or.inr (he.trans_lt (by simp)),?_⟩
  norm_num [entropyGap, metric_entropy, log2_ereal, cover_U, he, Real.logb_self_eq_one]

end Translation
end Chapter
```

```lean filename=Chapter/Rearrange.lean
import Chapter.Step
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter.Rearrange

def U : Set (Option ℝ) := {some 0,some 1,some 2,some 3}

noncomputable def f : Operator (Option ℝ) none := by
  classical
  exact ⟨fun x => if x ∈ U then x else none, by simp [U]⟩

noncomputable def g : Operator (Option ℝ) none :=
  ⟨fun x => if x = some 0 then some 0 else if x = some 1 then some 3 else
    if x = some 2 then some 1 else if x = some 3 then some 2 else none, by simp⟩

noncomputable def d : Unit → Option ℝ → Option ℝ → ℝ≥0∞ := fun _ => realDist

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := read_legal id

theorem mem_U (x : Option ℝ) : x ∈ U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 :=
  by simp [U]

theorem f_value {x : Option ℝ} (hx : x ∈ U) : f.func x = x := by
  simp [f,hx]

theorem g_values : g.func (some 0) = some 0 ∧ g.func (some 1) = some 3 ∧
    g.func (some 2) = some 1 ∧ g.func (some 3) = some 2 := by norm_num [g]

theorem outside {x : Option ℝ} (hx : x ∉ U) : f.func x = none ∧ g.func x = none := by
  have hn : x ≠ some 0 ∧ x ≠ some 1 ∧ x ≠ some 2 ∧ x ≠ some 3 := by
    simpa only [mem_U, not_or] using hx
  simp [f,g,hx,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem domains : U ⊆ dom f ∧ U ⊆ dom g := by
  constructor
  · intro x hx
    show f.func x ≠ none
    rw [f_value hx]
    rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _
  · intro x hx
    show g.func x ≠ none
    rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;> simp [g]

theorem images : f.func '' U = U ∧ g.func '' U = U := by
  constructor
  · exact Set.image_congr (fun _ hx => f_value hx) |>.trans (Set.image_id U)
  · obtain ⟨h0,h1,h2,h3⟩ := g_values
    simp only [U, Set.image_insert_eq, Set.image_singleton, h0,h1,h2,h3]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

theorem separated {x y : Option ℝ} (hx : x ∈ U) (hy : y ∈ U) (h : x ≠ y) :
    1 ≤ realDist x y := by
  rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;>
    rcases (mem_U y).mp hy with rfl | rfl | rfl | rfl <;>
    (norm_num at h <;> norm_num)

theorem at_most_three {x y : Option ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    realDist x y ≤ 3 := by
  rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;>
    rcases (mem_U y).mp hy with rfl | rfl | rfl | rfl <;>
    norm_num

noncomputable def centers : Finset (Option ℝ) := {some 0,some 1,some 2,some 3}

theorem centers_set : (↑centers : Set (Option ℝ)) = U := by
  classical
  ext x
  simp [centers,U]

theorem centers_card : centers.card = 4 := by
  classical
  norm_num [centers,Finset.card_insert_of_notMem]

theorem cover_small {r : ℝ≥0∞} (hr : 0 < r) (hr1 : r ≤ 1) :
    covering_number realDist r U = 4 := by
  classical
  apply le_antisymm
  · have hnet : InternalEpsilonNet realDist r U centers := by
      refine ⟨centers_set.le,fun x hx => ⟨x,?_ ,?_⟩⟩
      · exact show x ∈ (↑centers : Set (Option ℝ)) from centers_set.symm ▸ hx
      · rw [show realDist x x = 0 from (gauge ()).dist_self x]
        exact hr
    simpa [centers_card] using cover_le_card hnet
  · change ((4 : ℕ) : ℝ≥0∞) ≤ _
    apply card_lower_cover
    intro S hS
    rw [← centers_card]
    apply Finset.card_le_card
    intro x hx
    have hxu : x ∈ U := centers_set ▸ hx
    obtain ⟨c,hc,hxc⟩ := hS.2 x hxu
    have he : x = c := by
      by_contra hn
      exact (hxc.trans_le hr1).not_ge (separated hxu (hS.1 hc) hn)
    simpa [he] using hc

theorem cover_middle {r : ℝ≥0∞} (h1 : 1 < r) (h2 : r ≤ 2) :
    covering_number realDist r U = 2 := by
  apply le_antisymm
  · apply two_center_upper (some 0) (some 2) (by simp [U]) (by simp [U])
    intro x hx
    rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl
    · left; simpa using zero_lt_one.trans h1
    · left; simpa using h1
    · right; simpa using zero_lt_one.trans h1
    · right; (convert h1 using 1; norm_num)
  · apply two_center_lower ⟨some 0,by simp [U]⟩
    intro c hc
    rcases (mem_U c).mp hc with rfl | rfl | rfl | rfl
    · exact ⟨some 3, by simp [U], h2.trans (by norm_num)⟩
    · exact ⟨some 3, by simp [U], h2.trans (by norm_num)⟩
    · exact ⟨some 0, by simp [U], h2.trans (by norm_num)⟩
    · exact ⟨some 0, by simp [U], h2.trans (by norm_num)⟩

theorem cover_large {r : ℝ≥0∞} (hr : 2 < r) :
    covering_number realDist r U = 1 := by
  apply cover_single_center
  refine ⟨some 1, by simp [U],?_⟩
  intro x hx
  apply lt_of_le_of_lt _ hr
  rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;> norm_num

theorem cover_all {r : ℝ≥0∞} (hr : FinitePositive r) :
    covering_number realDist r U = if r ≤ 1 then 4 else if r ≤ 2 then 2 else 1 := by
  split
  · exact cover_small hr.1 (by assumption)
  · split
    · exact cover_middle (lt_of_not_ge (by assumption)) (by assumption)
    · exact cover_large (lt_of_not_ge (by assumption))

theorem excluded_center : some (3/2 : ℝ) ∉ U ∧
    ¬ InternalEpsilonNet realDist (ENNReal.ofReal (7/4)) U {some (3/2 : ℝ)} := by
  have h : some (3/2 : ℝ) ∉ U := by norm_num [U]
  exact ⟨h, fun H => h (H.1 (Finset.mem_singleton_self _))⟩

theorem image_statistics {r : ℝ≥0∞} (hr : FinitePositive r) :
    (∀ h : Operator (Option ℝ) none, (h = f ∨ h = g) →
      covering_number realDist r (h.func '' U) = covering_number realDist r U ∧
      ∃ hg : GapDefined h realDist realDist U r, entropyGap h realDist realDist U r hg = 0) := by
  intro h hh
  have hI : h.func '' U = U := hh.elim (fun e => e.symm ▸ images.1) (fun e => e.symm ▸ images.2)
  have hn : U.Nonempty := ⟨some 0,by simp [U]⟩
  have hf : covering_number realDist r U < ⊤ := by
    exact cover_finite (centers_set ▸ centers.finite_toSet) (fun x _ => (gauge ()).dist_self x) hr.1
  have he : covering_number realDist r (h.func '' U) = covering_number realDist r U :=
    congrArg (covering_number realDist r) hI
  exact ⟨he,Or.inl hf,equal_cover_gap hn he.symm (Or.inl hf)⟩

theorem f_optimal (L : ℝ≥0∞) : HasScalarLipBound d f U () () L ↔ 1 ≤ L := by
  constructor
  · intro h
    have he := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,f,U] at he
    exact he
  · intro h
    refine ⟨domains.1,fun x hx y hy => ?_⟩
    rw [f_value hx, f_value hy]
    calc
      d () x y = 1 * d () x y := (one_mul _).symm
      _ ≤ L * d () x y := mul_le_mul_left h _

theorem g_optimal (L : ℝ≥0∞) : HasScalarLipBound d g U () () L ↔ 3 ≤ L := by
  constructor
  · intro h
    have he := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,g] at he
    exact he
  · intro h
    refine ⟨domains.2,fun x hx y hy => ?_⟩
    by_cases he : x = y
    · subst y
      simp [(gauge ()).dist_self]
    · have hx' : g.func x ∈ U := images.2 ▸ (show g.func x ∈ g.func '' U from ⟨x,hx,rfl⟩)
      have hy' : g.func y ∈ U := images.2 ▸ (show g.func y ∈ g.func '' U from ⟨y,hy,rfl⟩)
      calc
        _ ≤ (3 : ℝ≥0∞) := at_most_three hx' hy'
        _ = 3 * 1 := by simp
        _ ≤ L * d () x y := mul_le_mul' h (separated hx hy he)

theorem bounds_at_seven_fourths :
    let r := ENNReal.ofReal (7/4)
    covering_number realDist r (f.func '' U) = 2 ∧
      covering_number realDist r (g.func '' U) = 2 ∧
      covering_number realDist r (f.func '' U) ≤ covering_number realDist (r/1) U ∧
      covering_number realDist (r/1) U = 2 ∧
      covering_number realDist r (g.func '' U) ≤ covering_number realDist (r/3) U ∧
      covering_number realDist (r/3) U = 4 := by
  dsimp
  let r := ENNReal.ofReal (7/4)
  have hr : covering_number realDist r U = 2 := by
    apply cover_middle
    · exact (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mpr (by norm_num)
    · exact ENNReal.ofReal_le_ofNat.mpr (by norm_num)
  have hp1 : FinitePositive (1 : ℝ≥0∞) := ⟨by norm_num,by simp⟩
  have hp3 : FinitePositive (3 : ℝ≥0∞) := ⟨by norm_num,by simp⟩
  have hf := lip_cover (r := r) hp1 ((f_optimal 1).mpr le_rfl).2
  have hg := lip_cover (r := r) hp3 ((g_optimal 3).mpr le_rfl).2
  refine ⟨images.1.symm ▸ hr, images.2.symm ▸ hr, hf, by simpa using hr, hg,?_⟩
  apply cover_small
  · exact ENNReal.div_pos (by simp) hp3.2.ne
  · rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_one.mpr (by norm_num [r])

end Chapter.Rearrange
```

```lean filename=Chapter/Representations.lean
import Chapter.Radius
import Chapter.Cover

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U A : Set X} {J K : Set I}
variable {i j : I} {x y : X} {P Q : X → X → ℝ≥0∞}

theorem component_membership (_hU : U ⊆ dom f) :
    (i ∈ Const d f U ↔ ∀ a ∈ U, ∀ b ∈ U, d i (f.func a) (f.func b) = 0) ∧
    (i ∈ Ident d f U ↔
      (¬ ∀ a ∈ U, ∀ b ∈ U, d i (f.func a) (f.func b) = 0) ∧
      ∀ a ∈ U, d i (f.func a) a = 0) ∧
    (i ∈ Active d f U ↔ i ∉ Const d f U ∧ i ∉ Ident d f U) :=
  ⟨Iff.rfl, Iff.rfl, not_or⟩

theorem fiber_membership (_hU : U ⊆ dom f) (_hJ : J.Nonempty) :
    x ∈ fiber (subfamily_pseudometric d J) f U y ↔
      x ∈ U ∧ ∀ j ∈ J, d j (f.func x) y = 0 := by
  simp [fiber, subfamily_zero]

theorem fiber_missing (_hU : U ⊆ dom f) (_hJ : J.Nonempty)
    (h : ∀ z ∈ f.func '' U, 0 < subfamily_pseudometric d J z y) :
    fiber (subfamily_pseudometric d J) f U y = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx => (h _ ⟨x,hx.1,rfl⟩).ne' hx.2

theorem finer_iff_blocks (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f ∩ dom g) :
    FiberFiner d U f g ↔
      ∀ B ∈ fiberBlocks (subfamily_pseudometric d Set.univ) f U,
        ∃ C ∈ fiberBlocks (subfamily_pseudometric d Set.univ) g U, B ⊆ C := by
  constructor
  · rintro h _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨_,⟨g.func x,⟨x,hx,rfl⟩,rfl⟩,fun y hy => ?_⟩
    exact (zeroPairs_fiber hd (f := g) hx hy.1).mp
      (h ((zeroPairs_fiber hd hx hy.1).mpr hy))
  · rintro h ⟨x,y⟩ hp
    have hx : x ∈ U := hp.1
    have hy : y ∈ U := hp.2.1
    obtain ⟨_,⟨z,hz,rfl⟩,hsub⟩ := h _ ⟨f.func x,⟨x,hx,rfl⟩,rfl⟩
    have hx0 : x ∈ fiber (subfamily_pseudometric d Set.univ) g U z :=
      hsub ((zeroPairs_fiber hd hx hx).mp ⟨hx,hx,fun i => (hd i).dist_self _⟩)
    have hy0 : y ∈ fiber (subfamily_pseudometric d Set.univ) g U z :=
      hsub ((zeroPairs_fiber hd hx hy).mp hp)
    refine ⟨hx,hy,fun j => ?_⟩
    have ha := (subfamily_zero d Set.univ _ _).mp hx0.2 j (Set.mem_univ _)
    have hb := (subfamily_zero d Set.univ _ _).mp hy0.2 j (Set.mem_univ _)
    exact (zero_left (hd j) ha _).trans (((hd j).symm _ _).trans hb)

theorem finer_iff_quotient (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) : FiberFiner d U f g ↔ QuotFactor hd f g U :=
  (quot_factor hd hU).symm

theorem radius_ball_formula (_hU : U ⊆ dom f) (_hy : y ∈ U) :
    radius f P Q U y =
      sSup {r | 0 < r ∧ r < ⊤ ∧ ball P y r ∩ U ⊆ {x ∈ U | Q (f.func x) (f.func y) = 0}} := by
  unfold radius
  congr 1
  ext r
  exact and_assoc

theorem radius_singleton (_hU : U ⊆ dom f) (_hy : y ∈ U) :
    radius f (d i) (subfamily_pseudometric d {j}) U y = radius f (d i) (d j) U y := by
  rw [subfamily_pseudometric_singleton]

theorem uniform_ball_formula (_hn : A.Nonempty) (_hAU : A ⊆ U) (_hU : U ⊆ dom f) :
    uniform f P Q A U = ⨅ y ∈ A, radius f P Q U y := by
  unfold uniform
  apply le_antisymm
  · exact le_iInf fun y => le_iInf fun hy => uniform_le_point (f := f) (P := P) (Q := Q) (U := U) hy
  · exact le_iInf fun y : A => iInf_le_of_le (y : X) (iInf_le_of_le y.2 le_rfl)

theorem nullMatrix_formula (hn : U.Nonempty) (hU : U ⊆ dom f) :
    nullMatrix d f U j i = ⨅ y ∈ U, radius f (d i) (d j) U y :=
  uniform_ball_formula hn Set.Subset.rfl hU

theorem radius_minimum [Finite I] (hJ : J.Nonempty) (hU : U ⊆ dom f) (hy : y ∈ U) :
    ∃ j ∈ J, radius f P (subfamily_pseudometric d J) U y = radius f P (d j) U y ∧
      ∀ k ∈ J, radius f P (d j) U y ≤ radius f P (d k) U y := by
  rw [radius_subfamily hJ hU hy]
  obtain ⟨j,hj⟩ := iInf_attains hJ (fun j => radius f P (d j) U y)
  exact ⟨j,j.2,hj,fun k hk => hj ▸ iInf_le (fun l : J => radius f P (d l) U y) ⟨k,hk⟩⟩

theorem uniform_minimum [Finite I] (hJ : J.Nonempty) (_hn : U.Nonempty) (hU : U ⊆ dom f) :
    ∃ j ∈ J, uniform f (d i) (subfamily_pseudometric d J) U U = nullMatrix d f U j i ∧
      ∀ k ∈ J, nullMatrix d f U j i ≤ nullMatrix d f U k i := by
  rw [uniform_subfamily hJ hU]
  obtain ⟨j,hj⟩ := iInf_attains hJ (fun j => nullMatrix d f U j i)
  exact ⟨j,j.2,hj,fun k hk => hj ▸ iInf_le (fun l : J => nullMatrix d f U l i) ⟨k,hk⟩⟩

theorem threshold_exclusive (σ : ScaleFamily X I) (hn : A.Nonempty) (s t : ℝ≥0∞) :
    ∃! q : Bool × Bool, q = thresholdType σ d f A hn s t i j :=
  ⟨_,rfl,fun _ h => h⟩

theorem small_threshold_type (hA : A ⊆ dom f) (hn : A.Nonempty) {s t : ℝ≥0∞}
    (hs : FinitePositive s) (ht : FinitePositive t)
    (hd : diameter (d i) A < s) (hst : s ≤ t) :
    (thresholdType (diameterScale d) d f A hn s t i j).1 = true ∧
    ((thresholdType (diameterScale d) d f A hn s t i j).2 = true ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0) := by
  simp only [thresholdType, diameterScale, decide_eq_true_eq]
  exact ⟨hd,small_iff hA hn hs ht hd hst⟩

theorem subfamily_cover_singleton (r : ℝ≥0∞) :
    covering_number (subfamily_pseudometric d {i}) r U = covering_number (d i) r U ∧
    subfamily_metric_entropy d {i} r U = metric_entropy (d i) r U := by
  constructor
  · rw [subfamily_pseudometric_singleton]
  · exact subfamily_metric_entropy_singleton d i r U

def SubfamilyGapDefined (d : I → X → X → ℝ≥0∞) (f : Operator X bot)
    (U : Set X) (J K : Set I) (r : ℝ≥0∞) : Prop :=
  GapDefined f (subfamily_pseudometric d J) (subfamily_pseudometric d K) U r

noncomputable def subfamilyGap (d : I → X → X → ℝ≥0∞) (f : Operator X bot)
    (U : Set X) (J K : Set I) (r : ℝ≥0∞)
    (_hU : U ⊆ dom f) (_hne : U.Nonempty) (_hJ : J.Nonempty) (_hK : K.Nonempty)
    (_hr : FinitePositive r) (h : SubfamilyGapDefined d f U J K r) : EReal :=
  entropyGap f (subfamily_pseudometric d J) (subfamily_pseudometric d K) U r h

theorem subfamily_gap_formula {r : ℝ≥0∞} (hU : U ⊆ dom f) (hne : U.Nonempty)
    (hJ : J.Nonempty) (hK : K.Nonempty) (hr : FinitePositive r)
    (h : SubfamilyGapDefined d f U J K r) :
    subfamilyGap d f U J K r hU hne hJ hK hr h =
      subfamily_metric_entropy d J r U - subfamily_metric_entropy d K r (f.func '' U) := rfl

theorem gap_excludes_double_infinity {r : ℝ≥0∞} :
    ¬ SubfamilyGapDefined d f U J K r ↔
      covering_number (subfamily_pseudometric d J) r U = ⊤ ∧
        covering_number (subfamily_pseudometric d K) r (f.func '' U) = ⊤ := by
  simp [SubfamilyGapDefined, GapDefined, not_or, not_lt]


theorem threshold_domain_radius {B : Set X}
    (_hB : B.Nonempty) (hBA : B ⊆ A) (_hA : A ⊆ dom f) (hy : y ∈ B) :
    radius f P Q A y ≤ radius f P Q B y := radius_restrict hBA hy

theorem finite_cover_minimum {r : ℝ≥0∞} (_hr : FinitePositive r)
    (h : covering_number P r U < ⊤) :
    ∃ S : Finset X, (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball P c r ∧
      covering_number P r U = S.card ∧
      ∀ T : Finset X, (↑T : Set X) ⊆ U → U ⊆ ⋃ c ∈ T, ball P c r → S.card ≤ T.card := by
  classical
  have hnet : ∃ S, InternalEpsilonNet P r U S := by
    by_contra hn
    exact h.ne ((covering_number_eq_top_iff _ _ _).mpr hn)
  obtain ⟨S,hS,he,hm⟩ := covering_number_attained _ _ _ hnet
  have hs := net_iff_ball_cover.mp hS
  exact ⟨S,hs.1,hs.2,he,fun T ht ht' => hm T (net_iff_ball_cover.mpr ⟨ht,ht'⟩)⟩

theorem finite_gap_conditions {r : ℝ≥0∞} (_hr : FinitePositive r) :
    covering_number P r U = ⊤ ↔
      ¬ ∃ S : Finset X, (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball P c r := by
  rw [covering_number_eq_top_iff]
  simp only [net_iff_ball_cover]


theorem chain_domain_valid (fs : List (Operator X bot)) (U : Set X) :
    U ⊆ dom (chain fs) →
      match fs with
      | [] => U ⊆ dom (1 : Operator X bot)
      | f :: tail => U ⊆ dom f ∧ f.func '' U ⊆ dom (chain tail) := by
  cases fs with
  | nil => exact id
  | cons f tail => exact stage_domains

theorem uniform_gap_disjoint (hr : 0 < nullMatrix d f U j i) :
    Disjoint ({0} : Set ℝ≥0∞) (Set.Ici (nullMatrix d f U j i)) := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have he : x = 0 := hx
  exact hr.not_ge (he ▸ hx')

end Chapter
```

```lean filename=Chapter/Step.lean
import Chapter.Models

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

theorem two_center_upper {X : Type} {D : X → X → ℝ≥0∞} {U : Set X} {r : ℝ≥0∞}
    (a b : X) (ha : a ∈ U) (hb : b ∈ U) (h : ∀ x ∈ U, D x a < r ∨ D x b < r) :
    covering_number D r U ≤ 2 := by
  classical
  have hn : InternalEpsilonNet D r U {a,b} := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact (Finset.mem_singleton.mp hx).symm ▸ hb
    · intro x hx
      rcases h x hx with hx' | hx'
      · exact ⟨a,by simp,hx'⟩
      · exact ⟨b,by simp,hx'⟩
  exact (cover_le_card hn).trans (by simpa using
    (show (({a,b} : Finset X).card : ℝ≥0∞) ≤ (2 : ℕ) by
      exact_mod_cast Finset.card_insert_le a ({b} : Finset X)))

theorem two_center_lower {X : Type} {D : X → X → ℝ≥0∞} {U : Set X} {r : ℝ≥0∞}
    (hn : U.Nonempty) (h : ∀ c ∈ U, ∃ x ∈ U, r ≤ D x c) :
    2 ≤ covering_number D r U := by
  classical
  change ((2 : ℕ) : ℝ≥0∞) ≤ _
  apply card_lower_cover
  intro S hs
  by_contra! hh
  obtain ⟨x,hx⟩ := hn
  obtain ⟨c,hc,_⟩ := hs.2 x hx
  obtain ⟨z,hz,hcz⟩ := h c (hs.1 hc)
  obtain ⟨c',hc',hz'⟩ := hs.2 z hz
  have he : c' = c := Finset.card_le_one.mp (by omega) c' hc' c hc
  exact (not_lt_of_ge hcz) (he ▸ hz')

namespace Step

noncomputable def step (x : ℝ) : ℝ := if x < 0 then 0 else 1
noncomputable def f := liftRealMap step
def S : Set ℝ := Set.Ico (-1) 0 ∪ Set.Ioc 0 1
def U : Set (Option ℝ) := realSet S

theorem legal : ExtendedPseudoMetric (Option ℝ) none realDist ∧ U.Nonempty ∧ U ⊆ dom f :=
  ⟨read_legal id, ⟨some 1, by simp [U,S]⟩, realSet_domain step _⟩

theorem step_pair (x y : ℝ) (_hx : x ≠ 0) (_hy : y ≠ 0) :
    step x ≠ step y → |y| ≤ |x - y| := by
  intro h
  by_cases hy' : y < 0
  · have hx' : 0 ≤ x := by
      by_contra! hn
      exact h (by simp [step, hn, hy'])
    rw [abs_of_neg hy', abs_of_nonneg (by linarith)]
    linarith
  · have hx' : x < 0 := by
      by_contra! hn
      exact h (by simp [step, not_lt.mpr hn, hy'])
    rw [abs_of_nonneg (le_of_not_gt hy'), abs_of_neg (by linarith [le_of_not_gt hy'])]
    linarith

theorem nonzero_of_mem {x : ℝ} (hx : x ∈ S) : x ≠ 0 := by
  rcases hx with h | h
  · exact h.2.ne
  · exact h.1.ne'

theorem admissible_exact {y : ℝ} (hy : y ∈ S) {r : ℝ≥0∞} :
    r ∈ admissible f realDist realDist U (some y) ↔
      FinitePositive r ∧ r ≤ ENNReal.ofReal |y| := by
  rw [admissible_iff]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr, le_of_not_gt fun hr' => ?_⟩
    have hylt : |y| < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mp hr'
    let a := min ((r.toReal - |y|)/2) 1
    have ha : 0 < a := lt_min (by linarith) zero_lt_one
    have ha1 : a ≤ 1 := min_le_right _ _
    have har : a + |y| < r.toReal := by
      have hh : a ≤ (r.toReal - |y|)/2 := min_le_left _ _
      linarith
    by_cases hyn : y < 0
    · have hx : a ∈ S := Or.inr ⟨ha,ha1⟩
      have hd : realDist (some a) (some y) < r := by
        rw [real_some, ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne,
          abs_of_pos (by linarith)]
        rw [abs_of_neg hyn] at har
        linarith
      have he := (real_zero _ _).mp (h (some a) ((mem_realSet _ _).mpr hx) hd)
      simp [step, not_lt.mpr ha.le, hyn] at he
    · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hyn) (nonzero_of_mem hy).symm
      have hx : -a ∈ S := Or.inl ⟨by linarith,by linarith⟩
      have hd : realDist (some (-a)) (some y) < r := by
        rw [real_some, ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne,
          abs_of_neg (by linarith)]
        rw [abs_of_pos hyp] at har
        linarith
      have he := (real_zero _ _).mp (h (some (-a)) ((mem_realSet _ _).mpr hx) hd)
      simp [step, show -a < 0 by linarith, hyn] at he
  · rintro ⟨hr,hr'⟩
    refine ⟨hr,?_⟩
    rintro _ ⟨x,hx,rfl⟩ hd
    apply (real_zero _ _).mpr
    by_contra hn
    exact (hd.trans_le hr').not_ge (ENNReal.ofReal_le_ofReal
      (step_pair x y (nonzero_of_mem hx) (nonzero_of_mem hy) hn))

theorem pointwise {y : ℝ} (hy : y ∈ S) :
    radius f realDist realDist U (some y) = ENNReal.ofReal |y| ∧
    0 < radius f realDist realDist U (some y) := by
  have hpos : 0 < ENNReal.ofReal |y| := ENNReal.ofReal_pos.mpr (abs_pos.mpr (nonzero_of_mem hy))
  have he : radius f realDist realDist U (some y) = ENNReal.ofReal |y| :=
    le_antisymm (sSup_le fun r hr => ((admissible_exact hy).mp hr).2)
      (le_sSup ((admissible_exact hy).mpr ⟨⟨hpos, ENNReal.ofReal_lt_top⟩,le_rfl⟩))
  exact ⟨he,he.symm ▸ hpos⟩

theorem small_positive {r : ℝ≥0∞} (hr : FinitePositive r) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < r := by
  have h : 0 < r.toReal := ENNReal.toReal_pos hr.1.ne' hr.2.ne
  refine ⟨min (r.toReal / 4) 1, lt_min (by linarith) zero_lt_one, min_le_right _ _, ?_⟩
  have h1 : min (r.toReal / 4) 1 ≤ r.toReal / 4 := min_le_left _ _
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hr.2.ne]
  linarith

theorem uniform_zero_value : uniform f realDist realDist U U = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra! h
  obtain ⟨r,hr,hrt⟩ := exists_between h
  obtain ⟨a,ha,ha1,har⟩ := small_positive ⟨hr,hrt.trans_le le_top⟩
  have hx : a ∈ S := Or.inr ⟨ha,ha1⟩
  have hrle : uniform f realDist realDist U U ≤ radius f realDist realDist U (some a) :=
    uniform_le_point ((mem_realSet _ _).mpr hx)
  rw [(pointwise hx).1, abs_of_pos ha] at hrle
  exact hrt.not_ge (hrle.trans ((ENNReal.ofReal_le_ofReal (by linarith : a ≤ 2*a)).trans har.le))

theorem cover_failure {r : ℝ≥0∞} (hr : FinitePositive r) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < r ∧
      let B : Set (Option ℝ) := {some (-a), some a}
      B ⊆ U ∧ covering_number realDist r B = 1 ∧
        covering_number realDist (ENNReal.ofReal (1/2)) (f.func '' B) = 2 := by
  obtain ⟨a,ha,ha1,har⟩ := small_positive hr
  have hp : a ∈ S := Or.inr ⟨ha,ha1⟩
  have hn : -a ∈ S := Or.inl ⟨by linarith,by linarith⟩
  have himg : f.func '' ({some (-a),some a} : Set (Option ℝ)) = {some 0,some 1} := by
    simp [Set.image_insert_eq, f, step, show -a < 0 by linarith, not_lt.mpr ha.le]
  refine ⟨a,ha,ha1,har,?_,?_,?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (mem_realSet _ _).mpr hn
    · exact (mem_realSet _ _).mpr hp
  · apply cover_single_center
    refine ⟨some a,by simp,?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rwa [real_some, show -a-a = -(2*a) by ring, abs_neg, abs_of_nonneg (by positivity)]
    · simpa using hr.1
  · rw [himg]
    apply le_antisymm
    · apply two_center_upper (some 0) (some 1) (by simp) (by simp)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · left; norm_num
      · right; norm_num
    · apply two_center_lower ⟨some 0,by simp⟩
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · exact ⟨some 1,by simp,by rw [real_some]; norm_num [ENNReal.ofReal_le_one]⟩
      · exact ⟨some 0,by simp,by rw [real_some]; norm_num [ENNReal.ofReal_le_one]⟩


theorem pointwise_cover_counterexample :
    (∀ y ∈ U, 0 < radius f realDist realDist U y) ∧
    ∀ r, FinitePositive r →
      ∃ B ⊆ U, covering_number realDist r B = 1 ∧
        covering_number realDist (ENNReal.ofReal (1/2)) (f.func '' B) = 2 := by
  constructor
  · rintro _ ⟨y,hy,rfl⟩
    exact (pointwise hy).2
  · intro r hr
    obtain ⟨a,_,_,_,hB,h1,h2⟩ := cover_failure hr
    exact ⟨{some (-a),some a},hB,h1,h2⟩

end Step
end Chapter
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
          "file": "Chapter/Components.lean",
          "name": "Chapter.Const"
        },
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.Ident"
        },
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.Active"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.component_membership"
        },
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.partition"
        }
      ],
      "representation": "Const 表示输出两两零距，Ident 先排除 Const 再要求每个输出与输入零距，Active 是前两类并集的补集。partition 证明覆盖与两两不交。用 U = dom f 即得全域分划。",
      "dependencies": []
    },
    {
      "id": "CH03-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.fiber_membership"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.fiber_missing"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.subfamily_zero"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.subfamily_max"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_singleton"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiberBlocks"
        }
      ],
      "representation": "输入在 U 内，目标 y 可以是任意点。有限非空 J 的复合距离取到最大，等于零当且仅当 J 中每分量均为零。fiberBlocks 用实际像集上的集合像去重，正距离目标对应空纤维；单分量和全域分别代入 {i} 与 dom f。",
      "dependencies": []
    },
    {
      "id": "CH03-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.pointPairs"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.zeroPairs"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.zeroPairs_fiber"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.imagePoint"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.imageSetoid"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.imageQuot"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.quotientPoint"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.FiberFiner"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.finer_iff_blocks"
        }
      ],
      "representation": "点对先限制在 U×U，随后比较点值或全分量零距。imageQuot 是实际像的子类型按受限族零距关系取 Quotient；quotientPoint 把同一个输入映至其输出的类。FiberFiner 的包含方向对应每个较细纤维包含于某个较粗纤维。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.FinitePositive"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.admissible"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.admissible_iff"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.radius_ball_formula"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_empty"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.radius_singleton"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_top"
        }
      ],
      "representation": "候选 r 是 ENNReal 中严格正且小于顶的参数，其开球与 U 的交包含于以 f(y) 为目标的纤维。radius 对这些候选取上确界；空集给零，全部有限球满足时可达顶。换入子族伪度量或单分量即相应简写。",
      "dependencies": [
        "CH03-D02",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.nullMatrix"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.uniform_ball_formula"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.nullMatrix_formula"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_eq_inf_separated"
        }
      ],
      "representation": "uniform 在基点子类型 A 上对评估域 U 的点态半径取下确界，与对 y∈A 取下确界相同。nullMatrix 固定 A=U，参数 j 为输出行、i 为输入列。代入 U=dom f 得全域矩阵。另证明同域统一半径等于正分离点对的输入距离下确界。",
      "dependencies": [
        "CH03-D04",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.ScaleFamily"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.diameter"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.le_diameter"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.diameterScale"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.thresholdType"
        }
      ],
      "representation": "尺度定义在非空集合的子类型并随包含单调；默认直径是域内所有点对距离的上确界。Bool 的 true、false 分别对应 1、0；两项依次判断尺度严格小于阈值与半径不小于阈值。",
      "dependencies": [
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-D07",
      "status": "complete",
      "declarations": [
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
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy_empty"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy_nonneg"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.log2_ereal"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.net_iff_ball_cover"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.finite_cover_minimum"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.finite_gap_conditions"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.subfamily_cover_singleton"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.TotallyBoundedAt"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.total_iff_nets"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.entropy_eq_coe"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.log2_mono"
        }
      ],
      "representation": "复用冻结的 Finset 内中心、覆盖数和以 2 为底的 EReal 熵。证明中心条件等价于开球并覆盖，有限覆盖取得最小基数，无有限内覆盖对应顶；空集的覆盖数与熵分别为零、底；全有界要求每个有限正精度存在有限内覆盖。单分量及子族沿用同一定义。",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.GapDefined"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.entropyGap"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.entropyGap_cases"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.entropyGap_sign"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.SubfamilyGapDefined"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.subfamilyGap"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.subfamily_gap_formula"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.gap_excludes_double_infinity"
        }
      ],
      "representation": "两端用非空子族、同一有限正精度，并以至少一个覆盖数有限作为熵差的调用前提。差取 EReal，两个单边无穷分支及双有限分支分别计算，双无穷时定义域为空；正、负、零对应原文两端熵的顺序。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P01-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.const_zero_row"
        }
      ],
      "representation": "固定属于常值类的输出分量 i，在 U 的所有点对上用 ENNReal 零系数求和给出零行上界。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.const_colip"
        }
      ],
      "representation": "对给定的合法受限 co-Lip 矩阵，任意源分量 j 有域内正距离见证时，输出常值分量 i 的对应条目 K j i 为零。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.ident_distance"
        }
      ],
      "representation": "未被常值优先排除的恒等分量，对 U 内任意两点，输出距离与输入距离相等。证明对两个端点分别使用伪度量的零距不变性。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P02-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.active_comp"
        }
      ],
      "representation": "复合用算子乘法表示，右侧先作用。复合在 U 定义蕴含第一步在 U 合法，第二步在第一步真实像集合法；复合有效分量包含于两步有效分量的并。",
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
          "file": "Chapter/Components.lean",
          "name": "Chapter.chain"
        },
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.stepActive"
        },
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.chain_representation"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.chain_domain_valid"
        },
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.chain_active"
        }
      ],
      "representation": "列表按作用顺序书写；反序后等于冻结的 OperatorChain。stepActive 每一步用前一步的实际像作为下一步输入域；归纳包含空列表恒等算子的空有效集。",
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
          "file": "Chapter/Components.lean",
          "name": "Chapter.ident_comp"
        }
      ],
      "representation": "每个共同恒等分量在实际像域逐点保持零距，且第二步沿该分量保留第一步的非零输出距离见证；因此复合也属于恒等类。",
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
          "file": "Chapter/Models.lean",
          "name": "Chapter.Swap.U"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Swap.d"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Swap.f"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Swap.gauge"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Swap.calculations"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Swap.reverse_failures"
        }
      ],
      "representation": "Option Bool 给出吸收元和两个有区别的点，指标是 Unit。换位保持 U 且两步都有效、都非恒等；复合恒等且无有效分量。用同一结构否定两条反向集合包含。",
      "dependencies": [
        "CH03-D01",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P04-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.outer_const"
        }
      ],
      "representation": "对于 U 内任意两点，将其第一步输出代入外侧算子在实际像集上的常值条件。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.Pt"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.d"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.f"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.g"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.U"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.gauge"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.Inner.counterexample"
        }
      ],
      "representation": "六个枚举的非吸收点加 none 构成七点空间。Bool 的 false 通道恰合并 p、q，true 通道离散。验证部分算子取值、复合定义域，以及内侧在前一通道零距而复合输出在该通道距离为 1。",
      "dependencies": [
        "CH03-D01",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P05-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Components.lean",
          "name": "Chapter.inner_const_of_row"
        }
      ],
      "representation": "给定下游在真实像域上的合法 Lip 矩阵及指定输出行除对角项均为零的条件，化简为对角系数乘零，允许系数为顶。",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P06-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_target"
        }
      ],
      "representation": "对任意两目标，零距离允许替换目标而不改变受限纤维；对子族由其复合伪度量实例化。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_cover"
        }
      ],
      "representation": "以实际像点为目标的每个块至少有一个原像；块并集是 U，包括 U 空时。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_eq_or_disjoint"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_partition"
        }
      ],
      "representation": "两个有共同原像的目标在所选距离下零距，从而块相等；Set 的块族自动去重并满足非空、覆盖及两两不交。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_inter"
        }
      ],
      "representation": "对非空 J，将复合零距展开为每个分量同时零距，证明与索引交集相等。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_antitone"
        }
      ],
      "representation": "子族 J 包含于 K 时，K 中全部零距条件蕴含 J 的条件，给出所需纤维包含。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-06",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_singleton"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_full"
        }
      ],
      "representation": "单点子族等于对应分量的纤维；全指标集用 Set.univ，实现到任一分量纤维的包含。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_ident"
        }
      ],
      "representation": "恒等分量上逐点使用距离对零距端点的不变性，对任意目标得到输入零距类。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_const"
        }
      ],
      "representation": "实际像中的目标得到整个 U；对与该目标严格正距的任意目标，用对称性和零距不变性证明其纤维为空。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.PointFactor"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.point_factor_necessary"
        }
      ],
      "representation": "T 的输入类型是第一算子的实际像，赋值对 U 子类型的每个输入成立；同一像点的相等经 T 传给第二算子。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.representative"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.representative_spec"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.point_factor_sufficient"
        }
      ],
      "representation": "对实际像的每个点从其成员证明取原像，关系包含保证赋值独立。U 空时像类型为空，定义仍成立。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.point_factor_both"
        }
      ],
      "representation": "用两个方向的存在性分别得到两个包含，反向由集合相等同时构造两映射。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.point_factor_lip"
        }
      ],
      "representation": "对 T 的任意两个实际像点取 U 中代表，先以有限正 K 消去同一输入距离，再合成有限 L 上界，得到系数 L/K。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P08-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.QuotFactor"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.quot_factor"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.finer_iff_quotient"
        }
      ],
      "representation": "在实际像子类型上用 Quotient.lift 构造映射；零距点对包含保证代表无关，证明对每个输入的规定公式。反向由商类相等反射为零距关系。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.quot_factor_both"
        }
      ],
      "representation": "双向商变换存在等价于两个零距点对集相等，两个方向均保持同一输入所生成的类。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.SeparatesImage"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.pairs_of_separated"
        },
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.factor_of_separated"
        }
      ],
      "representation": "仅要求分别在两个实际像集内零距蕴含点相等，由此分别证明两种点对集相等，得到单向和双向判据等价。",
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
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_preorder"
        }
      ],
      "representation": "固定共同评估域，纤维关系包含对固定算子自反，对三算子传递。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_finite_chain"
        }
      ],
      "representation": "有限链用自然数索引的前 m+1 层表示，逐步比较至 m；由自然数归纳得到任意 a≤b≤m 的关系，涵盖 a<b。",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Fibers.lean",
          "name": "Chapter.fiber_strict_chain"
        }
      ],
      "representation": "严格步索引是 r 到 r+1。抽出该步的差集点对，通过两边链的包含证明它也属于端点差集，故端点严格包含。",
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
          "file": "Chapter/Models.lean",
          "name": "Chapter.realDist"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.realSet"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.extendDistance"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.read_legal"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.liftRealMap"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.step"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.f"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.S"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.U"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.legal"
        }
      ],
      "representation": "实线取 Option ℝ，none 为吸收元；实数之间取差的绝对值，混合距离为顶。阶跃在负半轴取 0，其余实点取 1，保留吸收元；U 是指定两个半开区间的并并合法非空。",
      "dependencies": []
    },
    {
      "id": "CH03-P10-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.admissible_exact"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.pointwise"
        }
      ],
      "representation": "量化 U 内每个实数基点及所有候选；半径严格大于绝对值时构造异号点反证合法性，因此候选恰是 (0,|y|]，上确界取 |y| 且严格正。",
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
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.uniform_zero_value"
        }
      ],
      "representation": "固定同一个 U；用任意小的正实数构造基点，结合其点态半径等式推出统一下确界为零。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.const_subfamily_fiber"
        }
      ],
      "representation": "对非空输出子族的每个指标分别用常值条件；每个由 U 中基点产生的像目标，其 J 纤维为 U。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.const_subfamily_radii"
        }
      ],
      "representation": "对每一个输入 i，U 内每个基点的所有有限正半径合法，点态上确界和 U 上的统一下确界都为顶。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
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
          "file": "Chapter/Models.lean",
          "name": "Chapter.InfiniteGap.d"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.InfiniteGap.gauge"
        },
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.InfiniteGap.counterexample"
        }
      ],
      "representation": "Option Bool 上取恒等算子。输入通道不同点距离为顶，其余分量为 1。i=j 时输出不同点距离为顶，i≠j 时为 1；指定统一条目均为顶而输出分量非常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05",
        "CH03-P03-01",
        "CH03-P10-01",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P12-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.ident_fiber_self"
        }
      ],
      "representation": "恒等分量的保距等式用于 x、y 同属 U 且目标为 f(y)，得到以 y 为中心的输入零距类。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.ident_radius"
        }
      ],
      "representation": "给定有限正候选 r 和球交 U 的零距类包含，将其转成合法半径，以其见证上确界下界并保留严格正。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_subfamily"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.iInf_attains"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.radius_minimum"
        }
      ],
      "representation": "在同一基点和评估域，先证明点态子族值等于单分量值的下确界，再用有限非空性证明确实取到最小值。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_subfamily"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.uniform_minimum"
        }
      ],
      "representation": "基点下确界与输出索引下确界交换，并由非空有限索引取得某一矩阵行列条目的最小值。",
      "dependencies": [
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_subfamily_antitone"
        }
      ],
      "representation": "对非空 J⊆K，K 的下确界不大于 J 中任何一项，故统一半径关于输出子族反单调。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.fiber_step"
        }
      ],
      "representation": "源与目标基点在指定 U；纤维成员给出反向输出零距，由输出伪度量对称性得原方向。",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P14-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_witness"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_zero"
        },
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_step"
        }
      ],
      "representation": "输入距离严格小于上确界，提取一个更大的合法有限正半径；由输入对称性进入受限开球，再应用纤维分支。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.fiber_comp"
        }
      ],
      "representation": "把第一步的两个像点代入指定下游评估域的纤维成员判据。定理保留两输入的上游域条件和两像点的下游域条件。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_comp_zero"
        }
      ],
      "representation": "在第一步的真实像域逐点对保持指定零距的假设下，比较复合和第一步的统一条目。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P15-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_comp_lip"
        }
      ],
      "representation": "L 有限且正，由严格除法等价将输入距离小于下游条目除 L 转为下游距离小于条目，故得复合统一下界；ENNReal 等价允许条目为零或顶。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P16-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.threshold_four"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.threshold_exclusive"
        }
      ],
      "representation": "Bool×Bool 的四个值均列出与其阈值不等式的等价，并证明必落入其中且取值唯一，等号边界落在对应的非严格判断侧。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.threshold_scale_mono"
        }
      ],
      "representation": "固定第二阈值和其余数据，增大第一阈值后原先第一项 true 的通道仍为 true。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.threshold_null_antitone"
        }
      ],
      "representation": "固定第一阈值和其余数据，增大第二阈值后第二项 true 的通道集合缩小。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.scale_restrict"
        }
      ],
      "representation": "任意单调尺度族，对非空 B⊆A，由尺度的单调公理及传递性给出两条结论。",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.radius_restrict"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.threshold_domain_radius"
        }
      ],
      "representation": "固定 B 中基点，只把开球的评估域由 A 缩到 B，每个满足上界判据的半径仍满足。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_restrict"
        }
      ],
      "representation": "同时把评估域和基点集合缩到 B。以 A 的统一半径控制 B 中每个点态半径，再对 B 取下确界。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P17-02"
      ]
    },
    {
      "id": "CH03-P17-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.diameter_counterexample"
        }
      ],
      "representation": "带吸收元的实线上取恒等算子，非空 B={0}⊆A={0,1}，直径分别为 0 和 1，对阈值 1/2 否定反向判断。",
      "dependencies": [
        "CH03-D06",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P18-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_zero"
        }
      ],
      "representation": "统一半径不大于任一指定基点的半径，域内输入距离严格低于统一半径则输出零距。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_separation"
        }
      ],
      "representation": "取输出距离严格正的域内点对，由前一判据逆否得到输入距离不小于统一半径。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_failure"
        }
      ],
      "representation": "对满足统一半径<α<阈值的每个有限正 α，从不能全部零化推出点对见证，再在 0 与正输出距离之间选有限正 ε，输出为顶时也适用。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.threshold_fiber"
        }
      ],
      "representation": "每个中心在 A 内；半径为有限正阈值的开球与 A 相交后，所得点属于该中心输出的受限纤维。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04",
        "CH03-D05",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.cover_push"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.threshold_cover"
        }
      ],
      "representation": "从 B 的任意内覆盖把 Finset 中心映到 B 的实际像，基数不增；阈值使相应输出零距。对全部输入覆盖取下确界，包含空域及输入无有限覆盖。",
      "dependencies": [
        "CH03-D02",
        "CH03-D04",
        "CH03-D05",
        "CH03-D07",
        "CH03-P19-01"
      ]
    },
    {
      "id": "CH03-P19-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.threshold_entropy"
        }
      ],
      "representation": "B 非空时把已得覆盖数不等式应用到单调的扩展以 2 为底对数。",
      "dependencies": [
        "CH03-D04",
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
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.cover_failure"
        },
        {
          "file": "Chapter/Step.lean",
          "name": "Chapter.Step.pointwise_cover_counterexample"
        }
      ],
      "representation": "在同一个阶跃评估域，任意有限正半径 τ 选取 0<a≤1、2a<τ。二点集用单个内部中心覆盖；输出两点距离为 1，在精度 1/2 必须用两个内部中心。整个固定域的点态半径均正。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.small_iff"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.small_threshold_type"
        }
      ],
      "representation": "直径严格小于第一阈值，第一阈值不大于零化阈值。由统一阈值推出所有点对输出零距；反向全部有限球合法。也验证分类第一项及第二项的对应。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P14-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P21-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.cover_const_image"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.small_cover"
        }
      ],
      "representation": "对满足等价条件的非空域取任意像点为内中心，覆盖数至多为 1，非空性给出相反不等式。",
      "dependencies": [
        "CH03-D04",
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
          "file": "Chapter/Cover.lean",
          "name": "Chapter.cover_finite"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.finite_gap"
        }
      ],
      "representation": "有限非空 U 及其实际像用自身作有限中心。任意两端非空子族及有限正精度下两覆盖数均正有限，其熵各等于一个实数的嵌入，熵差可调用。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P23-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.const_gap"
        }
      ],
      "representation": "常值输出分量覆盖数为 1、熵为 0，熵差等于输入熵；以输出有限作为定义证据，输入可以为顶。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
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
          "file": "Chapter/Cover.lean",
          "name": "Chapter.cover_pull"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.ident_cover"
        }
      ],
      "representation": "恒等分量保距，前向映射中心，反向为每个输出中心选实际原像，两方向基数均不增，覆盖数和熵均相等。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
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
          "file": "Chapter/Cover.lean",
          "name": "Chapter.equal_cover_gap"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.ident_gap"
        }
      ],
      "representation": "仅在 GapDefined 成立时消去两个相同的熵。相同覆盖数和至少一端有限保证两端都有限。",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
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
          "file": "Chapter/Cover.lean",
          "name": "Chapter.lip_cover"
        }
      ],
      "representation": "有限正 L 将输入精度 ε/L 的任意内部中心有限集映成输出精度 ε 的内部中心有限集，使用 ENNReal 严格除法及像的基数上界。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P24-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.finitePositive_div"
        },
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.lip_gap"
        }
      ],
      "representation": "源集全有界给出两个输入精度的有限覆盖，再由输出覆盖上界得两端有限熵。应用扩展实数减法的单调性得到原文下界。",
      "dependencies": [
        "CH03-D04",
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
          "file": "Chapter/Cover.lean",
          "name": "Chapter.colip_cover"
        }
      ],
      "representation": "合法 co-Lip 矩阵的所选正有限条目乘输入距离不超过各项之和。按输出中心选原像拉回内部输入覆盖，并以 ε/K 作半径和基数上界。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-P23-02"
      ]
    },
    {
      "id": "CH03-P25-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Cover.lean",
          "name": "Chapter.colip_gap"
        }
      ],
      "representation": "源集全有界只用于两个输入精度，源端有限给出熵差定义证据。由覆盖下界和 EReal 减法单调性得到熵差上界，像熵可以为顶。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-D08",
        "CH03-P24-02",
        "CH03-P25-01"
      ]
    },
    {
      "id": "CH03-P26-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Models.lean",
          "name": "Chapter.absDist"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.d"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.f"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.U"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.gauge"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.values"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.first"
        }
      ],
      "representation": "实数读数 q(x)=|x| 诱导伪度量，并按吸收元规则延拓。仿射映射在 0、1 的输出为 −1、1，对目标 f(0) 的纤维为 U，唯一分量常值。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P26-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.values"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.second"
        }
      ],
      "representation": "自复合仍在 U={0,1} 上合法，输出为 −3、1。以复合在 0 的输出为目标的纤维是 {0}，唯一分量有效。",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P10-01",
        "CH03-P26-01"
      ]
    },
    {
      "id": "CH03-P26-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Affine.literal_constant"
        }
      ],
      "representation": "若 U 上的真实点值均为同一个实数，则再应用算子必取得同一点值。其非吸收时整个 U 是相应纤维；其为吸收元时 U 与自复合定义域无交。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.point_gap"
        }
      ],
      "representation": "任意正 K 条目，包括顶，反射输出零距。如果输入距离严格低于指定点态半径则归零，故不能同时严格正。",
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
          "file": "Chapter/Radius.lean",
          "name": "Chapter.uniform_gap"
        },
        {
          "file": "Chapter/Representations.lean",
          "name": "Chapter.uniform_gap_disjoint"
        }
      ],
      "representation": "统一半径严格正时，对域内各点对给出零距离或不小于统一半径的二择，并证明两个区间不交。",
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
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.f"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.U"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.V"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.gauge"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.domains"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.image"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.partitions"
        }
      ],
      "representation": "实数平移保持吸收元。恒等纤维是 {−3}、{−2,2}、{0}；平移纤维是 {−3}、{−2,0}、{2}。两侧按各自实际像目标取纤维并去重。",
      "dependencies": [
        "CH03-D02",
        "CH03-P10-01",
        "CH03-P26-01"
      ]
    },
    {
      "id": "CH03-P28-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.ε"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.cover_U"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.cover_V"
        },
        {
          "file": "Chapter/Readouts.lean",
          "name": "Chapter.Translation.covering_and_gap"
        }
      ],
      "representation": "精度为 3/2。源集用两个内部中心，并对任意单中心给出漏点；像集用一个内部中心。覆盖数为 2 与 1，映射熵差为 1。",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P26-01",
        "CH03-P28-01"
      ]
    },
    {
      "id": "CH03-P29-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.f"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.gauge"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.D1"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.first"
        }
      ],
      "representation": "吸收延拓的取整算子在 [0,1/2] 合法且为常值。直径 1/2，统一零化半径为顶，类为 (1,1)。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P10-01",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P29-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.D2"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.at_boundary_zero"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.second"
        }
      ],
      "representation": "在 [9/10,11/10]，直径为 1/5；以 1 与任意接近 1 的左侧点见证统一半径为零，类为 (1,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P10-01",
        "CH03-P18-01",
        "CH03-P29-01"
      ]
    },
    {
      "id": "CH03-P29-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.D3"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.third"
        }
      ],
      "representation": "在 {0,2}，直径恰为 2，唯一跨点对输入距离 2 且输出正距，故统一半径恰为 2，类为 (0,1)。",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P10-01",
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
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.D4"
        },
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.fourth"
        }
      ],
      "representation": "在 [0,2]，直径为 2；仍可在 1 左侧任意接近取整跳点，统一半径为零，类为 (0,0)。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P10-01",
        "CH03-P29-01",
        "CH03-P29-02"
      ]
    },
    {
      "id": "CH03-P29-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Floor.lean",
          "name": "Chapter.FloorExample.large_without_collapse"
        }
      ],
      "representation": "从 D3 取合法的两个点作为反例。最小跨点输入距离给出统一半径 2≥1，而取整输出仍为 0 与 2。",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P10-01",
        "CH03-P29-01",
        "CH03-P29-03"
      ]
    },
    {
      "id": "CH03-P30-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.U"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.gauge"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.cover_small"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.cover_middle"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.cover_large"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.cover_all"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.excluded_center"
        }
      ],
      "representation": "任意有限正半径下，区间 (0,1]、(1,2]、(2,+∞) 的覆盖数分别为 4、2、1，严格开球给出端点。3/2 不属于 U，单中心集不满足内部中心条件。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-P10-01"
      ]
    },
    {
      "id": "CH03-P30-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.f"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.g"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.f_value"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.g_values"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.outside"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.domains"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.images"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.image_statistics"
        }
      ],
      "representation": "两个部分算子均只在 U 有定义，并分别按表取值；实际像集均恰为 U，所以所有指定精度下覆盖数相等，两熵差均良定且为零。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-D08",
        "CH03-P10-01",
        "CH03-P22-01",
        "CH03-P23-03",
        "CH03-P30-01"
      ]
    },
    {
      "id": "CH03-P30-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.f_optimal"
        },
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.g_optimal"
        }
      ],
      "representation": "用冻结的标量 Lip 谓词，证明合法常数分别是所有 L≥1 和 L≥3。下界均由 0 与 1 的输入点对见证，并验证这些常数确实有效。",
      "dependencies": [
        "CH03-P10-01",
        "CH03-P30-01",
        "CH03-P30-02"
      ]
    },
    {
      "id": "CH03-P30-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Chapter/Rearrange.lean",
          "name": "Chapter.Rearrange.bounds_at_seven_fourths"
        }
      ],
      "representation": "在 ε=7/4 代入两个最小合法常数，使用一般的内部覆盖推送界。真实覆盖数均为 2，f 的界为 2，g 的界为 4。",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-P10-01",
        "CH03-P24-01",
        "CH03-P30-01",
        "CH03-P30-02",
        "CH03-P30-03"
      ]
    }
  ]
}
```

