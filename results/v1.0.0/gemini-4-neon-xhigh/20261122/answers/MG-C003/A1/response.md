已完成 **MG-C003 v0.1.1**（《The Operator Evolution Theory, Volume I》第 3 章，原作者 Zhe Li / Glen Li / glenzli，ORCID `https://orcid.org/0009-0006-6536-3453`，`https://glenzli.com/books/oet/`，CC BY 4.0）全部 **92** 项义务的 Lean 4.29.1 形式化与编译验证：

- **模块与入口**：[Ch03/ComponentPartition.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/ComponentPartition.lean)、[Ch03/FiberFactorization.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/FiberFactorization.lean)、[Ch03/NullificationRadius.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/NullificationRadius.lean)、[Ch03/ScaleAndCovering.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/ScaleAndCovering.lean)、[Ch03/MappingEntropyDiff.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/MappingEntropyDiff.lean)、[Ch03/Exercises1to3.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/Exercises1to3.lean)、[Ch03/Exercises4to5.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Ch03/Exercises4to5.lean)、[Main.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/Main.lean) 及 [alignment.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-C003/physical-3/session/work/alignment.json)。
- **编译与公理审计**：全部模块在冻结环境（Lean 4.29.1 + 固定 mathlib + 冻结 `formal_oet/`）下零错误、零警告编译通过；`alignment.json` 完整覆盖 92/92 项义务（207 条声明均在对应编译模块中核实存在），所有 573 个自建常量的传递公理并集仅为 `{propext, Quot.sound, Classical.choice}`，无 `sorry`/`admit`/新增公理。

以下为全部源代码文件与 `alignment.json` 全文：

```lean filename=Ch03/ComponentPartition.lean
/-
Formalization of Chapter 3 (Section 3.1: Component Partition and Composition Properties)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.1: Component Partition (CH03-D01) -/

/-- Constant components of `ϕ` on restricted domain `U ⊆ dom ϕ`. -/
def I_const {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0 }

/-- Identity components of `ϕ` on `U` (constant-priority: excludes `I_const`). -/
def I_id {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | i ∉ I_const d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0 }

/-- Active (effective) components of `ϕ` on `U`. -/
def I_act {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set I :=
  (I_const d ϕ U ∪ I_id d ϕ U)ᶜ

/-- Global constant components (`U = dom ϕ`). -/
def I_const_global {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : Set I :=
  I_const d ϕ (dom ϕ)

/-- Global identity components (`U = dom ϕ`). -/
def I_id_global {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : Set I :=
  I_id d ϕ (dom ϕ)

/-- Global active components (`U = dom ϕ`). -/
def I_act_global {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : Set I :=
  I_act d ϕ (dom ϕ)

theorem disjoint_I_const_I_id {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) :
    Disjoint (I_const d ϕ U) (I_id d ϕ U) := by
  rw [Set.disjoint_left]
  intro i hi_const hi_id
  exact hi_id.1 hi_const

theorem disjoint_I_const_I_act {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) :
    Disjoint (I_const d ϕ U) (I_act d ϕ U) := by
  rw [Set.disjoint_left]
  intro i hi_const hi_act
  exact hi_act (Or.inl hi_const)

theorem disjoint_I_id_I_act {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) :
    Disjoint (I_id d ϕ U) (I_act d ϕ U) := by
  rw [Set.disjoint_left]
  intro i hi_id hi_act
  exact hi_act (Or.inr hi_id)

theorem I_const_union_I_id_union_I_act {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) :
    I_const d ϕ U ∪ I_id d ϕ U ∪ I_act d ϕ U = Set.univ := by
  ext i
  simp only [Set.mem_union, Set.mem_univ, iff_true, I_act, Set.mem_compl_iff]
  tauto

theorem mem_I_const_of_both_const_and_id {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) {i : I}
    (hconst : ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0)
    (_hid : ∀ x ∈ U, d i (ϕ.func x) x = 0) :
    i ∈ I_const d ϕ U ∧ i ∉ I_id d ϕ U := by
  exact ⟨hconst, fun h => h.1 hconst⟩

/-! ### Proposition 3.1: Matrix Constraints of Component Types (CH03-P01-01..03) -/

/-- Proposition 3.1(i): Constant component admits the zero row as its Lip upper bound. -/
theorem prop_3_1_i {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_const d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ (∑ k : I, (0 : ENNReal) * d k x y) ∧
      (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by
  intro x hx y hy
  have hsum : (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by simp
  refine ⟨?_, hsum⟩
  rw [hi x hx y hy, hsum]

/-- Proposition 3.1(i) matrix form: zeroing output row `i` of a Lip matrix preserves validity. -/
theorem prop_3_1_i_lip_zero_row {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (L : I → I → ENNReal) (hL : IsLipMatrix d ϕ U L) (hi : i ∈ I_const d ϕ U) :
    IsLipMatrix d ϕ U (fun k j => if j = i then 0 else L k j) := by
  refine ⟨hL.1, ?_⟩
  intro x hx y hy j
  by_cases hj : j = i
  · subst hj
    simp [hi x hx y hy]
  · simp [hj, hL.2 x hx y hy j]

/-- Proposition 3.1(ii): If `i ∈ I_const(ϕ | U)` and `K` is a co-Lip matrix on `U`,
any source channel `k` having a positively separated pair in `U` satisfies `K_{k → i} = 0`. -/
theorem prop_3_1_ii {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i k : I)
    (K : I → I → ENNReal)
    (hi : i ∈ I_const d ϕ U) (hK : IsCoLipMatrix d ϕ U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hxy⟩
  exact colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K k i x y hK hx hy
    (hi x hx y hy) hxy

/-- Proposition 3.1(iii): Identity component preserves pairwise distances on `U`. -/
theorem prop_3_1_iii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_id d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y := by
  intro x hx y hy
  have hfx : d i (ϕ.func x) x = 0 := hi.2 x hx
  have hfy : d i (ϕ.func y) y = 0 := hi.2 y hy
  apply le_antisymm
  · calc
      d i (ϕ.func x) (ϕ.func y)
          ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := hd.triangle _ _ _
      _ ≤ d i (ϕ.func x) x + (d i x y + d i y (ϕ.func y)) :=
          add_le_add le_rfl (hd.triangle _ _ _)
      _ = d i x y := by rw [hfx, hd.symm y (ϕ.func y), hfy, zero_add, add_zero]
  · calc
      d i x y
          ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := hd.triangle _ _ _
      _ ≤ d i x (ϕ.func x) + (d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y) :=
          add_le_add le_rfl (hd.triangle _ _ _)
      _ = d i (ϕ.func x) (ϕ.func y) := by rw [hd.symm x (ϕ.func x), hfx, hfy, zero_add, add_zero]

/-! ### Proposition 3.2: Active Component Inclusion and Identity Preservation (CH03-P02-01..03) -/

/-- Helper: domain of `ϕ₂ ∘ ϕ₁` is contained in domain of `ϕ₁`. -/
theorem dom_operator_compose_subset_left {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) :
    dom (operator_compose ϕ₂ ϕ₁) ⊆ dom ϕ₁ := by
  intro x hx hbot
  apply hx
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [hbot, ϕ₂.preserves_bot]

/-- Helper: image of `U ⊆ dom (ϕ₂ ∘ ϕ₁)` under `ϕ₁` is contained in `dom ϕ₂`. -/
theorem image_subset_dom_of_compose {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) {U : Set X} (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    operator_image ϕ₁ U ⊆ dom ϕ₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact hU hx

/-- Proposition 3.2(iii): Identity components are preserved under composition
(including excluding the constant-priority branch). -/
theorem prop_3_2_iii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    I_id d ϕ₁ U ∩ I_id d ϕ₂ (operator_image ϕ₁ U) ⊆
      I_id d (operator_compose ϕ₂ ϕ₁) U := by
  intro i ⟨hi1, hi2⟩
  have hU2 : operator_image ϕ₁ U ⊆ dom ϕ₂ := image_subset_dom_of_compose ϕ₂ ϕ₁ hU
  refine ⟨?_, ?_⟩
  · intro hconst
    apply hi1.1
    intro x hx y hy
    have hpreserve := prop_3_1_iii d ϕ₂ (operator_image ϕ₁ U) i (hd i) hU2 hi2
      (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    rw [← hpreserve]
    exact hconst x hx y hy
  · intro x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i ((operator_compose ϕ₂ ϕ₁).func x) x
          ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) x := (hd i).triangle _ _ _
      _ = 0 := by
          rw [hi2.2 (ϕ₁.func x) ⟨x, hx, rfl⟩, hi1.2 x hx, zero_add]

/-- Proposition 3.2(i): Two-step active component inclusion on the actual intermediate image. -/
theorem prop_3_2_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    I_act d (operator_compose ϕ₂ ϕ₁) U ⊆
      I_act d ϕ₁ U ∪ I_act d ϕ₂ (operator_image ϕ₁ U) := by
  intro i hi_act
  by_contra hnot
  have h1 : i ∈ I_const d ϕ₁ U ∪ I_id d ϕ₁ U := by
    by_contra h
    exact hnot (Or.inl h)
  have h2 : i ∈ I_const d ϕ₂ (operator_image ϕ₁ U) ∪ I_id d ϕ₂ (operator_image ϕ₁ U) := by
    by_contra h
    exact hnot (Or.inr h)
  rcases h1 with h1c | h1i <;> rcases h2 with h2c | h2i
  · -- (d) both const
    apply hi_act
    left
    intro x hx y hy
    exact h2c (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
  · -- (c) ϕ₁ const, ϕ₂ id
    apply hi_act
    left
    intro x hx y hy
    apply le_antisymm _ (zero_le _)
    calc
      d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y))
          ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) (ϕ₂.func (ϕ₁.func y)) :=
            (hd i).triangle _ _ _
      _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) +
            (d i (ϕ₁.func x) (ϕ₁.func y) + d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y))) :=
            add_le_add le_rfl ((hd i).triangle _ _ _)
      _ = 0 := by
            rw [h2i.2 (ϕ₁.func x) ⟨x, hx, rfl⟩, h1c x hx y hy,
                (hd i).symm (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y)),
                h2i.2 (ϕ₁.func y) ⟨y, hy, rfl⟩]
            simp
  · -- (b) ϕ₁ id, ϕ₂ const
    apply hi_act
    left
    intro x hx y hy
    exact h2c (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
  · -- (a) both id
    apply hi_act
    right
    exact prop_3_2_iii d hd ϕ₁ ϕ₂ U hU ⟨h1i, h2i⟩

/-- Recursive `n`-step operator composition `c_n = ϕ_{n-1} ∘ ⋯ ∘ ϕ_0`, with `c_0 = id`. -/
def chainOp {X : Type} {bot : X} (ϕ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => operator_identity
  | n + 1 => operator_compose (ϕ n) (chainOp ϕ n)

/-- Recursive actual intermediate image domains `U_{m+1} = ϕ_m(U_m)` starting from `U_0 = U₁`. -/
def chainDomain {X : Type} {bot : X} (ϕ : ℕ → Operator X bot) (U₁ : Set X) : ℕ → Set X
  | 0 => U₁
  | m + 1 => operator_image (ϕ m) (chainDomain ϕ U₁ m)

theorem chainDomain_eq_image_chainOp {X : Type} {bot : X}
    (ϕ : ℕ → Operator X bot) (U₁ : Set X) (n : ℕ) :
    chainDomain ϕ U₁ n = operator_image (chainOp ϕ n) U₁ := by
  induction n with
  | zero =>
      ext x
      simp [chainDomain, chainOp, operator_image, operator_identity]
  | succ n ih =>
      rw [chainDomain, ih]
      ext z
      simp [chainOp, operator_image, operator_compose]

/-- The identity operator has no active components on any subset `U`. -/
theorem I_act_identity_eq_empty {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (U : Set X) :
    I_act d (@operator_identity X bot) U = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hi_act
  by_cases hc : i ∈ I_const d (@operator_identity X bot) U
  · exact hi_act (Or.inl hc)
  · apply hi_act
    right
    refine ⟨hc, ?_⟩
    intro x _
    exact (hd i).dist_self x

/-- Proposition 3.2(ii): Finite composition of arbitrary length `n` (including `n = 0`). -/
theorem prop_3_2_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : ℕ → Operator X bot) (U₁ : Set X) :
    ∀ n : ℕ, U₁ ⊆ dom (chainOp ϕ n) →
      I_act d (chainOp ϕ n) U₁ ⊆ ⋃ m : Fin n, I_act d (ϕ m.1) (chainDomain ϕ U₁ m.1) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [chainOp, I_act_identity_eq_empty d hd U₁]
      exact Set.empty_subset _
  | succ n ih =>
      intro hU
      have hU_prev : U₁ ⊆ dom (chainOp ϕ n) :=
        hU.trans (dom_operator_compose_subset_left (ϕ n) (chainOp ϕ n))
      have hstep := prop_3_2_i d hd (chainOp ϕ n) (ϕ n) U₁ hU
      rw [← chainDomain_eq_image_chainOp ϕ U₁ n] at hstep
      intro i hi
      rcases hstep hi with hi_prev | hi_last
      · have hmem := ih hU_prev hi_prev
        rcases Set.mem_iUnion.mp hmem with ⟨m, hm⟩
        exact Set.mem_iUnion.mpr ⟨m.castSucc, hm⟩
      · exact Set.mem_iUnion.mpr ⟨Fin.last n, hi_last⟩

/-- Fin-indexed corollary of Proposition 3.2(ii) for a finite tuple `Fin n → Operator X bot`. -/
def chainOpFin {X : Type} {bot : X} {n : ℕ} (ϕ : Fin n → Operator X bot) : Operator X bot :=
  chainOp (fun k => if h : k < n then ϕ ⟨k, h⟩ else operator_identity) n

def chainDomainFin {X : Type} {bot : X} {n : ℕ} (ϕ : Fin n → Operator X bot) (U₁ : Set X)
    (m : Fin n) : Set X :=
  chainDomain (fun k => if h : k < n then ϕ ⟨k, h⟩ else operator_identity) U₁ m.1

theorem prop_3_2_ii_fin {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    {n : ℕ} (ϕ : Fin n → Operator X bot) (U₁ : Set X)
    (hU : U₁ ⊆ dom (chainOpFin ϕ)) :
    I_act d (chainOpFin ϕ) U₁ ⊆ ⋃ m : Fin n, I_act d (ϕ m) (chainDomainFin ϕ U₁ m) := by
  let extϕ : ℕ → Operator X bot := fun k => if h : k < n then ϕ ⟨k, h⟩ else operator_identity
  have hsub := prop_3_2_ii d hd extϕ U₁ n hU
  intro i hi
  rcases Set.mem_iUnion.mp (hsub hi) with ⟨m, hm⟩
  refine Set.mem_iUnion.mpr ⟨m, ?_⟩
  simpa [extϕ, m.2, chainDomainFin] using hm

/-! ### Remark after Proposition 3.2: Counterexample to Both Converses (CH03-P03-01) -/

/-- Three-point space `{⊥, a, b}` for the two-point swap counterexample. -/
inductive SwapSpace : Type
  | bot
  | a
  | b
  deriving DecidableEq

/-- Single-component discrete extended metric on `SwapSpace`. -/
def swapDist : Unit → SwapSpace → SwapSpace → ENNReal
  | _, .bot, .bot => 0
  | _, .bot, .a => ⊤
  | _, .bot, .b => ⊤
  | _, .a, .bot => ⊤
  | _, .b, .bot => ⊤
  | _, .a, .a => 0
  | _, .b, .b => 0
  | _, .a, .b => 1
  | _, .b, .a => 1

theorem swapDist_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric SwapSpace .bot (swapDist u) := by
  intro u
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by intro x; cases x <;> rfl
      symm := by intro x y; cases x <;> cases y <;> rfl
      triangle := by
        intro x y z
        cases x <;> cases y <;> cases z <;> simp [swapDist]
      isolate_bot := by
        intro x hx
        cases x
        · exact (hx rfl).elim
        · rfl
        · rfl }

/-- Two-point transposition operator swapping `a ↔ b` and fixing `bot`. -/
def swapOp : Operator SwapSpace .bot where
  func
    | .bot => .bot
    | .a => .b
    | .b => .a
  preserves_bot := rfl

def swapU : Set SwapSpace := {.a, .b}

theorem swapU_subset_dom_compose :
    swapU ⊆ dom (operator_compose swapOp swapOp) := by
  intro x hx
  rcases hx with rfl | rfl <;> simp [dom, operator_compose, swapOp]

theorem swapOp_image_swapU :
    operator_image swapOp swapU = swapU := by
  ext x
  simp only [operator_image, swapU, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩ <;> simp [swapOp]
  · rintro (rfl | rfl)
    · exact ⟨.b, Or.inr rfl, rfl⟩
    · exact ⟨.a, Or.inl rfl, rfl⟩

theorem swapOp_I_act : I_act swapDist swapOp swapU = Set.univ := by
  ext u
  cases u
  simp only [Set.mem_univ, iff_true, I_act, Set.mem_compl_iff, Set.mem_union, not_or]
  constructor
  · intro hc
    have h := hc .a (Or.inl rfl) .b (Or.inr rfl)
    simp [swapOp, swapDist] at h
  · intro hid
    have h := hid.2 .a (Or.inl rfl)
    simp [swapOp, swapDist] at h

theorem swapOp_I_id : I_id swapDist swapOp swapU = ∅ := by
  ext u
  cases u
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hid
  have h := hid.2 .a (Or.inl rfl)
  simp [swapOp, swapDist] at h

theorem swapOp_comp_I_id :
    I_id swapDist (operator_compose swapOp swapOp) swapU = Set.univ := by
  ext u
  cases u
  simp only [Set.mem_univ, iff_true]
  refine ⟨?_, ?_⟩
  · intro hc
    have h := hc .a (Or.inl rfl) .b (Or.inr rfl)
    simp [operator_compose, swapOp, swapDist] at h
  · intro x hx
    rcases hx with rfl | rfl <;> simp [operator_compose, swapOp, swapDist]

theorem swapOp_comp_I_act :
    I_act swapDist (operator_compose swapOp swapOp) swapU = ∅ := by
  ext u
  cases u
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hact
  have hid : () ∈ I_id swapDist (operator_compose swapOp swapOp) swapU := by
    rw [swapOp_comp_I_id]; trivial
  exact hact (Or.inr hid)

/-- Remark after Prop 3.2: Both reverse inclusions of Prop 3.2(i) and 3.2(iii) fail
simultaneously on the two-point swap counterexample. -/
theorem remark_prop_3_2_converse_fails :
    (∀ u : Unit, ExtendedPseudoMetric SwapSpace .bot (swapDist u)) ∧
    swapU ⊆ dom (operator_compose swapOp swapOp) ∧
    I_act swapDist swapOp swapU = Set.univ ∧
    I_act swapDist swapOp (operator_image swapOp swapU) = Set.univ ∧
    I_id swapDist swapOp swapU = ∅ ∧
    I_id swapDist swapOp (operator_image swapOp swapU) = ∅ ∧
    I_id swapDist (operator_compose swapOp swapOp) swapU = Set.univ ∧
    I_act swapDist (operator_compose swapOp swapOp) swapU = ∅ ∧
    ¬ (I_act swapDist swapOp swapU ∪ I_act swapDist swapOp (operator_image swapOp swapU) ⊆
        I_act swapDist (operator_compose swapOp swapOp) swapU) ∧
    ¬ (I_id swapDist (operator_compose swapOp swapOp) swapU ⊆
        I_id swapDist swapOp swapU ∩ I_id swapDist swapOp (operator_image swapOp swapU)) := by
  refine ⟨swapDist_extendedPseudoMetric, swapU_subset_dom_compose,
    swapOp_I_act, by rw [swapOp_image_swapU, swapOp_I_act],
    swapOp_I_id, by rw [swapOp_image_swapU, swapOp_I_id],
    swapOp_comp_I_id, swapOp_comp_I_act, ?_, ?_⟩
  · intro hsub
    have hmem : () ∈ I_act swapDist (operator_compose swapOp swapOp) swapU :=
      hsub (Or.inl (by rw [swapOp_I_act]; trivial))
    rw [swapOp_comp_I_act] at hmem
    exact hmem
  · intro hsub
    have hmem : () ∈ I_id swapDist swapOp swapU ∩
        I_id swapDist swapOp (operator_image swapOp swapU) :=
      hsub (by rw [swapOp_comp_I_id]; trivial)
    rw [swapOp_I_id] at hmem
    exact hmem.1

/-! ### Proposition 3.3: One-Sided Preservation and Non-Closure of Constant Components (CH03-P04-01..02) -/

/-- Proposition 3.3(i): Outer constant component on `ϕ(U)` implies composite constant component on `U`. -/
theorem prop_3_3_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom (operator_compose ψ ϕ))
    (hψ : i ∈ I_const d ψ (operator_image ϕ U)) :
    i ∈ I_const d (operator_compose ψ ϕ) U := by
  intro x hx y hy
  exact hψ (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩

/-- Seven-point space `{⊥, a, b, p, q, r, s}` for Proposition 3.3(ii). -/
inductive SevenSpace : Type
  | bot | a | b | p | q | r | s
  deriving DecidableEq

/-- Two-component index set `{i, m}` for Proposition 3.3(ii). -/
inductive TwoIdx : Type
  | i | m
  deriving DecidableEq

instance : Fintype TwoIdx where
  elems := {.i, .m}
  complete := by intro x; cases x <;> simp

/-- Quotient projection identifying `p` and `q` (for component `i`). -/
def sevenQuot : SevenSpace → SevenSpace
  | .q => .p
  | x => x

/-- Two-component pseudometric family on `SevenSpace`:
`d_i` collapses `{p, q}` into one zero-distance class and assigns distance `1` between distinct non-`bot` classes;
`d_m` is the discrete metric on non-`bot` points. -/
def sevenDist : TwoIdx → SevenSpace → SevenSpace → ENNReal
  | .i, x, y =>
      if x = .bot ∧ y = .bot then 0
      else if x = .bot ∨ y = .bot then ⊤
      else if sevenQuot x = sevenQuot y then 0
      else 1
  | .m, x, y =>
      if x = .bot ∧ y = .bot then 0
      else if x = .bot ∨ y = .bot then ⊤
      else if x = y then 0
      else 1

theorem sevenDist_extendedPseudoMetric :
    ∀ k : TwoIdx, ExtendedPseudoMetric SevenSpace .bot (sevenDist k) := by
  intro k
  cases k
  · refine
      { nonabsorbing := ⟨.a, by decide⟩
        dist_self := by
          intro x; by_cases hx : x = .bot <;> simp [sevenDist, hx]
        symm := by
          intro x y
          by_cases hx : x = .bot <;> by_cases hy : y = .bot
          · simp [sevenDist, hx, hy]
          · simp [sevenDist, hx, hy]
          · simp [sevenDist, hx, hy]
          · simp only [sevenDist, hx, hy, and_self, or_self, ↓reduceIte]
            by_cases hq : sevenQuot x = sevenQuot y
            · simp [hq]
            · have hq' : sevenQuot y ≠ sevenQuot x := fun h => hq h.symm
              simp [hq, hq']
        triangle := by
          intro x y z
          by_cases hx : x = .bot <;> by_cases hy : y = .bot <;> by_cases hz : z = .bot
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp only [sevenDist, hx, hy, hz, and_self, or_self, ↓reduceIte]
            by_cases hxz : sevenQuot x = sevenQuot z
            · simp [hxz]
            · by_cases hxy : sevenQuot x = sevenQuot y
              · have hyz : sevenQuot y ≠ sevenQuot z := by rwa [← hxy]
                simp [hxy, hyz]
              · simp [hxz, hxy]
        isolate_bot := by
          intro x hx; simp [sevenDist, hx] }
  · refine
      { nonabsorbing := ⟨.a, by decide⟩
        dist_self := by
          intro x; by_cases hx : x = .bot <;> simp [sevenDist, hx]
        symm := by
          intro x y
          by_cases hx : x = .bot <;> by_cases hy : y = .bot
          · simp [sevenDist, hx, hy]
          · simp [sevenDist, hx, hy]
          · simp [sevenDist, hx, hy]
          · simp only [sevenDist, hx, hy, and_self, or_self, ↓reduceIte]
            by_cases hxy : x = y
            · simp [hxy]
            · have hyx : y ≠ x := fun h => hxy h.symm
              simp [hxy, hyx]
        triangle := by
          intro x y z
          by_cases hx : x = .bot <;> by_cases hy : y = .bot <;> by_cases hz : z = .bot
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp [sevenDist, hx, hy, hz]
          · simp only [sevenDist, hx, hy, hz, and_self, or_self, ↓reduceIte]
            by_cases hxz : x = z
            · simp [hxz]
            · by_cases hxy : x = y
              · have hyz : y ≠ z := by rwa [← hxy]
                simp [hxy, hyz]
              · simp [hxz, hxy]
        isolate_bot := by
          intro x hx; simp [sevenDist, hx] }

def sevenPhi : Operator SevenSpace .bot where
  func
    | .a => .p
    | .b => .q
    | _ => .bot
  preserves_bot := rfl

def sevenPsi : Operator SevenSpace .bot where
  func
    | .p => .r
    | .q => .s
    | _ => .bot
  preserves_bot := rfl

def sevenU : Set SevenSpace := {.a, .b}

/-- Proposition 3.3(ii): Seven-point, two-component counterexample showing inner constant
component need not remain constant after composition. -/
theorem prop_3_3_ii_counterexample :
    (∀ k : TwoIdx, ExtendedPseudoMetric SevenSpace .bot (sevenDist k)) ∧
    sevenU ⊆ dom (operator_compose sevenPsi sevenPhi) ∧
    TwoIdx.i ∈ I_const sevenDist sevenPhi sevenU ∧
    TwoIdx.i ∉ I_const sevenDist (operator_compose sevenPsi sevenPhi) sevenU ∧
    sevenDist .m .p .q = 1 ∧
    sevenDist .i .r .s = 1 := by
  refine ⟨sevenDist_extendedPseudoMetric, ?_, ?_, ?_, by simp [sevenDist], by simp [sevenDist, sevenQuot]⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, operator_compose, sevenPhi, sevenPsi]
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [sevenPhi, sevenDist, sevenQuot]
  · intro hconst
    have h := hconst .a (Or.inl rfl) .b (Or.inr rfl)
    simp [operator_compose, sevenPhi, sevenPsi, sevenDist, sevenQuot] at h

/-! ### Corollary 3.4: Preservation of Constant Component via Single-Channel Lip Row (CH03-P05-01) -/

/-- Corollary 3.4: If `j ∈ I_const(ϕ | U)` and `ψ` admits a Lip matrix `L` on `ϕ(U)` whose
output row `j` vanishes off the diagonal (`L_{k → j} = 0` for `k ≠ j`), then
`j ∈ I_const(ψ ∘ ϕ | U)`. Note `L j j` may be `⊤` since `⊤ * 0 = 0` in `ENNReal`. -/
theorem cor_3_4 {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) (j : I)
    (L : I → I → ENNReal)
    (_hU : U ⊆ dom (operator_compose ψ ϕ))
    (hϕ : j ∈ I_const d ϕ U)
    (hL : IsLipMatrix d ψ (operator_image ϕ U) L)
    (hrow : ∀ k : I, k ≠ j → L k j = 0) :
    j ∈ I_const d (operator_compose ψ ϕ) U := by
  intro x hx y hy
  have hbound := lip_bound_of_single_input_row d ψ (operator_image ϕ U) L j j hL hrow
    (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩
  have hzero : d j (ϕ.func x) (ϕ.func y) = 0 := hϕ x hx y hy
  rw [hzero, mul_zero] at hbound
  exact le_antisymm hbound (zero_le _)

end Ch03
```

```lean filename=Ch03/FiberFactorization.lean
/-
Formalization of Chapter 3 (Section 3.2: Computational Fibers and Image Factorization)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.ComponentPartition
import formal_oet.vol_01.ch_01_foundations.metric_entropy

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.2: Computational Fibers (CH03-D02) -/

/-- Computational fiber of target `y` under `ϕ` on restricted domain `U` with respect to
subfamily pseudometric `d_J`. -/
def compFiber {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) (y : X) : Set X :=
  { x ∈ U | subfamily_pseudometric d J (ϕ.func x) y = 0 }

/-- Single-component computational fiber `Fib_{ϕ, j}(y | U)`. -/
def compFiberSingle {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (U : Set X) (y : X) : Set X :=
  { x ∈ U | d j (ϕ.func x) y = 0 }

/-- Global computational fiber `Fib_{ϕ, J}(y) = Fib_{ϕ, J}(y | dom ϕ)`. -/
def compFiberGlobal {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (y : X) : Set X :=
  compFiber d ϕ J (dom ϕ) y

/-- Deduplicated family of computational fibers over image targets `y ∈ ϕ(U)`. -/
def compFiberFamily {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) : Set (Set X) :=
  (fun y => compFiber d ϕ J U y) '' (operator_image ϕ U)

theorem compFiber_singleton_eq_single {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (U : Set X) (y : X) :
    compFiber d ϕ ({j} : Set I) U y = compFiberSingle d ϕ j U y := by
  ext x
  simp [compFiber, compFiberSingle, subfamily_pseudometric_singleton]

/-- Subfamily pseudometric vanishes iff every component in the subfamily vanishes. -/
theorem subfamily_pseudometric_eq_zero_iff {X I : Type} (d : I → X → X → ENNReal)
    (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    have hle : d j x y ≤ subfamily_pseudometric d J x y :=
      le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩
    rw [h] at hle
    exact le_antisymm hle (zero_le _)
  · intro h
    apply le_antisymm _ (zero_le _)
    dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    rw [h j.1 j.2]

/-! ### Point-Equality Relation, Zero-Distance Relation, Image Quotient, Fiber Preorder (CH03-D03) -/

/-- Point-equality pair relation `R_=(ϕ | U)`. -/
def pointEqRel {X : Type} {bot : X} (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2 }

/-- Full-gauge zero-distance pair relation `R_~(ϕ | U)`. -/
def zeroDistRel {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2) }

/-- Correspondence between `R_~(ϕ | U)` and full-family computational fibers `Fib_{ϕ, I}(ϕ(x) | U)`. -/
theorem mem_zeroDistRel_iff_mem_compFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ zeroDistRel d ϕ U ↔ y ∈ compFiber d ϕ Set.univ U (ϕ.func x) := by
  simp only [zeroDistRel, compFiber, Set.mem_setOf_eq, GaugeZeroRelated,
    subfamily_pseudometric_eq_zero_iff, Set.mem_univ, forall_true_left, hx, hy, true_and]
  constructor
  · intro h i
    rw [(hd i).symm]
    exact h i
  · intro h i
    rw [(hd i).symm]
    exact h i

/-- Setoid induced by the gauge zero-distance relation `~_G` restricted to `ϕ(U)`. -/
def imageZeroSetoid {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Setoid { z : X // z ∈ operator_image ϕ U } where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have heq := gauge_zero_related_equivalence d
      (fun i x => (hd i).dist_self x)
      (fun i x y => (hd i).symm x y)
      (fun i x y z => (hd i).triangle x y z)
    exact ⟨fun a => heq.refl a.1, fun h => heq.symm h, fun h1 h2 => heq.trans h1 h2⟩

/-- Image quotient `ϕ(U) / ~_G`. -/
def ImageQuot {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Type :=
  Quotient (imageZeroSetoid d hd ϕ U)

/-- Canonical class `[ϕ(x)] ∈ ϕ(U) / ~_G` for `x ∈ U`. -/
def imageQuotMk {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) : ImageQuot d hd ϕ U :=
  Quotient.mk (imageZeroSetoid d hd ϕ U) ⟨ϕ.func x, ⟨x, hx, rfl⟩⟩

theorem imageQuotMk_eq_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    imageQuotMk d hd ϕ U x hx = imageQuotMk d hd ϕ U y hy ↔
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) := by
  exact Quotient.eq (r := imageZeroSetoid d hd ϕ U)

/-- Zero-distance fiber preorder `ϕ_A ⪰_{fiber, U} ϕ_B`, defined by `R_~(ϕ_A | U) ⊆ R_~(ϕ_B | U)`. -/
def FiberPreorder {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (U : Set X) (ϕA ϕB : Operator X bot) : Prop :=
  zeroDistRel d ϕA U ⊆ zeroDistRel d ϕB U

/-- Separating property of a gauge family restricted to a subset `S`. -/
def IsSeparatingOn {X I : Type} (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

/-! ### Proposition 3.5: Basic Properties of Computational Fibers (CH03-P06-01..08) -/

/-- Proposition 3.5(i): Target zero-distance invariance. -/
theorem prop_3_5_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (U : Set X) (y y' : X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty)
    (hyy' : subfamily_pseudometric d J y y' = 0) :
    compFiber d ϕ J U y = compFiber d ϕ J U y' := by
  have hzero := (subfamily_pseudometric_eq_zero_iff d J y y').mp hyy'
  ext x
  simp only [compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, fun j hj => le_antisymm ?_ (zero_le _)⟩
    calc
      d j (ϕ.func x) y' ≤ d j (ϕ.func x) y + d j y y' := (hd j).triangle _ _ _
      _ = 0 := by rw [hxy j hj, hzero j hj, zero_add]
  · rintro ⟨hx, hxy'⟩
    refine ⟨hx, fun j hj => le_antisymm ?_ (zero_le _)⟩
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) y' + d j y' y := (hd j).triangle _ _ _
      _ = 0 := by rw [hxy' j hj, (hd j).symm y' y, hzero j hj, zero_add]

/-- Proposition 3.5(ii-a): Every image-target fiber is nonempty and these fibers cover `U`. -/
theorem prop_3_5_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (U : Set X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty) :
    (∀ y ∈ operator_image ϕ U, (compFiber d ϕ J U y).Nonempty) ∧
    (⋃ y ∈ operator_image ϕ U, compFiber d ϕ J U y) = U ∧
    ⋃₀ compFiberFamily d ϕ J U = U := by
  have hnonempty : ∀ y ∈ operator_image ϕ U, (compFiber d ϕ J U y).Nonempty := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [subfamily_pseudometric_eq_zero_iff]
    intro j _
    exact (hd j).dist_self (ϕ.func x)
  have hunion : (⋃ y ∈ operator_image ϕ U, compFiber d ϕ J U y) = U := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, _, hx, _⟩
      exact hx
    · intro hx
      refine ⟨ϕ.func x, ⟨x, hx, rfl⟩, hx, ?_⟩
      rw [subfamily_pseudometric_eq_zero_iff]
      intro j _
      exact (hd j).dist_self (ϕ.func x)
  have hsUnion : ⋃₀ compFiberFamily d ϕ J U = U := by
    rw [compFiberFamily, Set.sUnion_image]
    exact hunion
  exact ⟨hnonempty, hunion, hsUnion⟩

/-- Proposition 3.5(ii-b): Image-target fibers are either equal or disjoint; after deduplication
`compFiberFamily` forms a partition of `U`. -/
theorem prop_3_5_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (U : Set X)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    (∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      compFiber d ϕ J U y₁ = compFiber d ϕ J U y₂ ∨
      Disjoint (compFiber d ϕ J U y₁) (compFiber d ϕ J U y₂)) ∧
    (compFiberFamily d ϕ J U).PairwiseDisjoint id ∧
    (∀ F ∈ compFiberFamily d ϕ J U, F.Nonempty ∧ F ⊆ U) ∧
    ⋃₀ compFiberFamily d ϕ J U = U := by
  have hdisj : ∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      compFiber d ϕ J U y₁ = compFiber d ϕ J U y₂ ∨
      Disjoint (compFiber d ϕ J U y₁) (compFiber d ϕ J U y₂) := by
    intro y₁ _ y₂ _
    by_cases hinter : (compFiber d ϕ J U y₁ ∩ compFiber d ϕ J U y₂).Nonempty
    · left
      rcases hinter with ⟨x, hx1, hx2⟩
      apply prop_3_5_i d hd ϕ J U y₁ y₂ hU hJ
      rw [subfamily_pseudometric_eq_zero_iff]
      have h1 := (subfamily_pseudometric_eq_zero_iff d J (ϕ.func x) y₁).mp hx1.2
      have h2 := (subfamily_pseudometric_eq_zero_iff d J (ϕ.func x) y₂).mp hx2.2
      intro j hj
      apply le_antisymm _ (zero_le _)
      calc
        d j y₁ y₂ ≤ d j y₁ (ϕ.func x) + d j (ϕ.func x) y₂ := (hd j).triangle _ _ _
        _ = 0 := by rw [(hd j).symm y₁ (ϕ.func x), h1 j hj, h2 j hj, zero_add]
    · right
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hinter
  have hpair : (compFiberFamily d ϕ J U).PairwiseDisjoint id := by
    rintro F₁ ⟨y₁, hy₁, rfl⟩ F₂ ⟨y₂, hy₂, rfl⟩ hne
    rcases hdisj y₁ hy₁ y₂ hy₂ with heq | hdis
    · exact (hne heq).elim
    · exact hdis
  have hmem : ∀ F ∈ compFiberFamily d ϕ J U, F.Nonempty ∧ F ⊆ U := by
    rintro F ⟨y, hy, rfl⟩
    refine ⟨(prop_3_5_ii_a d hd ϕ J U hU hJ).1 y hy, fun x hx => hx.1⟩
  exact ⟨hdisj, hpair, hmem, (prop_3_5_ii_a d hd ϕ J U hU hJ).2.2⟩

/-- Proposition 3.5(iii): Component intersection law for any nonempty subfamily `J`. -/
theorem prop_3_5_iii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J : Set I) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    compFiber d ϕ J U y = ⋂ j ∈ J, compFiberSingle d ϕ j U y := by
  ext x
  simp only [compFiber, compFiberSingle, Set.mem_setOf_eq, Set.mem_iInter,
    subfamily_pseudometric_eq_zero_iff]
  constructor
  · rintro ⟨hx, h⟩ j hj
    exact ⟨hx, h j hj⟩
  · intro h
    rcases hJ with ⟨j₀, hj₀⟩
    exact ⟨(h j₀ hj₀).1, fun j hj => (h j hj).2⟩

/-- Proposition 3.5(iv): Subfamily antitone inclusion `J ⊆ K → Fib_K ⊆ Fib_J`. -/
theorem prop_3_5_iv {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J K : Set I) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty) (_hK : K.Nonempty) (hJK : J ⊆ K) :
    compFiber d ϕ K U y ⊆ compFiber d ϕ J U y := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [subfamily_pseudometric_eq_zero_iff]
  intro j hj
  exact (subfamily_pseudometric_eq_zero_iff d K (ϕ.func x) y).mp hx.2 j (hJK hj)

/-- Proposition 3.5(v): Subfamily boundaries (`J = {i}` and `J = I`). -/
theorem prop_3_5_v {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) :
    (∀ i : I, compFiber d ϕ ({i} : Set I) U y = compFiberSingle d ϕ i U y) ∧
    (∀ i : I, compFiber d ϕ Set.univ U y ⊆ compFiberSingle d ϕ i U y) := by
  constructor
  · intro i
    exact compFiber_singleton_eq_single d ϕ i U y
  · intro i x hx
    refine ⟨hx.1, ?_⟩
    exact (subfamily_pseudometric_eq_zero_iff d Set.univ (ϕ.func x) y).mp hx.2 i trivial

/-- Proposition 3.5(vi-a): Identity component fiber equals the input zero-distance class. -/
theorem prop_3_5_vi_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (y : X)
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_id d ϕ U) :
    compFiberSingle d ϕ j U y = { x ∈ U | d j x y = 0 } := by
  ext x
  simp only [compFiberSingle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    calc
      d j x y ≤ d j x (ϕ.func x) + d j (ϕ.func x) y := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm x (ϕ.func x), hj.2 x hx, hxy, zero_add]
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) x + d j x y := (hd j).triangle _ _ _
      _ = 0 := by rw [hj.2 x hx, hxy, zero_add]

/-- Proposition 3.5(vi-b): Constant component fiber equals `U` at any image target `y₀ ∈ ϕ(U)`,
and equals `∅` at any target `y` with `d_j(y, y₀) > 0`. -/
theorem prop_3_5_vi_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I)
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_const d ϕ U) :
    ∀ y₀ ∈ operator_image ϕ U,
      compFiberSingle d ϕ j U y₀ = U ∧
      (∀ y : X, 0 < d j y y₀ → compFiberSingle d ϕ j U y = ∅) := by
  rintro y₀ ⟨x₀, hx₀, rfl⟩
  constructor
  · ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hj x hx x₀ hx₀
  · intro y hypos
    ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, hxy⟩
    have hzero : d j y (ϕ.func x₀) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        d j y (ϕ.func x₀)
            ≤ d j y (ϕ.func x) + d j (ϕ.func x) (ϕ.func x₀) := (hd j).triangle _ _ _
        _ = 0 := by rw [(hd j).symm y (ϕ.func x), hxy, hj x hx x₀ hx₀, zero_add]
    exact (ne_of_gt hypos) hzero

/-! ### Proposition 3.6: Point-Value Image Factorization and Scalar Lip Bound (CH03-P07-01..04) -/

/-- Proposition 3.6(i-necessary): Existence of a point-value factor map `T : ϕ_A(U) → X`
implies `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)`. -/
theorem prop_3_6_i_nec {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB)
    (hT : ∃ T : { z : X // z ∈ operator_image ϕA U } → X,
      ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) :
    pointEqRel ϕA U ⊆ pointEqRel ϕB U := by
  rcases hT with ⟨T, hT⟩
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have h1 := hT x hx
  have h2 := hT y hy
  have harg : (⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ : { z : X // z ∈ operator_image ϕA U }) =
      ⟨ϕA.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hxy
  rw [← h1, ← h2, harg]

/-- Proposition 3.6(i-sufficient): `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)` constructs a well-defined map
`T : ϕ_A(U) → X` satisfying `T ∘ ϕ_A = ϕ_B` on `U` (including when `U = ∅`). -/
theorem prop_3_6_i_suff {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB)
    (hsub : pointEqRel ϕA U ⊆ pointEqRel ϕB U) :
    ∃ T : { z : X // z ∈ operator_image ϕA U } → X,
      ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x := by
  classical
  refine ⟨fun z => ϕB.func (Classical.choose z.2), ?_⟩
  intro x hx
  let z : { z : X // z ∈ operator_image ϕA U } := ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩
  have hspec := Classical.choose_spec z.2
  have hrel : (Classical.choose z.2, x) ∈ pointEqRel ϕA U := ⟨hspec.1, hx, hspec.2⟩
  exact (hsub hrel).2.2

/-- Proposition 3.6(i): Full equivalence for unidirectional point-value factorization. -/
theorem prop_3_6_i {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB) :
    (∃ T : { z : X // z ∈ operator_image ϕA U } → X,
      ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ↔
      pointEqRel ϕA U ⊆ pointEqRel ϕB U :=
  ⟨prop_3_6_i_nec ϕA ϕB U hUA hUB, prop_3_6_i_suff ϕA ϕB U hUA hUB⟩

/-- Proposition 3.6(ii): Bidirectional point-value factorization exists iff
`R_=(ϕ_A | U) = R_=(ϕ_B | U)`. -/
theorem prop_3_6_ii {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB) :
    ((∃ T_AB : { z : X // z ∈ operator_image ϕA U } → X,
        ∀ x (hx : x ∈ U), T_AB ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ∧
     (∃ T_BA : { z : X // z ∈ operator_image ϕB U } → X,
        ∀ x (hx : x ∈ U), T_BA ⟨ϕB.func x, ⟨x, hx, rfl⟩⟩ = ϕA.func x)) ↔
      pointEqRel ϕA U = pointEqRel ϕB U := by
  rw [prop_3_6_i ϕA ϕB U hUA hUB, prop_3_6_i ϕB ϕA U hUB hUA, Set.Subset.antisymm_iff]

/-- Proposition 3.6(iii): In the single-component setting, if `T : ϕ_A(U) → X` satisfies
`T ∘ ϕ_A = ϕ_B` on `U`, `ϕ_A` is `K_A`-co-Lip (`0 < K_A < ∞`), and `ϕ_B` is `L_B`-Lip (`L_B < ∞`),
then `T` is `(L_B / K_A)`-Lip on `ϕ_A(U)`. -/
theorem prop_3_6_iii {X : Type} {bot : X}
    (d : X → X → ENNReal) (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB)
    (T : { z : X // z ∈ operator_image ϕA U } → X)
    (hT : ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x)
    (K_A L_B : ENNReal) (hK_pos : 0 < K_A) (hK_fin : K_A < ⊤) (_hL_fin : L_B < ⊤)
    (hcoLip : ∀ x ∈ U, ∀ x' ∈ U, K_A * d x x' ≤ d (ϕA.func x) (ϕA.func x'))
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d (ϕB.func x) (ϕB.func x') ≤ L_B * d x x') :
    ∀ y y' : { z : X // z ∈ operator_image ϕA U },
      d (T y) (T y') ≤ (L_B / K_A) * d y.1 y'.1 := by
  intro y y'
  rcases y with ⟨yval, x, hx, rfl⟩
  rcases y' with ⟨y'val, x', hx', rfl⟩
  rw [hT x hx, hT x' hx']
  have hK_ne0 : K_A ≠ 0 := ne_of_gt hK_pos
  have hK_netop : K_A ≠ ⊤ := ne_of_lt hK_fin
  have hdx : d x x' ≤ K_A⁻¹ * d (ϕA.func x) (ϕA.func x') := by
    calc
      d x x' = K_A⁻¹ * (K_A * d x x') := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK_ne0 hK_netop, one_mul]
      _ ≤ K_A⁻¹ * d (ϕA.func x) (ϕA.func x') :=
        mul_le_mul_right (hcoLip x hx x' hx') K_A⁻¹
  calc
    d (ϕB.func x) (ϕB.func x') ≤ L_B * d x x' := hLip x hx x' hx'
    _ ≤ L_B * (K_A⁻¹ * d (ϕA.func x) (ϕA.func x')) := mul_le_mul_right hdx L_B
    _ = (L_B / K_A) * d (ϕA.func x) (ϕA.func x') := by rw [div_eq_mul_inv, mul_assoc]

/-- Proposition 3.6(iii) matrix specialization for single-component gauge spaces (`[Subsingleton I]`). -/
theorem prop_3_6_iii_subsingleton {X I : Type} {bot : X} [Fintype I] [Subsingleton I]
    (d : I → X → X → ENNReal) (i : I) (ϕA ϕB : Operator X bot) (U : Set X)
    (T : { z : X // z ∈ operator_image ϕA U } → X)
    (hT : ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x)
    (K L : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕA U K) (hL : IsLipMatrix d ϕB U L)
    (hK_pos : 0 < K i i) (hK_fin : K i i < ⊤) (hL_fin : L i i < ⊤) :
    ∀ y y' : { z : X // z ∈ operator_image ϕA U },
      d i (T y) (T y') ≤ (L i i / K i i) * d i y.1 y'.1 := by
  apply prop_3_6_iii (d i) ϕA ϕB U hK.2.1 hL.1 T hT (K i i) (L i i) hK_pos hK_fin hL_fin
  · intro x hx x' hx'
    have h := hK.2.2 x hx x' hx' i
    have hsum : (∑ k : I, K k i * d k x x') = K i i * d i x x' := by
      apply Finset.sum_eq_single i
      · intro k _ hk; exact (hk (Subsingleton.elim k i)).elim
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    simpa [hsum] using h
  · exact single_component_lip_matrix_ineq d ϕB U L i hL

/-! ### Proposition 3.7: Image Factorization on the Zero-Distance Quotient (CH03-P08-01..03) -/

/-- Proposition 3.7 (unidirectional): A quotient map `Tbar : ϕ_A(U)/~_G → ϕ_B(U)/~_G` satisfying
`Tbar([ϕ_A(x)]) = [ϕ_B(x)]` exists iff `R_~(ϕ_A | U) ⊆ R_~(ϕ_B | U)`. -/
theorem prop_3_7_one_way {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB) :
    (∃ Tbar : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
      ∀ x (hx : x ∈ U), Tbar (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx) ↔
      zeroDistRel d ϕA U ⊆ zeroDistRel d ϕB U := by
  classical
  constructor
  · rintro ⟨Tbar, hTbar⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    have hqA : imageQuotMk d hd ϕA U x hx = imageQuotMk d hd ϕA U y hy :=
      (imageQuotMk_eq_iff d hd ϕA U hx hy).mpr hxy
    have hqB : imageQuotMk d hd ϕB U x hx = imageQuotMk d hd ϕB U y hy := by
      rw [← hTbar x hx, ← hTbar y hy, hqA]
    exact (imageQuotMk_eq_iff d hd ϕB U hx hy).mp hqB
  · intro hsub
    let f : { z : X // z ∈ operator_image ϕA U } → ImageQuot d hd ϕB U :=
      fun z => imageQuotMk d hd ϕB U (Classical.choose z.2) (Classical.choose_spec z.2).1
    have hresp : ∀ a b : { z : X // z ∈ operator_image ϕA U },
        (imageZeroSetoid d hd ϕA U).r a b → f a = f b := by
      intro a b hab
      have ha := Classical.choose_spec a.2
      have hb := Classical.choose_spec b.2
      have hrelA : (Classical.choose a.2, Classical.choose b.2) ∈ zeroDistRel d ϕA U := by
        refine ⟨ha.1, hb.1, ?_⟩
        simpa [ha.2, hb.2] using hab
      have hrelB := hsub hrelA
      exact (imageQuotMk_eq_iff d hd ϕB U ha.1 hb.1).mpr hrelB.2.2
    refine ⟨Quotient.lift f hresp, ?_⟩
    intro x hx
    change f ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = imageQuotMk d hd ϕB U x hx
    dsimp [f]
    have hspec := Classical.choose_spec (⟨x, hx, rfl⟩ : ϕA.func x ∈ operator_image ϕA U)
    have hrelA : (Classical.choose (⟨x, hx, rfl⟩ : ϕA.func x ∈ operator_image ϕA U), x) ∈
        zeroDistRel d ϕA U := by
      refine ⟨hspec.1, hx, ?_⟩
      intro i
      rw [hspec.2]
      exact (hd i).dist_self (ϕA.func x)
    exact (imageQuotMk_eq_iff d hd ϕB U hspec.1 hx).mpr (hsub hrelA).2.2

/-- Proposition 3.7 (bidirectional): Quotient maps in both directions exist iff
`R_~(ϕ_A | U) = R_~(ϕ_B | U)`. -/
theorem prop_3_7_two_way {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB) :
    ((∃ Tbar_AB : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
        ∀ x (hx : x ∈ U), Tbar_AB (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx) ∧
     (∃ Tbar_BA : ImageQuot d hd ϕB U → ImageQuot d hd ϕA U,
        ∀ x (hx : x ∈ U), Tbar_BA (imageQuotMk d hd ϕB U x hx) = imageQuotMk d hd ϕA U x hx)) ↔
      zeroDistRel d ϕA U = zeroDistRel d ϕB U := by
  rw [prop_3_7_one_way d hd ϕA ϕB U hUA hUB, prop_3_7_one_way d hd ϕB ϕA U hUB hUA,
    Set.Subset.antisymm_iff]

/-- Helper: when the gauge family separates an operator's actual image `ϕ(U)`,
`R_=(ϕ | U) = R_~(ϕ | U)`. -/
theorem pointEqRel_eq_zeroDistRel_of_separatingOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X)
    (hsep : IsSeparatingOn d (operator_image ϕ U)) :
    pointEqRel ϕ U = zeroDistRel d ϕ U := by
  ext ⟨x, y⟩
  simp only [pointEqRel, zeroDistRel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, fun i => by rw [hxy]; exact (hd i).dist_self _⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, hsep (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩ hxy⟩

/-- Proposition 3.7 (image-separating specialization): If the gauge family separates each of the
two actual images `ϕ_A(U)` and `ϕ_B(U)`, then `R_= = R_~` on each side, and both the unidirectional
and bidirectional point-value criteria coincide with the quotient criteria. -/
theorem prop_3_7_image_separating {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB)
    (hsepA : IsSeparatingOn d (operator_image ϕA U))
    (hsepB : IsSeparatingOn d (operator_image ϕB U)) :
    pointEqRel ϕA U = zeroDistRel d ϕA U ∧
    pointEqRel ϕB U = zeroDistRel d ϕB U ∧
    ((∃ T : { z : X // z ∈ operator_image ϕA U } → X,
        ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ↔
     (∃ Tbar : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
        ∀ x (hx : x ∈ U), Tbar (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx)) ∧
    (((∃ T_AB : { z : X // z ∈ operator_image ϕA U } → X,
        ∀ x (hx : x ∈ U), T_AB ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ∧
      (∃ T_BA : { z : X // z ∈ operator_image ϕB U } → X,
        ∀ x (hx : x ∈ U), T_BA ⟨ϕB.func x, ⟨x, hx, rfl⟩⟩ = ϕA.func x)) ↔
     ((∃ Tbar_AB : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
        ∀ x (hx : x ∈ U), Tbar_AB (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx) ∧
      (∃ Tbar_BA : ImageQuot d hd ϕB U → ImageQuot d hd ϕA U,
        ∀ x (hx : x ∈ U), Tbar_BA (imageQuotMk d hd ϕB U x hx) = imageQuotMk d hd ϕA U x hx))) := by
  have hA := pointEqRel_eq_zeroDistRel_of_separatingOn d hd ϕA U hsepA
  have hB := pointEqRel_eq_zeroDistRel_of_separatingOn d hd ϕB U hsepB
  refine ⟨hA, hB, ?_, ?_⟩
  · rw [prop_3_6_i ϕA ϕB U hUA hUB, prop_3_7_one_way d hd ϕA ϕB U hUA hUB, hA, hB]
  · rw [prop_3_6_ii ϕA ϕB U hUA hUB, prop_3_7_two_way d hd ϕA ϕB U hUA hUB, hA, hB]

/-! ### Remark: Transitivity of Fiber Inclusion (CH03-P09-01..03) -/

/-- Remark (CH03-P09-01): `FiberPreorder d U` is reflexive and transitive. -/
theorem remark_fiber_preorder_refl_trans {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) :
    (∀ ϕ : Operator X bot, FiberPreorder d U ϕ ϕ) ∧
    (∀ ϕ₁ ϕ₂ ϕ₃ : Operator X bot,
      FiberPreorder d U ϕ₁ ϕ₂ → FiberPreorder d U ϕ₂ ϕ₃ → FiberPreorder d U ϕ₁ ϕ₃) := by
  exact ⟨fun _ => Set.Subset.rfl, fun _ _ _ h12 h23 => h12.trans h23⟩

/-- Remark (CH03-P09-02): Along any finite chain `ϕ₀, …, ϕₘ` with stepwise `ϕ_{r-1} ⪰ ϕ_r`,
we have `ϕ_a ⪰ ϕ_b` for every `0 ≤ a ≤ b ≤ m` (in particular `a < b`). -/
theorem remark_fiber_chain_trans {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) {m : ℕ}
    (ϕ : Fin (m + 1) → Operator X bot)
    (_hdom : ∀ k : Fin (m + 1), U ⊆ dom (ϕ k))
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕ r.castSucc) (ϕ r.succ)) :
    ∀ a b : Fin (m + 1), a ≤ b → FiberPreorder d U (ϕ a) (ϕ b) := by
  have hnat : ∀ (a b : ℕ) (ha : a < m + 1) (hb : b < m + 1), a ≤ b →
      FiberPreorder d U (ϕ ⟨a, ha⟩) (ϕ ⟨b, hb⟩) := by
    intro a b ha hb hab
    induction b with
    | zero =>
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
        subst ha0
        exact Set.Subset.rfl
    | succ b ih =>
        by_cases hEq : a = b + 1
        · subst hEq
          exact Set.Subset.rfl
        · have hle : a ≤ b := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hab hEq)
          have hb' : b < m := Nat.lt_of_succ_lt_succ hb
          have hprev := ih (Nat.lt_trans hb' (Nat.lt_succ_self m)) hle
          have hlast : FiberPreorder d U (ϕ ⟨b, Nat.lt_trans hb' (Nat.lt_succ_self m)⟩)
              (ϕ ⟨b + 1, hb⟩) := hstep ⟨b, hb'⟩
          exact hprev.trans hlast
  intro a b hab
  exact hnat a.1 b.1 a.2 b.2 hab

/-- Remark (CH03-P09-03): If some step in the chain is a strict inclusion, then the endpoints
satisfy strict inclusion `R_~(ϕ₀ | U) ⊂ R_~(ϕₘ | U)` with an explicit difference witness. -/
theorem remark_fiber_chain_strict {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) {m : ℕ}
    (ϕ : Fin (m + 1) → Operator X bot)
    (hdom : ∀ k : Fin (m + 1), U ⊆ dom (ϕ k))
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕ r.castSucc) (ϕ r.succ))
    (hstrict : ∃ r : Fin m, zeroDistRel d (ϕ r.castSucc) U ⊂ zeroDistRel d (ϕ r.succ) U) :
    zeroDistRel d (ϕ 0) U ⊂ zeroDistRel d (ϕ (Fin.last m)) U ∧
    ∃ p : X × X, p ∈ zeroDistRel d (ϕ (Fin.last m)) U \ zeroDistRel d (ϕ 0) U := by
  have htrans := remark_fiber_chain_trans d U ϕ hdom hstep
  have h0m : zeroDistRel d (ϕ 0) U ⊆ zeroDistRel d (ϕ (Fin.last m)) U :=
    htrans 0 (Fin.last m) (Fin.zero_le _)
  rcases hstrict with ⟨r, hr_sub, hr_not_sub⟩
  have hex : ∃ p, p ∈ zeroDistRel d (ϕ r.succ) U ∧ p ∉ zeroDistRel d (ϕ r.castSucc) U := by
    by_contra hall
    push Not at hall
    exact hr_not_sub hall
  rcases hex with ⟨p, hp_succ, hp_not_prev⟩
  have h0_prev : zeroDistRel d (ϕ 0) U ⊆ zeroDistRel d (ϕ r.castSucc) U :=
    htrans 0 r.castSucc (Fin.zero_le _)
  have hsucc_m : zeroDistRel d (ϕ r.succ) U ⊆ zeroDistRel d (ϕ (Fin.last m)) U :=
    htrans r.succ (Fin.last m) (Fin.le_last _)
  have hp_in_m : p ∈ zeroDistRel d (ϕ (Fin.last m)) U := hsucc_m hp_succ
  have hp_not_0 : p ∉ zeroDistRel d (ϕ 0) U := fun hp0 => hp_not_prev (h0_prev hp0)
  refine ⟨⟨h0m, fun hm0 => hp_not_0 (hm0 hp_in_m)⟩, ⟨p, hp_in_m, hp_not_0⟩⟩

end Ch03
```

```lean filename=Ch03/NullificationRadius.lean
/-
Formalization of Chapter 3 (Section 3.3: Nullification Radius and Nullification Matrix)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.FiberFactorization

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.3: Pointwise Nullification Radius (CH03-D04) -/

/-- Admissibility of a finite positive radius `r ∈ (0, +∞)` at base point `y` on domain `U`. -/
def IsLegalNullRadius {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0

theorem isLegalNullRadius_iff_ball {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X) (r : ENNReal) :
    IsLegalNullRadius d_in d_out ϕ U y r ↔
      0 < r ∧ r < ⊤ ∧ ball d_in y r ∩ U ⊆ { x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0 } := by
  constructor
  · rintro ⟨hr0, hrt, h⟩
    refine ⟨hr0, hrt, ?_⟩
    rintro x ⟨hball, hxU⟩
    exact ⟨hxU, h x hxU hball⟩
  · rintro ⟨hr0, hrt, h⟩
    refine ⟨hr0, hrt, ?_⟩
    intro x hxU hlt
    exact (h ⟨hlt, hxU⟩).2

theorem isLegalNullRadius_subfamily_iff_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X)
    (y : X) (r : ENNReal) :
    IsLegalNullRadius (d i) (subfamily_pseudometric d J) ϕ U y r ↔
      0 < r ∧ r < ⊤ ∧ ball (d i) y r ∩ U ⊆ compFiber d ϕ J U (ϕ.func y) :=
  isLegalNullRadius_iff_ball (d i) (subfamily_pseudometric d J) ϕ U y r

theorem isLegalNullRadius_mono_down {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X}
    {r₁ r₂ : ENNReal} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂)
    (h₂ : IsLegalNullRadius d_in d_out ϕ U y r₂) :
    IsLegalNullRadius d_in d_out ϕ U y r₁ := by
  refine ⟨hr₁, lt_of_le_of_lt hle h₂.2.1, ?_⟩
  intro x hx hlt
  exact h₂.2.2 x hx (lt_of_lt_of_le hlt hle)

/-- Pointwise nullification inradius `r^N_{ϕ, d_in, d_out}(y | U)`. -/
noncomputable def pointwiseNullRadius {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X) : ENNReal :=
  sSup { r : ENNReal | IsLegalNullRadius d_in d_out ϕ U y r }

/-- Subfamily abbreviation `r^N_{ϕ, i, J}(y | U)`. -/
noncomputable def pointwiseNullRadiusSubfamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) (y : X) :
    ENNReal :=
  pointwiseNullRadius (d i) (subfamily_pseudometric d J) ϕ U y

/-- Single-component abbreviation `r^N_{ϕ, i, j}(y | U)`. -/
noncomputable def pointwiseNullRadiusComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) (y : X) : ENNReal :=
  pointwiseNullRadius (d i) (d j) ϕ U y

/-- Global pointwise nullification radius `r^N_{ϕ, d_in, d_out}(y)` on `dom ϕ`. -/
noncomputable def pointwiseNullRadiusGlobal {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) : ENNReal :=
  pointwiseNullRadius d_in d_out ϕ (dom ϕ) y

theorem pointwiseNullRadiusSubfamily_singleton {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) (y : X) :
    pointwiseNullRadiusSubfamily d ϕ i ({j} : Set I) U y =
      pointwiseNullRadiusComp d ϕ i j U y := by
  simp [pointwiseNullRadiusSubfamily, pointwiseNullRadiusComp, subfamily_pseudometric_singleton]

theorem pointwiseNullRadius_eq_zero_of_no_legal {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X}
    (hnone : ∀ r : ENNReal, ¬ IsLegalNullRadius d_in d_out ϕ U y r) :
    pointwiseNullRadius d_in d_out ϕ U y = 0 := by
  have hempty : { r : ENNReal | IsLegalNullRadius d_in d_out ϕ U y r } = ∅ := by
    ext r; simp [hnone r]
  simp [pointwiseNullRadius, hempty]

theorem pointwiseNullRadius_eq_top_of_all_finite_pos {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X}
    (hall : ∀ r : ENNReal, 0 < r → r < ⊤ → IsLegalNullRadius d_in d_out ϕ U y r) :
    pointwiseNullRadius d_in d_out ϕ U y = ⊤ := by
  by_contra hne
  have hlt : pointwiseNullRadius d_in d_out ϕ U y < ⊤ := lt_top_iff_ne_top.mpr hne
  let r : ENNReal := pointwiseNullRadius d_in d_out ϕ U y + 1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one le_add_self
  have hrt : r < ⊤ := ENNReal.add_lt_top.mpr ⟨hlt, ENNReal.one_lt_top⟩
  have hmem : r ∈ { s : ENNReal | IsLegalNullRadius d_in d_out ϕ U y s } := hall r hr0 hrt
  have hle : r ≤ pointwiseNullRadius d_in d_out ϕ U y := le_sSup hmem
  have hgt : pointwiseNullRadius d_in d_out ϕ U y < r := by
    change pointwiseNullRadius d_in d_out ϕ U y < pointwiseNullRadius d_in d_out ϕ U y + 1
    exact ENNReal.lt_add_right hne one_ne_zero
  exact not_le_of_gt hgt hle

theorem le_pointwiseNullRadius_of_all_lt_legal {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X} {M : ENNReal}
    (h : ∀ r : ENNReal, 0 < r → r < M → IsLegalNullRadius d_in d_out ϕ U y r) :
    M ≤ pointwiseNullRadius d_in d_out ϕ U y := by
  by_cases hM0 : M = 0
  · subst hM0; exact zero_le _
  · refine le_of_forall_lt fun c hc => ?_
    by_cases hc0 : c = 0
    · subst hc0
      obtain ⟨r, hr0, hrM⟩ := exists_between (pos_iff_ne_zero.mpr hM0)
      exact lt_of_lt_of_le hr0 (le_sSup (h r hr0 hrM))
    · obtain ⟨r, hcr, hrM⟩ := exists_between hc
      have hr0 : 0 < r := lt_trans (pos_iff_ne_zero.mpr hc0) hcr
      exact lt_of_lt_of_le hcr (le_sSup (h r hr0 hrM))

/-! ### Uniform Nullification Radius and Nullification Matrix (CH03-D05) -/

/-- Uniform nullification radius `\underline{r}^N_{ϕ, d_in, d_out}(A | U)` over base set `A`
with evaluation domain `U`. -/
noncomputable def uniformNullRadius {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, pointwiseNullRadius d_in d_out ϕ U y

/-- Uniform nullification radius on `U` (`A = U`): `\underline{r}^N_{ϕ, d_in, d_out}|_U`. -/
noncomputable def uniformNullRadiusOn {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  uniformNullRadius d_in d_out ϕ U U

/-- Subfamily uniform nullification radius on `U`: `\underline{r}^N_{ϕ, i, J}|_U`. -/
noncomputable def uniformNullRadiusSubfamilyOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  uniformNullRadiusOn (d i) (subfamily_pseudometric d J) ϕ U

/-- Component uniform nullification radius on `U`: `\underline{r}^N_{ϕ, i, j}|_U`. -/
noncomputable def uniformNullRadiusCompOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) : ENNReal :=
  uniformNullRadiusOn (d i) (d j) ϕ U

/-- Global uniform nullification radius (`A = U = dom ϕ`). -/
noncomputable def uniformNullRadiusGlobal {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) : ENNReal :=
  uniformNullRadiusOn d_in d_out ϕ (dom ϕ)

/-- Nullification matrix `N(ϕ)|_U` indexed as `(output j, input i)`:
`[N(ϕ)|_U]_{ji} := \underline{r}^N_{ϕ, i, j}|_U`. -/
noncomputable def nullificationMatrix {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : I → I → ENNReal :=
  fun j i => uniformNullRadiusCompOn d ϕ i j U

/-- Global nullification matrix `N(ϕ) = N(ϕ)|_{dom ϕ}`. -/
noncomputable def nullificationMatrixGlobal {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : I → I → ENNReal :=
  nullificationMatrix d ϕ (dom ϕ)

/-! ### Reusable Real Line with Absorbing Element `ℝ ⊔ {⊥}` -/

/-- The real line extended with a distinct absorbing element `none` (`⊥`). -/
abbrev RealWithBot : Type := Option ℝ

/-- Usual Euclidean distance on `ℝ` extended with absorbing-element isolation. -/
noncomputable def realWithBotDist : RealWithBot → RealWithBot → ENNReal
  | none, none => 0
  | some _, none => ⊤
  | none, some _ => ⊤
  | some x, some y => ENNReal.ofReal |x - y|

theorem realWithBotDist_extendedPseudoMetric :
    ExtendedPseudoMetric RealWithBot none realWithBotDist where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := by
    intro x
    cases x <;> simp [realWithBotDist]
  symm := by
    intro x y
    cases x <;> cases y <;> simp [realWithBotDist, abs_sub_comm]
  triangle := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [realWithBotDist]
    rename_i a b c
    calc
      ENNReal.ofReal |a - c| ≤ ENNReal.ofReal (|a - b| + |b - c|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le a b c)
      _ = ENNReal.ofReal |a - b| + ENNReal.ofReal |b - c| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  isolate_bot := by
    intro x hx
    cases x
    · exact (hx rfl).elim
    · rfl

/-! ### Counterexample 3.1: Everywhere-Positive Pointwise Radius with Zero Uniform Infimum (CH03-P10-01..03) -/

/-- Step operator `f(x) = 0` for `x < 0`, `f(x) = 1` for `x ≥ 0`, `f(⊥) = ⊥`. -/
noncomputable def stepOp : Operator RealWithBot none where
  func
    | none => none
    | some x => if x < 0 then some 0 else some 1
  preserves_bot := rfl

/-- Punctured interval `U = [-1, 0) ∪ (0, 1] ⊂ ℝ ⊔ {⊥}`. -/
def stepU : Set RealWithBot :=
  { z | ∃ x : ℝ, z = some x ∧ ((-1 ≤ x ∧ x < 0) ∨ (0 < x ∧ x ≤ 1)) }

/-- Counterexample 3.1 (CH03-P10-01): Legality of the space, step operator, and evaluation domain `U`. -/
theorem counterexample_3_1_valid :
    ExtendedPseudoMetric RealWithBot none realWithBotDist ∧
    stepU.Nonempty ∧
    stepU ⊆ dom stepOp := by
  refine ⟨realWithBotDist_extendedPseudoMetric, ⟨some 1, ⟨1, rfl, Or.inr ⟨zero_lt_one, le_rfl⟩⟩⟩, ?_⟩
  rintro z ⟨x, rfl, _⟩
  simp only [dom, Set.mem_setOf_eq, stepOp]
  split_ifs <;> simp

/-- Counterexample 3.1 (CH03-P10-02): For every `y = some t ∈ stepU`, the legal finite positive
radii are precisely `(0, |t|]`, so `r^N_{f, d, d}(some t | stepU) = |t| > 0`. -/
theorem counterexample_3_1_pointwise {t : ℝ} (ht : some t ∈ stepU) :
    (∀ r : ENNReal,
      IsLegalNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) r ↔
        0 < r ∧ r ≤ ENNReal.ofReal |t|) ∧
    pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) =
      ENNReal.ofReal |t| ∧
    0 < pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) := by
  rcases ht with ⟨t', ht', hbounds⟩
  injection ht' with hteq
  subst hteq
  have ht_ne : t ≠ 0 := by
    rcases hbounds with ⟨_, hlt⟩ | ⟨hgt, _⟩
    · exact ne_of_lt hlt
    · exact ne_of_gt hgt
  have habs_pos : 0 < |t| := abs_pos.mpr ht_ne
  have hlegal_iff : ∀ r : ENNReal,
      IsLegalNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) r ↔
        0 < r ∧ r ≤ ENNReal.ofReal |t| := by
    intro r
    constructor
    · rintro ⟨hr0, hrt, hrad⟩
      refine ⟨hr0, ?_⟩
      by_contra hnotle
      have hgt : ENNReal.ofReal |t| < r := lt_of_not_ge hnotle
      have htoReal_gt : |t| < r.toReal := by
        rw [← ENNReal.ofReal_toReal (ne_of_lt hrt)] at hgt
        exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))).mp hgt
      let δ : ℝ := min 1 ((r.toReal - |t|) / 2)
      have hδ_pos : 0 < δ := lt_min zero_lt_one (by linarith)
      have hδ_le1 : δ ≤ 1 := min_le_left _ _
      have hδ_lt : δ < r.toReal - |t| := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      rcases hbounds with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
      · -- `t < 0`, pick `x = δ ∈ (0, 1] ⊆ stepU`
        have hxU : some δ ∈ stepU := ⟨δ, rfl, Or.inr ⟨hδ_pos, hδ_le1⟩⟩
        have hdist : realWithBotDist (some δ) (some t) < r := by
          rw [realWithBotDist, ← ENNReal.ofReal_toReal (ne_of_lt hrt)]
          apply (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))).mpr
          rw [abs_of_pos (show 0 < δ - t by linarith)]
          rw [abs_of_neg ht_neg] at hδ_lt
          linarith
        have hout := hrad (some δ) hxU hdist
        simp only [stepOp, if_neg (not_lt.mpr (le_of_lt hδ_pos)), if_pos ht_neg,
          realWithBotDist] at hout
        norm_num at hout
      · -- `t > 0`, pick `x = -δ ∈ [-1, 0) ⊆ stepU`
        have hxU : some (-δ) ∈ stepU := ⟨-δ, rfl, Or.inl ⟨by linarith, by linarith⟩⟩
        have hdist : realWithBotDist (some (-δ)) (some t) < r := by
          rw [realWithBotDist, ← ENNReal.ofReal_toReal (ne_of_lt hrt)]
          apply (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))).mpr
          rw [abs_of_neg (show -δ - t < 0 by linarith)]
          rw [abs_of_pos ht_pos] at hδ_lt
          linarith
        have hout := hrad (some (-δ)) hxU hdist
        simp only [stepOp, if_pos (show -δ < 0 by linarith),
          if_neg (not_lt.mpr (le_of_lt ht_pos)), realWithBotDist] at hout
        norm_num at hout
    · rintro ⟨hr0, hrle⟩
      refine ⟨hr0, lt_of_le_of_lt hrle ENNReal.ofReal_lt_top, ?_⟩
      rintro z ⟨x, rfl, hxbounds⟩ hdist
      have hlt_abs : |x - t| < |t| := by
        have hlt_enn : ENNReal.ofReal |x - t| < ENNReal.ofReal |t| :=
          lt_of_lt_of_le hdist hrle
        exact (ENNReal.ofReal_lt_ofReal_iff habs_pos).mp hlt_enn
      rcases hbounds with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
      · have hx_neg : x < 0 := by
          rw [abs_of_neg ht_neg] at hlt_abs
          have := (abs_lt.mp hlt_abs).2
          linarith
        simp [stepOp, hx_neg, ht_neg, realWithBotDist]
      · have hx_pos : 0 < x := by
          rw [abs_of_pos ht_pos] at hlt_abs
          have := (abs_lt.mp hlt_abs).1
          linarith
        simp [stepOp, not_lt.mpr (le_of_lt hx_pos), not_lt.mpr (le_of_lt ht_pos), realWithBotDist]
  have hrad_eq :
      pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) =
        ENNReal.ofReal |t| := by
    apply le_antisymm
    · apply sSup_le
      intro r hr
      exact ((hlegal_iff r).mp hr).2
    · apply le_sSup
      exact (hlegal_iff (ENNReal.ofReal |t|)).mpr ⟨ENNReal.ofReal_pos.mpr habs_pos, le_rfl⟩
  refine ⟨hlegal_iff, hrad_eq, ?_⟩
  rw [hrad_eq]
  exact ENNReal.ofReal_pos.mpr habs_pos

/-- Counterexample 3.1 (CH03-P10-03): Uniform nullification radius on `stepU` is `0`. -/
theorem counterexample_3_1_uniform_zero :
    uniformNullRadiusOn realWithBotDist realWithBotDist stepOp stepU = 0 := by
  apply le_antisymm _ (zero_le _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  let t : ℝ := min 1 ((ε : ℝ) / 2)
  have ht_pos : 0 < t := lt_min zero_lt_one (by positivity)
  have ht_le1 : t ≤ 1 := min_le_left _ _
  have htU : some t ∈ stepU := ⟨t, rfl, Or.inr ⟨ht_pos, ht_le1⟩⟩
  have hpt := (counterexample_3_1_pointwise htU).2.1
  calc
    uniformNullRadiusOn realWithBotDist realWithBotDist stepOp stepU
        ≤ pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) :=
          iInf₂_le (some t) htU
    _ = ENNReal.ofReal |t| := hpt
    _ = ENNReal.ofReal t := by rw [abs_of_pos ht_pos]
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (le_trans (min_le_right _ _) (by linarith))
    _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal

/-! ### Proposition 3.8: Constant Components and Uniform Nullification Radius (CH03-P11-01..03) -/

/-- Proposition 3.8(i-a): If `J ⊆ I_const(ϕ | U)`, then every image-target fiber equals `U`. -/
theorem prop_3_8_i_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (_hUne : U.Nonempty) (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty)
    (hJconst : J ⊆ I_const d ϕ U) :
    ∀ y ∈ U, compFiber d ϕ J U (ϕ.func y) = U := by
  intro y hy
  ext x
  simp only [compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff,
    and_iff_left_iff_imp]
  intro hx j hj
  exact hJconst hj x hx y hy

/-- Proposition 3.8(i-b): If `J ⊆ I_const(ϕ | U)`, then for every input index `i`,
every pointwise radius and the uniform nullification radius equal `+∞`. -/
theorem prop_3_8_i_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty)
    (hJconst : J ⊆ I_const d ϕ U) :
    ∀ i : I,
      (∀ y ∈ U, pointwiseNullRadiusSubfamily d ϕ i J U y = ⊤) ∧
      uniformNullRadiusSubfamilyOn d ϕ i J U = ⊤ := by
  intro i
  have hpt : ∀ y ∈ U, pointwiseNullRadiusSubfamily d ϕ i J U y = ⊤ := by
    intro y hy
    apply pointwiseNullRadius_eq_top_of_all_finite_pos
    intro r hr0 hrt
    rw [isLegalNullRadius_subfamily_iff_fiber]
    refine ⟨hr0, hrt, ?_⟩
    rw [prop_3_8_i_a d ϕ U J hUne hU hJ hJconst y hy]
    exact Set.inter_subset_right
  refine ⟨hpt, ?_⟩
  apply top_unique
  apply le_iInf₂
  intro y hy
  change ⊤ ≤ pointwiseNullRadiusSubfamily d ϕ i J U y
  rw [hpt y hy]

/-- Counterexample pseudometric family on `SwapSpace` for Proposition 3.8(ii):
component `i` assigns `d_i(a, b) = ∞`, and every other component assigns `d_k(a, b) = 1`. -/
def infInputDist {I : Type} [DecidableEq I] (i : I) (k : I) : SwapSpace → SwapSpace → ENNReal
  | .bot, .bot => 0
  | .bot, .a => ⊤
  | .bot, .b => ⊤
  | .a, .bot => ⊤
  | .b, .bot => ⊤
  | .a, .a => 0
  | .b, .b => 0
  | .a, .b => if k = i then ⊤ else 1
  | .b, .a => if k = i then ⊤ else 1

theorem infInputDist_extendedPseudoMetric {I : Type} [DecidableEq I] (i : I) :
    ∀ k : I, ExtendedPseudoMetric SwapSpace .bot (infInputDist i k) := by
  intro k
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by intro x; cases x <;> rfl
      symm := by intro x y; cases x <;> cases y <;> rfl
      triangle := by
        intro x y z
        by_cases hk : k = i <;>
          cases x <;> cases y <;> cases z <;> simp [infInputDist, hk]
      isolate_bot := by
        intro x hx
        cases x
        · exact (hx rfl).elim
        · rfl
        · rfl }

/-- Proposition 3.8(ii): For any index type `I` and any pair `(i, j)` (covering both `i = j`
and `i ≠ j`), `[N(id)|_U]_{ji} = +∞` does not imply `j ∈ I_const(id | U)`. -/
theorem prop_3_8_ii_counterexample {I : Type} [DecidableEq I] (i j : I) :
    (∀ k : I, ExtendedPseudoMetric SwapSpace .bot (infInputDist i k)) ∧
    swapU.Nonempty ∧
    swapU ⊆ dom (@operator_identity SwapSpace .bot) ∧
    nullificationMatrix (infInputDist i) (@operator_identity SwapSpace .bot) swapU j i = ⊤ ∧
    j ∉ I_const (infInputDist i) (@operator_identity SwapSpace .bot) swapU := by
  refine ⟨infInputDist_extendedPseudoMetric i, ⟨.a, Or.inl rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, operator_identity]
  · apply top_unique
    apply le_iInf₂
    intro y hy
    rw [pointwiseNullRadius_eq_top_of_all_finite_pos]
    intro r hr0 hrt
    refine ⟨hr0, hrt, ?_⟩
    intro x hx hdist
    have hxy : x = y := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · simp [infInputDist] at hdist
      · simp [infInputDist] at hdist
      · rfl
    subst hxy
    exact (infInputDist_extendedPseudoMetric i j).dist_self _
  · intro hconst
    have h := hconst .a (Or.inl rfl) .b (Or.inr rfl)
    by_cases hji : j = i <;> simp [operator_identity, infInputDist, hji] at h

/-- Explicit `i = j` instance of Proposition 3.8(ii). -/
theorem prop_3_8_ii_eq {I : Type} [DecidableEq I] (i : I) :
    nullificationMatrix (infInputDist i) (@operator_identity SwapSpace .bot) swapU i i = ⊤ ∧
    i ∉ I_const (infInputDist i) (@operator_identity SwapSpace .bot) swapU :=
  let h := prop_3_8_ii_counterexample i i
  ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- Explicit `i ≠ j` instance of Proposition 3.8(ii). -/
theorem prop_3_8_ii_ne {I : Type} [DecidableEq I] {i j : I} (_hne : i ≠ j) :
    nullificationMatrix (infInputDist i) (@operator_identity SwapSpace .bot) swapU j i = ⊤ ∧
    j ∉ I_const (infInputDist i) (@operator_identity SwapSpace .bot) swapU ∧
    infInputDist i i .a .b = ⊤ ∧ infInputDist i j .a .b = 1 := by
  have h := prop_3_8_ii_counterexample i j
  refine ⟨h.2.2.2.1, h.2.2.2.2, by simp [infInputDist], by simp [infInputDist, _hne.symm]⟩

/-! ### Proposition 3.9: Fibers and Nullification Radius of Identity Components (CH03-P12-01..02) -/

/-- Proposition 3.9(i): For `i ∈ I_id(ϕ | U)` and `y ∈ U`, `Fib_{ϕ, i}(ϕ(y) | U)` equals
the input zero-distance class `{x ∈ U | d_i(x, y) = 0}`. -/
theorem prop_3_9_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X)
    (hU : U ⊆ dom ϕ) (hy : y ∈ U) (hi : i ∈ I_id d ϕ U) :
    compFiberSingle d ϕ i U (ϕ.func y) = { x ∈ U | d i x y = 0 } := by
  ext x
  simp only [compFiberSingle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hzero⟩
    rw [prop_3_1_iii d ϕ U i (hd i) hU hi x hx y hy] at hzero
    exact ⟨hx, hzero⟩
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, ?_⟩
    rw [prop_3_1_iii d ϕ U i (hd i) hU hi x hx y hy]
    exact hzero

/-- Proposition 3.9(ii): If `i ∈ I_id(ϕ | U)` and a finite positive `r₀` ball inside `U`
contains only input zero-distance points, then `r^N_{ϕ, i, i}(y | U) ≥ r₀ > 0`. -/
theorem prop_3_9_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X) (r₀ : ENNReal)
    (hU : U ⊆ dom ϕ) (hy : y ∈ U) (hi : i ∈ I_id d ϕ U)
    (hr₀_pos : 0 < r₀) (hr₀_fin : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ { x ∈ U | d i x y = 0 }) :
    r₀ ≤ pointwiseNullRadiusComp d ϕ i i U y ∧ 0 < pointwiseNullRadiusComp d ϕ i i U y := by
  have hlegal : IsLegalNullRadius (d i) (d i) ϕ U y r₀ := by
    rw [isLegalNullRadius_iff_ball]
    refine ⟨hr₀_pos, hr₀_fin, ?_⟩
    have hfib := prop_3_9_i d hd ϕ U i y hU hy hi
    simpa [compFiberSingle] using hball.trans hfib.symm.subset
  have hle : r₀ ≤ pointwiseNullRadiusComp d ϕ i i U y := le_sSup hlegal
  exact ⟨hle, lt_of_lt_of_le hr₀_pos hle⟩

/-! ### Proposition 3.10: Component Minimum Formula for Uniform Nullification Radius (CH03-P13-01..03) -/

/-- Proposition 3.10 (pointwise): For a finite nonempty output subfamily `J`,
`r^N_{ϕ, i, J}(y | U) = min_{j ∈ J} r^N_{ϕ, i, j}(y | U)`. -/
theorem prop_3_10_pointwise {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    pointwiseNullRadiusSubfamily d ϕ i J U y =
      ⨅ j ∈ J, pointwiseNullRadiusComp d ϕ i j U y ∧
    pointwiseNullRadiusSubfamily d ϕ i J U y =
      J.toFinite.toFinset.inf' (by simpa [Set.Finite.toFinset_nonempty] using hJ)
        (fun j => pointwiseNullRadiusComp d ϕ i j U y) := by
  have hinf : pointwiseNullRadiusSubfamily d ϕ i J U y =
      ⨅ j ∈ J, pointwiseNullRadiusComp d ϕ i j U y := by
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply sSup_le
      intro r hr
      apply le_sSup
      refine ⟨hr.1, hr.2.1, ?_⟩
      intro x hx hlt
      exact (subfamily_pseudometric_eq_zero_iff d J _ _).mp (hr.2.2 x hx hlt) j hj
    · apply le_pointwiseNullRadius_of_all_lt_legal
      intro r hr0 hrlt
      refine ⟨hr0, lt_of_lt_of_le hrlt le_top, ?_⟩
      intro x hx hdx
      rw [subfamily_pseudometric_eq_zero_iff]
      intro j hj
      have hrj : r < pointwiseNullRadiusComp d ϕ i j U y :=
        lt_of_lt_of_le hrlt (iInf₂_le j hj)
      rcases lt_sSup_iff.mp hrj with ⟨r', hr'legal, hrr'⟩
      exact hr'legal.2.2 x hx (lt_trans hdx hrr')
  refine ⟨hinf, ?_⟩
  rw [hinf]
  let s := J.toFinite.toFinset
  have hs : s.Nonempty := by simpa [s, Set.Finite.toFinset_nonempty] using hJ
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro j hj
    exact iInf₂_le j (by simpa [s] using hj)
  · apply le_iInf₂
    intro j hj
    exact Finset.inf'_le (f := fun j => pointwiseNullRadiusComp d ϕ i j U y) (by simpa [s] using hj)

/-- Proposition 3.10 (uniform): Exchanging base-point infimum and finite nonempty minimum gives
`\underline{r}^N_{ϕ, i, J}|_U = min_{j ∈ J} [N(ϕ)|_U]_{ji}`. -/
theorem prop_3_10_uniform {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X)
    (_hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    uniformNullRadiusSubfamilyOn d ϕ i J U =
      ⨅ j ∈ J, nullificationMatrix d ϕ U j i ∧
    uniformNullRadiusSubfamilyOn d ϕ i J U =
      J.toFinite.toFinset.inf' (by simpa [Set.Finite.toFinset_nonempty] using hJ)
        (fun j => nullificationMatrix d ϕ U j i) := by
  have hinf : uniformNullRadiusSubfamilyOn d ϕ i J U =
      ⨅ j ∈ J, nullificationMatrix d ϕ U j i := by
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply le_iInf₂
      intro y hy
      calc
        uniformNullRadiusSubfamilyOn d ϕ i J U
            ≤ pointwiseNullRadiusSubfamily d ϕ i J U y := iInf₂_le y hy
        _ = ⨅ k ∈ J, pointwiseNullRadiusComp d ϕ i k U y :=
            (prop_3_10_pointwise d ϕ i J U y hU hJ).1
        _ ≤ pointwiseNullRadiusComp d ϕ i j U y := iInf₂_le j hj
    · apply le_iInf₂
      intro y hy
      change (⨅ j ∈ J, nullificationMatrix d ϕ U j i) ≤ pointwiseNullRadiusSubfamily d ϕ i J U y
      rw [(prop_3_10_pointwise d ϕ i J U y hU hJ).1]
      apply le_iInf₂
      intro j hj
      calc
        (⨅ k ∈ J, nullificationMatrix d ϕ U k i)
            ≤ nullificationMatrix d ϕ U j i := iInf₂_le j hj
        _ ≤ pointwiseNullRadiusComp d ϕ i j U y := iInf₂_le y hy
  refine ⟨hinf, ?_⟩
  rw [hinf]
  let s := J.toFinite.toFinset
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro j hj
    exact iInf₂_le j (by simpa [s] using hj)
  · apply le_iInf₂
    intro j hj
    exact Finset.inf'_le (f := fun j => nullificationMatrix d ϕ U j i) (by simpa [s] using hj)

/-- Proposition 3.10 (antitonicity): If `J ⊆ K`, then
`\underline{r}^N_{ϕ, i, K}|_U ≤ \underline{r}^N_{ϕ, i, J}|_U`. -/
theorem prop_3_10_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J K : Set I) (U : Set X)
    (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) (hK : K.Nonempty) (hJK : J ⊆ K) :
    uniformNullRadiusSubfamilyOn d ϕ i K U ≤ uniformNullRadiusSubfamilyOn d ϕ i J U := by
  rw [(prop_3_10_uniform d ϕ i K U hUne hU hK).1, (prop_3_10_uniform d ϕ i J U hUne hU hJ).1]
  apply le_iInf₂
  intro j hj
  exact iInf₂_le j (hJK hj)

/-! ### Proposition 3.11: Single-Step Criterion for Fiber Truncation (CH03-P14-01..03) -/

/-- Proposition 3.11 (fiber condition): Membership in `Fib_{ϕ₂, j}(ϕ₂(y) | U₂)` implies
`d_j(ϕ₂(y), ϕ₂(y')) = 0`. -/
theorem prop_3_11_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) {y y' : X}
    (_hU₂ : U₂ ⊆ dom ϕ₂) (_hy : y ∈ U₂) (_hy' : y' ∈ U₂)
    (hfib : y' ∈ compFiberSingle d ϕ₂ j U₂ (ϕ₂.func y)) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rw [(hd j).symm]
  exact hfib.2

/-- Proposition 3.11 (radius condition): Strictly smaller input distance than `r^N_{ϕ₂, i, j}(y | U₂)`
extracts a legal finite positive radius `ρ` and gives `d_j(ϕ₂(y), ϕ₂(y')) = 0`. -/
theorem prop_3_11_radius {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (i j : I) {y y' : X}
    (hU₂ : U₂ ⊆ dom ϕ₂) (hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hlt : d i y y' < pointwiseNullRadiusComp d ϕ₂ i j U₂ y) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rcases lt_sSup_iff.mp hlt with ⟨ρ, hρ_legal, hlt_ρ⟩
  have hmem : y' ∈ compFiberSingle d ϕ₂ j U₂ (ϕ₂.func y) := by
    refine ⟨hy', hρ_legal.2.2 y' hy' ?_⟩
    rw [(hd i).symm]
    exact hlt_ρ
  exact prop_3_11_fiber d hd ϕ₂ U₂ j hU₂ hy hy' hmem

/-- Proposition 3.11 (composite specialization): If `ϕ₁(x), ϕ₁(x') ∈ U₂` and `ϕ₁(x')` lies in
`Fib_{ϕ₂, j}(ϕ₂(ϕ₁(x)) | U₂)`, then `d_j((ϕ₂ ∘ ϕ₁)(x), (ϕ₂ ∘ ϕ₁)(x')) = 0`. -/
theorem prop_3_11_compose {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) {x x' : X}
    (hU₂ : U₂ ⊆ dom ϕ₂) (_hx : x ∈ dom ϕ₁) (_hx' : x' ∈ dom ϕ₁)
    (hfx : ϕ₁.func x ∈ U₂) (hfx' : ϕ₁.func x' ∈ U₂)
    (hfib : ϕ₁.func x' ∈ compFiberSingle d ϕ₂ j U₂ (ϕ₂.func (ϕ₁.func x))) :
    d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func x') = 0 :=
  prop_3_11_fiber d hd ϕ₂ U₂ j hU₂ hfx hfx' hfib

/-! ### Proposition 3.12: Composition Lower Bounds for Uniform Nullification Radius (CH03-P15-01..02) -/

/-- Proposition 3.12(i): If `ϕ₂` preserves zero-distance from `d_l` to `d_j` on the actual
intermediate image `ϕ₁(U)`, then `[N(ϕ₂ ∘ ϕ₁)|_U]_{ji} ≥ [N(ϕ₁)|_U]_{li}`. -/
theorem prop_3_12_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I)
    (_hUne : U.Nonempty) (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁))
    (hpres : ∀ y ∈ operator_image ϕ₁ U, ∀ y' ∈ operator_image ϕ₁ U,
      d l y y' = 0 → d j (ϕ₂.func y) (ϕ₂.func y') = 0) :
    nullificationMatrix d ϕ₁ U l i ≤
      nullificationMatrix d (operator_compose ϕ₂ ϕ₁) U j i := by
  have hU1 : U ⊆ dom ϕ₁ := hU.trans (dom_operator_compose_subset_left ϕ₂ ϕ₁)
  apply le_iInf₂
  intro x hx
  apply le_pointwiseNullRadius_of_all_lt_legal
  intro r hr0 hrlt
  refine ⟨hr0, lt_of_lt_of_le hrlt le_top, ?_⟩
  intro x' hx' hdx
  have hdx_symm : d i x x' < pointwiseNullRadiusComp d ϕ₁ i l U x := by
    rw [(hd i).symm]
    exact lt_of_lt_of_le (lt_trans hdx hrlt) (iInf₂_le x hx)
  have hl0 : d l (ϕ₁.func x) (ϕ₁.func x') = 0 :=
    prop_3_11_radius d hd ϕ₁ U i l hU1 hx hx' hdx_symm
  rw [(hd j).symm]
  exact hpres (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func x') ⟨x', hx', rfl⟩ hl0

/-- Proposition 3.12(ii): Pullback via a finite positive single-channel Lip upper bound `L` on `U`:
`[N(ϕ₂ ∘ ϕ₁)|_U]_{ji} ≥ [N(ϕ₂)|_{ϕ₁(U)}]_{jl} / L` (handling both `0` and `∞` on the RHS). -/
theorem prop_3_12_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I) (L : ENNReal)
    (_hUne : U.Nonempty) (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁))
    (_hL_pos : 0 < L) (_hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x') :
    nullificationMatrix d ϕ₂ (operator_image ϕ₁ U) j l / L ≤
      nullificationMatrix d (operator_compose ϕ₂ ϕ₁) U j i := by
  have hU2 : operator_image ϕ₁ U ⊆ dom ϕ₂ := image_subset_dom_of_compose ϕ₂ ϕ₁ hU
  apply le_iInf₂
  intro x hx
  apply le_pointwiseNullRadius_of_all_lt_legal
  intro r hr0 hrlt
  have hrt : r < ⊤ := lt_of_lt_of_le hrlt le_top
  refine ⟨hr0, hrt, ?_⟩
  intro x' hx' hdx
  have hLr_lt : L * r < nullificationMatrix d ϕ₂ (operator_image ϕ₁ U) j l := by
    rw [mul_comm]
    exact ENNReal.mul_lt_of_lt_div hrlt
  have hdl_lt : d l (ϕ₁.func x) (ϕ₁.func x') <
      pointwiseNullRadiusComp d ϕ₂ l j (operator_image ϕ₁ U) (ϕ₁.func x) := by
    calc
      d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x' := hLip x hx x' hx'
      _ = L * d i x' x := by rw [(hd i).symm]
      _ ≤ L * r := mul_le_mul_right (le_of_lt hdx) L
      _ < nullificationMatrix d ϕ₂ (operator_image ϕ₁ U) j l := hLr_lt
      _ ≤ pointwiseNullRadiusComp d ϕ₂ l j (operator_image ϕ₁ U) (ϕ₁.func x) :=
          iInf₂_le (ϕ₁.func x) ⟨x, hx, rfl⟩
  rw [(hd j).symm]
  exact prop_3_11_radius d hd ϕ₂ (operator_image ϕ₁ U) l j hU2
    ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩ hdl_lt

end Ch03
```

```lean filename=Ch03/ScaleAndCovering.lean
/-
Formalization of Chapter 3 (Sections 3.4 & 3.5: Input Scale, Threshold Classification,
Local Nullification, and Covering Numbers)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.NullificationRadius

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.4: Input Scale Family and Threshold Classification (CH03-D06) -/

/-- Monotone input scale family `σ_i` on nonempty subsets of `X`. -/
structure InputScaleFamily (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i : I, ∀ A₁ A₂ : Set X, A₁.Nonempty → A₁ ⊆ A₂ → scale i A₁ ≤ scale i A₂

/-- Default diameter scale `diam_{d_i}(A) = sup_{x, y ∈ A} d_i(x, y)`. -/
noncomputable def diamScaleFun {X I : Type} (d : I → X → X → ENNReal) (i : I) (A : Set X) :
    ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d i x y

/-- The diameter scale family satisfies the input scale monotonicity axiom. -/
noncomputable def diamScale {X I : Type} (d : I → X → X → ENNReal) : InputScaleFamily X I where
  scale := diamScaleFun d
  mono := by
    intro i A₁ A₂ _ hsub
    apply iSup₂_le
    intro x hx
    apply iSup₂_le
    intro y hy
    exact le_iSup₂_of_le x (hsub hx) (le_iSup₂_of_le y (hsub hy) le_rfl)

/-- Threshold classification `Type_{f, A}(i, j) ∈ {0, 1}²` (represented as `Fin 2 × Fin 2`).
First entry is `1` iff `σ_i(A) < τ_σ`; second entry is `1` iff `\underline{r}^N_{f, i, j}|_A ≥ τ_N`. -/
noncomputable def thresholdType {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    (τ_σ τ_N : ENNReal) (f : Operator X bot) (A : Set X) (i j : I) : Fin 2 × Fin 2 :=
  (if σ.scale i A < τ_σ then 1 else 0,
   if τ_N ≤ uniformNullRadiusCompOn d f i j A then 1 else 0)

/-! ### Covering Number, Entropy, and Total Boundedness Interface (CH03-D07) -/

/-- Subfamily covering number `N_J(ε, U) := N(d_J, ε, U)`. -/
noncomputable def subfamily_covering_number {X I : Type}
    (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) ε U

theorem subfamily_covering_number_singleton {X I : Type}
    (d : I → X → X → ENNReal) (i : I) (ε : ENNReal) (U : Set X) :
    subfamily_covering_number d ({i} : Set I) ε U = covering_number (d i) ε U := by
  simp [subfamily_covering_number, subfamily_pseudometric_singleton]

/-- Total boundedness of `U` with respect to extended pseudometric `d`:
`N(r, U) < +∞` for every finite positive `r ∈ (0, +∞)`. -/
def IsTotallyBounded {X : Type} (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

/-- Correspondence between frozen `InternalEpsilonNet` and the textbook ball-union definition. -/
theorem internalEpsilonNet_iff_ball {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (centers : Finset X) :
    InternalEpsilonNet d ε U centers ↔
      (↑centers : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ centers, ball d c ε := by
  constructor
  · rintro ⟨hsub, hcov⟩
    refine ⟨hsub, ?_⟩
    intro x hx
    rcases hcov x hx with ⟨c, hc, hdist⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hdist⟩
  · rintro ⟨hsub, hcov⟩
    refine ⟨hsub, ?_⟩
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨c, hc, hdist⟩
    exact ⟨c, hc, hdist⟩

theorem covering_number_le_of_net {X : Type} {d : X → X → ENNReal}
    {ε : ENNReal} {U : Set X} {centers : Finset X}
    (hnet : InternalEpsilonNet d ε U centers) :
    covering_number d ε U ≤ (centers.card : ENNReal) :=
  iInf_le_of_le centers (iInf_le_of_le hnet le_rfl)

theorem le_covering_number_iff {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (k : ENNReal) :
    k ≤ covering_number d ε U ↔
      ∀ centers : Finset X, InternalEpsilonNet d ε U centers → k ≤ (centers.card : ENNReal) := by
  simp only [covering_number, le_iInf_iff]

theorem covering_number_eq_zero_iff {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) :
    covering_number d ε U = 0 ↔ U = ∅ := by
  constructor
  · intro h0
    by_contra hne
    have hnon : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have h1 := one_le_covering_number_of_nonempty d ε U hnon
    rw [h0] at h1
    exact not_le_of_gt zero_lt_one h1
  · intro heq
    subst heq
    exact covering_number_empty d ε

/-- Monotonicity of `log2_ereal` on `ENNReal`. -/
theorem log2_ereal_mono {a b : ENNReal} (hab : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  by_cases ha0 : a = 0
  · subst ha0
    simp [log2_ereal]
  · by_cases hbtop : b = ⊤
    · subst hbtop
      simp [log2_ereal]
    · have hatop : a ≠ ⊤ := ne_top_of_le_ne_top hbtop hab
      have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha0) hab)
      simp only [log2_ereal, if_neg ha0, if_neg hatop, if_neg hb0, if_neg hbtop]
      apply EReal.coe_le_coe_iff.mpr
      exact Real.logb_le_logb_of_le one_lt_two
        (ENNReal.toReal_pos ha0 hatop)
        (ENNReal.toReal_mono hbtop hab)

@[simp] theorem log2_ereal_one : log2_ereal 1 = 0 := by
  simp [log2_ereal]

@[simp] theorem log2_ereal_two : log2_ereal 2 = 1 := by
  have h20 : (2 : ENNReal) ≠ 0 := by simp
  have h2t : (2 : ENNReal) ≠ ⊤ := by simp
  simp only [log2_ereal, if_neg h20, if_neg h2t, ENNReal.toReal_ofNat]
  rw [Real.logb_self_eq_one one_lt_two]
  rfl

theorem metric_entropy_mono_of_covering_number_le {X Y : Type}
    {d₁ : X → X → ENNReal} {d₂ : Y → Y → ENNReal}
    {ε₁ ε₂ : ENNReal} {U₁ : Set X} {U₂ : Set Y}
    (h : covering_number d₁ ε₁ U₁ ≤ covering_number d₂ ε₂ U₂) :
    metric_entropy d₁ ε₁ U₁ ≤ metric_entropy d₂ ε₂ U₂ :=
  log2_ereal_mono h

theorem metric_entropy_eq_coe_of_nonempty_of_lt_top {X : Type}
    {d : X → X → ENNReal} {ε : ENNReal} {U : Set X}
    (hU : U.Nonempty) (hfin : covering_number d ε U < ⊤) :
    metric_entropy d ε U = ↑(Real.logb 2 (covering_number d ε U).toReal) := by
  have hne0 : covering_number d ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty d ε U hU))
  have hnetop : covering_number d ε U ≠ ⊤ := ne_of_lt hfin
  simp [metric_entropy, log2_ereal, hne0, hnetop]

theorem metric_entropy_eq_top_iff {X : Type}
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) :
    metric_entropy d ε U = ⊤ ↔ covering_number d ε U = ⊤ := by
  by_cases h0 : covering_number d ε U = 0
  · simp [metric_entropy, log2_ereal, h0]
  · by_cases ht : covering_number d ε U = ⊤
    · simp [metric_entropy, log2_ereal, ht]
    · simp [metric_entropy, log2_ereal, h0, ht]

/-! ### Lemma 3.13: Four-Way Threshold Classification and Monotonicity (CH03-P16-01..03) -/

/-- Lemma 3.13 (exhaustiveness and mutual exclusivity of the four cells). -/
theorem lemma_3_13_partition {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    (τ_σ τ_N : ENNReal) (f : Operator X bot) (A : Set X) (i j : I) :
    (thresholdType d σ τ_σ τ_N f A i j = (1, 1) ↔
        σ.scale i A < τ_σ ∧ τ_N ≤ uniformNullRadiusCompOn d f i j A) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (1, 0) ↔
        σ.scale i A < τ_σ ∧ uniformNullRadiusCompOn d f i j A < τ_N) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (0, 1) ↔
        τ_σ ≤ σ.scale i A ∧ τ_N ≤ uniformNullRadiusCompOn d f i j A) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (0, 0) ↔
        τ_σ ≤ σ.scale i A ∧ uniformNullRadiusCompOn d f i j A < τ_N) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (1, 1) ∨
     thresholdType d σ τ_σ τ_N f A i j = (1, 0) ∨
     thresholdType d σ τ_σ τ_N f A i j = (0, 1) ∨
     thresholdType d σ τ_σ τ_N f A i j = (0, 0)) := by
  unfold thresholdType
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A <;>
      simp [h1, h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A
    · simp [h1, h2, not_lt.mpr h2]
    · simp [h1, h2, lt_of_not_ge h2]
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A
    · simp [h1, h2, not_le.mpr h1]
    · simp [h1, h2]
    · simp [h1, h2, le_of_not_gt h1]
    · simp [h1, h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A
    · simp [h1, h2]
    · simp [h1, h2, not_le.mpr h1]
    · simp [h1, h2, not_lt.mpr h2]
    · simp [h1, h2, le_of_not_gt h1, lt_of_not_ge h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A <;>
      simp [h1, h2]

/-- Lemma 3.13(i): Increasing `τ_σ` monotonically enlarges the set of channels with first entry `1`. -/
theorem lemma_3_13_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    {τ_σ τ_σ' : ENNReal} (τ_N : ENNReal) (f : Operator X bot) (A : Set X)
    (hτ : τ_σ ≤ τ_σ') :
    { p : I × I | (thresholdType d σ τ_σ τ_N f A p.1 p.2).1 = 1 } ⊆
      { p : I × I | (thresholdType d σ τ_σ' τ_N f A p.1 p.2).1 = 1 } := by
  intro ⟨i, j⟩ hp
  simp only [thresholdType, Set.mem_setOf_eq] at hp ⊢
  split_ifs at hp with hlt
  · rw [if_pos (lt_of_lt_of_le hlt hτ)]
  · exact ((by decide : (0 : Fin 2) ≠ 1) hp).elim

/-- Lemma 3.13(ii): Increasing `τ_N` monotonically shrinks the set of channels with second entry `1`. -/
theorem lemma_3_13_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    (τ_σ : ENNReal) {τ_N τ_N' : ENNReal} (f : Operator X bot) (A : Set X)
    (hτ : τ_N ≤ τ_N') :
    { p : I × I | (thresholdType d σ τ_σ τ_N' f A p.1 p.2).2 = 1 } ⊆
      { p : I × I | (thresholdType d σ τ_σ τ_N f A p.1 p.2).2 = 1 } := by
  intro ⟨i, j⟩ hp
  simp only [thresholdType, Set.mem_setOf_eq] at hp ⊢
  split_ifs at hp with hge
  · rw [if_pos (le_trans hτ hge)]
  · exact ((by decide : (0 : Fin 2) ≠ 1) hp).elim

/-! ### Proposition 3.14: Monotonicity under Domain Refinement (CH03-P17-01..04) -/

/-- Proposition 3.14(i): For any monotone input scale family, `∅ ≠ B ⊆ A` implies
`σ_i(B) ≤ σ_i(A)` and preserves `σ_i(·) < τ_σ`. -/
theorem prop_3_14_i {X I : Type} {bot : X}
    (σ : InputScaleFamily X I) (f : Operator X bot) (A B : Set X) (i : I) (τ_σ : ENNReal)
    (hBne : B.Nonempty) (hBA : B ⊆ A) (_hAdom : A ⊆ dom f) :
    σ.scale i B ≤ σ.scale i A ∧ (σ.scale i A < τ_σ → σ.scale i B < τ_σ) := by
  have hle := σ.mono i B A hBne hBA
  exact ⟨hle, fun hlt => lt_of_le_of_lt hle hlt⟩

/-- Proposition 3.14(ii-a): Shrinking the evaluation domain from `A` to `B ⊆ A` does not
decrease the pointwise nullification radius at any fixed `x ∈ B`. -/
theorem prop_3_14_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X) (i j : I) {x : X}
    (hBA : B ⊆ A) (_hAdom : A ⊆ dom f) (_hxB : x ∈ B) :
    pointwiseNullRadiusComp d f i j A x ≤ pointwiseNullRadiusComp d f i j B x := by
  apply sSup_le
  intro r hr
  apply le_sSup
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro z hz hdist
  exact hr.2.2 z (hBA hz) hdist

/-- Proposition 3.14(ii-b): Simultaneously shrinking the evaluation domain and the infimum
base set from `A` to `B` does not decrease the uniform nullification radius. -/
theorem prop_3_14_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X) (i j : I)
    (_hBne : B.Nonempty) (hBA : B ⊆ A) (hAdom : A ⊆ dom f) :
    uniformNullRadiusCompOn d f i j A ≤ uniformNullRadiusCompOn d f i j B := by
  calc
    uniformNullRadiusCompOn d f i j A
        ≤ uniformNullRadius (d i) (d j) f B A := by
          apply le_iInf₂
          intro x hxB
          exact iInf₂_le x (hBA hxB)
    _ ≤ uniformNullRadiusCompOn d f i j B := by
          apply le_iInf₂
          intro x hxB
          exact le_trans (iInf₂_le x hxB) (prop_3_14_ii_a d f A B i j hBA hAdom hxB)

/-- Proposition 3.14(iii): Counterexample showing the reverse scale judgment fails
(`A = {0, 1}`, `B = {0}`, `τ_σ = 1/2` on `ℝ ⊔ {⊥}`). -/
theorem prop_3_14_iii_counterexample :
    let d : Unit → RealWithBot → RealWithBot → ENNReal := fun _ => realWithBotDist
    let A : Set RealWithBot := {some 0, some 1}
    let B : Set RealWithBot := {some 0}
    let τ_σ : ENNReal := ENNReal.ofReal (1 / 2)
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot none (d u)) ∧
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (@operator_identity RealWithBot none) ∧
    0 < τ_σ ∧ τ_σ < ⊤ ∧
    diamScaleFun d () B = 0 ∧
    diamScaleFun d () B < τ_σ ∧
    diamScaleFun d () A = 1 ∧
    τ_σ ≤ diamScaleFun d () A := by
  intro d A B τ_σ
  have hdiamB : diamScaleFun d () B = 0 := by
    apply le_antisymm _ (zero_le _)
    apply iSup₂_le; intro x hx
    apply iSup₂_le; intro y hy
    rcases hx with rfl; rcases hy with rfl
    simp [d, realWithBotDist]
  have hdiamA : diamScaleFun d () A = 1 := by
    apply le_antisymm
    · apply iSup₂_le; intro x hx
      apply iSup₂_le; intro y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [d, realWithBotDist]
    · apply le_iSup₂_of_le (some 0) (Or.inl rfl)
      apply le_iSup₂_of_le (some 1) (Or.inr rfl)
      simp [d, realWithBotDist]
  have hτ_pos : 0 < τ_σ := ENNReal.ofReal_pos.mpr (by norm_num)
  have hτ_fin : τ_σ < ⊤ := ENNReal.ofReal_lt_top
  have hτ_le1 : τ_σ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine ⟨fun _ => realWithBotDist_extendedPseudoMetric, ⟨some 0, rfl⟩,
    by intro x hx; rcases hx with rfl; exact Or.inl rfl,
    by intro x hx; rcases hx with rfl | rfl <;> simp [dom, operator_identity],
    hτ_pos, hτ_fin, hdiamB, by rw [hdiamB]; exact hτ_pos, hdiamA, by rw [hdiamA]; exact hτ_le1⟩

/-! ### Proposition 3.15: Separation Threshold Given by Uniform Nullification Radius (CH03-P18-01..03) -/

/-- Proposition 3.15(i): Input distance strictly below `\underline{r}^N_{f, i, j}|_A` forces
output zero-distance. -/
theorem prop_3_15_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I)
    (_hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hlt : d i x y < uniformNullRadiusCompOn d f i j A) :
    d j (f.func x) (f.func y) = 0 := by
  have hpt : d i x y < pointwiseNullRadiusComp d f i j A x :=
    lt_of_lt_of_le hlt (iInf₂_le x hx)
  exact prop_3_11_radius d hd f A i j hAdom hx hy hpt

/-- Proposition 3.15(ii): Positive output separation implies input distance at least
`\underline{r}^N_{f, i, j}|_A`. -/
theorem prop_3_15_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hpos : 0 < d j (f.func x) (f.func y)) :
    uniformNullRadiusCompOn d f i j A ≤ d i x y := by
  by_contra hlt
  have hzero := prop_3_15_i d hd f A i j hAne hAdom hx hy (lt_of_not_ge hlt)
  exact (ne_of_gt hpos) hzero

/-- Proposition 3.15(iii): When `\underline{r}^N_{f, i, j}|_A < τ_N`, for every finite positive `α`
with `\underline{r}^N < α < τ_N`, there exist `x, y ∈ A` and finite positive `ε` such that
`d_i(x, y) < α` and `ε ≤ d_j(f(x), f(y))` (handling both finite and infinite output distance). -/
theorem prop_3_15_iii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (_hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N α : ENNReal)
    (_hAne : A.Nonempty) (_hAdom : A ⊆ dom f)
    (_hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hα_gt : uniformNullRadiusCompOn d f i j A < α) (hα_lt : α < τ_N) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  have hα_pos : 0 < α := lt_of_le_of_lt (zero_le _) hα_gt
  have hα_fin : α < ⊤ := lt_trans hα_lt hτ_fin
  have hex_y : ∃ y ∈ A, pointwiseNullRadiusComp d f i j A y < α := by
    by_contra hall
    push Not at hall
    have hle : α ≤ uniformNullRadiusCompOn d f i j A := le_iInf₂ hall
    exact not_lt_of_ge hle hα_gt
  rcases hex_y with ⟨y, hyA, hy_lt⟩
  have hnot_legal : ¬ IsLegalNullRadius (d i) (d j) f A y α := fun hleg =>
    not_le_of_gt hy_lt (le_sSup hleg)
  have hex_x : ∃ x ∈ A, d i x y < α ∧ d j (f.func x) (f.func y) ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hnot_legal ⟨hα_pos, hα_fin, hno⟩
  rcases hex_x with ⟨x, hxA, hdx, hdy_ne0⟩
  have hdy_pos : 0 < d j (f.func x) (f.func y) := pos_iff_ne_zero.mpr hdy_ne0
  by_cases htop : d j (f.func x) (f.func y) = ⊤
  · refine ⟨x, hxA, y, hyA, 1, zero_lt_one, ENNReal.one_lt_top, hdx, ?_⟩
    rw [htop]; exact le_top
  · refine ⟨x, hxA, y, hyA, d j (f.func x) (f.func y), hdy_pos, lt_top_iff_ne_top.mpr htop,
      hdx, le_rfl⟩

/-! ### Proposition 3.16: Fiber Inclusion and Covering-Number / Entropy Bounds (CH03-P19-01..03) -/

/-- Proposition 3.16(i): If `\underline{r}^N_{f, i, j}|_A ≥ τ_N`, every `τ_N`-ball centered at
`x ∈ A` is contained in `Fib_{f, j}(f(x) | A)`. -/
theorem prop_3_16_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (_hτ_pos : 0 < τ_N) (_hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ x ∈ A, ball (d i) x τ_N ∩ A ⊆ compFiberSingle d f j A (f.func x) := by
  intro x hx y ⟨hball, hy⟩
  refine ⟨hy, ?_⟩
  have hlt : d i y x < uniformNullRadiusCompOn d f i j A := lt_of_lt_of_le hball hge
  exact prop_3_15_i d hd f A i j hAne hAdom hy hx hlt

/-- Proposition 3.16(ii-a): For every `B ⊆ A` (including empty `B` and infinite covering number)
and every finite positive `ε`, `N_j(ε, f(B)) ≤ N_i(τ_N, B)`. -/
theorem prop_3_16_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ B ⊆ A, ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number (d j) ε (operator_image f B) ≤ covering_number (d i) τ_N B := by
  classical
  intro B hBA ε hε_pos _hε_fin
  rw [le_covering_number_iff]
  intro S hS
  have hnet_img : InternalEpsilonNet (d j) ε (operator_image f B) (S.image f.func) := by
    constructor
    · intro y hy
      rcases Finset.mem_image.mp (by simpa using hy) with ⟨s, hs, rfl⟩
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro y ⟨b, hbB, rfl⟩
      rcases hS.2 b hbB with ⟨s, hs, hdist⟩
      have hfib := prop_3_16_i d hd f A i j τ_N hAne hAdom hτ_pos hτ_fin hge
        s (hBA (hS.1 hs)) ⟨hdist, hBA hbB⟩
      refine ⟨f.func s, Finset.mem_image_of_mem f.func hs, ?_⟩
      rw [hfib.2]
      exact hε_pos
  calc
    covering_number (d j) ε (operator_image f B)
        ≤ ((S.image f.func).card : ENNReal) := covering_number_le_of_net hnet_img
    _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le

/-- Proposition 3.16(ii-b): For nonempty `B ⊆ A`, `E_{ε, j}(f(B)) ≤ E_{τ_N, i}(B)`. -/
theorem prop_3_16_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ B ⊆ A, B.Nonempty → ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      metric_entropy (d j) ε (operator_image f B) ≤ metric_entropy (d i) τ_N B := by
  intro B hBA _hBne ε hε_pos hε_fin
  exact metric_entropy_mono_of_covering_number_le
    (prop_3_16_ii_a d hd f A i j τ_N hAne hAdom hτ_pos hτ_fin hge B hBA ε hε_pos hε_fin)

/-! ### Counterexample after Proposition 3.16: Pointwise Positive Radius Cannot Replace Uniform Threshold (CH03-P20-01) -/

/-- Post-Proposition 3.16 counterexample (for any admissible `0 < a ≤ 1` with `2a < τ`):
on Counterexample 3.1's `stepOp` and `stepU`, `B = {-a, a} ⊆ stepU` satisfies
`N_1(τ, B) = 1 < 2 = N_1(1/2, f(B))`. -/
theorem post_prop_3_16_counterexample_for_a (τ : ENNReal) (a : ℝ)
    (ha_pos : 0 < a) (ha_le1 : a ≤ 1) (h2a_lt : ENNReal.ofReal (2 * a) < τ) :
    let B : Set RealWithBot := {some (-a), some a}
    B ⊆ stepU ∧
    covering_number realWithBotDist τ B = 1 ∧
    covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) = 2 ∧
    covering_number realWithBotDist τ B <
      covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) := by
  classical
  intro B
  have hτ_pos : 0 < τ := lt_of_le_of_lt (zero_le _) h2a_lt
  have hB_sub : B ⊆ stepU := by
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨-a, rfl, Or.inl ⟨by linarith, by linarith⟩⟩
    · exact ⟨a, rfl, Or.inr ⟨ha_pos, ha_le1⟩⟩
  have hB_ne : B.Nonempty := ⟨some a, Or.inr rfl⟩
  have hcovB : covering_number realWithBotDist τ B = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist τ B {some a} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc; exact Or.inr rfl
        · intro x hx
          refine ⟨some a, Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl
          · have hdist : realWithBotDist (some (-a)) (some a) = ENNReal.ofReal (2 * a) := by
              simp only [realWithBotDist]
              congr 1
              rw [show -a - a = -(2 * a) by ring, abs_neg, abs_of_pos (by linarith)]
            rw [hdist]
            exact h2a_lt
          · simp [realWithBotDist, hτ_pos]
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty realWithBotDist τ B hB_ne
  have himgB : operator_image stepOp B = {some 0, some 1} := by
    ext z
    simp only [operator_image, B, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · left; simp [stepOp, show -a < 0 by linarith]
      · right; simp [stepOp, not_lt.mpr (le_of_lt ha_pos)]
    · rintro (rfl | rfl)
      · exact ⟨some (-a), Or.inl rfl, by simp [stepOp, show -a < 0 by linarith]⟩
      · exact ⟨some a, Or.inr rfl, by simp [stepOp, not_lt.mpr (le_of_lt ha_pos)]⟩
  have hcovImg : covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) = 2 := by
    rw [himgB]
    have hne01 : (some (0 : ℝ) : RealWithBot) ≠ some 1 := by simp
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist (ENNReal.ofReal (1 / 2))
          ({some 0, some 1} : Set RealWithBot) {some 0, some 1} := by
        constructor
        · intro c hc
          simp only [Finset.coe_insert, Finset.coe_singleton] at hc
          exact hc
        · intro x hx
          rcases hx with rfl | rfl
          · refine ⟨some 0, by simp, ?_⟩
            simp only [realWithBotDist, sub_self, abs_zero, ENNReal.ofReal_zero]
            exact ENNReal.ofReal_pos.mpr (by norm_num)
          · refine ⟨some 1, by simp, ?_⟩
            simp only [realWithBotDist, sub_self, abs_zero, ENNReal.ofReal_zero]
            exact ENNReal.ofReal_pos.mpr (by norm_num)
      have hcard : ({some (0 : ℝ), some (1 : ℝ)} : Finset RealWithBot).card = 2 := by
        rw [Finset.card_pair hne01]
      simpa [hcard] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      have h0 : some (0 : ℝ) ∈ S := by
        rcases hS.2 (some 0) (Or.inl rfl) with ⟨c, hcS, hdist⟩
        rcases hS.1 hcS with rfl | rfl
        · exact hcS
        · exfalso
          simp only [realWithBotDist] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp hdist
          norm_num at hlt
      have h1 : some (1 : ℝ) ∈ S := by
        rcases hS.2 (some 1) (Or.inr rfl) with ⟨c, hcS, hdist⟩
        rcases hS.1 hcS with rfl | rfl
        · exfalso
          simp only [realWithBotDist] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp hdist
          norm_num at hlt
        · exact hcS
      have hsub : ({some (0 : ℝ), some (1 : ℝ)} : Finset RealWithBot) ⊆ S := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption
      have hcard : 2 ≤ S.card := by
        calc
          2 = ({some (0 : ℝ), some (1 : ℝ)} : Finset RealWithBot).card :=
              (Finset.card_pair hne01).symm
          _ ≤ S.card := Finset.card_le_card hsub
      exact_mod_cast hcard
  refine ⟨hB_sub, hcovB, hcovImg, ?_⟩
  rw [hcovB, hcovImg]
  exact ENNReal.one_lt_two

/-- Post-Proposition 3.16 counterexample on Counterexample 3.1's `stepOp` and `stepU`:
for every finite positive `τ`, there exists `0 < a ≤ 1` with `2a < τ` such that
`B = {-a, a} ⊆ stepU` satisfies `N_1(τ, B) = 1 < 2 = N_1(1/2, f(B))`. -/
theorem post_prop_3_16_counterexample (τ : ENNReal) (hτ_pos : 0 < τ) (hτ_fin : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      let B : Set RealWithBot := {some (-a), some a}
      B ⊆ stepU ∧
      covering_number realWithBotDist τ B = 1 ∧
      covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) = 2 ∧
      covering_number realWithBotDist τ B <
        covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) := by
  have hτ_real_pos : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ_pos) (ne_of_lt hτ_fin)
  let a : ℝ := min 1 (τ.toReal / 4)
  have ha_pos : 0 < a := lt_min zero_lt_one (by linarith)
  have ha_le1 : a ≤ 1 := min_le_left _ _
  have h2a_lt_real : 2 * a < τ.toReal := by
    have : a ≤ τ.toReal / 4 := min_le_right _ _
    linarith
  have h2a_lt : ENNReal.ofReal (2 * a) < τ := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hτ_fin)]
    exact (ENNReal.ofReal_lt_ofReal_iff hτ_real_pos).mpr h2a_lt_real
  exact ⟨a, ha_pos, ha_le1, h2a_lt, post_prop_3_16_counterexample_for_a τ a ha_pos ha_le1 h2a_lt⟩

/-! ### Corollary 3.17: Global Nullification Criterion on Small Input Domains (CH03-P21-01..02) -/

/-- Corollary 3.17 (equivalence): Under `diam_{d_i}(A) < τ_σ ≤ τ_N`,
`\underline{r}^N_{f, i, j}|_A ≥ τ_N` iff `∀ x, y ∈ A, d_j(f(x), f(y)) = 0`. -/
theorem cor_3_17_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_σ τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (_hτσ_pos : 0 < τ_σ) (_hτσ_fin : τ_σ < ⊤)
    (_hτN_pos : 0 < τ_N) (_hτN_fin : τ_N < ⊤)
    (hdiam : diamScaleFun d i A < τ_σ) (hτ_le : τ_σ ≤ τ_N) :
    τ_N ≤ uniformNullRadiusCompOn d f i j A ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro hge x hx y hy
    have hdx : d i x y < uniformNullRadiusCompOn d f i j A := by
      calc
        d i x y ≤ diamScaleFun d i A :=
            le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
        _ < τ_σ := hdiam
        _ ≤ τ_N := hτ_le
        _ ≤ uniformNullRadiusCompOn d f i j A := hge
    exact prop_3_15_i d hd f A i j hAne hAdom hx hy hdx
  · intro hconst
    have htop : uniformNullRadiusCompOn d f i j A = ⊤ := by
      apply top_unique
      apply le_iInf₂
      intro y hy
      rw [pointwiseNullRadius_eq_top_of_all_finite_pos]
      intro r hr0 hrt
      exact ⟨hr0, hrt, fun x hx _ => hconst x hx y hy⟩
    rw [htop]
    exact le_top

/-- Corollary 3.17 (covering number = 1): When the equivalent condition holds on nonempty `A`,
`N_j(ε, f(A)) = 1` for every finite positive `ε`. -/
theorem cor_3_17_covering_one {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_σ τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (hτσ_pos : 0 < τ_σ) (hτσ_fin : τ_σ < ⊤)
    (hτN_pos : 0 < τ_N) (hτN_fin : τ_N < ⊤)
    (hdiam : diamScaleFun d i A < τ_σ) (hτ_le : τ_σ ≤ τ_N)
    (hcond : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number (d j) ε (operator_image f A) = 1 := by
  have hconst := (cor_3_17_iff d hd f A i j τ_σ τ_N hAne hAdom
    hτσ_pos hτσ_fin hτN_pos hτN_fin hdiam hτ_le).mp hcond
  intro ε hε_pos _hε_fin
  rcases hAne with ⟨x₀, hx₀⟩
  have himg_ne : (operator_image f A).Nonempty := ⟨f.func x₀, ⟨x₀, hx₀, rfl⟩⟩
  apply le_antisymm
  · have hnet : InternalEpsilonNet (d j) ε (operator_image f A) {f.func x₀} := by
      constructor
      · intro c hc
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
        subst hc
        exact ⟨x₀, hx₀, rfl⟩
      · rintro y ⟨x, hxA, rfl⟩
        refine ⟨f.func x₀, Finset.mem_singleton_self _, ?_⟩
        rw [hconst x hxA x₀ hx₀]
        exact hε_pos
    simpa using covering_number_le_of_net hnet
  · exact one_le_covering_number_of_nonempty (d j) ε (operator_image f A) himg_ne

end Ch03
```

```lean filename=Ch03/MappingEntropyDiff.lean
/-
Formalization of Chapter 3 (Section 3.6: Mapping Entropy Difference)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.ScaleAndCovering

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.6: Mapping Entropy Difference (CH03-D08) -/

/-- Well-definedness premise for the mapping entropy difference `ΔE_{ε, J_in, J_out}(ϕ | U)`:
at least one of the input or output covering numbers is finite (excluding `∞ - ∞`). -/
def MappingEntropyDiffWellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J_in J_out : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Prop :=
  subfamily_covering_number d J_in ε U < ⊤ ∨
    subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤

/-- Mapping entropy difference `ΔE_{ε, J_in, J_out}(ϕ | U) := E_{ε, J_in}(U) - E_{ε, J_out}(ϕ(U))`,
defined only under the well-definedness premise `MappingEntropyDiffWellDefined`. -/
noncomputable def mappingEntropyDiff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J_in J_out : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (_hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U) : EReal :=
  subfamily_metric_entropy d J_in ε U -
    subfamily_metric_entropy d J_out ε (operator_image ϕ U)

/-- Same-subfamily abbreviation `ΔE_{ε, J}(ϕ | U)`. -/
noncomputable def mappingEntropyDiffSame {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d J J ε ϕ U) : EReal :=
  mappingEntropyDiff d J J ε ϕ U hwd

/-- Single-component channel abbreviation `ΔE_{ε, i, j}(ϕ | U)`. -/
noncomputable def mappingEntropyDiffComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (i j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U) : EReal :=
  mappingEntropyDiff d ({i} : Set I) ({j} : Set I) ε ϕ U hwd

/-- Same single-component abbreviation `ΔE_{ε, j}(ϕ | U)`. -/
noncomputable def mappingEntropyDiffCompSame {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U) : EReal :=
  mappingEntropyDiff d ({j} : Set I) ({j} : Set I) ε ϕ U hwd

theorem mappingEntropyDiffWellDefined_comp_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (i j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X) :
    MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U ↔
      covering_number (d i) ε U < ⊤ ∨
        covering_number (d j) ε (operator_image ϕ U) < ⊤ := by
  simp [MappingEntropyDiffWellDefined, subfamily_covering_number_singleton]

theorem mappingEntropyDiffComp_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (i j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U) :
    mappingEntropyDiffComp d i j ε ϕ U hwd =
      metric_entropy (d i) ε U - metric_entropy (d j) ε (operator_image ϕ U) := by
  simp [mappingEntropyDiffComp, mappingEntropyDiff, subfamily_metric_entropy_singleton]

/-- Explicit case evaluation of `mappingEntropyDiff` in all three well-defined regimes. -/
theorem mappingEntropyDiff_cases {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J_in J_out : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X) (hU : U.Nonempty) :
    (subfamily_covering_number d J_in ε U < ⊤ →
      subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤ →
      ∀ hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U,
      mappingEntropyDiff d J_in J_out ε ϕ U hwd =
        ↑(Real.logb 2 (subfamily_covering_number d J_in ε U).toReal -
          Real.logb 2 (subfamily_covering_number d J_out ε (operator_image ϕ U)).toReal)) ∧
    (subfamily_covering_number d J_in ε U = ⊤ →
      subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤ →
      ∀ hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U,
      mappingEntropyDiff d J_in J_out ε ϕ U hwd = ⊤) ∧
    (subfamily_covering_number d J_in ε U < ⊤ →
      subfamily_covering_number d J_out ε (operator_image ϕ U) = ⊤ →
      ∀ hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U,
      mappingEntropyDiff d J_in J_out ε ϕ U hwd = ⊥) := by
  have himg_ne : (operator_image ϕ U).Nonempty := hU.image ϕ.func
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 hwd
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_metric_entropy_eq_metric_entropy]
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU h1,
        metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne h2]
    rfl
  · intro h1 h2 hwd
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_metric_entropy_eq_metric_entropy]
    rw [(metric_entropy_eq_top_iff _ _ _).mpr h1,
        metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne h2]
    simp
  · intro h1 h2 hwd
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_metric_entropy_eq_metric_entropy]
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU h1,
        (metric_entropy_eq_top_iff _ _ _).mpr h2]
    simp

/-! ### Remark: Well-Definedness on Nonempty Finite Sets (CH03-P22-01) -/

/-- Helper: A finite set is covered by itself at any positive radius `ε`. -/
theorem covering_number_le_card_of_finite {X : Type} {bot : X}
    {d : X → X → ENNReal} (hd : ExtendedPseudoMetric X bot d)
    {ε : ENNReal} (hε_pos : 0 < ε) {S : Set X} (hS : S.Finite) :
    covering_number d ε S ≤ (hS.toFinset.card : ENNReal) := by
  have hnet : InternalEpsilonNet d ε S hS.toFinset := by
    constructor
    · intro c hc
      simpa using hc
    · intro x hx
      refine ⟨x, hS.mem_toFinset.mpr hx, ?_⟩
      rw [hd.dist_self x]
      exact hε_pos
  exact covering_number_le_of_net hnet

/-- Remark (CH03-P22-01): If `U ⊆ dom ϕ` is nonempty and finite, then for any nonempty
subfamilies `J_in, J_out` and any finite positive `ε`, both covering numbers are positive and
finite, both metric entropies are finite reals, and `ΔE` is well-defined. -/
theorem remark_finite_mapping_entropy_diff_well_defined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (J_in J_out : Set I) (ε : ENNReal)
    (hUne : U.Nonempty) (hUfin : U.Finite) (_hUdom : U ⊆ dom ϕ)
    (hJin : J_in.Nonempty) (hJout : J_out.Nonempty)
    (hε_pos : 0 < ε) (_hε_fin : ε < ⊤) :
    (1 ≤ subfamily_covering_number d J_in ε U ∧
      subfamily_covering_number d J_in ε U < ⊤) ∧
    (1 ≤ subfamily_covering_number d J_out ε (operator_image ϕ U) ∧
      subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤) ∧
    (∃ r₁ : ℝ, subfamily_metric_entropy d J_in ε U = ↑r₁) ∧
    (∃ r₂ : ℝ, subfamily_metric_entropy d J_out ε (operator_image ϕ U) = ↑r₂) ∧
    MappingEntropyDiffWellDefined d J_in J_out ε ϕ U := by
  have hd_in := subfamily_pseudometric_is_extended d J_in hJin hd
  have hd_out := subfamily_pseudometric_is_extended d J_out hJout hd
  have himg_ne : (operator_image ϕ U).Nonempty := hUne.image ϕ.func
  have himg_fin : (operator_image ϕ U).Finite := hUfin.image ϕ.func
  have h1_in : 1 ≤ subfamily_covering_number d J_in ε U :=
    one_le_covering_number_of_nonempty _ ε U hUne
  have hfin_in : subfamily_covering_number d J_in ε U < ⊤ :=
    lt_of_le_of_lt (covering_number_le_card_of_finite hd_in hε_pos hUfin)
      (ENNReal.natCast_lt_top _)
  have h1_out : 1 ≤ subfamily_covering_number d J_out ε (operator_image ϕ U) :=
    one_le_covering_number_of_nonempty _ ε (operator_image ϕ U) himg_ne
  have hfin_out : subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤ :=
    lt_of_le_of_lt (covering_number_le_card_of_finite hd_out hε_pos himg_fin)
      (ENNReal.natCast_lt_top _)
  refine ⟨⟨h1_in, hfin_in⟩, ⟨h1_out, hfin_out⟩, ?_, ?_, Or.inl hfin_in⟩
  · exact ⟨Real.logb 2 (subfamily_covering_number d J_in ε U).toReal,
      metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in⟩
  · exact ⟨Real.logb 2 (subfamily_covering_number d J_out ε (operator_image ϕ U)).toReal,
      metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hfin_out⟩

/-! ### Proposition 3.18: Component Partition and Mapping Entropy Difference (CH03-P23-01..03) -/

/-- Proposition 3.18(i): If `j ∈ I_const(ϕ | U)`, then `N_j(ε, ϕ(U)) = 1`, `E_{ε, j}(ϕ(U)) = 0`,
`ΔE_{ε, j}(ϕ | U)` is well-defined (even if input entropy is `+∞`), and equals `E_{ε, j}(U)`. -/
theorem prop_3_18_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (ε : ENNReal) (j : I)
    (hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (_hε_fin : ε < ⊤) (hj : j ∈ I_const d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) = 1 ∧
    metric_entropy (d j) ε (operator_image ϕ U) = 0 ∧
    MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U ∧
    ∀ hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U,
      mappingEntropyDiffCompSame d j ε ϕ U hwd = metric_entropy (d j) ε U := by
  rcases hUne with ⟨x₀, hx₀⟩
  have himg_ne : (operator_image ϕ U).Nonempty := ⟨ϕ.func x₀, ⟨x₀, hx₀, rfl⟩⟩
  have hcov : covering_number (d j) ε (operator_image ϕ U) = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (d j) ε (operator_image ϕ U) {ϕ.func x₀} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc
          exact ⟨x₀, hx₀, rfl⟩
        · rintro y ⟨x, hxU, rfl⟩
          refine ⟨ϕ.func x₀, Finset.mem_singleton_self _, ?_⟩
          rw [hj x hxU x₀ hx₀]
          exact hε_pos
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty (d j) ε (operator_image ϕ U) himg_ne
  have hent : metric_entropy (d j) ε (operator_image ϕ U) = 0 := by
    rw [metric_entropy, hcov, log2_ereal_one]
  have hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    right
    rw [hcov]
    exact ENNReal.one_lt_top
  refine ⟨hcov, hent, hwd, ?_⟩
  intro hwd'
  change mappingEntropyDiffComp d j j ε ϕ U hwd' = metric_entropy (d j) ε U
  rw [mappingEntropyDiffComp_eq, hent, sub_zero]

/-- Proposition 3.18(ii-a): If `j ∈ I_id(ϕ | U)`, then `N_j(ε, ϕ(U)) = N_j(ε, U)` and
`E_{ε, j}(ϕ(U)) = E_{ε, j}(U)`. -/
theorem prop_3_18_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (ε : ENNReal) (j : I)
    (_hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤) (hj : j ∈ I_id d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (operator_image ϕ U) = metric_entropy (d j) ε U := by
  classical
  have hiso := prop_3_1_iii d ϕ U j (hd j) hUdom hj
  have hcov : covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U := by
    apply le_antisymm
    · rw [le_covering_number_iff]
      intro S hS
      have hnet : InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) := by
        constructor
        · intro y hy
          rcases Finset.mem_image.mp (by simpa using hy) with ⟨s, hs, rfl⟩
          exact ⟨s, hS.1 hs, rfl⟩
        · rintro y ⟨x, hxU, rfl⟩
          rcases hS.2 x hxU with ⟨s, hs, hdist⟩
          refine ⟨ϕ.func s, Finset.mem_image_of_mem ϕ.func hs, ?_⟩
          rw [hiso x hxU s (hS.1 hs)]
          exact hdist
      calc
        covering_number (d j) ε (operator_image ϕ U)
            ≤ ((S.image ϕ.func).card : ENNReal) := covering_number_le_of_net hnet
        _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
    · rw [le_covering_number_iff]
      intro T hT
      let pick : X → X := fun t => if h : t ∈ operator_image ϕ U then Classical.choose h else bot
      have hnet : InternalEpsilonNet (d j) ε U (T.image pick) := by
        constructor
        · intro c hc
          rcases Finset.mem_image.mp (by simpa using hc) with ⟨t, ht, rfl⟩
          have htimg : t ∈ operator_image ϕ U := hT.1 ht
          simp only [pick, dif_pos htimg]
          exact (Classical.choose_spec htimg).1
        · intro x hxU
          rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, ht, hdist⟩
          have htimg : t ∈ operator_image ϕ U := hT.1 ht
          refine ⟨pick t, Finset.mem_image_of_mem pick ht, ?_⟩
          have hpick_mem : pick t ∈ U := by
            simp only [pick, dif_pos htimg]
            exact (Classical.choose_spec htimg).1
          have hpick_eq : ϕ.func (pick t) = t := by
            simp only [pick, dif_pos htimg]
            exact (Classical.choose_spec htimg).2
          rw [← hiso x hxU (pick t) hpick_mem, hpick_eq]
          exact hdist
      calc
        covering_number (d j) ε U
            ≤ ((T.image pick).card : ENNReal) := covering_number_le_of_net hnet
        _ ≤ (T.card : ENNReal) := by exact_mod_cast Finset.card_image_le
  exact ⟨hcov, by simp [metric_entropy, hcov]⟩

/-- Proposition 3.18(ii-b): If `j ∈ I_id(ϕ | U)` and `ΔE_{ε, j}(ϕ | U)` is well-defined
(excluding `∞ - ∞`), then `ΔE_{ε, j}(ϕ | U) = 0`. -/
theorem prop_3_18_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (ε : ENNReal) (j : I)
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) (hj : j ∈ I_id d ϕ U)
    (hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U) :
    mappingEntropyDiffCompSame d j ε ϕ U hwd = 0 := by
  have heq := prop_3_18_ii_a d hd ϕ U ε j hUne hUdom hε_pos hε_fin hj
  have hfin : covering_number (d j) ε U < ⊤ := by
    rw [mappingEntropyDiffWellDefined_comp_iff] at hwd
    rcases hwd with h1 | h2
    · exact h1
    · rwa [heq.1] at h2
  change mappingEntropyDiffComp d j j ε ϕ U hwd = 0
  rw [mappingEntropyDiffComp_eq, heq.2]
  rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin]
  exact_mod_cast sub_self (Real.logb 2 (covering_number (d j) ε U).toReal)

/-! ### Proposition 3.19: Single-Channel Lip Upper Bound and Entropy Difference Lower Bound (CH03-P24-01..02) -/

/-- Proposition 3.19 (net pushforward): A finite positive single-channel Lip constant `L` pushes
any internal `(ε / L)`-net of `U` to an internal `ε`-net of `ϕ(U)` without increasing cardinality. -/
theorem prop_3_19_net_pushforward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε L : ENNReal) (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤) (_hL_pos : 0 < L) (_hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y)
    {S : Finset X} (hS : InternalEpsilonNet (d i) (ε / L) U S) :
    letI := Classical.decEq X
    InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card := by
  classical
  refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro y hy
    rcases Finset.mem_image.mp (by simpa using hy) with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · rintro y ⟨x, hxU, rfl⟩
    rcases hS.2 x hxU with ⟨c, hc, hdist⟩
    refine ⟨ϕ.func c, Finset.mem_image_of_mem ϕ.func hc, ?_⟩
    have hmul : L * d i x c < ε := by
      rw [mul_comm]
      exact ENNReal.mul_lt_of_lt_div hdist
    exact lt_of_le_of_lt (hLip x hxU c (hS.1 hc)) hmul

/-- Proposition 3.19 (covering number upper bound): `N_j(ε, ϕ(U)) ≤ N_i(ε / L, U)`. -/
theorem prop_3_19_covering_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε L : ENNReal) (hε_pos : 0 < ε) (hε_fin : ε < ⊤) (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    covering_number (d j) ε (operator_image ϕ U) ≤ covering_number (d i) (ε / L) U := by
  classical
  rw [le_covering_number_iff]
  intro S hS
  have hpush := prop_3_19_net_pushforward d ϕ U i j ε L hε_pos hε_fin hL_pos hL_fin hLip hS
  calc
    covering_number (d j) ε (operator_image ϕ U)
        ≤ ((S.image ϕ.func).card : ENNReal) := covering_number_le_of_net hpush.1
    _ ≤ (S.card : ENNReal) := by exact_mod_cast hpush.2

/-- Proposition 3.19 (entropy difference lower bound): When `U` is totally bounded in `d_i`,
both covering numbers are finite, `ΔE_{ε, i, j}(ϕ | U)` is well-defined, and
`ΔE_{ε, i, j}(ϕ | U) ≥ E_{ε, i}(U) - E_{ε / L, i}(U)`. -/
theorem prop_3_19_entropy_diff_ge {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε L : ENNReal)
    (hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (hTB : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    covering_number (d i) ε U < ⊤ ∧
    covering_number (d j) ε (operator_image ϕ U) < ⊤ ∧
    MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U ∧
    ∀ hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U,
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        mappingEntropyDiffComp d i j ε ϕ U hwd := by
  have hcov_le := prop_3_19_covering_le d ϕ U i j ε L hε_pos hε_fin hL_pos hL_fin hLip
  have hεL_pos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hL_fin)
  have hεL_fin : ε / L < ⊤ := ENNReal.div_lt_top (ne_of_lt hε_fin) (ne_of_gt hL_pos)
  have hfin_in : covering_number (d i) ε U < ⊤ := hTB ε hε_pos hε_fin
  have hfin_inL : covering_number (d i) (ε / L) U < ⊤ := hTB (ε / L) hεL_pos hεL_fin
  have hfin_out : covering_number (d j) ε (operator_image ϕ U) < ⊤ :=
    lt_of_le_of_lt hcov_le hfin_inL
  have himg_ne : (operator_image ϕ U).Nonempty := hUne.image ϕ.func
  have hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    exact Or.inl hfin_in
  refine ⟨hfin_in, hfin_out, hwd, ?_⟩
  intro hwd'
  rw [mappingEntropyDiffComp_eq]
  have hent_le : metric_entropy (d j) ε (operator_image ϕ U) ≤ metric_entropy (d i) (ε / L) U :=
    metric_entropy_mono_of_covering_number_le hcov_le
  rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_inL,
      metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hfin_out] at hent_le ⊢
  rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in]
  have hreal_le : Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal ≤
      Real.logb 2 (covering_number (d i) (ε / L) U).toReal :=
    EReal.coe_le_coe_iff.mp hent_le
  change ((Real.logb 2 (covering_number (d i) ε U).toReal -
      Real.logb 2 (covering_number (d i) (ε / L) U).toReal : ℝ) : EReal) ≤
    ((Real.logb 2 (covering_number (d i) ε U).toReal -
      Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal : ℝ) : EReal)
  exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left hreal_le _)

/-! ### Proposition 3.20: co-Lip Constant and Entropy Difference Upper Bound (CH03-P25-01..02) -/

/-- Proposition 3.20 (net pullback): A finite positive co-Lip entry `K_{i → j}` pulls back any
internal `ε`-net `T` of `ϕ(U)` to an internal `(ε / K_{i → j})`-net `S` of `U` with `|S| ≤ |T|`. -/
theorem prop_3_20_net_pullback {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε : ENNReal) (K : I → I → ENNReal)
    (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤)
    {T : Finset X} (hT : InternalEpsilonNet (d j) ε (operator_image ϕ U) T) :
    ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
  classical
  let pick : X → X := fun t => if h : t ∈ operator_image ϕ U then Classical.choose h else bot
  refine ⟨T.image pick, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro c hc
    rcases Finset.mem_image.mp (by simpa using hc) with ⟨t, ht, rfl⟩
    have htimg : t ∈ operator_image ϕ U := hT.1 ht
    simp only [pick, dif_pos htimg]
    exact (Classical.choose_spec htimg).1
  · intro x hxU
    rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, ht, hdist⟩
    have htimg : t ∈ operator_image ϕ U := hT.1 ht
    refine ⟨pick t, Finset.mem_image_of_mem pick ht, ?_⟩
    have hpick_mem : pick t ∈ U := by
      simp only [pick, dif_pos htimg]
      exact (Classical.choose_spec htimg).1
    have hpick_eq : ϕ.func (pick t) = t := by
      simp only [pick, dif_pos htimg]
      exact (Classical.choose_spec htimg).2
    have hcolip : K i j * d i x (pick t) ≤ d j (ϕ.func x) (ϕ.func (pick t)) := by
      calc
        K i j * d i x (pick t)
            ≤ ∑ k : I, K k j * d k x (pick t) :=
              Finset.single_le_sum (f := fun k => K k j * d k x (pick t))
                (fun _ _ => zero_le _) (Finset.mem_univ i)
        _ ≤ d j (ϕ.func x) (ϕ.func (pick t)) := hK.2.2 x hxU (pick t) hpick_mem j
    have hlt : d i x (pick t) * K i j < ε := by
      rw [mul_comm]
      exact lt_of_le_of_lt hcolip (by rw [hpick_eq]; exact hdist)
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hK_pos)) (Or.inl (ne_of_lt hK_fin))).mpr hlt

/-- Proposition 3.20 (covering number lower bound): `N_i(ε / K_{i → j}, U) ≤ N_j(ε, ϕ(U))`. -/
theorem prop_3_20_covering_ge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε : ENNReal) (K : I → I → ENNReal)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (operator_image ϕ U) := by
  rw [le_covering_number_iff]
  intro T hT
  rcases prop_3_20_net_pullback d ϕ U i j ε K hε_pos hε_fin hK hK_pos hK_fin hT with
    ⟨S, hSnet, hScard⟩
  calc
    covering_number (d i) (ε / K i j) U
        ≤ (S.card : ENNReal) := covering_number_le_of_net hSnet
    _ ≤ (T.card : ENNReal) := by exact_mod_cast hScard

/-- Proposition 3.20 (entropy difference upper bound): When `U` is totally bounded in `d_i`
(allowing output entropy to be `+∞`), `ΔE_{ε, i, j}(ϕ | U)` is well-defined and satisfies
`ΔE_{ε, i, j}(ϕ | U) ≤ E_{ε, i}(U) - E_{ε / K_{i → j}, i}(U)`. -/
theorem prop_3_20_entropy_diff_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε : ENNReal) (K : I → I → ENNReal)
    (hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (hTB : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U ∧
    ∀ hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U,
      mappingEntropyDiffComp d i j ε ϕ U hwd ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hcov_ge := prop_3_20_covering_ge d ϕ U i j ε K hε_pos hε_fin hK hK_pos hK_fin
  have hεK_pos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hK_fin)
  have hεK_fin : ε / K i j < ⊤ := ENNReal.div_lt_top (ne_of_lt hε_fin) (ne_of_gt hK_pos)
  have hfin_in : covering_number (d i) ε U < ⊤ := hTB ε hε_pos hε_fin
  have hfin_inK : covering_number (d i) (ε / K i j) U < ⊤ := hTB (ε / K i j) hεK_pos hεK_fin
  have himg_ne : (operator_image ϕ U).Nonempty := hUne.image ϕ.func
  have hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    exact Or.inl hfin_in
  refine ⟨hwd, ?_⟩
  intro hwd'
  rw [mappingEntropyDiffComp_eq]
  by_cases htop : covering_number (d j) ε (operator_image ϕ U) = ⊤
  · rw [(metric_entropy_eq_top_iff _ _ _).mpr htop,
        metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in]
    simp
  · have hfin_out : covering_number (d j) ε (operator_image ϕ U) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hent_le : metric_entropy (d i) (ε / K i j) U ≤
        metric_entropy (d j) ε (operator_image ϕ U) :=
      metric_entropy_mono_of_covering_number_le hcov_ge
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_inK,
        metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hfin_out] at hent_le ⊢
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in]
    have hreal_le : Real.logb 2 (covering_number (d i) (ε / K i j) U).toReal ≤
        Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal :=
      EReal.coe_le_coe_iff.mp hent_le
    change ((Real.logb 2 (covering_number (d i) ε U).toReal -
        Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal : ℝ) : EReal) ≤
      ((Real.logb 2 (covering_number (d i) ε U).toReal -
        Real.logb 2 (covering_number (d i) (ε / K i j) U).toReal : ℝ) : EReal)
    exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left hreal_le _)

end Ch03
```

```lean filename=Ch03/Exercises1to3.lean
/-
Formalization of Chapter 3 (Section 3.7: Exercises 3.1, 3.2, and 3.3)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.MappingEntropyDiff

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Shared Pseudometric `d(x, y) = ||x| - |y||` on `ℝ ⊔ {⊥}` for Exercises 3.1 & 3.3 -/

/-- Single-component extended pseudometric `d(x, y) = ||x| - |y||` on `ℝ ⊔ {⊥}` with `⊥` isolated. -/
noncomputable def absDiffDist : Unit → RealWithBot → RealWithBot → ENNReal
  | _, none, none => 0
  | _, some _, none => ⊤
  | _, none, some _ => ⊤
  | _, some x, some y => ENNReal.ofReal |(|x| - |y|)|

theorem absDiffDist_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric RealWithBot none (absDiffDist u) := by
  intro u
  refine
    { nonabsorbing := ⟨some 0, by simp⟩
      dist_self := by
        intro x; cases x <;> simp [absDiffDist]
      symm := by
        intro x y; cases x <;> cases y <;> simp [absDiffDist, abs_sub_comm]
      triangle := by
        intro x y z
        cases x <;> cases y <;> cases z <;> simp [absDiffDist]
        rename_i a b c
        calc
          ENNReal.ofReal |(|a| - |c|)| ≤ ENNReal.ofReal (|(|a| - |b|)| + |(|b| - |c|)|) :=
            ENNReal.ofReal_le_ofReal (abs_sub_le |a| |b| |c|)
          _ = ENNReal.ofReal |(|a| - |b|)| + ENNReal.ofReal |(|b| - |c|)| :=
            ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      isolate_bot := by
        intro x hx
        cases x
        · exact (hx rfl).elim
        · rfl }

/-! ### Exercise 3.1: Computational Fibers and Self-Composition (CH03-P26-01..03) -/

/-- Affine operator `ϕ(x) = 2x - 1` on `ℝ`, `ϕ(⊥) = ⊥`. -/
def ex31Op : Operator RealWithBot none where
  func
    | none => none
    | some x => some (2 * x - 1)
  preserves_bot := rfl

/-- Domain `U = {0, 1} ⊂ ℝ ⊔ {⊥}` for Exercise 3.1. -/
def ex31U : Set RealWithBot := {some 0, some 1}

/-- Exercise 3.1(i-a) (CH03-P26-01): Legality of `absDiffDist` and `ex31Op`, fiber of `ϕ(0)`,
and component classification `() ∈ I_const(ϕ | U)`. -/
theorem exercise_3_1_i_a :
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot none (absDiffDist u)) ∧
    ex31U ⊆ dom ex31Op ∧
    compFiberSingle absDiffDist ex31Op () ex31U (ex31Op.func (some 0)) = ex31U ∧
    () ∈ I_const absDiffDist ex31Op ex31U ∧
    () ∉ I_id absDiffDist ex31Op ex31U ∧
    () ∉ I_act absDiffDist ex31Op ex31U := by
  have hdom : ex31U ⊆ dom ex31Op := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ex31Op]
  have hconst : () ∈ I_const absDiffDist ex31Op ex31U := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [ex31Op, absDiffDist]
  have hfib : compFiberSingle absDiffDist ex31Op () ex31U (ex31Op.func (some 0)) = ex31U := by
    ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hconst x hx (some 0) (Or.inl rfl)
  refine ⟨absDiffDist_extendedPseudoMetric, hdom, hfib, hconst,
    fun hid => hid.1 hconst, fun hact => hact (Or.inl hconst)⟩

/-- Exercise 3.1(i-b) (CH03-P26-02): Fiber of `ϕ²(0)` on the same `U = {0, 1}` is `{0}`,
and `() ∈ I_act(ϕ² | U)`. -/
theorem exercise_3_1_i_b :
    let ϕ2 := operator_compose ex31Op ex31Op
    ex31U ⊆ dom ϕ2 ∧
    compFiberSingle absDiffDist ϕ2 () ex31U (ϕ2.func (some 0)) = {some 0} ∧
    () ∈ I_act absDiffDist ϕ2 ex31U ∧
    () ∉ I_const absDiffDist ϕ2 ex31U ∧
    () ∉ I_id absDiffDist ϕ2 ex31U := by
  intro ϕ2
  have hdom : ex31U ⊆ dom ϕ2 := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ϕ2, operator_compose, ex31Op]
  have hd01 : absDiffDist () (ϕ2.func (some 1)) (ϕ2.func (some 0)) = ENNReal.ofReal 2 := by
    simp only [ϕ2, operator_compose, Function.comp_apply, ex31Op, absDiffDist]
    norm_num
  have hnot_const : () ∉ I_const absDiffDist ϕ2 ex31U := by
    intro hc
    have h := hc (some 1) (Or.inr rfl) (some 0) (Or.inl rfl)
    rw [hd01] at h
    norm_num at h
  have hnot_id : () ∉ I_id absDiffDist ϕ2 ex31U := by
    intro hid
    have h := hid.2 (some 0) (Or.inl rfl)
    simp only [ϕ2, operator_compose, Function.comp_apply, ex31Op, absDiffDist] at h
    norm_num at h
  have hfib : compFiberSingle absDiffDist ϕ2 () ex31U (ϕ2.func (some 0)) = {some 0} := by
    ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h0⟩
      rcases hx with rfl | rfl
      · rfl
      · rw [hd01] at h0
        norm_num at h0
    · rintro rfl
      exact ⟨Or.inl rfl, (absDiffDist_extendedPseudoMetric ()).dist_self _⟩
  have hact : () ∈ I_act absDiffDist ϕ2 ex31U := by
    intro h
    rcases h with hc | hi
    · exact hnot_const hc
    · exact hnot_id hi
  exact ⟨hdom, hfib, hact, hnot_const, hnot_id⟩

/-- Exercise 3.1(ii) (CH03-P26-03): If `ψ` takes the same real value `c` on `U = {0, 1}`, then
`ψ²(0) = ψ²(1)`. Either `some c ∈ dom ψ` (in which case `U ⊆ dom ψ²`, `0` and `1` stay in the
same fiber `U`, and `() ∈ I_const(ψ² | U)`), or `some c ∉ dom ψ` (in which case `U ⊈ dom ψ²`
and `U ∩ dom ψ² = ∅`, so the restricted domain condition fails). -/
theorem exercise_3_1_ii (ψ : Operator RealWithBot none) (c : ℝ)
    (h0 : ψ.func (some 0) = some c) (h1 : ψ.func (some 1) = some c) :
    let ψ2 := operator_compose ψ ψ
    ψ2.func (some 0) = ψ2.func (some 1) ∧
    (some c ∈ dom ψ →
      ex31U ⊆ dom ψ2 ∧
      compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 0)) = ex31U ∧
      compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 0)) =
        compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 1)) ∧
      () ∈ I_const absDiffDist ψ2 ex31U) ∧
    (some c ∉ dom ψ →
      ¬ (ex31U ⊆ dom ψ2) ∧ ex31U ∩ dom ψ2 = ∅) := by
  intro ψ2
  have heq : ψ2.func (some 0) = ψ2.func (some 1) := by
    change ψ.func (ψ.func (some 0)) = ψ.func (ψ.func (some 1))
    rw [h0, h1]
  refine ⟨heq, ?_, ?_⟩
  · intro hc_dom
    have hdom : ex31U ⊆ dom ψ2 := by
      intro x hx
      rcases hx with rfl | rfl
      · change ψ.func (ψ.func (some 0)) ≠ none
        rw [h0]; exact hc_dom
      · change ψ.func (ψ.func (some 1)) ≠ none
        rw [h1]; exact hc_dom
    have hconst : () ∈ I_const absDiffDist ψ2 ex31U := by
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (absDiffDist_extendedPseudoMetric ()).dist_self _
      · rw [heq]; exact (absDiffDist_extendedPseudoMetric ()).dist_self _
      · rw [heq]; exact (absDiffDist_extendedPseudoMetric ()).dist_self _
      · exact (absDiffDist_extendedPseudoMetric ()).dist_self _
    have hfib : compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 0)) = ex31U := by
      ext x
      simp only [compFiberSingle, Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro hx
      exact hconst x hx (some 0) (Or.inl rfl)
    refine ⟨hdom, hfib, by rw [heq], hconst⟩
  · intro hc_ndom
    have hbot : ψ.func (some c) = none := by
      by_contra hne
      exact hc_ndom hne
    have hinter : ex31U ∩ dom ψ2 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hdx
      rcases hx with rfl | rfl
      · apply hdx
        change ψ.func (ψ.func (some 0)) = none
        rw [h0, hbot]
      · apply hdx
        change ψ.func (ψ.func (some 1)) = none
        rw [h1, hbot]
    refine ⟨?_, hinter⟩
    intro hsub
    have hmem : some (0 : ℝ) ∈ ex31U ∩ dom ψ2 := ⟨Or.inl rfl, hsub (Or.inl rfl)⟩
    rw [hinter] at hmem
    exact hmem

/-! ### Exercise 3.2: Nullification Radius and Distance Gap (CH03-P27-01..02) -/

/-- Exercise 3.2(i) (CH03-P27-01): With a positive co-Lip entry `K_{i → j} > 0` (not assumed
finite) and positive pointwise nullification radius `r^N_{ϕ, i, j}(y | U) > 0`, no input point
`x ∈ U` has distance `d_i(x, y) ∈ (0, r^N_{ϕ, i, j}(y | U))`. -/
theorem exercise_3_2_i {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I) (y : X)
    (_hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j)
    (hy : y ∈ U) (_hr_pos : 0 < pointwiseNullRadiusComp d ϕ i j U y) :
    ∀ x ∈ U, d i x y ∉ Set.Ioo 0 (pointwiseNullRadiusComp d ϕ i j U y) := by
  intro x hx ⟨hpos, hlt⟩
  have hlt_symm : d i y x < pointwiseNullRadiusComp d ϕ i j U y := by
    rw [(hd i).symm]; exact hlt
  have hout0 : d j (ϕ.func y) (ϕ.func x) = 0 :=
    prop_3_11_radius d hd ϕ U i j hUdom hy hx hlt_symm
  have hin0 : d i y x = 0 :=
    positive_colip_entry_reflects_zero d ϕ U K i j hK hK_pos y hy x hx hout0
  rw [(hd i).symm] at hin0
  exact (ne_of_gt hpos) hin0

/-- Exercise 3.2(ii) (CH03-P27-02): If `\underline{r}^N_{ϕ, i, j}|_U > 0` under `K_{i → j} > 0`,
then for all `x, y ∈ U`, `d_i(x, y) ∈ {0} ⊔ [\underline{r}^N_{ϕ, i, j}|_U, +∞]`. -/
theorem exercise_3_2_ii {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j)
    (hr_pos : 0 < uniformNullRadiusCompOn d ϕ i j U) :
    Disjoint ({0} : Set ENNReal) (Set.Ici (uniformNullRadiusCompOn d ϕ i j U)) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      d i x y ∈ ({0} : Set ENNReal) ∪ Set.Ici (uniformNullRadiusCompOn d ϕ i j U) := by
  constructor
  · rw [Set.disjoint_left]
    intro a ha0 hage
    simp only [Set.mem_singleton_iff] at ha0
    subst ha0
    exact not_lt_of_ge hage hr_pos
  · intro x hx y hy
    by_cases h0 : d i x y = 0
    · exact Or.inl h0
    · right
      have hpos : 0 < d i x y := pos_iff_ne_zero.mpr h0
      have hr_y : uniformNullRadiusCompOn d ϕ i j U ≤ pointwiseNullRadiusComp d ϕ i j U y :=
        iInf₂_le y hy
      have hgap := exercise_3_2_i d hd ϕ U K i j y hUne hUdom hK hK_pos hy
        (lt_of_lt_of_le hr_pos hr_y) x hx
      by_contra hlt
      have hlt_y : d i x y < pointwiseNullRadiusComp d ϕ i j U y :=
        lt_of_lt_of_le (lt_of_not_ge hlt) hr_y
      exact hgap ⟨hpos, hlt_y⟩

/-! ### Exercise 3.3: Fibers and Entropy Difference under Translation (CH03-P28-01..02) -/

/-- Translation operator `ϕ(x) = x + 1` on `ℝ`, `ϕ(⊥) = ⊥`. -/
def ex33Op : Operator RealWithBot none where
  func
    | none => none
    | some x => some (x + 1)
  preserves_bot := rfl

/-- Four-point domain `U = {-3, -2, 0, 2} ⊂ ℝ ⊔ {⊥}` for Exercise 3.3. -/
def ex33U : Set RealWithBot := {some (-3), some (-2), some 0, some 2}

/-- Exercise 3.3(i) (CH03-P28-01): Complete fiber partitions of `id` and `ϕ(x) = x + 1`
on `U = {-3, -2, 0, 2}` under `d_i(x, y) = ||x| - |y||`. -/
theorem exercise_3_3_i :
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot none (absDiffDist u)) ∧
    ex33U ⊆ dom (@operator_identity RealWithBot none) ∧
    ex33U ⊆ dom ex33Op ∧
    compFiberFamily absDiffDist (@operator_identity RealWithBot none) Set.univ ex33U =
      {{some (-3)}, {some (-2), some 2}, {some 0}} ∧
    compFiberFamily absDiffDist ex33Op Set.univ ex33U =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  have hdom_id : ex33U ⊆ dom (@operator_identity RealWithBot none) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [dom, operator_identity]
  have hdom_op : ex33U ⊆ dom ex33Op := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [dom, ex33Op]
  have hfib_univ : ∀ (ϕ : Operator RealWithBot none) (y : RealWithBot),
      compFiber absDiffDist ϕ Set.univ ex33U y = compFiberSingle absDiffDist ϕ () ex33U y := by
    intro ϕ y
    ext x
    simp only [compFiber, compFiberSingle, Set.mem_setOf_eq,
      subfamily_pseudometric_eq_zero_iff, Set.mem_univ, forall_true_left]
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, h ()⟩, fun ⟨hx, h⟩ => ⟨hx, fun u => by cases u; exact h⟩⟩
  have hid_m3 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some (-3)) = {some (-3)} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      · norm_num [absDiffDist] at h0
      · norm_num [absDiffDist] at h0
      · norm_num [absDiffDist] at h0
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num [absDiffDist]⟩
  have hid_m2 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some (-2)) = {some (-2), some 2} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [absDiffDist] at h0
      · exact Or.inl rfl
      · norm_num [absDiffDist] at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [absDiffDist]⟩
  have hid_2 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some 2) = {some (-2), some 2} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [absDiffDist] at h0
      · exact Or.inl rfl
      · norm_num [absDiffDist] at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [absDiffDist]⟩
  have hid_0 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some 0) = {some 0} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [absDiffDist] at h0
      · norm_num [absDiffDist] at h0
      · rfl
      · norm_num [absDiffDist] at h0
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [absDiffDist]⟩
  have hpart_id : compFiberFamily absDiffDist (@operator_identity RealWithBot none) Set.univ ex33U =
      {{some (-3)}, {some (-2), some 2}, {some 0}} := by
    ext F
    simp only [compFiberFamily, operator_image, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [hfib_univ]
      rcases hx with rfl | rfl | rfl | rfl
      · left; exact hid_m3
      · right; left; exact hid_m2
      · right; right; exact hid_0
      · right; left; exact hid_2
    · rintro (rfl | rfl | rfl)
      · exact ⟨some (-3), ⟨some (-3), Or.inl rfl, rfl⟩, by rw [hfib_univ]; exact hid_m3⟩
      · exact ⟨some (-2), ⟨some (-2), Or.inr (Or.inl rfl), rfl⟩, by rw [hfib_univ]; exact hid_m2⟩
      · exact ⟨some 0, ⟨some 0, Or.inr (Or.inr (Or.inl rfl)), rfl⟩, by rw [hfib_univ]; exact hid_0⟩
  have hop_m2 : compFiberSingle absDiffDist ex33Op () ex33U (some (-2)) = {some (-3)} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num [ex33Op, absDiffDist]⟩
  have hop_m1 : compFiberSingle absDiffDist ex33Op () ex33U (some (-1)) = {some (-2), some 0} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [ex33Op, absDiffDist] at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num [ex33Op, absDiffDist] at h0
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [ex33Op, absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex33Op, absDiffDist]⟩
  have hop_1 : compFiberSingle absDiffDist ex33Op () ex33U (some 1) = {some (-2), some 0} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [ex33Op, absDiffDist] at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num [ex33Op, absDiffDist] at h0
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [ex33Op, absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex33Op, absDiffDist]⟩
  have hop_3 : compFiberSingle absDiffDist ex33Op () ex33U (some 3) = {some 2} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [ex33Op, absDiffDist]⟩
  have hpart_op : compFiberFamily absDiffDist ex33Op Set.univ ex33U =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
    ext F
    simp only [compFiberFamily, operator_image, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [hfib_univ]
      rcases hx with rfl | rfl | rfl | rfl
      · left; simpa [ex33Op, show (-3 : ℝ) + 1 = -2 by norm_num] using hop_m2
      · right; left; simpa [ex33Op, show (-2 : ℝ) + 1 = -1 by norm_num] using hop_m1
      · right; left; simpa [ex33Op, show (0 : ℝ) + 1 = 1 by norm_num] using hop_1
      · right; right; simpa [ex33Op, show (2 : ℝ) + 1 = 3 by norm_num] using hop_3
    · rintro (rfl | rfl | rfl)
      · refine ⟨ex33Op.func (some (-3)), ⟨some (-3), Or.inl rfl, rfl⟩, ?_⟩
        rw [hfib_univ]; simpa [ex33Op, show (-3 : ℝ) + 1 = -2 by norm_num] using hop_m2
      · refine ⟨ex33Op.func (some (-2)), ⟨some (-2), Or.inr (Or.inl rfl), rfl⟩, ?_⟩
        rw [hfib_univ]; simpa [ex33Op, show (-2 : ℝ) + 1 = -1 by norm_num] using hop_m1
      · refine ⟨ex33Op.func (some 2), ⟨some 2, Or.inr (Or.inr (Or.inr rfl)), rfl⟩, ?_⟩
        rw [hfib_univ]; simpa [ex33Op, show (2 : ℝ) + 1 = 3 by norm_num] using hop_3
  exact ⟨absDiffDist_extendedPseudoMetric, hdom_id, hdom_op, hpart_id, hpart_op⟩

/-- Exercise 3.3(ii) (CH03-P28-02): At `ε = 3/2`, `N_i(3/2, U) = 2`, `N_i(3/2, ϕ(U)) = 1`,
`ΔE_{3/2, i}(ϕ | U)` is well-defined and equals `1`. -/
theorem exercise_3_3_ii :
    let ε : ENNReal := ENNReal.ofReal (3 / 2)
    0 < ε ∧ ε < ⊤ ∧
    covering_number (absDiffDist ()) ε ex33U = 2 ∧
    covering_number (absDiffDist ()) ε (operator_image ex33Op ex33U) = 1 ∧
    MappingEntropyDiffWellDefined absDiffDist {()} {()} ε ex33Op ex33U ∧
    ∀ hwd : MappingEntropyDiffWellDefined absDiffDist {()} {()} ε ex33Op ex33U,
      mappingEntropyDiffCompSame absDiffDist () ε ex33Op ex33U hwd = 1 := by
  classical
  intro ε
  have hε_pos : 0 < ε := ENNReal.ofReal_pos.mpr (by norm_num)
  have hε_fin : ε < ⊤ := ENNReal.ofReal_lt_top
  have hcovU : covering_number (absDiffDist ()) ε ex33U = 2 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (absDiffDist ()) ε ex33U {some 0, some 2} := by
        constructor
        · intro c hc
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hc
          rcases hc with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        · intro x hx
          rcases hx with rfl | rfl | rfl | rfl
          · refine ⟨some 2, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
          · refine ⟨some 2, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
          · refine ⟨some 0, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
          · refine ⟨some 2, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
      have hcard : ({some (0 : ℝ), some (2 : ℝ)} : Finset RealWithBot).card = 2 := by
        rw [Finset.card_pair (by simp)]
      simpa [hcard] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      have h0_mem : some (0 : ℝ) ∈ S := by
        rcases hS.2 (some 0) (Or.inr (Or.inr (Or.inl rfl))) with ⟨c, hcS, hdist⟩
        rcases hS.1 hcS with rfl | rfl | rfl | rfl
        · exfalso
          simp only [absDiffDist, ε] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist
          norm_num at hlt
        · exfalso
          simp only [absDiffDist, ε] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist
          norm_num at hlt
        · exact hcS
        · exfalso
          simp only [absDiffDist, ε] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist
          norm_num at hlt
      rcases hS.2 (some 2) (Or.inr (Or.inr (Or.inr rfl))) with ⟨c₂, hc₂S, hdist₂⟩
      have hc₂_ne : c₂ ≠ some (0 : ℝ) := by
        rintro rfl
        simp only [absDiffDist, ε] at hdist₂
        have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist₂
        norm_num at hlt
      have hsub : ({some (0 : ℝ), c₂} : Finset RealWithBot) ⊆ S := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption
      have hcard : 2 ≤ S.card := by
        calc
          2 = ({some (0 : ℝ), c₂} : Finset RealWithBot).card :=
              (Finset.card_pair hc₂_ne.symm).symm
          _ ≤ S.card := Finset.card_le_card hsub
      exact_mod_cast hcard
  have hcovImg : covering_number (absDiffDist ()) ε (operator_image ex33Op ex33U) = 1 := by
    have himg_ne : (operator_image ex33Op ex33U).Nonempty :=
      ⟨ex33Op.func (some (-3)), ⟨some (-3), Or.inl rfl, rfl⟩⟩
    apply le_antisymm
    · have hnet : InternalEpsilonNet (absDiffDist ()) ε (operator_image ex33Op ex33U)
          {ex33Op.func (some (-3))} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc
          exact ⟨some (-3), Or.inl rfl, rfl⟩
        · rintro y ⟨x, hx, rfl⟩
          refine ⟨ex33Op.func (some (-3)), Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl <;>
            (simp only [ex33Op, absDiffDist, ε]
             apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
             norm_num)
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty _ _ _ himg_ne
  have hwd : MappingEntropyDiffWellDefined absDiffDist {()} {()} ε ex33Op ex33U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    left
    rw [hcovU]
    exact ENNReal.ofNat_lt_top
  refine ⟨hε_pos, hε_fin, hcovU, hcovImg, hwd, ?_⟩
  intro hwd'
  change mappingEntropyDiffComp absDiffDist () () ε ex33Op ex33U hwd' = 1
  rw [mappingEntropyDiffComp_eq, metric_entropy, metric_entropy, hcovU, hcovImg,
      log2_ereal_two, log2_ereal_one, sub_zero]

end Ch03
```

```lean filename=Ch03/Exercises4to5.lean
/-
Formalization of Chapter 3 (Section 3.7: Exercises 3.4 and 3.5)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.MappingEntropyDiff

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Shared Single-Component Family on `ℝ ⊔ {⊥}` -/

/-- Single-component gauge family on `ℝ ⊔ {⊥}` given by the usual Euclidean distance. -/
noncomputable def realWithBotDistFamily : Unit → RealWithBot → RealWithBot → ENNReal :=
  fun _ => realWithBotDist

theorem realWithBotDistFamily_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric RealWithBot none (realWithBotDistFamily u) :=
  fun _ => realWithBotDist_extendedPseudoMetric

/-- Closed real interval `[a, b]` embedded in `ℝ ⊔ {⊥}`. -/
def realIcc (a b : ℝ) : Set RealWithBot :=
  { z | ∃ x : ℝ, z = some x ∧ a ≤ x ∧ x ≤ b }

theorem diamScaleFun_realIcc {a b : ℝ} (hab : a ≤ b) :
    diamScaleFun realWithBotDistFamily () (realIcc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup₂_le
    rintro z₁ ⟨x, rfl, hxa, hxb⟩
    apply iSup₂_le
    rintro z₂ ⟨y, rfl, hya, hyb⟩
    simp only [realWithBotDistFamily, realWithBotDist]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;> linarith
  · apply le_iSup₂_of_le (some a) ⟨a, rfl, le_rfl, hab⟩
    apply le_iSup₂_of_le (some b) ⟨b, rfl, hab, le_rfl⟩
    simp only [realWithBotDistFamily, realWithBotDist]
    rw [show a - b = -(b - a) by ring, abs_neg, abs_of_nonneg (sub_nonneg.mpr hab)]

/-! ### Exercise 3.4: Threshold Classification under Changing Input Domains (CH03-P29-01..05) -/

/-- Floor operator `f(x) = ⌊x⌋` on `ℝ`, `f(⊥) = ⊥`. -/
noncomputable def floorOp : Operator RealWithBot none where
  func
    | none => none
    | some x => some (⌊x⌋ : ℝ)
  preserves_bot := rfl

def ex34D1 : Set RealWithBot := realIcc 0 (1 / 2)
def ex34D2 : Set RealWithBot := realIcc (9 / 10) (11 / 10)
def ex34D3 : Set RealWithBot := {some 0, some 2}
def ex34D4 : Set RealWithBot := realIcc 0 2

/-- Helper: If `D` contains `[c, 1]` for some `c < 1`, then `r^N_{floorOp}(1 | D) = 0`. -/
theorem floorOp_pointwise_zero_at_one {D : Set RealWithBot} {c : ℝ}
    (hc : c < 1) (hsub : ∀ x : ℝ, c ≤ x → x ≤ 1 → some x ∈ D) :
    pointwiseNullRadiusComp realWithBotDistFamily floorOp () () D (some 1) = 0 := by
  apply pointwiseNullRadius_eq_zero_of_no_legal
  rintro r ⟨hr0, hrt, hrad⟩
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt)
  let x : ℝ := max c (1 - r.toReal / 2)
  have hx_ge : c ≤ x := le_max_left _ _
  have hx_lt1 : x < 1 := max_lt hc (by linarith)
  have hx_in : some x ∈ D := hsub x hx_ge (le_of_lt hx_lt1)
  have hdist : realWithBotDistFamily () (some x) (some 1) < r := by
    simp only [realWithBotDistFamily, realWithBotDist]
    rw [← ENNReal.ofReal_toReal (ne_of_lt hrt)]
    apply (ENNReal.ofReal_lt_ofReal_iff hr_real_pos).mpr
    rw [abs_of_neg (by linarith)]
    have hx_ge2 : 1 - r.toReal / 2 ≤ x := le_max_right _ _
    linarith
  have hout := hrad (some x) hx_in hdist
  have hfl_lt : (⌊x⌋ : ℤ) < 1 := Int.floor_lt.mpr (by simpa using hx_lt1)
  have hfl1 : (⌊(1 : ℝ)⌋ : ℤ) = 1 := Int.floor_one
  simp only [realWithBotDistFamily, floorOp, realWithBotDist, hfl1] at hout
  have hne_real : ((⌊x⌋ : ℤ) : ℝ) ≠ (1 : ℝ) := by
    intro hEq
    have hEqInt : (⌊x⌋ : ℤ) = 1 := by exact_mod_cast hEq
    omega
  have habs_pos : 0 < |((⌊x⌋ : ℤ) : ℝ) - ((1 : ℤ) : ℝ)| := by
    rw [abs_pos, sub_ne_zero]
    simpa using hne_real
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr habs_pos)) hout

/-- Exercise 3.4(i-a) (CH03-P29-01): `D = [0, 1/2]` has `diam = 1/2`, uniform nullification
radius `= +∞`, and threshold type `(1, 1)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_a :
    ex34D1.Nonempty ∧
    ex34D1 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D1 = ENNReal.ofReal (1 / 2) ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D1 = ⊤ ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D1 () () = (1, 1) := by
  have hne : ex34D1.Nonempty := ⟨some 0, ⟨0, rfl, le_rfl, by norm_num⟩⟩
  have hdom : ex34D1 ⊆ dom floorOp := by
    rintro z ⟨x, rfl, _⟩; simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D1 = ENNReal.ofReal (1 / 2) := by
    simpa [ex34D1] using diamScaleFun_realIcc (a := (0 : ℝ)) (b := 1 / 2) (by norm_num)
  have hconst : ∀ x ∈ ex34D1, ∀ y ∈ ex34D1,
      realWithBotDistFamily () (floorOp.func x) (floorOp.func y) = 0 := by
    rintro z₁ ⟨x, rfl, hx0, hx1⟩ z₂ ⟨y, rfl, hy0, hy1⟩
    have hfx : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx0, by linarith⟩
    have hfy : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hy0, by linarith⟩
    simp [realWithBotDistFamily, floorOp, hfx, hfy, realWithBotDist]
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D1 = ⊤ := by
    apply top_unique
    apply le_iInf₂
    intro y hy
    rw [pointwiseNullRadius_eq_top_of_all_finite_pos]
    intro r hr0 hrt
    exact ⟨hr0, hrt, fun x hx _ => hconst x hx y hy⟩
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D1 () () = (1, 1) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D1 () ()).1]
    refine ⟨?_, ?_⟩
    · change diamScaleFun realWithBotDistFamily () ex34D1 < 1
      rw [hdiam, ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
    · rw [hrad]; exact le_top
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(i-b) (CH03-P29-02): `D = [9/10, 11/10]` has `diam = 1/5`, uniform nullification
radius `= 0`, and threshold type `(1, 0)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_b :
    ex34D2.Nonempty ∧
    ex34D2 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D2 = ENNReal.ofReal (1 / 5) ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D2 = 0 ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D2 () () = (1, 0) := by
  have hne : ex34D2.Nonempty := ⟨some 1, ⟨1, rfl, by norm_num, by norm_num⟩⟩
  have hdom : ex34D2 ⊆ dom floorOp := by
    rintro z ⟨x, rfl, _⟩; simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D2 = ENNReal.ofReal (1 / 5) := by
    have h := diamScaleFun_realIcc (a := (9 / 10 : ℝ)) (b := 11 / 10) (by norm_num)
    have hsub : (11 / 10 : ℝ) - 9 / 10 = 1 / 5 := by norm_num
    simpa [ex34D2, hsub] using h
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D2 = 0 := by
    apply le_antisymm _ (zero_le _)
    have h1 : some (1 : ℝ) ∈ ex34D2 := ⟨1, rfl, by norm_num, by norm_num⟩
    have hpt := floorOp_pointwise_zero_at_one (D := ex34D2) (c := 9 / 10) (by norm_num)
      (fun x hx1 hx2 => ⟨x, rfl, hx1, by linarith⟩)
    calc
      uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D2
          ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D2 (some 1) :=
            iInf₂_le (some 1) h1
      _ = 0 := hpt
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D2 () () = (1, 0) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D2 () ()).2.1]
    refine ⟨?_, ?_⟩
    · change diamScaleFun realWithBotDistFamily () ex34D2 < 1
      rw [hdiam, ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
    · rw [hrad]; exact zero_lt_one
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(i-c) (CH03-P29-03): `D = {0, 2}` has `diam = 2`, uniform nullification radius `= 2`,
and threshold type `(0, 1)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_c :
    ex34D3.Nonempty ∧
    ex34D3 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D3 = 2 ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 = 2 ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D3 () () = (0, 1) := by
  have hne : ex34D3.Nonempty := ⟨some 0, Or.inl rfl⟩
  have hdom : ex34D3 ⊆ dom floorOp := by
    intro z hz; rcases hz with rfl | rfl <;> simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D3 = 2 := by
    apply le_antisymm
    · apply iSup₂_le; intro x hx
      apply iSup₂_le; intro y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        norm_num [realWithBotDistFamily, realWithBotDist]
    · apply le_iSup₂_of_le (some 0) (Or.inl rfl)
      apply le_iSup₂_of_le (some 2) (Or.inr rfl)
      norm_num [realWithBotDistFamily, realWithBotDist]
  have hpt : ∀ y ∈ ex34D3,
      pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D3 y = 2 := by
    intro y hy
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨_, _, hrad⟩
      by_contra hgt
      have h2lt : (2 : ENNReal) < r := lt_of_not_ge hgt
      rcases hy with rfl | rfl
      · have hdist : realWithBotDistFamily () (some 2) (some 0) < r := by
          simpa [realWithBotDistFamily, realWithBotDist] using h2lt
        have hout := hrad (some 2) (Or.inr rfl) hdist
        simp [realWithBotDistFamily, floorOp, realWithBotDist] at hout
      · have hdist : realWithBotDistFamily () (some 0) (some 2) < r := by
          simpa [realWithBotDistFamily, realWithBotDist] using h2lt
        have hout := hrad (some 0) (Or.inl rfl) hdist
        simp [realWithBotDistFamily, floorOp, realWithBotDist] at hout
    · apply le_sSup
      refine ⟨by norm_num, ENNReal.ofNat_lt_top, ?_⟩
      intro x hx hdist
      have hxy : x = y := by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exfalso; simp [realWithBotDistFamily, realWithBotDist] at hdist
        · exfalso; simp [realWithBotDistFamily, realWithBotDist] at hdist
        · rfl
      subst hxy
      exact realWithBotDist_extendedPseudoMetric.dist_self _
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 = 2 := by
    apply le_antisymm
    · calc
        uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3
            ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D3 (some 0) :=
              iInf₂_le (some 0) (Or.inl rfl)
        _ = 2 := hpt (some 0) (Or.inl rfl)
    · apply le_iInf₂
      intro y hy
      change 2 ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D3 y
      rw [hpt y hy]
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D3 () () = (0, 1) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D3 () ()).2.2.1]
    refine ⟨?_, ?_⟩
    · change 1 ≤ diamScaleFun realWithBotDistFamily () ex34D3
      rw [hdiam]; norm_num
    · rw [hrad]; norm_num
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(i-d) (CH03-P29-04): `D = [0, 2]` has `diam = 2`, uniform nullification radius `= 0`,
and threshold type `(0, 0)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_d :
    ex34D4.Nonempty ∧
    ex34D4 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D4 = 2 ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D4 = 0 ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D4 () () = (0, 0) := by
  have hne : ex34D4.Nonempty := ⟨some 0, ⟨0, rfl, le_rfl, by norm_num⟩⟩
  have hdom : ex34D4 ⊆ dom floorOp := by
    rintro z ⟨x, rfl, _⟩; simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D4 = 2 := by
    simpa [ex34D4] using diamScaleFun_realIcc (a := (0 : ℝ)) (b := 2) (by norm_num)
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D4 = 0 := by
    apply le_antisymm _ (zero_le _)
    have h1 : some (1 : ℝ) ∈ ex34D4 := ⟨1, rfl, by norm_num, by norm_num⟩
    have hpt := floorOp_pointwise_zero_at_one (D := ex34D4) (c := 0) zero_lt_one
      (fun x hx1 hx2 => ⟨x, rfl, hx1, by linarith⟩)
    calc
      uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D4
          ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D4 (some 1) :=
            iInf₂_le (some 1) h1
      _ = 0 := hpt
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D4 () () = (0, 0) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D4 () ()).2.2.2.1]
    refine ⟨?_, ?_⟩
    · change 1 ≤ diamScaleFun realWithBotDistFamily () ex34D4
      rw [hdiam]; norm_num
    · rw [hrad]; exact zero_lt_one
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(ii) (CH03-P29-05): Without the diameter condition, `\underline{r}^N_{f, d, d}|_D ≥ 1`
does NOT imply global output zero-distance on `D`. Counterexample: `D = {0, 2}` from (i-c),
whose positive uniform nullification radius `2` arises from the point-separation gap `≥ 2` in `D`. -/
theorem exercise_3_4_ii :
    ¬ (∀ D : Set RealWithBot, D.Nonempty → D ⊆ dom floorOp →
        1 ≤ uniformNullRadiusCompOn realWithBotDistFamily floorOp () () D →
        ∀ x ∈ D, ∀ y ∈ D, realWithBotDist (floorOp.func x) (floorOp.func y) = 0) ∧
    (ex34D3.Nonempty ∧ ex34D3 ⊆ dom floorOp ∧
      1 ≤ uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 ∧
      realWithBotDist (floorOp.func (some 0)) (floorOp.func (some 2)) = 2 ∧
      ∀ x ∈ ex34D3, ∀ y ∈ ex34D3, x ≠ y → 2 ≤ realWithBotDist x y) := by
  have h3 := exercise_3_4_i_c
  have hge1 : 1 ≤ uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 := by
    rw [h3.2.2.2.1]; norm_num
  have hdiff : realWithBotDist (floorOp.func (some 0)) (floorOp.func (some 2)) = 2 := by
    norm_num [floorOp, realWithBotDist]
  have hgap : ∀ x ∈ ex34D3, ∀ y ∈ ex34D3, x ≠ y → 2 ≤ realWithBotDist x y := by
    intro x hx y hy hne
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hne rfl).elim
    · norm_num [realWithBotDist]
    · norm_num [realWithBotDist]
    · exact (hne rfl).elim
  refine ⟨?_, h3.1, h3.2.1, hge1, hdiff, hgap⟩
  intro hall
  have h0 := hall ex34D3 h3.1 h3.2.1 hge1 (some 0) (Or.inl rfl) (some 2) (Or.inr rfl)
  rw [hdiff] at h0
  norm_num at h0

/-! ### Exercise 3.5: Image Rearrangement and Covering Estimates (CH03-P30-01..04) -/

/-- Four-point domain `U = {0, 1, 2, 3} ⊂ ℝ ⊔ {⊥}` for Exercise 3.5. -/
def ex35U : Set RealWithBot := {some 0, some 1, some 2, some 3}

/-- Operator `f` on `U = {0, 1, 2, 3}` (identity on `U`, `⊥` outside `U`). -/
noncomputable def ex35f : Operator RealWithBot none where
  func
    | none => none
    | some x =>
        if x = 0 then some 0
        else if x = 1 then some 1
        else if x = 2 then some 2
        else if x = 3 then some 3
        else none
  preserves_bot := rfl

/-- Operator `g` on `U = {0, 1, 2, 3}` sending `0 ↦ 0, 1 ↦ 3, 2 ↦ 1, 3 ↦ 2`, and `⊥` outside `U`. -/
noncomputable def ex35g : Operator RealWithBot none where
  func
    | none => none
    | some x =>
        if x = 0 then some 0
        else if x = 1 then some 3
        else if x = 2 then some 1
        else if x = 3 then some 2
        else none
  preserves_bot := rfl

/-- Exercise 3.5(i) (CH03-P30-01): Complete piecewise formula (including all endpoints) for
`N(ε, {0, 1, 2, 3})` over all finite positive `ε`, plus the external-center obstruction at
`ε = 7/4` with `3/2 ∉ U`. -/
theorem exercise_3_5_i :
    (∀ ε : ENNReal, 0 < ε → ε ≤ 1 → covering_number realWithBotDist ε ex35U = 4) ∧
    (∀ ε : ENNReal, 1 < ε → ε ≤ 2 → covering_number realWithBotDist ε ex35U = 2) ∧
    (∀ ε : ENNReal, 2 < ε → ε < ⊤ → covering_number realWithBotDist ε ex35U = 1) ∧
    (ex35U ⊆ ball realWithBotDist (some (3 / 2)) (ENNReal.ofReal (7 / 4)) ∧
      some (3 / 2) ∉ ex35U ∧
      ¬ InternalEpsilonNet realWithBotDist (ENNReal.ofReal (7 / 4)) ex35U {some (3 / 2)} ∧
      covering_number realWithBotDist (ENNReal.ofReal (7 / 4)) ex35U = 2) := by
  classical
  have h1 : ∀ ε : ENNReal, 0 < ε → ε ≤ 1 → covering_number realWithBotDist ε ex35U = 4 := by
    intro ε hε_pos hε_le1
    let s4 : Finset RealWithBot := {some 0, some 1, some 2, some 3}
    have hs4_card : s4.card = 4 := by
      have h01 : some (0 : ℝ) ≠ some 1 := by simp
      have h02 : some (0 : ℝ) ≠ some 2 := by simp
      have h03 : some (0 : ℝ) ≠ some 3 := by simp
      have h12 : some (1 : ℝ) ≠ some 2 := by simp
      have h13 : some (1 : ℝ) ≠ some 3 := by simp
      have h23 : some (2 : ℝ) ≠ some 3 := by simp
      simp [s4, h01, h02, h03, h12, h13, h23]
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist ε ex35U s4 := by
        constructor
        · intro c hc
          simp only [s4, Finset.coe_insert, Finset.coe_singleton] at hc
          exact hc
        · intro x hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨some 0, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
          · exact ⟨some 1, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
          · exact ⟨some 2, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
          · exact ⟨some 3, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
      simpa [hs4_card] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      have hmem_all : s4 ⊆ S := by
        intro x hx
        have hxU : x ∈ ex35U := by
          simp only [s4, Finset.mem_insert, Finset.mem_singleton] at hx
          exact hx
        rcases hS.2 x hxU with ⟨c, hcS, hdist⟩
        have hlt1 : realWithBotDist x c < 1 := lt_of_lt_of_le hdist hε_le1
        have hxc : x = c := by
          rcases hxU with rfl | rfl | rfl | rfl <;> rcases hS.1 hcS with rfl | rfl | rfl | rfl
          · rfl
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · rfl
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · rfl
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · rfl
        rwa [hxc]
      have hcard : 4 ≤ S.card := by
        rw [← hs4_card]; exact Finset.card_le_card hmem_all
      exact_mod_cast hcard
  have h2 : ∀ ε : ENNReal, 1 < ε → ε ≤ 2 → covering_number realWithBotDist ε ex35U = 2 := by
    intro ε hε_gt1 hε_le2
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist ε ex35U {some 0, some 2} := by
        constructor
        · intro c hc
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hc
          rcases hc with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
        · intro x hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨some 0, by simp, by simp [realWithBotDist, lt_trans zero_lt_one hε_gt1]⟩
          · exact ⟨some 0, by simp, by simpa [realWithBotDist] using hε_gt1⟩
          · exact ⟨some 2, by simp, by simp [realWithBotDist, lt_trans zero_lt_one hε_gt1]⟩
          · exact ⟨some 2, by simp, by
              have h32 : realWithBotDist (some 3) (some 2) = 1 := by norm_num [realWithBotDist]
              rw [h32]; exact hε_gt1⟩
      have hcard : ({some (0 : ℝ), some (2 : ℝ)} : Finset RealWithBot).card = 2 := by
        rw [Finset.card_pair (by simp)]
      simpa [hcard] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      rcases hS.2 (some 0) (Or.inl rfl) with ⟨c₀, hc₀S, hdist₀⟩
      rcases hS.2 (some 3) (Or.inr (Or.inr (Or.inr rfl))) with ⟨c₃, hc₃S, hdist₃⟩
      have hc₀_lt2 : realWithBotDist (some 0) c₀ < 2 := lt_of_lt_of_le hdist₀ hε_le2
      have hc₃_lt2 : realWithBotDist (some 3) c₃ < 2 := lt_of_lt_of_le hdist₃ hε_le2
      have hne : c₀ ≠ c₃ := by
        intro hEq
        subst hEq
        rcases hS.1 hc₀S with rfl | rfl | rfl | rfl
        · norm_num [realWithBotDist] at hc₃_lt2
        · norm_num [realWithBotDist] at hc₃_lt2
        · norm_num [realWithBotDist] at hc₀_lt2
        · norm_num [realWithBotDist] at hc₀_lt2
      have hsub : ({c₀, c₃} : Finset RealWithBot) ⊆ S := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption
      have hcard : 2 ≤ S.card := by
        calc
          2 = ({c₀, c₃} : Finset RealWithBot).card := (Finset.card_pair hne).symm
          _ ≤ S.card := Finset.card_le_card hsub
      exact_mod_cast hcard
  have h3 : ∀ ε : ENNReal, 2 < ε → ε < ⊤ → covering_number realWithBotDist ε ex35U = 1 := by
    intro ε hε_gt2 _hε_fin
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist ε ex35U {some 1} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc; exact Or.inr (Or.inl rfl)
        · intro x hx
          refine ⟨some 1, Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl
          · have h1lt2 : (1 : ENNReal) < 2 := ENNReal.one_lt_two
            simpa [realWithBotDist] using lt_trans h1lt2 hε_gt2
          · simp [realWithBotDist, lt_trans (show (0 : ENNReal) < 2 by norm_num) hε_gt2]
          · have h21 : realWithBotDist (some 2) (some 1) = 1 := by norm_num [realWithBotDist]
            rw [h21]
            exact lt_trans ENNReal.one_lt_two hε_gt2
          · have h31 : realWithBotDist (some 3) (some 1) = 2 := by norm_num [realWithBotDist]
            rw [h31]
            exact hε_gt2
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty _ _ _ ⟨some 0, Or.inl rfl⟩
  have h74_gt1 : (1 : ENNReal) < ENNReal.ofReal (7 / 4) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h74_le2 : ENNReal.ofReal (7 / 4) ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hball_ext : ex35U ⊆ ball realWithBotDist (some (3 / 2)) (ENNReal.ofReal (7 / 4)) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      (simp only [ball, Set.mem_setOf_eq, realWithBotDist]
       apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 7 / 4)).mpr
       norm_num)
  have hnot_mem : some (3 / 2 : ℝ) ∉ ex35U := by
    rintro (h | h | h | h) <;> (injection h with h'; norm_num at h')
  have hnot_net : ¬ InternalEpsilonNet realWithBotDist (ENNReal.ofReal (7 / 4)) ex35U {some (3 / 2)} := by
    intro hnet
    exact hnot_mem (hnet.1 (Finset.mem_singleton_self _))
  exact ⟨h1, h2, h3, hball_ext, hnot_mem, hnot_net, h2 _ h74_gt1 h74_le2⟩

/-- Exercise 3.5(ii) (CH03-P30-02): Domains, images (`f(U) = g(U) = U`), identical covering numbers
at all finite positive `ε`, and zero mapping entropy difference for both `f` and `g`. -/
theorem exercise_3_5_ii :
    dom ex35f = ex35U ∧
    dom ex35g = ex35U ∧
    operator_image ex35f ex35U = ex35U ∧
    operator_image ex35g ex35U = ex35U ∧
    ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realWithBotDist ε (operator_image ex35f ex35U) =
        covering_number realWithBotDist ε ex35U ∧
      covering_number realWithBotDist ε (operator_image ex35g ex35U) =
        covering_number realWithBotDist ε ex35U ∧
      covering_number realWithBotDist ε (operator_image ex35f ex35U) =
        covering_number realWithBotDist ε (operator_image ex35g ex35U) ∧
      MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35f ex35U ∧
      MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35g ex35U ∧
      (∀ hwd, mappingEntropyDiffCompSame realWithBotDistFamily () ε ex35f ex35U hwd = 0) ∧
      (∀ hwd, mappingEntropyDiffCompSame realWithBotDistFamily () ε ex35g ex35U hwd = 0) := by
  have hdomf : dom ex35f = ex35U := by
    ext z
    cases z with
    | none => simp [dom, ex35f, ex35U]
    | some x =>
        simp only [dom, ex35f, ex35U, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, Option.some.injEq]
        by_cases h0 : x = 0
        · simp [h0]
        · by_cases h1 : x = 1
          · simp [h1]
          · by_cases h2 : x = 2
            · simp [h2]
            · by_cases h3 : x = 3
              · simp [h3]
              · simp [h0, h1, h2, h3]
  have hdomg : dom ex35g = ex35U := by
    ext z
    cases z with
    | none => simp [dom, ex35g, ex35U]
    | some x =>
        simp only [dom, ex35g, ex35U, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, Option.some.injEq]
        by_cases h0 : x = 0
        · simp [h0]
        · by_cases h1 : x = 1
          · simp [h1]
          · by_cases h2 : x = 2
            · simp [h2]
            · by_cases h3 : x = 3
              · simp [h3]
              · simp [h0, h1, h2, h3]
  have himgf : operator_image ex35f ex35U = ex35U := by
    ext z
    simp only [operator_image, ex35U, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩ <;> norm_num [ex35f]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨some 0, Or.inl rfl, by norm_num [ex35f]⟩
      · exact ⟨some 1, Or.inr (Or.inl rfl), by norm_num [ex35f]⟩
      · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex35f]⟩
      · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), by norm_num [ex35f]⟩
  have himgg : operator_image ex35g ex35U = ex35U := by
    ext z
    simp only [operator_image, ex35U, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩ <;> norm_num [ex35g]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨some 0, Or.inl rfl, by norm_num [ex35g]⟩
      · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex35g]⟩
      · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), by norm_num [ex35g]⟩
      · exact ⟨some 1, Or.inr (Or.inl rfl), by norm_num [ex35g]⟩
  have hU_ne : ex35U.Nonempty := ⟨some 0, Or.inl rfl⟩
  have hU_fin : ex35U.Finite := by
    simp only [ex35U]
    exact ((Set.finite_singleton _).insert _).insert _ |>.insert _
  refine ⟨hdomf, hdomg, himgf, himgg, ?_⟩
  intro ε hε_pos hε_fin
  have hcov_fin : covering_number realWithBotDist ε ex35U < ⊤ :=
    lt_of_le_of_lt (covering_number_le_card_of_finite realWithBotDist_extendedPseudoMetric hε_pos hU_fin)
      (ENNReal.natCast_lt_top _)
  have hwdf : MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35f ex35U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]; exact Or.inl hcov_fin
  have hwdg : MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35g ex35U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]; exact Or.inl hcov_fin
  refine ⟨by rw [himgf], by rw [himgg], by rw [himgf, himgg], hwdf, hwdg, ?_, ?_⟩
  · intro hwd
    change mappingEntropyDiffComp realWithBotDistFamily () () ε ex35f ex35U hwd = 0
    rw [mappingEntropyDiffComp_eq, himgf]
    change metric_entropy realWithBotDist ε ex35U - metric_entropy realWithBotDist ε ex35U = 0
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU_ne hcov_fin]
    exact_mod_cast sub_self _
  · intro hwd
    change mappingEntropyDiffComp realWithBotDistFamily () () ε ex35g ex35U hwd = 0
    rw [mappingEntropyDiffComp_eq, himgg]
    change metric_entropy realWithBotDist ε ex35U - metric_entropy realWithBotDist ε ex35U = 0
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU_ne hcov_fin]
    exact_mod_cast sub_self _

/-- Exercise 3.5(iii-a) (CH03-P30-03): Minimal scalar Lip constants on `U = {0, 1, 2, 3}` are
`L_f = 1` for `f` and `L_g = 3` for `g`, with both sufficiency and necessity proved. -/
theorem exercise_3_5_iii_a :
    (∀ x ∈ ex35U, ∀ y ∈ ex35U,
      realWithBotDist (ex35f.func x) (ex35f.func y) ≤ 1 * realWithBotDist x y) ∧
    (∀ L : ENNReal,
      (∀ x ∈ ex35U, ∀ y ∈ ex35U,
        realWithBotDist (ex35f.func x) (ex35f.func y) ≤ L * realWithBotDist x y) →
      1 ≤ L) ∧
    (∀ x ∈ ex35U, ∀ y ∈ ex35U,
      realWithBotDist (ex35g.func x) (ex35g.func y) ≤ 3 * realWithBotDist x y) ∧
    (∀ L : ENNReal,
      (∀ x ∈ ex35U, ∀ y ∈ ex35U,
        realWithBotDist (ex35g.func x) (ex35g.func y) ≤ L * realWithBotDist x y) →
      3 ≤ L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [ex35f, realWithBotDist]
  · intro L hL
    have h := hL (some 0) (Or.inl rfl) (some 1) (Or.inr (Or.inl rfl))
    norm_num [ex35f, realWithBotDist] at h
    exact h
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      (simp only [ex35g, realWithBotDist]; norm_num)
  · intro L hL
    have h := hL (some 0) (Or.inl rfl) (some 1) (Or.inr (Or.inl rfl))
    norm_num [ex35g, realWithBotDist] at h
    exact h

/-- Exercise 3.5(iii-b) (CH03-P30-04): At `ε = 7/4`, apply Proposition 3.19's covering-number
upper bound with optimal `L_f = 1` and `L_g = 3` and compare with the true covering numbers:
for `f`, bound `N(7/4, U) = 2` equals the true `2`; for `g`, bound `N(7/12, U) = 4` strictly
exceeds the true `2`. -/
theorem exercise_3_5_iii_b :
    let ε : ENNReal := ENNReal.ofReal (7 / 4)
    covering_number realWithBotDist ε (operator_image ex35f ex35U) ≤
      covering_number realWithBotDist (ε / 1) ex35U ∧
    covering_number realWithBotDist ε (operator_image ex35g ex35U) ≤
      covering_number realWithBotDist (ε / 3) ex35U ∧
    covering_number realWithBotDist ε (operator_image ex35f ex35U) = 2 ∧
    covering_number realWithBotDist (ε / 1) ex35U = 2 ∧
    covering_number realWithBotDist ε (operator_image ex35f ex35U) =
      covering_number realWithBotDist (ε / 1) ex35U ∧
    covering_number realWithBotDist ε (operator_image ex35g ex35U) = 2 ∧
    covering_number realWithBotDist (ε / 3) ex35U = 4 ∧
    covering_number realWithBotDist ε (operator_image ex35g ex35U) <
      covering_number realWithBotDist (ε / 3) ex35U := by
  intro ε
  have hε_pos : 0 < ε := ENNReal.ofReal_pos.mpr (by norm_num)
  have hε_fin : ε < ⊤ := ENNReal.ofReal_lt_top
  have hlip := exercise_3_5_iii_a
  have hbound_f : covering_number realWithBotDist ε (operator_image ex35f ex35U) ≤
      covering_number realWithBotDist (ε / 1) ex35U :=
    prop_3_19_covering_le realWithBotDistFamily ex35f ex35U () () ε 1
      hε_pos hε_fin zero_lt_one ENNReal.one_lt_top hlip.1
  have hbound_g : covering_number realWithBotDist ε (operator_image ex35g ex35U) ≤
      covering_number realWithBotDist (ε / 3) ex35U :=
    prop_3_19_covering_le realWithBotDistFamily ex35g ex35U () () ε 3
      hε_pos hε_fin (by norm_num) ENNReal.ofNat_lt_top hlip.2.2.1
  have hcovU74 : covering_number realWithBotDist ε ex35U = 2 := exercise_3_5_i.2.2.2.2.2.2
  have himgs := exercise_3_5_ii
  have htrue_f : covering_number realWithBotDist ε (operator_image ex35f ex35U) = 2 := by
    rw [himgs.2.2.1, hcovU74]
  have htrue_g : covering_number realWithBotDist ε (operator_image ex35g ex35U) = 2 := by
    rw [himgs.2.2.2.1, hcovU74]
  have hest_f : covering_number realWithBotDist (ε / 1) ex35U = 2 := by
    rw [div_one, hcovU74]
  have h712_eq : ε / 3 = ENNReal.ofReal (7 / 12) := by
    change ENNReal.ofReal (7 / 4) / (3 : ENNReal) = ENNReal.ofReal (7 / 12)
    rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have h712_pos : 0 < ε / 3 := by
    rw [h712_eq]; exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h712_le1 : ε / 3 ≤ 1 := by
    rw [h712_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hest_g : covering_number realWithBotDist (ε / 3) ex35U = 4 :=
    exercise_3_5_i.1 (ε / 3) h712_pos h712_le1
  refine ⟨hbound_f, hbound_g, htrue_f, hest_f, by rw [htrue_f, hest_f], htrue_g, hest_g, ?_⟩
  rw [htrue_g, hest_g]
  norm_num

end Ch03
```

```lean filename=Main.lean
/-
Main entry point importing all Chapter 3 formalization modules for MG-C003 v0.1.1.
Source work: "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli),
https://glenzli.com/books/oet/, licensed under CC BY 4.0.
-/
import Ch03.ComponentPartition
import Ch03.FiberFactorization
import Ch03.NullificationRadius
import Ch03.ScaleAndCovering
import Ch03.MappingEntropyDiff
import Ch03.Exercises1to3
import Ch03.Exercises4to5
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
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_const"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_id"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_act"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_const_global"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_id_global"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_act_global"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.disjoint_I_const_I_id"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.disjoint_I_const_I_act"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.disjoint_I_id_I_act"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_const_union_I_id_union_I_act"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.mem_I_const_of_both_const_and_id"}
      ],
      "representation": "对算子 ϕ : Operator X bot、规范族 d : I → X → X → ENNReal 与受限子集 U : Set X，依次定义常值分量 I_const、常值优先的恒等分量 I_id 与有效分量 I_act 及其全域特化（U = dom ϕ），并证明三者两两不交、并为全集 Set.univ 且满足常值优先原则。",
      "dependencies": []
    },
    {
      "id": "CH03-D02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.compFiber"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.compFiberSingle"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.compFiberGlobal"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.compFiberFamily"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.compFiber_singleton_eq_single"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.subfamily_pseudometric_eq_zero_iff"}
      ],
      "representation": "用冻结背景模块的 subfamily_pseudometric d J 定义计算纤维 compFiber d ϕ J U y = {x ∈ U | d_J(ϕ(x), y) = 0}，同时给出单分量纤维 compFiberSingle、全域纤维 compFiberGlobal（U = dom ϕ）及像目标去重纤维族 compFiberFamily，并证明单元素子族与单分量纤维一致及 d_J 零距等价于逐分量零距。",
      "dependencies": []
    },
    {
      "id": "CH03-D03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.pointEqRel"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.zeroDistRel"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.mem_zeroDistRel_iff_mem_compFiber"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.imageZeroSetoid"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.ImageQuot"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.imageQuotMk"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.imageQuotMk_eq_iff"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.FiberPreorder"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.IsSeparatingOn"}
      ],
      "representation": "定义点值相等点对集 pointEqRel（R_=(ϕ|U)）、全分量零距点对集 zeroDistRel（R_~(ϕ|U)）并证明其与全族计算纤维的等价对应；借助冻结引理 gauge_zero_related_equivalence 构造像集 ϕ(U) 上的等价关系 imageZeroSetoid、像商类型 ImageQuot = ϕ(U)/~_G 与典型商映射 imageQuotMk；定义纤维预序 FiberPreorder（R_~(ϕ_A|U) ⊆ R_~(ϕ_B|U)）及子集上的分离性 IsSeparatingOn。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-D04",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.IsLegalNullRadius"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.isLegalNullRadius_iff_ball"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.isLegalNullRadius_subfamily_iff_fiber"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadius"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadiusSubfamily"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadiusComp"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadiusGlobal"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadiusSubfamily_singleton"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadius_eq_zero_of_no_legal"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.pointwiseNullRadius_eq_top_of_all_finite_pos"}
      ],
      "representation": "对任意输入、输出扩展伪度量 d_in, d_out、算子 ϕ、评估域 U 与基点 y，定义合法有限正半径谓词 IsLegalNullRadius（0 < r < ⊤ 且 B_{d_in}(y,r) ∩ U ⊆ {x ∈ U | d_out(ϕ(x), ϕ(y)) = 0}）及其 ENNReal 上确界 pointwiseNullRadius（空集上确界为 0，任意有限正半径合法时取 ⊤），并给出子族/单分量/全域简写及与 ball、compFiber 的等价对应。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-D05",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.uniformNullRadius"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.uniformNullRadiusOn"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.uniformNullRadiusSubfamilyOn"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.uniformNullRadiusCompOn"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.uniformNullRadiusGlobal"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.nullificationMatrix"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.nullificationMatrixGlobal"}
      ],
      "representation": "对基点集 A 与评估域 U 定义统一零化半径 uniformNullRadius = ⨅ y ∈ A, r^N(y|U)，特化 A = U 得 uniformNullRadiusOn 及子族/单分量/全域版本；按原文行列约定（输出 j 为行、输入 i 为列）定义零化矩阵 nullificationMatrix d ϕ U j i = \\underline{r}^N_{ϕ,i,j}|_U 及全域零化矩阵 nullificationMatrixGlobal。",
      "dependencies": ["CH03-D04"]
    },
    {
      "id": "CH03-D06",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.InputScaleFamily"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.diamScaleFun"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.diamScale"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.thresholdType"}
      ],
      "representation": "用结构 InputScaleFamily 封装非空子集上关于包含单调的输入尺度族 σ_i : Set X → ENNReal；定义默认直径尺度 diamScaleFun d i A = ⨆ x ∈ A, ⨆ y ∈ A, d_i(x,y) 并验证其构成 InputScaleFamily（diamScale）；定义阈值分类 thresholdType : Fin 2 × Fin 2，第一项指示 σ_i(A) < τ_σ、第二项指示 \\underline{r}^N_{f,i,j}|_A ≥ τ_N。",
      "dependencies": ["CH03-D05"]
    },
    {
      "id": "CH03-D07",
      "status": "complete",
      "declarations": [
        {"file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean", "name": "formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet"},
        {"file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean", "name": "formal_oet.vol_01.ch_01_foundations.covering_number"},
        {"file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean", "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy"},
        {"file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean", "name": "formal_oet.vol_01.ch_01_foundations.subfamily_pseudometric"},
        {"file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean", "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.subfamily_covering_number"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.subfamily_covering_number_singleton"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.IsTotallyBounded"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.internalEpsilonNet_iff_ball"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.covering_number_eq_zero_iff"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.log2_ereal_mono"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.metric_entropy_mono_of_covering_number_le"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.metric_entropy_eq_coe_of_nonempty_of_lt_top"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.metric_entropy_eq_top_iff"}
      ],
      "representation": "直接复用冻结模块 formal_oet 中的 InternalEpsilonNet、covering_number、metric_entropy、subfamily_pseudometric 与 subfamily_metric_entropy，补充子族覆盖数 subfamily_covering_number、全有界谓词 IsTotallyBounded（∀ r ∈ (0, ⊤), N(r, U) < ⊤），并证明与开球并覆盖表述、零覆盖数等价空集、对数与度量熵单调性及有限实数/无穷取值刻画的对应。",
      "dependencies": []
    },
    {
      "id": "CH03-D08",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.MappingEntropyDiffWellDefined"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.mappingEntropyDiff"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.mappingEntropyDiffSame"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.mappingEntropyDiffComp"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.mappingEntropyDiffCompSame"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.mappingEntropyDiff_cases"}
      ],
      "representation": "定义良定前提 MappingEntropyDiffWellDefined（输入覆盖数 < ⊤ 或像集覆盖数 < ⊤，从定义层排除 ∞ - ∞ 不定形）与依赖该前提的映射熵差 mappingEntropyDiff = E_{ε,J_in}(U) - E_{ε,J_out}(ϕ(U)) : EReal，给出同子族与单分量简写，并在 mappingEntropyDiff_cases 中验证两有限、+∞ 减有限（得 ⊤）、有限减 +∞（得 ⊥）三种良定分支。",
      "dependencies": ["CH03-D07"]
    },
    {
      "id": "CH03-P01-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_1_i"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_1_i_lip_zero_row"}
      ],
      "representation": "命题 3.1(i)：对任意 i ∈ I_const(ϕ|U) 与 x, y ∈ U，证明 d_i(ϕ(x), ϕ(y)) ≤ ∑_{k ∈ I} 0 · d_k(x, y) = 0；并证明将任意合法 Lip 矩阵的第 i 输出行置零仍为合法 Lip 矩阵。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P01-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_1_ii"}
      ],
      "representation": "命题 3.1(ii)：若 i ∈ I_const(ϕ|U)、K 为 U 上合法 co-Lip 矩阵且存在 x, y ∈ U 使 d_k(x, y) > 0，则 K_{k→i} = 0（按 formal_oet 索引记作 K k i = 0）。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P01-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_1_iii"}
      ],
      "representation": "命题 3.1(iii)：对扩展伪度量 d_i 与 i ∈ I_id(ϕ|U)，用两次三角不等式与对称性证明 ∀ x, y ∈ U, d_i(ϕ(x), ϕ(y)) = d_i(x, y)。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P02-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_2_i"}
      ],
      "representation": "命题 3.2(i)：在 U ⊆ dom(ϕ₂ ∘ ϕ₁) 与扩展伪度量族下，按四种非有效情形逆否证明 I_act(ϕ₂ ∘ ϕ₁ | U) ⊆ I_act(ϕ₁ | U) ∪ I_act(ϕ₂ | ϕ₁(U))，其中第二步采用实际中间像域 ϕ₁(U)。",
      "dependencies": ["CH03-D01", "CH03-P02-03"]
    },
    {
      "id": "CH03-P02-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.chainOp"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.chainDomain"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.chainDomain_eq_image_chainOp"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.I_act_identity_eq_empty"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_2_ii"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.chainOpFin"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.chainDomainFin"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_2_ii_fin"}
      ],
      "representation": "命题 3.2(ii)：定义任意长度 n ∈ ℕ（含 n = 0 时 c₀ = id）的递归复合 chainOp 与递归实际像域 chainDomain（U_{m+1} = ϕ_m(U_m)），证明空复合有效分量为空集并通过对 n 归纳证明 I_act(c_n | U₁) ⊆ ⋃_{m < n} I_act(ϕ_m | U_m)，同时提供 Fin n 有限元组版本。",
      "dependencies": ["CH03-D01", "CH03-P02-01"]
    },
    {
      "id": "CH03-P02-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_2_iii"}
      ],
      "representation": "命题 3.2(iii)：证明 I_id(ϕ₁ | U) ∩ I_id(ϕ₂ | ϕ₁(U)) ⊆ I_id(ϕ₂ ∘ ϕ₁ | U)，既由三角不等式得逐点零距，又利用命题 3.1(iii) 排除复合落入常值优先分支。",
      "dependencies": ["CH03-D01", "CH03-P01-03"]
    },
    {
      "id": "CH03-P03-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.SwapSpace"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.swapDist"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.swapDist_extendedPseudoMetric"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.swapOp"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.swapU"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.remark_prop_3_2_converse_fails"}
      ],
      "representation": "命题 3.2 后注：构造合法三点扩展规范空间 SwapSpace = {⊥, a, b}、离散伪度量 swapDist 与两点换位算子 swapOp（U = {a, b}），完整计算两步均有效且非恒等、复合后恒等且非有效，并同时否定命题 3.2(i) 与 (iii) 的反向包含。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P04-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_3_i"}
      ],
      "representation": "命题 3.3(i)：在 U ⊆ dom(ψ ∘ ϕ) 下，若 i ∈ I_const(ψ | ϕ(U))，则 i ∈ I_const(ψ ∘ ϕ | U)。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P04-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.SevenSpace"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.TwoIdx"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.sevenDist"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.sevenDist_extendedPseudoMetric"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.sevenPhi"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.sevenPsi"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.sevenU"},
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.prop_3_3_ii_counterexample"}
      ],
      "representation": "命题 3.3(ii)：构造合法七点空间 SevenSpace = {⊥, a, b, p, q, r, s} 与双分量规范族 TwoIdx = {i, m}（d_i 合并 {p, q}，d_m 离散），验证全部扩展伪度量公理、U = {a, b} ⊆ dom(ψ ∘ ϕ)、i ∈ I_const(ϕ | U) 且 i ∉ I_const(ψ ∘ ϕ | U)。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P05-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ComponentPartition.lean", "name": "Ch03.cor_3_4"}
      ],
      "representation": "推论 3.4：若 U ⊆ dom(ψ ∘ ϕ)、j ∈ I_const(ϕ | U) 且存在 L ∈ L(ψ)|_{ϕ(U)} 使 k ≠ j 时 L_{k→j} = 0（允许 L_{j→j} = ⊤），由冻结引理 lip_bound_of_single_input_row 与 ⊤ · 0 = 0 推出 j ∈ I_const(ψ ∘ ϕ | U)。",
      "dependencies": ["CH03-D01"]
    },
    {
      "id": "CH03-P06-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_i"}
      ],
      "representation": "命题 3.5(i)：对任意 y, y' ∈ X，若 d_J(y, y') = 0，则 Fib_{ϕ,J}(y | U) = Fib_{ϕ,J}(y' | U)。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-P06-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_ii_a"}
      ],
      "representation": "命题 3.5(ii-a)：对任意 y ∈ ϕ(U)，Fib_{ϕ,J}(y | U) 非空，且这些纤维之并（及 ⋃₀ compFiberFamily）等于 U。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-P06-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_ii_b"}
      ],
      "representation": "命题 3.5(ii-b)：任意两像目标 y₁, y₂ ∈ ϕ(U) 的纤维要么相等要么不交；去重后的集合族 compFiberFamily 满足两两不交、每元非空且含于 U、并等于 U，构成 U 的分划。",
      "dependencies": ["CH03-D02", "CH03-P06-01", "CH03-P06-02"]
    },
    {
      "id": "CH03-P06-04",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_iii"}
      ],
      "representation": "命题 3.5(iii)：对任意非空子族 J ⊆ I，证明 Fib_{ϕ,J}(y | U) = ⋂_{j ∈ J} Fib_{ϕ,j}(y | U)。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-P06-05",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_iv"}
      ],
      "representation": "命题 3.5(iv)：若非空子族 J ⊆ K，则 Fib_{ϕ,K}(y | U) ⊆ Fib_{ϕ,J}(y | U)。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-P06-06",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_v"}
      ],
      "representation": "命题 3.5(v)：证明单元素子族 Fib_{ϕ,{i}}(y | U) = Fib_{ϕ,i}(y | U)，且全子族纤维 Fib_{ϕ,I}(y | U) 含于每个单分量纤维 Fib_{ϕ,i}(y | U)。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-P06-07",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_vi_a"}
      ],
      "representation": "命题 3.5(vi-a)：当 j ∈ I_id(ϕ | U) 时，对任意目标 y ∈ X，单分量纤维 Fib_{ϕ,j}(y | U) 等于输入零距类 {x ∈ U | d_j(x, y) = 0}。",
      "dependencies": ["CH03-D01", "CH03-D02"]
    },
    {
      "id": "CH03-P06-08",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_5_vi_b"}
      ],
      "representation": "命题 3.5(vi-b)：当 j ∈ I_const(ϕ | U) 时，对任意像目标 y₀ ∈ ϕ(U) 有 Fib_{ϕ,j}(y₀ | U) = U，且对任意满足 d_j(y, y₀) > 0 的目标 y 有 Fib_{ϕ,j}(y | U) = ∅。",
      "dependencies": ["CH03-D01", "CH03-D02"]
    },
    {
      "id": "CH03-P07-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_i_nec"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_i"}
      ],
      "representation": "命题 3.6(i-必要)：若存在映射 T : ϕ_A(U) → X 使 U 上 T ∘ ϕ_A = ϕ_B，则 R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)。",
      "dependencies": ["CH03-D03"]
    },
    {
      "id": "CH03-P07-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_i_suff"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_i"}
      ],
      "representation": "命题 3.6(i-充分)：由 R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U) 显式构造良定义映射 T : {z // z ∈ ϕ_A(U)} → X 并验证 ∀ x ∈ U, T(ϕ_A(x)) = ϕ_B(x)，无需非空假设（涵括 U = ∅）。",
      "dependencies": ["CH03-D03"]
    },
    {
      "id": "CH03-P07-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_ii"}
      ],
      "representation": "命题 3.6(ii)：双向点值像映射都存在当且仅当 R_=(ϕ_A | U) = R_=(ϕ_B | U)。",
      "dependencies": ["CH03-D03", "CH03-P07-01", "CH03-P07-02"]
    },
    {
      "id": "CH03-P07-04",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_iii"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_6_iii_subsingleton"}
      ],
      "representation": "命题 3.6(iii)：在单分量情形下，若 T 存在且 ϕ_A 在 U 上 K_A-co-Lip（0 < K_A < ⊤）、ϕ_B 在 U 上 L_B-Lip（L_B < ⊤），则 T 在实际像域 ϕ_A(U) 上满足 (L_B / K_A)-Lip 标量界；另附 [Subsingleton I] 矩阵界特化版本。",
      "dependencies": ["CH03-D03"]
    },
    {
      "id": "CH03-P08-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_7_one_way"}
      ],
      "representation": "命题 3.7（单向）：存在满足 Tbar([ϕ_A(x)]) = [ϕ_B(x)]（∀ x ∈ U）的商映射 Tbar : ϕ_A(U)/~_G → ϕ_B(U)/~_G 当且仅当 R_~(ϕ_A | U) ⊆ R_~(ϕ_B | U)，充分性以 Quotient.lift 构造代表元无关商映射。",
      "dependencies": ["CH03-D03"]
    },
    {
      "id": "CH03-P08-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_7_two_way"}
      ],
      "representation": "命题 3.7（双向）：按规定公式诱导的双向商映射都存在当且仅当 R_~(ϕ_A | U) = R_~(ϕ_B | U)。",
      "dependencies": ["CH03-D03", "CH03-P08-01"]
    },
    {
      "id": "CH03-P08-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.pointEqRel_eq_zeroDistRel_of_separatingOn"},
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.prop_3_7_image_separating"}
      ],
      "representation": "命题 3.7（像集分离特化）：仅在两个实际像集 ϕ_A(U) 与 ϕ_B(U) 各自满足 IsSeparatingOn 的前提下，证明 R_= = R_~ 在两侧均成立，并推出单向与双向点值因子化判据分别等价于相应商值因子化判据。",
      "dependencies": ["CH03-D03", "CH03-P07-01", "CH03-P07-02", "CH03-P07-03", "CH03-P08-01", "CH03-P08-02"]
    },
    {
      "id": "CH03-P09-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.remark_fiber_preorder_refl_trans"}
      ],
      "representation": "纤维包含传递注（预序性质）：证明固定公共域 U 上的 FiberPreorder d U 具有自反性与传递性。",
      "dependencies": ["CH03-D03"]
    },
    {
      "id": "CH03-P09-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.remark_fiber_chain_trans"}
      ],
      "representation": "纤维包含传递注（有限链传递）：对公共评估域 U 上的任意有限链 ϕ₀, …, ϕₘ，若每步 ϕ_{r-1} ⪰_{fiber,U} ϕ_r，则对任意 0 ≤ a ≤ b ≤ m 均有 ϕ_a ⪰_{fiber,U} ϕ_b。",
      "dependencies": ["CH03-D03"]
    },
    {
      "id": "CH03-P09-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/FiberFactorization.lean", "name": "Ch03.remark_fiber_chain_strict"}
      ],
      "representation": "纤维包含传递注（严格包含传递）：若链中存在某一步为真包含 R_~(ϕ_{r-1}|U) ⊂ R_~(ϕ_r|U)，则推出端点真包含 R_~(ϕ₀|U) ⊂ R_~(ϕₘ|U) 并显式给出差集见证 p ∈ R_~(ϕₘ|U) \\ R_~(ϕ₀|U)。",
      "dependencies": ["CH03-D03", "CH03-P09-02"]
    },
    {
      "id": "CH03-P10-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.RealWithBot"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.realWithBotDist"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.realWithBotDist_extendedPseudoMetric"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.stepOp"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.stepU"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.counterexample_3_1_valid"}
      ],
      "representation": "反例 3.1（结构合法性）：构造带吸收元的通常实线 RealWithBot = Option ℝ 与扩展伪度量 realWithBotDist、阶跃算子 stepOp 及穿孔评估域 stepU = [-1,0) ∪ (0,1]，验证 ExtendedPseudoMetric、非空性与 stepU ⊆ dom stepOp。",
      "dependencies": []
    },
    {
      "id": "CH03-P10-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.counterexample_3_1_pointwise"}
      ],
      "representation": "反例 3.1（点态半径）：对任意 some t ∈ stepU，证明合法有限正半径集恰为 (0, |t|]，进而点态零化半径等于 ENNReal.ofReal |t| > 0。",
      "dependencies": ["CH03-D04", "CH03-P10-01"]
    },
    {
      "id": "CH03-P10-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.counterexample_3_1_uniform_zero"}
      ],
      "representation": "反例 3.1（统一半径为零）：在同一个固定评估域 stepU 上取任意趋零正基点 t = min 1 (ε/2)，证明统一零化半径 uniformNullRadiusOn 等于 0。",
      "dependencies": ["CH03-D05", "CH03-P10-02"]
    },
    {
      "id": "CH03-P11-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_8_i_a"}
      ],
      "representation": "命题 3.8(i-a)：若非空输出子族 J ⊆ I_const(ϕ | U)，则对任意 y ∈ U，像目标纤维 Fib_{ϕ,J}(ϕ(y) | U) = U。",
      "dependencies": ["CH03-D01", "CH03-D02"]
    },
    {
      "id": "CH03-P11-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_8_i_b"}
      ],
      "representation": "命题 3.8(i-b)：若非空输出子族 J ⊆ I_const(ϕ | U)，则对任意输入指标 i ∈ I，每个基点 y ∈ U 的点态半径与统一零化半径均为 ⊤。",
      "dependencies": ["CH03-D01", "CH03-D04", "CH03-D05", "CH03-P11-01"]
    },
    {
      "id": "CH03-P11-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.infInputDist"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.infInputDist_extendedPseudoMetric"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_8_ii_counterexample"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_8_ii_eq"},
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_8_ii_ne"}
      ],
      "representation": "命题 3.8(ii)：在 SwapSpace = {⊥, a, b}、U = {a, b}、ϕ = id 上构造任意指标集 I 的扩展伪度量族 infInputDist i（d_i(a,b) = ⊤，其余分量取 1），同时覆盖 i = j 与 i ≠ j 两种情形，证明 [N(id)|_U]_{ji} = ⊤ 但 j ∉ I_const(id | U)。",
      "dependencies": ["CH03-D01", "CH03-D05", "CH03-P03-01"]
    },
    {
      "id": "CH03-P12-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_9_i"}
      ],
      "representation": "命题 3.9(i)：若 i ∈ I_id(ϕ | U) 且 y ∈ U，由命题 3.1(iii) 证明 Fib_{ϕ,i}(ϕ(y) | U) = {x ∈ U | d_i(x, y) = 0}。",
      "dependencies": ["CH03-D01", "CH03-D02", "CH03-P01-03"]
    },
    {
      "id": "CH03-P12-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_9_ii"}
      ],
      "representation": "命题 3.9(ii)：若 i ∈ I_id(ϕ | U)、y ∈ U 且有限正半径 r₀ 满足 B_i(y, r₀) ∩ U ⊆ {x ∈ U | d_i(x, y) = 0}，则 r^N_{ϕ,i,i}(y | U) ≥ r₀ > 0。",
      "dependencies": ["CH03-D04", "CH03-P12-01"]
    },
    {
      "id": "CH03-P13-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_10_pointwise"}
      ],
      "representation": "命题 3.10（点态最小值公式）：对有限非空输出子族 J ⊆ I，证明点态零化半径 r^N_{ϕ,i,J}(y | U) 等于单分量半径之最小值（同时给出 ⨅ j ∈ J 与 Finset.inf' 形式）。",
      "dependencies": ["CH03-D04"]
    },
    {
      "id": "CH03-P13-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_10_uniform"}
      ],
      "representation": "命题 3.10（统一半径公式）：交换基点下确界与有限非空最小值，证明 \\underline{r}^N_{ϕ,i,J}|_U = min_{j ∈ J} [N(ϕ)|_U]_{ji}（同时给出 ⨅ j ∈ J 与 Finset.inf' 形式）。",
      "dependencies": ["CH03-D05", "CH03-P13-01"]
    },
    {
      "id": "CH03-P13-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_10_antitone"}
      ],
      "representation": "命题 3.10（输出子族反单调性）：若非空子族 J ⊆ K，则 \\underline{r}^N_{ϕ,i,K}|_U ≤ \\underline{r}^N_{ϕ,i,J}|_U。",
      "dependencies": ["CH03-D05", "CH03-P13-02"]
    },
    {
      "id": "CH03-P14-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_11_fiber"}
      ],
      "representation": "命题 3.11（纤维条件）：若 y' ∈ Fib_{ϕ₂,j}(ϕ₂(y) | U₂)，由纤维定义与伪度量对称性得 d_j(ϕ₂(y), ϕ₂(y')) = 0。",
      "dependencies": ["CH03-D02"]
    },
    {
      "id": "CH03-P14-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_11_radius"}
      ],
      "representation": "命题 3.11（零化半径条件）：若 d_i(y, y') < r^N_{ϕ₂,i,j}(y | U₂)，由上确界定义提取满足 d_i(y', y) < ρ 的合法有限正半径 ρ，归结至纤维条件推出 d_j(ϕ₂(y), ϕ₂(y')) = 0。",
      "dependencies": ["CH03-D04", "CH03-P14-01"]
    },
    {
      "id": "CH03-P14-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_11_compose"}
      ],
      "representation": "命题 3.11（复合特化）：在 x, x' ∈ dom ϕ₁、两像点 ϕ₁(x), ϕ₁(x') 均属于指定下游域 U₂ ⊆ dom ϕ₂ 且 ϕ₁(x') ∈ Fib_{ϕ₂,j}(ϕ₂(ϕ₁(x)) | U₂) 条件下，推出 d_j((ϕ₂ ∘ ϕ₁)(x), (ϕ₂ ∘ ϕ₁)(x')) = 0。",
      "dependencies": ["CH03-D02", "CH03-P14-01"]
    },
    {
      "id": "CH03-P15-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_12_i"}
      ],
      "representation": "命题 3.12(i)：若下游 ϕ₂ 在实际像域 ϕ₁(U) 上保持 d_l-零距到 d_j-零距，则复合零化矩阵满足 [N(ϕ₂ ∘ ϕ₁)|_U]_{ji} ≥ [N(ϕ₁)|_U]_{li}。",
      "dependencies": ["CH03-D05", "CH03-P14-02"]
    },
    {
      "id": "CH03-P15-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/NullificationRadius.lean", "name": "Ch03.prop_3_12_ii"}
      ],
      "representation": "命题 3.12(ii)：若存在有限正数 L 使 ϕ₁ 在 U 上满足单通道 Lip 上界 d_l(ϕ₁(x), ϕ₁(x')) ≤ L · d_i(x, x')，则 [N(ϕ₂ ∘ ϕ₁)|_U]_{ji} ≥ [N(ϕ₂)|_{ϕ₁(U)}]_{jl} / L，统一覆盖右端为 0、有限正数与 ⊤ 三种情况。",
      "dependencies": ["CH03-D05", "CH03-P14-02"]
    },
    {
      "id": "CH03-P16-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.lemma_3_13_partition"}
      ],
      "representation": "引理 3.13（四分划）：证明 thresholdType 对每个通道 (i, j) 恰取 (1,1), (1,0), (0,1), (0,0) 之一（互斥且穷尽），并给出各组合与两个互补阈值不等式的精确充要刻画。",
      "dependencies": ["CH03-D06"]
    },
    {
      "id": "CH03-P16-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.lemma_3_13_i"}
      ],
      "representation": "引理 3.13(i)：固定其他数据，当 τ_σ ≤ τ_σ' 时，第一项取 1 的通道集合按包含单调不减。",
      "dependencies": ["CH03-D06"]
    },
    {
      "id": "CH03-P16-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.lemma_3_13_ii"}
      ],
      "representation": "引理 3.13(ii)：固定其他数据，当 τ_N ≤ τ_N' 时，第二项取 1 的通道集合按包含单调不增。",
      "dependencies": ["CH03-D06"]
    },
    {
      "id": "CH03-P17-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_14_i"}
      ],
      "representation": "命题 3.14(i)：对任意单调输入尺度族 σ，若 ∅ ≠ B ⊆ A ⊆ dom f，则 σ_i(B) ≤ σ_i(A)，特别地 σ_i(A) < τ_σ 推出 σ_i(B) < τ_σ。",
      "dependencies": ["CH03-D06"]
    },
    {
      "id": "CH03-P17-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_14_ii_a"}
      ],
      "representation": "命题 3.14(ii-a)：对固定基点 x ∈ B ⊆ A，缩小评估域使点态零化半径单调不减 r^N_{f,i,j}(x | A) ≤ r^N_{f,i,j}(x | B)。",
      "dependencies": ["CH03-D04"]
    },
    {
      "id": "CH03-P17-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_14_ii_b"}
      ],
      "representation": "命题 3.14(ii-b)：先缩小取下确界基点集（A → B）再缩小评估域（应用命题 3.14(ii-a)），证明 \\underline{r}^N_{f,i,j}|_A ≤ \\underline{r}^N_{f,i,j}|_B。",
      "dependencies": ["CH03-D05", "CH03-P17-02"]
    },
    {
      "id": "CH03-P17-04",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_14_iii_counterexample"}
      ],
      "representation": "命题 3.14(iii)：在带吸收元实直线 RealWithBot 上取 f = id、A = {0, 1}、B = {0}、直径尺度与 τ_σ = 1/2，证明 diam(B) = 0 < 1/2 而 diam(A) = 1 ≥ 1/2，否定反向尺度判断。",
      "dependencies": ["CH03-D06", "CH03-P10-01"]
    },
    {
      "id": "CH03-P18-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_15_i"}
      ],
      "representation": "命题 3.15(i)：对 x, y ∈ A，若 d_i(x, y) < \\underline{r}^N_{f,i,j}|_A，由下确界定义与命题 3.11 推出 d_j(f(x), f(y)) = 0。",
      "dependencies": ["CH03-D05", "CH03-P14-02"]
    },
    {
      "id": "CH03-P18-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_15_ii"}
      ],
      "representation": "命题 3.15(ii)：作为 (i) 的逆否命题，对 x, y ∈ A，若 d_j(f(x), f(y)) > 0，则 d_i(x, y) ≥ \\underline{r}^N_{f,i,j}|_A。",
      "dependencies": ["CH03-D05", "CH03-P18-01"]
    },
    {
      "id": "CH03-P18-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_15_iii"}
      ],
      "representation": "命题 3.15(iii)：当 \\underline{r}^N_{f,i,j}|_A < α < τ_N < ⊤ 时，构造点对 x, y ∈ A 与有限正数 ε（当输出距离为 ⊤ 时取 ε = 1，有限时取输出距离本身），使 d_i(x, y) < α 且 ε ≤ d_j(f(x), f(y))。",
      "dependencies": ["CH03-D04", "CH03-D05"]
    },
    {
      "id": "CH03-P19-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_16_i"}
      ],
      "representation": "命题 3.16(i)：当 \\underline{r}^N_{f,i,j}|_A ≥ τ_N（有限正阈值）时，对任意 x ∈ A，B_i(x, τ_N) ∩ A ⊆ Fib_{f,j}(f(x) | A)。",
      "dependencies": ["CH03-D02", "CH03-D05", "CH03-P18-01"]
    },
    {
      "id": "CH03-P19-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_16_ii_a"}
      ],
      "representation": "命题 3.16(ii-a)：对任意 B ⊆ A（含 B = ∅ 及无有限覆盖情形）与任意有限正 ε，将 B 的有限 τ_N-内覆盖中心集 S 映为 f(S) 构成 f(B) 的内部 ε-覆盖且基数不增，从而 N_j(ε, f(B)) ≤ N_i(τ_N, B)。",
      "dependencies": ["CH03-D07", "CH03-P19-01"]
    },
    {
      "id": "CH03-P19-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.prop_3_16_ii_b"}
      ],
      "representation": "命题 3.16(ii-b)：当 B ⊆ A 非空时，由覆盖数不等式及 log2_ereal 的单调性推出 E_{ε,j}(f(B)) ≤ E_{τ_N,i}(B)。",
      "dependencies": ["CH03-D07", "CH03-P19-02"]
    },
    {
      "id": "CH03-P20-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.post_prop_3_16_counterexample_for_a"},
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.post_prop_3_16_counterexample"}
      ],
      "representation": "命题 3.16 后正文反例：在反例 3.1 的同一阶跃算子 stepOp 与评估域 stepU 上，既对任意有限正 τ 与任意满足 0 < a ≤ 1、2a < τ 的 a，也显式构造满足条件的 a = min 1 (τ/4)，令 B = {-a, a} ⊆ stepU，证明 N_1(τ, B) = 1 < 2 = N_1(1/2, f(B))。",
      "dependencies": ["CH03-D07", "CH03-P10-01"]
    },
    {
      "id": "CH03-P21-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.cor_3_17_iff"}
      ],
      "representation": "推论 3.17（整体零化等价判据）：在 diam_{d_i}(A) < τ_σ ≤ τ_N（有限正阈值）精确条件下，证明 \\underline{r}^N_{f,i,j}|_A ≥ τ_N 当且仅当 ∀ x, y ∈ A, d_j(f(x), f(y)) = 0。",
      "dependencies": ["CH03-D05", "CH03-D06", "CH03-P18-01"]
    },
    {
      "id": "CH03-P21-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/ScaleAndCovering.lean", "name": "Ch03.cor_3_17_covering_one"}
      ],
      "representation": "推论 3.17（覆盖数为 1）：当上述等价条件成立且 A 非空时，对任意有限正 ε，任取 f(x₀) ∈ f(A) 作单中心内部覆盖并结合非空下界，证明 N_j(ε, f(A)) = 1。",
      "dependencies": ["CH03-D07", "CH03-P21-01"]
    },
    {
      "id": "CH03-P22-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.covering_number_le_card_of_finite"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.remark_finite_mapping_entropy_diff_well_defined"}
      ],
      "representation": "有限集上映射熵差良定注：对任意非空有限子集 U ⊆ dom ϕ、任意非空子族 J_in, J_out 与有限正 ε，证明输入与像集覆盖数均满足 1 ≤ N < ⊤、两端熵均为有限实数，且 MappingEntropyDiffWellDefined 成立。",
      "dependencies": ["CH03-D07", "CH03-D08"]
    },
    {
      "id": "CH03-P23-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_18_i"}
      ],
      "representation": "命题 3.18(i)：若 j ∈ I_const(ϕ | U)（U 非空），证明 N_j(ε, ϕ(U)) = 1、E_{ε,j}(ϕ(U)) = 0、熵差良定（允许输入熵为 +∞）且 ΔE_{ε,j}(ϕ | U) = E_{ε,j}(U)。",
      "dependencies": ["CH03-D01", "CH03-D07", "CH03-D08"]
    },
    {
      "id": "CH03-P23-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_18_ii_a"}
      ],
      "representation": "命题 3.18(ii-a)：若 j ∈ I_id(ϕ | U)，借助命题 3.1(iii) 保距性将输入中心前推且将像集中心反向取原像代表元，证明 N_j(ε, ϕ(U)) = N_j(ε, U) 与 E_{ε,j}(ϕ(U)) = E_{ε,j}(U)。",
      "dependencies": ["CH03-D01", "CH03-D07", "CH03-P01-03"]
    },
    {
      "id": "CH03-P23-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_18_ii_b"}
      ],
      "representation": "命题 3.18(ii-b)：若 j ∈ I_id(ϕ | U) 且显式假定 MappingEntropyDiffWellDefined（从而两覆盖数同为有限正数，绝不定义 ∞ - ∞），证明 ΔE_{ε,j}(ϕ | U) = 0。",
      "dependencies": ["CH03-D08", "CH03-P23-02"]
    },
    {
      "id": "CH03-P24-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_19_net_pushforward"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_19_covering_le"}
      ],
      "representation": "命题 3.19（覆盖数上界）：有限正单通道 Lip 常数 L 将 U 的内部 (ε/L)-覆盖中心集 S 前推为 ϕ(U) 的内部 ε-覆盖中心集 S.image ϕ 且基数不增，从而 N_j(ε, ϕ(U)) ≤ N_i(ε/L, U)。",
      "dependencies": ["CH03-D07"]
    },
    {
      "id": "CH03-P24-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_19_entropy_diff_ge"}
      ],
      "representation": "命题 3.19（熵差下界）：在 U 关于 d_i 全有界前提下，证明输入与像集覆盖数均有限、熵差良定，且 ΔE_{ε,i,j}(ϕ | U) ≥ E_{ε,i}(U) - E_{ε/L,i}(U)。",
      "dependencies": ["CH03-D07", "CH03-D08", "CH03-P24-01"]
    },
    {
      "id": "CH03-P25-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_20_net_pullback"},
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_20_covering_ge"}
      ],
      "representation": "命题 3.20（覆盖数下界）：在 IsCoLipMatrix d ϕ U K 且 0 < K_{i→j} < ⊤ 下，将 ϕ(U) 的内部 ε-覆盖中心集 T 逐点选原像拉回为 U 的内部 (ε/K_{i→j})-覆盖中心集 S 且 |S| ≤ |T|，从而 N_i(ε/K_{i→j}, U) ≤ N_j(ε, ϕ(U))。",
      "dependencies": ["CH03-D07"]
    },
    {
      "id": "CH03-P25-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/MappingEntropyDiff.lean", "name": "Ch03.prop_3_20_entropy_diff_le"}
      ],
      "representation": "命题 3.20（熵差上界）：在 U 关于 d_i 全有界前提下（允许输出覆盖数与输出熵为 +∞），证明熵差良定并满足 ΔE_{ε,i,j}(ϕ | U) ≤ E_{ε,i}(U) - E_{ε/K_{i→j},i}(U)。",
      "dependencies": ["CH03-D07", "CH03-D08", "CH03-P25-01"]
    },
    {
      "id": "CH03-P26-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.absDiffDist"},
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.absDiffDist_extendedPseudoMetric"},
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.ex31Op"},
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.ex31U"},
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_1_i_a"}
      ],
      "representation": "习题 3.1(i-a)：验证 ℝ ⊔ {⊥} 上绝对值差伪度量 d_i(x,y) = ||x|-|y|| 的合法性、仿射算子 ϕ(x) = 2x - 1 在 U = {0, 1} 上的定义域合法性，算出 Fib_{ϕ,i}(ϕ(0) | U) = U 及 i ∈ I_const(ϕ | U)（且不属于 I_id 与 I_act）。",
      "dependencies": ["CH03-D01", "CH03-D02", "CH03-P10-01"]
    },
    {
      "id": "CH03-P26-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_1_i_b"}
      ],
      "representation": "习题 3.1(i-b)：在同一子集 U = {0, 1} 上验证 U ⊆ dom(ϕ²)，算出 Fib_{ϕ²,i}(ϕ²(0) | U) = {0} 及 i ∈ I_act(ϕ² | U)（且不属于 I_const 与 I_id）。",
      "dependencies": ["CH03-D01", "CH03-D02", "CH03-P26-01"]
    },
    {
      "id": "CH03-P26-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_1_ii"}
      ],
      "representation": "习题 3.1(ii)：对任意在 U = {0, 1} 上同取实值 c 的算子 ψ，证明 ψ²(0) = ψ²(1) 恒成立；分两种情形说明：若 some c ∈ dom ψ 则 U ⊆ dom(ψ²) 且 0, 1 落入同一纤维 U（常值分量）；若 some c ∉ dom ψ 则 U ⊈ dom(ψ²) 且 U ∩ dom(ψ²) = ∅（再次像为吸收元时不再满足受限域条件）。",
      "dependencies": ["CH03-D01", "CH03-D02", "CH03-P26-01"]
    },
    {
      "id": "CH03-P27-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_2_i"}
      ],
      "representation": "习题 3.2(i)：在 IsCoLipMatrix d ϕ U K、K_{i→j} > 0（不要求有限）与 r^N_{ϕ,i,j}(y | U) > 0 下，联立命题 3.11 与冻结引理 positive_colip_entry_reflects_zero，证明 ∀ x ∈ U, d_i(x, y) ∉ (0, r^N_{ϕ,i,j}(y | U))。",
      "dependencies": ["CH03-D04", "CH03-P14-02"]
    },
    {
      "id": "CH03-P27-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_2_ii"}
      ],
      "representation": "习题 3.2(ii)：若 \\underline{r}^N_{ϕ,i,j}|_U > 0，证明 {0} 与 [\\underline{r}^N_{ϕ,i,j}|_U, +∞] 不交且 ∀ x, y ∈ U, d_i(x, y) ∈ {0} ∪ [\\underline{r}^N_{ϕ,i,j}|_U, +∞]。",
      "dependencies": ["CH03-D05", "CH03-P27-01"]
    },
    {
      "id": "CH03-P28-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.ex33Op"},
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.ex33U"},
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_3_i"}
      ],
      "representation": "习题 3.3(i)：验证绝对值差规范空间与平移算子 ϕ(x) = x + 1 在 U = {-3, -2, 0, 2} 上的合法性，并精确计算恒等算子纤维分划 {{-3}, {-2, 2}, {0}} 与平移算子纤维分划 {{-3}, {-2, 0}, {2}}。",
      "dependencies": ["CH03-D02", "CH03-P26-01"]
    },
    {
      "id": "CH03-P28-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises1to3.lean", "name": "Ch03.exercise_3_3_ii"}
      ],
      "representation": "习题 3.3(ii)：在精确半径 ε = 3/2 下通过显式内部覆盖与下界反证证明 N_i(3/2, U) = 2、N_i(3/2, ϕ(U)) = 1、熵差良定且 ΔE_{3/2,i}(ϕ | U) = 1。",
      "dependencies": ["CH03-D07", "CH03-D08", "CH03-P28-01"]
    },
    {
      "id": "CH03-P29-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.realWithBotDistFamily"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.realWithBotDistFamily_extendedPseudoMetric"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.realIcc"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.diamScaleFun_realIcc"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.floorOp"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex34D1"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_4_i_a"}
      ],
      "representation": "习题 3.4(i-a)：对取整算子 floorOp 与 D₁ = [0, 1/2]（τ_σ = τ_N = 1），验证非空与域合法性，算得 diam = 1/2、统一零化半径 = ⊤、阈值组合为 (1, 1)。",
      "dependencies": ["CH03-D05", "CH03-D06", "CH03-P10-01", "CH03-P16-01"]
    },
    {
      "id": "CH03-P29-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex34D2"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.floorOp_pointwise_zero_at_one"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_4_i_b"}
      ],
      "representation": "习题 3.4(i-b)：对 D₂ = [9/10, 11/10]，验证 diam = 1/5、在跳跃点 1 处点态零化半径为 0 从而统一零化半径 = 0、阈值组合为 (1, 0)。",
      "dependencies": ["CH03-D05", "CH03-D06", "CH03-P16-01", "CH03-P29-01"]
    },
    {
      "id": "CH03-P29-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex34D3"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_4_i_c"}
      ],
      "representation": "习题 3.4(i-c)：对 D₃ = {0, 2}，证明 diam = 2、两点点态半径均为 2 从而统一零化半径 = 2、阈值组合为 (0, 1)。",
      "dependencies": ["CH03-D05", "CH03-D06", "CH03-P16-01", "CH03-P29-01"]
    },
    {
      "id": "CH03-P29-04",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex34D4"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_4_i_d"}
      ],
      "representation": "习题 3.4(i-d)：对 D₄ = [0, 2]，证明 diam = 2、统一零化半径 = 0（由跳跃点 1 处点态半径为 0 得到）、阈值组合为 (0, 0)。",
      "dependencies": ["CH03-D05", "CH03-D06", "CH03-P16-01", "CH03-P29-01", "CH03-P29-02"]
    },
    {
      "id": "CH03-P29-05",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_4_ii"}
      ],
      "representation": "习题 3.4(ii)：以 (i-c) 的 D₃ = {0, 2} 为反例否定无直径条件时 \\underline{r}^N ≥ 1 蕴含整体输出零距（因 d(f(0), f(2)) = 2 ≠ 0），并证明 D₃ 内不同点间距至少为 2 是其正统一零化半径的来源。",
      "dependencies": ["CH03-D05", "CH03-P29-03"]
    },
    {
      "id": "CH03-P30-01",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex35U"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_5_i"}
      ],
      "representation": "习题 3.5(i)：对 U = {0, 1, 2, 3} 证明全部有限正 ε 的完整分段覆盖数（0 < ε ≤ 1 时为 4，1 < ε ≤ 2 时为 2，2 < ε < ⊤ 时为 1，含端点 ε = 1, 2），并在 ε = 7/4 处证明 U ⊆ B(3/2, 7/4) 但 3/2 ∉ U，故 {3/2} 不是合法内部覆盖且 N(7/4, U) = 2。",
      "dependencies": ["CH03-D07", "CH03-P10-01"]
    },
    {
      "id": "CH03-P30-02",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex35f"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.ex35g"},
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_5_ii"}
      ],
      "representation": "习题 3.5(ii)：验证 dom f = dom g = U、f(U) = g(U) = U，并对所有有限正 ε 证明两像集覆盖数彼此相等且等于 N(ε, U)，两个映射熵差均良定且等于 0。",
      "dependencies": ["CH03-D07", "CH03-D08", "CH03-P22-01", "CH03-P30-01"]
    },
    {
      "id": "CH03-P30-03",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_5_iii_a"}
      ],
      "representation": "习题 3.5(iii-a)：分别证明 f 在 U 上最小标量 Lip 常数为 1（充分性与点对 (0, 1) 给出的必要下界 1 ≤ L）及 g 在 U 上最小标量 Lip 常数为 3（充分性与点对 (0, 1) 给出的必要下界 3 ≤ L）。",
      "dependencies": ["CH03-P30-02"]
    },
    {
      "id": "CH03-P30-04",
      "status": "complete",
      "declarations": [
        {"file": "Ch03/Exercises4to5.lean", "name": "Ch03.exercise_3_5_iii_b"}
      ],
      "representation": "习题 3.5(iii-b)：在 ε = 7/4 下调用命题 3.19 的覆盖数上界 prop_3_19_covering_le 分别代入最优常数 L_f = 1 与 L_g = 3，算出 f 的上界 N(7/4, U) = 2 与真实覆盖数 2 相等，g 的上界 N(7/12, U) = 4 严格大于真实覆盖数 2。",
      "dependencies": ["CH03-P24-01", "CH03-P30-01", "CH03-P30-02", "CH03-P30-03"]
    }
  ]
}
```