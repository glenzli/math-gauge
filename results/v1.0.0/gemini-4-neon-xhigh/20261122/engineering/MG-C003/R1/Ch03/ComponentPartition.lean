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
