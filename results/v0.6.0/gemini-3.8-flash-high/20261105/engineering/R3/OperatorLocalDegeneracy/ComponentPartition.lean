import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Finset

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D01: 常值分量 -/
def I_const (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0 }

/-- CH03-D01: 恒等分量 -/
def I_id (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | i ∉ I_const d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0 }

/-- CH03-D01: 有效分量 -/
def I_act (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | i ∉ I_const d ϕ U ∧ i ∉ I_id d ϕ U }

lemma not_mem_I_act_iff (ϕ : Operator X bot) (U : Set X) (i : I) :
    i ∉ I_act d ϕ U ↔ i ∈ I_const d ϕ U ∨ i ∈ I_id d ϕ U := by
  dsimp [I_act]
  push Not
  tauto

/-- CH03-P01-01: 命题 3.1 (i) 常值分量零行上界 -/
theorem prop_3_1_i (ϕ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ I_const d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  have h0 : d i (ϕ.func x) (ϕ.func y) = 0 := hi x hx y hy
  rw [h0]
  have hsum : (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by
    simp
  rw [hsum]

/-- CH03-P01-02: 命题 3.1 (ii) 存在正输入距离的源条目必为零 -/
theorem prop_3_1_ii (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K) (i : I) (hi : i ∈ I_const d ϕ U)
    (k : I) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hpos : 0 < d k x y) :
    K k i = 0 := by
  have hout : d i (ϕ.func x) (ϕ.func y) = 0 := hi x hx y hy
  exact colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K k i x y hK hx hy hout hpos

/-- CH03-P01-03: 命题 3.1 (iii) 恒等分量双向保距等式 -/
theorem prop_3_1_iii (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (i : I) (hi : i ∈ I_id d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y := by
  intro x hx y hy
  have hx0 : d i (ϕ.func x) x = 0 := hi.2 x hx
  have hy0 : d i (ϕ.func y) y = 0 := hi.2 y hy
  apply le_antisymm
  · calc
      d i (ϕ.func x) (ϕ.func y) ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := (hd i).triangle _ _ _
      _ ≤ d i (ϕ.func x) x + (d i x y + d i y (ϕ.func y)) := add_le_add (le_refl _) ((hd i).triangle _ _ _)
      _ = 0 + (d i x y + 0) := by
        rw [hx0]
        congr 1
        congr 1
        rw [(hd i).symm, hy0]
      _ = d i x y := by simp
  · calc
      d i x y ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := (hd i).triangle _ _ _
      _ ≤ d i x (ϕ.func x) + (d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y) := add_le_add (le_refl _) ((hd i).triangle _ _ _)
      _ = 0 + (d i (ϕ.func x) (ϕ.func y) + 0) := by
        rw [(hd i).symm, hx0]
        congr 1
        rw [hy0]
      _ = d i (ϕ.func x) (ϕ.func y) := by simp

/-- CH03-P02-03: 命题 3.2 (iii) 恒等分量保留，同时排除常值优先分支 -/
theorem prop_3_2_iii (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    I_id d ϕ₁ U ∩ I_id d ϕ₂ (ϕ₁.func '' U) ⊆ I_id d (ϕ₂ * ϕ₁) U := by
  rintro i ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro hconst
    rcases h1.1 with h1_not_const
    apply h1_not_const
    intro x hx y hy
    have hx_im : ϕ₁.func x ∈ ϕ₁.func '' U := Set.mem_image_of_mem _ hx
    have hy_im : ϕ₁.func y ∈ ϕ₁.func '' U := Set.mem_image_of_mem _ hy
    have h_eq := prop_3_1_iii d hd ϕ₂ (ϕ₁.func '' U) i h2 (ϕ₁.func x) hx_im (ϕ₁.func y) hy_im
    have h_comp : d i ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) = 0 := hconst x hx y hy
    change d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) = 0 at h_comp
    rw [h_eq] at h_comp
    exact h_comp
  · intro x hx
    change d i (ϕ₂.func (ϕ₁.func x)) x = 0
    have hx_im : ϕ₁.func x ∈ ϕ₁.func '' U := Set.mem_image_of_mem _ hx
    have h2x : d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) = 0 := h2.2 (ϕ₁.func x) hx_im
    have h1x : d i (ϕ₁.func x) x = 0 := h1.2 x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i (ϕ₂.func (ϕ₁.func x)) x ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) x := (hd i).triangle _ _ _
      _ = 0 + 0 := by rw [h2x, h1x]
      _ = 0 := by simp

/-- CH03-P02-01: 命题 3.2 (i) 两步有效分量包含，实际中间像域 -/
theorem prop_3_2_i (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    I_act d (ϕ₂ * ϕ₁) U ⊆ I_act d ϕ₁ U ∪ I_act d ϕ₂ (ϕ₁.func '' U) := by
  intro i hi
  by_contra hnot
  have hnot' : i ∉ I_act d ϕ₁ U ∧ i ∉ I_act d ϕ₂ (ϕ₁.func '' U) := by
    simpa [Set.mem_union] using hnot
  have hnot1 := hnot'.1
  have hnot2 := hnot'.2
  have h_cases1 : i ∈ I_const d ϕ₁ U ∨ i ∈ I_id d ϕ₁ U :=
    (not_mem_I_act_iff d ϕ₁ U i).mp hnot1
  have h_cases2 : i ∈ I_const d ϕ₂ (ϕ₁.func '' U) ∨ i ∈ I_id d ϕ₂ (ϕ₁.func '' U) :=
    (not_mem_I_act_iff d ϕ₂ (ϕ₁.func '' U) i).mp hnot2
  have h_comp : i ∈ I_const d (ϕ₂ * ϕ₁) U ∨ i ∈ I_id d (ϕ₂ * ϕ₁) U := by
    rcases h_cases2 with h2c | h2id
    · left
      intro x hx y hy
      change d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) = 0
      exact h2c (ϕ₁.func x) (Set.mem_image_of_mem _ hx) (ϕ₁.func y) (Set.mem_image_of_mem _ hy)
    · rcases h_cases1 with h1c | h1id
      · left
        intro x hx y hy
        change d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) = 0
        have hx_im : ϕ₁.func x ∈ ϕ₁.func '' U := Set.mem_image_of_mem _ hx
        have hy_im : ϕ₁.func y ∈ ϕ₁.func '' U := Set.mem_image_of_mem _ hy
        have h2x : d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) = 0 := h2id.2 (ϕ₁.func x) hx_im
        have h2y : d i (ϕ₂.func (ϕ₁.func y)) (ϕ₁.func y) = 0 := h2id.2 (ϕ₁.func y) hy_im
        have h1xy : d i (ϕ₁.func x) (ϕ₁.func y) = 0 := h1c x hx y hy
        apply le_antisymm _ (zero_le _)
        calc
          d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y))
              ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) (ϕ₂.func (ϕ₁.func y)) := (hd i).triangle _ _ _
          _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + (d i (ϕ₁.func x) (ϕ₁.func y) + d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y))) :=
              add_le_add (le_refl _) ((hd i).triangle _ _ _)
          _ = 0 + (0 + 0) := by
            rw [h2x, h1xy]
            congr 1
            rw [(hd i).symm, h2y]
          _ = 0 := by simp
      · right
        exact prop_3_2_iii d hd ϕ₁ ϕ₂ U ⟨h1id, h2id⟩
  dsimp [I_act] at hi
  rcases h_comp with hc | hid
  · exact hi.1 hc
  · exact hi.2 hid

lemma I_act_identity (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) (U : Set X) :
    I_act d (@operator_identity X bot) U = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hi
  dsimp [I_act] at hi
  apply hi.2
  refine ⟨hi.1, ?_⟩
  intro x hx
  change d i (id x) x = 0
  exact (hd i).dist_self x

/-- 任意有限链的有效分量并集 -/
def chain_active_union (ϕs : List (Operator X bot)) (U : Set X) : Set I :=
  match ϕs with
  | [] => ∅
  | ϕ :: tail => chain_active_union tail U ∪ I_act d ϕ ((OperatorChain tail).func '' U)

/-- CH03-P02-02: 命题 3.2 (ii) 任意有限长度链，包含零步基例和实际域递推 -/
theorem prop_3_2_ii (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕs : List (Operator X bot)) (U : Set X) :
    I_act d (OperatorChain ϕs) U ⊆ chain_active_union d ϕs U := by
  induction ϕs with
  | nil =>
      dsimp [OperatorChain, chain_active_union]
      have hid : (⟨id, rfl⟩ : Operator X bot) = @operator_identity X bot := rfl
      rw [hid, I_act_identity d hd U]
  | cons ϕ tail ih =>
      dsimp [chain_active_union]
      change I_act d (ϕ * OperatorChain tail) U ⊆ chain_active_union d tail U ∪ I_act d ϕ ((OperatorChain tail).func '' U)
      have hstep := prop_3_2_i d hd (OperatorChain tail) ϕ U
      apply Set.Subset.trans hstep
      apply Set.union_subset_union_left
      exact ih

/-- CH03-P04-01: 命题 3.3 (i) 外侧在实际像域上常值则复合常值 -/
theorem prop_3_3_i (ϕ ψ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ I_const d ψ (ϕ.func '' U)) :
    i ∈ I_const d (ψ * ϕ) U := by
  intro x hx y hy
  change d i (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0
  exact hi (ϕ.func x) (Set.mem_image_of_mem _ hx) (ϕ.func y) (Set.mem_image_of_mem _ hy)

/-- CH03-P05-01: 推论 3.4 常值分量在复合中的保持条件 -/
theorem cor_3_4 (ϕ ψ : Operator X bot) (U : Set X) (j : I)
    (hj : j ∈ I_const d ϕ U) (L : I → I → ENNReal)
    (hL : IsLipMatrix d ψ (ϕ.func '' U) L)
    (h_row_zero : ∀ k, k ≠ j → L k j = 0) :
    j ∈ I_const d (ψ * ϕ) U := by
  intro x hx y hy
  change d j (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0
  have hx_im : ϕ.func x ∈ ϕ.func '' U := Set.mem_image_of_mem _ hx
  have hy_im : ϕ.func y ∈ ϕ.func '' U := Set.mem_image_of_mem _ hy
  have hbound := lip_bound_of_single_input_row d ψ (ϕ.func '' U) L j j hL h_row_zero
    (ϕ.func x) hx_im (ϕ.func y) hy_im
  have hj0 : d j (ϕ.func x) (ϕ.func y) = 0 := hj x hx y hy
  rw [hj0, mul_zero] at hbound
  exact le_antisymm hbound (zero_le _)

def option_discrete_dist {α : Type} [DecidableEq α] : Option α → Option α → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => if x = y then 0 else 1

theorem option_discrete_extended {α : Type} [DecidableEq α] (hα : Nonempty α) :
    ExtendedPseudoMetric (Option α) none option_discrete_dist := by
  rcases hα with ⟨a⟩
  refine {
    nonabsorbing := ⟨some a, by simp⟩
    dist_self := by
      intro x
      cases x <;> simp [option_discrete_dist]
    symm := by
      intro x y
      cases x <;> cases y <;> simp [option_discrete_dist]
      split_ifs <;> tauto
    triangle := by
      intro x y z
      cases x <;> cases y <;> cases z <;> simp [option_discrete_dist]
      split_ifs <;> try simp <;> try (subst_vars; contradiction)
    isolate_bot := by
      intro x hx
      cases x
      · exact False.elim (hx rfl)
      · rfl
  }

theorem pullback_extended_pseudo_metric {X Y : Type} {botX : X} {botY : Y}
    (dY : Y → Y → ENNReal) (hY : ExtendedPseudoMetric Y botY dY)
    (f : X → Y) (h_bot : f botX = botY) (h_bot_iff : ∀ x, f x = botY ↔ x = botX)
    (h_nonabsorbing : ∃ x, x ≠ botX) :
    ExtendedPseudoMetric X botX (fun x y => dY (f x) (f y)) := by
  refine {
    nonabsorbing := h_nonabsorbing
    dist_self := fun x => hY.dist_self (f x)
    symm := fun x y => hY.symm (f x) (f y)
    triangle := fun x y z => hY.triangle (f x) (f y) (f z)
    isolate_bot := by
      intro x hx
      have hfx : f x ≠ botY := by
        intro h
        exact hx ((h_bot_iff x).mp h)
      have h := hY.isolate_bot (f x) hfx
      rw [h_bot]
      exact h
  }

inductive TwoPt : Type
  | a : TwoPt
  | b : TwoPt
  | bot : TwoPt
deriving DecidableEq, Fintype

def two_pt_to_opt : TwoPt → Option (Fin 2)
  | TwoPt.bot => none
  | TwoPt.a => some 0
  | TwoPt.b => some 1

def two_pt_gauge : Unit → TwoPt → TwoPt → ENNReal :=
  fun () x y => option_discrete_dist (two_pt_to_opt x) (two_pt_to_opt y)

theorem two_pt_gauge_extended : ∀ i : Unit, ExtendedPseudoMetric TwoPt TwoPt.bot (two_pt_gauge i) := by
  intro ()
  apply pullback_extended_pseudo_metric option_discrete_dist
    (option_discrete_extended ⟨0⟩) two_pt_to_opt rfl
  · intro x; cases x <;> simp [two_pt_to_opt]
  · exact ⟨TwoPt.a, by decide⟩

def swap_func : TwoPt → TwoPt
  | TwoPt.a => TwoPt.b
  | TwoPt.b => TwoPt.a
  | TwoPt.bot => TwoPt.bot

def swap_op : Operator TwoPt TwoPt.bot :=
  ⟨swap_func, rfl⟩

def two_pt_U : Set TwoPt := {TwoPt.a, TwoPt.b}

theorem swap_im : swap_op.func '' two_pt_U = two_pt_U := by
  ext x
  simp only [two_pt_U, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩
    · right; rfl
    · left; rfl
  · rintro (rfl | rfl)
    · exact ⟨TwoPt.b, Or.inr rfl, rfl⟩
    · exact ⟨TwoPt.a, Or.inl rfl, rfl⟩

theorem swap_I_act : () ∈ I_act two_pt_gauge swap_op two_pt_U := by
  dsimp [I_act, I_const, I_id]
  refine ⟨?_, ?_⟩
  · intro hc
    have h := hc TwoPt.a (Or.inl rfl) TwoPt.b (Or.inr rfl)
    change option_discrete_dist (some 1) (some 0) = 0 at h
    simp [option_discrete_dist] at h
  · rintro ⟨-, hid⟩
    have h := hid TwoPt.a (Or.inl rfl)
    change option_discrete_dist (some 1) (some 0) = 0 at h
    simp [option_discrete_dist] at h

theorem swap_comp_I_id : () ∈ I_id two_pt_gauge (swap_op * swap_op) two_pt_U := by
  dsimp [I_id, I_const]
  refine ⟨?_, ?_⟩
  · intro hc
    have h := hc TwoPt.a (Or.inl rfl) TwoPt.b (Or.inr rfl)
    change option_discrete_dist (some 0) (some 1) = 0 at h
    simp [option_discrete_dist] at h
  · intro x hx
    rcases hx with rfl | rfl
    · change option_discrete_dist (some 0) (some 0) = 0
      simp [option_discrete_dist]
    · change option_discrete_dist (some 1) (some 1) = 0
      simp [option_discrete_dist]

theorem swap_comp_I_act_empty : I_act two_pt_gauge (swap_op * swap_op) two_pt_U = ∅ := by
  ext x; cases x
  simp [I_act]
  intro _
  exact swap_comp_I_id

/-- CH03-P03-01: 注（复合分量保持的逆向蕴含一般不成立） -/
theorem remark_3_2_counterexample :
    (¬ (I_act two_pt_gauge swap_op two_pt_U ∪ I_act two_pt_gauge swap_op (swap_op.func '' two_pt_U) ⊆
        I_act two_pt_gauge (swap_op * swap_op) two_pt_U)) ∧
    (¬ (I_id two_pt_gauge (swap_op * swap_op) two_pt_U ⊆
        I_id two_pt_gauge swap_op two_pt_U ∩ I_id two_pt_gauge swap_op (swap_op.func '' two_pt_U))) := by
  constructor
  · intro hsub
    have h_mem : () ∈ I_act two_pt_gauge swap_op two_pt_U ∪ I_act two_pt_gauge swap_op (swap_op.func '' two_pt_U) :=
      Or.inl swap_I_act
    have h_in := hsub h_mem
    rw [swap_comp_I_act_empty] at h_in
    exact h_in
  · intro hsub
    have h_in := hsub swap_comp_I_id
    rcases h_in with ⟨h1, -⟩
    have h_act := swap_I_act
    dsimp [I_act] at h_act
    exact h_act.2 h1

inductive SevenPt : Type
  | bot : SevenPt
  | a : SevenPt
  | b : SevenPt
  | p : SevenPt
  | q : SevenPt
  | r : SevenPt
  | s : SevenPt
deriving DecidableEq, Fintype

def to_opt_fin5 : SevenPt → Option (Fin 5)
  | SevenPt.bot => none
  | SevenPt.a => some 0
  | SevenPt.b => some 1
  | SevenPt.p => some 2
  | SevenPt.q => some 2
  | SevenPt.r => some 3
  | SevenPt.s => some 4

def to_opt_fin6 : SevenPt → Option (Fin 6)
  | SevenPt.bot => none
  | SevenPt.a => some 0
  | SevenPt.b => some 1
  | SevenPt.p => some 2
  | SevenPt.q => some 3
  | SevenPt.r => some 4
  | SevenPt.s => some 5

def seven_pt_d0 (x y : SevenPt) : ENNReal :=
  option_discrete_dist (to_opt_fin5 x) (to_opt_fin5 y)

def seven_pt_d1 (x y : SevenPt) : ENNReal :=
  option_discrete_dist (to_opt_fin6 x) (to_opt_fin6 y)

def seven_pt_gauge : Fin 2 → SevenPt → SevenPt → ENNReal
  | 0 => seven_pt_d0
  | 1 => seven_pt_d1

theorem seven_pt_d0_extended : ExtendedPseudoMetric SevenPt SevenPt.bot seven_pt_d0 := by
  apply pullback_extended_pseudo_metric option_discrete_dist
    (option_discrete_extended ⟨0⟩) to_opt_fin5 rfl
  · intro x; cases x <;> simp [to_opt_fin5]
  · exact ⟨SevenPt.a, by decide⟩

theorem seven_pt_d1_extended : ExtendedPseudoMetric SevenPt SevenPt.bot seven_pt_d1 := by
  apply pullback_extended_pseudo_metric option_discrete_dist
    (option_discrete_extended ⟨0⟩) to_opt_fin6 rfl
  · intro x; cases x <;> simp [to_opt_fin6]
  · exact ⟨SevenPt.a, by decide⟩

theorem seven_pt_gauge_extended : ∀ i : Fin 2, ExtendedPseudoMetric SevenPt SevenPt.bot (seven_pt_gauge i) := by
  intro i
  fin_cases i
  · exact seven_pt_d0_extended
  · exact seven_pt_d1_extended

def seven_phi_func : SevenPt → SevenPt
  | SevenPt.a => SevenPt.p
  | SevenPt.b => SevenPt.q
  | _ => SevenPt.bot

def seven_psi_func : SevenPt → SevenPt
  | SevenPt.p => SevenPt.r
  | SevenPt.q => SevenPt.s
  | _ => SevenPt.bot

def seven_phi : Operator SevenPt SevenPt.bot := ⟨seven_phi_func, rfl⟩
def seven_psi : Operator SevenPt SevenPt.bot := ⟨seven_psi_func, rfl⟩

def seven_U : Set SevenPt := {SevenPt.a, SevenPt.b}

/-- CH03-P04-02: 命题 3.3 (ii) 内侧同分量零距未必复合零距的合法七点、双分量反例 -/
theorem prop_3_3_ii_counterexample :
    (0 : Fin 2) ∈ I_const seven_pt_gauge seven_phi seven_U ∧
    (0 : Fin 2) ∉ I_const seven_pt_gauge (seven_psi * seven_phi) seven_U := by
  constructor
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
  · intro hc
    have h := hc SevenPt.a (Or.inl rfl) SevenPt.b (Or.inr rfl)
    change (1 : ENNReal) = 0 at h
    exact one_ne_zero h

end OperatorLocalDegeneracy
