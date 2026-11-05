import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius
import OperatorLocalDegeneracy.ThresholdClassification
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

-- ============================================================================
-- 习题 3.1: CH03-P26-01, CH03-P26-02, CH03-P26-03
-- ============================================================================

noncomputable def d_abs (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (abs (abs a - abs b))
  | _, _ => ⊤

/-- CH03-P26-01: 验证绝对值读数伪度量合法 -/
theorem ex_3_1_i_a_extended : ExtendedPseudoMetric (Option ℝ) none d_abs := by
  refine {
    nonabsorbing := ⟨some 0, by simp⟩
    dist_self := by
      intro x; cases x <;> simp [d_abs]
    symm := by
      intro x y; cases x <;> cases y <;> simp [d_abs]
      rw [abs_sub_comm]
    triangle := by
      intro x y z
      cases x <;> cases y <;> cases z <;> simp [d_abs]
      rename_i a b c
      have h : abs (abs a - abs c) ≤ abs (abs a - abs b) + abs (abs b - abs c) := by
        have := abs_sub_le (abs a) (abs b) (abs c)
        linarith
      refine le_trans (ENNReal.ofReal_le_ofReal h) ?_
      exact ENNReal.ofReal_add_le
    isolate_bot := by
      intro x hx; cases x
      · exact False.elim (hx rfl)
      · rfl
  }

noncomputable def affine_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (2 * r - 1)
  preserves_bot := rfl

def ex31_U : Set (Option ℝ) := { some 0, some 1 }

lemma mem_ex31_U (x : Option ℝ) : x ∈ ex31_U ↔ x = some 0 ∨ x = some 1 := by
  dsimp [ex31_U]; simp

noncomputable def d_abs_gauge : Unit → Option ℝ → Option ℝ → ENNReal := fun () => d_abs

lemma affine_op_eval_zero : affine_op.func (some 0) = some (-1) := by
  dsimp [affine_op]; congr 1; norm_num

lemma affine_op_eval_one : affine_op.func (some 1) = some 1 := by
  dsimp [affine_op]; congr 1; norm_num

lemma affine_sq_eval_zero : (affine_op * affine_op).func (some 0) = some (-3) := by
  change affine_op.func (affine_op.func (some 0)) = some (-3)
  rw [affine_op_eval_zero]
  dsimp [affine_op]; congr 1; norm_num

lemma affine_sq_eval_one : (affine_op * affine_op).func (some 1) = some 1 := by
  change affine_op.func (affine_op.func (some 1)) = some 1
  rw [affine_op_eval_one, affine_op_eval_one]

/-- CH03-P26-01: 习题 3.1 (i-a) φ的纤维与分量类型 -/
theorem ex_3_1_i_a_fiber :
    Fib_single d_abs_gauge affine_op () (affine_op.func (some 0)) ex31_U = ex31_U := by
  ext x
  simp only [Fib_single, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    rw [mem_ex31_U] at hx
    dsimp [d_abs_gauge]
    rw [affine_op_eval_zero]
    rcases hx with rfl | rfl
    · rw [affine_op_eval_zero]
      dsimp [d_abs]
      have : abs (abs (-1 : ℝ) - abs (-1 : ℝ)) = 0 := by norm_num
      rw [this]; exact ENNReal.ofReal_zero
    · rw [affine_op_eval_one]
      dsimp [d_abs]
      have : abs (abs (1 : ℝ) - abs (-1 : ℝ)) = 0 := by norm_num
      rw [this]; exact ENNReal.ofReal_zero

theorem ex_3_1_i_a_const :
    () ∈ I_const d_abs_gauge affine_op ex31_U := by
  intro x hx y hy
  rw [mem_ex31_U] at hx hy
  dsimp [d_abs_gauge]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> {
    change d_abs (some (2 * _ - 1)) (some (2 * _ - 1)) = 0
    dsimp [d_abs]
    norm_num
  }

/-- CH03-P26-02: 习题 3.1 (i-b) φ²的纤维与分量类型 -/
theorem ex_3_1_i_b_fiber :
    Fib_single d_abs_gauge (affine_op * affine_op) () ((affine_op * affine_op).func (some 0)) ex31_U = {some 0} := by
  ext x
  simp only [Fib_single, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hdist⟩
    rw [mem_ex31_U] at hx
    rcases hx with rfl | rfl
    · rfl
    · dsimp [d_abs_gauge] at hdist
      rw [affine_sq_eval_one, affine_sq_eval_zero] at hdist
      dsimp [d_abs] at hdist
      have : abs (abs (1 : ℝ) - abs (-3 : ℝ)) = 2 := by norm_num
      rw [this] at hdist
      have : ENNReal.ofReal 2 ≠ 0 := by norm_num
      contradiction
  · rintro rfl
    refine ⟨by simp [mem_ex31_U], ?_⟩
    dsimp [d_abs_gauge]
    rw [affine_sq_eval_zero]
    dsimp [d_abs]
    have : abs (abs (-3 : ℝ) - abs (-3 : ℝ)) = 0 := by norm_num
    rw [this]; exact ENNReal.ofReal_zero

theorem ex_3_1_i_b_act :
    () ∈ I_act d_abs_gauge (affine_op * affine_op) ex31_U := by
  dsimp [I_act, I_const, I_id]
  simp only [Set.mem_setOf_eq, not_and]
  constructor
  · intro hconst
    have h := hconst (some 0) (by simp [mem_ex31_U]) (some 1) (by simp [mem_ex31_U])
    dsimp [d_abs_gauge] at h
    rw [affine_sq_eval_zero, affine_sq_eval_one] at h
    dsimp [d_abs] at h
    have : abs (abs (-3 : ℝ) - abs (1 : ℝ)) = 2 := by norm_num
    rw [this] at h
    have : ENNReal.ofReal 2 ≠ 0 := by norm_num
    contradiction
  · intro _ hid
    have h := hid (some 0) (by simp [mem_ex31_U])
    dsimp [d_abs_gauge] at h
    rw [affine_sq_eval_zero] at h
    dsimp [d_abs] at h
    have : abs (abs (-3 : ℝ) - abs (0 : ℝ)) = 3 := by norm_num
    rw [this] at h
    have : ENNReal.ofReal 3 ≠ 0 := by norm_num
    contradiction

/-- CH03-P26-03: 习题 3.1 (ii) 点值常算子自复合仍不能区分两点 -/
theorem ex_3_1_ii (c : Option ℝ) :
    let const_op : Operator (Option ℝ) none := {
      func := fun x => match x with | none => none | some _ => c,
      preserves_bot := rfl
    }
    ∀ x ∈ ex31_U, ∀ y ∈ ex31_U,
      d_abs ((const_op * const_op).func x) ((const_op * const_op).func y) = 0 := by
  intro const_op x hx y hy
  rw [mem_ex31_U] at hx hy
  change d_abs (const_op.func (const_op.func x)) (const_op.func (const_op.func y)) = 0
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> {
    dsimp [const_op]
    cases c <;> simp [d_abs]
  }

-- ============================================================================
-- 习题 3.2: CH03-P27-01, CH03-P27-02
-- ============================================================================

variable {X : Type} {bot : X}

/-- CH03-P27-01: 习题 3.2 (i) 正co-Lip通道与点态零化推出不存在(0, rN)内的输入距离 -/
theorem ex_3_2_i (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K r_N : ENNReal) (hK_pos : 0 < K) (hrN_pos : 0 < r_N)
    (h_unif : r_N ≤ r_null_uniform d_in d_out ϕ U)
    (hcoLip : ∀ x ∈ U, ∀ y ∈ U, K * d_in x y ≤ d_out (ϕ.func x) (ϕ.func y)) :
    ¬∃ x ∈ U, ∃ y ∈ U, 0 < d_in x y ∧ d_in x y < r_N := by
  rintro ⟨x, hx, y, hy, hdist_pos, hdist_rN⟩
  have hlt : d_in x y < r_null_uniform d_in d_out ϕ U := lt_of_lt_of_le hdist_rN h_unif
  have hzero := prop_3_15_i d_in d_out ϕ U hx hy hlt
  have h1 := hcoLip x hx y hy
  rw [hzero] at h1
  have h_prod_zero : K * d_in x y = 0 := nonpos_iff_eq_zero.mp h1
  rw [mul_eq_zero] at h_prod_zero
  rcases h_prod_zero with hK0 | hd0
  · exact hK_pos.ne' hK0
  · rw [hd0] at hdist_pos
    exact (lt_self_iff_false 0).mp hdist_pos

/-- CH03-P27-02: 习题 3.2 (ii) 统一正半径给零或≥统一半径二择 -/
theorem ex_3_2_ii (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K r_N : ENNReal) (hK_pos : 0 < K) (hrN_pos : 0 < r_N)
    (h_unif : r_N ≤ r_null_uniform d_in d_out ϕ U)
    (hcoLip : ∀ x ∈ U, ∀ y ∈ U, K * d_in x y ≤ d_out (ϕ.func x) (ϕ.func y))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d_in x y = 0 ∨ r_N ≤ d_in x y := by
  by_cases hzero : d_in x y = 0
  · left; exact hzero
  · right
    have hpos : 0 < d_in x y := pos_iff_ne_zero.mpr hzero
    have hno := ex_3_2_i d_in d_out ϕ U K r_N hK_pos hrN_pos h_unif hcoLip
    by_contra! hlt
    exact hno ⟨x, hx, y, hy, hpos, hlt⟩

-- ============================================================================
-- 习题 3.3: CH03-P28-01, CH03-P28-02
-- ============================================================================

def id_op (X : Type) (bot : X) : Operator X bot := ⟨id, rfl⟩

noncomputable def trans_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (r + 1)
  preserves_bot := rfl

def ex33_U : Set (Option ℝ) := { some (-3), some (-2), some 0, some 2 }

lemma mem_ex33_U (x : Option ℝ) : x ∈ ex33_U ↔ x = some (-3) ∨ x = some (-2) ∨ x = some 0 ∨ x = some 2 := by
  dsimp [ex33_U]; simp

/-- CH03-P28-01: 习题 3.3 (i) 恒等算子输入纤维分划 -/
theorem ex_3_3_i_id_fiber (x : Option ℝ) (hx : x ∈ ex33_U) :
    Fib_single d_abs_gauge (id_op (Option ℝ) none) () ((id_op (Option ℝ) none).func x) ex33_U =
      if x = some (-2) ∨ x = some 2 then {some (-2), some 2} else {x} := by
  rw [mem_ex33_U] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · -- x = some (-3)
    have : ¬ (some (-3 : ℝ) = some (-2) ∨ some (-3 : ℝ) = some 2) := by intro h; rcases h with h | h <;> { injection h with h_eq; norm_num at h_eq }
    rw [if_neg this]
    ext y; simp only [Fib_single, id_op, id_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try rfl
      all_goals { dsimp [d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro rfl; refine ⟨by simp [mem_ex33_U], ?_⟩
      dsimp [d_abs_gauge, d_abs]; norm_num
  · -- x = some (-2)
    have : (some (-2 : ℝ) = some (-2) ∨ some (-2 : ℝ) = some 2) := Or.inl rfl
    rw [if_pos this]
    ext y; simp only [Fib_single, id_op, id_eq, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try { left; rfl } <;> try { right; rfl }
      all_goals { dsimp [d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro (rfl | rfl) <;> refine ⟨by simp [mem_ex33_U], ?_⟩ <;> { dsimp [d_abs_gauge, d_abs]; norm_num }
  · -- x = some 0
    have : ¬ (some (0 : ℝ) = some (-2) ∨ some (0 : ℝ) = some 2) := by intro h; rcases h with h | h <;> { injection h with h_eq; norm_num at h_eq }
    rw [if_neg this]
    ext y; simp only [Fib_single, id_op, id_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try rfl
      all_goals { dsimp [d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro rfl; refine ⟨by simp [mem_ex33_U], ?_⟩
      dsimp [d_abs_gauge, d_abs]; norm_num
  · -- x = some 2
    have : (some (2 : ℝ) = some (-2) ∨ some (2 : ℝ) = some 2) := Or.inr rfl
    rw [if_pos this]
    ext y; simp only [Fib_single, id_op, id_eq, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try { left; rfl } <;> try { right; rfl }
      all_goals { dsimp [d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro (rfl | rfl) <;> refine ⟨by simp [mem_ex33_U], ?_⟩ <;> { dsimp [d_abs_gauge, d_abs]; norm_num }

/-- CH03-P28-01: 习题 3.3 (i) 平移算子输入纤维分划 -/
theorem ex_3_3_i_trans_fiber (x : Option ℝ) (hx : x ∈ ex33_U) :
    Fib_single d_abs_gauge trans_op () (trans_op.func x) ex33_U =
      if x = some (-2) ∨ x = some 0 then {some (-2), some 0} else {x} := by
  rw [mem_ex33_U] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · -- x = some (-3)
    have : ¬ (some (-3 : ℝ) = some (-2) ∨ some (-3 : ℝ) = some 0) := by intro h; rcases h with h | h <;> { injection h with h_eq; norm_num at h_eq }
    rw [if_neg this]
    ext y; simp only [Fib_single, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try rfl
      all_goals { dsimp [trans_op, d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro rfl; refine ⟨by simp [mem_ex33_U], ?_⟩
      dsimp [trans_op, d_abs_gauge, d_abs]; norm_num
  · -- x = some (-2)
    have : (some (-2 : ℝ) = some (-2) ∨ some (-2 : ℝ) = some 0) := Or.inl rfl
    rw [if_pos this]
    ext y; simp only [Fib_single, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try { left; rfl } <;> try { right; rfl }
      all_goals { dsimp [trans_op, d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro (rfl | rfl) <;> refine ⟨by simp [mem_ex33_U], ?_⟩ <;> { dsimp [trans_op, d_abs_gauge, d_abs]; norm_num }
  · -- x = some 0
    have : (some (0 : ℝ) = some (-2) ∨ some (0 : ℝ) = some 0) := Or.inr rfl
    rw [if_pos this]
    ext y; simp only [Fib_single, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try { left; rfl } <;> try { right; rfl }
      all_goals { dsimp [trans_op, d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro (rfl | rfl) <;> refine ⟨by simp [mem_ex33_U], ?_⟩ <;> { dsimp [trans_op, d_abs_gauge, d_abs]; norm_num }
  · -- x = some 2
    have : ¬ (some (2 : ℝ) = some (-2) ∨ some (2 : ℝ) = some 0) := by intro h; rcases h with h | h <;> { injection h with h_eq; norm_num at h_eq }
    rw [if_neg this]
    ext y; simp only [Fib_single, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hdist⟩; rw [mem_ex33_U] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> try rfl
      all_goals { dsimp [trans_op, d_abs_gauge, d_abs] at hdist; norm_num at hdist }
    · rintro rfl; refine ⟨by simp [mem_ex33_U], ?_⟩
      dsimp [trans_op, d_abs_gauge, d_abs]; norm_num

noncomputable def eps32 : ENNReal := ENNReal.ofReal (3 / 2)

lemma eps32_pos : 0 < eps32 := by
  dsimp [eps32]; rw [ENNReal.ofReal_pos]; norm_num

/-- CH03-P28-02: 习题 3.3 (ii) 输入覆盖数等于2 -/
theorem ex_3_3_cov_U : covering_number d_abs eps32 ex33_U = 2 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 0, some 2 }
    have hnet : InternalEpsilonNet d_abs eps32 ex33_U centers := by
      dsimp [InternalEpsilonNet, centers, ex33_U]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · right; right; left; rfl
        · right; right; right; rfl
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_abs, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_abs, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
        · refine ⟨some 0, Finset.mem_insert_self _ _, ?_⟩
          dsimp [d_abs, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_abs, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_abs eps32 ex33_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_abs eps32 ex33_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 2 := by
      dsimp [centers]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · apply le_iInf; intro c
    apply le_iInf; intro hnet
    by_contra! hlt
    have hcard : c.card ≤ 1 := Nat.le_of_lt_succ (Nat.cast_lt.mp hlt)
    have hc_nonempty : c.Nonempty := by
      rcases hnet.2 (some 0) (by simp [mem_ex33_U]) with ⟨w, hw, _⟩
      exact ⟨w, hw⟩
    have hcard1 : c.card = 1 := le_antisymm hcard (Finset.Nonempty.card_pos hc_nonempty)
    rcases Finset.card_eq_one.mp hcard1 with ⟨c0, rfl⟩
    have hc0_in : c0 ∈ ex33_U := by
      have := hnet.1
      simp only [Finset.coe_singleton, Set.singleton_subset_iff] at this
      exact this
    rw [mem_ex33_U] at hc0_in
    rcases hc0_in with rfl | rfl | rfl | rfl
    · rcases hnet.2 (some 0) (by simp [mem_ex33_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_abs, eps32] at hd; norm_num at hd
    · rcases hnet.2 (some 0) (by simp [mem_ex33_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_abs, eps32] at hd; norm_num at hd
    · rcases hnet.2 (some 2) (by simp [mem_ex33_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_abs, eps32] at hd; norm_num at hd
    · rcases hnet.2 (some 0) (by simp [mem_ex33_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_abs, eps32] at hd; norm_num at hd

/-- CH03-P28-02: 习题 3.3 (ii) 输出覆盖数等于1 -/
theorem ex_3_3_cov_phi_U : covering_number d_abs eps32 (trans_op.func '' ex33_U) = 1 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some (-2) }
    have hnet : InternalEpsilonNet d_abs eps32 (trans_op.func '' ex33_U) centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_singleton] at hx; subst hx
        refine ⟨some (-3), by simp [mem_ex33_U], ?_⟩
        dsimp [trans_op]; congr 1; norm_num
      · rintro x ⟨y, hy, rfl⟩
        rw [mem_ex33_U] at hy
        refine ⟨some (-2), Finset.mem_singleton_self _, ?_⟩
        rcases hy with rfl | rfl | rfl | rfl <;> {
          dsimp [trans_op, d_abs, eps32]
          rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
          norm_num
        }
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_abs eps32 (trans_op.func '' ex33_U) s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_abs eps32 (trans_op.func '' ex33_U) centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 1 := Finset.card_singleton (some (-2))
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · have h_img_nonempty : (trans_op.func '' ex33_U).Nonempty := ⟨trans_op.func (some 0), ⟨some 0, by simp [mem_ex33_U], rfl⟩⟩
    exact one_le_covering_number_of_nonempty d_abs eps32 (trans_op.func '' ex33_U) h_img_nonempty

/-- CH03-P28-02: 习题 3.3 (ii) 映射熵差等于 -1 -/
theorem ex_3_3_entropy_diff :
    entropy_diff d_abs d_abs trans_op eps32 ex33_U = -1 := by
  dsimp [entropy_diff, metric_entropy]
  rw [ex_3_3_cov_phi_U, ex_3_3_cov_U]
  dsimp [log2_ereal]
  norm_num




-- ============================================================================
-- 习题 3.4: CH03-P29-01 ~ CH03-P29-05
-- ============================================================================

noncomputable def floor_func (r : ℝ) : ℝ :=
  if r < 1 then 0 else if r < 2 then 1 else 2

noncomputable def floor_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (floor_func r)
  preserves_bot := rfl

def ex34_Da : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ x = some r }
def ex34_Db : Set (Option ℝ) := { x | ∃ r : ℝ, 9 / 10 ≤ r ∧ r ≤ 11 / 10 ∧ x = some r }
def ex34_Dc : Set (Option ℝ) := { some 0, some 2 }
def ex34_Dd : Set (Option ℝ) := { x | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 2 ∧ x = some r }

-- Diameters
lemma diam_Da : diam d_real_bot ex34_Da = ENNReal.ofReal (1 / 2) := by
  dsimp [diam]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro ⟨rx, hrx0, hrx1, hx⟩
    apply iSup_le; intro y
    apply iSup_le; intro ⟨ry, hry0, hry1, hy⟩
    subst hx hy
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    have : abs (rx - ry) ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    exact this
  · refine le_iSup_of_le (some 0) ?_
    refine le_iSup_of_le ⟨0, by norm_num, by norm_num, rfl⟩ ?_
    refine le_iSup_of_le (some (1 / 2)) ?_
    refine le_iSup_of_le ⟨1 / 2, by norm_num, by norm_num, rfl⟩ ?_
    dsimp [d_real_bot]
    norm_num

lemma diam_Db : diam d_real_bot ex34_Db = ENNReal.ofReal (1 / 5) := by
  dsimp [diam]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro ⟨rx, hrx0, hrx1, hx⟩
    apply iSup_le; intro y
    apply iSup_le; intro ⟨ry, hry0, hry1, hy⟩
    subst hx hy
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    have : abs (rx - ry) ≤ 1 / 5 := by
      rw [abs_le]
      constructor <;> linarith
    exact this
  · refine le_iSup_of_le (some (9 / 10)) ?_
    refine le_iSup_of_le ⟨9 / 10, by norm_num, by norm_num, rfl⟩ ?_
    refine le_iSup_of_le (some (11 / 10)) ?_
    refine le_iSup_of_le ⟨11 / 10, by norm_num, by norm_num, rfl⟩ ?_
    dsimp [d_real_bot]
    have : abs (9 / 10 - 11 / 10 : ℝ) = 1 / 5 := by norm_num
    rw [this]

lemma diam_Dc : diam d_real_bot ex34_Dc = ENNReal.ofReal 2 := by
  dsimp [diam, ex34_Dc]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> {
      dsimp [d_real_bot]; norm_num
    }
  · refine le_iSup_of_le (some 0) ?_
    refine le_iSup_of_le (Or.inl rfl) ?_
    refine le_iSup_of_le (some 2) ?_
    refine le_iSup_of_le (Or.inr rfl) ?_
    dsimp [d_real_bot]; norm_num

lemma diam_Dd : diam d_real_bot ex34_Dd = ENNReal.ofReal 2 := by
  dsimp [diam]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro ⟨rx, hrx0, hrx1, hx⟩
    apply iSup_le; intro y
    apply iSup_le; intro ⟨ry, hry0, hry1, hy⟩
    subst hx hy
    dsimp [d_real_bot]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    have : abs (rx - ry) ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    exact this
  · refine le_iSup_of_le (some 0) ?_
    refine le_iSup_of_le ⟨0, by norm_num, by norm_num, rfl⟩ ?_
    refine le_iSup_of_le (some 2) ?_
    refine le_iSup_of_le ⟨2, by norm_num, by norm_num, rfl⟩ ?_
    dsimp [d_real_bot]; norm_num

-- Radii
lemma floor_op_Da (x : Option ℝ) (hx : x ∈ ex34_Da) : floor_op.func x = some 0 := by
  rcases hx with ⟨r, hr0, hr1, rfl⟩
  dsimp [floor_op, floor_func]
  have : r < 1 := by linarith
  rw [if_pos this]

lemma r_null_unif_Da : r_null_uniform d_real_bot d_real_bot floor_op ex34_Da = ⊤ := by
  dsimp [r_null_uniform]
  apply le_antisymm le_top
  apply le_iInf; intro y
  apply le_iInf; intro hy
  dsimp [r_null]
  rw [top_le_iff, sSup_eq_top]
  intro b hb
  rcases ENNReal.exists_nat_gt (ne_top_of_lt hb) with ⟨n, hn⟩
  refine ⟨n + 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · norm_num
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top n, ENNReal.one_lt_top⟩
  · intro x hx _
    rw [floor_op_Da x hx, floor_op_Da y hy]
    dsimp [d_real_bot]; norm_num
  · exact lt_of_lt_of_le hn (by simp)

lemma r_null_unif_Db : r_null_uniform d_real_bot d_real_bot floor_op ex34_Db = 0 := by
  dsimp [r_null_uniform]
  have h1_in : some 1 ∈ ex34_Db := ⟨1, by norm_num, by norm_num, rfl⟩
  refine le_antisymm ?_ (zero_le _)
  refine le_trans (biInf_le (fun y => r_null d_real_bot d_real_bot floor_op y ex34_Db) h1_in) ?_
  dsimp [r_null]
  apply sSup_le; intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  by_contra!
  by_cases h_large : ENNReal.ofReal (1 / 10) < r
  · have hx : some (9 / 10 : ℝ) ∈ ex34_Db := ⟨9 / 10, by norm_num, by norm_num, rfl⟩
    have hdist : d_real_bot (some (9 / 10 : ℝ)) (some 1) < r := by
      dsimp [d_real_bot]
      have : ENNReal.ofReal (abs (9 / 10 - 1 : ℝ)) = ENNReal.ofReal (1 / 10) := by norm_num
      rw [this]; exact h_large
    have hzero := hball (some (9 / 10 : ℝ)) hx hdist
    dsimp [floor_op, floor_func, d_real_bot] at hzero
    norm_num at hzero
  · have h_le : r ≤ ENNReal.ofReal (1 / 10) := le_of_not_gt h_large
    have hr_pos_real : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hrt.ne
    set delta := r.toReal / 2
    have hdelta_pos : 0 < delta := half_pos hr_pos_real
    have hdelta_lt : delta < r.toReal := half_lt_self hr_pos_real
    have h_r_real_le : r.toReal ≤ 1 / 10 := by
      rw [← ENNReal.ofReal_toReal hrt.ne] at h_le
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h_le
    have hdelta_le : delta ≤ 1 / 20 := by dsimp [delta]; linarith [h_r_real_le]
    set x_real := 1 - delta
    have hx_in : some x_real ∈ ex34_Db := by
      refine ⟨x_real, ?_, ?_, rfl⟩
      · dsimp [x_real]; linarith [hdelta_le]
      · dsimp [x_real]; linarith [hdelta_pos]
    have hdist : d_real_bot (some x_real) (some 1) < r := by
      dsimp [d_real_bot]
      have : abs (x_real - 1) = delta := by
        dsimp [x_real]; rw [sub_sub_cancel_left, abs_neg, abs_of_pos hdelta_pos]
      rw [this]
      have : ENNReal.ofReal delta < r := by
        rw [← ENNReal.ofReal_toReal hrt.ne]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hdelta_pos)).mpr hdelta_lt
      exact this
    have hzero := hball (some x_real) hx_in hdist
    dsimp [floor_op, floor_func, d_real_bot] at hzero
    have h_x_lt1 : x_real < 1 := by dsimp [x_real]; linarith [hdelta_pos]
    have h1_ge1 : ¬ ((1 : ℝ) < 1) := by norm_num
    have h1_lt2 : (1 : ℝ) < 2 := by norm_num
    rw [if_pos h_x_lt1, if_neg h1_ge1, if_pos h1_lt2] at hzero
    norm_num at hzero

lemma r_null_unif_Dc : r_null_uniform d_real_bot d_real_bot floor_op ex34_Dc = 2 := by
  dsimp [r_null_uniform]
  apply le_antisymm
  · have h0_in : some 0 ∈ ex34_Dc := Or.inl rfl
    refine le_trans (biInf_le (fun y => r_null d_real_bot d_real_bot floor_op y ex34_Dc) h0_in) ?_
    dsimp [r_null]
    apply sSup_le; intro r hr
    rcases hr with ⟨hr0, hrt, hball⟩
    by_contra! hgt
    have hdist : d_real_bot (some 2) (some 0) < r := by
      dsimp [d_real_bot]
      have : ENNReal.ofReal (abs (2 - 0 : ℝ)) = 2 := by norm_num
      rw [this]; exact hgt
    have hzero := hball (some 2) (Or.inr rfl) hdist
    dsimp [floor_op, floor_func, d_real_bot] at hzero
    norm_num at hzero
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    dsimp [r_null]
    refine le_trans ?_ (le_sSup (a := 2) ?_)
    · exact le_rfl
    · refine ⟨by norm_num, by norm_num, ?_⟩
      intro x hx hdist
      simp only [ex34_Dc, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · cases floor_op.func (some 0) <;> simp [d_real_bot]
      · dsimp [d_real_bot] at hdist
        have : ENNReal.ofReal (abs (0 - 2 : ℝ)) = 2 := by norm_num
        rw [this] at hdist
        exact False.elim (lt_irrefl 2 hdist)
      · dsimp [d_real_bot] at hdist
        have : ENNReal.ofReal (abs (2 - 0 : ℝ)) = 2 := by norm_num
        rw [this] at hdist
        exact False.elim (lt_irrefl 2 hdist)
      · cases floor_op.func (some 2) <;> simp [d_real_bot]

lemma ex34_Db_sub_Dd : ex34_Db ⊆ ex34_Dd := by
  rintro x ⟨r, hr0, hr1, rfl⟩
  exact ⟨r, by linarith, by linarith, rfl⟩

lemma r_null_unif_Dd : r_null_uniform d_real_bot d_real_bot floor_op ex34_Dd = 0 := by
  have hmono := prop_3_14_ii_b d_real_bot d_real_bot floor_op ex34_Db_sub_Dd
  rw [r_null_unif_Db] at hmono
  exact nonpos_iff_eq_zero.mp hmono

-- Types:
def tau_sigma : ENNReal := 1
def tau_N : ENNReal := 1

noncomputable def threshold_type (D : Set (Option ℝ)) : ℕ × ℕ :=
  (if diam d_real_bot D < tau_sigma then 1 else 0,
   if tau_N ≤ r_null_uniform d_real_bot d_real_bot floor_op D then 1 else 0)

theorem type_Da : threshold_type ex34_Da = (1, 1) := by
  dsimp [threshold_type, tau_sigma, tau_N]
  rw [diam_Da, r_null_unif_Da]
  have h1 : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)
  have h2 : 1 ≤ (⊤ : ENNReal) := le_top
  simp [h1, h2]

theorem type_Db : threshold_type ex34_Db = (1, 0) := by
  dsimp [threshold_type, tau_sigma, tau_N]
  rw [diam_Db, r_null_unif_Db]
  have h1 : ENNReal.ofReal (1 / 5) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)
  have h2 : ¬ ((1 : ENNReal) ≤ 0) := by norm_num
  simp [h1, h2]

theorem type_Dc : threshold_type ex34_Dc = (0, 1) := by
  dsimp [threshold_type, tau_sigma, tau_N]
  rw [diam_Dc, r_null_unif_Dc]
  have h1 : ¬ (ENNReal.ofReal 2 < 1) := by
    rw [← ENNReal.ofReal_one]
    intro h
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp h
    norm_num at this
  have h2 : (1 : ENNReal) ≤ 2 := by norm_num
  simp [h1, h2]

theorem type_Dd : threshold_type ex34_Dd = (0, 0) := by
  dsimp [threshold_type, tau_sigma, tau_N]
  rw [diam_Dd, r_null_unif_Dd]
  have h1 : ¬ (ENNReal.ofReal 2 < 1) := by
    rw [← ENNReal.ofReal_one]
    intro h
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp h
    norm_num at this
  have h2 : ¬ ((1 : ENNReal) ≤ 0) := by norm_num
  simp [h1, h2]

-- (ii) Counterexample to unif_radius ≥ 1 ⟹ global zero-dist
theorem ex_3_4_ii_counterexample :
    tau_N ≤ r_null_uniform d_real_bot d_real_bot floor_op ex34_Dc ∧
    ∃ x ∈ ex34_Dc, ∃ y ∈ ex34_Dc, 0 < d_real_bot (floor_op.func x) (floor_op.func y) := by
  dsimp [tau_N]
  rw [r_null_unif_Dc]
  refine ⟨by norm_num, some 0, Or.inl rfl, some 2, Or.inr rfl, ?_⟩
  dsimp [floor_op, floor_func, d_real_bot]
  norm_num



-- ============================================================================
-- 习题 3.5: CH03-P30-01 ~ CH03-P30-04
-- ============================================================================

def ex35_U : Set (Option ℝ) := { some 0, some 1, some 2, some 3 }

lemma mem_ex35_U (x : Option ℝ) : x ∈ ex35_U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 := by
  dsimp [ex35_U]; simp

noncomputable def ex35_f : Operator (Option ℝ) none where
  func := fun x => match x with
    | some r => if r = 0 then some 0 else if r = 1 then some 1 else if r = 2 then some 2 else if r = 3 then some 3 else none
    | none => none
  preserves_bot := rfl

noncomputable def ex35_g : Operator (Option ℝ) none where
  func := fun x => match x with
    | some r => if r = 0 then some 0 else if r = 1 then some 3 else if r = 2 then some 1 else if r = 3 then some 2 else none
    | none => none
  preserves_bot := rfl

lemma ex35_f_0 : ex35_f.func (some 0) = some 0 := by dsimp [ex35_f]; norm_num
lemma ex35_f_1 : ex35_f.func (some 1) = some 1 := by dsimp [ex35_f]; norm_num
lemma ex35_f_2 : ex35_f.func (some 2) = some 2 := by dsimp [ex35_f]; norm_num
lemma ex35_f_3 : ex35_f.func (some 3) = some 3 := by dsimp [ex35_f]; norm_num

lemma ex35_g_0 : ex35_g.func (some 0) = some 0 := by dsimp [ex35_g]; norm_num
lemma ex35_g_1 : ex35_g.func (some 1) = some 3 := by dsimp [ex35_g]; norm_num
lemma ex35_g_2 : ex35_g.func (some 2) = some 1 := by dsimp [ex35_g]; norm_num
lemma ex35_g_3 : ex35_g.func (some 3) = some 2 := by dsimp [ex35_g]; norm_num

-- ============================================================================
-- CH03-P30-01: 完整分段覆盖数与 3/2 不是合法内部中心
-- ============================================================================

theorem ex35_cov_gt_2 (ε : ENNReal) (hε : 2 < ε) :
    covering_number d_real_bot ε ex35_U = 1 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 1 }
    have hnet : InternalEpsilonNet d_real_bot ε ex35_U centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_coe, Finset.mem_singleton] at hx; subst hx; simp [mem_ex35_U]
      · intro x hx
        refine ⟨some 1, Finset.mem_singleton_self _, ?_⟩
        rw [mem_ex35_U] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> {
          dsimp [d_real_bot]; norm_num; exact lt_of_le_of_lt (by norm_num) hε
        }
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot ε ex35_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot ε ex35_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 1 := Finset.card_singleton _
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · exact one_le_covering_number_of_nonempty d_real_bot ε ex35_U ⟨some 0, by simp [mem_ex35_U]⟩

theorem ex35_cov_1_to_2 (ε : ENNReal) (h1 : 1 < ε) (h2 : ε ≤ 2) :
    covering_number d_real_bot ε ex35_U = 2 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 1, some 2 }
    have hnet : InternalEpsilonNet d_real_bot ε ex35_U centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [mem_ex35_U]
      · intro x hx
        rw [mem_ex35_U] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · refine ⟨some 1, Finset.mem_insert_self _ _, ?_⟩
          dsimp [d_real_bot]; norm_num; exact h1
        · refine ⟨some 1, Finset.mem_insert_self _ _, ?_⟩
          dsimp [d_real_bot]; norm_num; exact lt_trans (by norm_num) h1
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_real_bot]; norm_num; exact lt_trans (by norm_num) h1
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_real_bot]; norm_num; exact h1
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot ε ex35_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot ε ex35_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 2 := by
      dsimp [centers]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · apply le_iInf; intro c
    apply le_iInf; intro hnet
    by_contra! hlt
    have hcard : c.card ≤ 1 := Nat.le_of_lt_succ (Nat.cast_lt.mp hlt)
    have hc_nonempty : c.Nonempty := by
      rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨w, hw, _⟩
      exact ⟨w, hw⟩
    have hcard1 : c.card = 1 := le_antisymm hcard (Finset.Nonempty.card_pos hc_nonempty)
    rcases Finset.card_eq_one.mp hcard1 with ⟨c0, rfl⟩
    have hc0_in : c0 ∈ ex35_U := by
      have := hnet.1
      simp only [Finset.coe_singleton, Set.singleton_subset_iff] at this
      exact this
    rw [mem_ex35_U] at hc0_in
    rcases hc0_in with rfl | rfl | rfl | rfl
    · rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (3 : ENNReal) < ε := by norm_num at hd; exact hd
      have : (3 : ENNReal) < 2 := lt_of_lt_of_le (by assumption) h2
      norm_num at this
    · rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (2 : ENNReal) < ε := by norm_num at hd; exact hd
      exact (not_le_of_gt this) h2
    · rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (2 : ENNReal) < ε := by norm_num at hd; exact hd
      exact (not_le_of_gt this) h2
    · rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (3 : ENNReal) < ε := by norm_num at hd; exact hd
      have : (3 : ENNReal) < 2 := lt_of_lt_of_le (by assumption) h2
      norm_num at this

lemma unique_covered (x c0 : Option ℝ) (hx : x ∈ ex35_U) (hc0 : c0 ∈ ex35_U)
    (ε : ENNReal) (hd : d_real_bot x c0 < ε) (hε : ε ≤ 1) : x = c0 := by
  rw [mem_ex35_U] at hx hc0
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hc0 with rfl | rfl | rfl | rfl <;> try rfl
  all_goals {
    dsimp [d_real_bot] at hd
    norm_num at hd
    have : (1 : ENNReal) < ε := lt_of_le_of_lt (by norm_num) hd
    exact False.elim ((not_le_of_gt this) hε)
  }

lemma ex35_card_ge_4 (ε : ENNReal) (hε : ε ≤ 1) (c : Finset (Option ℝ))
    (hnet : InternalEpsilonNet d_real_bot ε ex35_U c) : 4 ≤ c.card := by
  rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨c0, hc0, hd0⟩
  rcases hnet.2 (some 1) (by simp [mem_ex35_U]) with ⟨c1, hc1, hd1⟩
  rcases hnet.2 (some 2) (by simp [mem_ex35_U]) with ⟨c2, hc2, hd2⟩
  rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨c3, hc3, hd3⟩
  have eq0 : some 0 = c0 := unique_covered (some 0) c0 (by simp [mem_ex35_U]) (hnet.1 hc0) ε hd0 hε
  have eq1 : some 1 = c1 := unique_covered (some 1) c1 (by simp [mem_ex35_U]) (hnet.1 hc1) ε hd1 hε
  have eq2 : some 2 = c2 := unique_covered (some 2) c2 (by simp [mem_ex35_U]) (hnet.1 hc2) ε hd2 hε
  have eq3 : some 3 = c3 := unique_covered (some 3) c3 (by simp [mem_ex35_U]) (hnet.1 hc3) ε hd3 hε
  subst eq0 eq1 eq2 eq3
  have hsub : ({some 0, some 1, some 2, some 3} : Finset (Option ℝ)) ⊆ c := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({some 0, some 1, some 2, some 3} : Finset (Option ℝ)).card = 4 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_singleton]
        · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
        rcases h with h | h <;> norm_num at h
    · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
      rcases h with h | h | h <;> norm_num at h
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem ex35_cov_le_1 (ε : ENNReal) (hε_pos : 0 < ε) (hε_le1 : ε ≤ 1) :
    covering_number d_real_bot ε ex35_U = 4 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 0, some 1, some 2, some 3 }
    have hnet : InternalEpsilonNet d_real_bot ε ex35_U centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [mem_ex35_U]
      · intro x hx
        rw [mem_ex35_U] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · refine ⟨some 0, Finset.mem_insert_self _ _, ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
        · refine ⟨some 1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
        · refine ⟨some 3, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))), ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot ε ex35_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot ε ex35_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 4 := by
      dsimp [centers]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
        · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
          rcases h with h | h <;> norm_num at h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
        rcases h with h | h | h <;> norm_num at h
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · apply le_iInf; intro c
    apply le_iInf; intro hnet
    exact_mod_cast ex35_card_ge_4 ε hε_le1 c hnet

theorem ex35_center_3_2_not_in_U : some (3 / 2 : ℝ) ∉ ex35_U := by
  intro h
  rw [mem_ex35_U] at h
  rcases h with h | h | h | h <;> {
    injection h with h_eq
    norm_num at h_eq
  }

-- ============================================================================
-- CH03-P30-02: 像集、覆盖数及熵差
-- ============================================================================

noncomputable def eps74 : ENNReal := ENNReal.ofReal (7 / 4)

theorem ex35_cov_at_7_4 : covering_number d_real_bot eps74 ex35_U = 2 := by
  apply ex35_cov_1_to_2
  · dsimp [eps74]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)
  · dsimp [eps74]
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)


theorem ex35_f_image : ex35_f.func '' ex35_U = ex35_U := by
  ext x
  simp only [Set.mem_image, mem_ex35_U]
  constructor
  · rintro ⟨y, rfl | rfl | rfl | rfl, rfl⟩
    · rw [ex35_f_0]; exact Or.inl rfl
    · rw [ex35_f_1]; exact Or.inr (Or.inl rfl)
    · rw [ex35_f_2]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [ex35_f_3]; exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨some 0, Or.inl rfl, ex35_f_0⟩
    · exact ⟨some 1, Or.inr (Or.inl rfl), ex35_f_1⟩
    · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), ex35_f_2⟩
    · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), ex35_f_3⟩

theorem ex35_g_image : ex35_g.func '' ex35_U = ex35_U := by
  ext x
  simp only [Set.mem_image, mem_ex35_U]
  constructor
  · rintro ⟨y, rfl | rfl | rfl | rfl, rfl⟩
    · rw [ex35_g_0]; exact Or.inl rfl
    · rw [ex35_g_1]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [ex35_g_2]; exact Or.inr (Or.inl rfl)
    · rw [ex35_g_3]; exact Or.inr (Or.inr (Or.inl rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨some 0, Or.inl rfl, ex35_g_0⟩
    · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), ex35_g_2⟩
    · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), ex35_g_3⟩
    · exact ⟨some 1, Or.inr (Or.inl rfl), ex35_g_1⟩

theorem ex35_cov_f_image (ε : ENNReal) :
    covering_number d_real_bot ε (ex35_f.func '' ex35_U) = covering_number d_real_bot ε ex35_U := by
  rw [ex35_f_image]

theorem ex35_cov_g_image (ε : ENNReal) :
    covering_number d_real_bot ε (ex35_g.func '' ex35_U) = covering_number d_real_bot ε ex35_U := by
  rw [ex35_g_image]

theorem ex35_entropy_diff_f :
    entropy_diff d_real_bot d_real_bot ex35_f eps74 ex35_U = 0 := by
  dsimp [entropy_diff]
  rw [ex35_f_image]
  have hE : metric_entropy d_real_bot eps74 ex35_U = (1 : EReal) := by
    dsimp [metric_entropy]; rw [ex35_cov_at_7_4]; dsimp [log2_ereal]; norm_num
  rw [hE]
  exact ereal_sub_self_of_ne_top_bot (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)

theorem ex35_entropy_diff_g :
    entropy_diff d_real_bot d_real_bot ex35_g eps74 ex35_U = 0 := by
  dsimp [entropy_diff]
  rw [ex35_g_image]
  have hE : metric_entropy d_real_bot eps74 ex35_U = (1 : EReal) := by
    dsimp [metric_entropy]; rw [ex35_cov_at_7_4]; dsimp [log2_ereal]; norm_num
  rw [hE]
  exact ereal_sub_self_of_ne_top_bot (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)

-- ============================================================================
-- CH03-P30-03: 最优标量 Lip 常数及下界
-- ============================================================================

theorem ex35_f_lip (x y : Option ℝ) (hx : x ∈ ex35_U) (hy : y ∈ ex35_U) :
    d_real_bot (ex35_f.func x) (ex35_f.func y) ≤ 1 * d_real_bot x y := by
  rw [one_mul]
  rw [mem_ex35_U] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> {
    try rw [ex35_f_0]
    try rw [ex35_f_1]
    try rw [ex35_f_2]
    try rw [ex35_f_3]
    try exact le_rfl
  }

theorem ex35_f_lip_lower (L : ENNReal)
    (hL : ∀ x ∈ ex35_U, ∀ y ∈ ex35_U, d_real_bot (ex35_f.func x) (ex35_f.func y) ≤ L * d_real_bot x y) :
    1 ≤ L := by
  have h := hL (some 0) (by simp [mem_ex35_U]) (some 1) (by simp [mem_ex35_U])
  rw [ex35_f_0, ex35_f_1] at h
  dsimp [d_real_bot] at h
  have hd1 : ENNReal.ofReal (abs (0 - 1 : ℝ)) = 1 := by norm_num
  rw [hd1, mul_one] at h
  exact h

theorem ex35_g_lip (x y : Option ℝ) (hx : x ∈ ex35_U) (hy : y ∈ ex35_U) :
    d_real_bot (ex35_g.func x) (ex35_g.func y) ≤ 3 * d_real_bot x y := by
  rw [mem_ex35_U] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> {
    try rw [ex35_g_0]
    try rw [ex35_g_1]
    try rw [ex35_g_2]
    try rw [ex35_g_3]
    dsimp [d_real_bot]
    norm_num
  }

theorem ex35_g_lip_lower (L : ENNReal)
    (hL : ∀ x ∈ ex35_U, ∀ y ∈ ex35_U, d_real_bot (ex35_g.func x) (ex35_g.func y) ≤ L * d_real_bot x y) :
    3 ≤ L := by
  have h := hL (some 0) (by simp [mem_ex35_U]) (some 1) (by simp [mem_ex35_U])
  rw [ex35_g_0, ex35_g_1] at h
  dsimp [d_real_bot] at h
  have hdg : ENNReal.ofReal (abs (0 - 3 : ℝ)) = 3 := by norm_num
  have hdin : ENNReal.ofReal (abs (0 - 1 : ℝ)) = 1 := by norm_num
  rw [hdg, hdin, mul_one] at h
  exact h

-- ============================================================================
-- CH03-P30-04: ε=7/4 代入一般上界与真实覆盖数比较
-- ============================================================================


theorem ex35_bound_f_at_7_4 :
    covering_number d_real_bot (eps74 / 1) ex35_U = 2 := by
  rw [ENNReal.div_eq_inv_mul, inv_one, one_mul]
  exact ex35_cov_at_7_4

theorem ex35_bound_g_at_7_4 :
    covering_number d_real_bot (eps74 / 3) ex35_U = 4 := by
  apply ex35_cov_le_1
  · dsimp [eps74]
    have : 0 < (7 / 4 : ℝ) := by norm_num
    have h_pos : 0 < ENNReal.ofReal (7 / 4) := (ENNReal.ofReal_pos).mpr this
    exact ENNReal.div_pos h_pos.ne' (by norm_num)
  · rw [ENNReal.div_le_iff (by norm_num) (by norm_num), one_mul]
    dsimp [eps74]
    have h3 : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_num
    rw [h3]
    exact ENNReal.ofReal_le_ofReal (by norm_num)

-- Comparison:
-- For f: bound is 2, actual is 2 (equality)
theorem ex35_compare_f :
    covering_number d_real_bot eps74 (ex35_f.func '' ex35_U) =
    covering_number d_real_bot (eps74 / 1) ex35_U := by
  rw [ex35_f_image, ex35_bound_f_at_7_4, ex35_cov_at_7_4]

-- For g: actual is 2, bound is 4 (strictly smaller)
theorem ex35_compare_g :
    covering_number d_real_bot eps74 (ex35_g.func '' ex35_U) <
    covering_number d_real_bot (eps74 / 3) ex35_U := by
  rw [ex35_g_image, ex35_cov_at_7_4, ex35_bound_g_at_7_4]
  norm_num



end OperatorLocalDegeneracy
