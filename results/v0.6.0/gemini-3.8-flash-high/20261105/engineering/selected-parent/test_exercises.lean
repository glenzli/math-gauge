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


