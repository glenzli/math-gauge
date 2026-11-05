import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D04: 点态零化半径 -/
noncomputable def r_null (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_single (ϕ : Operator X bot) (i j : I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (d j) ϕ y U

noncomputable def r_null_subfamily (ϕ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (subfamily_pseudometric d J) ϕ y U

/-- CH03-D05: 统一半径与零化矩阵 -/
noncomputable def r_null_uniform (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

noncomputable def N_matrix (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  r_null_uniform (d i) (d j) ϕ U

noncomputable def r_null_subfamily_uniform (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  r_null_uniform (d i) (subfamily_pseudometric d J) ϕ U

/- ====================================================================
   Counterexample 3.1: CH03-P10-01, CH03-P10-02, CH03-P10-03
   ==================================================================== -/

noncomputable def d_real_bot (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (|a - b|)
  | _, _ => ⊤

lemma d_real_bot_self (x : Option ℝ) : d_real_bot x x = 0 := by
  cases x <;> simp [d_real_bot]

lemma d_real_bot_symm (x y : Option ℝ) : d_real_bot x y = d_real_bot y x := by
  cases x <;> cases y <;> simp [d_real_bot, abs_sub_comm]

lemma d_real_bot_triangle (x y z : Option ℝ) : d_real_bot x z ≤ d_real_bot x y + d_real_bot y z := by
  cases x <;> cases y <;> cases z <;> simp [d_real_bot]
  rename_i a b c
  have h := abs_sub_le a b c
  have h2 : ENNReal.ofReal (|a - c|) ≤ ENNReal.ofReal (|a - b| + |b - c|) :=
    ENNReal.ofReal_le_ofReal h
  exact le_trans h2 (ENNReal.ofReal_add_le)

lemma d_real_bot_isolate_bot (x : Option ℝ) (hx : x ≠ none) : d_real_bot x none = ⊤ := by
  cases x <;> [contradiction; rfl]

instance instExtendedPseudoMetricRealBot : ExtendedPseudoMetric (Option ℝ) none d_real_bot where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := d_real_bot_self
  symm := d_real_bot_symm
  triangle := d_real_bot_triangle
  isolate_bot := d_real_bot_isolate_bot

noncomputable def step_func (x : Option ℝ) : Option ℝ :=
  match x with
  | none => none
  | some r => if r > 0 then some 1 else some 0

noncomputable def step_op : Operator (Option ℝ) none where
  func := step_func
  preserves_bot := rfl

def U_step : Set (Option ℝ) :=
  { y | ∃ r : ℝ, y = some r ∧ ((-1 ≤ r ∧ r < 0) ∨ (0 < r ∧ r ≤ 1)) }

/-- CH03-P10-01: 反例 3.1 构造带吸收元的通常实线和阶跃算子，验证合法结构和U的域条件 -/
theorem prop_3_10_01 :
    (none : Option ℝ) ∉ U_step ∧
    U_step.Nonempty ∧
    step_op.func none = none ∧
    ExtendedPseudoMetric (Option ℝ) none d_real_bot := by
  refine ⟨?_, ?_, rfl, instExtendedPseudoMetricRealBot⟩
  · intro ⟨r, hr, _⟩; contradiction
  · exact ⟨some 1, ⟨1, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩⟩

def step_admissible (y : Option ℝ) : Set ENNReal :=
  { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U_step, d_real_bot x y < r → d_real_bot (step_op.func x) (step_op.func y) = 0 }

lemma step_func_pos {r : ℝ} (hr : 0 < r) : step_func (some r) = some 1 := by
  dsimp [step_func]; rw [if_pos hr]

lemma step_func_neg {r : ℝ} (hr : r < 0) : step_func (some r) = some 0 := by
  dsimp [step_func]; rw [if_neg (by linarith)]

lemma d_real_bot_some (a b : ℝ) : d_real_bot (some a) (some b) = ENNReal.ofReal (|a - b|) := rfl

lemma step_admissible_eq (y0 : ℝ) (hy : some y0 ∈ U_step) :
    step_admissible (some y0) = { r : ENNReal | 0 < r ∧ r ≤ ENNReal.ofReal (|y0|) } := by
  rcases hy with ⟨r0, hr0, hcase⟩
  cases Option.some.inj hr0
  ext r
  simp only [step_admissible, Set.mem_setOf_eq]
  have hy_ne : y0 ≠ 0 := by
    rcases hcase with ⟨_, h1⟩ | ⟨h1, _⟩
    · exact ne_of_lt h1
    · exact ne_of_gt h1
  have hy_abs_pos : 0 < |y0| := abs_pos.mpr hy_ne
  have hy_ofReal_pos : 0 < ENNReal.ofReal (|y0|) := by
    rwa [ENNReal.ofReal_pos]
  have hy_ofReal_ne_top : ENNReal.ofReal (|y0|) < ⊤ := ENNReal.ofReal_lt_top
  constructor
  · rintro ⟨hr0, hrt, hball⟩
    refine ⟨hr0, ?_⟩
    by_contra! hgt
    rcases hcase with ⟨hneg1, hneg2⟩ | ⟨hpos1, hpos2⟩
    · have habs : |y0| = -y0 := abs_of_neg hneg2
      rw [habs] at hgt
      lift r to NNReal using (ne_of_lt hrt)
      have hr_real : -y0 < (r : ℝ) := by
        have := (ENNReal.ofReal_lt_coe_iff (by linarith)).mp hgt
        exact this
      set x0 := min (1 : ℝ) (((r : ℝ) + y0) / 2)
      have hx0_pos : 0 < x0 := by
        apply lt_min (by norm_num)
        linarith
      have hx0_le1 : x0 ≤ 1 := min_le_left 1 _
      have hx_mem : some x0 ∈ U_step := by
        exact ⟨x0, rfl, Or.inr ⟨hx0_pos, hx0_le1⟩⟩
      have hdist : d_real_bot (some x0) (some y0) < r := by
        rw [d_real_bot_some]
        have hdiff : |x0 - y0| = x0 - y0 := abs_of_pos (by linarith)
        rw [hdiff]
        have hx0_le : x0 ≤ ((r : ℝ) + y0) / 2 := min_le_right 1 _
        have hle : x0 - y0 < (r : ℝ) := by linarith
        have hr_pos : 0 < (r : ℝ) := by linarith
        rw [← ENNReal.ofReal_coe_nnreal]
        rw [ENNReal.ofReal_lt_ofReal_iff hr_pos]
        exact hle
      have hzero := hball (some x0) hx_mem hdist
      dsimp [step_op] at hzero
      rw [step_func_pos hx0_pos, step_func_neg hneg2] at hzero
      revert hzero
      simp [d_real_bot]
    · have habs : |y0| = y0 := abs_of_pos hpos1
      rw [habs] at hgt
      lift r to NNReal using (ne_of_lt hrt)
      have hr_real : y0 < (r : ℝ) := by
        have := (ENNReal.ofReal_lt_coe_iff (by linarith)).mp hgt
        exact this
      set x0 := max (-1 : ℝ) ((y0 - (r : ℝ)) / 2)
      have hx0_neg : x0 < 0 := by
        apply max_lt (by norm_num)
        linarith
      have hx0_ge : -1 ≤ x0 := le_max_left (-1) _
      have hx_mem : some x0 ∈ U_step := by
        exact ⟨x0, rfl, Or.inl ⟨hx0_ge, hx0_neg⟩⟩
      have hdist : d_real_bot (some x0) (some y0) < r := by
        rw [d_real_bot_some]
        have hdiff : |x0 - y0| = y0 - x0 := by
          rw [abs_sub_comm]
          exact abs_of_pos (by linarith)
        rw [hdiff]
        have hx0_ge2 : (y0 - (r : ℝ)) / 2 ≤ x0 := le_max_right (-1) _
        have hle : y0 - x0 < (r : ℝ) := by linarith
        have hr_pos : 0 < (r : ℝ) := by linarith
        rw [← ENNReal.ofReal_coe_nnreal]
        rw [ENNReal.ofReal_lt_ofReal_iff hr_pos]
        exact hle
      have hzero := hball (some x0) hx_mem hdist
      dsimp [step_op] at hzero
      rw [step_func_neg hx0_neg, step_func_pos hpos1] at hzero
      revert hzero
      simp [d_real_bot]
  · rintro ⟨hr0, hrle⟩
    have hrt : r < ⊤ := lt_of_le_of_lt hrle hy_ofReal_ne_top
    refine ⟨hr0, hrt, ?_⟩
    intro x hx hdist
    rcases hx with ⟨x0, rfl, hxcase⟩
    rw [d_real_bot_some] at hdist
    have hdist_real : |x0 - y0| < |y0| := by
      have h1 : ENNReal.ofReal (|x0 - y0|) < ENNReal.ofReal (|y0|) :=
        lt_of_lt_of_le hdist hrle
      rwa [ENNReal.ofReal_lt_ofReal_iff (abs_pos.mpr hy_ne)] at h1
    rcases hcase with ⟨hneg1, hneg2⟩ | ⟨hpos1, hpos2⟩
    · have habs : |y0| = -y0 := abs_of_neg hneg2
      rw [habs] at hdist_real
      have hx0_neg : x0 < 0 := by
        by_contra! hge
        have : -y0 ≤ |x0 - y0| := by
          rw [abs_of_pos (by linarith)]
          linarith
        linarith
      dsimp [step_op]
      rw [step_func_neg hx0_neg, step_func_neg hneg2]
      simp [d_real_bot]
    · have habs : |y0| = y0 := abs_of_pos hpos1
      rw [habs] at hdist_real
      have hx0_pos : 0 < x0 := by
        by_contra! hle
        have : y0 ≤ |x0 - y0| := by
          rw [abs_sub_comm, abs_of_pos (by linarith)]
          linarith
        linarith
      dsimp [step_op]
      rw [step_func_pos hx0_pos, step_func_pos hpos1]
      simp [d_real_bot]

lemma sSup_Ioc_eq (c : ENNReal) (hc0 : 0 < c) :
    sSup { r : ENNReal | 0 < r ∧ r ≤ c } = c := by
  apply le_antisymm
  · apply sSup_le
    intro x hx
    exact hx.2
  · apply le_sSup
    exact ⟨hc0, le_refl c⟩

/-- CH03-P10-02: 反例 3.1 每个y∈U的合法有限正半径恰为(0,|y|]，故点态半径=|y|>0 -/
theorem prop_3_10_02 (y0 : ℝ) (hy : some y0 ∈ U_step) :
    step_admissible (some y0) = { r : ENNReal | 0 < r ∧ r ≤ ENNReal.ofReal (|y0|) } ∧
    r_null d_real_bot d_real_bot step_op (some y0) U_step = ENNReal.ofReal (|y0|) ∧
    0 < ENNReal.ofReal (|y0|) := by
  have hadm := step_admissible_eq y0 hy
  have hy_ne : y0 ≠ 0 := by
    rcases hy with ⟨r0, hr0, ⟨_, h1⟩ | ⟨h1, _⟩⟩
    · cases Option.some.inj hr0; exact ne_of_lt h1
    · cases Option.some.inj hr0; exact ne_of_gt h1
  have hy_pos : 0 < ENNReal.ofReal (|y0|) := by
    rwa [ENNReal.ofReal_pos, abs_pos]
  refine ⟨hadm, ?_, hy_pos⟩
  dsimp [r_null]
  change sSup (step_admissible (some y0)) = ENNReal.ofReal (|y0|)
  rw [hadm]
  exact sSup_Ioc_eq _ hy_pos

lemma eq_zero_of_forall_le (a : ENNReal) (h : ∀ ε : ENNReal, 0 < ε → a ≤ ε) : a = 0 := by
  by_contra ha
  have hpos : 0 < a := pos_iff_ne_zero.mpr ha
  rcases exists_between hpos with ⟨b, hb0, hba⟩
  have := h b hb0
  exact (lt_self_iff_false _).mp (lt_of_lt_of_le hba this)

/-- CH03-P10-03: 反例 3.1 用趋零基点证明同一固定U上的统一半径为0 -/
theorem prop_3_10_03 :
    r_null_uniform d_real_bot d_real_bot step_op U_step = 0 := by
  apply eq_zero_of_forall_le
  intro ε hε
  by_cases htop : ε = ⊤
  · rw [htop]; exact le_top
  lift ε to NNReal using htop
  have hε_pos : 0 < (ε : ℝ) := by
    rwa [ENNReal.coe_pos] at hε
  rcases exists_nat_gt (1 / (ε : ℝ)) with ⟨n, hn⟩
  set y0 : ℝ := 1 / ((n : ℝ) + 2)
  have hy0_pos : 0 < y0 := by
    apply div_pos (by norm_num)
    linarith
  have hy0_le1 : y0 ≤ 1 := by
    dsimp [y0]
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hy_mem : some y0 ∈ U_step := by
    exact ⟨y0, rfl, Or.inr ⟨hy0_pos, hy0_le1⟩⟩
  have hr_y0 : r_null d_real_bot d_real_bot step_op (some y0) U_step = ENNReal.ofReal y0 := by
    have h_abs : |y0| = y0 := abs_of_pos hy0_pos
    have h := (prop_3_10_02 y0 hy_mem).2.1
    rw [h_abs] at h
    exact h
  have h_inf_le : r_null_uniform d_real_bot d_real_bot step_op U_step ≤ r_null d_real_bot d_real_bot step_op (some y0) U_step := by
    dsimp [r_null_uniform]
    exact biInf_le (fun y => r_null d_real_bot d_real_bot step_op y U_step) hy_mem
  have h_le_eps : y0 ≤ (ε : ℝ) := by
    have h1 : 1 < (n : ℝ) * (ε : ℝ) := (div_lt_iff₀ hε_pos).mp hn
    have h2 : (n : ℝ) * (ε : ℝ) < ((n : ℝ) + 2) * (ε : ℝ) :=
      mul_lt_mul_of_pos_right (by linarith) hε_pos
    have h3 : 1 < ((n : ℝ) + 2) * (ε : ℝ) := lt_trans h1 h2
    dsimp [y0]
    rw [div_le_iff₀ (by linarith)]
    linarith
  rw [hr_y0] at h_inf_le
  refine le_trans h_inf_le ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal_iff NNReal.zero_le_coe).mpr h_le_eps

/- ====================================================================
   Proposition 3.8: CH03-P11-01, CH03-P11-02, CH03-P11-03
   ==================================================================== -/

/-- CH03-P11-01: 命题 3.8 (i-a) 输出子族常值时每个像目标纤维等于U -/
theorem prop_3_8_i_a (ϕ : Operator X bot) (U : Set X) (J : Set I) (hJ : J ⊆ I_const d ϕ U)
    (y : X) (hy : y ∈ ϕ.func '' U) :
    Fib d ϕ J y U = U := by
  ext x
  simp only [Fib, Set.mem_setOf_eq]
  rcases hy with ⟨x0, hx0, rfl⟩
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    dsimp [subfamily_pseudometric]
    rw [← ENNReal.bot_eq_zero, iSup_eq_bot]
    intro ⟨j, hj⟩
    exact hJ hj x hx x0 hx0

/-- CH03-P11-02: 命题 3.8 (i-b) 任意输入分量的点态与统一半径均为无穷 -/
theorem prop_3_8_i_b_ptwise (ϕ : Operator X bot) (U : Set X) (i : I) (J : Set I)
    (hJ : J ⊆ I_const d ϕ U) (y : X) (hy : y ∈ U) :
    r_null_subfamily d ϕ i J y U = ⊤ := by
  dsimp [r_null_subfamily, r_null]
  apply sSup_eq_top.mpr
  intro b hb
  rcases exists_between hb with ⟨r, hbr, hrt⟩
  refine ⟨r, ⟨?_, hrt, ?_⟩, hbr⟩
  · exact lt_of_le_of_lt bot_le hbr
  · intro x hx _
    dsimp [subfamily_pseudometric]
    rw [← ENNReal.bot_eq_zero, iSup_eq_bot]
    intro ⟨j, hj⟩
    exact hJ hj x hx y hy

theorem prop_3_8_i_b_uniform (ϕ : Operator X bot) (U : Set X) (i : I) (J : Set I)
    (hJ : J ⊆ I_const d ϕ U) :
    r_null_subfamily_uniform d ϕ i J U = ⊤ := by
  dsimp [r_null_subfamily_uniform, r_null_uniform]
  rw [iInf_eq_top]
  intro y
  rw [iInf_eq_top]
  intro hy
  exact prop_3_8_i_b_ptwise d ϕ U i J hJ y hy

def inf_two_pt_d (i : Fin 2) (x y : Option (Fin 2)) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => if a = b then 0 else ⊤
  | _, _ => ⊤

lemma inf_two_pt_d_self (i : Fin 2) (x : Option (Fin 2)) : inf_two_pt_d i x x = 0 := by
  cases x <;> simp [inf_two_pt_d]

lemma inf_two_pt_d_symm (i : Fin 2) (x y : Option (Fin 2)) : inf_two_pt_d i x y = inf_two_pt_d i y x := by
  cases x <;> cases y <;> simp [inf_two_pt_d, eq_comm]

lemma inf_two_pt_d_tri (i : Fin 2) (x y z : Option (Fin 2)) : inf_two_pt_d i x z ≤ inf_two_pt_d i x y + inf_two_pt_d i y z := by
  cases x <;> cases y <;> cases z <;> simp [inf_two_pt_d]
  rename_i a b c
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

lemma inf_two_pt_d_iso (i : Fin 2) (x : Option (Fin 2)) (hx : x ≠ none) : inf_two_pt_d i x none = ⊤ := by
  cases x <;> [contradiction; rfl]

instance instInfTwoPtMetric (i : Fin 2) : ExtendedPseudoMetric (Option (Fin 2)) none (inf_two_pt_d i) where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := inf_two_pt_d_self i
  symm := inf_two_pt_d_symm i
  triangle := inf_two_pt_d_tri i
  isolate_bot := inf_two_pt_d_iso i

def inf_two_pt_op : Operator (Option (Fin 2)) none where
  func := id
  preserves_bot := rfl

def inf_two_pt_U : Set (Option (Fin 2)) := { some 0, some 1 }

lemma mem_inf_two_pt_U (x : Option (Fin 2)) : x ∈ inf_two_pt_U ↔ x = some 0 ∨ x = some 1 := by
  dsimp [inf_two_pt_U]; simp

/-- CH03-P11-03: 命题 3.8 (ii) 合法两点无穷输入距离反例，包括i=j和i≠j，证明无穷统一半径不推出常值 -/
theorem prop_3_8_ii_counterexample :
    (∀ i j : Fin 2, r_null_uniform (inf_two_pt_d i) (inf_two_pt_d j) inf_two_pt_op inf_two_pt_U = ⊤) ∧
    (∀ j : Fin 2, j ∉ I_const inf_two_pt_d inf_two_pt_op inf_two_pt_U) ∧
    (none : Option (Fin 2)) ∉ inf_two_pt_U ∧
    inf_two_pt_U.Nonempty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    dsimp [r_null_uniform, r_null]
    rw [iInf_eq_top]
    intro y
    rw [iInf_eq_top]
    intro hy
    apply sSup_eq_top.mpr
    intro b hb
    rcases exists_between hb with ⟨r, hbr, hrt⟩
    refine ⟨r, ⟨?_, hrt, ?_⟩, hbr⟩
    · exact lt_of_le_of_lt bot_le hbr
    · intro x hx hdist
      rw [mem_inf_two_pt_U] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · simp [inf_two_pt_d, inf_two_pt_op]
      · exfalso
        dsimp [inf_two_pt_d] at hdist
        exact (not_top_lt (lt_trans hdist hrt)).elim
      · exfalso
        dsimp [inf_two_pt_d] at hdist
        exact (not_top_lt (lt_trans hdist hrt)).elim
      · simp [inf_two_pt_d, inf_two_pt_op]
  · intro j hj
    dsimp [I_const] at hj
    have h0 : (some 0 : Option (Fin 2)) ∈ inf_two_pt_U := by rw [mem_inf_two_pt_U]; left; rfl
    have h1 : (some 1 : Option (Fin 2)) ∈ inf_two_pt_U := by rw [mem_inf_two_pt_U]; right; rfl
    have h01 := hj (some 0) h0 (some 1) h1
    dsimp [inf_two_pt_d, inf_two_pt_op] at h01
    contradiction
  · intro h
    rw [mem_inf_two_pt_U] at h
    rcases h with h | h <;> contradiction
  · exact ⟨some 0, by rw [mem_inf_two_pt_U]; left; rfl⟩

/- ====================================================================
   Proposition 3.9: CH03-P12-01, CH03-P12-02
   ==================================================================== -/

/-- CH03-P12-01: 命题 3.9 (i) 恒等分量的像目标纤维等于输入零距类 -/
theorem prop_3_9_i (ϕ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ I_id d ϕ U) (y : X) (hy : y ∈ U)
    [hE : ExtendedPseudoMetric X bot (d i)] :
    Fib_single d ϕ i (ϕ.func y) U = { x ∈ U | d i x y = 0 } := by
  ext x
  simp only [Fib_single, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, ?_⟩
    have h_x_id : d i (ϕ.func x) x = 0 := hi.2 x hx
    have h_y_id : d i (ϕ.func y) y = 0 := hi.2 y hy
    have h1 : d i x y ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := hE.triangle x (ϕ.func x) y
    have h2 : d i (ϕ.func x) y ≤ d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y := hE.triangle (ϕ.func x) (ϕ.func y) y
    rw [hE.symm x (ϕ.func x), h_x_id, zero_add] at h1
    rw [hzero, h_y_id, add_zero] at h2
    exact le_antisymm (le_trans h1 h2) bot_le
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, ?_⟩
    have h_x_id : d i (ϕ.func x) x = 0 := hi.2 x hx
    have h_y_id : d i (ϕ.func y) y = 0 := hi.2 y hy
    have h1 : d i (ϕ.func x) (ϕ.func y) ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := hE.triangle (ϕ.func x) x (ϕ.func y)
    have h2 : d i x (ϕ.func y) ≤ d i x y + d i y (ϕ.func y) := hE.triangle x y (ϕ.func y)
    rw [h_x_id, zero_add] at h1
    rw [hzero, hE.symm y (ϕ.func y), h_y_id, add_zero] at h2
    exact le_antisymm (le_trans h1 h2) bot_le

/-- CH03-P12-02: 命题 3.9 (ii) 有限正r0球内仅零距时，点态零化半径≥r0>0 -/
theorem prop_3_9_ii (ϕ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ I_id d ϕ U) (y : X) (hy : y ∈ U)
    [hE : ExtendedPseudoMetric X bot (d i)]
    (r0 : ENNReal) (hr0_pos : 0 < r0) (hr0_top : r0 < ⊤)
    (h_ball : ∀ x ∈ U, d i x y < r0 → d i x y = 0) :
    r0 ≤ r_null (d i) (d i) ϕ y U ∧ 0 < r_null (d i) (d i) ϕ y U := by
  have hr0_adm : r0 ∈ { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → d i (ϕ.func x) (ϕ.func y) = 0 } := by
    refine ⟨hr0_pos, hr0_top, ?_⟩
    intro x hx hdist
    have h_in_zero := h_ball x hx hdist
    have h_x_id : d i (ϕ.func x) x = 0 := hi.2 x hx
    have h_y_id : d i (ϕ.func y) y = 0 := hi.2 y hy
    have h1 : d i (ϕ.func x) (ϕ.func y) ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := hE.triangle (ϕ.func x) x (ϕ.func y)
    have h2 : d i x (ϕ.func y) ≤ d i x y + d i y (ϕ.func y) := hE.triangle x y (ϕ.func y)
    rw [h_x_id, zero_add] at h1
    rw [h_in_zero, hE.symm y (ϕ.func y), h_y_id, add_zero] at h2
    exact le_antisymm (le_trans h1 h2) bot_le
  have h_le : r0 ≤ r_null (d i) (d i) ϕ y U := le_sSup hr0_adm
  exact ⟨h_le, lt_of_lt_of_le hr0_pos h_le⟩

/- ====================================================================
   Proposition 3.10: CH03-P13-01, CH03-P13-02, CH03-P13-03
   ==================================================================== -/

/-- CH03-P13-01: 命题 3.10 有限非空输出子族的点态半径等于单分量半径最小值 -/
theorem prop_3_10_ptwise_min (ϕ : Operator X bot) (i : I) (J : Set I) (hJ : J.Nonempty)
    (y : X) (U : Set X) :
    r_null_subfamily d ϕ i J y U = ⨅ j ∈ J, r_null (d i) (d j) ϕ y U := by
  apply le_antisymm
  · apply le_iInf; intro j
    apply le_iInf; intro hj
    dsimp [r_null_subfamily, r_null]
    apply sSup_le_sSup
    intro r hr
    rcases hr with ⟨hr0, hrt, hball⟩
    refine ⟨hr0, hrt, ?_⟩
    intro x hx hdist
    have hzero := hball x hx hdist
    dsimp [subfamily_pseudometric] at hzero
    rw [← ENNReal.bot_eq_zero, iSup_eq_bot] at hzero
    exact hzero ⟨j, hj⟩
  · set m := ⨅ j ∈ J, r_null (d i) (d j) ϕ y U
    dsimp [r_null_subfamily, r_null]
    by_cases hm0 : m = 0
    · rw [hm0]; exact bot_le
    by_contra! hlt
    rcases exists_between hlt with ⟨c, hc_sup, hc_m⟩
    have hc0 : 0 < c := lt_of_le_of_lt bot_le hc_sup
    have hc_top : c < ⊤ := by
      by_contra! hct
      have : c = ⊤ := top_le_iff.mp hct
      subst this
      exact (not_top_lt hc_m).elim
    have hc_adm : c ∈ { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → subfamily_pseudometric d J (ϕ.func x) (ϕ.func y) = 0 } := by
      refine ⟨hc0, hc_top, ?_⟩
      intro x hx hdist
      dsimp [subfamily_pseudometric]
      rw [← ENNReal.bot_eq_zero, iSup_eq_bot]
      intro ⟨j, hj⟩
      have hj_lt : c < r_null (d i) (d j) ϕ y U := lt_of_lt_of_le hc_m (biInf_le (fun j => r_null (d i) (d j) ϕ y U) hj)
      dsimp [r_null] at hj_lt
      rcases lt_sSup_iff.mp hj_lt with ⟨rj, hrj_adm, hcrj⟩
      exact hrj_adm.2.2 x hx (lt_trans hdist hcrj)
    have hc_le : c ≤ sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → subfamily_pseudometric d J (ϕ.func x) (ϕ.func y) = 0 } :=
      le_sSup hc_adm
    exact (lt_self_iff_false c).mp (lt_of_le_of_lt hc_le hc_sup)

/-- CH03-P13-02: 命题 3.10 交换基点下确界与有限非空最小值，得到统一半径公式 -/
theorem prop_3_10_uniform_min (ϕ : Operator X bot) (i : I) (J : Set I) (hJ : J.Nonempty) (U : Set X) :
    r_null_subfamily_uniform d ϕ i J U = ⨅ j ∈ J, N_matrix d ϕ U i j := by
  dsimp [r_null_subfamily_uniform, r_null_uniform, N_matrix]
  have h_ptwise : (⨅ y ∈ U, r_null_subfamily d ϕ i J y U) = ⨅ y ∈ U, ⨅ j ∈ J, r_null (d i) (d j) ϕ y U := by
    congr 1; ext y
    congr 1; ext hy
    exact prop_3_10_ptwise_min d ϕ i J hJ y U
  change (⨅ y ∈ U, r_null_subfamily d ϕ i J y U) = _
  rw [h_ptwise]
  apply le_antisymm
  · apply le_iInf; intro j
    apply le_iInf; intro hj
    apply le_iInf; intro y
    apply le_iInf; intro hy
    have h1 := biInf_le (fun y => ⨅ j ∈ J, r_null (d i) (d j) ϕ y U) hy
    have h2 := biInf_le (fun j => r_null (d i) (d j) ϕ y U) hj
    exact le_trans h1 h2
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    apply le_iInf; intro j
    apply le_iInf; intro hj
    have h1 := biInf_le (fun j => ⨅ y ∈ U, r_null (d i) (d j) ϕ y U) hj
    have h2 := biInf_le (fun y => r_null (d i) (d j) ϕ y U) hy
    exact le_trans h1 h2

/-- CH03-P13-03: 命题 3.10 J⊆K时统一半径关于输出子族反单调 -/
theorem prop_3_10_antimono (ϕ : Operator X bot) (i : I) (J K : Set I) (hJK : J ⊆ K) (U : Set X) :
    r_null_subfamily_uniform d ϕ i K U ≤ r_null_subfamily_uniform d ϕ i J U := by
  dsimp [r_null_subfamily_uniform, r_null_uniform, r_null_subfamily, r_null]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  refine le_trans (biInf_le (fun y => sSup {r | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → subfamily_pseudometric d K (ϕ.func x) (ϕ.func y) = 0}) hy) ?_
  apply sSup_le_sSup
  intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  refine ⟨hr0, hrt, ?_⟩
  intro x hx hdist
  have hzero := hball x hx hdist
  dsimp [subfamily_pseudometric] at hzero ⊢
  rw [← ENNReal.bot_eq_zero, iSup_eq_bot] at hzero ⊢
  intro ⟨j, hj⟩
  exact hzero ⟨j, hJK hj⟩

/- ====================================================================
   Proposition 3.11: CH03-P14-01, CH03-P14-02, CH03-P14-03
   ==================================================================== -/

/-- CH03-P14-01: 命题 3.11 纤维成员条件推出输出零距 -/
theorem prop_3_11_fiber_zero (ϕ : Operator X bot) (U : Set X) (J : Set I) (y : X)
    {x : X} (hx : x ∈ Fib d ϕ J y U) :
    subfamily_pseudometric d J (ϕ.func x) y = 0 := hx.2

/-- CH03-P14-02: 命题 3.11 严格小于点态上确界时提取合法有限正半径，推出零距 -/
theorem prop_3_11_lt_sSup (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X)
    {x : X} (hx : x ∈ U) (hdist : d_in x y < r_null d_in d_out ϕ y U) :
    d_out (ϕ.func x) (ϕ.func y) = 0 := by
  dsimp [r_null] at hdist
  rcases lt_sSup_iff.mp hdist with ⟨r, hr_adm, hxr⟩
  exact hr_adm.2.2 x hx hxr

/-- CH03-P14-03: 命题 3.11 复合输入实例：检查两像点均属于指定下游域，代入纤维判据 -/
theorem prop_3_11_compose_inst (d_in d_mid d_out : X → X → ENNReal)
    (ϕ ψ : Operator X bot) (U U2 : Set X) (y : X)
    {x : X} (hx : x ∈ U) (hy : y ∈ U)
    (hx_mid : ϕ.func x ∈ U2) (hy_mid : ϕ.func y ∈ U2)
    (hdist : d_mid (ϕ.func x) (ϕ.func y) < r_null d_mid d_out ψ (ϕ.func y) U2) :
    d_out (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0 := by
  exact prop_3_11_lt_sSup d_mid d_out ψ U2 (ϕ.func y) hx_mid hdist

/- ====================================================================
   Proposition 3.12: CH03-P15-01, CH03-P15-02
   ==================================================================== -/

/-- CH03-P15-01: 命题 3.12 (i) 下游在实际像域保持零距时，复合统一半径下界 -/
theorem prop_3_12_i (d_in d_mid d_out : X → X → ENNReal)
    (ϕ ψ : Operator X bot) (U : Set X)
    (hψ : ∀ u ∈ ϕ.func '' U, ∀ v ∈ ϕ.func '' U, d_mid u v = 0 → d_out (ψ.func u) (ψ.func v) = 0) :
    r_null_uniform d_in d_mid ϕ U ≤ r_null_uniform d_in d_out (ψ * ϕ) U := by
  dsimp [r_null_uniform]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  refine le_trans (biInf_le (fun y => r_null d_in d_mid ϕ y U) hy) ?_
  dsimp [r_null]
  apply sSup_le_sSup
  intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  refine ⟨hr0, hrt, ?_⟩
  intro x hx hdist
  have hmid := hball x hx hdist
  change d_out (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0
  exact hψ (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩ hmid

/-- CH03-P15-02: 命题 3.12 (ii) 有限正L的单通道Lip上界给下游实际像域半径除以L的下界，处理右端0与无穷 -/
theorem prop_3_12_ii (d_in d_mid d_out : X → X → ENNReal)
    (ϕ ψ : Operator X bot) (U : Set X)
    (L : ENNReal) (hL_pos : 0 < L) (hL_top : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d_mid (ϕ.func x) (ϕ.func y) ≤ L * d_in x y) :
    (r_null_uniform d_mid d_out ψ (ϕ.func '' U)) / L ≤
      r_null_uniform d_in d_out (ψ * ϕ) U := by
  set R2 := r_null_uniform d_mid d_out ψ (ϕ.func '' U)
  dsimp [r_null_uniform]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  dsimp [r_null]
  by_cases hR2 : R2 / L = 0
  · rw [hR2]; exact bot_le
  have h_bound : ∀ c : ENNReal, 0 < c → c < R2 / L →
      c ≤ sSup { r | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out ((ψ * ϕ).func x) ((ψ * ϕ).func y) = 0 } := by
    intro c hc0 hc
    apply le_sSup
    have h_c_top : c < ⊤ := by
      by_contra! h_c
      have : c = ⊤ := top_le_iff.mp h_c
      subst this
      exact (not_top_lt hc).elim
    have hcL : L * c < R2 := by
      have h_iff := ENNReal.lt_div_iff_mul_lt (a := R2) (b := L) (c := c) (Or.inl hL_pos.ne') (Or.inl hL_top.ne)
      have hcL := h_iff.mp hc
      rw [mul_comm]
      exact hcL
    refine ⟨hc0, h_c_top, ?_⟩
    intro x hx hdist
    have h_mid_lt : d_mid (ϕ.func x) (ϕ.func y) < R2 := by
      have h1 := hLip x hx y hy
      have h2 : L * d_in x y < L * c := by
        rw [mul_comm L (d_in x y), mul_comm L c]
        exact ENNReal.mul_lt_mul_left hL_pos.ne' hL_top.ne hdist
      exact lt_of_le_of_lt h1 (lt_trans h2 hcL)
    have h_R2_le : R2 ≤ r_null d_mid d_out ψ (ϕ.func y) (ϕ.func '' U) := by
      dsimp [R2, r_null_uniform]
      exact biInf_le (fun u => r_null d_mid d_out ψ u (ϕ.func '' U)) ⟨y, hy, rfl⟩
    have h_mid_lt_sup : d_mid (ϕ.func x) (ϕ.func y) < r_null d_mid d_out ψ (ϕ.func y) (ϕ.func '' U) :=
      lt_of_lt_of_le h_mid_lt h_R2_le
    change d_out (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) = 0
    exact prop_3_11_lt_sSup d_mid d_out ψ (ϕ.func '' U) (ϕ.func y) ⟨x, hx, rfl⟩ h_mid_lt_sup
  by_contra! hlt
  rcases exists_between hlt with ⟨c, hc_sup, hc_r2⟩
  have hc0 : 0 < c := lt_of_le_of_lt bot_le hc_sup
  have hc_le := h_bound c hc0 hc_r2
  exact (lt_self_iff_false c).mp (lt_of_le_of_lt hc_le hc_sup)

end OperatorLocalDegeneracy
