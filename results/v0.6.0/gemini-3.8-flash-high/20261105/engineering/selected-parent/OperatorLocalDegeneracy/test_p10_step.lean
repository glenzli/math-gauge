import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.gauge_space

open formal_oet.vol_01.ch_01_foundations

noncomputable def d_real_bot (x y : Option ℝ) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => ENNReal.ofReal (|a - b|)
  | _, _ => ⊤

noncomputable def step_func (x : Option ℝ) : Option ℝ :=
  match x with
  | none => none
  | some r => if r > 0 then some 1 else some 0

noncomputable def step_op : Operator (Option ℝ) none where
  func := step_func
  preserves_bot := rfl

def U_step : Set (Option ℝ) :=
  { y | ∃ r : ℝ, y = some r ∧ ((-1 ≤ r ∧ r < 0) ∨ (0 < r ∧ r ≤ 1)) }

noncomputable def r_null (d_in d_out : Option ℝ → Option ℝ → ENNReal) (ϕ : Operator (Option ℝ) none) (y : Option ℝ) (U : Set (Option ℝ)) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_uniform (d_in d_out : Option ℝ → Option ℝ → ENNReal) (ϕ : Operator (Option ℝ) none) (U : Set (Option ℝ)) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

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
