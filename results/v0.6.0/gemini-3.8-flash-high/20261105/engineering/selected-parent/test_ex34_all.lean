import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ThresholdClassification
import OperatorLocalDegeneracy.NullificationRadius

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

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

end OperatorLocalDegeneracy
