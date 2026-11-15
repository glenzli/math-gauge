import Ch03.Defs
import Ch03.RealLineExt
import Ch03.Sec1_ComponentPartition
import Ch03.Sec2_FibersAndFactorization
import Ch03.Sec3_NullificationRadius
import Ch03.Sec4_ScaleAndThresholds
import Ch03.Sec5_LocalNullificationCovering
import Ch03.Sec6_MappingEntropyDiff
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-!
# § 3.7 习题 3.4 – 3.5 (`CH03-P29-01` – `CH03-P30-04`)
-/

/-! ## 习题 3.4：输入域改变下的阈值分类 (`CH03-P29-01` – `CH03-P29-05`) -/

/-- 习题 3.4 的下取整算子 `f(x) = ⌊x⌋`（`x ∈ ℝ`），`f(⊥) = ⊥`。 -/
noncomputable def ex3_4_f : Operator RealWithBot RealWithBot.bot :=
  liftRealMap (fun x : ℝ => ((Int.floor x : ℤ) : ℝ))

/-- 习题 3.4(i) 的四个局部输入域 `D₁ = [0, 1/2]`，`D₂ = [9/10, 11/10]`，`D₃ = {0, 2}`，`D₄ = [0, 2]`。 -/
def ex3_4_D1 : Set RealWithBot := RealWithBot.ofReal '' Set.Icc (0 : ℝ) (1 / 2)
def ex3_4_D2 : Set RealWithBot := RealWithBot.ofReal '' Set.Icc (9 / 10 : ℝ) (11 / 10)
def ex3_4_D3 : Set RealWithBot := {.ofReal 0, .ofReal 2}
def ex3_4_D4 : Set RealWithBot := RealWithBot.ofReal '' Set.Icc (0 : ℝ) 2

/-- 辅助引理：闭区间 `[a, b]`（`a ≤ b`）在 `realStdExtDist` 下的直径等于 `b - a`。 -/
theorem setDiam_ofReal_Icc (a b : ℝ) (hab : a ≤ b) :
    setDiam realStdExtDist (RealWithBot.ofReal '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · unfold setDiam
    apply iSup₂_le
    rintro _ ⟨x, hx, rfl⟩
    apply iSup₂_le
    rintro _ ⟨y, hy, rfl⟩
    rw [realStdExtDist_ofReal]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
  · unfold setDiam
    have hb : RealWithBot.ofReal b ∈ RealWithBot.ofReal '' Set.Icc a b :=
      ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    have ha : RealWithBot.ofReal a ∈ RealWithBot.ofReal '' Set.Icc a b :=
      ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    refine le_trans ?_
      (le_iSup₂_of_le (.ofReal b) hb (le_iSup₂_of_le (.ofReal a) ha le_rfl))
    rw [realStdExtDist_ofReal, abs_of_nonneg (sub_nonneg.mpr hab)]

/-- `CH03-P29-01`：习题 3.4(i-a) — 验证基础空间/算子/阈值合法性，并计算 `D₁ = [0, 1/2]` 的直径 `1/2`、统一零化半径 `+∞`（`⊤`）及阈值组合 `(1, 1)`。 -/
theorem ex_3_4_part_i_D1 :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realStdExtDist ∧
    ex3_4_f.func .bot = .bot ∧
    IsFinitePosThreshold 1 ∧
    ex3_4_D1.Nonempty ∧
    ex3_4_D1 ⊆ dom ex3_4_f ∧
    setDiam realStdExtDist ex3_4_D1 = (1 / 2 : ENNReal) ∧
    uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D1 = ⊤ ∧
    channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D1 () () = (1, 1) := by
  have h12_eq : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hne : ex3_4_D1.Nonempty := ⟨.ofReal 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hdom : ex3_4_D1 ⊆ dom ex3_4_f := ofReal_image_subset_dom_liftRealMap _ _
  have hdiam : setDiam realStdExtDist ex3_4_D1 = (1 / 2 : ENNReal) := by
    rw [ex3_4_D1, setDiam_ofReal_Icc 0 (1 / 2) (by norm_num), sub_zero, h12_eq]
  have hfloor0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), Int.floor x = 0 := by
    intro x hx
    exact Int.floor_eq_iff.mpr ⟨by norm_num; exact hx.1, by norm_num; linarith [hx.2]⟩
  have hunif : uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D1 = ⊤ := by
    rw [eq_top_iff]
    apply le_iInf₂
    rintro _ ⟨y, hy, rfl⟩
    apply le_nullRadius_of_forall_lt
    rintro r _ _ _ _ ⟨_, ⟨x, hx, rfl⟩⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simp [realStdGauge, ex3_4_f, hfloor0 x hx, hfloor0 y hy]
  have hlt1 : setDiam realStdExtDist ex3_4_D1 < 1 := by
    rw [hdiam, h12_eq, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
  have hge1 : (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D1 := by
    rw [hunif]
    exact le_top
  have htype :
      channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D1 () () = (1, 1) := by
    have hlt1' : diamScaleFamily realStdGauge () ex3_4_D1 < 1 := hlt1
    simp [channelType, ind01, hlt1', hge1]
  exact ⟨realStdExtDist_isExtendedPseudoMetric, rfl, ⟨zero_lt_one, ENNReal.one_lt_top⟩,
    hne, hdom, hdiam, hunif, htype⟩

/-- `CH03-P29-02`：习题 3.4(i-b) — 计算 `D₂ = [9/10, 11/10]` 的直径 `1/5`、跨跳跃点 `1` 处的点态与统一零化半径 `0`，以及阈值组合 `(1, 0)`。 -/
theorem ex_3_4_part_i_D2 :
    ex3_4_D2.Nonempty ∧
    ex3_4_D2 ⊆ dom ex3_4_f ∧
    setDiam realStdExtDist ex3_4_D2 = (1 / 5 : ENNReal) ∧
    nullRadiusComp realStdGauge ex3_4_f () () (.ofReal 1) ex3_4_D2 = 0 ∧
    uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D2 = 0 ∧
    channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D2 () () = (1, 0) := by
  have h15_eq : (1 / 5 : ENNReal) = ENNReal.ofReal (1 / 5 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5)]
    norm_num
  have h1_mem : RealWithBot.ofReal 1 ∈ ex3_4_D2 :=
    ⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hne : ex3_4_D2.Nonempty := ⟨.ofReal 1, h1_mem⟩
  have hdom : ex3_4_D2 ⊆ dom ex3_4_f := ofReal_image_subset_dom_liftRealMap _ _
  have hdiam : setDiam realStdExtDist ex3_4_D2 = (1 / 5 : ENNReal) := by
    rw [ex3_4_D2, setDiam_ofReal_Icc (9 / 10) (11 / 10) (by norm_num)]
    have hsub : (11 / 10 : ℝ) - 9 / 10 = 1 / 5 := by norm_num
    rw [hsub, h15_eq]
  have hpt0 : nullRadiusComp realStdGauge ex3_4_f () () (.ofReal 1) ex3_4_D2 = 0 := by
    apply nullRadius_eq_zero_of_empty
    rintro r ⟨hr_pos, hr_fin, hinc⟩
    have hr_real_pos : 0 < r.toReal :=
      ENNReal.toReal_pos (ne_of_gt hr_pos) (ne_of_lt hr_fin)
    let δ : ℝ := min (r.toReal / 2) (1 / 10)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ_lt_r : δ < r.toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ_le_10 : δ ≤ 1 / 10 := min_le_right _ _
    let x : ℝ := 1 - δ
    have hx_mem : RealWithBot.ofReal x ∈ ex3_4_D2 :=
      ⟨x, ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩, rfl⟩
    have hx_ball : RealWithBot.ofReal x ∈ ball (realStdGauge ()) (.ofReal 1) r := by
      simp only [ball, Set.mem_setOf_eq, realStdGauge, realStdExtDist_ofReal]
      have habs : |x - 1| = δ := by
        rw [abs_sub_comm]
        have hsub : (1 : ℝ) - x = δ := by dsimp [x]; ring
        rw [hsub, abs_of_pos hδ_pos]
      rw [habs]
      calc
        ENNReal.ofReal δ < ENNReal.ofReal r.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hr_real_pos).mpr hδ_lt_r
        _ = r := ENNReal.ofReal_toReal (ne_of_lt hr_fin)
    have hout0 := (hinc ⟨hx_ball, hx_mem⟩).2
    have hfloor_x : Int.floor x = 0 := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · norm_num; dsimp [x]; linarith
      · norm_num; dsimp [x]; linarith
    have hfloor_1 : Int.floor (1 : ℝ) = 1 := by norm_num
    simp [realStdGauge, ex3_4_f, hfloor_x, hfloor_1] at hout0
  have hunif : uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D2 = 0 := by
    apply le_antisymm _ (zero_le _)
    exact le_trans (iInf₂_le (RealWithBot.ofReal 1) h1_mem) hpt0.le
  have hlt1 : diamScaleFamily realStdGauge () ex3_4_D2 < 1 := by
    change setDiam realStdExtDist ex3_4_D2 < 1
    rw [hdiam, h15_eq, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
  have hnot_ge1 : ¬ (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D2 := by
    rw [hunif]
    exact not_le_of_gt zero_lt_one
  have htype :
      channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D2 () () = (1, 0) := by
    simp [channelType, ind01, hlt1, hnot_ge1]
  exact ⟨hne, hdom, hdiam, hpt0, hunif, htype⟩

/-- `CH03-P29-03`：习题 3.4(i-c) — 计算离散二点集 `D₃ = {0, 2}` 的直径 `2`、各点及统一零化半径 `2` 及阈值组合 `(0, 1)`。 -/
theorem ex_3_4_part_i_D3 :
    ex3_4_D3.Nonempty ∧
    ex3_4_D3 ⊆ dom ex3_4_f ∧
    setDiam realStdExtDist ex3_4_D3 = 2 ∧
    (∀ y ∈ ex3_4_D3, ∀ r : ENNReal, 0 < r → r ≤ 2 →
      ball realStdExtDist y r ∩ ex3_4_D3 = {y}) ∧
    nullRadiusComp realStdGauge ex3_4_f () () (.ofReal 0) ex3_4_D3 = 2 ∧
    nullRadiusComp realStdGauge ex3_4_f () () (.ofReal 2) ex3_4_D3 = 2 ∧
    uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D3 = 2 ∧
    channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D3 () () = (0, 1) := by
  have hne : ex3_4_D3.Nonempty := ⟨.ofReal 0, Or.inl rfl⟩
  have hdom : ex3_4_D3 ⊆ dom ex3_4_f := by
    intro p hp
    rcases hp with rfl | rfl <;> simp [dom, ex3_4_f]
  have hd02 : realStdExtDist (.ofReal 0) (.ofReal 2) = 2 := by norm_num
  have hd20 : realStdExtDist (.ofReal 2) (.ofReal 0) = 2 := by norm_num
  have hdiam : setDiam realStdExtDist ex3_4_D3 = 2 := by
    apply le_antisymm
    · unfold setDiam
      apply iSup₂_le
      intro x hx
      apply iSup₂_le
      intro y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
    · unfold setDiam
      refine le_trans ?_
        (le_iSup₂_of_le (.ofReal 0) (Or.inl rfl)
          (le_iSup₂_of_le (.ofReal 2) (Or.inr rfl) le_rfl))
      rw [hd02]
  have hiso : ∀ y ∈ ex3_4_D3, ∀ r : ENNReal, 0 < r → r ≤ 2 →
      ball realStdExtDist y r ∩ ex3_4_D3 = {y} := by
    intro y hy r hr_pos hr_le2
    ext z
    simp only [Set.mem_inter_iff, ball, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz_lt, hzD⟩
      rcases hy with rfl | rfl <;> rcases hzD with rfl | rfl
      · rfl
      · rw [hd20] at hz_lt; exact False.elim ((not_lt_of_ge hr_le2) hz_lt)
      · rw [hd02] at hz_lt; exact False.elim ((not_lt_of_ge hr_le2) hz_lt)
      · rfl
    · rintro rfl
      refine ⟨?_, hy⟩
      rw [realStdExtDist_isExtendedPseudoMetric.dist_self]
      exact hr_pos
  have hpt : ∀ y ∈ ex3_4_D3, nullRadiusComp realStdGauge ex3_4_f () () y ex3_4_D3 = 2 := by
    intro y hy
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨_, _, hinc⟩
      by_contra hnot_le
      have hgt2 : (2 : ENNReal) < r := lt_of_not_ge hnot_le
      rcases hy with rfl | rfl
      · have hmem2 : RealWithBot.ofReal 2 ∈ ball (realStdGauge ()) (.ofReal 0) r ∩ ex3_4_D3 :=
          ⟨by simpa [ball, realStdGauge, hd20] using hgt2, Or.inr rfl⟩
        have hout := (hinc hmem2).2
        norm_num [realStdGauge, ex3_4_f] at hout
      · have hmem0 : RealWithBot.ofReal 0 ∈ ball (realStdGauge ()) (.ofReal 2) r ∩ ex3_4_D3 :=
          ⟨by simpa [ball, realStdGauge, hd02] using hgt2, Or.inl rfl⟩
        have hout := (hinc hmem0).2
        norm_num [realStdGauge, ex3_4_f] at hout
    · apply le_sSup
      refine ⟨by norm_num, by simp, ?_⟩
      intro z hz
      have hz_eq : z = y := by
        have hmem_sing : z ∈ ({y} : Set RealWithBot) := by
          rw [← hiso y hy 2 (by norm_num) le_rfl]
          exact hz
        exact Set.mem_singleton_iff.mp hmem_sing
      subst hz_eq
      exact ⟨hy, realStdExtDist_isExtendedPseudoMetric.dist_self _⟩
  have hpt0 := hpt (.ofReal 0) (Or.inl rfl)
  have hpt2 := hpt (.ofReal 2) (Or.inr rfl)
  have hunif : uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D3 = 2 := by
    apply le_antisymm
    · exact le_trans (iInf₂_le (RealWithBot.ofReal 0) (Or.inl rfl)) hpt0.le
    · apply le_iInf₂
      intro y hy
      exact (hpt y hy).ge
  have hnot_lt1 : ¬ diamScaleFamily realStdGauge () ex3_4_D3 < 1 := by
    change ¬ setDiam realStdExtDist ex3_4_D3 < 1
    rw [hdiam]
    norm_num
  have hge1 : (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D3 := by
    rw [hunif]
    norm_num
  have htype :
      channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D3 () () = (0, 1) := by
    simp [channelType, ind01, hnot_lt1, hge1]
  exact ⟨hne, hdom, hdiam, hiso, hpt0, hpt2, hunif, htype⟩

/-- `CH03-P29-04`：习题 3.4(i-d) — 计算 `D₄ = [0, 2]` 的直径 `2`、统一零化半径 `0` 及阈值组合 `(0, 0)`。 -/
theorem ex_3_4_part_i_D4 :
    ex3_4_D4.Nonempty ∧
    ex3_4_D4 ⊆ dom ex3_4_f ∧
    setDiam realStdExtDist ex3_4_D4 = 2 ∧
    uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D4 = 0 ∧
    channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D4 () () = (0, 0) := by
  have hD2_ne : ex3_4_D2.Nonempty := ex_3_4_part_i_D2.1
  have hD2_sub_D4 : ex3_4_D2 ⊆ ex3_4_D4 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
  have hne : ex3_4_D4.Nonempty := hD2_ne.mono hD2_sub_D4
  have hdom : ex3_4_D4 ⊆ dom ex3_4_f := ofReal_image_subset_dom_liftRealMap _ _
  have hdiam : setDiam realStdExtDist ex3_4_D4 = 2 := by
    rw [ex3_4_D4, setDiam_ofReal_Icc 0 2 (by norm_num), sub_zero]
    norm_num
  have hunif : uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D4 = 0 := by
    apply le_antisymm _ (zero_le _)
    calc
      uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D4
          ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D2 :=
            (prop_3_14_uniform_nullRadius_antitone realStdGauge ex3_4_f
              ex3_4_D4 ex3_4_D2 () () hD2_ne hD2_sub_D4 hdom).2.2
      _ = 0 := ex_3_4_part_i_D2.2.2.2.2.1
  have hnot_lt1 : ¬ diamScaleFamily realStdGauge () ex3_4_D4 < 1 := by
    change ¬ setDiam realStdExtDist ex3_4_D4 < 1
    rw [hdiam]
    norm_num
  have hnot_ge1 : ¬ (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D4 := by
    rw [hunif]
    exact not_le_of_gt zero_lt_one
  have htype :
      channelType (diamScaleFamily realStdGauge) 1 1 realStdGauge ex3_4_f ex3_4_D4 () () = (0, 0) := by
    simp [channelType, ind01, hnot_lt1, hnot_ge1]
  exact ⟨hne, hdom, hdiam, hunif, htype⟩

/-- `CH03-P29-05`：习题 3.4(ii) — 否定“无直径小尺度假设时对任意非空 `D ⊆ ℝ`，`\underline{r}^N_{f,d,d}|_D ≥ 1 ⟹ ∀ x, y ∈ D, d(f(x), f(y)) = 0`”，并由 (i) 中合法反例 `D₃ = {0, 2}` 证明其正零化半径 `2` 源于离散受限域的孤立点间隙（半径 `≤ 2` 的受限开球仅含基点自身），而非输出合并。 -/
theorem ex_3_4_part_ii_counterexample_and_source :
    ¬ (∀ D_real : Set ℝ, D_real.Nonempty →
        (1 : ENNReal) ≤
          uniformNullRadiusComp realStdGauge ex3_4_f () () (RealWithBot.ofReal '' D_real) →
        ∀ x ∈ RealWithBot.ofReal '' D_real, ∀ y ∈ RealWithBot.ofReal '' D_real,
          realStdExtDist (ex3_4_f.func x) (ex3_4_f.func y) = 0) ∧
    ex3_4_D3 = RealWithBot.ofReal '' ({0, 2} : Set ℝ) ∧
    (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D3 ∧
    realStdExtDist (ex3_4_f.func (.ofReal 0)) (ex3_4_f.func (.ofReal 2)) = 2 ∧
    (∀ y ∈ ex3_4_D3, ∀ r : ENNReal, 0 < r → r ≤ 2 →
      ball realStdExtDist y r ∩ ex3_4_D3 = {y}) := by
  have hD3_img : ex3_4_D3 = RealWithBot.ofReal '' ({0, 2} : Set ℝ) := by
    ext p
    simp [ex3_4_D3, eq_comm]
  have hunif_D3 : uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D3 = 2 :=
    ex_3_4_part_i_D3.2.2.2.2.2.2.1
  have hge1 : (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex3_4_f () () ex3_4_D3 := by
    rw [hunif_D3]; norm_num
  have hout_dist : realStdExtDist (ex3_4_f.func (.ofReal 0)) (ex3_4_f.func (.ofReal 2)) = 2 := by
    norm_num [ex3_4_f]
  have hnot_imp :
      ¬ (∀ D_real : Set ℝ, D_real.Nonempty →
          (1 : ENNReal) ≤
            uniformNullRadiusComp realStdGauge ex3_4_f () () (RealWithBot.ofReal '' D_real) →
          ∀ x ∈ RealWithBot.ofReal '' D_real, ∀ y ∈ RealWithBot.ofReal '' D_real,
            realStdExtDist (ex3_4_f.func x) (ex3_4_f.func y) = 0) := by
    intro hall
    have hge1' : (1 : ENNReal) ≤
        uniformNullRadiusComp realStdGauge ex3_4_f () ()
          (RealWithBot.ofReal '' ({0, 2} : Set ℝ)) := by
      rwa [← hD3_img]
    have h0_mem : RealWithBot.ofReal 0 ∈ RealWithBot.ofReal '' ({0, 2} : Set ℝ) :=
      ⟨0, Or.inl rfl, rfl⟩
    have h2_mem : RealWithBot.ofReal 2 ∈ RealWithBot.ofReal '' ({0, 2} : Set ℝ) :=
      ⟨2, Or.inr rfl, rfl⟩
    have hzero := hall ({0, 2} : Set ℝ) ⟨0, Or.inl rfl⟩ hge1' (.ofReal 0) h0_mem (.ofReal 2) h2_mem
    rw [hout_dist] at hzero
    norm_num at hzero
  exact ⟨hnot_imp, hD3_img, hge1, hout_dist, ex_3_4_part_i_D3.2.2.2.1⟩

/-! ## 习题 3.5：像集重排与覆盖估计 (`CH03-P30-01` – `CH03-P30-04`) -/

/-- 习题 3.5 的四点评估域 `U = {0, 1, 2, 3}`。 -/
def ex3_5_U : Set RealWithBot :=
  {.ofReal 0, .ofReal 1, .ofReal 2, .ofReal 3}

/-- 习题 3.5 算子 `f`：在 `U` 上取 `0 ↦ 0, 1 ↦ 1, 2 ↦ 2, 3 ↦ 3`，在 `X \ U` 上取 `⊥`。 -/
noncomputable def ex3_5_f : Operator RealWithBot RealWithBot.bot where
  func p := by
    classical
    exact
      if p = .ofReal 0 then .ofReal 0
      else if p = .ofReal 1 then .ofReal 1
      else if p = .ofReal 2 then .ofReal 2
      else if p = .ofReal 3 then .ofReal 3
      else .bot
  preserves_bot := by simp

/-- 习题 3.5 算子 `g`：在 `U` 上取 `0 ↦ 0, 1 ↦ 3, 2 ↦ 1, 3 ↦ 2`，在 `X \ U` 上取 `⊥`。 -/
noncomputable def ex3_5_g : Operator RealWithBot RealWithBot.bot where
  func p := by
    classical
    exact
      if p = .ofReal 0 then .ofReal 0
      else if p = .ofReal 1 then .ofReal 3
      else if p = .ofReal 2 then .ofReal 1
      else if p = .ofReal 3 then .ofReal 2
      else .bot
  preserves_bot := by simp

@[simp] theorem ex3_5_f_val0 : ex3_5_f.func (.ofReal 0) = .ofReal 0 := by simp [ex3_5_f]
@[simp] theorem ex3_5_f_val1 : ex3_5_f.func (.ofReal 1) = .ofReal 1 := by simp [ex3_5_f]
@[simp] theorem ex3_5_f_val2 : ex3_5_f.func (.ofReal 2) = .ofReal 2 := by simp [ex3_5_f]
@[simp] theorem ex3_5_f_val3 : ex3_5_f.func (.ofReal 3) = .ofReal 3 := by simp [ex3_5_f]

@[simp] theorem ex3_5_g_val0 : ex3_5_g.func (.ofReal 0) = .ofReal 0 := by simp [ex3_5_g]
@[simp] theorem ex3_5_g_val1 : ex3_5_g.func (.ofReal 1) = .ofReal 3 := by simp [ex3_5_g]
@[simp] theorem ex3_5_g_val2 : ex3_5_g.func (.ofReal 2) = .ofReal 1 := by simp [ex3_5_g]
@[simp] theorem ex3_5_g_val3 : ex3_5_g.func (.ofReal 3) = .ofReal 2 := by simp [ex3_5_g]

theorem ex3_5_outside_bot (p : RealWithBot) (hp : p ∉ ex3_5_U) :
    ex3_5_f.func p = .bot ∧ ex3_5_g.func p = .bot := by
  have h0 : p ≠ .ofReal 0 := fun h => hp (by simp [ex3_5_U, h])
  have h1 : p ≠ .ofReal 1 := fun h => hp (by simp [ex3_5_U, h])
  have h2 : p ≠ .ofReal 2 := fun h => hp (by simp [ex3_5_U, h])
  have h3 : p ≠ .ofReal 3 := fun h => hp (by simp [ex3_5_U, h])
  simp [ex3_5_f, ex3_5_g, h0, h1, h2, h3]

theorem dom_ex3_5_f : dom ex3_5_f = ex3_5_U := by
  ext p
  by_cases hp : p ∈ ex3_5_U
  · refine iff_of_true ?_ hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [dom]
  · exact iff_of_false (fun hdom => hdom (ex3_5_outside_bot p hp).1) hp

theorem dom_ex3_5_g : dom ex3_5_g = ex3_5_U := by
  ext p
  by_cases hp : p ∈ ex3_5_U
  · refine iff_of_true ?_ hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [dom]
  · exact iff_of_false (fun hdom => hdom (ex3_5_outside_bot p hp).2) hp

/-- 习题 3.5(i) 四点集 `U = {0, 1, 2, 3}` 在有限正精度 `ε` 下的完整三分段函数。 -/
noncomputable def ex3_5_piecewise_cov (ε : ENNReal) : ENNReal :=
  if ε ≤ 1 then 4
  else if ε ≤ 2 then 2
  else 1

/-- `CH03-P30-01`：习题 3.5(i) — 所有有限正 `ε ∈ (0, +∞)` 下 `N(ε, U)` 的完整三分段表达式与端点值（`0 < ε ≤ 1` 时为 `4`、`1 < ε ≤ 2` 时为 `2`、`2 < ε < ⊤` 时为 `1`），并证明在 `ε = 7/4` 时虽然开球 `B(3/2, 7/4)` 覆盖 `U`，但 `3/2 ∉ U` 不满足内部中心要求，故 `{3/2}` 不是合法内覆盖且 `N(7/4, U) = 2`。 -/
theorem ex_3_5_part_i_covering_piecewise_and_noninternal :
    (∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realStdExtDist ε ex3_5_U = ex3_5_piecewise_cov ε) ∧
    (∀ ε : ENNReal, 0 < ε → ε ≤ 1 → covering_number realStdExtDist ε ex3_5_U = 4) ∧
    (∀ ε : ENNReal, 1 < ε → ε ≤ 2 → covering_number realStdExtDist ε ex3_5_U = 2) ∧
    (∀ ε : ENNReal, 2 < ε → ε < ⊤ → covering_number realStdExtDist ε ex3_5_U = 1) ∧
    covering_number realStdExtDist 1 ex3_5_U = 4 ∧
    covering_number realStdExtDist 2 ex3_5_U = 2 ∧
    ex3_5_U ⊆ ball realStdExtDist (.ofReal (3 / 2)) (7 / 4 : ENNReal) ∧
    RealWithBot.ofReal (3 / 2) ∉ ex3_5_U ∧
    ¬ InternalEpsilonNet realStdExtDist (7 / 4 : ENNReal) ex3_5_U {.ofReal (3 / 2)} ∧
    covering_number realStdExtDist (7 / 4 : ENNReal) ex3_5_U = 2 := by
  classical
  have hpair_sep : ∀ x ∈ ex3_5_U, ∀ y ∈ ex3_5_U, x ≠ y → 1 ≤ realStdExtDist x y := by
    intro x hx y hy hne
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact False.elim (hne rfl) | norm_num
  -- 第一段：0 < ε ≤ 1 ⟹ N(ε, U) = 4
  have hseg1 : ∀ ε : ENNReal, 0 < ε → ε ≤ 1 →
      covering_number realStdExtDist ε ex3_5_U = 4 := by
    intro ε hε_pos hε_le1
    let S4 : Finset RealWithBot := {.ofReal 0, .ofReal 1, .ofReal 2, .ofReal 3}
    have hS4_card : S4.card = 4 := by
      simp [S4, show (0 : ℝ) ≠ 1 by norm_num, show (0 : ℝ) ≠ 2 by norm_num,
        show (0 : ℝ) ≠ 3 by norm_num, show (1 : ℝ) ≠ 2 by norm_num,
        show (1 : ℝ) ≠ 3 by norm_num]
    have hle4 : covering_number realStdExtDist ε ex3_5_U ≤ 4 := by
      have hnet : InternalEpsilonNet realStdExtDist ε ex3_5_U S4 := by
        refine ⟨?_, ?_⟩
        · intro p hp
          simpa [S4, ex3_5_U] using hp
        · intro p hp
          have hpS : p ∈ S4 := by simpa [S4, ex3_5_U] using hp
          refine ⟨p, hpS, ?_⟩
          rw [realStdExtDist_isExtendedPseudoMetric.dist_self]
          exact hε_pos
      exact le_trans (iInf_le_of_le S4 (iInf_le_of_le hnet le_rfl)) (by simp [hS4_card])
    have hge4 : 4 ≤ covering_number realStdExtDist ε ex3_5_U := by
      apply le_iInf₂
      intro S hS
      have hsub : S4 ⊆ S := by
        intro p hpS4
        have hpU : p ∈ ex3_5_U := by simpa [S4, ex3_5_U] using hpS4
        rcases hS.2 p hpU with ⟨c, hcS, hpc⟩
        by_cases hpc_eq : p = c
        · rwa [hpc_eq]
        · exfalso
          have hge1 := hpair_sep p hpU c (hS.1 hcS) hpc_eq
          exact (not_lt_of_ge (le_trans hε_le1 hge1)) hpc
      have hcard_le : 4 ≤ S.card := by
        rw [← hS4_card]
        exact Finset.card_le_card hsub
      exact_mod_cast hcard_le
    exact le_antisymm hle4 hge4
  -- 第二段：1 < ε ≤ 2 ⟹ N(ε, U) = 2
  have hseg2 : ∀ ε : ENNReal, 1 < ε → ε ≤ 2 →
      covering_number realStdExtDist ε ex3_5_U = 2 := by
    intro ε h1_lt_ε hε_le2
    have hε_pos : 0 < ε := lt_trans zero_lt_one h1_lt_ε
    let S2 : Finset RealWithBot := {.ofReal 0, .ofReal 2}
    have hS2_card : S2.card = 2 := Finset.card_pair (by norm_num)
    have hle2 : covering_number realStdExtDist ε ex3_5_U ≤ 2 := by
      have hnet : InternalEpsilonNet realStdExtDist ε ex3_5_U S2 := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact Or.inl rfl
          · rw [Finset.mem_singleton.mp hp']
            exact Or.inr (Or.inr (Or.inl rfl))
        · intro p hp
          rcases hp with rfl | rfl | rfl | rfl
          · exact ⟨.ofReal 0, by simp [S2], by simpa using hε_pos⟩
          · exact ⟨.ofReal 0, by simp [S2], by norm_num; exact h1_lt_ε⟩
          · exact ⟨.ofReal 2, by simp [S2], by simpa using hε_pos⟩
          · exact ⟨.ofReal 2, by simp [S2], by norm_num; exact h1_lt_ε⟩
      exact le_trans (iInf_le_of_le S2 (iInf_le_of_le hnet le_rfl)) (by simp [hS2_card])
    have hge2 : 2 ≤ covering_number realStdExtDist ε ex3_5_U := by
      apply le_iInf₂
      intro S hS
      rcases hS.2 (.ofReal 0) (Or.inl rfl) with ⟨c₀, hc₀S, hc₀_dist⟩
      rcases hS.2 (.ofReal 3) (Or.inr (Or.inr (Or.inr rfl))) with ⟨c₃, hc₃S, hc₃_dist⟩
      have hc₀_low : c₀ = .ofReal 0 ∨ c₀ = .ofReal 1 := by
        rcases hS.1 hc₀S with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          have hd : realStdExtDist (.ofReal 0) (.ofReal 2) = 2 := by norm_num
          rw [hd] at hc₀_dist
          exact (not_lt_of_ge hε_le2) hc₀_dist
        · exfalso
          have hd : realStdExtDist (.ofReal 0) (.ofReal 3) = 3 := by norm_num
          rw [hd] at hc₀_dist
          have h23 : (2 : ENNReal) ≤ 3 := by norm_num
          exact (not_lt_of_ge (le_trans hε_le2 h23)) hc₀_dist
      have hc₃_high : c₃ = .ofReal 2 ∨ c₃ = .ofReal 3 := by
        rcases hS.1 hc₃S with rfl | rfl | rfl | rfl
        · exfalso
          have hd : realStdExtDist (.ofReal 3) (.ofReal 0) = 3 := by norm_num
          rw [hd] at hc₃_dist
          have h23 : (2 : ENNReal) ≤ 3 := by norm_num
          exact (not_lt_of_ge (le_trans hε_le2 h23)) hc₃_dist
        · exfalso
          have hd : realStdExtDist (.ofReal 3) (.ofReal 1) = 2 := by norm_num
          rw [hd] at hc₃_dist
          exact (not_lt_of_ge hε_le2) hc₃_dist
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hne_c : c₀ ≠ c₃ := by
        rcases hc₀_low with rfl | rfl <;> rcases hc₃_high with rfl | rfl <;> norm_num
      have hsub_pair : ({c₀, c₃} : Finset RealWithBot) ⊆ S := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact hc₀S
        · rw [Finset.mem_singleton.mp hz']
          exact hc₃S
      have hcard_ge : 2 ≤ S.card := by
        calc
          2 = ({c₀, c₃} : Finset RealWithBot).card := (Finset.card_pair hne_c).symm
          _ ≤ S.card := Finset.card_le_card hsub_pair
      exact_mod_cast hcard_ge
    exact le_antisymm hle2 hge2
  -- 第三段：2 < ε < ⊤ ⟹ N(ε, U) = 1
  have hseg3 : ∀ ε : ENNReal, 2 < ε → ε < ⊤ →
      covering_number realStdExtDist ε ex3_5_U = 1 := by
    intro ε h2_lt_ε _
    have h1_lt_ε : 1 < ε := lt_trans (by norm_num) h2_lt_ε
    have h0_lt_ε : 0 < ε := lt_trans zero_lt_one h1_lt_ε
    let S1 : Finset RealWithBot := {.ofReal 1}
    have hle1 : covering_number realStdExtDist ε ex3_5_U ≤ 1 := by
      have hnet : InternalEpsilonNet realStdExtDist ε ex3_5_U S1 := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_singleton] at hp
          rw [hp]
          exact Or.inr (Or.inl rfl)
        · intro p hp
          refine ⟨.ofReal 1, Finset.mem_singleton_self _, ?_⟩
          rcases hp with rfl | rfl | rfl | rfl
          · norm_num; exact h1_lt_ε
          · norm_num; exact h0_lt_ε
          · norm_num; exact h1_lt_ε
          · norm_num; exact h2_lt_ε
      exact le_trans (iInf_le_of_le S1 (iInf_le_of_le hnet le_rfl)) (by simp [S1])
    have hge1 : 1 ≤ covering_number realStdExtDist ε ex3_5_U :=
      one_le_covering_number_of_nonempty _ _ _ ⟨.ofReal 0, Or.inl rfl⟩
    exact le_antisymm hle1 hge1
  have hpiece : ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realStdExtDist ε ex3_5_U = ex3_5_piecewise_cov ε := by
    intro ε hε_pos hε_fin
    unfold ex3_5_piecewise_cov
    by_cases h1 : ε ≤ 1
    · rw [if_pos h1]
      exact hseg1 ε hε_pos h1
    · rw [if_neg h1]
      have h1_lt : 1 < ε := lt_of_not_ge h1
      by_cases h2 : ε ≤ 2
      · rw [if_pos h2]
        exact hseg2 ε h1_lt h2
      · rw [if_neg h2]
        exact hseg3 ε (lt_of_not_ge h2) hε_fin
  -- ε = 7/4 处外部中心 3/2 的性质
  have h74_eq : (7 / 4 : ENNReal) = ENNReal.ofReal (7 / 4 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hball_cov : ex3_5_U ⊆ ball realStdExtDist (.ofReal (3 / 2)) (7 / 4 : ENNReal) := by
    intro p hp
    simp only [ball, Set.mem_setOf_eq]
    rcases hp with rfl | rfl | rfl | rfl
    · rw [realStdExtDist_ofReal, h74_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    · rw [realStdExtDist_ofReal, h74_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    · rw [realStdExtDist_ofReal, h74_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    · rw [realStdExtDist_ofReal, h74_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hnot_in_U : RealWithBot.ofReal (3 / 2) ∉ ex3_5_U := by
    simp [ex3_5_U]
    norm_num
  have hnot_net :
      ¬ InternalEpsilonNet realStdExtDist (7 / 4 : ENNReal) ex3_5_U {.ofReal (3 / 2)} := by
    intro hnet
    exact hnot_in_U (hnet.1 (Finset.mem_singleton_self _))
  have h1_lt_74 : (1 : ENNReal) < 7 / 4 := by
    rw [← ENNReal.ofReal_one, h74_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h74_le_2 : (7 / 4 : ENNReal) ≤ 2 := by
    rw [h74_eq, show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact ⟨hpiece, hseg1, hseg2, hseg3,
    hseg1 1 zero_lt_one le_rfl,
    hseg2 2 (by norm_num) le_rfl,
    hball_cov, hnot_in_U, hnot_net,
    hseg2 (7 / 4) h1_lt_74 h74_le_2⟩

/-- `CH03-P30-02`：习题 3.5(ii) — 证明 `dom(f) = dom(g) = U`、`f(U) = g(U) = U`，对任意有限正精度 `0 < ε < ⊤` 比较两像集覆盖数（均等于 `N(ε, U)`），并证明两算子的映射熵差均为 `0`。 -/
theorem ex_3_5_part_ii_images_covering_and_entropyDiff :
    dom ex3_5_f = ex3_5_U ∧
    dom ex3_5_g = ex3_5_U ∧
    operator_image ex3_5_f ex3_5_U = ex3_5_U ∧
    operator_image ex3_5_g ex3_5_U = ex3_5_U ∧
    (∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realStdExtDist ε (operator_image ex3_5_f ex3_5_U) =
        covering_number realStdExtDist ε (operator_image ex3_5_g ex3_5_U) ∧
      covering_number realStdExtDist ε (operator_image ex3_5_f ex3_5_U) =
        covering_number realStdExtDist ε ex3_5_U ∧
      covering_number realStdExtDist ε (operator_image ex3_5_g ex3_5_U) =
        ex3_5_piecewise_cov ε ∧
      (∃ hdef_f : MappingEntropyDiffSingleDefined realStdGauge ex3_5_f ex3_5_U () ε,
        mappingEntropyDiffSingle realStdGauge ex3_5_f ex3_5_U () ε hdef_f = 0) ∧
      (∃ hdef_g : MappingEntropyDiffSingleDefined realStdGauge ex3_5_g ex3_5_U () ε,
        mappingEntropyDiffSingle realStdGauge ex3_5_g ex3_5_U () ε hdef_g = 0)) := by
  have himg_f : operator_image ex3_5_f ex3_5_U = ex3_5_U := by
    ext p
    simp only [operator_image, ex3_5_U, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩
      · exact Or.inl ex3_5_f_val0
      · exact Or.inr (Or.inl ex3_5_f_val1)
      · exact Or.inr (Or.inr (Or.inl ex3_5_f_val2))
      · exact Or.inr (Or.inr (Or.inr ex3_5_f_val3))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨.ofReal 0, Or.inl rfl, ex3_5_f_val0⟩
      · exact ⟨.ofReal 1, Or.inr (Or.inl rfl), ex3_5_f_val1⟩
      · exact ⟨.ofReal 2, Or.inr (Or.inr (Or.inl rfl)), ex3_5_f_val2⟩
      · exact ⟨.ofReal 3, Or.inr (Or.inr (Or.inr rfl)), ex3_5_f_val3⟩
  have himg_g : operator_image ex3_5_g ex3_5_U = ex3_5_U := by
    ext p
    simp only [operator_image, ex3_5_U, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩
      · exact Or.inl ex3_5_g_val0
      · exact Or.inr (Or.inr (Or.inr ex3_5_g_val1))
      · exact Or.inr (Or.inl ex3_5_g_val2)
      · exact Or.inr (Or.inr (Or.inl ex3_5_g_val3))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨.ofReal 0, Or.inl rfl, ex3_5_g_val0⟩
      · exact ⟨.ofReal 2, Or.inr (Or.inr (Or.inl rfl)), ex3_5_g_val2⟩
      · exact ⟨.ofReal 3, Or.inr (Or.inr (Or.inr rfl)), ex3_5_g_val3⟩
      · exact ⟨.ofReal 1, Or.inr (Or.inl rfl), ex3_5_g_val1⟩
  refine ⟨dom_ex3_5_f, dom_ex3_5_g, himg_f, himg_g, ?_⟩
  intro ε hε_pos hε_fin
  have hcov_U := ex_3_5_part_i_covering_piecewise_and_noninternal.1 ε hε_pos hε_fin
  have hcov_fin : covering_number realStdExtDist ε ex3_5_U < ⊤ := by
    rw [hcov_U]
    unfold ex3_5_piecewise_cov
    split_ifs <;> simp
  have hU_ne : ex3_5_U.Nonempty := ⟨.ofReal 0, Or.inl rfl⟩
  have hcov_ge1 : 1 ≤ covering_number realStdExtDist ε ex3_5_U :=
    one_le_covering_number_of_nonempty _ _ _ hU_ne
  have hcov_ne0 : covering_number realStdExtDist ε ex3_5_U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hcov_ge1)
  have hcov_netop : covering_number realStdExtDist ε ex3_5_U ≠ ⊤ :=
    ne_of_lt hcov_fin
  have he_U :
      log2_ereal (covering_number realStdExtDist ε ex3_5_U) =
        ((Real.logb 2 (covering_number realStdExtDist ε ex3_5_U).toReal : ℝ) : EReal) := by
    simp [log2_ereal, hcov_ne0, hcov_netop]
  have hsub_fin : subfamilyCoveringNumber realStdGauge {()} ε ex3_5_U < ⊤ := by
    rwa [subfamilyCoveringNumber_singleton]
  have hdef_f : MappingEntropyDiffSingleDefined realStdGauge ex3_5_f ex3_5_U () ε :=
    ⟨hU_ne, le_of_eq dom_ex3_5_f.symm, Set.singleton_nonempty (), Set.singleton_nonempty (),
      hε_pos, hε_fin, Or.inl hsub_fin⟩
  have hdef_g : MappingEntropyDiffSingleDefined realStdGauge ex3_5_g ex3_5_U () ε :=
    ⟨hU_ne, le_of_eq dom_ex3_5_g.symm, Set.singleton_nonempty (), Set.singleton_nonempty (),
      hε_pos, hε_fin, Or.inl hsub_fin⟩
  refine ⟨by rw [himg_f, himg_g], by rw [himg_f], by rw [himg_g, hcov_U],
    ⟨hdef_f, ?_⟩, ⟨hdef_g, ?_⟩⟩
  · unfold mappingEntropyDiffSingle
    rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
      subfamily_metric_entropy_singleton, himg_f]
    change metric_entropy realStdExtDist ε ex3_5_U -
        metric_entropy realStdExtDist ε ex3_5_U = 0
    unfold metric_entropy
    rw [he_U, ← EReal.coe_sub, sub_self]
    rfl
  · unfold mappingEntropyDiffSingle
    rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
      subfamily_metric_entropy_singleton, himg_g]
    change metric_entropy realStdExtDist ε ex3_5_U -
        metric_entropy realStdExtDist ε ex3_5_U = 0
    unfold metric_entropy
    rw [he_U, ← EReal.coe_sub, sub_self]
    rfl

/-- `CH03-P30-03`：习题 3.5(iii-a) — 分别证明 `f` 与 `g` 在 `U` 上最小标量 Lip 常数为 `1` 与 `3`（含合法上界验证、由特定点对给出的必要下界及最小值/下确界刻画）。 -/
theorem ex_3_5_part_iii_optimal_scalar_lip :
    HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () 1 ∧
    (∀ L : ENNReal, HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () L → 1 ≤ L) ∧
    IsLeast { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () L } 1 ∧
    sInf { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () L } = 1 ∧
    HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () 3 ∧
    (∀ L : ENNReal, HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () L → 3 ≤ L) ∧
    IsLeast { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () L } 3 ∧
    sInf { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () L } = 3 := by
  have hLip_f : HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () 1 := by
    refine ⟨le_of_eq dom_ex3_5_f.symm, ?_⟩
    intro x hx y hy
    rw [one_mul]
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [realStdGauge]
  have hLow_f : ∀ L : ENNReal,
      HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () L → 1 ≤ L := by
    intro L hL
    have h01 := hL.2 (.ofReal 0) (Or.inl rfl) (.ofReal 1) (Or.inr (Or.inl rfl))
    have hd_in : realStdGauge () (.ofReal 0) (.ofReal 1) = 1 := by norm_num [realStdGauge]
    have hd_out : realStdGauge () (ex3_5_f.func (.ofReal 0)) (ex3_5_f.func (.ofReal 1)) = 1 := by
      norm_num [realStdGauge]
    rw [hd_out, hd_in, mul_one] at h01
    exact h01
  have hLeast_f : IsLeast { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () L } 1 :=
    ⟨hLip_f, fun L hL => hLow_f L hL⟩
  have hsInf_f : sInf { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_f ex3_5_U () () L } = 1 :=
    le_antisymm (sInf_le hLip_f) (le_sInf fun L hL => hLow_f L hL)
  have hLip_g : HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () 3 := by
    refine ⟨le_of_eq dom_ex3_5_g.symm, ?_⟩
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simp [realStdGauge, realStdExtDist_isExtendedPseudoMetric.dist_self]
    · have hin_ge1 : 1 ≤ realStdGauge () x y := by
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          first | exact False.elim (hxy rfl) | norm_num [realStdGauge]
      have hout_le3 : realStdGauge () (ex3_5_g.func x) (ex3_5_g.func y) ≤ 3 := by
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          norm_num [realStdGauge]
      calc
        realStdGauge () (ex3_5_g.func x) (ex3_5_g.func y)
            ≤ 3 := hout_le3
        _ = 3 * 1 := (mul_one 3).symm
        _ ≤ 3 * realStdGauge () x y := mul_le_mul_of_nonneg_left hin_ge1 (zero_le _)
  have hLow_g : ∀ L : ENNReal,
      HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () L → 3 ≤ L := by
    intro L hL
    have h01 := hL.2 (.ofReal 0) (Or.inl rfl) (.ofReal 1) (Or.inr (Or.inl rfl))
    have hd_in : realStdGauge () (.ofReal 0) (.ofReal 1) = 1 := by norm_num [realStdGauge]
    have hd_out : realStdGauge () (ex3_5_g.func (.ofReal 0)) (ex3_5_g.func (.ofReal 1)) = 3 := by
      norm_num [realStdGauge]
    rw [hd_out, hd_in, mul_one] at h01
    exact h01
  have hLeast_g : IsLeast { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () L } 3 :=
    ⟨hLip_g, fun L hL => hLow_g L hL⟩
  have hsInf_g : sInf { L : ENNReal | HasScalarLipBound realStdGauge ex3_5_g ex3_5_U () () L } = 3 :=
    le_antisymm (sInf_le hLip_g) (le_sInf fun L hL => hLow_g L hL)
  exact ⟨hLip_f, hLow_f, hLeast_f, hsInf_f, hLip_g, hLow_g, hLeast_g, hsInf_g⟩

/-- `CH03-P30-04`：习题 3.5(iii-b) — 在精度 `ε = 7/4` 下将最优 Lip 常数 `L_f = 1` 与 `L_g = 3` 代入命题 3.19 的一般覆盖数上界 `N(ε, ϕ(U)) ≤ N(ε/L, U)`，并逐项与真实覆盖数比较：
对 `f`，上界给出 `2`，与真实覆盖数 `2` 相等（紧）；对 `g`，上界给出 `N(7/12, U) = 4`，严格大于真实覆盖数 `2`（松）。 -/
theorem ex_3_5_part_iii_bound_comparison :
    covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_f ex3_5_U) ≤
      covering_number realStdExtDist ((7 / 4 : ENNReal) / 1) ex3_5_U ∧
    covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_f ex3_5_U) = 2 ∧
    covering_number realStdExtDist ((7 / 4 : ENNReal) / 1) ex3_5_U = 2 ∧
    covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_f ex3_5_U) =
      covering_number realStdExtDist ((7 / 4 : ENNReal) / 1) ex3_5_U ∧
    covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_g ex3_5_U) ≤
      covering_number realStdExtDist ((7 / 4 : ENNReal) / 3) ex3_5_U ∧
    ((7 / 4 : ENNReal) / 3) = (7 / 12 : ENNReal) ∧
    covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_g ex3_5_U) = 2 ∧
    covering_number realStdExtDist ((7 / 4 : ENNReal) / 3) ex3_5_U = 4 ∧
    covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_g ex3_5_U) <
      covering_number realStdExtDist ((7 / 4 : ENNReal) / 3) ex3_5_U := by
  have h74_eq : (7 / 4 : ENNReal) = ENNReal.ofReal (7 / 4 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have h712_eq : (7 / 12 : ENNReal) = ENNReal.ofReal (7 / 12 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 12)]
    norm_num
  have hdiv3 : ((7 / 4 : ENNReal) / 3) = (7 / 12 : ENNReal) := by
    rw [h74_eq, h712_eq, show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have h74_pos : (0 : ENNReal) < 7 / 4 := by
    rw [h74_eq]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h74_fin : (7 / 4 : ENNReal) < ⊤ := by
    rw [h74_eq]
    exact ENNReal.ofReal_lt_top
  have hU_ne : ex3_5_U.Nonempty := ⟨.ofReal 0, Or.inl rfl⟩
  have hLip_f := ex_3_5_part_iii_optimal_scalar_lip.1
  have hLip_g := ex_3_5_part_iii_optimal_scalar_lip.2.2.2.2.1
  -- 直接应用命题 3.19 的一般覆盖数上界引理
  have hbound_f :
      covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_f ex3_5_U) ≤
        covering_number realStdExtDist ((7 / 4 : ENNReal) / 1) ex3_5_U :=
    (prop_3_19_covering_number_le realStdGauge ex3_5_f ex3_5_U () () (7 / 4) 1
      hU_ne hLip_f.1 h74_pos h74_fin zero_lt_one ENNReal.one_lt_top hLip_f.2).2
  have hbound_g :
      covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_g ex3_5_U) ≤
        covering_number realStdExtDist ((7 / 4 : ENNReal) / 3) ex3_5_U :=
    (prop_3_19_covering_number_le realStdGauge ex3_5_g ex3_5_U () () (7 / 4) 3
      hU_ne hLip_g.1 h74_pos h74_fin (by norm_num) (by simp) hLip_g.2).2
  have hcov_74 : covering_number realStdExtDist (7 / 4 : ENNReal) ex3_5_U = 2 :=
    ex_3_5_part_i_covering_piecewise_and_noninternal.2.2.2.2.2.2.2.2.2
  have himg_f := ex_3_5_part_ii_images_covering_and_entropyDiff.2.2.1
  have himg_g := ex_3_5_part_ii_images_covering_and_entropyDiff.2.2.2.1
  have htrue_f :
      covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_f ex3_5_U) = 2 := by
    rw [himg_f, hcov_74]
  have hrhs_f :
      covering_number realStdExtDist ((7 / 4 : ENNReal) / 1) ex3_5_U = 2 := by
    rw [div_one, hcov_74]
  have htrue_g :
      covering_number realStdExtDist (7 / 4 : ENNReal) (operator_image ex3_5_g ex3_5_U) = 2 := by
    rw [himg_g, hcov_74]
  have h712_pos : (0 : ENNReal) < 7 / 12 := by
    rw [h712_eq]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h712_le1 : (7 / 12 : ENNReal) ≤ 1 := by
    rw [h712_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hrhs_g :
      covering_number realStdExtDist ((7 / 4 : ENNReal) / 3) ex3_5_U = 4 := by
    rw [hdiv3]
    exact ex_3_5_part_i_covering_piecewise_and_noninternal.2.1 (7 / 12) h712_pos h712_le1
  refine ⟨hbound_f, htrue_f, hrhs_f, by rw [htrue_f, hrhs_f],
    hbound_g, hdiv3, htrue_g, hrhs_g, ?_⟩
  rw [htrue_g, hrhs_g]
  norm_num

end Ch03
