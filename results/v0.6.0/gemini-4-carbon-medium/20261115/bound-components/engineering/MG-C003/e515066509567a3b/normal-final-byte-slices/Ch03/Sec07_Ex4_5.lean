import Ch03.Sec07_Ex1_3
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset
 
/-! ### 习题 3.4：输入域改变下的阈值分类 (CH03-P29-01 .. 05) -/
 
/-- 单分量通常距离规范族 `realStdGauge`。 -/
noncomputable abbrev realStdGauge : Unit → RealWithBot → RealWithBot → ENNReal :=
  fun _ => realStdDist
 
@[simp] theorem realStdDist_val (x y : ℝ) :
    realStdDist (.val x) (.val y) = ENNReal.ofReal |x - y| := rfl
 
/-- 习题 3.4 中的向下取整算子 `f(x) = ⌊x⌋, f(⊥) = ⊥`。 -/
noncomputable def ex34Floor : Operator RealWithBot RealWithBot.bot where
  func
    | .bot => .bot
    | .val x => .val (Int.floor x : ℝ)
  preserves_bot := rfl
 
@[simp] theorem ex34Floor_val (x : ℝ) :
    ex34Floor.func (.val x) = .val (Int.floor x : ℝ) := rfl
 
private theorem val_image_sub_dom_ex34Floor (S : Set ℝ) :
    RealWithBot.val '' S ⊆ dom ex34Floor := by
  rintro _ ⟨x, _, rfl⟩ hbot
  cases hbot
 
/-- 实闭区间 `[a, b]`（`a ≤ b`）嵌入 `RealWithBot` 后的直径等于 `b - a`。 -/
private theorem setDiam_val_Icc (a b : ℝ) (hab : a ≤ b) :
    setDiam realStdDist (RealWithBot.val '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup₂_le
    rintro _ ⟨x, ⟨hxa, hxb⟩, rfl⟩
    apply iSup₂_le
    rintro _ ⟨y, ⟨hya, hyb⟩, rfl⟩
    rw [realStdDist_val]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;> linarith
  · have ha_mem : RealWithBot.val a ∈ RealWithBot.val '' Set.Icc a b :=
      ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    have hb_mem : RealWithBot.val b ∈ RealWithBot.val '' Set.Icc a b :=
      ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    refine le_iSup₂_of_le (.val a) ha_mem (le_iSup₂_of_le (.val b) hb_mem ?_)
    rw [realStdDist_val, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
 
/-- 当闭区间 `[a, b]` 满足 `0 ≤ a < 1 ≤ b` 时，基点 `1` 处跨越跃变点，点态与统一零化半径均为 `0`。 -/
private theorem ex34Floor_zero_radius_on_Icc (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb1 : 1 ≤ b) :
    pointwiseNullRadius ex34Floor realStdDist realStdDist (.val 1)
      (RealWithBot.val '' Set.Icc a b) = 0 ∧
    uniformNullRadiusComp realStdGauge ex34Floor () ()
      (RealWithBot.val '' Set.Icc a b) = 0 := by
  let D : Set RealWithBot := RealWithBot.val '' Set.Icc a b
  have h1_mem : RealWithBot.val 1 ∈ D := ⟨1, ⟨le_of_lt ha1, hb1⟩, rfl⟩
  have hpt : pointwiseNullRadius ex34Floor realStdDist realStdDist (.val 1) D = 0 := by
    apply pointwiseNullRadius_eq_zero_of_no_valid
    rintro ⟨r, hr0, hrtop, hsub⟩
    have hr_ne_top : r ≠ ⊤ := lt_top_iff_ne_top.mp hrtop
    let ρ : ℝ := r.toReal
    have hρ_pos : 0 < ρ := ENNReal.toReal_pos (ne_of_gt hr0) hr_ne_top
    let x : ℝ := max a (1 - ρ / 2)
    have hax : a ≤ x := le_max_left _ _
    have hx1 : x < 1 := max_lt ha1 (by linarith)
    have hxb : x ≤ b := le_trans (le_of_lt hx1) hb1
    have hx0 : 0 ≤ x := le_trans ha0 hax
    have hxD : RealWithBot.val x ∈ D := ⟨x, ⟨hax, hxb⟩, rfl⟩
    have hx_ball : RealWithBot.val x ∈ ball realStdDist (.val 1) r := by
      simp only [ball, Set.mem_setOf_eq, realStdDist_val]
      have hdist_lt : |x - 1| < ρ := by
        have hge : 1 - ρ / 2 ≤ x := le_max_right _ _
        rw [abs_of_neg (by linarith)]
        linarith
      rw [← ENNReal.ofReal_toReal hr_ne_top]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ_pos).mpr hdist_lt
    have hout := (hsub ⟨hx_ball, hxD⟩).2
    have hfx : Int.floor x = 0 :=
      Int.floor_eq_iff.mpr ⟨by simpa using hx0, by simpa using hx1⟩
    have hf1 : Int.floor (1 : ℝ) = 1 := by norm_num
    rw [ex34Floor_val, ex34Floor_val, hfx, hf1, realStdDist_val] at hout
    norm_num at hout
  refine ⟨hpt, le_antisymm ?_ (zero_le _)⟩
  unfold uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
  have hle : (⨅ y ∈ D, pointwiseNullRadius ex34Floor realStdDist realStdDist y D) ≤
      pointwiseNullRadius ex34Floor realStdDist realStdDist (RealWithBot.val 1) D :=
    iInf₂_le (RealWithBot.val 1) h1_mem
  rwa [hpt] at hle
 
/-- 习题 3.4(i-a) 输入域 `D₁ = [0, 1/2]`。 -/
def ex34D1 : Set RealWithBot := RealWithBot.val '' Set.Icc (0 : ℝ) (1 / 2)
 
/-- 习题 3.4(i-b) 输入域 `D₂ = [9/10, 11/10]`。 -/
def ex34D2 : Set RealWithBot := RealWithBot.val '' Set.Icc (9 / 10 : ℝ) (11 / 10)
 
/-- 习题 3.4(i-c) 输入域 `D₃ = {0, 2}`。 -/
def ex34D3 : Set RealWithBot := {.val 0, .val 2}
 
/-- 习题 3.4(i-d) 输入域 `D₄ = [0, 2]`。 -/
def ex34D4 : Set RealWithBot := RealWithBot.val '' Set.Icc (0 : ℝ) 2
 
/-- CH03-P29-01: 习题 3.4(i-a) `D₁ = [0, 1/2]` 的直径为 `1/2`、统一零化半径为 `+∞`、阈值类型为 `(1, 1)`。 -/
theorem ex_3_4_i_a_D1 :
    ex34D1.Nonempty ∧
    ex34D1 ⊆ dom ex34Floor ∧
    setDiam realStdDist ex34D1 = 1 / 2 ∧
    uniformNullRadiusComp realStdGauge ex34Floor () () ex34D1 = ⊤ ∧
    channelType realStdGauge (diameterScaleFamily realStdGauge) ex34Floor ex34D1 1 1 () () =
      (1, 1) := by
  have hne : ex34D1.Nonempty := ⟨.val 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hdom : ex34D1 ⊆ dom ex34Floor := val_image_sub_dom_ex34Floor _
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hdiam : setDiam realStdDist ex34D1 = 1 / 2 := by
    unfold ex34D1
    rw [setDiam_val_Icc 0 (1 / 2) (by norm_num), sub_zero, hhalf]
  have hconst : () ∈ I_const realStdGauge ex34Floor ex34D1 := by
    rintro _ ⟨x, ⟨hx0, hx12⟩, rfl⟩ _ ⟨y, ⟨hy0, hy12⟩, rfl⟩
    have hfx : Int.floor x = 0 :=
      Int.floor_eq_iff.mpr ⟨by simpa using hx0, by norm_num; linarith⟩
    have hfy : Int.floor y = 0 :=
      Int.floor_eq_iff.mpr ⟨by simpa using hy0, by norm_num; linarith⟩
    simp [realStdGauge, hfx, hfy]
  have hunif : uniformNullRadiusComp realStdGauge ex34Floor () () ex34D1 = ⊤ := by
    have hsub := (prop_3_8_i_b_const_subfamily_radius_top realStdGauge ex34Floor ex34D1 {()} ()
      hne hdom (Set.singleton_nonempty ()) (Set.singleton_subset_iff.mpr hconst)).2
    rwa [uniformNullRadiusSubfamily_singleton, nullMatrix] at hsub
  refine ⟨hne, hdom, hdiam, hunif, ?_⟩
  simp [channelType, diameterScaleFamily, realStdGauge, hdiam, hunif, ind01_eq_one_iff]
 
/-- CH03-P29-02: 习题 3.4(i-b) `D₂ = [9/10, 11/10]` 的直径为 `1/5`、统一零化半径为 `0`、阈值类型为 `(1, 0)`。 -/
theorem ex_3_4_i_b_D2 :
    ex34D2.Nonempty ∧
    ex34D2 ⊆ dom ex34Floor ∧
    setDiam realStdDist ex34D2 = 1 / 5 ∧
    uniformNullRadiusComp realStdGauge ex34Floor () () ex34D2 = 0 ∧
    channelType realStdGauge (diameterScaleFamily realStdGauge) ex34Floor ex34D2 1 1 () () =
      (1, 0) := by
  have hne : ex34D2.Nonempty := ⟨.val 1, 1, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hdom : ex34D2 ⊆ dom ex34Floor := val_image_sub_dom_ex34Floor _
  have hfifth : ENNReal.ofReal (1 / 5 : ℝ) = (1 / 5 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hdiam : setDiam realStdDist ex34D2 = 1 / 5 := by
    unfold ex34D2
    rw [setDiam_val_Icc (9 / 10) (11 / 10) (by norm_num)]
    have hsub : (11 / 10 : ℝ) - 9 / 10 = 1 / 5 := by norm_num
    rw [hsub, hfifth]
  have hunif : uniformNullRadiusComp realStdGauge ex34Floor () () ex34D2 = 0 :=
    (ex34Floor_zero_radius_on_Icc (9 / 10) (11 / 10) (by norm_num) (by norm_num) (by norm_num)).2
  refine ⟨hne, hdom, hdiam, hunif, ?_⟩
  simp [channelType, diameterScaleFamily, realStdGauge, hdiam, hunif,
    ind01_eq_one_iff, ind01_eq_zero_iff]
 
/-- CH03-P29-03: 习题 3.4(i-c) `D₃ = {0, 2}` 的直径为 `2`、各点与统一零化半径均为 `2`、阈值类型为 `(0, 1)`。 -/
theorem ex_3_4_i_c_D3 :
    ex34D3 = RealWithBot.val '' ({0, 2} : Set ℝ) ∧
    ex34D3.Nonempty ∧
    ex34D3 ⊆ dom ex34Floor ∧
    setDiam realStdDist ex34D3 = 2 ∧
    (∀ y ∈ ex34D3, pointwiseNullRadius ex34Floor realStdDist realStdDist y ex34D3 = 2) ∧
    uniformNullRadiusComp realStdGauge ex34Floor () () ex34D3 = 2 ∧
    channelType realStdGauge (diameterScaleFamily realStdGauge) ex34Floor ex34D3 1 1 () () =
      (0, 1) := by
  have himg : ex34D3 = RealWithBot.val '' ({0, 2} : Set ℝ) := by
    ext z
    simp [ex34D3, eq_comm]
  have hne : ex34D3.Nonempty := ⟨.val 0, Set.mem_insert _ _⟩
  have hdom : ex34D3 ⊆ dom ex34Floor := by
    rw [himg]
    exact val_image_sub_dom_ex34Floor _
  have hdiam : setDiam realStdDist ex34D3 = 2 := by
    apply le_antisymm
    · apply iSup₂_le
      rintro _ (rfl | rfl)
      · apply iSup₂_le
        rintro _ (rfl | rfl) <;> simp [realStdDist]
      · apply iSup₂_le
        rintro _ (rfl | rfl) <;> simp [realStdDist]
    · refine le_iSup₂_of_le (.val 0) (Set.mem_insert _ _)
        (le_iSup₂_of_le (.val 2) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) ?_)
      simp [realStdDist]
  have hpt : ∀ y ∈ ex34D3,
      pointwiseNullRadius ex34Floor realStdDist realStdDist y ex34D3 = 2 := by
    intro y hy
    have hset : {r : ENNReal | ValidNullRadius ex34Floor realStdDist realStdDist y ex34D3 r} =
        Set.Ioc 0 2 := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, ValidNullRadius]
      constructor
      · rintro ⟨hr0, _, hsub⟩
        refine ⟨hr0, ?_⟩
        by_contra hgt2
        push Not at hgt2
        rcases hy with rfl | rfl
        · have h2_ball : RealWithBot.val 2 ∈ ball realStdDist (.val 0) r := by
            simpa [ball, realStdDist] using hgt2
          have h2_mem : RealWithBot.val 2 ∈ ex34D3 :=
            Set.mem_insert_of_mem _ (Set.mem_singleton _)
          have hout := (hsub ⟨h2_ball, h2_mem⟩).2
          have hf0 : Int.floor (0 : ℝ) = 0 := by norm_num
          simp [hf0, realStdDist] at hout
        · have h0_ball : RealWithBot.val 0 ∈ ball realStdDist (.val 2) r := by
            simpa [ball, realStdDist] using hgt2
          have h0_mem : RealWithBot.val 0 ∈ ex34D3 := Set.mem_insert _ _
          have hout := (hsub ⟨h0_ball, h0_mem⟩).2
          have hf0 : Int.floor (0 : ℝ) = 0 := by norm_num
          simp [hf0, realStdDist] at hout
      · rintro ⟨hr0, hrle2⟩
        refine ⟨hr0, lt_of_le_of_lt hrle2 ENNReal.ofNat_lt_top, ?_⟩
        rintro x ⟨hx_ball, hxD⟩
        refine ⟨hxD, ?_⟩
        rcases hy with rfl | rfl <;> rcases hxD with rfl | rfl
        · simp [realStdDist]
        · exfalso
          simp [ball, realStdDist] at hx_ball
          exact not_lt_of_ge hrle2 hx_ball
        · exfalso
          simp [ball, realStdDist] at hx_ball
          exact not_lt_of_ge hrle2 hx_ball
        · simp [realStdDist]
    unfold pointwiseNullRadius
    rw [hset]
    apply le_antisymm
    · exact sSup_le (fun _ hr => hr.2)
    · exact le_sSup (s := Set.Ioc (0 : ENNReal) 2) ⟨by norm_num, le_rfl⟩
  have hunif : uniformNullRadiusComp realStdGauge ex34Floor () () ex34D3 = 2 := by
    unfold uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn realStdGauge
    apply le_antisymm
    · exact le_trans (iInf₂_le (RealWithBot.val 0) (Set.mem_insert _ _))
        (le_of_eq (hpt (RealWithBot.val 0) (Set.mem_insert _ _)))
    · exact le_iInf₂ (fun y hy => le_of_eq (hpt y hy).symm)
  have hnlt : ¬ ((2 : ENNReal) < 1) := by norm_num
  have hge1 : (1 : ENNReal) ≤ 2 := by norm_num
  refine ⟨himg, hne, hdom, hdiam, hpt, hunif, ?_⟩
  simp [channelType, diameterScaleFamily, realStdGauge, hdiam, hunif,
    ind01_eq_one_iff, ind01_eq_zero_iff, hnlt, hge1]
 
/-- CH03-P29-04: 习题 3.4(i-d) `D₄ = [0, 2]` 的直径为 `2`、统一零化半径为 `0`、阈值类型为 `(0, 0)`。 -/
theorem ex_3_4_i_d_D4 :
    ex34D4.Nonempty ∧
    ex34D4 ⊆ dom ex34Floor ∧
    setDiam realStdDist ex34D4 = 2 ∧
    uniformNullRadiusComp realStdGauge ex34Floor () () ex34D4 = 0 ∧
    channelType realStdGauge (diameterScaleFamily realStdGauge) ex34Floor ex34D4 1 1 () () =
      (0, 0) := by
  have hne : ex34D4.Nonempty := ⟨.val 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hdom : ex34D4 ⊆ dom ex34Floor := val_image_sub_dom_ex34Floor _
  have hdiam : setDiam realStdDist ex34D4 = 2 := by
    unfold ex34D4
    rw [setDiam_val_Icc 0 2 (by norm_num), sub_zero]
    simp
  have hunif : uniformNullRadiusComp realStdGauge ex34Floor () () ex34D4 = 0 :=
    (ex34Floor_zero_radius_on_Icc 0 2 le_rfl zero_lt_one (by norm_num)).2
  have hnlt : ¬ ((2 : ENNReal) < 1) := by norm_num
  refine ⟨hne, hdom, hdiam, hunif, ?_⟩
  simp [channelType, diameterScaleFamily, realStdGauge, hdiam, hunif,
    ind01_eq_zero_iff, hnlt]
 
/-- CH03-P29-05: 习题 3.4(ii) 以 (i-c) 的合法离散反例 `D = {0, 2}` 否定缺少直径条件时“`\underline{r}^N ≥ 1` 即整体零化”，并刻画其正零化半径来源于两点距离为 `2` 使半径 `≤ 2` 的受限开球退化为单点集。 -/
theorem ex_3_4_ii_no_diam_counterexample :
    ¬ (∀ D : Set ℝ, D.Nonempty →
        1 ≤ uniformNullRadiusComp realStdGauge ex34Floor () () (RealWithBot.val '' D) →
        ∀ x ∈ D, ∀ y ∈ D,
          realStdDist (ex34Floor.func (.val x)) (ex34Floor.func (.val y)) = 0) ∧
    (({0, 2} : Set ℝ).Nonempty ∧
     RealWithBot.val '' ({0, 2} : Set ℝ) = ex34D3 ∧
     1 ≤ setDiam realStdDist ex34D3 ∧
     uniformNullRadiusComp realStdGauge ex34Floor () () ex34D3 = 2 ∧
     1 ≤ uniformNullRadiusComp realStdGauge ex34Floor () () ex34D3 ∧
     realStdDist (ex34Floor.func (.val 0)) (ex34Floor.func (.val 2)) = 2 ∧
     realStdDist (ex34Floor.func (.val 0)) (ex34Floor.func (.val 2)) ≠ 0 ∧
     (∀ x ∈ ex34D3, ∀ y ∈ ex34D3, x ≠ y → realStdDist x y = 2) ∧
     (∀ y ∈ ex34D3, ∀ r ∈ Set.Ioc (0 : ENNReal) 2,
        ball realStdDist y r ∩ ex34D3 = {y})) := by
  rcases ex_3_4_i_c_D3 with ⟨himg, _, _, hdiam, _, hunif, _⟩
  have hout2 : realStdDist (ex34Floor.func (.val 0)) (ex34Floor.func (.val 2)) = 2 := by
    have hf0 : Int.floor (0 : ℝ) = 0 := by norm_num
    simp [hf0, realStdDist]
  have hout_ne : realStdDist (ex34Floor.func (.val 0)) (ex34Floor.func (.val 2)) ≠ 0 := by
    rw [hout2]; norm_num
  have hge1 : (1 : ENNReal) ≤ uniformNullRadiusComp realStdGauge ex34Floor () () ex34D3 := by
    rw [hunif]; norm_num
  have hdiam_ge1 : (1 : ENNReal) ≤ setDiam realStdDist ex34D3 := by
    rw [hdiam]; norm_num
  have hnot : ¬ (∀ D : Set ℝ, D.Nonempty →
      1 ≤ uniformNullRadiusComp realStdGauge ex34Floor () () (RealWithBot.val '' D) →
      ∀ x ∈ D, ∀ y ∈ D,
        realStdDist (ex34Floor.func (.val x)) (ex34Floor.func (.val y)) = 0) := by
    intro hall
    have hge1' : 1 ≤ uniformNullRadiusComp realStdGauge ex34Floor () ()
        (RealWithBot.val '' ({0, 2} : Set ℝ)) := by
      rwa [← himg]
    have h0 := hall {0, 2} ⟨0, Set.mem_insert _ _⟩ hge1'
      0 (Set.mem_insert _ _) 2 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    exact hout_ne h0
  refine ⟨hnot, ⟨0, Set.mem_insert _ _⟩, himg.symm, hdiam_ge1, hunif, hge1, hout2, hout_ne, ?_, ?_⟩
  · rintro _ (rfl | rfl) _ (rfl | rfl) hne
    · exact False.elim (hne rfl)
    · simp [realStdDist]
    · simp [realStdDist]
    · exact False.elim (hne rfl)
  · intro y hy r ⟨hr0, hrle2⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx_ball, hxD⟩
      rcases hy with rfl | rfl <;> rcases hxD with rfl | rfl
      · rfl
      · exfalso; simp [ball, realStdDist] at hx_ball; exact not_lt_of_ge hrle2 hx_ball
      · exfalso; simp [ball, realStdDist] at hx_ball; exact not_lt_of_ge hrle2 hx_ball
      · rfl
    · rintro rfl
      exact ⟨by simp [ball, realStdDist_is_extended.dist_self, hr0], hy⟩
 
/-! ### 习题 3.5：像集重排与覆盖估计 (CH03-P30-01 .. 04) -/
 
/-- 习题 3.5 的四点评估域 `U = {0, 1, 2, 3}`。 -/
def ex35U : Set RealWithBot := {.val 0, .val 1, .val 2, .val 3}
 
private theorem mem_ex35U_iff (x : RealWithBot) :
    x ∈ ex35U ↔ x = .val 0 ∨ x = .val 1 ∨ x = .val 2 ∨ x = .val 3 := by
  simp [ex35U]
 
/-- 习题 3.5 算子 `f`：在 `U` 上保持 `0, 1, 2, 3`，在 `𝒳 \ U` 上取值 `⊥`。 -/
noncomputable def ex35F : Operator RealWithBot RealWithBot.bot where
  func x :=
    open scoped Classical in
    if x = .val 0 then .val 0
    else if x = .val 1 then .val 1
    else if x = .val 2 then .val 2
    else if x = .val 3 then .val 3
    else .bot
  preserves_bot := by
    classical
    simp
 
/-- 习题 3.5 算子 `g`：在 `U` 上重排为 `0 ↦ 0, 1 ↦ 3, 2 ↦ 1, 3 ↦ 2`，在 `𝒳 \ U` 上取值 `⊥`。 -/
noncomputable def ex35G : Operator RealWithBot RealWithBot.bot where
  func x :=
    open scoped Classical in
    if x = .val 0 then .val 0
    else if x = .val 1 then .val 3
    else if x = .val 2 then .val 1
    else if x = .val 3 then .val 2
    else .bot
  preserves_bot := by
    classical
    simp
 
@[simp] theorem ex35F_0 : ex35F.func (.val 0) = .val 0 := by classical simp [ex35F]
@[simp] theorem ex35F_1 : ex35F.func (.val 1) = .val 1 := by
  classical
  have h10 : RealWithBot.val 1 ≠ .val 0 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  simp [ex35F, h10]
@[simp] theorem ex35F_2 : ex35F.func (.val 2) = .val 2 := by
  classical
  have h20 : RealWithBot.val 2 ≠ .val 0 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  have h21 : RealWithBot.val 2 ≠ .val 1 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  simp [ex35F, h20, h21]
@[simp] theorem ex35F_3 : ex35F.func (.val 3) = .val 3 := by
  classical
  have h30 : RealWithBot.val 3 ≠ .val 0 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  have h31 : RealWithBot.val 3 ≠ .val 1 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  have h32 : RealWithBot.val 3 ≠ .val 2 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  simp [ex35F, h30, h31, h32]
 
@[simp] theorem ex35G_0 : ex35G.func (.val 0) = .val 0 := by classical simp [ex35G]
@[simp] theorem ex35G_1 : ex35G.func (.val 1) = .val 3 := by
  classical
  have h10 : RealWithBot.val 1 ≠ .val 0 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  simp [ex35G, h10]
@[simp] theorem ex35G_2 : ex35G.func (.val 2) = .val 1 := by
  classical
  have h20 : RealWithBot.val 2 ≠ .val 0 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  have h21 : RealWithBot.val 2 ≠ .val 1 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  simp [ex35G, h20, h21]
@[simp] theorem ex35G_3 : ex35G.func (.val 3) = .val 2 := by
  classical
  have h30 : RealWithBot.val 3 ≠ .val 0 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  have h31 : RealWithBot.val 3 ≠ .val 1 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  have h32 : RealWithBot.val 3 ≠ .val 2 := fun h => by have := RealWithBot.val.inj h; norm_num at this
  simp [ex35G, h30, h31, h32]
 
theorem ex35_domains_and_outside :
    (∀ x ∉ ex35U, ex35F.func x = .bot) ∧
    (∀ x ∉ ex35U, ex35G.func x = .bot) ∧
    dom ex35F = ex35U ∧
    dom ex35G = ex35U := by
  classical
  have houtF : ∀ x ∉ ex35U, ex35F.func x = .bot := by
    intro x hx
    rw [mem_ex35U_iff] at hx
    push Not at hx
    rcases hx with ⟨h0, h1, h2, h3⟩
    simp [ex35F, h0, h1, h2, h3]
  have houtG : ∀ x ∉ ex35U, ex35G.func x = .bot := by
    intro x hx
    rw [mem_ex35U_iff] at hx
    push Not at hx
    rcases hx with ⟨h0, h1, h2, h3⟩
    simp [ex35G, h0, h1, h2, h3]
  refine ⟨houtF, houtG, ?_, ?_⟩
  · ext x
    constructor
    · intro hdom
      by_contra hnot
      exact hdom (houtF x hnot)
    · intro hx hbot
      rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl
      · rw [ex35F_0] at hbot; cases hbot
      · rw [ex35F_1] at hbot; cases hbot
      · rw [ex35F_2] at hbot; cases hbot
      · rw [ex35F_3] at hbot; cases hbot
  · ext x
    constructor
    · intro hdom
      by_contra hnot
      exact hdom (houtG x hnot)
    · intro hx hbot
      rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl
      · rw [ex35G_0] at hbot; cases hbot
      · rw [ex35G_1] at hbot; cases hbot
      · rw [ex35G_2] at hbot; cases hbot
      · rw [ex35G_3] at hbot; cases hbot
 
private theorem ennreal_seven_fourths : (7 / 4 : ENNReal) = ENNReal.ofReal (7 / 4) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
 
/-- CH03-P30-01: 习题 3.5(i) 对所有有限正 `ε` 给出 `𝒩(ε, U)` 的完整三段公式（含端点 `ε = 1` 取 `4`、`ε = 2` 取 `2`），并证明 `ε = 7/4` 时外部点 `3/2` 虽以开球覆盖 `U`，但因 `3/2 ∉ U` 不能成为合法内部覆盖中心，内部覆盖数为 `2`。 -/
theorem ex_3_5_i_covering_piecewise_and_external_center :
    (∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realStdDist ε ex35U =
        if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1) ∧
    covering_number realStdDist 1 ex35U = 4 ∧
    covering_number realStdDist 2 ex35U = 2 ∧
    ex35U ⊆ ball realStdDist (.val (3 / 2)) (7 / 4) ∧
    RealWithBot.val (3 / 2) ∉ ex35U ∧
    (∀ S : Finset RealWithBot, RealWithBot.val (3 / 2) ∈ S →
      ¬ InternalEpsilonNet realStdDist (7 / 4) ex35U S) ∧
    ¬ InternalEpsilonNet realStdDist (7 / 4) ex35U {.val (3 / 2)} ∧
    covering_number realStdDist (7 / 4) ex35U = 2 := by
  classical
  have hmain : ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realStdDist ε ex35U =
        if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1 := by
    intro ε hε0 _hεtop
    by_cases hle1 : ε ≤ 1
    · rw [if_pos hle1]
      apply le_antisymm
      · let S4 : Finset RealWithBot := {.val 0, .val 1, .val 2, .val 3}
        have hnet4 : InternalEpsilonNet realStdDist ε ex35U S4 := by
          refine ⟨fun x hx => ?_, fun x hx => ?_⟩
          · simp [S4, mem_ex35U_iff] at hx ⊢; exact hx
          · refine ⟨x, ?_, ?_⟩
            · rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl <;> simp [S4]
            · rw [realStdDist_is_extended.dist_self]; exact hε0
        have hcard4 : (S4.card : ENNReal) ≤ 4 := by
          have hc1 : ({.val 2, .val 3} : Finset RealWithBot).card ≤ 2 := Finset.card_le_two
          have hc2 : ({.val 1, .val 2, .val 3} : Finset RealWithBot).card ≤ 3 :=
            le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ hc1)
          have hc3 : S4.card ≤ 4 :=
            le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ hc2)
          exact_mod_cast hc3
        exact le_trans (iInf_le_of_le S4 (iInf_le_of_le hnet4 le_rfl)) hcard4
      · apply le_iInf₂
        intro S hS
        let S4 : Finset RealWithBot := {.val 0, .val 1, .val 2, .val 3}
        have hsub4 : S4 ⊆ S := by
          intro x hxS4
          have hxU : x ∈ ex35U := by
            simp [S4, mem_ex35U_iff] at hxS4 ⊢; exact hxS4
          rcases hS.2 x hxU with ⟨c, hcS, hdxc⟩
          have hlt1 : realStdDist x c < 1 := lt_of_lt_of_le hdxc hle1
          have hxeq : x = c := by
            rcases (mem_ex35U_iff x).mp hxU with rfl | rfl | rfl | rfl <;>
              rcases (mem_ex35U_iff c).mp (hS.1 hcS) with rfl | rfl | rfl | rfl
            all_goals
              first
              | rfl
              | (exfalso; rw [realStdDist_val] at hlt1;
                 rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one] at hlt1;
                 norm_num at hlt1)
          rwa [hxeq]
        have hc4 : S4.card = 4 := by
          have hne01 : RealWithBot.val 0 ≠ .val 1 := fun h => by have := RealWithBot.val.inj h; norm_num at this
          have hne02 : RealWithBot.val 0 ≠ .val 2 := fun h => by have := RealWithBot.val.inj h; norm_num at this
          have hne03 : RealWithBot.val 0 ≠ .val 3 := fun h => by have := RealWithBot.val.inj h; norm_num at this
          have hne12 : RealWithBot.val 1 ≠ .val 2 := fun h => by have := RealWithBot.val.inj h; norm_num at this
          have hne13 : RealWithBot.val 1 ≠ .val 3 := fun h => by have := RealWithBot.val.inj h; norm_num at this
          have hne23 : RealWithBot.val 2 ≠ .val 3 := fun h => by have := RealWithBot.val.inj h; norm_num at this
          simp [S4, hne01, hne02, hne03, hne12, hne13, hne23]
        have h4le : 4 ≤ S.card := by rw [← hc4]; exact Finset.card_le_card hsub4
        exact_mod_cast h4le
    · rw [if_neg hle1]
      have hgt1 : 1 < ε := lt_of_not_ge hle1
      by_cases hle2 : ε ≤ 2
      · rw [if_pos hle2]
        apply le_antisymm
        · let S2 : Finset RealWithBot := {.val 0, .val 2}
          have hnet2 : InternalEpsilonNet realStdDist ε ex35U S2 := by
            refine ⟨fun x hx => ?_, fun x hx => ?_⟩
            · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx2
              · exact (mem_ex35U_iff _).mpr (Or.inl rfl)
              · rw [Finset.mem_singleton.mp hx2]
                exact (mem_ex35U_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))
            · rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl
              · refine ⟨.val 0, by simp [S2], ?_⟩; simp [realStdDist, hε0]
              · refine ⟨.val 0, by simp [S2], ?_⟩
                simpa [realStdDist] using hgt1
              · refine ⟨.val 2, by simp [S2], ?_⟩; simp [realStdDist, hε0]
              · refine ⟨.val 2, by simp [S2], ?_⟩
                have h32 : |(3 : ℝ) - 2| = 1 := by norm_num
                rw [realStdDist_val, h32, ENNReal.ofReal_one]
                exact hgt1
          have hcard2 : (S2.card : ENNReal) ≤ 2 := by
            exact_mod_cast (Finset.card_le_two : S2.card ≤ 2)
          exact le_trans (iInf_le_of_le S2 (iInf_le_of_le hnet2 le_rfl)) hcard2
        · apply le_iInf₂
          intro S hS
          rcases hS.2 (.val 0) ((mem_ex35U_iff _).mpr (Or.inl rfl)) with ⟨c0, hc0S, hd0⟩
          rcases hS.2 (.val 3) ((mem_ex35U_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))) with ⟨c3, hc3S, hd3⟩
          have hd0_lt2 : realStdDist (.val 0) c0 < 2 := lt_of_lt_of_le hd0 hle2
          have hd3_lt2 : realStdDist (.val 3) c3 < 2 := lt_of_lt_of_le hd3 hle2
          have hc0_01 : c0 = .val 0 ∨ c0 = .val 1 := by
            rcases (mem_ex35U_iff c0).mp (hS.1 hc0S) with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exfalso; simp [realStdDist] at hd0_lt2
            · exfalso
              have h03 : |(0 : ℝ) - 3| = 3 := by norm_num
              rw [realStdDist_val, h03] at hd0_lt2
              have h3eq : ENNReal.ofReal 3 = (3 : ENNReal) := by norm_num
              rw [h3eq] at hd0_lt2
              norm_num at hd0_lt2
          have hc3_23 : c3 = .val 2 ∨ c3 = .val 3 := by
            rcases (mem_ex35U_iff c3).mp (hS.1 hc3S) with rfl | rfl | rfl | rfl
            · exfalso
              have h30 : |(3 : ℝ) - 0| = 3 := by norm_num
              rw [realStdDist_val, h30] at hd3_lt2
              have h3eq : ENNReal.ofReal 3 = (3 : ENNReal) := by norm_num
              rw [h3eq] at hd3_lt2
              norm_num at hd3_lt2
            · exfalso
              have h31 : |(3 : ℝ) - 1| = 2 := by norm_num
              rw [realStdDist_val, h31] at hd3_lt2
              simp at hd3_lt2
            · exact Or.inl rfl
            · exact Or.inr rfl
          have hne : c0 ≠ c3 := by
            rcases hc0_01 with rfl | rfl <;> rcases hc3_23 with rfl | rfl <;>
              (intro h; have := RealWithBot.val.inj h; norm_num at this)
          have h2le : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨c0, hc0S, c3, hc3S, hne⟩
          exact_mod_cast h2le
      · rw [if_neg hle2]
        have hgt2 : 2 < ε := lt_of_not_ge hle2
        apply le_antisymm
        · have hnet1 : InternalEpsilonNet realStdDist ε ex35U {.val 1} := by
            refine ⟨fun x hx => ?_, fun x hx => ?_⟩
            · rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
              rw [hx]; exact (mem_ex35U_iff _).mpr (Or.inr (Or.inl rfl))
            · refine ⟨.val 1, Finset.mem_singleton_self _, ?_⟩
              rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl
              · simp [realStdDist]; exact lt_trans (by norm_num : (1 : ENNReal) < 2) hgt2
              · simp [realStdDist, hε0]
              · have h21 : |(2 : ℝ) - 1| = 1 := by norm_num
                rw [realStdDist_val, h21, ENNReal.ofReal_one]
                exact lt_trans (by norm_num : (1 : ENNReal) < 2) hgt2
              · have h31 : |(3 : ℝ) - 1| = 2 := by norm_num
                rw [realStdDist_val, h31]
                simpa using hgt2
          exact le_trans (iInf_le_of_le {.val 1} (iInf_le_of_le hnet1 le_rfl)) (by simp)
        · exact one_le_covering_number_of_nonempty realStdDist ε ex35U
            ⟨.val 0, (mem_ex35U_iff _).mpr (Or.inl rfl)⟩
  have hcov1 : covering_number realStdDist 1 ex35U = 4 := by
    rw [hmain 1 zero_lt_one ENNReal.one_lt_top]
    simp
  have hcov2 : covering_number realStdDist 2 ex35U = 2 := by
    rw [hmain 2 (by norm_num) ENNReal.ofNat_lt_top]
    have hn1 : ¬ ((2 : ENNReal) ≤ 1) := by norm_num
    simp [hn1]
  have hball_ext : ex35U ⊆ ball realStdDist (.val (3 / 2)) (7 / 4) := by
    intro x hx
    simp only [ball, Set.mem_setOf_eq]
    rw [ennreal_seven_fourths]
    rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl <;>
      (rw [realStdDist_val, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num)
  have hnot_mem : RealWithBot.val (3 / 2) ∉ ex35U := by
    rw [mem_ex35U_iff]
    rintro (h | h | h | h) <;> (have := RealWithBot.val.inj h; norm_num at this)
  have hno_internal : ∀ S : Finset RealWithBot, RealWithBot.val (3 / 2) ∈ S →
      ¬ InternalEpsilonNet realStdDist (7 / 4) ex35U S := by
    intro S hmem hnet
    exact hnot_mem (hnet.1 hmem)
  have h74_pos : (0 : ENNReal) < 7 / 4 := by
    rw [ennreal_seven_fourths]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h74_top : (7 / 4 : ENNReal) < ⊤ := by
    rw [ennreal_seven_fourths]; exact ENNReal.ofReal_lt_top
  have h74_gt1 : ¬ ((7 / 4 : ENNReal) ≤ 1) := by
    rw [ennreal_seven_fourths, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one]
    norm_num
  have h74_le2 : (7 / 4 : ENNReal) ≤ 2 := by
    have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
    rw [ennreal_seven_fourths, h2]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hcov74 : covering_number realStdDist (7 / 4) ex35U = 2 := by
    rw [hmain (7 / 4) h74_pos h74_top, if_neg h74_gt1, if_pos h74_le2]
  exact ⟨hmain, hcov1, hcov2, hball_ext, hnot_mem, hno_internal,
    hno_internal {.val (3 / 2)} (Finset.mem_singleton_self _), hcov74⟩
 
/-- CH03-P30-02: 习题 3.5(ii) `f(U) = U` 且 `g(U) = U`；任意有限正精度下两像集覆盖数相等且等于 `U` 的覆盖数，两算子映射熵差良定且均为 `0`。 -/
theorem ex_3_5_ii_images_covering_and_entropy_diff :
    operator_image ex35F ex35U = ex35U ∧
    operator_image ex35G ex35U = ex35U ∧
    (∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realStdDist ε (operator_image ex35F ex35U) =
        covering_number realStdDist ε ex35U ∧
      covering_number realStdDist ε (operator_image ex35G ex35U) =
        covering_number realStdDist ε ex35U ∧
      covering_number realStdDist ε (operator_image ex35F ex35U) =
        covering_number realStdDist ε (operator_image ex35G ex35U) ∧
      (∃ hwfF : MappingEntropyDiffSingleWellDefined realStdGauge ex35F ex35U () ε,
        mappingEntropyDiffSingle realStdGauge ex35F ex35U () ε hwfF = 0) ∧
      (∃ hwfG : MappingEntropyDiffSingleWellDefined realStdGauge ex35G ex35U () ε,
        mappingEntropyDiffSingle realStdGauge ex35G ex35U () ε hwfG = 0)) := by
  have himF : operator_image ex35F ex35U = ex35U := by
    ext y
    simp only [operator_image, Set.mem_image, mem_ex35U_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩
      · rw [ex35F_0]; exact Or.inl rfl
      · rw [ex35F_1]; exact Or.inr (Or.inl rfl)
      · rw [ex35F_2]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [ex35F_3]; exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨.val 0, Or.inl rfl, ex35F_0⟩
      · exact ⟨.val 1, Or.inr (Or.inl rfl), ex35F_1⟩
      · exact ⟨.val 2, Or.inr (Or.inr (Or.inl rfl)), ex35F_2⟩
      · exact ⟨.val 3, Or.inr (Or.inr (Or.inr rfl)), ex35F_3⟩
  have himG : operator_image ex35G ex35U = ex35U := by
    ext y
    simp only [operator_image, Set.mem_image, mem_ex35U_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩
      · rw [ex35G_0]; exact Or.inl rfl
      · rw [ex35G_1]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [ex35G_2]; exact Or.inr (Or.inl rfl)
      · rw [ex35G_3]; exact Or.inr (Or.inr (Or.inl rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨.val 0, Or.inl rfl, ex35G_0⟩
      · exact ⟨.val 2, Or.inr (Or.inr (Or.inl rfl)), ex35G_2⟩
      · exact ⟨.val 3, Or.inr (Or.inr (Or.inr rfl)), ex35G_3⟩
      · exact ⟨.val 1, Or.inr (Or.inl rfl), ex35G_1⟩
  refine ⟨himF, himG, ?_⟩
  intro ε hε0 hεtop
  have hcov_pw := ex_3_5_i_covering_piecewise_and_external_center.1 ε hε0 hεtop
  have hcov_lt_top : covering_number realStdDist ε ex35U < ⊤ := by
    rw [hcov_pw]
    split_ifs <;> norm_num
  have hne : ex35U.Nonempty := ⟨.val 0, (mem_ex35U_iff _).mpr (Or.inl rfl)⟩
  have hdomF : ex35U ⊆ dom ex35F := le_of_eq ex35_domains_and_outside.2.2.1.symm
  have hdomG : ex35U ⊆ dom ex35G := le_of_eq ex35_domains_and_outside.2.2.2.symm
  have hwfF : MappingEntropyDiffSingleWellDefined realStdGauge ex35F ex35U () ε := by
    refine ⟨hne, hdomF, Set.singleton_nonempty (), Set.singleton_nonempty (),
      hε0, hεtop, Or.inl ?_⟩
    simpa [subfamily_covering_number_singleton, realStdGauge] using hcov_lt_top
  have hwfG : MappingEntropyDiffSingleWellDefined realStdGauge ex35G ex35U () ε := by
    refine ⟨hne, hdomG, Set.singleton_nonempty (), Set.singleton_nonempty (),
      hε0, hεtop, Or.inl ?_⟩
    simpa [subfamily_covering_number_singleton, realStdGauge] using hcov_lt_top
  refine ⟨by rw [himF], by rw [himG], by rw [himF, himG], ⟨hwfF, ?_⟩, ⟨hwfG, ?_⟩⟩
  · unfold mappingEntropyDiffSingle mappingEntropyDiff subfamily_covering_number
    simp [subfamily_pseudometric_singleton, realStdGauge, himF, hcov_lt_top]
  · unfold mappingEntropyDiffSingle mappingEntropyDiff subfamily_covering_number
    simp [subfamily_pseudometric_singleton, realStdGauge, himG, hcov_lt_top]
 
/-- CH03-P30-03: 习题 3.5(iii-a) `f` 与 `g` 在 `U` 上最小标量 Lip 常数分别为 `1` 与 `3`（同时证明合法性与必要下界）。 -/
theorem ex_3_5_iii_a_optimal_scalar_lip :
    HasScalarLipBound realStdGauge ex35F ex35U () () 1 ∧
    (∀ c : ENNReal, HasScalarLipBound realStdGauge ex35F ex35U () () c → 1 ≤ c) ∧
    sInf {c : ENNReal | HasScalarLipBound realStdGauge ex35F ex35U () () c} = 1 ∧
    HasScalarLipBound realStdGauge ex35G ex35U () () 3 ∧
    (∀ c : ENNReal, HasScalarLipBound realStdGauge ex35G ex35U () () c → 3 ≤ c) ∧
    sInf {c : ENNReal | HasScalarLipBound realStdGauge ex35G ex35U () () c} = 3 := by
  have hdomF : ex35U ⊆ dom ex35F := le_of_eq ex35_domains_and_outside.2.2.1.symm
  have hdomG : ex35U ⊆ dom ex35G := le_of_eq ex35_domains_and_outside.2.2.2.symm
  have hlipF : HasScalarLipBound realStdGauge ex35F ex35U () () 1 := by
    refine ⟨hdomF, fun x hx y hy => ?_⟩
    have hfx : ex35F.func x = x := by
      rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl
      · exact ex35F_0
      · exact ex35F_1
      · exact ex35F_2
      · exact ex35F_3
    have hfy : ex35F.func y = y := by
      rcases (mem_ex35U_iff y).mp hy with rfl | rfl | rfl | rfl
      · exact ex35F_0
      · exact ex35F_1
      · exact ex35F_2
      · exact ex35F_3
    rw [hfx, hfy, one_mul]
  have hlowF : ∀ c : ENNReal, HasScalarLipBound realStdGauge ex35F ex35U () () c → 1 ≤ c := by
    intro c hc
    have h01 := hc.2 (.val 0) ((mem_ex35U_iff _).mpr (Or.inl rfl))
      (.val 1) ((mem_ex35U_iff _).mpr (Or.inr (Or.inl rfl)))
    simpa [realStdGauge, realStdDist] using h01
  have hinfF : sInf {c : ENNReal | HasScalarLipBound realStdGauge ex35F ex35U () () c} = 1 :=
    le_antisymm (sInf_le hlipF) (le_sInf hlowF)
  have h3_ofReal : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_num
  have hlipG : HasScalarLipBound realStdGauge ex35G ex35U () () 3 := by
    refine ⟨hdomG, fun x hx y hy => ?_⟩
    rcases (mem_ex35U_iff x).mp hx with rfl | rfl | rfl | rfl <;>
      rcases (mem_ex35U_iff y).mp hy with rfl | rfl | rfl | rfl <;>
      (simp only [realStdGauge, ex35G_0, ex35G_1, ex35G_2, ex35G_3, realStdDist_val];
       rw [h3_ofReal, ← ENNReal.ofReal_mul (by norm_num)];
       exact ENNReal.ofReal_le_ofReal (by norm_num))
  have hlowG : ∀ c : ENNReal, HasScalarLipBound realStdGauge ex35G ex35U () () c → 3 ≤ c := by
    intro c hc
    have h01 := hc.2 (.val 0) ((mem_ex35U_iff _).mpr (Or.inl rfl))
      (.val 1) ((mem_ex35U_iff _).mpr (Or.inr (Or.inl rfl)))
    rw [realStdGauge, ex35G_0, ex35G_1, realStdDist_val, realStdDist_val] at h01
    have h03 : |(0 : ℝ) - 3| = 3 := by norm_num
    have h01' : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [h03, h01', ← h3_ofReal, ENNReal.ofReal_one, mul_one] at h01
    exact h01
  have hinfG : sInf {c : ENNReal | HasScalarLipBound realStdGauge ex35G ex35U () () c} = 3 :=
    le_antisymm (sInf_le hlipG) (le_sInf hlowG)
  exact ⟨hlipF, hlowF, hinfF, hlipG, hlowG, hinfG⟩
 
/-- CH03-P30-04: 习题 3.5(iii-b) 在精度 `ε = 7/4` 下代入命题 3.19 的覆盖数上界 `𝒩(ε/L, U)`：对 `f`（`L = 1`）上界为 `2`，与真实像覆盖数 `2` 相等（紧）；对 `g`（`L = 3`）上界为 `𝒩(7/12, U) = 4`，严格大于真实像覆盖数 `2`。 -/
theorem ex_3_5_iii_b_prop_3_19_bound_comparison :
    let ε : ENNReal := 7 / 4
    covering_number realStdDist ε (operator_image ex35F ex35U) ≤
      covering_number realStdDist (ε / 1) ex35U ∧
    covering_number realStdDist ε (operator_image ex35F ex35U) = 2 ∧
    covering_number realStdDist (ε / 1) ex35U = 2 ∧
    covering_number realStdDist ε (operator_image ex35F ex35U) =
      covering_number realStdDist (ε / 1) ex35U ∧
    covering_number realStdDist ε (operator_image ex35G ex35U) ≤
      covering_number realStdDist (ε / 3) ex35U ∧
    covering_number realStdDist ε (operator_image ex35G ex35U) = 2 ∧
    covering_number realStdDist (ε / 3) ex35U = 4 ∧
    covering_number realStdDist ε (operator_image ex35G ex35U) <
      covering_number realStdDist (ε / 3) ex35U := by
  dsimp only
  have hne : ex35U.Nonempty := ⟨.val 0, (mem_ex35U_iff _).mpr (Or.inl rfl)⟩
  have h74_pos : (0 : ENNReal) < 7 / 4 := by
    rw [ennreal_seven_fourths]; exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h74_top : (7 / 4 : ENNReal) < ⊤ := by
    rw [ennreal_seven_fourths]; exact ENNReal.ofReal_lt_top
  rcases ex_3_5_iii_a_optimal_scalar_lip with ⟨hlipF, _, _, hlipG, _, _⟩
  have hboundF := (prop_3_19_covering_number_upper_bound realStdGauge ex35F ex35U () ()
    (7 / 4) 1 hne hlipF.1 h74_pos h74_top zero_lt_one ENNReal.one_lt_top hlipF.2).2
  have hboundG := (prop_3_19_covering_number_upper_bound realStdGauge ex35G ex35U () ()
    (7 / 4) 3 hne hlipG.1 h74_pos h74_top (by norm_num) ENNReal.ofNat_lt_top hlipG.2).2
  have hcovU74 : covering_number realStdDist (7 / 4) ex35U = 2 :=
    ex_3_5_i_covering_piecewise_and_external_center.2.2.2.2.2.2.2
  have himF := ex_3_5_ii_images_covering_and_entropy_diff.1
  have himG := ex_3_5_ii_images_covering_and_entropy_diff.2.1
  have htrueF : covering_number realStdDist (7 / 4) (operator_image ex35F ex35U) = 2 := by
    rw [himF, hcovU74]
  have htrueG : covering_number realStdDist (7 / 4) (operator_image ex35G ex35U) = 2 := by
    rw [himG, hcovU74]
  have hdiv1 : covering_number realStdDist ((7 / 4 : ENNReal) / 1) ex35U = 2 := by
    rw [div_one, hcovU74]
  have h712_eq : ((7 / 4 : ENNReal) / 3) = ENNReal.ofReal (7 / 12) := by
    have h3 : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_num
    rw [ennreal_seven_fourths, h3, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have h712_pos : (0 : ENNReal) < (7 / 4 : ENNReal) / 3 := by
    rw [h712_eq]; exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h712_top : (7 / 4 : ENNReal) / 3 < ⊤ := by
    rw [h712_eq]; exact ENNReal.ofReal_lt_top
  have h712_le1 : (7 / 4 : ENNReal) / 3 ≤ 1 := by
    rw [h712_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hdiv3 : covering_number realStdDist ((7 / 4 : ENNReal) / 3) ex35U = 4 := by
    rw [ex_3_5_i_covering_piecewise_and_external_center.1 _ h712_pos h712_top, if_pos h712_le1]
  refine ⟨hboundF, htrueF, hdiv1, by rw [htrueF, hdiv1], hboundG, htrueG, hdiv3, ?_⟩
  rw [htrueG, hdiv3]
  norm_num
 
end Ch03
