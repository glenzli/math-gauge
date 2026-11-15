import Ch03.Sec02
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
 
/-! ### 带吸收元的实数空间基础模型 (`ℝ ⊔ {⊥}`) -/
 
/-- 带吸收元的实数空间 `𝒳 = ℝ ⊔ {⊥}`。 -/
inductive RealWithBot : Type
  | bot : RealWithBot
  | val : ℝ → RealWithBot
 
/-- 实数部分采用标准欧氏距离 `|x - y|`、吸收元隔离的扩展伪度量。 -/
noncomputable def realStdDist : RealWithBot → RealWithBot → ENNReal
  | .bot, .bot => 0
  | .bot, .val _ => ⊤
  | .val _, .bot => ⊤
  | .val x, .val y => ENNReal.ofReal |x - y|
 
theorem realStdDist_is_extended :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realStdDist where
  nonabsorbing := ⟨.val 0, fun h => by cases h⟩
  dist_self x := by cases x <;> simp [realStdDist]
  symm x y := by
    cases x <;> cases y <;> simp [realStdDist, abs_sub_comm]
  triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp [realStdDist]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
  isolate_bot x hx := by
    cases x with
    | bot => exact False.elim (hx rfl)
    | val _ => rfl
 
/-! ### 反例 3.1：处处正的零化半径未必有正的统一下界 (CH03-P10-01 .. 03) -/
 
/-- 反例 3.1 中的阶跃算子 `f(x) = 0 (x < 0), 1 (x ≥ 0), f(⊥) = ⊥`。 -/
noncomputable def stepOp : Operator RealWithBot RealWithBot.bot where
  func
    | .bot => .bot
    | .val x => open scoped Classical in .val (if x < 0 then 0 else 1)
  preserves_bot := rfl
 
/-- 反例 3.1 中的评估域 `U = [-1, 0) ∪ (0, 1]`。 -/
def stepU : Set RealWithBot :=
  RealWithBot.val '' (Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1)
 
/-- CH03-P10-01: 反例 3.1 构造带吸收元实线、阶跃算子并验证扩展伪度量与评估域条件。 -/
theorem counterexample_3_1_setup :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realStdDist ∧
    stepU.Nonempty ∧
    stepU ⊆ dom stepOp := by
  refine ⟨realStdDist_is_extended, ?_, ?_⟩
  · refine ⟨.val 1, 1, Or.inr ⟨by norm_num, le_rfl⟩, rfl⟩
  · rintro _ ⟨x, _, rfl⟩ hbot
    simp [stepOp] at hbot
 
/-- CH03-P10-02: 反例 3.1 对每个 `y ∈ U`，合法有限正半径集恰为 `(0, |y|]`，点态零化半径为 `|y| > 0`。 -/
theorem counterexample_3_1_pointwise_radius :
    (∀ y : ℝ, y ∈ Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1 →
      {r : ENNReal | ValidNullRadius stepOp realStdDist realStdDist (.val y) stepU r} =
        Set.Ioc 0 (ENNReal.ofReal |y|) ∧
      pointwiseNullRadius stepOp realStdDist realStdDist (.val y) stepU =
        ENNReal.ofReal |y|) ∧
    (∀ y_pt ∈ stepU,
      0 < pointwiseNullRadius stepOp realStdDist realStdDist y_pt stepU) := by
  have hmain : ∀ y : ℝ, y ∈ Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1 →
      {r : ENNReal | ValidNullRadius stepOp realStdDist realStdDist (.val y) stepU r} =
        Set.Ioc 0 (ENNReal.ofReal |y|) ∧
      pointwiseNullRadius stepOp realStdDist realStdDist (.val y) stepU =
        ENNReal.ofReal |y| := by
    intro y hy
    have habs_pos : 0 < |y| := by
      rcases hy with ⟨_, hy0⟩ | ⟨hy0, _⟩
      · exact abs_pos.mpr (ne_of_lt hy0)
      · exact abs_pos.mpr (ne_of_gt hy0)
    have hset : {r : ENNReal | ValidNullRadius stepOp realStdDist realStdDist (.val y) stepU r} =
        Set.Ioc 0 (ENNReal.ofReal |y|) := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, ValidNullRadius]
      constructor
      · rintro ⟨hr0, hrtop, hsub⟩
        refine ⟨hr0, ?_⟩
        by_contra hnotle
        push Not at hnotle
        have hr_real_gt : |y| < r.toReal := by
          have h1 := (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt habs_pos) (lt_top_iff_ne_top.mp hrtop)).mp hnotle
          exact h1
        rcases hy with ⟨_, hy0⟩ | ⟨hy0, _⟩
        · have hy_abs : |y| = -y := abs_of_neg hy0
          let x : ℝ := min 1 ((r.toReal - |y|) / 2)
          have hx_pos : 0 < x := lt_min zero_lt_one (by linarith)
          have hx_le1 : x ≤ 1 := min_le_left _ _
          have hxU : RealWithBot.val x ∈ stepU := ⟨x, Or.inr ⟨hx_pos, hx_le1⟩, rfl⟩
          have hx_dist : |x - y| < r.toReal := by
            have hx_le_half : x ≤ (r.toReal - |y|) / 2 := min_le_right _ _
            have hxy_pos : 0 < x - y := by linarith
            rw [abs_of_pos hxy_pos]
            linarith
          have hx_ball : RealWithBot.val x ∈ ball realStdDist (.val y) r := by
            change ENNReal.ofReal |x - y| < r
            rw [← ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hrtop)]
            exact ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (lt_top_iff_ne_top.mp hrtop)) |>.mpr hx_dist
          have hout := (hsub ⟨hx_ball, hxU⟩).2
          have hne : ¬ (x < 0) := not_lt_of_ge (le_of_lt hx_pos)
          simp [stepOp, realStdDist, hy0, hne] at hout
        · have hy_abs : |y| = y := abs_of_pos hy0
          let x : ℝ := -min 1 ((r.toReal - |y|) / 2)
          have hmin_pos : 0 < min 1 ((r.toReal - |y|) / 2) := lt_min zero_lt_one (by linarith)
          have hx_neg : x < 0 := neg_lt_zero.mpr hmin_pos
          have hx_ge : -1 ≤ x := neg_le_neg (min_le_left _ _)
          have hxU : RealWithBot.val x ∈ stepU := ⟨x, Or.inl ⟨hx_ge, hx_neg⟩, rfl⟩
          have hx_dist : |x - y| < r.toReal := by
            have hmin_le : min 1 ((r.toReal - |y|) / 2) ≤ (r.toReal - |y|) / 2 := min_le_right _ _
            have hxy_neg : x - y < 0 := by linarith
            rw [abs_of_neg hxy_neg]
            dsimp [x]
            linarith
          have hx_ball : RealWithBot.val x ∈ ball realStdDist (.val y) r := by
            change ENNReal.ofReal |x - y| < r
            rw [← ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hrtop)]
            exact ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (lt_top_iff_ne_top.mp hrtop)) |>.mpr hx_dist
          have hout := (hsub ⟨hx_ball, hxU⟩).2
          have hne : ¬ (y < 0) := not_lt_of_ge (le_of_lt hy0)
          simp [stepOp, realStdDist, hx_neg, hne] at hout
      · rintro ⟨hr0, hrle⟩
        have hrtop : r < ⊤ := lt_of_le_of_lt hrle ENNReal.ofReal_lt_top
        refine ⟨hr0, hrtop, ?_⟩
        rintro z ⟨hz_ball, x, hx_mem, rfl⟩
        refine ⟨⟨x, hx_mem, rfl⟩, ?_⟩
        have hlt_ofReal : ENNReal.ofReal |x - y| < ENNReal.ofReal |y| := lt_of_lt_of_le hz_ball hrle
        have hxy_lt : |x - y| < |y| := (ENNReal.ofReal_lt_ofReal_iff habs_pos).mp hlt_ofReal
        rcases abs_lt.mp hxy_lt with ⟨_, hright⟩
        rcases abs_lt.mp hxy_lt with ⟨hleft, _⟩
        rcases hy with ⟨_, hy0⟩ | ⟨hy0, _⟩
        · have hy_abs : |y| = -y := abs_of_neg hy0
          have hx_neg : x < 0 := by linarith
          simp [stepOp, realStdDist, hx_neg, hy0]
        · have hy_abs : |y| = y := abs_of_pos hy0
          have hx_pos : 0 < x := by linarith
          have hnx : ¬ (x < 0) := not_lt_of_ge (le_of_lt hx_pos)
          have hny : ¬ (y < 0) := not_lt_of_ge (le_of_lt hy0)
          simp [stepOp, realStdDist, hnx, hny]
    have hsup : pointwiseNullRadius stepOp realStdDist realStdDist (.val y) stepU =
        ENNReal.ofReal |y| := by
      unfold pointwiseNullRadius
      rw [hset]
      apply le_antisymm
      · exact sSup_le (fun _ hr => hr.2)
      · exact le_sSup ⟨ENNReal.ofReal_pos.mpr habs_pos, le_rfl⟩
    exact ⟨hset, hsup⟩
  refine ⟨hmain, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [(hmain y hy).2]
  rcases hy with ⟨_, hy0⟩ | ⟨hy0, _⟩
  · exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt hy0))
  · exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_gt hy0))
 
/-- CH03-P10-03: 反例 3.1 用趋零基点证明同一固定评估域 `U` 上的统一零化半径为 `0`。 -/
theorem counterexample_3_1_uniform_radius_zero :
    uniformNullRadius stepOp realStdDist realStdDist stepU = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hnot
  have hpos : 0 < uniformNullRadius stepOp realStdDist realStdDist stepU :=
    pos_iff_ne_zero.mpr (fun h => hnot (le_of_eq h))
  let δ : ℝ := if htop : uniformNullRadius stepOp realStdDist realStdDist stepU = ⊤ then 1 / 2
    else min (1 / 2) ((uniformNullRadius stepOp realStdDist realStdDist stepU).toReal / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    split_ifs with htop
    · norm_num
    · exact lt_min (by norm_num)
        (half_pos (ENNReal.toReal_pos (ne_of_gt hpos) htop))
  have hδ_le : δ ≤ 1 := by
    dsimp [δ]
    split_ifs with htop
    · norm_num
    · exact le_trans (min_le_left _ _) (by norm_num)
  have hy_mem : δ ∈ Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1 := Or.inr ⟨hδ_pos, hδ_le⟩
  have hyU : RealWithBot.val δ ∈ stepU := ⟨δ, hy_mem, rfl⟩
  have hle : uniformNullRadius stepOp realStdDist realStdDist stepU ≤
      pointwiseNullRadius stepOp realStdDist realStdDist (RealWithBot.val δ) stepU :=
    iInf₂_le (RealWithBot.val δ) hyU
  rw [(counterexample_3_1_pointwise_radius.1 δ hy_mem).2, abs_of_pos hδ_pos] at hle
  by_cases htop : uniformNullRadius stepOp realStdDist realStdDist stepU = ⊤
  · rw [htop] at hle
    exact not_lt_of_ge hle ENNReal.ofReal_lt_top
  · have hlt : ENNReal.ofReal δ < uniformNullRadius stepOp realStdDist realStdDist stepU := by
      rw [← ENNReal.ofReal_toReal htop]
      apply ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hpos) htop) |>.mpr
      have hδ_half : δ ≤ (uniformNullRadius stepOp realStdDist realStdDist stepU).toReal / 2 := by
        dsimp [δ]
        rw [if_neg htop]
        exact min_le_right _ _
      have hr_pos := ENNReal.toReal_pos (ne_of_gt hpos) htop
      linarith
    exact not_lt_of_ge hle hlt
 
/-! ### 命题 3.8：常值分量与统一零化半径 (CH03-P11-01 .. 03) -/
 
/-- CH03-P11-01: 命题 3.8(i-a) 输出子族常值时每个基点的像目标计算纤维等于 `U`。 -/
theorem prop_3_8_i_a_const_subfamily_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (_hU_ne : U.Nonempty) (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty)
    (hconst : J ⊆ I_const d ϕ U) :
    ∀ y ∈ U, CompFiber d ϕ J (ϕ.func y) U = U := by
  intro y hy
  ext x
  simp only [CompFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff, and_iff_left_iff_imp]
  intro hx j hj
  exact hconst hj x hx y hy
 
/-- `ENNReal` 中全体有限正数 `(0, ⊤)` 的上确界为 `⊤`。 -/
theorem sSup_Ioo_zero_top : sSup (Set.Ioo (0 : ENNReal) ⊤) = ⊤ := by
  by_contra hne
  have hlt : sSup (Set.Ioo (0 : ENNReal) ⊤) < ⊤ := lt_top_iff_ne_top.mpr hne
  let s := sSup (Set.Ioo (0 : ENNReal) ⊤)
  have hs1_lt : s + 1 < ⊤ := ENNReal.add_lt_top.mpr ⟨hlt, ENNReal.one_lt_top⟩
  have hs1_pos : (0 : ENNReal) < s + 1 := by simp
  have hle : s + 1 ≤ s := le_sSup ⟨hs1_pos, hs1_lt⟩
  exact not_lt_of_ge hle (ENNReal.lt_add_right hne one_ne_zero)
 
/-- CH03-P11-02: 命题 3.8(i-b) 输出子族常值时任意输入分量的点态与统一零化半径均为 `+∞`。 -/
theorem prop_3_8_i_b_const_subfamily_radius_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I) (i : I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty)
    (hconst : J ⊆ I_const d ϕ U) :
    (∀ y ∈ U, pointwiseNullRadiusSubfamily d ϕ i J y U = ⊤) ∧
    uniformNullRadiusSubfamily d ϕ i J U = ⊤ := by
  have hpt : ∀ y ∈ U, pointwiseNullRadiusSubfamily d ϕ i J y U = ⊤ := by
    intro y hy
    have hfib := prop_3_8_i_a_const_subfamily_fiber d ϕ U J hU_ne hU hJ hconst y hy
    unfold pointwiseNullRadiusSubfamily pointwiseNullRadius
    have hset : {r : ENNReal | ValidNullRadius ϕ (d i) (subfamily_pseudometric d J) y U r} =
        Set.Ioo 0 ⊤ := by
      ext r
      simp only [Set.mem_setOf_eq, ValidNullRadius_subfamily_iff_fiber, hfib, Set.mem_Ioo]
      simp [Set.inter_subset_right]
    rw [hset, sSup_Ioo_zero_top]
  refine ⟨hpt, ?_⟩
  apply top_unique
  apply le_iInf₂
  intro y hy
  exact le_of_eq (hpt y hy).symm
 
/-- 命题 3.8(ii) 反例距离族：对任意 `I` 及指定输入指标 `i`，令 `d_i(a, b) = ⊤`，其余分量在 `{a, b}` 上取 `1`。 -/
def infInputDist {I : Type} [DecidableEq I] (i : I) (k : I) (x y : SwapSpace) : ENNReal :=
  if x = .bot ∧ y = .bot then 0
  else if x = .bot ∨ y = .bot then ⊤
  else if x = y then 0
  else if k = i then ⊤ else 1
 
/-- CH03-P11-03: 命题 3.8(ii) 合法两点无穷输入距离反例（统一涵盖 `i = j` 与 `i ≠ j`），无穷统一零化半径不推出常值分量。 -/
theorem prop_3_8_ii_inf_radius_not_const {I : Type} [DecidableEq I] (i j : I) :
    (∀ k : I, ExtendedPseudoMetric SwapSpace SwapSpace.bot (infInputDist i k)) ∧
    swapU.Nonempty ∧
    swapU ⊆ dom (operator_identity : Operator SwapSpace SwapSpace.bot) ∧
    nullMatrix (infInputDist i) (operator_identity : Operator SwapSpace SwapSpace.bot) swapU j i = ⊤ ∧
    j ∉ I_const (infInputDist i) (operator_identity : Operator SwapSpace SwapSpace.bot) swapU := by
  have hd : ∀ k : I, ExtendedPseudoMetric SwapSpace SwapSpace.bot (infInputDist i k) := by
    intro k
    refine
      { nonabsorbing := ⟨.a, by decide⟩
        dist_self := fun x => by unfold infInputDist; by_cases hx : x = .bot <;> simp [hx]
        symm := fun x y => by
          unfold infInputDist
          by_cases hx : x = .bot <;> by_cases hy : y = .bot <;> simp [hx, hy, eq_comm]
        triangle := fun x y z => by
          unfold infInputDist
          by_cases hx : x = .bot <;> by_cases hy : y = .bot <;> by_cases hz : z = .bot
          all_goals try simp [hx, hy, hz]
          by_cases hxz : x = z
          · simp [hxz]
          · by_cases hxy : x = y
            · have hyz : y ≠ z := fun h => hxz (hxy.trans h)
              simp [hxy, hyz]
            · simp [hxz, hxy]
        isolate_bot := fun x hx => by unfold infInputDist; simp [hx] }
  let idOp : Operator SwapSpace SwapSpace.bot := operator_identity
  have hpt : ∀ y ∈ swapU,
      pointwiseNullRadiusComp (infInputDist i) idOp i j y swapU = ⊤ := by
    intro y hy
    unfold pointwiseNullRadiusComp pointwiseNullRadius
    have hset : {r : ENNReal | ValidNullRadius idOp (infInputDist i i)
        (infInputDist i j) y swapU r} = Set.Ioo 0 ⊤ := by
      ext r
      simp only [ValidNullRadius, Set.mem_setOf_eq, Set.mem_Ioo]
      refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨hr0, hrtop⟩ => ⟨hr0, hrtop, ?_⟩⟩
      rintro x ⟨hx_ball, hxU⟩
      refine ⟨hxU, ?_⟩
      change infInputDist i i x y < r at hx_ball
      have hxy : x = y := by
        by_contra hne
        have hxnb : x ≠ .bot := by rcases hxU with rfl | rfl <;> decide
        have hynb : y ≠ .bot := by rcases hy with rfl | rfl <;> decide
        have htop : infInputDist i i x y = ⊤ := by
          unfold infInputDist
          simp [hxnb, hynb, hne]
        rw [htop] at hx_ball
        exact not_lt_of_ge le_top (lt_trans hx_ball hrtop)
      subst hxy
      exact (hd j).dist_self x
    rw [hset, sSup_Ioo_zero_top]
  refine ⟨hd, ⟨.a, by simp [swapU]⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> intro hbot <;> cases hbot
  · unfold nullMatrix uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
    apply top_unique
    apply le_iInf₂
    intro y hy
    exact le_of_eq (hpt y hy).symm
  · intro hconst
    have h0 := hconst .a (by simp [swapU]) .b (by simp [swapU])
    change infInputDist i j .a .b = 0 at h0
    unfold infInputDist at h0
    by_cases hji : j = i <;> simp [hji] at h0
 
/-- 命题 3.8(ii) 同分量情形 `i = j` 实例与异分量情形 `i ≠ j` 实例。 -/
theorem prop_3_8_ii_both_cases_explicit :
    (nullMatrix (infInputDist ()) (operator_identity : Operator SwapSpace SwapSpace.bot) swapU () () = ⊤ ∧
      () ∉ I_const (infInputDist ()) (operator_identity : Operator SwapSpace SwapSpace.bot) swapU) ∧
    (nullMatrix (infInputDist TwoIdx.idx_i) (operator_identity : Operator SwapSpace SwapSpace.bot)
        swapU TwoIdx.idx_m TwoIdx.idx_i = ⊤ ∧
      TwoIdx.idx_m ∉ I_const (infInputDist TwoIdx.idx_i)
        (operator_identity : Operator SwapSpace SwapSpace.bot) swapU) :=
  ⟨⟨(prop_3_8_ii_inf_radius_not_const () ()).2.2.2.1,
    (prop_3_8_ii_inf_radius_not_const () ()).2.2.2.2⟩,
   ⟨(prop_3_8_ii_inf_radius_not_const TwoIdx.idx_i TwoIdx.idx_m).2.2.2.1,
    (prop_3_8_ii_inf_radius_not_const TwoIdx.idx_i TwoIdx.idx_m).2.2.2.2⟩⟩
 
/-! ### 命题 3.9：恒等分量的纤维与零化半径 (CH03-P12-01 .. 02) -/
 
/-- CH03-P12-01: 命题 3.9(i) 恒等分量的像目标纤维等于输入零距类。 -/
theorem prop_3_9_i_id_target_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (y : X) (i : I)
    (hy : y ∈ U) (hU : U ⊆ dom ϕ) (hi : i ∈ I_id d ϕ U) :
    CompFiberSingle d ϕ i (ϕ.func y) U = {x ∈ U | d i x y = 0} := by
  rw [CompFiberSingle_eq]
  ext x
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun hx => ?_
  rw [prop_3_1_iii_id_preserves_dist d hd ϕ U i hU hi x hx y hy]
 
/-- CH03-P12-02: 命题 3.9(ii) 有限正 `r₀` 球内仅含输入零距点时，点态零化半径 `≥ r₀ > 0`。 -/
theorem prop_3_9_ii_id_radius_lower_bound {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (y : X) (i : I) (r₀ : ENNReal)
    (hy : y ∈ U) (hU : U ⊆ dom ϕ) (hi : i ∈ I_id d ϕ U)
    (hr0 : 0 < r₀) (hrtop : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r₀ ≤ pointwiseNullRadiusComp d ϕ i i y U ∧
    0 < pointwiseNullRadiusComp d ϕ i i y U := by
  have hfib := prop_3_9_i_id_target_fiber d hd ϕ U y i hy hU hi
  rw [CompFiberSingle_eq] at hfib
  have hval : ValidNullRadius ϕ (d i) (d i) y U r₀ := by
    refine ⟨hr0, hrtop, ?_⟩
    rw [hfib]
    exact hball
  have hle : r₀ ≤ pointwiseNullRadiusComp d ϕ i i y U := le_sSup hval
  exact ⟨hle, lt_of_lt_of_le hr0 hle⟩
 
/-! ### 命题 3.10：统一零化半径的分量最小值公式 (CH03-P13-01 .. 03) -/
 
/-- 合法零化半径关于减小半径向下封闭。 -/
theorem ValidNullRadius_mono_radius {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (y : X) (U : Set X) {r₁ r₂ : ENNReal}
    (hr₁0 : 0 < r₁) (hle : r₁ ≤ r₂) (h₂ : ValidNullRadius ϕ d_in d_out y U r₂) :
    ValidNullRadius ϕ d_in d_out y U r₁ := by
  refine ⟨hr₁0, lt_of_le_of_lt hle h₂.2.1, ?_⟩
  rintro x ⟨hx_ball, hxU⟩
  exact h₂.2.2 ⟨lt_of_lt_of_le hx_ball hle, hxU⟩
 
theorem ennreal_le_of_forall_lt {a b : ENNReal} (h : ∀ r < a, r ≤ b) : a ≤ b := by
  by_contra hnot
  push Not at hnot
  rcases exists_between hnot with ⟨r, hbr, hra⟩
  exact not_lt_of_ge (h r hra) hbr
 
/-- CH03-P13-01: 命题 3.10 有限非空输出子族的点态零化半径等于单分量半径最小值（并由某个 `j ∈ J` 取得）。 -/
theorem prop_3_10_pointwise_min_formula {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) (J : Set I) (y : X)
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) (_hy : y ∈ U) :
    pointwiseNullRadiusSubfamily d ϕ i J y U =
      (⨅ j ∈ J, pointwiseNullRadiusComp d ϕ i j y U) ∧
    ∃ jmin ∈ J, pointwiseNullRadiusSubfamily d ϕ i J y U =
      pointwiseNullRadiusComp d ϕ i jmin y U := by
  have heq : pointwiseNullRadiusSubfamily d ϕ i J y U =
      ⨅ j ∈ J, pointwiseNullRadiusComp d ϕ i j y U := by
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply sSup_le
      intro r hr
      apply le_sSup
      refine ⟨hr.1, hr.2.1, ?_⟩
      rintro x hx
      have hmem : x ∈ CompFiber d ϕ J (ϕ.func y) U := hr.2.2 hx
      have hsub := prop_3_5_iii_inter_eq d ϕ U J (ϕ.func y) hU hJ
      rw [hsub] at hmem
      have hsingle := Set.mem_iInter₂.mp hmem j hj
      rw [CompFiberSingle_eq] at hsingle
      exact hsingle
    · apply ennreal_le_of_forall_lt
      intro r hr
      by_cases hr0 : r = 0
      · subst hr0; exact zero_le _
      · have hr_pos : 0 < r := pos_iff_ne_zero.mpr hr0
        have hr_top : r < ⊤ := lt_of_lt_of_le hr le_top
        have hall : ∀ j ∈ J, ValidNullRadius ϕ (d i) (d j) y U r := by
          intro j hj
          have hrj : r < pointwiseNullRadiusComp d ϕ i j y U :=
            lt_of_lt_of_le hr (iInf₂_le j hj)
          rcases lt_sSup_iff.mp hrj with ⟨r', hr'val, hrr'⟩
          exact ValidNullRadius_mono_radius ϕ (d i) (d j) y U hr_pos (le_of_lt hrr') hr'val
        apply le_sSup
        change ValidNullRadius ϕ (d i) (subfamily_pseudometric d J) y U r
        rw [ValidNullRadius_subfamily_iff_fiber, prop_3_5_iii_inter_eq d ϕ U J (ϕ.func y) hU hJ]
        refine ⟨hr_pos, hr_top, fun x hx => Set.mem_iInter₂.mpr (fun j hj => ?_)⟩
        rw [CompFiberSingle_eq]
        exact (hall j hj).2.2 hx
  refine ⟨heq, ?_⟩
  classical
  have hfin_ne : J.toFinset.Nonempty := Set.toFinset_nonempty.mpr hJ
  rcases Finset.exists_mem_eq_inf' hfin_ne (fun j => pointwiseNullRadiusComp d ϕ i j y U) with
    ⟨jmin, hjmin_mem, hjmin_eq⟩
  refine ⟨jmin, Set.mem_toFinset.mp hjmin_mem, ?_⟩
  rw [heq, ← hjmin_eq, Finset.inf'_eq_inf]
  simp [Finset.inf_eq_iInf]
 
/-- CH03-P13-02: 命题 3.10 交换基点下确界与有限非空最小值，得到统一零化半径的分量最小值公式。 -/
theorem prop_3_10_uniform_min_formula {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) (J : Set I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    uniformNullRadiusSubfamily d ϕ i J U =
      (⨅ j ∈ J, nullMatrix d ϕ U j i) ∧
    ∃ jmin ∈ J, uniformNullRadiusSubfamily d ϕ i J U = nullMatrix d ϕ U jmin i := by
  have heq : uniformNullRadiusSubfamily d ϕ i J U = ⨅ j ∈ J, nullMatrix d ϕ U j i := by
    unfold uniformNullRadiusSubfamily nullMatrix uniformNullRadiusComp uniformNullRadius
      uniformNullRadiusOn
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply le_iInf₂
      intro y hy
      have hpt := (prop_3_10_pointwise_min_formula d ϕ U i J y hU_ne hU hJ hy).1
      exact le_trans (iInf₂_le y hy) (le_of_eq_of_le hpt (iInf₂_le j hj))
    · apply le_iInf₂
      intro y hy
      have hpt := (prop_3_10_pointwise_min_formula d ϕ U i J y hU_ne hU hJ hy).1
      change _ ≤ pointwiseNullRadiusSubfamily d ϕ i J y U
      rw [hpt]
      apply le_iInf₂
      intro j hj
      exact le_trans (iInf₂_le j hj) (iInf₂_le y hy)
  refine ⟨heq, ?_⟩
  classical
  have hfin_ne : J.toFinset.Nonempty := Set.toFinset_nonempty.mpr hJ
  rcases Finset.exists_mem_eq_inf' hfin_ne (fun j => nullMatrix d ϕ U j i) with
    ⟨jmin, hjmin_mem, hjmin_eq⟩
  refine ⟨jmin, Set.mem_toFinset.mp hjmin_mem, ?_⟩
  rw [heq, ← hjmin_eq, Finset.inf'_eq_inf]
  simp [Finset.inf_eq_iInf]
 
/-- CH03-P13-03: 命题 3.10 当 `J ⊆ K` 时，统一零化半径关于输出子族反单调。 -/
theorem prop_3_10_uniform_subfamily_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) (J K : Set I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (hJ : J.Nonempty) (hK : K.Nonempty) (hJK : J ⊆ K) :
    uniformNullRadiusSubfamily d ϕ i K U ≤ uniformNullRadiusSubfamily d ϕ i J U := by
  rw [(prop_3_10_uniform_min_formula d ϕ U i K hU_ne hU hK).1,
      (prop_3_10_uniform_min_formula d ϕ U i J hU_ne hU hJ).1]
  apply le_iInf₂
  intro j hj
  exact iInf₂_le j (hJK hj)
 
/-! ### 命题 3.11：纤维截断的单步判据 (CH03-P14-01 .. 03) -/
 
/-- CH03-P14-01: 命题 3.11 纤维成员条件推出输出零距。 -/
theorem prop_3_11_fiber_mem_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) (y y' : X)
    (_hU₂ : U₂ ⊆ dom ϕ₂) (_hy : y ∈ U₂) (_hy' : y' ∈ U₂)
    (hmem : y' ∈ CompFiberSingle d ϕ₂ j (ϕ₂.func y) U₂) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rw [CompFiberSingle_eq] at hmem
  rw [(hd j).symm (ϕ₂.func y) (ϕ₂.func y')]
  exact hmem.2
 
/-- CH03-P14-02: 命题 3.11 严格小于点态上确界时提取合法有限正半径 `ρ`，并推出输出零距。 -/
theorem prop_3_11_lt_radius_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (i j : I) (y y' : X)
    (hU₂ : U₂ ⊆ dom ϕ₂) (hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hlt : d i y y' < pointwiseNullRadiusComp d ϕ₂ i j y U₂) :
    (∃ ρ : ENNReal, ValidNullRadius ϕ₂ (d i) (d j) y U₂ ρ ∧ d i y y' < ρ) ∧
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rcases lt_sSup_iff.mp hlt with ⟨ρ, hρ_val, hlt_ρ⟩
  refine ⟨⟨ρ, hρ_val, hlt_ρ⟩, ?_⟩
  have hy'_ball : y' ∈ ball (d i) y ρ := by
    change d i y' y < ρ
    rw [(hd i).symm y' y]
    exact hlt_ρ
  have hmem : y' ∈ CompFiberSingle d ϕ₂ j (ϕ₂.func y) U₂ := by
    rw [CompFiberSingle_eq]
    exact hρ_val.2.2 ⟨hy'_ball, hy'⟩
  exact prop_3_11_fiber_mem_zero d hd ϕ₂ U₂ j y y' hU₂ hy hy' hmem
 
theorem prop_3_11_single_step_criterion {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (i j : I) (y y' : X)
    (hU₂ : U₂ ⊆ dom ϕ₂) (hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hcond : y' ∈ CompFiberSingle d ϕ₂ j (ϕ₂.func y) U₂ ∨
      d i y y' < pointwiseNullRadiusComp d ϕ₂ i j y U₂) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rcases hcond with hmem | hlt
  · exact prop_3_11_fiber_mem_zero d hd ϕ₂ U₂ j y y' hU₂ hy hy' hmem
  · exact (prop_3_11_lt_radius_zero d hd ϕ₂ U₂ i j y y' hU₂ hy hy' hlt).2
 
/-- CH03-P14-03: 命题 3.11 复合输入实例：检查两像点属于下游域并代入纤维判据。 -/
theorem prop_3_11_composite_instance {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) (x x' : X)
    (hU₂ : U₂ ⊆ dom ϕ₂) (_hx : x ∈ dom ϕ₁) (_hx' : x' ∈ dom ϕ₁)
    (hϕx : ϕ₁.func x ∈ U₂) (hϕx' : ϕ₁.func x' ∈ U₂)
    (hfib : ϕ₁.func x' ∈ CompFiberSingle d ϕ₂ j (ϕ₂.func (ϕ₁.func x)) U₂) :
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func x') = 0 :=
  prop_3_11_fiber_mem_zero d hd ϕ₂ U₂ j (ϕ₁.func x) (ϕ₁.func x') hU₂ hϕx hϕx' hfib
 
/-! ### 命题 3.12：统一零化半径的复合下界 (CH03-P15-01 .. 02) -/
 
/-- CH03-P15-01: 命题 3.12(i) 下游在实际像域 `ϕ₁(U)` 上保持零距时，复合统一零化半径继承上游下界。 -/
theorem prop_3_12_i_zero_preserving_propagation {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I)
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom (ϕ₂ * ϕ₁))
    (hkeep : ∀ y ∈ operator_image ϕ₁ U, ∀ y' ∈ operator_image ϕ₁ U,
      d l y y' = 0 → d j (ϕ₂.func y) (ϕ₂.func y') = 0) :
    nullMatrix d ϕ₁ U l i ≤ nullMatrix d (ϕ₂ * ϕ₁) U j i := by
  rcases comp_dom_inclusions ϕ₁ ϕ₂ U hU with ⟨hU1, _⟩
  unfold nullMatrix uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
  apply le_iInf₂
  intro x hx
  apply ennreal_le_of_forall_lt
  intro r hr
  by_cases hr0 : r = 0
  · subst hr0; exact zero_le _
  · have hr_pos : 0 < r := pos_iff_ne_zero.mpr hr0
    have hr_top : r < ⊤ := lt_of_lt_of_le hr le_top
    have hr_x : r < pointwiseNullRadiusComp d ϕ₁ i l x U :=
      lt_of_lt_of_le hr (iInf₂_le x hx)
    apply le_sSup
    refine ⟨hr_pos, hr_top, ?_⟩
    rintro x' ⟨hx'_ball, hx'U⟩
    refine ⟨hx'U, ?_⟩
    have hlt_xx' : d i x x' < pointwiseNullRadiusComp d ϕ₁ i l x U := by
      rw [(hd i).symm x x']
      exact lt_trans hx'_ball hr_x
    have hl0 := (prop_3_11_lt_radius_zero d hd ϕ₁ U i l x x' hU1 hx hx'U hlt_xx').2
    have hj0 := hkeep (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func x') ⟨x', hx'U, rfl⟩ hl0
    rw [(hd j).symm]
    exact hj0
 
/-- CH03-P15-02: 命题 3.12(ii) 有限正 `L` 的单通道 Lip 上界拉回下游实际像域零化半径（完整覆盖右端 `0` 与 `+∞` 情形）。 -/
theorem prop_3_12_ii_lip_pullback {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I) (L : ENNReal)
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom (ϕ₂ * ϕ₁))
    (hL0 : 0 < L) (hLtop : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x') :
    nullMatrix d ϕ₂ (operator_image ϕ₁ U) j l / L ≤ nullMatrix d (ϕ₂ * ϕ₁) U j i ∧
    ((0 : ENNReal) / L = 0 ∧ (⊤ : ENNReal) / L = ⊤) := by
  have hL_ne0 : L ≠ 0 := ne_of_gt hL0
  have hL_netop : L ≠ ⊤ := lt_top_iff_ne_top.mp hLtop
  refine ⟨?_, ⟨ENNReal.zero_div, ENNReal.top_div_of_lt_top hLtop⟩⟩
  rcases comp_dom_inclusions ϕ₁ ϕ₂ U hU with ⟨_, hU2⟩
  unfold nullMatrix uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
  apply le_iInf₂
  intro x hx
  apply ennreal_le_of_forall_lt
  intro r hr
  by_cases hr0 : r = 0
  · subst hr0; exact zero_le _
  · have hr_pos : 0 < r := pos_iff_ne_zero.mpr hr0
    have hr_top : r < ⊤ := lt_of_lt_of_le hr le_top
    apply le_sSup
    refine ⟨hr_pos, hr_top, ?_⟩
    rintro x' ⟨hx'_ball, hx'U⟩
    refine ⟨hx'U, ?_⟩
    have hd_lt_r : d i x x' < r := by
      rw [(hd i).symm x x']
      exact hx'_ball
    have hd_lt_div : d i x x' < (⨅ y ∈ operator_image ϕ₁ U,
        pointwiseNullRadius ϕ₂ (d l) (d j) y (operator_image ϕ₁ U)) / L :=
      lt_trans hd_lt_r hr
    have hmul_lt : L * d i x x' < ⨅ y ∈ operator_image ϕ₁ U,
        pointwiseNullRadius ϕ₂ (d l) (d j) y (operator_image ϕ₁ U) := by
      calc
        L * d i x x' = d i x x' * L := mul_comm _ _
        _ < ((⨅ y ∈ operator_image ϕ₁ U,
            pointwiseNullRadius ϕ₂ (d l) (d j) y (operator_image ϕ₁ U)) / L) * L :=
          ENNReal.mul_lt_mul_left hL_ne0 hL_netop hd_lt_div
        _ = L * ((⨅ y ∈ operator_image ϕ₁ U,
            pointwiseNullRadius ϕ₂ (d l) (d j) y (operator_image ϕ₁ U)) / L) := mul_comm _ _
        _ = ⨅ y ∈ operator_image ϕ₁ U,
            pointwiseNullRadius ϕ₂ (d l) (d j) y (operator_image ϕ₁ U) :=
          ENNReal.mul_div_cancel hL_ne0 hL_netop
    have hdl_lt : d l (ϕ₁.func x) (ϕ₁.func x') <
        pointwiseNullRadiusComp d ϕ₂ l j (ϕ₁.func x) (operator_image ϕ₁ U) :=
      lt_of_le_of_lt (hLip x hx x' hx'U) (lt_of_lt_of_le hmul_lt (iInf₂_le (ϕ₁.func x) ⟨x, hx, rfl⟩))
    have hj0 := (prop_3_11_lt_radius_zero d hd ϕ₂ (operator_image ϕ₁ U) l j
      (ϕ₁.func x) (ϕ₁.func x') hU2 ⟨x, hx, rfl⟩ ⟨x', hx'U, rfl⟩ hdl_lt).2
    rw [(hd j).symm]
    exact hj0
 
end Ch03
