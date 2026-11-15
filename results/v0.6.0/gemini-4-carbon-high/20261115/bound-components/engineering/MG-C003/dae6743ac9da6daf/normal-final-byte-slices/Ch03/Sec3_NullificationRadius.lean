import Ch03.Defs
import Ch03.RealLineExt
import Ch03.Sec1_ComponentPartition
import Ch03.Sec2_FibersAndFactorization

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open Set

/-!
# § 3.3 零化半径与零化矩阵 (`CH03-P10-01` – `CH03-P15-02`)
-/

/-! ## 反例 3.1：处处正的零化半径未必有正的统一下界 (`CH03-P10-01` – `CH03-P10-03`) -/

/-- 反例 3.1 的实阶跃函数：`x < 0` 取 `0`，`x ≥ 0` 取 `1`。 -/
noncomputable def stepRealFunc (x : ℝ) : ℝ := by
  classical
  exact if x < 0 then 0 else 1

/-- 反例 3.1 的阶跃算子 `f ∈ X_op`。 -/
noncomputable def stepOp : Operator RealWithBot RealWithBot.bot :=
  liftRealMap stepRealFunc

/-- 反例 3.1 的实数评估域子集 `[-1, 0) ∪ (0, 1]`。 -/
def stepRealSetU : Set ℝ := Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1

/-- 反例 3.1 的评估域 `U = [-1, 0) ∪ (0, 1] ⊆ X`。 -/
def stepSetU : Set RealWithBot := RealWithBot.ofReal '' stepRealSetU

/-- `CH03-P10-01`：反例 3.1（结构与域合法性验证）— 带吸收元的实线通常距离为扩展伪度量，阶跃算子保持吸收元，且 `∅ ≠ U ⊆ dom(f)`。 -/
theorem counterexample_3_1_setup_valid :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realStdExtDist ∧
    stepOp.func RealWithBot.bot = RealWithBot.bot ∧
    stepSetU.Nonempty ∧
    stepSetU ⊆ dom stepOp := by
  refine ⟨realStdExtDist_isExtendedPseudoMetric, rfl, ?_, ?_⟩
  · refine ⟨RealWithBot.ofReal 1, ?_⟩
    exact ⟨1, Or.inr ⟨by norm_num, le_rfl⟩, rfl⟩
  · exact ofReal_image_subset_dom_liftRealMap stepRealFunc stepRealSetU

/-- `CH03-P10-02`：反例 3.1（点态合法半径精确刻画与点态正半径）—
对每个 `y = ofReal t ∈ U`，合法有限正半径集恰为 `(0, |t|]`，故点态零化半径为 `|t| > 0`。 -/
theorem counterexample_3_1_pointwise_radius :
    (∀ t ∈ stepRealSetU,
      { r : ENNReal | IsNullifyingRadius stepOp realStdExtDist realStdExtDist stepSetU (.ofReal t) r } =
        Set.Ioc 0 (ENNReal.ofReal |t|) ∧
      nullRadius stepOp realStdExtDist realStdExtDist (.ofReal t) stepSetU = ENNReal.ofReal |t| ∧
      0 < ENNReal.ofReal |t|) ∧
    (∀ y ∈ stepSetU, 0 < nullRadius stepOp realStdExtDist realStdExtDist y stepSetU) := by
  have hmain : ∀ t ∈ stepRealSetU,
      { r : ENNReal | IsNullifyingRadius stepOp realStdExtDist realStdExtDist stepSetU (.ofReal t) r } =
        Set.Ioc 0 (ENNReal.ofReal |t|) ∧
      nullRadius stepOp realStdExtDist realStdExtDist (.ofReal t) stepSetU = ENNReal.ofReal |t| ∧
      0 < ENNReal.ofReal |t| := by
    intro t ht
    have ht_ne0 : t ≠ 0 := by
      rcases ht with ⟨_, hlt⟩ | ⟨hgt, _⟩
      · exact ne_of_lt hlt
      · exact ne_of_gt hgt
    have habs_pos : 0 < |t| := abs_pos.mpr ht_ne0
    have henn_pos : 0 < ENNReal.ofReal |t| := ENNReal.ofReal_pos.mpr habs_pos
    have hset :
        { r : ENNReal | IsNullifyingRadius stepOp realStdExtDist realStdExtDist stepSetU (.ofReal t) r } =
          Set.Ioc 0 (ENNReal.ofReal |t|) := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, IsNullifyingRadius]
      constructor
      · rintro ⟨hr_pos, hr_top, hinc⟩
        refine ⟨hr_pos, ?_⟩
        by_contra hnot_le
        have hgt : ENNReal.ofReal |t| < r := lt_of_not_ge hnot_le
        have hr_real_gt : |t| < r.toReal :=
          (ENNReal.ofReal_lt_iff_lt_toReal habs_pos.le (ne_of_lt hr_top)).mp hgt
        set s : ℝ := min (1 / 2) ((r.toReal - |t|) / 2)
        have hs_pos : 0 < s := by
          apply lt_min (by norm_num)
          linarith
        have hs_le_half : s ≤ 1 / 2 := min_le_left _ _
        have hs_le_diff : s ≤ (r.toReal - |t|) / 2 := min_le_right _ _
        rcases ht with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
        · -- t < 0: 选取异号点 x = s ∈ (0, 1] ⊆ U
          have hs_mem_U : RealWithBot.ofReal s ∈ stepSetU :=
            ⟨s, Or.inr ⟨hs_pos, by linarith⟩, rfl⟩
          have hdist_lt : realStdExtDist (.ofReal s) (.ofReal t) < r := by
            rw [realStdExtDist_ofReal]
            have habs_st : |s - t| < r.toReal := by
              rw [abs_of_neg ht_neg] at hr_real_gt hs_le_diff
              rw [abs_of_pos (by linarith)]
              linarith
            rw [← ENNReal.ofReal_toReal (ne_of_lt hr_top)]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg (s - t)])).mpr habs_st
          have hmem_ball : RealWithBot.ofReal s ∈ ball realStdExtDist (.ofReal t) r ∩ stepSetU :=
            ⟨hdist_lt, hs_mem_U⟩
          have hout0 := (hinc hmem_ball).2
          have hs_not_neg : ¬ s < 0 := not_lt.mpr hs_pos.le
          simp [stepOp, stepRealFunc, ht_neg, hs_not_neg] at hout0
        · -- t > 0: 选取异号点 x = -s ∈ [-1, 0) ⊆ U
          have hns_mem_U : RealWithBot.ofReal (-s) ∈ stepSetU :=
            ⟨-s, Or.inl ⟨by linarith, by linarith⟩, rfl⟩
          have hdist_lt : realStdExtDist (.ofReal (-s)) (.ofReal t) < r := by
            rw [realStdExtDist_ofReal]
            have habs_st : |-s - t| < r.toReal := by
              rw [abs_of_pos ht_pos] at hr_real_gt hs_le_diff
              have hneg : -s - t < 0 := by linarith
              rw [abs_of_neg hneg]
              linarith
            rw [← ENNReal.ofReal_toReal (ne_of_lt hr_top)]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg (-s - t)])).mpr habs_st
          have hmem_ball : RealWithBot.ofReal (-s) ∈ ball realStdExtDist (.ofReal t) r ∩ stepSetU :=
            ⟨hdist_lt, hns_mem_U⟩
          have hout0 := (hinc hmem_ball).2
          have hns_neg : -s < 0 := by linarith
          have ht_not_neg : ¬ t < 0 := not_lt.mpr ht_pos.le
          simp [stepOp, stepRealFunc, hns_neg, ht_not_neg] at hout0
      · rintro ⟨hr_pos, hr_le⟩
        have hr_top : r < ⊤ := lt_of_le_of_lt hr_le ENNReal.ofReal_lt_top
        refine ⟨hr_pos, hr_top, ?_⟩
        rintro p ⟨hp_ball, x, hxU, rfl⟩
        refine ⟨⟨x, hxU, rfl⟩, ?_⟩
        have hlt_abs : ENNReal.ofReal |x - t| < ENNReal.ofReal |t| :=
          lt_of_lt_of_le hp_ball hr_le
        have hreal_lt : |x - t| < |t| :=
          (ENNReal.ofReal_lt_ofReal_iff habs_pos).mp hlt_abs
        rcases abs_lt.mp hreal_lt with ⟨hlow, hhigh⟩
        rcases ht with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
        · rw [abs_of_neg ht_neg] at hlow hhigh
          have hx_neg : x < 0 := by linarith
          simp [stepOp, stepRealFunc, hx_neg, ht_neg]
        · rw [abs_of_pos ht_pos] at hlow hhigh
          have hx_pos : 0 < x := by linarith
          have hx_not_neg : ¬ x < 0 := not_lt.mpr hx_pos.le
          have ht_not_neg : ¬ t < 0 := not_lt.mpr ht_pos.le
          simp [stepOp, stepRealFunc, hx_not_neg, ht_not_neg]
    have hsup : nullRadius stepOp realStdExtDist realStdExtDist (.ofReal t) stepSetU =
        ENNReal.ofReal |t| := by
      unfold nullRadius
      rw [hset]
      apply le_antisymm
      · exact sSup_le (fun _ hr => hr.2)
      · exact le_sSup ⟨henn_pos, le_rfl⟩
    exact ⟨hset, hsup, henn_pos⟩
  refine ⟨hmain, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  rw [(hmain t ht).2.1]
  exact (hmain t ht).2.2

/-- `CH03-P10-03`：反例 3.1（同一固定评估域上的统一半径为零）— 利用 `U` 中趋近于零的基点，证明 `\underline{r}^N_{f, d, d}|_U = 0`。 -/
theorem counterexample_3_1_uniform_radius_zero :
    uniformNullRadius stepOp realStdExtDist realStdExtDist stepSetU = 0 := by
  apply le_antisymm _ (zero_le _)
  rw [nonpos_iff_eq_zero]
  by_contra hne0
  have hpos : 0 < uniformNullRadius stepOp realStdExtDist realStdExtDist stepSetU :=
    pos_iff_ne_zero.mpr hne0
  set m := min (1 : ENNReal) (uniformNullRadius stepOp realStdExtDist realStdExtDist stepSetU)
  have hm_pos : 0 < m := lt_min zero_lt_one hpos
  have hm_le1 : m ≤ 1 := min_le_left _ _
  have hm_lt_top : m < ⊤ := lt_of_le_of_lt hm_le1 ENNReal.one_lt_top
  set a : ℝ := m.toReal / 2
  have hm_real_pos : 0 < m.toReal := ENNReal.toReal_pos (ne_of_gt hm_pos) (ne_of_lt hm_lt_top)
  have hm_real_le1 : m.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hm_le1
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have ha_le1 : a ≤ 1 := by dsimp [a]; linarith
  have ha_mem : a ∈ stepRealSetU := Or.inr ⟨ha_pos, ha_le1⟩
  have hya_mem : RealWithBot.ofReal a ∈ stepSetU := ⟨a, ha_mem, rfl⟩
  have hinf_le : uniformNullRadius stepOp realStdExtDist realStdExtDist stepSetU ≤
      nullRadius stepOp realStdExtDist realStdExtDist (.ofReal a) stepSetU :=
    iInf₂_le (RealWithBot.ofReal a) hya_mem
  have hpt := (counterexample_3_1_pointwise_radius.1 a ha_mem).2.1
  rw [hpt, abs_of_pos ha_pos] at hinf_le
  have hm_le_a : m ≤ ENNReal.ofReal a := le_trans (min_le_right _ _) hinf_le
  have hm_eq : m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal (ne_of_lt hm_lt_top)).symm
  rw [hm_eq] at hm_le_a
  have hreal_le : m.toReal ≤ a := (ENNReal.ofReal_le_ofReal_iff ha_pos.le).mp hm_le_a
  dsimp [a] at hreal_le
  linarith

/-! ## 命题 3.8：常值分量与统一零化半径 (`CH03-P11-01` – `CH03-P11-03`) -/

/-- `CH03-P11-01`：命题 3.8(i-a) — 若 `J ⊆ I_const(ϕ | U)`，则对任意基点 `y ∈ U` 有 `Fib_{ϕ, J}(ϕ(y) | U) = U`。 -/
theorem prop_3_8_const_subfamily_fiber_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (J : Set I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty)
    (hconst : J ⊆ constComponents d ϕ U) :
    ∀ y ∈ U, compFiber d ϕ J (ϕ.func y) U = U := by
  have _ := hU_ne
  have _ := hU
  intro y hy
  ext x
  simp only [compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff d J hJ,
    and_iff_left_iff_imp]
  intro hx j hj
  exact hconst hj x hx y hy

/-- `CH03-P11-02`：命题 3.8(i-b) — 若 `J ⊆ I_const(ϕ | U)`，则对任意输入指标 `i ∈ I`，点态与统一零化半径均为 `+∞`。 -/
theorem prop_3_8_const_subfamily_radius_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (J : Set I) (i : I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty)
    (hconst : J ⊆ constComponents d ϕ U) :
    (∀ y ∈ U, nullRadiusSubfamily d ϕ i J y U = ⊤) ∧
    uniformNullRadiusSubfamily d ϕ i J U = ⊤ := by
  have hfib := prop_3_8_const_subfamily_fiber_eq d ϕ U J hU_ne hU hJ hconst
  have hpt : ∀ y ∈ U, nullRadiusSubfamily d ϕ i J y U = ⊤ := by
    intro y hy
    apply top_unique
    apply le_nullRadius_of_forall_lt
    intro r _ _ _
    rw [nullRadiusSubfamily_target_eq_compFiber, hfib y hy]
    exact Set.inter_subset_right
  refine ⟨hpt, ?_⟩
  unfold uniformNullRadiusSubfamily uniformNullRadius uniformNullRadiusOn
  apply top_unique
  apply le_iInf₂
  intro y hy
  have hy_top : nullRadius ϕ (d i) (subfamily_pseudometric d J) y U = ⊤ := hpt y hy
  rw [hy_top]

/-- 命题 3.8(ii) 参数化两点无穷输入距离规范族：第 `i` 分量上 `d_i(a, b) = ⊤`，其余分量上 `d_k(a, b) = 1`（统一覆盖 `i = j` 与 `i ≠ j`）。 -/
def infInputCounterDist {I : Type} [DecidableEq I] (i : I) (k : I) :
    SwapSpace → SwapSpace → ENNReal
  | .bot, .bot => 0
  | .a, .a => 0
  | .b, .b => 0
  | .a, .b => if k = i then ⊤ else 1
  | .b, .a => if k = i then ⊤ else 1
  | .bot, _ => ⊤
  | _, .bot => ⊤

theorem infInputCounterDist_isExtendedPseudoMetric {I : Type} [DecidableEq I] (i : I) :
    ∀ k : I, ExtendedPseudoMetric SwapSpace SwapSpace.bot (infInputCounterDist i k) := by
  intro k
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by rintro (_ | _ | _) <;> rfl
      symm := by rintro (_ | _ | _) (_ | _ | _) <;> rfl
      triangle := ?_
      isolate_bot := ?_ }
  · rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
      by_cases hki : k = i <;> simp [infInputCounterDist, hki]
  · rintro (_ | _ | _) hx
    · exact False.elim (hx rfl)
    · rfl
    · rfl

/-- `SwapSpace` 上的恒等算子显式缩写。 -/
def swapIdOp : Operator SwapSpace SwapSpace.bot := operator_identity

/-- `CH03-P11-03`：命题 3.8(ii) — 合法两点无穷输入距离反例（对任意有限非空指标集中的任意 `i, j ∈ I`，同时覆盖 `i = j` 与 `i ≠ j`）：
`[N(ϕ)|_U]_{j, i} = ⊤` 不能推出 `j ∈ I_const(ϕ | U)`。 -/
theorem prop_3_8_inf_nullMatrix_not_const {I : Type} [Fintype I] [DecidableEq I] (i j : I) :
    (∀ k : I, ExtendedPseudoMetric SwapSpace SwapSpace.bot (infInputCounterDist i k)) ∧
    swapSetU.Nonempty ∧
    swapSetU ⊆ dom swapIdOp ∧
    nullMatrix (infInputCounterDist i) swapIdOp swapSetU j i = ⊤ ∧
    j ∉ constComponents (infInputCounterDist i) swapIdOp swapSetU := by
  refine ⟨infInputCounterDist_isExtendedPseudoMetric i,
    ⟨.a, by simp [swapSetU]⟩,
    by intro x hx; rcases hx with rfl | rfl <;> simp [dom, swapIdOp, operator_identity],
    ?_, ?_⟩
  · unfold nullMatrix uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
    apply top_unique
    apply le_iInf₂
    intro y hy
    apply le_nullRadius_of_forall_lt
    intro r _ _ _ x ⟨hx_ball, hxU⟩
    refine ⟨hxU, ?_⟩
    rcases hy with rfl | rfl <;> rcases hxU with rfl | rfl
    · simp [swapIdOp, operator_identity, infInputCounterDist]
    · simp [ball, infInputCounterDist] at hx_ball
    · simp [ball, infInputCounterDist] at hx_ball
    · simp [swapIdOp, operator_identity, infInputCounterDist]
  · intro hconst
    have h0 := hconst .a (by simp [swapSetU]) .b (by simp [swapSetU])
    by_cases hji : j = i <;> simp [swapIdOp, operator_identity, infInputCounterDist, hji] at h0

/-- `CH03-P11-03`（显式双分支封装）：具体给出 `i = j` 与 `i ≠ j` 两种情形的具体反例实例。 -/
theorem prop_3_8_inf_nullMatrix_both_branches :
    (nullMatrix (infInputCounterDist TwoIdx.i) swapIdOp swapSetU TwoIdx.i TwoIdx.i = ⊤ ∧
      TwoIdx.i ∉ constComponents (infInputCounterDist TwoIdx.i) swapIdOp swapSetU) ∧
    (TwoIdx.i ≠ TwoIdx.m ∧
      nullMatrix (infInputCounterDist TwoIdx.i) swapIdOp swapSetU TwoIdx.m TwoIdx.i = ⊤ ∧
      TwoIdx.m ∉ constComponents (infInputCounterDist TwoIdx.i) swapIdOp swapSetU) := by
  have h1 := prop_3_8_inf_nullMatrix_not_const TwoIdx.i TwoIdx.i
  have h2 := prop_3_8_inf_nullMatrix_not_const TwoIdx.i TwoIdx.m
  exact ⟨⟨h1.2.2.2.1, h1.2.2.2.2⟩, ⟨by decide, h2.2.2.2.1, h2.2.2.2.2⟩⟩

/-! ## 命题 3.9：恒等分量的纤维与零化半径 (`CH03-P12-01`, `CH03-P12-02`) -/

/-- `CH03-P12-01`：命题 3.9(i) — 若 `y ∈ U ⊆ dom(ϕ)` 且 `i ∈ I_id(ϕ | U)`，则 `Fib_{ϕ, i}(ϕ(y) | U) = {x ∈ U : d_i(x, y) = 0}`。 -/
theorem prop_3_9_id_fiber_eq_zero_class {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (y : X) (i : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hy : y ∈ U) (hU : U ⊆ dom ϕ)
    (hi : i ∈ idComponents d ϕ U) :
    singleCompFiber d ϕ i (ϕ.func y) U = { x ∈ U | d i x y = 0 } := by
  ext x
  simp only [singleCompFiber, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, h0⟩
    rw [prop_3_1_id_preserves_dist d ϕ U i hdi hU hi x hx y hy] at h0
    exact ⟨hx, h0⟩
  · rintro ⟨hx, h0⟩
    rw [← prop_3_1_id_preserves_dist d ϕ U i hdi hU hi x hx y hy] at h0
    exact ⟨hx, h0⟩

/-- `CH03-P12-02`：命题 3.9(ii) — 在恒等分量下，若有限正半径 `r₀` 满足 `B_i(y, r₀) ∩ U ⊆ {x ∈ U : d_i(x, y) = 0}`，则 `r^N_{ϕ, i, i}(y | U) ≥ r₀ > 0`。 -/
theorem prop_3_9_id_nullRadius_ge {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (y : X) (i : I) (r₀ : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hy : y ∈ U) (hU : U ⊆ dom ϕ)
    (hi : i ∈ idComponents d ϕ U)
    (hr₀_pos : 0 < r₀) (hr₀_fin : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ { x ∈ U | d i x y = 0 }) :
    r₀ ≤ nullRadiusComp d ϕ i i y U ∧ 0 < r₀ := by
  refine ⟨?_, hr₀_pos⟩
  have hfib := prop_3_9_id_fiber_eq_zero_class d ϕ U y i hdi hy hU hi
  apply le_sSup
  refine ⟨hr₀_pos, hr₀_fin, ?_⟩
  change ball (d i) y r₀ ∩ U ⊆ singleCompFiber d ϕ i (ϕ.func y) U
  rw [hfib]
  exact hball

/-! ## 命题 3.10：统一零化半径的分量最小值公式 (`CH03-P13-01` – `CH03-P13-03`) -/

/-- `CH03-P13-01`：命题 3.10（点态最小值公式）— 有限非空输出子族的点态零化半径等于各单分量点态零化半径的最小值。 -/
theorem prop_3_10_pointwise_min {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i : I) (J : Set I) (y : X)
    (hU : U ⊆ dom ϕ) (hy : y ∈ U) (hJ : J.Nonempty) :
    nullRadiusSubfamily d ϕ i J y U = (⨅ j ∈ J, nullRadiusComp d ϕ i j y U) ∧
    ∃ j₀ ∈ J, nullRadiusSubfamily d ϕ i J y U = nullRadiusComp d ϕ i j₀ y U := by
  classical
  have _ := hU
  have _ := hy
  have h_eq : nullRadiusSubfamily d ϕ i J y U = ⨅ j ∈ J, nullRadiusComp d ϕ i j y U := by
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply sSup_le
      rintro r ⟨hr_pos, hr_fin, hinc⟩
      apply le_sSup
      refine ⟨hr_pos, hr_fin, ?_⟩
      intro x hx
      have hxJ := hinc hx
      refine ⟨hxJ.1, ?_⟩
      exact ((subfamily_pseudometric_eq_zero_iff d J hJ _ _).mp hxJ.2) j hj
    · apply le_nullRadius_of_forall_lt
      intro r hr_pos hr_fin hr_lt x hx
      refine ⟨hx.2, ?_⟩
      rw [subfamily_pseudometric_eq_zero_iff d J hJ]
      intro j hj
      have hr_lt_j : r < nullRadiusComp d ϕ i j y U :=
        lt_of_lt_of_le hr_lt (iInf₂_le j hj)
      obtain ⟨rj, ⟨_, _, hinc_j⟩, hr_rj⟩ := lt_sSup_iff.mp hr_lt_j
      have hx_rj : x ∈ ball (d i) y rj ∩ U :=
        ⟨lt_trans hx.1 hr_rj, hx.2⟩
      exact (hinc_j hx_rj).2
  have hfin : J.toFinset.Nonempty := by
    rcases hJ with ⟨j₀, hj₀⟩
    exact ⟨j₀, Set.mem_toFinset.mpr hj₀⟩
  obtain ⟨j₀, hj₀_fin, hmin⟩ :=
    Finset.exists_min_image J.toFinset (fun j => nullRadiusComp d ϕ i j y U) hfin
  have hj₀ : j₀ ∈ J := Set.mem_toFinset.mp hj₀_fin
  refine ⟨h_eq, j₀, hj₀, ?_⟩
  rw [h_eq]
  apply le_antisymm
  · exact iInf₂_le j₀ hj₀
  · apply le_iInf₂
    intro j hj
    exact hmin j (Set.mem_toFinset.mpr hj)

/-- `CH03-P13-02`：命题 3.10（统一零化半径分量最小值公式）— 交换基点下确界与有限非空最小值，得到 `\underline{r}^N_{ϕ, i, J}|_U = min_{j ∈ J} [N(ϕ)|_U]_{j, i}`。 -/
theorem prop_3_10_uniform_min {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i : I) (J : Set I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    uniformNullRadiusSubfamily d ϕ i J U = (⨅ j ∈ J, nullMatrix d ϕ U j i) ∧
    ∃ j₀ ∈ J, uniformNullRadiusSubfamily d ϕ i J U = nullMatrix d ϕ U j₀ i := by
  classical
  have _ := hU_ne
  have h_eq : uniformNullRadiusSubfamily d ϕ i J U = ⨅ j ∈ J, nullMatrix d ϕ U j i := by
    unfold uniformNullRadiusSubfamily nullMatrix uniformNullRadiusComp
      uniformNullRadius uniformNullRadiusOn
    have hcongr : (⨅ y ∈ U, nullRadius ϕ (d i) (subfamily_pseudometric d J) y U) =
        ⨅ y ∈ U, ⨅ j ∈ J, nullRadius ϕ (d i) (d j) y U := by
      apply iInf_congr
      intro y
      apply iInf_congr
      intro hy
      exact (prop_3_10_pointwise_min d ϕ U i J y hU hy hJ).1
    rw [hcongr]
    apply le_antisymm
    · exact le_iInf₂ (fun j hj => le_iInf₂ (fun y hy => iInf₂_le_of_le y hy (iInf₂_le j hj)))
    · exact le_iInf₂ (fun y hy => le_iInf₂ (fun j hj => iInf₂_le_of_le j hj (iInf₂_le y hy)))
  have hfin : J.toFinset.Nonempty := by
    rcases hJ with ⟨j₀, hj₀⟩
    exact ⟨j₀, Set.mem_toFinset.mpr hj₀⟩
  obtain ⟨j₀, hj₀_fin, hmin⟩ :=
    Finset.exists_min_image J.toFinset (fun j => nullMatrix d ϕ U j i) hfin
  have hj₀ : j₀ ∈ J := Set.mem_toFinset.mp hj₀_fin
  refine ⟨h_eq, j₀, hj₀, ?_⟩
  rw [h_eq]
  apply le_antisymm
  · exact iInf₂_le j₀ hj₀
  · apply le_iInf₂
    intro j hj
    exact hmin j (Set.mem_toFinset.mpr hj)

/-- `CH03-P13-03`：命题 3.10（输出子族反单调性）— 当非空子族满足 `J ⊆ K` 时，`\underline{r}^N_{ϕ, i, K}|_U ≤ \underline{r}^N_{ϕ, i, J}|_U`。 -/
theorem prop_3_10_uniform_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i : I) (J K : Set I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (hJ : J.Nonempty) (hK : K.Nonempty) (hJK : J ⊆ K) :
    uniformNullRadiusSubfamily d ϕ i K U ≤ uniformNullRadiusSubfamily d ϕ i J U := by
  rw [(prop_3_10_uniform_min d ϕ U i K hU_ne hU hK).1,
    (prop_3_10_uniform_min d ϕ U i J hU_ne hU hJ).1]
  apply le_iInf₂
  intro j hj
  exact iInf₂_le j (hJK hj)

/-! ## 命题 3.11：纤维截断的单步判据 (`CH03-P14-01` – `CH03-P14-03`) -/

/-- `CH03-P14-01`：命题 3.11（纤维成员判据）— 若 `y' ∈ Fib_{ϕ₂, j}(ϕ₂(y) | U₂)`，则 `d_j(ϕ₂(y), ϕ₂(y')) = 0`。 -/
theorem prop_3_11_of_mem_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ₂ : Operator X bot)
    (U₂ : Set X) (j : I) (y y' : X)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hU₂ : U₂ ⊆ dom ϕ₂) (hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hfib : y' ∈ singleCompFiber d ϕ₂ j (ϕ₂.func y) U₂) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  have _ := hU₂
  have _ := hy
  have _ := hy'
  rw [hdj.symm]
  exact hfib.2

/-- `CH03-P14-02`：命题 3.11（零化半径判据）— 若 `d_i(y, y') < r^N_{ϕ₂, i, j}(y | U₂)`，则存在合法有限正半径 `ρ > d_i(y, y')`，并推出 `d_j(ϕ₂(y), ϕ₂(y')) = 0`。 -/
theorem prop_3_11_of_lt_nullRadius {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ₂ : Operator X bot)
    (U₂ : Set X) (i j : I) (y y' : X)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hU₂ : U₂ ⊆ dom ϕ₂) (hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hlt : d i y y' < nullRadiusComp d ϕ₂ i j y U₂) :
    (∃ ρ : ENNReal, IsNullifyingRadius ϕ₂ (d i) (d j) U₂ y ρ ∧ d i y y' < ρ) ∧
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  obtain ⟨ρ, hρ_adm, hρ_gt⟩ := lt_sSup_iff.mp hlt
  refine ⟨⟨ρ, hρ_adm, hρ_gt⟩, ?_⟩
  have hy'_ball : y' ∈ ball (d i) y ρ ∩ U₂ := by
    refine ⟨?_, hy'⟩
    dsimp [ball]
    rw [hdi.symm y' y]
    exact hρ_gt
  have hy'_fib : y' ∈ singleCompFiber d ϕ₂ j (ϕ₂.func y) U₂ := hρ_adm.2.2 hy'_ball
  exact prop_3_11_of_mem_fiber d ϕ₂ U₂ j y y' hdj hU₂ hy hy' hy'_fib

/-- `CH03-P14-03`：命题 3.11（复合输入特例）— 若 `x, x' ∈ dom(ϕ₁)`，两像点 `ϕ₁(x), ϕ₁(x') ∈ U₂` 且 `ϕ₁(x') ∈ Fib_{ϕ₂, j}(ϕ₂(ϕ₁(x)) | U₂)`，则复合输出 `d_j`-零距。 -/
theorem prop_3_11_comp_instance {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    (U₂ : Set X) (j : I) (x x' : X)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hU₂ : U₂ ⊆ dom ϕ₂)
    (hx_dom : x ∈ dom ϕ₁) (hx'_dom : x' ∈ dom ϕ₁)
    (hx_img : ϕ₁.func x ∈ U₂) (hx'_img : ϕ₁.func x' ∈ U₂)
    (hfib : ϕ₁.func x' ∈ singleCompFiber d ϕ₂ j (ϕ₂.func (ϕ₁.func x)) U₂) :
    d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func x') = 0 := by
  have _ := hx_dom
  have _ := hx'_dom
  exact prop_3_11_of_mem_fiber d ϕ₂ U₂ j (ϕ₁.func x) (ϕ₁.func x')
    hdj hU₂ hx_img hx'_img hfib

/-! ## 命题 3.12：统一零化半径的复合下界 (`CH03-P15-01`, `CH03-P15-02`) -/

/-- `CH03-P15-01`：命题 3.12(i) — 零距保持下的传播：若 `ϕ₂` 在实际像域 `ϕ₁(U)` 上将 `d_l`-零距保持为 `d_j`-零距，则 `[N(ϕ₂ ∘ ϕ₁)|_U]_{j, i} ≥ [N(ϕ₁)|_U]_{l, i}`。 -/
theorem prop_3_12_zero_preserving_lower_bound {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I)
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁))
    (hpres : ∀ y ∈ operator_image ϕ₁ U, ∀ y' ∈ operator_image ϕ₁ U,
      d l y y' = 0 → d j (ϕ₂.func y) (ϕ₂.func y') = 0) :
    nullMatrix d ϕ₁ U l i ≤ nullMatrix d (operator_compose ϕ₂ ϕ₁) U j i := by
  have _ := hU_ne
  obtain ⟨hU₁, _⟩ := dom_comp_subset ϕ₁ ϕ₂ U hU
  unfold nullMatrix uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
  apply le_iInf₂
  intro x hx
  apply le_nullRadius_of_forall_lt
  intro r _ _ hr_lt x' ⟨hx'_ball, hx'U⟩
  refine ⟨hx'U, ?_⟩
  have hr_lt_x : r < nullRadiusComp d ϕ₁ i l x U :=
    lt_of_lt_of_le hr_lt (iInf₂_le x hx)
  have hd_xx' : d i x x' < nullRadiusComp d ϕ₁ i l x U := by
    dsimp [ball] at hx'_ball
    rw [(hd i).symm x x']
    exact lt_trans hx'_ball hr_lt_x
  have hl0 : d l (ϕ₁.func x) (ϕ₁.func x') = 0 :=
    (prop_3_11_of_lt_nullRadius d ϕ₁ U i l x x' (hd i) (hd l) hU₁ hx hx'U hd_xx').2
  have hj0 : d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func x')) = 0 :=
    hpres (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func x') ⟨x', hx'U, rfl⟩ hl0
  rw [(hd j).symm]
  exact hj0

/-- `CH03-P15-02`：命题 3.12(ii) — 经单通道有限正 Lip 上界拉回：
若 `0 < L < ⊤` 且在 `U` 上 `d_l(ϕ₁(x), ϕ₁(x')) ≤ L · d_i(x, x')`，则 `[N(ϕ₂ ∘ ϕ₁)|_U]_{j, i} ≥ [N(ϕ₂)|_{ϕ₁(U)}]_{j, l} / L`（完整涵盖右端为 `0`、有限正数与 `⊤` 的情形）。 -/
theorem prop_3_12_lip_pullback_lower_bound {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I) (L : ENNReal)
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁))
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x') :
    nullMatrix d ϕ₂ (operator_image ϕ₁ U) j l / L ≤
      nullMatrix d (operator_compose ϕ₂ ϕ₁) U j i := by
  have _ := hU_ne
  obtain ⟨_, hU₂⟩ := dom_comp_subset ϕ₁ ϕ₂ U hU
  have hL_ne0 : L ≠ 0 := ne_of_gt hL_pos
  have hL_netop : L ≠ ⊤ := ne_of_lt hL_fin
  unfold nullMatrix uniformNullRadiusComp uniformNullRadius uniformNullRadiusOn
  apply le_iInf₂
  intro x hx
  apply le_nullRadius_of_forall_lt
  intro r _ hr_fin hr_lt x' ⟨hx'_ball, hx'U⟩
  refine ⟨hx'U, ?_⟩
  set R₂ := ⨅ y ∈ operator_image ϕ₁ U, nullRadius ϕ₂ (d l) (d j) y (operator_image ϕ₁ U)
  have hLr_lt_R₂ : L * r < R₂ := by
    by_cases hR₂_top : R₂ = ⊤
    · rw [hR₂_top]
      exact ENNReal.mul_lt_top hL_fin hr_fin
    · have hmul : L * r < L * (R₂ / L) := by
        rw [mul_comm L r, mul_comm L (R₂ / L)]
        exact ENNReal.mul_lt_mul_left hL_ne0 hL_netop hr_lt
      have hcancel : L * (R₂ / L) = R₂ := by
        calc
          L * (R₂ / L) = R₂ * (L * L⁻¹) := by
            simp only [div_eq_mul_inv]
            ac_rfl
          _ = R₂ := by rw [ENNReal.mul_inv_cancel hL_ne0 hL_netop, mul_one]
      rwa [hcancel] at hmul
  have hx_img : ϕ₁.func x ∈ operator_image ϕ₁ U := ⟨x, hx, rfl⟩
  have hx'_img : ϕ₁.func x' ∈ operator_image ϕ₁ U := ⟨x', hx'U, rfl⟩
  have hd_xx'_lt : d i x x' < r := by
    dsimp [ball] at hx'_ball
    rw [(hd i).symm x x']
    exact hx'_ball
  have hdl_lt : d l (ϕ₁.func x) (ϕ₁.func x') <
      nullRadiusComp d ϕ₂ l j (ϕ₁.func x) (operator_image ϕ₁ U) := by
    have hmul_lt : L * d i x x' < L * r := by
      rw [mul_comm L (d i x x'), mul_comm L r]
      exact ENNReal.mul_lt_mul_left hL_ne0 hL_netop hd_xx'_lt
    calc
      d l (ϕ₁.func x) (ϕ₁.func x')
          ≤ L * d i x x' := hLip x hx x' hx'U
      _ < L * r := hmul_lt
      _ < R₂ := hLr_lt_R₂
      _ ≤ nullRadiusComp d ϕ₂ l j (ϕ₁.func x) (operator_image ϕ₁ U) :=
          iInf₂_le (ϕ₁.func x) hx_img
  have hj0 : d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func x')) = 0 :=
    (prop_3_11_of_lt_nullRadius d ϕ₂ (operator_image ϕ₁ U) l j
      (ϕ₁.func x) (ϕ₁.func x') (hd l) (hd j) hU₂ hx_img hx'_img hdl_lt).2
  rw [(hd j).symm]
  exact hj0

end Ch03
