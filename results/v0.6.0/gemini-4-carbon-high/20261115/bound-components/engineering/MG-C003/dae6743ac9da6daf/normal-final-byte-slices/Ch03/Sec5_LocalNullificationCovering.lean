import Ch03.Defs
import Ch03.RealLineExt
import Ch03.Sec3_NullificationRadius

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open Set

/-!
# § 3.5 局部零化与覆盖数 (`CH03-P18-01` – `CH03-P21-02`)
-/

/-! ## 命题 3.15：统一零化半径给出的分离阈值 (`CH03-P18-01` – `CH03-P18-03`) -/

/-- `CH03-P18-01`：命题 3.15(i) — 低于统一零化半径必归零：
对任意 `x, y ∈ A`，若 `d_i(x, y) < \underline{r}^N_{f, i, j}|_A`，则 `d_j(f(x), f(y)) = 0`。 -/
theorem prop_3_15_zero_of_lt_uniformNullRadius {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f) :
    ∀ x ∈ A, ∀ y ∈ A,
      d i x y < uniformNullRadiusComp d f i j A →
      d j (f.func x) (f.func y) = 0 := by
  have _ := hA_ne
  intro x hx y hy hlt
  have hlt_pt : d i x y < nullRadiusComp d f i j x A :=
    lt_of_lt_of_le hlt (iInf₂_le x hx)
  exact (prop_3_11_of_lt_nullRadius d f A i j x y hdi hdj hA_dom hx hy hlt_pt).2

/-- `CH03-P18-02`：命题 3.15(ii) — 输出正分离时的输入距离下界：
对任意 `x, y ∈ A`，若 `d_j(f(x), f(y)) > 0`，则 `d_i(x, y) ≥ \underline{r}^N_{f, i, j}|_A`。 -/
theorem prop_3_15_le_dist_of_pos_output {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f) :
    ∀ x ∈ A, ∀ y ∈ A,
      0 < d j (f.func x) (f.func y) →
      uniformNullRadiusComp d f i j A ≤ d i x y := by
  intro x hx y hy hpos
  by_contra hnot_le
  have hlt : d i x y < uniformNullRadiusComp d f i j A := lt_of_not_ge hnot_le
  have h0 := prop_3_15_zero_of_lt_uniformNullRadius d f A i j hdi hdj hA_ne hA_dom x hx y hy hlt
  exact (ne_of_gt hpos) h0

/-- `CH03-P18-03`：命题 3.15(iii) — 零化半径不足时的分离见证：
若 `\underline{r}^N < τ_N`，则对任意满足 `\underline{r}^N < α < τ_N` 的有限正数 `α`，
存在 `x, y ∈ A` 与有限正数 `ε ∈ (0, +∞)` 使 `d_i(x, y) < α` 且 `ε ≤ d_j(f(x), f(y))`（含输出距离无穷情形）。 -/
theorem prop_3_15_separation_witness {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_N : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_N : IsFinitePosThreshold τ_N)
    (hlt_tau : uniformNullRadiusComp d f i j A < τ_N) :
    ∀ α : ENNReal,
      uniformNullRadiusComp d f i j A < α → α < τ_N →
      ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
        0 < ε ∧ ε < ⊤ ∧ d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  have _ := hdi
  have _ := hdj
  have _ := hA_ne
  have _ := hA_dom
  have _ := hlt_tau
  intro α hr_lt_α hα_lt_τ
  have hα_pos : 0 < α := lt_of_le_of_lt (zero_le _) hr_lt_α
  have hα_fin : α < ⊤ := lt_trans hα_lt_τ hτ_N.2
  -- 由下确界严格小于 α 提取基点 y ∈ A 使 r^N(y | A) < α
  have hex_y : ∃ y ∈ A, nullRadiusComp d f i j y A < α := by
    by_contra hall
    push Not at hall
    have hge : α ≤ uniformNullRadiusComp d f i j A := le_iInf₂ hall
    exact (not_lt_of_ge hge) hr_lt_α
  rcases hex_y with ⟨y, hyA, hy_lt⟩
  -- α 不能是 y 处的合法零化半径
  have hnot_adm : ¬ IsNullifyingRadius f (d i) (d j) A y α := by
    intro hadm
    have hle : α ≤ nullRadiusComp d f i j y A :=
      le_sSup (s := { r | IsNullifyingRadius f (d i) (d j) A y r }) hadm
    exact (not_lt_of_ge hle) hy_lt
  have hnot_inc : ¬ (ball (d i) y α ∩ A ⊆ { x ∈ A | d j (f.func x) (f.func y) = 0 }) := by
    intro hinc
    exact hnot_adm ⟨hα_pos, hα_fin, hinc⟩
  rw [Set.not_subset] at hnot_inc
  rcases hnot_inc with ⟨x, ⟨hx_ball, hxA⟩, hx_not_zero⟩
  have hout_ne0 : d j (f.func x) (f.func y) ≠ 0 := by
    intro h0
    exact hx_not_zero ⟨hxA, h0⟩
  have hout_pos : 0 < d j (f.func x) (f.func y) := pos_iff_ne_zero.mpr hout_ne0
  -- 分输出距离为 ⊤ 或有限两分支构造有限正数 ε
  by_cases hout_top : d j (f.func x) (f.func y) = ⊤
  · refine ⟨x, hxA, y, hyA, 1, zero_lt_one, ENNReal.one_lt_top, hx_ball, ?_⟩
    rw [hout_top]
    exact le_top
  · refine ⟨x, hxA, y, hyA, d j (f.func x) (f.func y),
      hout_pos, lt_top_iff_ne_top.mpr hout_top, hx_ball, le_rfl⟩

/-! ## 命题 3.16：零化阈值下的纤维包含与覆盖数约束 (`CH03-P19-01` – `CH03-P19-03`) -/

/-- `CH03-P19-01`：命题 3.16(i) — 纤维包含：
若 `\underline{r}^N_{f, i, j}|_A ≥ τ_N`（有限正阈值 `τ_N`），则对任意 `x ∈ A`，`B_i(x, τ_N) ∩ A ⊆ Fib_{f, j}(f(x) | A)`。 -/
theorem prop_3_16_ball_subset_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_N : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_N : IsFinitePosThreshold τ_N)
    (hge : τ_N ≤ uniformNullRadiusComp d f i j A) :
    ∀ x ∈ A, ball (d i) x τ_N ∩ A ⊆ singleCompFiber d f j (f.func x) A := by
  have _ := hτ_N
  intro x hx y ⟨hy_ball, hyA⟩
  refine ⟨hyA, ?_⟩
  have hd_xy : d i x y < uniformNullRadiusComp d f i j A := by
    dsimp [ball] at hy_ball
    rw [hdi.symm x y]
    exact lt_of_lt_of_le hy_ball hge
  have h0 := prop_3_15_zero_of_lt_uniformNullRadius d f A i j hdi hdj hA_ne hA_dom x hx y hyA hd_xy
  rw [hdj.symm]
  exact h0

/-- 命题 3.16(ii) 内部中心前推构造引理：输入 `τ_N`-内覆盖中心集 `S ⊆ B` 的像 `f(S) ⊆ f(B)` 构成任意精度 `ε > 0` 下的内部覆盖，且基数不增。 -/
theorem prop_3_16_pushforward_internal_net {X I : Type} [DecidableEq X] {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (i j : I) (τ_N ε : ENNReal) (S : Finset X)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_N : IsFinitePosThreshold τ_N)
    (hge : τ_N ≤ uniformNullRadiusComp d f i j A)
    (hBA : B ⊆ A) (hε_pos : 0 < ε)
    (hS : InternalEpsilonNet (d i) τ_N B S) :
    InternalEpsilonNet (d j) ε (operator_image f B) (S.image f.func) ∧
    (S.image f.func).card ≤ S.card := by
  refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · rintro z ⟨b, hbB, rfl⟩
    rcases hS.2 b hbB with ⟨s, hsS, hd_bs⟩
    have hbA : b ∈ A := hBA hbB
    have hsA : s ∈ A := hBA (hS.1 hsS)
    have hb_fib := prop_3_16_ball_subset_fiber d f A i j τ_N hdi hdj hA_ne hA_dom hτ_N hge
      s hsA ⟨hd_bs, hbA⟩
    refine ⟨f.func s, Finset.mem_image_of_mem f.func hsS, ?_⟩
    rw [hb_fib.2]
    exact hε_pos

/-- `CH03-P19-02`：命题 3.16(ii-a) — 对任意 `B ⊆ A`（含空集及不存在有限内覆盖情形）与任意 `ε ∈ (0, +∞)`，
`N_j(ε, f(B)) ≤ N_i(τ_N, B)`。 -/
theorem prop_3_16_covering_number_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (i j : I) (τ_N ε : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_N : IsFinitePosThreshold τ_N)
    (hge : τ_N ≤ uniformNullRadiusComp d f i j A)
    (hBA : B ⊆ A) (hε_pos : 0 < ε) (hε_fin : ε < ⊤) :
    covering_number (d j) ε (operator_image f B) ≤ covering_number (d i) τ_N B := by
  classical
  have _ := hε_fin
  apply le_iInf₂
  intro S hS
  obtain ⟨hnet_out, hcard_le⟩ :=
    prop_3_16_pushforward_internal_net d f A B i j τ_N ε S
      hdi hdj hA_ne hA_dom hτ_N hge hBA hε_pos hS
  calc
    covering_number (d j) ε (operator_image f B)
        ≤ ((S.image f.func).card : ENNReal) :=
          iInf_le_of_le (S.image f.func) (iInf_le_of_le hnet_out le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast hcard_le

/-- `CH03-P19-03`：命题 3.16(ii-b) — 当 `B ⊆ A` 且 `B ≠ ∅` 时，由覆盖数不等式与对数单调性得 `E_{ε, j}(f(B)) ≤ E_{τ_N, i}(B)`。 -/
theorem prop_3_16_metric_entropy_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (i j : I) (τ_N ε : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_N : IsFinitePosThreshold τ_N)
    (hge : τ_N ≤ uniformNullRadiusComp d f i j A)
    (hBA : B ⊆ A) (hB_ne : B.Nonempty)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) :
    metric_entropy (d j) ε (operator_image f B) ≤ metric_entropy (d i) τ_N B := by
  have _ := hB_ne
  exact log2_ereal_mono
    (prop_3_16_covering_number_le d f A B i j τ_N ε hdi hdj hA_ne hA_dom hτ_N hge hBA hε_pos hε_fin)

/-! ## 命题 3.16 后正文反例：点态正半径不能代替统一阈值 (`CH03-P20-01`) -/

/-- 反例中的二点子集 `B_a = {-a, a}`。 -/
def stepTwoPtSetB (a : ℝ) : Set RealWithBot := {.ofReal (-a), .ofReal a}

/-- `CH03-P20-01`：命题 3.16 后正文反例 — 在反例 3.1 的同一个阶跃算子与评估域 `U` 上，
对任意有限正数 `τ` 及满足 `0 < a ≤ 1`、`2a < τ` 的 `a`，二点集 `B = {-a, a} ⊆ U` 满足
`N(τ, B) = 1 < 2 = N(1/2, f(B))`；故即使每点零化半径均为正，也不存在统一正输入尺度使命题 3.16 的覆盖数界对所有 `B ⊆ U` 成立。 -/
theorem post_prop_3_16_pointwise_pos_not_sufficient :
    (∀ (τ : ENNReal) (a : ℝ),
      IsFinitePosThreshold τ →
      0 < a → a ≤ 1 → ENNReal.ofReal (2 * a) < τ →
      stepTwoPtSetB a ⊆ stepSetU ∧
      operator_image stepOp (stepTwoPtSetB a) = {.ofReal 0, .ofReal 1} ∧
      covering_number realStdExtDist τ (stepTwoPtSetB a) = 1 ∧
      covering_number realStdExtDist (1 / 2 : ENNReal) (operator_image stepOp (stepTwoPtSetB a)) = 2 ∧
      covering_number realStdExtDist τ (stepTwoPtSetB a) <
        covering_number realStdExtDist (1 / 2 : ENNReal) (operator_image stepOp (stepTwoPtSetB a))) ∧
    ((∀ y ∈ stepSetU, 0 < nullRadius stepOp realStdExtDist realStdExtDist y stepSetU) ∧
      ¬ ∃ τ : ENNReal, IsFinitePosThreshold τ ∧
        ∀ B ⊆ stepSetU,
          covering_number realStdExtDist (1 / 2 : ENNReal) (operator_image stepOp B) ≤
            covering_number realStdExtDist τ B) := by
  classical
  have hpart1 : ∀ (τ : ENNReal) (a : ℝ),
      IsFinitePosThreshold τ →
      0 < a → a ≤ 1 → ENNReal.ofReal (2 * a) < τ →
      stepTwoPtSetB a ⊆ stepSetU ∧
      operator_image stepOp (stepTwoPtSetB a) = {.ofReal 0, .ofReal 1} ∧
      covering_number realStdExtDist τ (stepTwoPtSetB a) = 1 ∧
      covering_number realStdExtDist (1 / 2 : ENNReal) (operator_image stepOp (stepTwoPtSetB a)) = 2 ∧
      covering_number realStdExtDist τ (stepTwoPtSetB a) <
        covering_number realStdExtDist (1 / 2 : ENNReal) (operator_image stepOp (stepTwoPtSetB a)) := by
    intro τ a hτ ha_pos ha_le1 h2a_lt
    have hB_sub : stepTwoPtSetB a ⊆ stepSetU := by
      intro p hp
      rcases hp with rfl | rfl
      · exact ⟨-a, Or.inl ⟨by linarith, by linarith⟩, rfl⟩
      · exact ⟨a, Or.inr ⟨ha_pos, ha_le1⟩, rfl⟩
    have himg : operator_image stepOp (stepTwoPtSetB a) = {.ofReal 0, .ofReal 1} := by
      ext p
      simp only [operator_image, stepTwoPtSetB, Set.mem_image, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl | rfl, rfl⟩
        · have hneg : -a < 0 := by linarith
          left
          simp [stepOp, stepRealFunc, hneg]
        · have hnot_neg : ¬ a < 0 := not_lt.mpr ha_pos.le
          right
          simp [stepOp, stepRealFunc, hnot_neg]
      · rintro (rfl | rfl)
        · have hneg : -a < 0 := by linarith
          exact ⟨.ofReal (-a), Or.inl rfl, by simp [stepOp, stepRealFunc, hneg]⟩
        · have hnot_neg : ¬ a < 0 := not_lt.mpr ha_pos.le
          exact ⟨.ofReal a, Or.inr rfl, by simp [stepOp, stepRealFunc, hnot_neg]⟩
    have hcov_in : covering_number realStdExtDist τ (stepTwoPtSetB a) = 1 := by
      apply le_antisymm
      · have hnet : InternalEpsilonNet realStdExtDist τ (stepTwoPtSetB a) {RealWithBot.ofReal a} := by
          refine ⟨?_, ?_⟩
          · intro x hx
            rw [Finset.mem_coe, Finset.mem_singleton] at hx
            rw [hx]
            exact Or.inr rfl
          · intro x hx
            refine ⟨RealWithBot.ofReal a, Finset.mem_singleton_self _, ?_⟩
            rcases hx with rfl | rfl
            · rw [realStdExtDist_ofReal]
              have habs : |-a - a| = 2 * a := by
                have hneg : -a - a < 0 := by linarith
                rw [abs_of_neg hneg]
                ring
              rw [habs]
              exact h2a_lt
            · simpa using hτ.1
        exact le_trans
          (iInf_le_of_le {RealWithBot.ofReal a} (iInf_le_of_le hnet le_rfl))
          (by simp)
      · exact one_le_covering_number_of_nonempty realStdExtDist τ (stepTwoPtSetB a)
          ⟨RealWithBot.ofReal a, Or.inr rfl⟩
    have hcov_out :
        covering_number realStdExtDist (1 / 2 : ENNReal)
          (operator_image stepOp (stepTwoPtSetB a)) = 2 := by
      rw [himg]
      set Out : Set RealWithBot := {.ofReal 0, .ofReal 1}
      apply le_antisymm
      · let S2 : Finset RealWithBot := {RealWithBot.ofReal 0, RealWithBot.ofReal 1}
        have hnet2 : InternalEpsilonNet realStdExtDist (1 / 2 : ENNReal) Out S2 := by
          refine ⟨?_, ?_⟩
          · intro x hx
            simpa [S2, Out] using hx
          · intro x hx
            rcases hx with rfl | rfl
            · exact ⟨RealWithBot.ofReal 0, by simp [S2], by simp⟩
            · exact ⟨RealWithBot.ofReal 1, by simp [S2], by simp⟩
        have hcard2 : (S2.card : ENNReal) ≤ 2 := by
          have hne01 : RealWithBot.ofReal 0 ≠ RealWithBot.ofReal 1 := by simp
          simp [S2, Finset.card_pair hne01]
        exact le_trans (iInf_le_of_le S2 (iInf_le_of_le hnet2 le_rfl)) hcard2
      · apply le_iInf₂
        intro S hS
        -- 证明 S 必须同时包含 ofReal 0 与 ofReal 1
        have h0_mem : RealWithBot.ofReal 0 ∈ S := by
          rcases hS.2 (RealWithBot.ofReal 0) (Or.inl rfl) with ⟨c, hcS, hc_dist⟩
          rcases hS.1 hcS with rfl | rfl
          · exact hcS
          · exfalso
            have hd1 : realStdExtDist (.ofReal 0) (.ofReal 1) = 1 := by simp
            rw [hd1] at hc_dist
            exact (not_lt_of_ge ENNReal.half_le_self) hc_dist
        have h1_mem : RealWithBot.ofReal 1 ∈ S := by
          rcases hS.2 (RealWithBot.ofReal 1) (Or.inr rfl) with ⟨c, hcS, hc_dist⟩
          rcases hS.1 hcS with rfl | rfl
          · exfalso
            have hd1 : realStdExtDist (.ofReal 1) (.ofReal 0) = 1 := by simp
            rw [hd1] at hc_dist
            exact (not_lt_of_ge ENNReal.half_le_self) hc_dist
          · exact hcS
        have hsub_pair : ({RealWithBot.ofReal 0, RealWithBot.ofReal 1} : Finset RealWithBot) ⊆ S := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact h0_mem
          · rw [Finset.mem_singleton.mp hz']
            exact h1_mem
        have hne01 : RealWithBot.ofReal 0 ≠ RealWithBot.ofReal 1 := by simp
        have hcard_ge : 2 ≤ S.card := by
          calc
            2 = ({RealWithBot.ofReal 0, RealWithBot.ofReal 1} : Finset RealWithBot).card :=
              (Finset.card_pair hne01).symm
            _ ≤ S.card := Finset.card_le_card hsub_pair
        exact_mod_cast hcard_ge
    refine ⟨hB_sub, himg, hcov_in, hcov_out, ?_⟩
    rw [hcov_in, hcov_out]
    norm_num
  refine ⟨hpart1, counterexample_3_1_pointwise_radius.2, ?_⟩
  rintro ⟨τ, hτ, hall⟩
  have hτ_real_pos : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ.1) (ne_of_lt hτ.2)
  set a : ℝ := min 1 (τ.toReal / 4)
  have ha_pos : 0 < a := lt_min zero_lt_one (by linarith)
  have ha_le1 : a ≤ 1 := min_le_left _ _
  have ha_le_q : a ≤ τ.toReal / 4 := min_le_right _ _
  have h2a_lt : ENNReal.ofReal (2 * a) < τ := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hτ.2)]
    exact (ENNReal.ofReal_lt_ofReal_iff hτ_real_pos).mpr (by linarith)
  obtain ⟨hB_sub, _, _, _, hstrict⟩ := hpart1 τ a hτ ha_pos ha_le1 h2a_lt
  exact (not_lt_of_ge (hall (stepTwoPtSetB a) hB_sub)) hstrict

/-! ## 推论 3.17：小输入域上的整体零化判据 (`CH03-P21-01`, `CH03-P21-02`) -/

/-- `CH03-P21-01`：推论 3.17（双向判据）— 在 `diam_{d_i}(A) < τ_σ ≤ τ_N`（有限正阈值）条件下，
`\underline{r}^N_{f, i, j}|_A ≥ τ_N` 当且仅当 `∀ x, y ∈ A`，`d_j(f(x), f(y)) = 0`。 -/
theorem cor_3_17_small_domain_nullification_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_σ τ_N : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_σ : IsFinitePosThreshold τ_σ) (hτ_N : IsFinitePosThreshold τ_N)
    (hdiam : setDiam (d i) A < τ_σ) (hτ_le : τ_σ ≤ τ_N) :
    (τ_N ≤ uniformNullRadiusComp d f i j A ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0) ∧
    (channelType (diamScaleFamily d) τ_σ τ_N d f A i j).1 = 1 := by
  have _ := hτ_σ
  refine ⟨?_, ?_⟩
  · constructor
    · intro hge x hx y hy
      have hd_le_diam : d i x y ≤ setDiam (d i) A :=
        le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
      have hd_lt : d i x y < uniformNullRadiusComp d f i j A :=
        lt_of_le_of_lt hd_le_diam (lt_of_lt_of_le hdiam (le_trans hτ_le hge))
      exact prop_3_15_zero_of_lt_uniformNullRadius d f A i j hdi hdj hA_ne hA_dom x hx y hy hd_lt
    · intro hall_zero
      have hconst : ({j} : Set I) ⊆ constComponents d f A := by
        intro k hk x hx y hy
        rw [Set.mem_singleton_iff.mp hk]
        exact hall_zero x hx y hy
      have htop := (prop_3_8_const_subfamily_radius_top d f A ({j} : Set I) i
        hA_ne hA_dom (Set.singleton_nonempty j) hconst).2
      have heq_rad : uniformNullRadiusSubfamily d f i ({j} : Set I) A =
          uniformNullRadiusComp d f i j A := by
        simp [uniformNullRadiusSubfamily, uniformNullRadiusComp, subfamily_pseudometric_singleton]
      rw [heq_rad] at htop
      rw [htop]
      exact le_of_lt hτ_N.2
  · classical
    simp [channelType, ind01, diamScaleFamily, hdiam]

/-- `CH03-P21-02`：推论 3.17（像集内覆盖数为 1）— 当推论 3.17 的等价条件成立且 `A ≠ ∅` 时，
对任意 `ε ∈ (0, +∞)`，有 `N_j(ε, f(A)) = 1`。 -/
theorem cor_3_17_covering_number_eq_one {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_σ τ_N ε : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f)
    (hτ_σ : IsFinitePosThreshold τ_σ) (hτ_N : IsFinitePosThreshold τ_N)
    (hdiam : setDiam (d i) A < τ_σ) (hτ_le : τ_σ ≤ τ_N)
    (hge : τ_N ≤ uniformNullRadiusComp d f i j A)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) :
    covering_number (d j) ε (operator_image f A) = 1 := by
  classical
  have _ := hε_fin
  have hall_zero : ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 :=
    (cor_3_17_small_domain_nullification_iff d f A i j τ_σ τ_N
      hdi hdj hA_ne hA_dom hτ_σ hτ_N hdiam hτ_le).1.mp hge
  rcases hA_ne with ⟨a₀, ha₀⟩
  apply le_antisymm
  · have hnet : InternalEpsilonNet (d j) ε (operator_image f A) {f.func a₀} := by
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [Finset.mem_coe, Finset.mem_singleton] at hz
        rw [hz]
        exact ⟨a₀, ha₀, rfl⟩
      · rintro z ⟨x, hxA, rfl⟩
        refine ⟨f.func a₀, Finset.mem_singleton_self _, ?_⟩
        rw [hall_zero x hxA a₀ ha₀]
        exact hε_pos
    exact le_trans
      (iInf_le_of_le {f.func a₀} (iInf_le_of_le hnet le_rfl))
      (by simp)
  · exact one_le_covering_number_of_nonempty (d j) ε (operator_image f A)
      ⟨f.func a₀, ⟨a₀, ha₀, rfl⟩⟩

end Ch03
