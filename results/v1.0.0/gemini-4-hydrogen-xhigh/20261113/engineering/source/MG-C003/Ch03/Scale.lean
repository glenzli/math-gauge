import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch03.Partition
import Ch03.Fiber
import Ch03.Radius
import Mathlib.Tactic

namespace Ch03

open formal_oet.vol_01.ch_01_foundations

section InputScaleAndThreshold

variable {X I : Type} {bot : X}

/-- **定义（输入尺度函数族）**：对非空子集单调的尺度映射族。 -/
structure InputScaleFamily (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i : I, ∀ A₁ A₂ : Set X, A₁.Nonempty → A₁ ⊆ A₂ → scale i A₁ ≤ scale i A₂

/-- 集合在单个伪度量下的直径 `diam_d(A) = sup_{x, y ∈ A} d(x, y)`。 -/
noncomputable def diam (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

/-- 默认直径尺度函数族 `σ_i(A) = diam_{d_i}(A)`。 -/
noncomputable def diamScale (d : I → X → X → ENNReal) : InputScaleFamily X I where
  scale i A := diam (d i) A
  mono i A₁ A₂ _ hsub := by
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    exact le_iSup_of_le x (le_iSup_of_le (hsub hx) (le_iSup_of_le y (le_iSup_of_le (hsub hy) le_rfl)))

lemma le_diam_of_mem {d : X → X → ENNReal} {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    d x y ≤ diam d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

/-- **定义（阈值分类）**：`Type_{f, A}(i, j) ∈ {0, 1}^2`。 -/
noncomputable def thresholdType (d : I → X → X → ENNReal) (f : Operator X bot)
    (σ : InputScaleFamily X I) (A : Set X) (τ_σ τ_N : ENNReal) (i j : I) :
    Fin 2 × Fin 2 := by
  classical
  exact (if σ.scale i A < τ_σ then 1 else 0,
         if τ_N ≤ uniformZeroRadiusComp d f i j A then 1 else 0)

/-- **引理 3.13（穷尽性与互斥性）**：每个通道恰落入四种阈值组合之一。 -/
theorem lemma_3_13_exhaustive_exclusive (d : I → X → X → ENNReal) (f : Operator X bot)
    (σ : InputScaleFamily X I) (A : Set X) (τ_σ τ_N : ENNReal) (i j : I) :
    (thresholdType d f σ A τ_σ τ_N i j = (1, 1) ↔
      σ.scale i A < τ_σ ∧ τ_N ≤ uniformZeroRadiusComp d f i j A) ∧
    (thresholdType d f σ A τ_σ τ_N i j = (1, 0) ↔
      σ.scale i A < τ_σ ∧ uniformZeroRadiusComp d f i j A < τ_N) ∧
    (thresholdType d f σ A τ_σ τ_N i j = (0, 1) ↔
      τ_σ ≤ σ.scale i A ∧ τ_N ≤ uniformZeroRadiusComp d f i j A) ∧
    (thresholdType d f σ A τ_σ τ_N i j = (0, 0) ↔
      τ_σ ≤ σ.scale i A ∧ uniformZeroRadiusComp d f i j A < τ_N) ∧
    (thresholdType d f σ A τ_σ τ_N i j ∈ ({(1, 1), (1, 0), (0, 1), (0, 0)} : Set (Fin 2 × Fin 2))) := by
  classical
  unfold thresholdType
  by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformZeroRadiusComp d f i j A
  · simp [h1, h2, not_lt.mpr h2, not_le.mpr h1]
  · have h2' : uniformZeroRadiusComp d f i j A < τ_N := lt_of_not_ge h2
    simp [h1, h2, h2', not_le.mpr h1]
  · have h1' : τ_σ ≤ σ.scale i A := le_of_not_gt h1
    simp [h1, h1', h2, not_lt.mpr h2]
  · have h1' : τ_σ ≤ σ.scale i A := le_of_not_gt h1
    have h2' : uniformZeroRadiusComp d f i j A < τ_N := lt_of_not_ge h2
    simp [h1, h1', h2, h2']

/-- **引理 3.13 (i)**：增大输入尺度阈值 `τ_σ` 时，第一项取 `1` 的通道集合单调不减。 -/
theorem lemma_3_13_mono_sigma (d : I → X → X → ENNReal) (f : Operator X bot)
    (σ : InputScaleFamily X I) (A : Set X) {τ_σ τ'_σ τ_N : ENNReal} (hle : τ_σ ≤ τ'_σ) :
    { p : I × I | (thresholdType d f σ A τ_σ τ_N p.1 p.2).1 = 1 } ⊆
      { p : I × I | (thresholdType d f σ A τ'_σ τ_N p.1 p.2).1 = 1 } := by
  classical
  rintro ⟨i, j⟩ hp
  simp only [Set.mem_setOf_eq, thresholdType] at hp ⊢
  by_cases h1 : σ.scale i A < τ_σ
  · simp [lt_of_lt_of_le h1 hle]
  · simp [h1] at hp

/-- **引理 3.13 (ii)**：增大零化阈值 `τ_N` 时，第二项取 `1` 的通道集合单调不增。 -/
theorem lemma_3_13_antitone_N (d : I → X → X → ENNReal) (f : Operator X bot)
    (σ : InputScaleFamily X I) (A : Set X) {τ_σ τ_N τ'_N : ENNReal} (hle : τ_N ≤ τ'_N) :
    { p : I × I | (thresholdType d f σ A τ_σ τ'_N p.1 p.2).2 = 1 } ⊆
      { p : I × I | (thresholdType d f σ A τ_σ τ_N p.1 p.2).2 = 1 } := by
  classical
  rintro ⟨i, j⟩ hp
  simp only [Set.mem_setOf_eq, thresholdType] at hp ⊢
  by_cases h1 : τ'_N ≤ uniformZeroRadiusComp d f i j A
  · simp [le_trans hle h1]
  · simp [h1] at hp

/-- **命题 3.14 (i)**：域缩小下任意单调输入尺度的单调性及阈值推论。 -/
theorem prop_3_14_scale_mono (f : Operator X bot) (σ : InputScaleFamily X I)
    (A B : Set X) (hBne : B.Nonempty) (hBA : B ⊆ A) (_hA : A ⊆ dom f)
    (i : I) (τ_σ : ENNReal) :
    σ.scale i B ≤ σ.scale i A ∧ (σ.scale i A < τ_σ → σ.scale i B < τ_σ) := by
  have hle := σ.mono i B A hBne hBA
  exact ⟨hle, fun hlt => lt_of_le_of_lt hle hlt⟩

/-- **命题 3.14 (ii-a)**：固定基点 `x ∈ B` 时，缩小评估域使点态零化半径不减。 -/
theorem prop_3_14_pointwise_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (hBA : B ⊆ A) (_hA : A ⊆ dom f) (i j : I) :
    ∀ x ∈ B, pointwiseZeroRadiusComp d f i j A x ≤ pointwiseZeroRadiusComp d f i j B x := by
  intro x _
  unfold pointwiseZeroRadiusComp pointwiseZeroRadius
  apply iSup_le; intro r
  apply iSup_le; intro hadm
  apply le_pointwiseZeroRadius_of_admissible
  refine ⟨hadm.1, hadm.2.1, ?_⟩
  intro y ⟨hyball, hyB⟩
  exact ⟨hyB, (hadm.2.2 ⟨hyball, hBA hyB⟩).2⟩

/-- **命题 3.14 (ii-b)**：同时缩小评估域与基点集合使统一零化半径不减。 -/
theorem prop_3_14_uniform_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (_hBne : B.Nonempty) (hBA : B ⊆ A) (hA : A ⊆ dom f) (i j : I) :
    uniformZeroRadiusComp d f i j A ≤ uniformZeroRadiusComp d f i j B := by
  unfold uniformZeroRadiusComp uniformZeroRadius uniformZeroRadiusOn
  apply le_iInf; intro x
  apply le_iInf; intro hxB
  have h1 : (⨅ y, ⨅ (_ : y ∈ A), pointwiseZeroRadiusComp d f i j A y) ≤
      pointwiseZeroRadiusComp d f i j A x :=
    iInf_le_of_le x (iInf_le_of_le (hBA hxB) le_rfl)
  exact le_trans h1 (prop_3_14_pointwise_antitone d f A B hBA hA i j x hxB)

/-- **命题 3.14 (iii)**：反向尺度判断一般不成立（带吸收元实直线上的二点/单点反例）。 -/
theorem prop_3_14_reverse_counterexample :
    let d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => realAbsDist
    let f : Operator (Option ℝ) none := 1
    let σ := diamScale d
    let A : Set (Option ℝ) := {some 0, some 1}
    let B : Set (Option ℝ) := {some 0}
    let τ_σ : ENNReal := 1 / 2
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom f ∧
    σ.scale () B < τ_σ ∧ τ_σ ≤ σ.scale () A := by
  dsimp only
  have hBne : ({some (0 : ℝ)} : Set (Option ℝ)).Nonempty := ⟨some 0, rfl⟩
  have hBA : ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ {some 0, some 1} := by
    intro x hx; left; exact hx
  have hAdom : ({some (0 : ℝ), some 1} : Set (Option ℝ)) ⊆ dom (1 : Operator (Option ℝ) none) := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom]
  have hB_lt : (diamScale (fun _ : Unit => realAbsDist)).scale () {some (0 : ℝ)} < 1 / 2 := by
    have hzero : (diamScale (fun _ : Unit => realAbsDist)).scale () {some (0 : ℝ)} = 0 := by
      apply le_antisymm _ (zero_le _)
      apply iSup_le; intro x
      apply iSup_le; intro hx
      apply iSup_le; intro y
      apply iSup_le; intro hy
      rcases hx with rfl; rcases hy with rfl
      simp [realAbsDist]
    rw [hzero]
    norm_num
  have hA_ge : (1 / 2 : ENNReal) ≤
      (diamScale (fun _ : Unit => realAbsDist)).scale () {some (0 : ℝ), some 1} := by
    have h1le : (1 : ENNReal) ≤
        (diamScale (fun _ : Unit => realAbsDist)).scale () {some (0 : ℝ), some 1} := by
      have hmem0 : some (0 : ℝ) ∈ ({some 0, some 1} : Set (Option ℝ)) := Or.inl rfl
      have hmem1 : some (1 : ℝ) ∈ ({some 0, some 1} : Set (Option ℝ)) := Or.inr rfl
      have hle := le_diam_of_mem (d := realAbsDist) hmem0 hmem1
      have hd01 : realAbsDist (some 0) (some 1) = 1 := by simp [realAbsDist]
      rwa [hd01] at hle
    exact le_trans (by norm_num) h1le
  exact ⟨hBne, hBA, hAdom, hB_lt, hA_ge⟩

end InputScaleAndThreshold

section CoveringAndLocalZeroing

variable {X I : Type} {bot : X}

/-- 子族覆盖数 `N_J(ε, U)`。 -/
noncomputable def subfamily_covering_number (d : I → X → X → ENNReal) (J : Set I)
    (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) ε U

/-- **定义（全有界性接口）**：对一切有限正半径 `r ∈ (0, +∞)` 均有有限覆盖数。 -/
def IsTotallyBounded (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

lemma covering_number_le_card {X : Type} (d : X → X → ENNReal) (ε : ENNReal)
    (U : Set X) (S : Finset X) (hS : InternalEpsilonNet d ε U S) :
    covering_number d ε U ≤ (S.card : ENNReal) :=
  iInf_le_of_le S (iInf_le_of_le hS le_rfl)

/-- **表示对应（CH03-D07）**：`InternalEpsilonNet` 与原文开球内覆盖表述等价。 -/
theorem internalEpsilonNet_iff_ball_cover (d : X → X → ENNReal) (ε : ENNReal)
    (U : Set X) (centers : Finset X) :
    InternalEpsilonNet d ε U centers ↔
      (↑centers : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ (↑centers : Set X), ball d s ε := by
  constructor
  · rintro ⟨hsub, hcov⟩
    refine ⟨hsub, ?_⟩
    intro x hx
    rcases hcov x hx with ⟨c, hc, hdist⟩
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hdist⟩
  · rintro ⟨hsub, hcov⟩
    refine ⟨hsub, ?_⟩
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨c, hc, hdist⟩
    exact ⟨c, Finset.mem_coe.mp hc, hdist⟩

/-- **表示对应（CH03-D07）**：覆盖数有限等价于存在有限开球内覆盖，且有限时恰由最小中心数取得。 -/
theorem covering_number_lt_top_iff_ball_cover (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) :
    covering_number d ε U < ⊤ ↔
      ∃ centers : Finset X, (↑centers : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ (↑centers : Set X), ball d s ε := by
  rw [lt_top_iff_ne_top, ne_eq, covering_number_eq_top_iff, not_not]
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S, (internalEpsilonNet_iff_ball_cover d ε U S).mp hS⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, (internalEpsilonNet_iff_ball_cover d ε U S).mpr hS⟩

/-- 单分量与单元素子族覆盖数一致。 -/
theorem subfamily_covering_number_singleton (d : I → X → X → ENNReal) (i : I)
    (ε : ENNReal) (U : Set X) :
    subfamily_covering_number d {i} ε U = covering_number (d i) ε U := by
  simp [subfamily_covering_number, subfamily_pseudometric_singleton]

/-- `log2_ereal` 在 `ENNReal` 上单调不减。 -/
theorem log2_ereal_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    simp [log2_ereal]
  · have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha0) hab)
    by_cases hbtop : b = ⊤
    · subst hbtop
      simp [log2_ereal, ha0]
    · have hatop : a ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hab (lt_top_iff_ne_top.mpr hbtop))
      simp only [log2_ereal, if_neg ha0, if_neg hatop, if_neg hb0, if_neg hbtop]
      apply EReal.coe_le_coe_iff.mpr
      have ha_pos : 0 < a.toReal := ENNReal.toReal_pos ha0 hatop
      have h_le : a.toReal ≤ b.toReal := ENNReal.toReal_mono hbtop hab
      exact Real.logb_le_logb_of_le one_lt_two ha_pos h_le

/-- 覆盖数不等式导出度量熵不等式。 -/
theorem metric_entropy_le_of_covering_le {X₁ X₂ : Type}
    {d₁ : X₁ → X₁ → ENNReal} {d₂ : X₂ → X₂ → ENNReal}
    {ε₁ ε₂ : ENNReal} {U₁ : Set X₁} {U₂ : Set X₂}
    (hle : covering_number d₁ ε₁ U₁ ≤ covering_number d₂ ε₂ U₂) :
    metric_entropy d₁ ε₁ U₁ ≤ metric_entropy d₂ ε₂ U₂ :=
  log2_ereal_mono hle

/-- **命题 3.15 (i)**：严格低于统一零化半径的输入点对必输出零距。 -/
theorem prop_3_15_below_uniform_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (_hAne : A.Nonempty) (_hA : A ⊆ dom f) :
    ∀ x ∈ A, ∀ y ∈ A,
      d i x y < uniformZeroRadiusComp d f i j A → d j (f.func x) (f.func y) = 0 := by
  intro x hx y hy hlt
  have hle : uniformZeroRadiusComp d f i j A ≤ pointwiseZeroRadiusComp d f i j A x :=
    iInf_le_of_le x (iInf_le_of_le hx le_rfl)
  exact prop_3_11_cutoff_radius d f A i j x y hdi hdj hx hy (lt_of_lt_of_le hlt hle)

/-- **命题 3.15 (ii)**：输出正分离时输入距离至少为统一零化半径。 -/
theorem prop_3_15_pos_sep_ge_uniform (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hAne : A.Nonempty) (hA : A ⊆ dom f) :
    ∀ x ∈ A, ∀ y ∈ A,
      0 < d j (f.func x) (f.func y) → uniformZeroRadiusComp d f i j A ≤ d i x y := by
  intro x hx y hy hpos
  by_contra hlt
  rw [not_le] at hlt
  have hzero := prop_3_15_below_uniform_zero d f A i j hdi hdj hAne hA x hx y hy hlt
  exact ne_of_gt hpos hzero

/-- **命题 3.15 (iii)**：统一零化半径小于 `τ_N` 时，对每个中间有限正 `α` 构造正分离见证。 -/
theorem prop_3_15_insufficient_witness (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_N : ENNReal)
    (_hdi : ExtendedPseudoMetric X bot (d i))
    (_hdj : ExtendedPseudoMetric X bot (d j))
    (_hAne : A.Nonempty) (_hA : A ⊆ dom f)
    (_hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (_hlt : uniformZeroRadiusComp d f i j A < τ_N) :
    ∀ α : ENNReal, uniformZeroRadiusComp d f i j A < α → α < τ_N →
      ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
        0 < ε ∧ ε < ⊤ ∧ d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  intro α hα_gt hα_lt
  have hα_pos : 0 < α := lt_of_le_of_lt (zero_le _) hα_gt
  have hα_fin : α < ⊤ := lt_trans hα_lt hτ_fin
  have hex_y : ∃ y ∈ A, pointwiseZeroRadiusComp d f i j A y < α := by
    by_contra hnone
    push Not at hnone
    have hle : α ≤ uniformZeroRadiusComp d f i j A := by
      apply le_iInf; intro y
      apply le_iInf; intro hy
      exact hnone y hy
    exact not_le_of_gt hα_gt hle
  rcases hex_y with ⟨y, hy, hy_lt⟩
  have hnot_adm : ¬ IsAdmissibleZeroRadius f (d i) (d j) A y α := by
    intro hadm
    have hle := le_pointwiseZeroRadius_of_admissible f (d i) (d j) A y α hadm
    exact not_lt_of_ge hle hy_lt
  have hex_x : ∃ x ∈ ball (d i) y α ∩ A, d j (f.func x) (f.func y) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hnot_adm
    refine ⟨hα_pos, hα_fin, ?_⟩
    intro x hx
    refine ⟨hx.2, ?_⟩
    by_contra hne
    exact hne (hnone x hx)
  rcases hex_x with ⟨x, ⟨hxball, hxA⟩, hd_ne⟩
  have hd_pos : 0 < d j (f.func x) (f.func y) := pos_iff_ne_zero.mpr hd_ne
  have hixy : d i x y < α := hxball
  by_cases hd_top : d j (f.func x) (f.func y) = ⊤
  · refine ⟨x, hxA, y, hy, 1, zero_lt_one, ENNReal.one_lt_top, hixy, ?_⟩
    rw [hd_top]
    exact le_top
  · refine ⟨x, hxA, y, hy, d j (f.func x) (f.func y), hd_pos,
      lt_top_iff_ne_top.mpr hd_top, hixy, le_rfl⟩

/-- **命题 3.16 (i)**：统一零化半径至少为 `τ_N` 时，每个中心的 `τ_N`-开球包含于对应计算纤维。 -/
theorem prop_3_16_fiber_inclusion (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_N : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hAne : A.Nonempty) (hA : A ⊆ dom f)
    (_hτ_pos : 0 < τ_N) (_hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformZeroRadiusComp d f i j A) :
    ∀ x ∈ A, ball (d i) x τ_N ∩ A ⊆ compFiber_single d f j (f.func x) A := by
  intro x hx y ⟨hyball, hyA⟩
  rw [compFiber_single_eq]
  refine ⟨hyA, ?_⟩
  have hlt : d i y x < uniformZeroRadiusComp d f i j A := lt_of_lt_of_le hyball hge
  exact prop_3_15_below_uniform_zero d f A i j hdi hdj hAne hA y hyA x hx hlt

/-- **命题 3.16 (ii-a)**：对任意 `B ⊆ A`（含空集及无有限覆盖情形）与任意有限正 `ε`，
输出覆盖数不超过输入 `τ_N`-覆盖数。 -/
theorem prop_3_16_covering_le (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (i j : I) (τ_N ε : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hAne : A.Nonempty) (hA : A ⊆ dom f)
    (hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformZeroRadiusComp d f i j A)
    (hBA : B ⊆ A) (hε_pos : 0 < ε) (_hε_fin : ε < ⊤) :
    covering_number (d j) ε (f.func '' B) ≤ covering_number (d i) τ_N B := by
  classical
  by_cases htop : covering_number (d i) τ_N B = ⊤
  · rw [htop]; exact le_top
  · have hfin : ∃ S : Finset X, InternalEpsilonNet (d i) τ_N B S := by
      by_contra hnone
      exact htop ((covering_number_eq_top_iff (d i) τ_N B).mpr hnone)
    rcases covering_number_attained (d i) τ_N B hfin with ⟨S, hSnet, hScard, _⟩
    let T : Finset X := S.image f.func
    have hTnet : InternalEpsilonNet (d j) ε (f.func '' B) T := by
      constructor
      · intro z hz
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨s, hs, rfl⟩
        exact ⟨s, hSnet.1 hs, rfl⟩
      · rintro y ⟨x, hxB, rfl⟩
        rcases hSnet.2 x hxB with ⟨s, hs, hdist⟩
        have hsA : s ∈ A := hBA (hSnet.1 hs)
        have hxball : x ∈ ball (d i) s τ_N ∩ A := ⟨hdist, hBA hxB⟩
        have hfib := prop_3_16_fiber_inclusion d f A i j τ_N hdi hdj hAne hA
          hτ_pos hτ_fin hge s hsA hxball
        rw [compFiber_single_eq] at hfib
        refine ⟨f.func s, Finset.mem_image_of_mem f.func hs, ?_⟩
        rw [hfib.2]
        exact hε_pos
    have hcov_le : covering_number (d j) ε (f.func '' B) ≤ (T.card : ENNReal) :=
      iInf_le_of_le T (iInf_le_of_le hTnet le_rfl)
    have hcard_le : (T.card : ENNReal) ≤ (S.card : ENNReal) :=
      Nat.cast_le.mpr (Finset.card_image_le)
    rw [hScard]
    exact le_trans hcov_le hcard_le

/-- **命题 3.16 (ii-b)**：非空子集 `B ⊆ A` 上的度量熵约束。 -/
theorem prop_3_16_entropy_le (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (i j : I) (τ_N ε : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hAne : A.Nonempty) (hA : A ⊆ dom f)
    (hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformZeroRadiusComp d f i j A)
    (_hBne : B.Nonempty) (hBA : B ⊆ A) (hε_pos : 0 < ε) (hε_fin : ε < ⊤) :
    metric_entropy (d j) ε (f.func '' B) ≤ metric_entropy (d i) τ_N B :=
  metric_entropy_le_of_covering_le
    (prop_3_16_covering_le d f A B i j τ_N ε hdi hdj hAne hA hτ_pos hτ_fin hge hBA hε_pos hε_fin)

/-- **命题 3.16 后正文反例**：在反例 3.1 的同一阶跃算子与 `U_ce31` 上，
对任意有限正 `τ` 取 `0 < a ≤ 1` 且 `2a < τ`，二点子集 `B = {-a, a}` 输入覆盖数为 `1`，
输出在 `1/2` 尺度下覆盖数为 `2`，说明点态正零化半径不能替代统一阈值。 -/
theorem prop_3_16_pointwise_counterexample (τ : ENNReal) (hτ_pos : 0 < τ) (hτ_fin : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      let B : Set (Option ℝ) := {some (-a), some a}
      B ⊆ U_ce31 ∧
      covering_number realAbsDist τ B = 1 ∧
      covering_number realAbsDist (1 / 2) (stepOp.func '' B) = 2 ∧
      covering_number realAbsDist τ B <
        covering_number realAbsDist (1 / 2) (stepOp.func '' B) := by
  have hτ_real_pos : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ_pos) (ne_of_lt hτ_fin)
  let a : ℝ := min 1 (τ.toReal / 4)
  have ha_pos : 0 < a := lt_min zero_lt_one (by linarith)
  have ha_le : a ≤ 1 := min_le_left _ _
  have h2a_lt : 2 * a < τ.toReal := by
    have hle : a ≤ τ.toReal / 4 := min_le_right _ _
    linarith
  have h2a_enn : ENNReal.ofReal (2 * a) < τ := by
    calc
      ENNReal.ofReal (2 * a) < ENNReal.ofReal τ.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hτ_real_pos).mpr h2a_lt
      _ = τ := ENNReal.ofReal_toReal (ne_of_lt hτ_fin)
  let B : Set (Option ℝ) := {some (-a), some a}
  have hBU : B ⊆ U_ce31 := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨-a, rfl, Or.inl ⟨by linarith, neg_lt_zero.mpr ha_pos⟩⟩
    · exact ⟨a, rfl, Or.inr ⟨ha_pos, ha_le⟩⟩
  have hBne : B.Nonempty := ⟨some a, Or.inr rfl⟩
  have hcovB : covering_number realAbsDist τ B = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet realAbsDist τ B {some (-a)} := by
        constructor
        · intro z hz
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hz
          rw [hz]
          exact Or.inl rfl
        · intro x hx
          refine ⟨some (-a), Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl
          · simpa [realAbsDist] using hτ_pos
          · have hdiff : |a - (-a)| = 2 * a := by
              rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
            dsimp [realAbsDist]
            rw [hdiff]
            exact h2a_enn
      have hle := covering_number_le_card realAbsDist τ B {some (-a)} hnet
      simpa using hle
    · exact one_le_covering_number_of_nonempty realAbsDist τ B hBne
  have himg : stepOp.func '' B = {some 0, some 1} := by
    ext z
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · left; simp [stepOp, ha_pos]
      · right; simp [stepOp, not_lt.mpr (le_of_lt ha_pos)]
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨some (-a), Or.inl rfl, by simp [stepOp, ha_pos]⟩
      · exact ⟨some a, Or.inr rfl, by simp [stepOp, not_lt.mpr (le_of_lt ha_pos)]⟩
  have hcovImg : covering_number realAbsDist (1 / 2) (stepOp.func '' B) = 2 := by
    rw [himg]
    apply le_antisymm
    · let T : Finset (Option ℝ) := {some 0, some 1}
      have hTnet : InternalEpsilonNet realAbsDist (1 / 2) {some 0, some 1} T := by
        constructor
        · intro z hz
          simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hz ⊢
          exact hz
        · intro x hx
          rcases hx with rfl | rfl
          · refine ⟨some 0, by simp [T], ?_⟩
            simp [realAbsDist]
          · refine ⟨some 1, by simp [T], ?_⟩
            simp [realAbsDist]
      have hle := covering_number_le_card realAbsDist (1 / 2) {some 0, some 1} T hTnet
      have hcard : T.card ≤ 2 := by
        simp [T]
      exact le_trans hle (by exact_mod_cast hcard)
    · apply le_iInf; intro T
      apply le_iInf; intro hTnet
      rcases hTnet.2 (some 0) (Or.inl rfl) with ⟨c₀, hc₀T, hc₀dist⟩
      rcases hTnet.2 (some 1) (Or.inr rfl) with ⟨c₁, hc₁T, hc₁dist⟩
      have h0mem : some (0 : ℝ) ∈ T := by
        rcases hTnet.1 hc₀T with h | h
        · rw [← h]; exact hc₀T
        · exfalso
          rw [h] at hc₀dist
          simp [realAbsDist] at hc₀dist
      have h1mem : some (1 : ℝ) ∈ T := by
        rcases hTnet.1 hc₁T with h | h
        · exfalso
          rw [h] at hc₁dist
          simp [realAbsDist] at hc₁dist
        · rw [← h]; exact hc₁T
      have hne : (some (0 : ℝ) : Option ℝ) ≠ some 1 := by simp
      have h2le : 2 ≤ T.card := by
        have hlt : 1 < T.card := Finset.one_lt_card.mpr ⟨some 0, h0mem, some 1, h1mem, hne⟩
        exact hlt
      exact_mod_cast h2le
  refine ⟨a, ha_pos, ha_le, h2a_enn, hBU, hcovB, hcovImg, ?_⟩
  rw [hcovB, hcovImg]
  norm_num

/-- **推论 3.17 (i)**：小输入域上（`diam_{d_i}(A) < τ_σ ≤ τ_N`）的整体零化判据。 -/
theorem cor_3_17_small_domain_zeroing (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_σ τ_N : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hAne : A.Nonempty) (hA : A ⊆ dom f)
    (_hτσ_pos : 0 < τ_σ) (_hτσ_fin : τ_σ < ⊤)
    (_hτN_pos : 0 < τ_N) (_hτN_fin : τ_N < ⊤)
    (hdiam : diam (d i) A < τ_σ) (hτ_le : τ_σ ≤ τ_N) :
    τ_N ≤ uniformZeroRadiusComp d f i j A ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro hge x hx y hy
    have hd_lt : d i x y < uniformZeroRadiusComp d f i j A :=
      lt_of_le_of_lt (le_diam_of_mem hx hy) (lt_of_lt_of_le hdiam (le_trans hτ_le hge))
    exact prop_3_15_below_uniform_zero d f A i j hdi hdj hAne hA x hx y hy hd_lt
  · intro hall
    unfold uniformZeroRadiusComp uniformZeroRadius uniformZeroRadiusOn
    apply le_iInf; intro y
    apply le_iInf; intro hy
    have htop : pointwiseZeroRadius f (d i) (d j) A y = ⊤ := by
      apply pointwiseZeroRadius_eq_top_of_forall_pos
      intro r hr_pos hr_fin
      refine ⟨hr_pos, hr_fin, ?_⟩
      intro x ⟨_, hxA⟩
      exact ⟨hxA, hall x hxA y hy⟩
    rw [htop]
    exact le_top

/-- **推论 3.17 (ii)**：等价条件成立且 `A` 非空时，任意有限正精度下像集覆盖数恰为 `1`。 -/
theorem cor_3_17_covering_one (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (τ_σ τ_N ε : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hAne : A.Nonempty) (hA : A ⊆ dom f)
    (hτσ_pos : 0 < τ_σ) (hτσ_fin : τ_σ < ⊤)
    (hτN_pos : 0 < τ_N) (hτN_fin : τ_N < ⊤)
    (hdiam : diam (d i) A < τ_σ) (hτ_le : τ_σ ≤ τ_N)
    (hge : τ_N ≤ uniformZeroRadiusComp d f i j A)
    (hε_pos : 0 < ε) (_hε_fin : ε < ⊤) :
    covering_number (d j) ε (f.func '' A) = 1 := by
  have hall := (cor_3_17_small_domain_zeroing d f A i j τ_σ τ_N hdi hdj hAne hA
    hτσ_pos hτσ_fin hτN_pos hτN_fin hdiam hτ_le).mp hge
  rcases hAne with ⟨x₀, hx₀⟩
  apply le_antisymm
  · have hnet : InternalEpsilonNet (d j) ε (f.func '' A) {f.func x₀} := by
      constructor
      · intro z hz
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hz
        rw [hz]
        exact ⟨x₀, hx₀, rfl⟩
      · rintro y ⟨x, hx, rfl⟩
        refine ⟨f.func x₀, Finset.mem_singleton_self _, ?_⟩
        rw [hall x hx x₀ hx₀]
        exact hε_pos
    have hle := covering_number_le_card (d j) ε (f.func '' A) {f.func x₀} hnet
    simpa using hle
  · exact one_le_covering_number_of_nonempty (d j) ε (f.func '' A) ⟨f.func x₀, x₀, hx₀, rfl⟩

end CoveringAndLocalZeroing

end Ch03
