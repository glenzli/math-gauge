import Ch03.Defs
import Ch03.RealLineExt
import Ch03.Sec1_ComponentPartition
import Ch03.Sec2_FibersAndFactorization
import Ch03.Sec3_NullificationRadius
import Ch03.Sec4_ScaleAndThresholds
import Ch03.Sec6_MappingEntropyDiff

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-!
# § 3.7 习题 3.1 – 3.3 (`CH03-P26-01` – `CH03-P28-02`)
-/

/-! ## 习题 3.1：计算纤维与自复合 (`CH03-P26-01` – `CH03-P26-03`) -/

/-- 习题 3.1 的仿射算子 `ϕ(x) = 2x - 1`（保吸收元）。 -/
noncomputable def ex3_1_phi : Operator RealWithBot RealWithBot.bot :=
  liftRealMap (fun x : ℝ => 2 * x - 1)

/-- 习题 3.1 的自复合算子 `ϕ² = ϕ ∘ ϕ`。 -/
noncomputable def ex3_1_phi_sq : Operator RealWithBot RealWithBot.bot :=
  operator_compose ex3_1_phi ex3_1_phi

/-- 习题 3.1 的受限域 `U = {0, 1}`。 -/
def ex3_1_U : Set RealWithBot := {.ofReal 0, .ofReal 1}

/-- `CH03-P26-01`：习题 3.1(i-a) — 验证绝对值读数伪度量与仿射算子合法性，计算 `Fib_{ϕ, i}(ϕ(0) | U) = U = {0, 1}`，并判定 `i ∈ I_const(ϕ | U)`。 -/
theorem ex_3_1_part_i_phi :
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot RealWithBot.bot (realAbsModGauge u)) ∧
    ex3_1_phi.func .bot = .bot ∧
    ex3_1_U ⊆ dom ex3_1_phi ∧
    singleCompFiber realAbsModGauge ex3_1_phi () (ex3_1_phi.func (.ofReal 0)) ex3_1_U = ex3_1_U ∧
    () ∈ constComponents realAbsModGauge ex3_1_phi ex3_1_U ∧
    () ∉ idComponents realAbsModGauge ex3_1_phi ex3_1_U ∧
    () ∉ actComponents realAbsModGauge ex3_1_phi ex3_1_U := by
  have hdom : ex3_1_U ⊆ dom ex3_1_phi := by
    intro p hp
    rcases hp with rfl | rfl <;> simp [dom, ex3_1_phi]
  have hconst : () ∈ constComponents realAbsModGauge ex3_1_phi ex3_1_U := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [realAbsModGauge, ex3_1_phi]
  have hfib :
      singleCompFiber realAbsModGauge ex3_1_phi () (ex3_1_phi.func (.ofReal 0)) ex3_1_U =
        ex3_1_U :=
    (prop_3_5_const_component_fiber realAbsModGauge ex3_1_phi ex3_1_U ()
      (ex3_1_phi.func (.ofReal 0)) realAbsModExtDist_isExtendedPseudoMetric hdom hconst
      ⟨.ofReal 0, Or.inl rfl, rfl⟩).1
  refine ⟨realAbsModGauge_isExtendedPseudoMetric, rfl, hdom, hfib, hconst, ?_, ?_⟩
  · intro hid
    exact hid.1 hconst
  · intro hact
    exact hact.2 (Or.inl hconst)

/-- `CH03-P26-02`：习题 3.1(i-b) — 精确保留 `U = {0, 1}`，计算 `Fib_{ϕ², i}(ϕ²(0) | U) = {0}`（以及 `Fib_{ϕ², i}(ϕ²(1) | U) = {1}`），并判定 `i ∈ I_act(ϕ² | U)`。 -/
theorem ex_3_1_part_i_phi_sq :
    ex3_1_U ⊆ dom ex3_1_phi_sq ∧
    singleCompFiber realAbsModGauge ex3_1_phi_sq ()
      (ex3_1_phi_sq.func (.ofReal 0)) ex3_1_U = {.ofReal 0} ∧
    singleCompFiber realAbsModGauge ex3_1_phi_sq ()
      (ex3_1_phi_sq.func (.ofReal 1)) ex3_1_U = {.ofReal 1} ∧
    () ∉ constComponents realAbsModGauge ex3_1_phi_sq ex3_1_U ∧
    () ∉ idComponents realAbsModGauge ex3_1_phi_sq ex3_1_U ∧
    () ∈ actComponents realAbsModGauge ex3_1_phi_sq ex3_1_U := by
  have hdom : ex3_1_U ⊆ dom ex3_1_phi_sq := by
    intro p hp
    rcases hp with rfl | rfl <;> simp [dom, ex3_1_phi_sq, operator_compose, ex3_1_phi]
  have hd01 : realAbsModGauge () (ex3_1_phi_sq.func (.ofReal 0))
      (ex3_1_phi_sq.func (.ofReal 1)) = 2 := by
    norm_num [realAbsModGauge, ex3_1_phi_sq, operator_compose, ex3_1_phi]
  have hd10 : realAbsModGauge () (ex3_1_phi_sq.func (.ofReal 1))
      (ex3_1_phi_sq.func (.ofReal 0)) = 2 := by
    norm_num [realAbsModGauge, ex3_1_phi_sq, operator_compose, ex3_1_phi]
  have hfib0 :
      singleCompFiber realAbsModGauge ex3_1_phi_sq ()
        (ex3_1_phi_sq.func (.ofReal 0)) ex3_1_U = {.ofReal 0} := by
    ext p
    simp only [singleCompFiber, ex3_1_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h0⟩
      · rfl
      · rw [hd10] at h0
        norm_num at h0
    · rintro rfl
      exact ⟨Or.inl rfl, realAbsModExtDist_isExtendedPseudoMetric.dist_self _⟩
  have hfib1 :
      singleCompFiber realAbsModGauge ex3_1_phi_sq ()
        (ex3_1_phi_sq.func (.ofReal 1)) ex3_1_U = {.ofReal 1} := by
    ext p
    simp only [singleCompFiber, ex3_1_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h0⟩
      · rw [hd01] at h0
        norm_num at h0
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, realAbsModExtDist_isExtendedPseudoMetric.dist_self _⟩
  have hnot_const : () ∉ constComponents realAbsModGauge ex3_1_phi_sq ex3_1_U := by
    intro hc
    have h0 := hc (.ofReal 0) (Or.inl rfl) (.ofReal 1) (Or.inr rfl)
    rw [hd01] at h0
    norm_num at h0
  have hnot_id : () ∉ idComponents realAbsModGauge ex3_1_phi_sq ex3_1_U := by
    intro hid
    have h0 := hid.2 (.ofReal 0) (Or.inl rfl)
    norm_num [realAbsModGauge, ex3_1_phi_sq, operator_compose, ex3_1_phi] at h0
  refine ⟨hdom, hfib0, hfib1, hnot_const, hnot_id, ?_⟩
  refine ⟨trivial, ?_⟩
  rintro (hc | hid)
  · exact hnot_const hc
  · exact hnot_id hid

/-- `CH03-P26-03`：习题 3.1(ii) — 若算子 `ψ ∈ X_op` 在 `U = {0, 1}` 上取同一个实数值 `c ∈ ℝ`，则：
(1) 当 `ψ(c) ≠ bot` 时，`U ⊆ dom(ψ²)`，`ψ²(0) = ψ²(1)`，`i ∈ I_const(ψ² | U)`，`Fib_{ψ², i}(ψ²(0) | U) = U`，对任意目标 `y` 两点同进同出，不能落入不同计算纤维；
(2) 当再次像 `ψ(c) = bot` 时，`U ∩ dom(ψ²) = ∅`（`¬ U ⊆ dom(ψ²)`），`U` 内合法评估子域仅为空集 `∅`，两点同样不可能落入 `ψ²` 的不同合法计算纤维。 -/
theorem ex_3_1_part_ii_const_real_op
    (ψ : Operator RealWithBot RealWithBot.bot) (c : ℝ)
    (h0 : ψ.func (.ofReal 0) = .ofReal c)
    (h1 : ψ.func (.ofReal 1) = .ofReal c) :
    ex3_1_U ⊆ dom ψ ∧
    ((ψ.func (.ofReal c) ≠ .bot ∧
        ex3_1_U ⊆ dom (operator_compose ψ ψ) ∧
        (operator_compose ψ ψ).func (.ofReal 0) = (operator_compose ψ ψ).func (.ofReal 1) ∧
        () ∈ constComponents realAbsModGauge (operator_compose ψ ψ) ex3_1_U ∧
        singleCompFiber realAbsModGauge (operator_compose ψ ψ) ()
          ((operator_compose ψ ψ).func (.ofReal 0)) ex3_1_U = ex3_1_U ∧
        ∀ y : RealWithBot,
          RealWithBot.ofReal 0 ∈ singleCompFiber realAbsModGauge (operator_compose ψ ψ) () y ex3_1_U ↔
            RealWithBot.ofReal 1 ∈ singleCompFiber realAbsModGauge (operator_compose ψ ψ) () y ex3_1_U) ∨
      (ψ.func (.ofReal c) = .bot ∧
        ex3_1_U ∩ dom (operator_compose ψ ψ) = ∅ ∧
        ¬ (ex3_1_U ⊆ dom (operator_compose ψ ψ)) ∧
        ∀ V : Set RealWithBot, V ⊆ ex3_1_U → V ⊆ dom (operator_compose ψ ψ) → V = ∅)) := by
  have hdom1 : ex3_1_U ⊆ dom ψ := by
    intro p hp
    rcases hp with rfl | rfl
    · simp [dom, h0]
    · simp [dom, h1]
  refine ⟨hdom1, ?_⟩
  by_cases hc_bot : ψ.func (.ofReal c) = .bot
  · right
    have hinter : ex3_1_U ∩ dom (operator_compose ψ ψ) = ∅ := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hpU hpdom
      rcases hpU with rfl | rfl
      · exact hpdom (by simp [operator_compose, h0, hc_bot])
      · exact hpdom (by simp [operator_compose, h1, hc_bot])
    have hnot_sub : ¬ (ex3_1_U ⊆ dom (operator_compose ψ ψ)) := by
      intro hsub
      have hmem : RealWithBot.ofReal 0 ∈ ex3_1_U ∩ dom (operator_compose ψ ψ) :=
        ⟨Or.inl rfl, hsub (Or.inl rfl)⟩
      rw [hinter] at hmem
      exact hmem
    refine ⟨hc_bot, hinter, hnot_sub, ?_⟩
    intro V hVU hVdom
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hpV
    have hmem : p ∈ ex3_1_U ∩ dom (operator_compose ψ ψ) := ⟨hVU hpV, hVdom hpV⟩
    rw [hinter] at hmem
    exact hmem
  · left
    have hdom2 : ex3_1_U ⊆ dom (operator_compose ψ ψ) := by
      intro p hp
      rcases hp with rfl | rfl
      · simpa [dom, operator_compose, h0] using hc_bot
      · simpa [dom, operator_compose, h1] using hc_bot
    have heq01 : (operator_compose ψ ψ).func (.ofReal 0) =
        (operator_compose ψ ψ).func (.ofReal 1) := by
      simp [operator_compose, h0, h1]
    have hconst2 : () ∈ constComponents realAbsModGauge (operator_compose ψ ψ) ex3_1_U := by
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact realAbsModExtDist_isExtendedPseudoMetric.dist_self _
      · rw [heq01]; exact realAbsModExtDist_isExtendedPseudoMetric.dist_self _
      · rw [heq01]; exact realAbsModExtDist_isExtendedPseudoMetric.dist_self _
      · exact realAbsModExtDist_isExtendedPseudoMetric.dist_self _
    have hfib_eq :
        singleCompFiber realAbsModGauge (operator_compose ψ ψ) ()
          ((operator_compose ψ ψ).func (.ofReal 0)) ex3_1_U = ex3_1_U :=
      (prop_3_5_const_component_fiber realAbsModGauge (operator_compose ψ ψ) ex3_1_U ()
        ((operator_compose ψ ψ).func (.ofReal 0)) realAbsModExtDist_isExtendedPseudoMetric
        hdom2 hconst2 ⟨.ofReal 0, Or.inl rfl, rfl⟩).1
    refine ⟨hc_bot, hdom2, heq01, hconst2, hfib_eq, ?_⟩
    intro y
    simp only [singleCompFiber, Set.mem_setOf_eq, heq01]
    have h0U : RealWithBot.ofReal 0 ∈ ex3_1_U := Or.inl rfl
    have h1U : RealWithBot.ofReal 1 ∈ ex3_1_U := Or.inr rfl
    simp [h0U, h1U]

/-! ## 习题 3.2：零化半径与距离间隙 (`CH03-P27-01`, `CH03-P27-02`) -/

/-- `CH03-P27-01`：习题 3.2(i) — 正 co-Lip 通道 `K_{i→j} > 0`（无需有限）与点态正零化半径推出：
对任意 `x ∈ U`，`d_i(x, y) ∉ (0, r^N_{ϕ, i, j}(y | U))`。 -/
theorem ex_3_2_part_i_pointwise_gap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (i j : I) (y : X)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK_pos : 0 < K i j)
    (hy : y ∈ U)
    (hr_pos : 0 < nullRadiusComp d ϕ i j y U) :
    ∀ x ∈ U, d i x y ∉ Set.Ioo 0 (nullRadiusComp d ϕ i j y U) := by
  have _ := hU_ne
  have _ := hr_pos
  intro x hx ⟨hd_pos, hd_lt⟩
  have hout_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    (positive_colip_channels_preserve_distinguishability d ϕ U K hK).1
      i j hK_pos x hx y hy hd_pos
  have hd_yx_lt : d i y x < nullRadiusComp d ϕ i j y U := by
    rw [(hd i).symm y x]
    exact hd_lt
  have hout_zero : d j (ϕ.func y) (ϕ.func x) = 0 :=
    (prop_3_11_of_lt_nullRadius d ϕ U i j y x (hd i) (hd j) hU_dom hy hx hd_yx_lt).2
  rw [(hd j).symm] at hout_zero
  exact (ne_of_gt hout_pos) hout_zero

/-- `CH03-P27-02`：习题 3.2(ii) — 当统一零化半径 `\underline{r}^N_{ϕ, i, j}|_U > 0` 且 `K_{i→j} > 0` 时，
对任意 `x, y ∈ U`，`d_i(x, y)` 落入不交并 `{0} ⊔ [\underline{r}^N_{ϕ, i, j}|_U, +∞]`。 -/
theorem ex_3_2_part_ii_uniform_gap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (i j : I)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK_pos : 0 < K i j)
    (hunif_pos : 0 < uniformNullRadiusComp d ϕ i j U) :
    Disjoint ({0} : Set ENNReal) (Set.Ici (uniformNullRadiusComp d ϕ i j U)) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      (d i x y = 0 ∨ uniformNullRadiusComp d ϕ i j U ≤ d i x y) ∧
      d i x y ∈ ({0} : Set ENNReal) ∪ Set.Ici (uniformNullRadiusComp d ϕ i j U) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_singleton_left, Set.mem_Ici]
    exact not_le_of_gt hunif_pos
  · intro x hx y hy
    have hle_pt : uniformNullRadiusComp d ϕ i j U ≤ nullRadiusComp d ϕ i j y U :=
      iInf₂_le y hy
    have hpt_pos : 0 < nullRadiusComp d ϕ i j y U := lt_of_lt_of_le hunif_pos hle_pt
    have hnot_in := ex_3_2_part_i_pointwise_gap d hd ϕ U K i j y
      hU_ne hU_dom hK hK_pos hy hpt_pos x hx
    by_cases h0 : d i x y = 0
    · exact ⟨Or.inl h0, Or.inl h0⟩
    · have hpos : 0 < d i x y := pos_iff_ne_zero.mpr h0
      have hge : uniformNullRadiusComp d ϕ i j U ≤ d i x y := by
        by_contra hnot_ge
        have hlt : d i x y < nullRadiusComp d ϕ i j y U :=
          lt_of_lt_of_le (lt_of_not_ge hnot_ge) hle_pt
        exact hnot_in ⟨hpos, hlt⟩
      exact ⟨Or.inr hge, Or.inr hge⟩

/-! ## 习题 3.3：平移下的纤维与熵差 (`CH03-P28-01`, `CH03-P28-02`) -/

/-- 习题 3.3 的平移算子 `ϕ(x) = x + 1`（保吸收元）。 -/
noncomputable def ex3_3_phi : Operator RealWithBot RealWithBot.bot :=
  liftRealMap (fun x : ℝ => x + 1)

/-- 习题 3.3 的受限域 `U = {-3, -2, 0, 2}`。 -/
def ex3_3_U : Set RealWithBot :=
  {.ofReal (-3), .ofReal (-2), .ofReal 0, .ofReal 2}

/-- `CH03-P28-01`：习题 3.3(i) — 验证空间与算子结构合法性，并完整给出恒等算子与平移算子 `ϕ` 在 `U = {-3, -2, 0, 2}` 上的计算纤维分划：
恒等算子分划为 `{{-3}, {-2, 2}, {0}}`；`ϕ` 分划为 `{{-3}, {-2, 0}, {2}}`。 -/
theorem ex_3_3_part_i_fiber_partitions :
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot RealWithBot.bot (realAbsModGauge u)) ∧
    ex3_3_U ⊆ dom realIdOp ∩ dom ex3_3_phi ∧
    fiberPartitionFamily realAbsModGauge realIdOp ({()} : Set Unit) ex3_3_U =
      {{.ofReal (-3)}, {.ofReal (-2), .ofReal 2}, {.ofReal 0}} ∧
    IsSetPartition (fiberPartitionFamily realAbsModGauge realIdOp ({()} : Set Unit) ex3_3_U) ex3_3_U ∧
    fiberPartitionFamily realAbsModGauge ex3_3_phi ({()} : Set Unit) ex3_3_U =
      {{.ofReal (-3)}, {.ofReal (-2), .ofReal 0}, {.ofReal 2}} ∧
    IsSetPartition (fiberPartitionFamily realAbsModGauge ex3_3_phi ({()} : Set Unit) ex3_3_U) ex3_3_U := by
  have hdom_id : ex3_3_U ⊆ dom realIdOp := by
    intro p hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [dom, realIdOp, operator_identity]
  have hdom_phi : ex3_3_U ⊆ dom ex3_3_phi := by
    intro p hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [dom, ex3_3_phi]
  -- 恒等算子各像点纤维计算
  have hid_m3 : compFiber realAbsModGauge realIdOp {()} (realIdOp.func (.ofReal (-3))) ex3_3_U =
      {.ofReal (-3)} := by
    ext p
    rw [compFiber_singleton_eq]
    simp only [singleCompFiber, ex3_3_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      all_goals norm_num [realAbsModGauge, realIdOp, operator_identity] at h0
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num [realAbsModGauge, realIdOp, operator_identity]⟩
  have hid_m2 : compFiber realAbsModGauge realIdOp {()} (realIdOp.func (.ofReal (-2))) ex3_3_U =
      {.ofReal (-2), .ofReal 2} := by
    ext p
    rw [compFiber_singleton_eq]
    simp only [singleCompFiber, ex3_3_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [realAbsModGauge, realIdOp, operator_identity] at h0
      · exact Or.inl rfl
      · norm_num [realAbsModGauge, realIdOp, operator_identity] at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [realAbsModGauge, realIdOp, operator_identity]⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)),
          by norm_num [realAbsModGauge, realIdOp, operator_identity]⟩
  have hid_0 : compFiber realAbsModGauge realIdOp {()} (realIdOp.func (.ofReal 0)) ex3_3_U =
      {.ofReal 0} := by
    ext p
    rw [compFiber_singleton_eq]
    simp only [singleCompFiber, ex3_3_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [realAbsModGauge, realIdOp, operator_identity] at h0
      · norm_num [realAbsModGauge, realIdOp, operator_identity] at h0
      · rfl
      · norm_num [realAbsModGauge, realIdOp, operator_identity] at h0
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inl rfl)),
        by norm_num [realAbsModGauge, realIdOp, operator_identity]⟩
  have hid_2 : compFiber realAbsModGauge realIdOp {()} (realIdOp.func (.ofReal 2)) ex3_3_U =
      {.ofReal (-2), .ofReal 2} := by
    rw [← hid_m2]
    apply prop_3_5_target_zero_invariant realAbsModGauge realAbsModGauge_isExtendedPseudoMetric
      realIdOp ex3_3_U {()} _ _ hdom_id (Set.singleton_nonempty ())
    rw [subfamily_pseudometric_singleton]
    norm_num [realAbsModGauge, realIdOp, operator_identity]
  have hpart_id_eq :
      fiberPartitionFamily realAbsModGauge realIdOp ({()} : Set Unit) ex3_3_U =
        {{.ofReal (-3)}, {.ofReal (-2), .ofReal 2}, {.ofReal 0}} := by
    ext F
    simp only [fiberPartitionFamily, operator_image, ex3_3_U, Set.mem_setOf_eq,
      Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨x, rfl | rfl | rfl | rfl, rfl⟩, rfl⟩
      · exact Or.inl hid_m3
      · exact Or.inr (Or.inl hid_m2)
      · exact Or.inr (Or.inr hid_0)
      · exact Or.inr (Or.inl hid_2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, ⟨.ofReal (-3), Or.inl rfl, rfl⟩, hid_m3.symm⟩
      · exact ⟨_, ⟨.ofReal (-2), Or.inr (Or.inl rfl), rfl⟩, hid_m2.symm⟩
      · exact ⟨_, ⟨.ofReal 0, Or.inr (Or.inr (Or.inl rfl)), rfl⟩, hid_0.symm⟩
  -- 平移算子 ϕ 各像点纤维计算
  have hphi_m3 : compFiber realAbsModGauge ex3_3_phi {()} (ex3_3_phi.func (.ofReal (-3))) ex3_3_U =
      {.ofReal (-3)} := by
    ext p
    rw [compFiber_singleton_eq]
    simp only [singleCompFiber, ex3_3_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      all_goals norm_num [realAbsModGauge, ex3_3_phi] at h0
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num [realAbsModGauge, ex3_3_phi]⟩
  have hphi_m2 : compFiber realAbsModGauge ex3_3_phi {()} (ex3_3_phi.func (.ofReal (-2))) ex3_3_U =
      {.ofReal (-2), .ofReal 0} := by
    ext p
    rw [compFiber_singleton_eq]
    simp only [singleCompFiber, ex3_3_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [realAbsModGauge, ex3_3_phi] at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num [realAbsModGauge, ex3_3_phi] at h0
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [realAbsModGauge, ex3_3_phi]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [realAbsModGauge, ex3_3_phi]⟩
  have hphi_0 : compFiber realAbsModGauge ex3_3_phi {()} (ex3_3_phi.func (.ofReal 0)) ex3_3_U =
      {.ofReal (-2), .ofReal 0} := by
    rw [← hphi_m2]
    apply prop_3_5_target_zero_invariant realAbsModGauge realAbsModGauge_isExtendedPseudoMetric
      ex3_3_phi ex3_3_U {()} _ _ hdom_phi (Set.singleton_nonempty ())
    rw [subfamily_pseudometric_singleton]
    norm_num [realAbsModGauge, ex3_3_phi]
  have hphi_2 : compFiber realAbsModGauge ex3_3_phi {()} (ex3_3_phi.func (.ofReal 2)) ex3_3_U =
      {.ofReal 2} := by
    ext p
    rw [compFiber_singleton_eq]
    simp only [singleCompFiber, ex3_3_U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [realAbsModGauge, ex3_3_phi] at h0
      · norm_num [realAbsModGauge, ex3_3_phi] at h0
      · norm_num [realAbsModGauge, ex3_3_phi] at h0
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [realAbsModGauge, ex3_3_phi]⟩
  have hpart_phi_eq :
      fiberPartitionFamily realAbsModGauge ex3_3_phi ({()} : Set Unit) ex3_3_U =
        {{.ofReal (-3)}, {.ofReal (-2), .ofReal 0}, {.ofReal 2}} := by
    ext F
    simp only [fiberPartitionFamily, operator_image, ex3_3_U, Set.mem_setOf_eq,
      Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨x, rfl | rfl | rfl | rfl, rfl⟩, rfl⟩
      · exact Or.inl hphi_m3
      · exact Or.inr (Or.inl hphi_m2)
      · exact Or.inr (Or.inl hphi_0)
      · exact Or.inr (Or.inr hphi_2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, ⟨.ofReal (-3), Or.inl rfl, rfl⟩, hphi_m3.symm⟩
      · exact ⟨_, ⟨.ofReal (-2), Or.inr (Or.inl rfl), rfl⟩, hphi_m2.symm⟩
      · exact ⟨_, ⟨.ofReal 2, Or.inr (Or.inr (Or.inr rfl)), rfl⟩, hphi_2.symm⟩
  refine ⟨realAbsModGauge_isExtendedPseudoMetric, fun p hp => ⟨hdom_id hp, hdom_phi hp⟩,
    hpart_id_eq,
    (prop_3_5_image_fibers_dichotomy_and_partition realAbsModGauge
      realAbsModGauge_isExtendedPseudoMetric realIdOp ex3_3_U {()} hdom_id
      (Set.singleton_nonempty ())).2,
    hpart_phi_eq,
    (prop_3_5_image_fibers_dichotomy_and_partition realAbsModGauge
      realAbsModGauge_isExtendedPseudoMetric ex3_3_phi ex3_3_U {()} hdom_phi
      (Set.singleton_nonempty ())).2⟩

/-- `CH03-P28-02`：习题 3.3(ii) — 在精度 `ε = 3/2` 下显式给出两端内部覆盖数的上下界与精确值：
`N_i(3/2, U) = 2`，`N_i(3/2, ϕ(U)) = 1`，以及 `\Delta E_{3/2, i}(ϕ | U) = 1`。 -/
theorem ex_3_3_part_ii_covering_and_entropyDiff :
    covering_number realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U ≤ 2 ∧
    2 ≤ covering_number realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U ∧
    covering_number realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U = 2 ∧
    covering_number realAbsModExtDist (3 / 2 : ENNReal) (operator_image ex3_3_phi ex3_3_U) ≤ 1 ∧
    1 ≤ covering_number realAbsModExtDist (3 / 2 : ENNReal) (operator_image ex3_3_phi ex3_3_U) ∧
    covering_number realAbsModExtDist (3 / 2 : ENNReal) (operator_image ex3_3_phi ex3_3_U) = 1 ∧
    metric_entropy realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U = 1 ∧
    metric_entropy realAbsModExtDist (3 / 2 : ENNReal) (operator_image ex3_3_phi ex3_3_U) = 0 ∧
    ∃ hdef : MappingEntropyDiffSingleDefined realAbsModGauge ex3_3_phi ex3_3_U () (3 / 2 : ENNReal),
      mappingEntropyDiffSingle realAbsModGauge ex3_3_phi ex3_3_U () (3 / 2 : ENNReal) hdef = 1 := by
  classical
  have h32_eq : (3 / 2 : ENNReal) = ENNReal.ofReal (3 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h1_lt_32 : (1 : ENNReal) < 3 / 2 := by
    rw [← ENNReal.ofReal_one, h32_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h0_lt_32 : (0 : ENNReal) < 3 / 2 := lt_trans zero_lt_one h1_lt_32
  have h32_lt_2 : (3 / 2 : ENNReal) < 2 := by
    rw [h32_eq, show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h32_lt_top : (3 / 2 : ENNReal) < ⊤ := lt_trans h32_lt_2 (by simp)
  -- 1. 输入覆盖数上界 ≤ 2：取内部中心集 {-2, 0} ⊆ U
  have hin_le2 : covering_number realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U ≤ 2 := by
    let Sin : Finset RealWithBot := {RealWithBot.ofReal (-2), RealWithBot.ofReal 0}
    have hnet_in : InternalEpsilonNet realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U Sin := by
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact Or.inr (Or.inl rfl)
        · rw [Finset.mem_singleton.mp hp']
          exact Or.inr (Or.inr (Or.inl rfl))
      · intro p hp
        rcases hp with rfl | rfl | rfl | rfl
        · refine ⟨.ofReal (-2), by simp [Sin], ?_⟩
          have hd : realAbsModExtDist (.ofReal (-3)) (.ofReal (-2)) = 1 := by norm_num
          rw [hd]; exact h1_lt_32
        · refine ⟨.ofReal (-2), by simp [Sin], ?_⟩
          have hd : realAbsModExtDist (.ofReal (-2)) (.ofReal (-2)) = 0 := by norm_num
          rw [hd]; exact h0_lt_32
        · refine ⟨.ofReal 0, by simp [Sin], ?_⟩
          have hd : realAbsModExtDist (.ofReal 0) (.ofReal 0) = 0 := by norm_num
          rw [hd]; exact h0_lt_32
        · refine ⟨.ofReal (-2), by simp [Sin], ?_⟩
          have hd : realAbsModExtDist (.ofReal 2) (.ofReal (-2)) = 0 := by norm_num
          rw [hd]; exact h0_lt_32
    have hne_pair : RealWithBot.ofReal (-2) ≠ RealWithBot.ofReal 0 := by norm_num
    have hcard : (Sin.card : ENNReal) ≤ 2 := by simp [Sin, Finset.card_pair hne_pair]
    exact le_trans (iInf_le_of_le Sin (iInf_le_of_le hnet_in le_rfl)) hcard
  -- 2. 输入覆盖数下界 ≥ 2：0 与其余点距离 ≥ 2 > 3/2，故 0 必须作为独立中心，且不能覆盖 -3
  have hin_ge2 : 2 ≤ covering_number realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U := by
    apply le_iInf₂
    intro S hS
    have h0_mem : RealWithBot.ofReal 0 ∈ S := by
      rcases hS.2 (.ofReal 0) (Or.inr (Or.inr (Or.inl rfl))) with ⟨c, hcS, hc_dist⟩
      rcases hS.1 hcS with rfl | rfl | rfl | rfl
      · exfalso
        have hd : realAbsModExtDist (.ofReal 0) (.ofReal (-3)) = 3 := by norm_num
        rw [hd] at hc_dist
        have h2_le_3 : (2 : ENNReal) ≤ 3 := by norm_num
        exact (not_lt_of_ge (le_trans h32_lt_2.le h2_le_3)) hc_dist
      · exfalso
        have hd : realAbsModExtDist (.ofReal 0) (.ofReal (-2)) = 2 := by norm_num
        rw [hd] at hc_dist
        exact (not_lt_of_ge h32_lt_2.le) hc_dist
      · exact hcS
      · exfalso
        have hd : realAbsModExtDist (.ofReal 0) (.ofReal 2) = 2 := by norm_num
        rw [hd] at hc_dist
        exact (not_lt_of_ge h32_lt_2.le) hc_dist
    rcases hS.2 (.ofReal (-3)) (Or.inl rfl) with ⟨c₂, hc₂S, hc₂_dist⟩
    have hc₂_ne0 : c₂ ≠ RealWithBot.ofReal 0 := by
      rintro rfl
      have hd : realAbsModExtDist (.ofReal (-3)) (.ofReal 0) = 3 := by norm_num
      rw [hd] at hc₂_dist
      have h2_le_3 : (2 : ENNReal) ≤ 3 := by norm_num
      exact (not_lt_of_ge (le_trans h32_lt_2.le h2_le_3)) hc₂_dist
    have hsub_pair : ({RealWithBot.ofReal 0, c₂} : Finset RealWithBot) ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact h0_mem
      · rw [Finset.mem_singleton.mp hz']
        exact hc₂S
    have hcard_ge : 2 ≤ S.card := by
      calc
        2 = ({RealWithBot.ofReal 0, c₂} : Finset RealWithBot).card :=
          (Finset.card_pair hc₂_ne0.symm).symm
        _ ≤ S.card := Finset.card_le_card hsub_pair
    exact_mod_cast hcard_ge
  have hin_eq2 : covering_number realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U = 2 :=
    le_antisymm hin_le2 hin_ge2
  -- 3. 输出覆盖数上下界：取单中心 {ϕ(-3) = -2} ⊆ ϕ(U)
  have hout_le1 :
      covering_number realAbsModExtDist (3 / 2 : ENNReal)
        (operator_image ex3_3_phi ex3_3_U) ≤ 1 := by
    let Sout : Finset RealWithBot := {ex3_3_phi.func (.ofReal (-3))}
    have hnet_out : InternalEpsilonNet realAbsModExtDist (3 / 2 : ENNReal)
        (operator_image ex3_3_phi ex3_3_U) Sout := by
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [Finset.mem_coe, Finset.mem_singleton] at hz
        rw [hz]
        exact ⟨.ofReal (-3), Or.inl rfl, rfl⟩
      · rintro z ⟨x, hxU, rfl⟩
        refine ⟨ex3_3_phi.func (.ofReal (-3)), Finset.mem_singleton_self _, ?_⟩
        rcases hxU with rfl | rfl | rfl | rfl
        · have hd : realAbsModExtDist (ex3_3_phi.func (.ofReal (-3)))
              (ex3_3_phi.func (.ofReal (-3))) = 0 := by norm_num [ex3_3_phi]
          rw [hd]; exact h0_lt_32
        · have hd : realAbsModExtDist (ex3_3_phi.func (.ofReal (-2)))
              (ex3_3_phi.func (.ofReal (-3))) = 1 := by norm_num [ex3_3_phi]
          rw [hd]; exact h1_lt_32
        · have hd : realAbsModExtDist (ex3_3_phi.func (.ofReal 0))
              (ex3_3_phi.func (.ofReal (-3))) = 1 := by norm_num [ex3_3_phi]
          rw [hd]; exact h1_lt_32
        · have hd : realAbsModExtDist (ex3_3_phi.func (.ofReal 2))
              (ex3_3_phi.func (.ofReal (-3))) = 1 := by norm_num [ex3_3_phi]
          rw [hd]; exact h1_lt_32
    exact le_trans (iInf_le_of_le Sout (iInf_le_of_le hnet_out le_rfl)) (by simp [Sout])
  have hout_ge1 :
      1 ≤ covering_number realAbsModExtDist (3 / 2 : ENNReal)
        (operator_image ex3_3_phi ex3_3_U) :=
    one_le_covering_number_of_nonempty _ _ _ ⟨ex3_3_phi.func (.ofReal (-3)), ⟨.ofReal (-3), Or.inl rfl, rfl⟩⟩
  have hout_eq1 :
      covering_number realAbsModExtDist (3 / 2 : ENNReal)
        (operator_image ex3_3_phi ex3_3_U) = 1 :=
    le_antisymm hout_le1 hout_ge1
  -- 4. 度量熵与映射熵差
  have hent_in : metric_entropy realAbsModExtDist (3 / 2 : ENNReal) ex3_3_U = 1 := by
    have h2_ne0 : (2 : ENNReal) ≠ 0 := by norm_num
    have h2_netop : (2 : ENNReal) ≠ ⊤ := by simp
    simp only [metric_entropy, hin_eq2, log2_ereal, if_neg h2_ne0, if_neg h2_netop]
    have hto : (2 : ENNReal).toReal = 2 := by norm_num
    rw [hto, Real.logb_self_eq_one one_lt_two]
    rfl
  have hent_out :
      metric_entropy realAbsModExtDist (3 / 2 : ENNReal)
        (operator_image ex3_3_phi ex3_3_U) = 0 := by
    simp [metric_entropy, hout_eq1, log2_ereal]
  have hdom_phi : ex3_3_U ⊆ dom ex3_3_phi := by
    intro p hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [dom, ex3_3_phi]
  have hin_sub_fin : subfamilyCoveringNumber realAbsModGauge {()} (3 / 2 : ENNReal) ex3_3_U < ⊤ := by
    rw [subfamilyCoveringNumber_singleton, realAbsModGauge, hin_eq2]
    exact by simp
  have hdef : MappingEntropyDiffSingleDefined realAbsModGauge ex3_3_phi ex3_3_U () (3 / 2 : ENNReal) :=
    ⟨⟨.ofReal (-3), Or.inl rfl⟩, hdom_phi, Set.singleton_nonempty (), Set.singleton_nonempty (),
      h0_lt_32, h32_lt_top, Or.inl hin_sub_fin⟩
  refine ⟨hin_le2, hin_ge2, hin_eq2, hout_le1, hout_ge1, hout_eq1, hent_in, hent_out, hdef, ?_⟩
  unfold mappingEntropyDiffSingle
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
    subfamily_metric_entropy_singleton]
  change metric_entropy realAbsModExtDist (3 / 2) ex3_3_U -
      metric_entropy realAbsModExtDist (3 / 2) (operator_image ex3_3_phi ex3_3_U) = 1
  rw [hent_in, hent_out, sub_zero]

end Ch03
