import Ch03.Sec06
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset
 
/-! ### 绝对值读数伪度量 `d(x, y) = ||x| - |y||`（习题 3.1 与 3.3 共用） -/
 
/-- 实数部分采用绝对值读数差 `|(|x| - |y|)|`、吸收元隔离的扩展伪度量。 -/
noncomputable def realAbsDist : RealWithBot → RealWithBot → ENNReal
  | .bot, .bot => 0
  | .bot, .val _ => ⊤
  | .val _, .bot => ⊤
  | .val x, .val y => ENNReal.ofReal |(|x| - |y|)|
 
@[simp] theorem realAbsDist_val (x y : ℝ) :
    realAbsDist (.val x) (.val y) = ENNReal.ofReal |(|x| - |y|)| := rfl
 
@[simp] theorem realAbsDist_val_eq_zero_iff (x y : ℝ) :
    realAbsDist (.val x) (.val y) = 0 ↔ |x| = |y| := by
  rw [realAbsDist_val, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have h0 : |(|x| - |y|)| = 0 := le_antisymm h (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h0)
  · intro h
    simp [h]
 
theorem realAbsDist_is_extended :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realAbsDist where
  nonabsorbing := ⟨.val 0, fun h => by cases h⟩
  dist_self x := by cases x <;> simp [realAbsDist]
  symm x y := by
    cases x <;> cases y <;> simp [realAbsDist, abs_sub_comm]
  triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp [realAbsDist]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
  isolate_bot x hx := by
    cases x with
    | bot => exact False.elim (hx rfl)
    | val _ => rfl
 
noncomputable abbrev realAbsGauge : Unit → RealWithBot → RealWithBot → ENNReal := fun _ => realAbsDist
 
/-! ### 习题 3.1：计算纤维与自复合 (CH03-P26-01 .. 03) -/
 
/-- 习题 3.1 中的仿射算子 `ϕ(x) = 2x - 1, ϕ(⊥) = ⊥`。 -/
noncomputable def ex31Phi : Operator RealWithBot RealWithBot.bot where
  func
    | .bot => .bot
    | .val x => .val (2 * x - 1)
  preserves_bot := rfl
 
@[simp] theorem ex31Phi_val (x : ℝ) : ex31Phi.func (.val x) = .val (2 * x - 1) := rfl
 
def ex31U : Set RealWithBot := {.val 0, .val 1}
 
/-- CH03-P26-01: 习题 3.1(i-a) 验证绝对值读数伪度量与算子合法性，算出 `ϕ` 的纤维与分量类型。 -/
theorem ex_3_1_i_a_phi_fiber_and_type :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realAbsDist ∧
    ex31U ⊆ dom ex31Phi ∧
    CompFiberSingle realAbsGauge ex31Phi () (ex31Phi.func (.val 0)) ex31U = ex31U ∧
    () ∈ I_const realAbsGauge ex31Phi ex31U ∧
    I_const realAbsGauge ex31Phi ex31U = {()} ∧
    I_id realAbsGauge ex31Phi ex31U = ∅ ∧
    I_act realAbsGauge ex31Phi ex31U = ∅ := by
  have hdom : ex31U ⊆ dom ex31Phi := by
    intro x hx hbot
    rcases hx with rfl | rfl <;> cases hbot
  have hconst_mem : () ∈ I_const realAbsGauge ex31Phi ex31U := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [realAbsGauge] <;> norm_num
  have hfib : CompFiberSingle realAbsGauge ex31Phi ()
      (ex31Phi.func (.val 0)) ex31U = ex31U := by
    rw [CompFiberSingle_eq]
    ext x
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hconst_mem x hx (.val 0) (Set.mem_insert _ _)
  refine ⟨realAbsDist_is_extended, hdom, hfib, hconst_mem, ?_, ?_, ?_⟩
  · ext u; cases u; simp [hconst_mem]
  · ext u; cases u; simp [I_id, hconst_mem]
  · ext u; cases u; simp [I_act, hconst_mem]
 
/-- CH03-P26-02: 习题 3.1(i-b) 算出自复合 `ϕ²` 在 `U = {0, 1}` 上的纤维与分量类型。 -/
theorem ex_3_1_i_b_phi_sq_fiber_and_type :
    ex31U ⊆ dom (ex31Phi * ex31Phi) ∧
    CompFiberSingle realAbsGauge (ex31Phi * ex31Phi) ()
      ((ex31Phi * ex31Phi).func (.val 0)) ex31U = {.val 0} ∧
    CompFiberSingle realAbsGauge (ex31Phi * ex31Phi) ()
      ((ex31Phi * ex31Phi).func (.val 1)) ex31U = {.val 1} ∧
    () ∉ I_const realAbsGauge (ex31Phi * ex31Phi) ex31U ∧
    () ∉ I_id realAbsGauge (ex31Phi * ex31Phi) ex31U ∧
    () ∈ I_act realAbsGauge (ex31Phi * ex31Phi) ex31U ∧
    I_act realAbsGauge (ex31Phi * ex31Phi) ex31U = {()} := by
  have hdom : ex31U ⊆ dom (ex31Phi * ex31Phi) := by
    intro x hx hbot
    rcases hx with rfl | rfl <;> cases hbot
  have hsq_val : ∀ x : ℝ, (ex31Phi * ex31Phi).func (.val x) = .val (2 * (2 * x - 1) - 1) :=
    fun _ => rfl
  have hfib0 : CompFiberSingle realAbsGauge (ex31Phi * ex31Phi) ()
      ((ex31Phi * ex31Phi).func (.val 0)) ex31U = {.val 0} := by
    rw [CompFiberSingle_eq]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h0⟩
      · rfl
      · exfalso
        rw [hsq_val 1, hsq_val 0] at h0
        simp [realAbsGauge] at h0
        norm_num at h0
    · rintro rfl
      exact ⟨Set.mem_insert _ _, by rw [hsq_val 0]; simp [realAbsGauge]⟩
  have hfib1 : CompFiberSingle realAbsGauge (ex31Phi * ex31Phi) ()
      ((ex31Phi * ex31Phi).func (.val 1)) ex31U = {.val 1} := by
    rw [CompFiberSingle_eq]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h0⟩
      · exfalso
        rw [hsq_val 0, hsq_val 1] at h0
        simp [realAbsGauge] at h0
        norm_num at h0
      · rfl
    · rintro rfl
      exact ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), by rw [hsq_val 1]; simp [realAbsGauge]⟩
  have hnconst : () ∉ I_const realAbsGauge (ex31Phi * ex31Phi) ex31U := by
    intro hc
    have h := hc (.val 0) (Set.mem_insert _ _) (.val 1)
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [hsq_val 0, hsq_val 1] at h
    simp [realAbsGauge] at h
    norm_num at h
  have hnid : () ∉ I_id realAbsGauge (ex31Phi * ex31Phi) ex31U := by
    intro hid
    have h := hid.2 (.val 0) (Set.mem_insert _ _)
    rw [hsq_val 0] at h
    simp [realAbsGauge] at h
    norm_num at h
  have hact : () ∈ I_act realAbsGauge (ex31Phi * ex31Phi) ex31U :=
    ⟨trivial, fun hor => hor.elim hnconst hnid⟩
  refine ⟨hdom, hfib0, hfib1, hnconst, hnid, hact, ?_⟩
  ext u; cases u
  exact ⟨fun _ => rfl, fun _ => hact⟩
 
/-- CH03-P26-03: 习题 3.1(ii) 点值常算子在 `U` 上取同一实数值 `c` 时，自复合仍不能使 `0, 1` 落入不同纤维；并完整区分 `ψ(c) ≠ ⊥`（`U ⊆ dom(ψ²)`，常值单一纤维 `U`）与 `ψ(c) = ⊥`（`U ⊈ dom(ψ²)`，超出受限纤维适用域）两分支。 -/
theorem ex_3_1_ii_pointwise_const_self_comp (ψ : Operator RealWithBot RealWithBot.bot) (c : ℝ)
    (hconst_val : ∀ x ∈ ex31U, ψ.func x = .val c) :
    ex31U ⊆ dom ψ ∧
    (ψ * ψ).func (.val 0) = ψ.func (.val c) ∧
    (ψ * ψ).func (.val 1) = ψ.func (.val c) ∧
    (∀ y : RealWithBot,
      .val 0 ∈ CompFiberSingle realAbsGauge (ψ * ψ) () y ex31U ↔
        .val 1 ∈ CompFiberSingle realAbsGauge (ψ * ψ) () y ex31U) ∧
    ((ψ.func (.val c) ≠ .bot →
        ex31U ⊆ dom (ψ * ψ) ∧
        () ∈ I_const realAbsGauge (ψ * ψ) ex31U ∧
        CompFiberSingle realAbsGauge (ψ * ψ) () ((ψ * ψ).func (.val 0)) ex31U = ex31U) ∧
     (ψ.func (.val c) = .bot →
        dom (ψ * ψ) ∩ ex31U = ∅ ∧
        ¬ (ex31U ⊆ dom (ψ * ψ)))) := by
  have h0 : ψ.func (.val 0) = .val c := hconst_val (.val 0) (Set.mem_insert _ _)
  have h1 : ψ.func (.val 1) = .val c :=
    hconst_val (.val 1) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hdomψ : ex31U ⊆ dom ψ := by
    intro x hx hbot
    rw [hconst_val x hx] at hbot
    cases hbot
  have hsq0 : (ψ * ψ).func (.val 0) = ψ.func (.val c) := by
    change ψ.func (ψ.func (.val 0)) = _
    rw [h0]
  have hsq1 : (ψ * ψ).func (.val 1) = ψ.func (.val c) := by
    change ψ.func (ψ.func (.val 1)) = _
    rw [h1]
  refine ⟨hdomψ, hsq0, hsq1, ?_, ⟨?_, ?_⟩⟩
  · intro y
    rw [CompFiberSingle_eq]
    simp only [Set.mem_setOf_eq, hsq0, hsq1]
    have hm0 : RealWithBot.val 0 ∈ ex31U := Set.mem_insert _ _
    have hm1 : RealWithBot.val 1 ∈ ex31U := Set.mem_insert_of_mem _ (Set.mem_singleton _)
    simp [hm0, hm1]
  · intro hne_bot
    have hdom2 : ex31U ⊆ dom (ψ * ψ) := by
      intro x hx
      rcases hx with rfl | rfl
      · change (ψ * ψ).func (.val 0) ≠ .bot; rw [hsq0]; exact hne_bot
      · change (ψ * ψ).func (.val 1) ≠ .bot; rw [hsq1]; exact hne_bot
    have hc2 : () ∈ I_const realAbsGauge (ψ * ψ) ex31U := by
      intro x hx y hy
      have hsqx : (ψ * ψ).func x = ψ.func (.val c) := by
        rcases hx with rfl | rfl <;> [exact hsq0; exact hsq1]
      have hsqy : (ψ * ψ).func y = ψ.func (.val c) := by
        rcases hy with rfl | rfl <;> [exact hsq0; exact hsq1]
      rw [hsqx, hsqy]
      exact realAbsDist_is_extended.dist_self _
    have hfib2 : CompFiberSingle realAbsGauge (ψ * ψ) () ((ψ * ψ).func (.val 0)) ex31U = ex31U := by
      rw [CompFiberSingle_eq]
      ext x
      simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
      exact fun hx => hc2 x hx (.val 0) (Set.mem_insert _ _)
    exact ⟨hdom2, hc2, hfib2⟩
  · intro heq_bot
    refine ⟨?_, ?_⟩
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hdomx (rfl | rfl)
      · exact hdomx (by rw [hsq0, heq_bot])
      · exact hdomx (by rw [hsq1, heq_bot])
    · intro hsub
      exact hsub (Set.mem_insert _ _) (by rw [hsq0, heq_bot])
 
/-! ### 习题 3.2：零化半径与距离间隙 (CH03-P27-01 .. 02) -/
 
/-- CH03-P27-01: 习题 3.2(i) 正 co-Lip 通道（无需有限）与点态正零化半径推出 `(0, r^N(y | U))` 内无输入距离。 -/
theorem ex_3_2_i_pointwise_distance_gap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I) (y : X)
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j)
    (hy : y ∈ U) (_hr_pos : 0 < pointwiseNullRadiusComp d ϕ i j y U) :
    ∀ x ∈ U, d i x y ∉ Set.Ioo 0 (pointwiseNullRadiusComp d ϕ i j y U) := by
  intro x hx ⟨hd_pos, hd_lt⟩
  have hyx_lt : d i y x < pointwiseNullRadiusComp d ϕ i j y U := by
    rw [(hd i).symm y x]
    exact hd_lt
  have hout_zero : d j (ϕ.func y) (ϕ.func x) = 0 :=
    (prop_3_11_lt_radius_zero d hd ϕ U i j y x hU hy hx hyx_lt).2
  have hout_zero' : d j (ϕ.func x) (ϕ.func y) = 0 := by
    rw [(hd j).symm]
    exact hout_zero
  have hout_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    (positive_colip_channels_preserve_distinguishability d ϕ U K hK).1 i j hK_pos x hx y hy hd_pos
  exact (ne_of_gt hout_pos) hout_zero'
 
/-- CH03-P27-02: 习题 3.2(ii) 正统一零化半径下，`U` 中任意点对的输入距离落入不交并 `{0} ⊔ [\underline{r}^N|_U, +∞]`。 -/
theorem ex_3_2_ii_uniform_distance_dichotomy {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j)
    (hr_pos : 0 < uniformNullRadiusComp d ϕ i j U) :
    Disjoint ({0} : Set ENNReal) (Set.Ici (uniformNullRadiusComp d ϕ i j U)) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      (d i x y = 0 ∨ uniformNullRadiusComp d ϕ i j U ≤ d i x y) ∧
      d i x y ∈ ({0} : Set ENNReal) ∪ Set.Ici (uniformNullRadiusComp d ϕ i j U) := by
  refine ⟨Set.disjoint_left.mpr (fun z hz0 hge => ?_), ?_⟩
  · rw [Set.mem_singleton_iff.mp hz0] at hge
    exact not_lt_of_ge hge hr_pos
  · intro x hx y hy
    have hpt_ge : uniformNullRadiusComp d ϕ i j U ≤ pointwiseNullRadiusComp d ϕ i j y U :=
      iInf₂_le y hy
    have hpt_pos : 0 < pointwiseNullRadiusComp d ϕ i j y U := lt_of_lt_of_le hr_pos hpt_ge
    have hgap := ex_3_2_i_pointwise_distance_gap d hd ϕ U K i j y hU_ne hU hK hK_pos hy hpt_pos x hx
    have hor : d i x y = 0 ∨ uniformNullRadiusComp d ϕ i j U ≤ d i x y := by
      by_cases h0 : d i x y = 0
      · exact Or.inl h0
      · right
        by_contra hlt
        push Not at hlt
        exact hgap ⟨pos_iff_ne_zero.mpr h0, lt_of_lt_of_le hlt hpt_ge⟩
    exact ⟨hor, by simpa only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici] using hor⟩
 
/-! ### 习题 3.3：平移下的纤维与熵差 (CH03-P28-01 .. 02) -/
 
/-- 习题 3.3 中的平移算子 `ϕ(x) = x + 1, ϕ(⊥) = ⊥`。 -/
noncomputable def ex33Phi : Operator RealWithBot RealWithBot.bot where
  func
    | .bot => .bot
    | .val x => .val (x + 1)
  preserves_bot := rfl
 
@[simp] theorem ex33Phi_val (x : ℝ) : ex33Phi.func (.val x) = .val (x + 1) := rfl
 
def ex33U : Set RealWithBot := {.val (-3), .val (-2), .val 0, .val 2}
 
private theorem mem_ex33U_iff (x : RealWithBot) :
    x ∈ ex33U ↔ x = .val (-3) ∨ x = .val (-2) ∨ x = .val 0 ∨ x = .val 2 := by
  simp [ex33U]
 
/-- CH03-P28-01: 习题 3.3(i) 验证结构合法性，并完整列出恒等算子与平移算子在 `U` 上的计算纤维及分划。 -/
theorem ex_3_3_i_fiber_partitions :
    let idOp : Operator RealWithBot RealWithBot.bot := operator_identity
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realAbsDist ∧
    ex33U ⊆ dom idOp ∧
    ex33U ⊆ dom ex33Phi ∧
    CompFiberSingle realAbsGauge idOp () (.val (-3)) ex33U = {.val (-3)} ∧
    CompFiberSingle realAbsGauge idOp () (.val (-2)) ex33U = {.val (-2), .val 2} ∧
    CompFiberSingle realAbsGauge idOp () (.val 0) ex33U = {.val 0} ∧
    CompFiberSingle realAbsGauge idOp () (.val 2) ex33U = {.val (-2), .val 2} ∧
    CompFiberPartition realAbsGauge idOp {()} ex33U =
      {{.val (-3)}, {.val (-2), .val 2}, {.val 0}} ∧
    CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val (-3))) ex33U = {.val (-3)} ∧
    CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val (-2))) ex33U = {.val (-2), .val 0} ∧
    CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val 0)) ex33U = {.val (-2), .val 0} ∧
    CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val 2)) ex33U = {.val 2} ∧
    CompFiberPartition realAbsGauge ex33Phi {()} ex33U =
      {{.val (-3)}, {.val (-2), .val 0}, {.val 2}} := by
  dsimp only
  let idOp : Operator RealWithBot RealWithBot.bot := operator_identity
  have hid_val : ∀ x : ℝ, idOp.func (.val x) = .val x := fun _ => rfl
  have hdom_id : ex33U ⊆ dom idOp := by
    intro x hx hbot
    rcases (mem_ex33U_iff x).mp hx with rfl | rfl | rfl | rfl <;> cases hbot
  have hdom_phi : ex33U ⊆ dom ex33Phi := by
    intro x hx hbot
    rcases (mem_ex33U_iff x).mp hx with rfl | rfl | rfl | rfl <;> cases hbot
  have hid_m3 : CompFiberSingle realAbsGauge idOp () (.val (-3)) ex33U = {.val (-3)} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      all_goals rw [hid_val] at h0; rw [realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
    · rintro rfl; refine ⟨Or.inl rfl, ?_⟩; rw [hid_val]; simp [realAbsGauge]
  have hid_m2 : CompFiberSingle realAbsGauge idOp () (.val (-2)) ex33U = {.val (-2), .val 2} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
      · exact Or.inl rfl
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩; rw [hid_val]; simp [realAbsGauge]
      · refine ⟨Or.inr (Or.inr (Or.inr rfl)), ?_⟩; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff]; norm_num
  have hid_0 : CompFiberSingle realAbsGauge idOp () (.val 0) ex33U = {.val 0} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
      · rfl
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
    · rintro rfl; refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩; rw [hid_val]; simp [realAbsGauge]
  have hid_2 : CompFiberSingle realAbsGauge idOp () (.val 2) ex33U = {.val (-2), .val 2} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
      · exact Or.inl rfl
      · exfalso; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff] at h0; norm_num at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩; rw [hid_val, realAbsGauge, realAbsDist_val_eq_zero_iff]; norm_num
      · refine ⟨Or.inr (Or.inr (Or.inr rfl)), ?_⟩; rw [hid_val]; simp [realAbsGauge]
  have hpart_id : CompFiberPartition realAbsGauge idOp {()} ex33U =
      {{.val (-3)}, {.val (-2), .val 2}, {.val 0}} := by
    ext F
    simp only [CompFiberPartition, operator_image, Set.mem_setOf_eq, Set.mem_image,
      mem_ex33U_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨x, rfl | rfl | rfl | rfl, rfl⟩, rfl⟩
      · exact Or.inl hid_m3
      · exact Or.inr (Or.inl hid_m2)
      · exact Or.inr (Or.inr hid_0)
      · exact Or.inr (Or.inl hid_2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨.val (-3), ⟨.val (-3), Or.inl rfl, rfl⟩, hid_m3.symm⟩
      · exact ⟨.val (-2), ⟨.val (-2), Or.inr (Or.inl rfl), rfl⟩, hid_m2.symm⟩
      · exact ⟨.val 0, ⟨.val 0, Or.inr (Or.inr (Or.inl rfl)), rfl⟩, hid_0.symm⟩
  have hphi_m3 : CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val (-3))) ex33U =
      {.val (-3)} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      all_goals simp [realAbsGauge] at h0; norm_num at h0
    · rintro rfl; refine ⟨Or.inl rfl, ?_⟩; simp [realAbsGauge]
  have hphi_m2 : CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val (-2))) ex33U =
      {.val (-2), .val 0} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩; simp [realAbsGauge]
      · refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩; simp [realAbsGauge]; norm_num
  have hphi_0 : CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val 0)) ex33U =
      {.val (-2), .val 0} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
    · rintro (rfl | rfl)
      · refine ⟨Or.inr (Or.inl rfl), ?_⟩; simp [realAbsGauge]; norm_num
      · refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩; simp [realAbsGauge]
  have hphi_2 : CompFiberSingle realAbsGauge ex33Phi () (ex33Phi.func (.val 2)) ex33U =
      {.val 2} := by
    rw [CompFiberSingle_eq]; ext x; rw [Set.mem_setOf_eq, mem_ex33U_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
      · exfalso; simp [realAbsGauge] at h0; norm_num at h0
      · rfl
    · rintro rfl; refine ⟨Or.inr (Or.inr (Or.inr rfl)), ?_⟩; simp [realAbsGauge]
  have hpart_phi : CompFiberPartition realAbsGauge ex33Phi {()} ex33U =
      {{.val (-3)}, {.val (-2), .val 0}, {.val 2}} := by
    ext F
    simp only [CompFiberPartition, operator_image, Set.mem_setOf_eq, Set.mem_image,
      mem_ex33U_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨x, rfl | rfl | rfl | rfl, rfl⟩, rfl⟩
      · exact Or.inl hphi_m3
      · exact Or.inr (Or.inl hphi_m2)
      · exact Or.inr (Or.inl hphi_0)
      · exact Or.inr (Or.inr hphi_2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨_, ⟨.val (-3), Or.inl rfl, rfl⟩, hphi_m3.symm⟩
      · exact ⟨_, ⟨.val (-2), Or.inr (Or.inl rfl), rfl⟩, hphi_m2.symm⟩
      · exact ⟨_, ⟨.val 2, Or.inr (Or.inr (Or.inr rfl)), rfl⟩, hphi_2.symm⟩
  exact ⟨realAbsDist_is_extended, hdom_id, hdom_phi,
    hid_m3, hid_m2, hid_0, hid_2, hpart_id,
    hphi_m3, hphi_m2, hphi_0, hphi_2, hpart_phi⟩
 
private theorem ennreal_three_halves : (3 / 2 : ENNReal) = ENNReal.ofReal (3 / 2) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
 
/-- CH03-P28-02: 习题 3.3(ii) 在精度 `ε = 3/2` 下给出上下界并精确计算 `𝒩_i(ε, U) = 2`、`𝒩_i(ε, ϕ(U)) = 1` 与 `ΔE_{ε, i}(ϕ | U) = 1`。 -/
theorem ex_3_3_ii_covering_and_entropy_diff :
    covering_number realAbsDist (3 / 2) ex33U ≤ 2 ∧
    2 ≤ covering_number realAbsDist (3 / 2) ex33U ∧
    covering_number realAbsDist (3 / 2) ex33U = 2 ∧
    covering_number realAbsDist (3 / 2) (operator_image ex33Phi ex33U) ≤ 1 ∧
    1 ≤ covering_number realAbsDist (3 / 2) (operator_image ex33Phi ex33U) ∧
    covering_number realAbsDist (3 / 2) (operator_image ex33Phi ex33U) = 1 ∧
    ∃ hwf : MappingEntropyDiffSingleWellDefined realAbsGauge ex33Phi ex33U () (3 / 2),
      mappingEntropyDiffSingle realAbsGauge ex33Phi ex33U () (3 / 2) hwf = 1 := by
  classical
  have hε_pos : (0 : ENNReal) < 3 / 2 := by rw [ennreal_three_halves]; norm_num
  have hε_top : (3 / 2 : ENNReal) < ⊤ := by rw [ennreal_three_halves]; exact ENNReal.ofReal_lt_top
  have hlt0_32 : ENNReal.ofReal 0 < (3 / 2 : ENNReal) := by simp [hε_pos]
  have hlt1_32 : ENNReal.ofReal 1 < (3 / 2 : ENNReal) := by
    rw [ennreal_three_halves]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hnlt2_32 : ¬ (ENNReal.ofReal 2 < (3 / 2 : ENNReal)) := by
    rw [ennreal_three_halves, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  have hnlt3_32 : ¬ (ENNReal.ofReal 3 < (3 / 2 : ENNReal)) := by
    rw [ennreal_three_halves, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  -- 上界：`{.val 0, .val 2}` 构成 `ex33U` 的 `3/2`-内覆盖
  have hin_le : covering_number realAbsDist (3 / 2) ex33U ≤ 2 := by
    let S : Finset RealWithBot := {.val 0, .val 2}
    have hnet : InternalEpsilonNet realAbsDist (3 / 2) ex33U S := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx2
        · exact (mem_ex33U_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))
        · rw [Finset.mem_singleton.mp hx2]
          exact (mem_ex33U_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))
      · rcases (mem_ex33U_iff x).mp hx with rfl | rfl | rfl | rfl
        · refine ⟨.val 2, by simp [S], ?_⟩
          rw [realAbsDist_val]
          have h1 : |(|(-3 : ℝ)| - |2|)| = 1 := by norm_num
          rw [h1]; exact hlt1_32
        · refine ⟨.val 2, by simp [S], ?_⟩
          rw [realAbsDist_val]
          have h0 : |(|(-2 : ℝ)| - |2|)| = 0 := by norm_num
          rw [h0]; exact hlt0_32
        · refine ⟨.val 0, by simp [S], ?_⟩
          rw [realAbsDist_val]
          have h0 : |(|(0 : ℝ)| - |0|)| = 0 := by norm_num
          rw [h0]; exact hlt0_32
        · refine ⟨.val 2, by simp [S], ?_⟩
          rw [realAbsDist_val]
          have h0 : |(|(2 : ℝ)| - |2|)| = 0 := by norm_num
          rw [h0]; exact hlt0_32
    have hcard : (S.card : ENNReal) ≤ 2 := by
      have hc : S.card = 2 := by
        rw [Finset.card_pair]
        intro heq; have h := RealWithBot.val.inj heq; norm_num at h
      simp [hc]
    exact le_trans (iInf_le_of_le S (iInf_le_of_le hnet le_rfl)) hcard
  -- 下界：覆盖 `.val 0` 与 `.val 2` 需要不同内部中心
  have hin_ge : 2 ≤ covering_number realAbsDist (3 / 2) ex33U := by
    apply le_iInf₂
    intro S hS
    rcases hS.2 (.val 0) ((mem_ex33U_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))) with ⟨c0, hc0S, hd0⟩
    rcases hS.2 (.val 2) ((mem_ex33U_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))) with ⟨c2, hc2S, hd2⟩
    have hc0_eq : c0 = .val 0 := by
      rcases (mem_ex33U_iff c0).mp (hS.1 hc0S) with rfl | rfl | rfl | rfl
      · exfalso; rw [realAbsDist_val] at hd0
        have h3 : |(|(0 : ℝ)| - |-3|)| = 3 := by norm_num
        rw [h3] at hd0; exact hnlt3_32 hd0
      · exfalso; rw [realAbsDist_val] at hd0
        have h2 : |(|(0 : ℝ)| - |-2|)| = 2 := by norm_num
        rw [h2] at hd0; exact hnlt2_32 hd0
      · rfl
      · exfalso; rw [realAbsDist_val] at hd0
        have h2 : |(|(0 : ℝ)| - |2|)| = 2 := by norm_num
        rw [h2] at hd0; exact hnlt2_32 hd0
    have hc2_ne0 : c2 ≠ .val 0 := by
      rintro rfl
      rw [realAbsDist_val] at hd2
      have h2 : |(|(2 : ℝ)| - |0|)| = 2 := by norm_num
      rw [h2] at hd2; exact hnlt2_32 hd2
    have hne : c0 ≠ c2 := by rw [hc0_eq]; exact Ne.symm hc2_ne0
    have h2le : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨c0, hc0S, c2, hc2S, hne⟩
    exact_mod_cast h2le
  have hin_eq : covering_number realAbsDist (3 / 2) ex33U = 2 := le_antisymm hin_le hin_ge
  -- 像集上界：单中心 `{ex33Phi(.val (-3))} = {.val (-2)}` 覆盖整个 `ϕ(U)`
  have hout_le : covering_number realAbsDist (3 / 2) (operator_image ex33Phi ex33U) ≤ 1 := by
    let c : RealWithBot := ex33Phi.func (.val (-3))
    have hc_mem : c ∈ operator_image ex33Phi ex33U :=
      ⟨.val (-3), (mem_ex33U_iff _).mpr (Or.inl rfl), rfl⟩
    have hnet : InternalEpsilonNet realAbsDist (3 / 2) (operator_image ex33Phi ex33U) {c} := by
      refine ⟨fun z hz => ?_, ?_⟩
      · rw [Finset.coe_singleton, Set.mem_singleton_iff] at hz
        rw [hz]; exact hc_mem
      · rintro _ ⟨x, hxU, rfl⟩
        refine ⟨c, Finset.mem_singleton_self _, ?_⟩
        rcases (mem_ex33U_iff x).mp hxU with rfl | rfl | rfl | rfl
        · dsimp [c]
          have h0 : |(|(-3 + 1 : ℝ)| - |-3 + 1|)| = 0 := by norm_num
          rw [h0]; exact hlt0_32
        · dsimp [c]
          have h1 : |(|(-2 + 1 : ℝ)| - |-3 + 1|)| = 1 := by norm_num
          rw [h1]; exact hlt1_32
        · dsimp [c]
          have h1 : |(|(0 + 1 : ℝ)| - |-3 + 1|)| = 1 := by norm_num
          rw [h1]; exact hlt1_32
        · dsimp [c]
          have h1 : |(|(2 + 1 : ℝ)| - |-3 + 1|)| = 1 := by norm_num
          rw [h1]; exact hlt1_32
    exact le_trans (iInf_le_of_le {c} (iInf_le_of_le hnet le_rfl)) (by simp)
  have hout_ge : 1 ≤ covering_number realAbsDist (3 / 2) (operator_image ex33Phi ex33U) :=
    one_le_covering_number_of_nonempty realAbsDist (3 / 2) (operator_image ex33Phi ex33U)
      ⟨ex33Phi.func (.val 0), .val 0, (mem_ex33U_iff _).mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  have hout_eq : covering_number realAbsDist (3 / 2) (operator_image ex33Phi ex33U) = 1 :=
    le_antisymm hout_le hout_ge
  have hwf : MappingEntropyDiffSingleWellDefined realAbsGauge ex33Phi ex33U () (3 / 2) := by
    refine ⟨⟨.val 0, (mem_ex33U_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩,
      ex_3_3_i_fiber_partitions.2.2.1,
      Set.singleton_nonempty (), Set.singleton_nonempty (),
      hε_pos, hε_top, Or.inl ?_⟩
    rw [subfamily_covering_number_singleton, realAbsGauge, hin_eq]
    exact ENNReal.ofNat_lt_top
  refine ⟨hin_le, hin_ge, hin_eq, hout_le, hout_ge, hout_eq, hwf, ?_⟩
  unfold mappingEntropyDiffSingle
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
      subfamily_metric_entropy_singleton]
  change metric_entropy realAbsDist (3 / 2) ex33U -
      metric_entropy realAbsDist (3 / 2) (operator_image ex33Phi ex33U) = 1
  unfold metric_entropy log2_ereal
  rw [hin_eq, hout_eq]
  have h2_ne0 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2_netop : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  have h1_ne0 : (1 : ENNReal) ≠ 0 := one_ne_zero
  have h1_netop : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
  simp [h2_ne0, h2_netop, h1_ne0, h1_netop]
 
end Ch03
