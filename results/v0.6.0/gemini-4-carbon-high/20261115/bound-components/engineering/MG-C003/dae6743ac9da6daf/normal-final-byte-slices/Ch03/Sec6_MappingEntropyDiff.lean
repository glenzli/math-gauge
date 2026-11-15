import Ch03.Defs
import Ch03.Sec1_ComponentPartition

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset

/-!
# § 3.6 映射熵差 (`CH03-P22-01` – `CH03-P25-02`)
-/

/-- 辅助引理：当 `1 ≤ N < ⊤` 时，`log2_ereal N` 为非负有限实数 `↑(Real.logb 2 N.toReal)`。 -/
private theorem log2_ereal_eq_coe_of_one_le_lt_top {N : ENNReal}
    (h1 : 1 ≤ N) (hfin : N < ⊤) :
    log2_ereal N = ((Real.logb 2 N.toReal : ℝ) : EReal) ∧
    0 ≤ Real.logb 2 N.toReal := by
  have hne0 : N ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  have hnetop : N ≠ ⊤ := ne_of_lt hfin
  refine ⟨by simp [log2_ereal, hne0, hnetop], ?_⟩
  apply Real.logb_nonneg one_lt_two
  simpa using ENNReal.toReal_mono hnetop h1

/-! ## 注：有限集上映射熵差的良定性 (`CH03-P22-01`) -/

/-- 非空有限集在任意自距为零的伪度量与有限正精度下，覆盖数正且有限（不超过集合自身基数）。 -/
theorem covering_number_pos_and_le_card_of_finite {X : Type}
    (d : X → X → ENNReal) (dist_self : ∀ x : X, d x x = 0)
    (ε : ENNReal) (hε_pos : 0 < ε)
    (S : Set X) (hS_ne : S.Nonempty) (hS_fin : S.Finite) :
    1 ≤ covering_number d ε S ∧
    covering_number d ε S ≤ (hS_fin.toFinset.card : ENNReal) ∧
    covering_number d ε S < ⊤ := by
  have hnet : InternalEpsilonNet d ε S hS_fin.toFinset := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hS_fin.mem_toFinset.mp hx
    · intro x hx
      refine ⟨x, hS_fin.mem_toFinset.mpr hx, ?_⟩
      rw [dist_self x]
      exact hε_pos
  have hle : covering_number d ε S ≤ (hS_fin.toFinset.card : ENNReal) :=
    iInf_le_of_le hS_fin.toFinset (iInf_le_of_le hnet le_rfl)
  exact ⟨one_le_covering_number_of_nonempty d ε S hS_ne, hle,
    lt_of_le_of_lt hle (ENNReal.natCast_lt_top _)⟩

/-- `CH03-P22-01`：注（有限集上映射熵差的良定性）— 若 `∅ ≠ U ⊆ dom(ϕ)` 为有限集，则对任意非空子族 `J_in, J_out ⊆ I` 与有限正精度 `ε`，输入与像集覆盖数均正且有限，两端度量熵均为有限非负实数，映射熵差良定且为有限实数。 -/
theorem remark_finite_set_mappingEntropyDiff_wellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X)
    (J_in J_out : Set I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU_fin : U.Finite) (hU_dom : U ⊆ dom ϕ)
    (hJin : J_in.Nonempty) (hJout : J_out.Nonempty)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) :
    1 ≤ subfamilyCoveringNumber d J_in ε U ∧
    subfamilyCoveringNumber d J_in ε U ≤ (hU_fin.toFinset.card : ENNReal) ∧
    subfamilyCoveringNumber d J_in ε U < ⊤ ∧
    1 ≤ subfamilyCoveringNumber d J_out ε (operator_image ϕ U) ∧
    subfamilyCoveringNumber d J_out ε (operator_image ϕ U) < ⊤ ∧
    ∃ (hdef : MappingEntropyDiffDefined d ϕ U J_in J_out ε) (rin rout : ℝ),
      0 ≤ rin ∧ 0 ≤ rout ∧
      subfamily_metric_entropy d J_in ε U = (rin : EReal) ∧
      subfamily_metric_entropy d J_out ε (operator_image ϕ U) = (rout : EReal) ∧
      mappingEntropyDiff d ϕ U J_in J_out ε hdef = ((rin - rout : ℝ) : EReal) := by
  have hd_in := subfamily_pseudometric_is_extended d J_in hJin hd
  have hd_out := subfamily_pseudometric_is_extended d J_out hJout hd
  obtain ⟨hin_ge1, hin_le, hin_fin⟩ :=
    covering_number_pos_and_le_card_of_finite
      (subfamily_pseudometric d J_in) hd_in.dist_self ε hε_pos U hU_ne hU_fin
  have himg_ne : (operator_image ϕ U).Nonempty := hU_ne.image ϕ.func
  have himg_fin : (operator_image ϕ U).Finite := hU_fin.image ϕ.func
  obtain ⟨hout_ge1, _, hout_fin⟩ :=
    covering_number_pos_and_le_card_of_finite
      (subfamily_pseudometric d J_out) hd_out.dist_self ε hε_pos
      (operator_image ϕ U) himg_ne himg_fin
  have hdef : MappingEntropyDiffDefined d ϕ U J_in J_out ε :=
    ⟨hU_ne, hU_dom, hJin, hJout, hε_pos, hε_fin, Or.inl hin_fin⟩
  obtain ⟨hein, hrin_nn⟩ := log2_ereal_eq_coe_of_one_le_lt_top hin_ge1 hin_fin
  obtain ⟨heout, hrout_nn⟩ := log2_ereal_eq_coe_of_one_le_lt_top hout_ge1 hout_fin
  refine ⟨hin_ge1, hin_le, hin_fin, hout_ge1, hout_fin, hdef,
    Real.logb 2 (subfamilyCoveringNumber d J_in ε U).toReal,
    Real.logb 2 (subfamilyCoveringNumber d J_out ε (operator_image ϕ U)).toReal,
    hrin_nn, hrout_nn, hein, heout, ?_⟩
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy, subfamily_metric_entropy]
  unfold subfamilyCoveringNumber
  rw [hein, heout, ← EReal.coe_sub]

/-! ## 命题 3.18：分量分划与映射熵差 (`CH03-P23-01` – `CH03-P23-03`) -/

/-- `CH03-P23-01`：命题 3.18(i) — 常值分量下像集覆盖数为 `1`、输出熵为 `0`、映射熵差恒良定（允许输入熵为 `+∞`）且等于输入熵 `E_{ε, j}(U)`。 -/
theorem prop_3_18_const_component {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (j : I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hj : j ∈ constComponents d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) = 1 ∧
    metric_entropy (d j) ε (operator_image ϕ U) = 0 ∧
    ∃ hdef : MappingEntropyDiffSingleDefined d ϕ U j ε,
      mappingEntropyDiffSingle d ϕ U j ε hdef = metric_entropy (d j) ε U := by
  classical
  rcases hU_ne with ⟨x₀, hx₀⟩
  have hcov1 : covering_number (d j) ε (operator_image ϕ U) = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (d j) ε (operator_image ϕ U) {ϕ.func x₀} := by
        refine ⟨?_, ?_⟩
        · intro z hz
          rw [Finset.mem_coe, Finset.mem_singleton] at hz
          rw [hz]
          exact ⟨x₀, hx₀, rfl⟩
        · rintro z ⟨x, hxU, rfl⟩
          refine ⟨ϕ.func x₀, Finset.mem_singleton_self _, ?_⟩
          rw [hj x hxU x₀ hx₀]
          exact hε_pos
      exact le_trans
        (iInf_le_of_le {ϕ.func x₀} (iInf_le_of_le hnet le_rfl))
        (by simp)
    · exact one_le_covering_number_of_nonempty (d j) ε (operator_image ϕ U)
        ⟨ϕ.func x₀, ⟨x₀, hx₀, rfl⟩⟩
  have hent0 : metric_entropy (d j) ε (operator_image ϕ U) = 0 := by
    simp [metric_entropy, hcov1, log2_ereal]
  have hout_fin : subfamilyCoveringNumber d ({j} : Set I) ε (operator_image ϕ U) < ⊤ := by
    rw [subfamilyCoveringNumber_singleton, hcov1]
    exact ENNReal.one_lt_top
  have hdef : MappingEntropyDiffSingleDefined d ϕ U j ε :=
    ⟨⟨x₀, hx₀⟩, hU_dom, Set.singleton_nonempty j, Set.singleton_nonempty j,
      hε_pos, hε_fin, Or.inr hout_fin⟩
  refine ⟨hcov1, hent0, hdef, ?_⟩
  unfold mappingEntropyDiffSingle
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
    subfamily_metric_entropy_singleton, hent0, sub_zero]

/-- `CH03-P23-02`：命题 3.18(ii-a) — 恒等分量下通过前向推中心与反向选原像代表元双向不等式，证明输入与像集的覆盖数相等且度量熵相等。 -/
theorem prop_3_18_id_covering_and_entropy_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (j : I) (ε : ENNReal)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hj : j ∈ idComponents d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) ≤ covering_number (d j) ε U ∧
    covering_number (d j) ε U ≤ covering_number (d j) ε (operator_image ϕ U) ∧
    covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (operator_image ϕ U) = metric_entropy (d j) ε U := by
  classical
  have _ := hU_ne
  have _ := hε_pos
  have _ := hε_fin
  have hiso := prop_3_1_id_preserves_dist d ϕ U j hdj hU_dom hj
  -- 前向：将 U 的内部中心集 S 推为 ϕ(S)
  have hfwd : covering_number (d j) ε (operator_image ϕ U) ≤ covering_number (d j) ε U := by
    apply le_iInf₂
    intro S hS
    have hnet_out : InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) := by
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
        exact ⟨s, hS.1 hs, rfl⟩
      · rintro z ⟨x, hxU, rfl⟩
        rcases hS.2 x hxU with ⟨s, hsS, hd_xs⟩
        refine ⟨ϕ.func s, Finset.mem_image_of_mem ϕ.func hsS, ?_⟩
        rw [hiso x hxU s (hS.1 hsS)]
        exact hd_xs
    calc
      covering_number (d j) ε (operator_image ϕ U)
          ≤ ((S.image ϕ.func).card : ENNReal) :=
            iInf_le_of_le (S.image ϕ.func) (iInf_le_of_le hnet_out le_rfl)
      _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
  -- 反向：对 ϕ(U) 的每个内部中心 t ∈ T 选取原像代表元 s_t ∈ U
  have hrev : covering_number (d j) ε U ≤ covering_number (d j) ε (operator_image ϕ U) := by
    apply le_iInf₂
    intro T hT
    let rep : { t // t ∈ T } → X := fun t => Classical.choose (hT.1 t.2)
    have hrep_spec : ∀ t : { t // t ∈ T }, rep t ∈ U ∧ ϕ.func (rep t) = t.1 :=
      fun t => Classical.choose_spec (hT.1 t.2)
    let S : Finset X := Finset.univ.image rep
    have hnet_in : InternalEpsilonNet (d j) ε U S := by
      refine ⟨?_, ?_⟩
      · intro s hs
        rcases Finset.mem_image.mp hs with ⟨t, _, rfl⟩
        exact (hrep_spec t).1
      · intro x hxU
        rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, htT, hd_t⟩
        refine ⟨rep ⟨t, htT⟩, Finset.mem_image_of_mem rep (Finset.mem_univ _), ?_⟩
        rw [← hiso x hxU (rep ⟨t, htT⟩) (hrep_spec ⟨t, htT⟩).1, (hrep_spec ⟨t, htT⟩).2]
        exact hd_t
    have hcard : S.card ≤ T.card := by
      calc
        S.card ≤ (Finset.univ : Finset { t // t ∈ T }).card := Finset.card_image_le
        _ = T.card := by simp
    calc
      covering_number (d j) ε U
          ≤ (S.card : ENNReal) := iInf_le_of_le S (iInf_le_of_le hnet_in le_rfl)
      _ ≤ (T.card : ENNReal) := by exact_mod_cast hcard
  have heq : covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U :=
    le_antisymm hfwd hrev
  exact ⟨hfwd, hrev, heq, by simp [metric_entropy, heq]⟩

/-- `CH03-P23-03`：命题 3.18(ii-b) — 在恒等分量下，仅当映射熵差良定（即提供 `hdef : MappingEntropyDiffSingleDefined`，不定义 `+∞ - +∞`）时，推出 `\Delta E_{ε, j}(ϕ | U) = 0`。 -/
theorem prop_3_18_id_mappingEntropyDiff_eq_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (j : I) (ε : ENNReal)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hj : j ∈ idComponents d ϕ U)
    (hdef : MappingEntropyDiffSingleDefined d ϕ U j ε) :
    mappingEntropyDiffSingle d ϕ U j ε hdef = 0 := by
  have heq_cov := (prop_3_18_id_covering_and_entropy_eq d ϕ U j ε hdj
    hdef.1 hdef.2.1 hdef.2.2.2.2.1 hdef.2.2.2.2.2.1 hj).2.2.1
  have hin_fin : covering_number (d j) ε U < ⊤ := by
    rcases hdef.2.2.2.2.2.2 with hin | hout
    · rwa [subfamilyCoveringNumber_singleton] at hin
    · rwa [subfamilyCoveringNumber_singleton, heq_cov] at hout
  have hin_ge1 : 1 ≤ covering_number (d j) ε U :=
    one_le_covering_number_of_nonempty (d j) ε U hdef.1
  obtain ⟨hein, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hin_ge1 hin_fin
  unfold mappingEntropyDiffSingle
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
    subfamily_metric_entropy_singleton]
  unfold metric_entropy
  rw [heq_cov, hein, ← EReal.coe_sub, sub_self]
  rfl

/-! ## 命题 3.19：单通道 Lip 上界与熵差下界 (`CH03-P24-01`, `CH03-P24-02`) -/

/-- `CH03-P24-01`：命题 3.19（覆盖数放缩步）— 有限正标量 Lip 常数 `0 < L < ⊤` 将 `U` 的任意有限 `ε/L`-内覆盖中心集 `S` 前推为 `ϕ(U)` 的有限 `ε`-内覆盖 `ϕ(S)` 且基数不增，从而 `N_j(ε, ϕ(U)) ≤ N_i(ε/L, U)`。 -/
theorem prop_3_19_covering_number_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (ε L : ENNReal)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    (∀ [DecidableEq X] (S : Finset X),
      InternalEpsilonNet (d i) (ε / L) U S →
      InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card) ∧
    covering_number (d j) ε (operator_image ϕ U) ≤ covering_number (d i) (ε / L) U := by
  have _ := hU_ne
  have _ := hU_dom
  have _ := hε_pos
  have _ := hε_fin
  have hL_ne0 : L ≠ 0 := ne_of_gt hL_pos
  have hL_netop : L ≠ ⊤ := ne_of_lt hL_fin
  have hpush : ∀ [DecidableEq X] (S : Finset X),
      InternalEpsilonNet (d i) (ε / L) U S →
      InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card := by
    intro _ S hS
    refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro z ⟨x, hxU, rfl⟩
      rcases hS.2 x hxU with ⟨c, hcS, hd_xc⟩
      refine ⟨ϕ.func c, Finset.mem_image_of_mem ϕ.func hcS, ?_⟩
      have hmul_lt : L * d i x c < L * (ε / L) := by
        rw [mul_comm L (d i x c), mul_comm L (ε / L)]
        exact ENNReal.mul_lt_mul_left hL_ne0 hL_netop hd_xc
      have hcancel : L * (ε / L) = ε := by
        calc
          L * (ε / L) = ε * (L * L⁻¹) := by
            simp only [div_eq_mul_inv]
            ac_rfl
          _ = ε := by rw [ENNReal.mul_inv_cancel hL_ne0 hL_netop, mul_one]
      calc
        d j (ϕ.func x) (ϕ.func c)
            ≤ L * d i x c := hLip x hxU c (hS.1 hcS)
        _ < L * (ε / L) := hmul_lt
        _ = ε := hcancel
  refine ⟨hpush, ?_⟩
  classical
  apply le_iInf₂
  intro S hS
  obtain ⟨hnet_out, hcard_le⟩ := hpush S hS
  calc
    covering_number (d j) ε (operator_image ϕ U)
        ≤ ((S.image ϕ.func).card : ENNReal) :=
          iInf_le_of_le (S.image ϕ.func) (iInf_le_of_le hnet_out le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast hcard_le

/-- `CH03-P24-02`：命题 3.19（熵差良定性与下界）— 当 `U` 在 `d_i` 下全有界且满足单通道有限正 Lip 上界时，映射熵差良定且满足
`\Delta E_{ε, i, j}(ϕ | U) ≥ E_{ε, i}(U) - E_{ε/L, i}(U)`。 -/
theorem prop_3_19_mappingEntropyDiff_lower_bound {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (ε L : ENNReal)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (htb : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    ∃ hdef : MappingEntropyDiffCompDefined d ϕ U i j ε,
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        mappingEntropyDiffComp d ϕ U i j ε hdef := by
  have hcov_le := (prop_3_19_covering_number_le d ϕ U i j ε L
    hU_ne hU_dom hε_pos hε_fin hL_pos hL_fin hLip).2
  have hdiv_pos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hL_fin)
  have hdiv_fin : ε / L < ⊤ :=
    ENNReal.mul_lt_top hε_fin (ENNReal.inv_lt_top.mpr hL_pos)
  have hin_fin : covering_number (d i) ε U < ⊤ := htb ε hε_pos hε_fin
  have hinL_fin : covering_number (d i) (ε / L) U < ⊤ := htb (ε / L) hdiv_pos hdiv_fin
  have hout_fin : covering_number (d j) ε (operator_image ϕ U) < ⊤ :=
    lt_of_le_of_lt hcov_le hinL_fin
  have hin_sub_fin : subfamilyCoveringNumber d ({i} : Set I) ε U < ⊤ := by
    rwa [subfamilyCoveringNumber_singleton]
  have hdef : MappingEntropyDiffCompDefined d ϕ U i j ε :=
    ⟨hU_ne, hU_dom, Set.singleton_nonempty i, Set.singleton_nonempty j,
      hε_pos, hε_fin, Or.inl hin_sub_fin⟩
  refine ⟨hdef, ?_⟩
  have hin_ge1 := one_le_covering_number_of_nonempty (d i) ε U hU_ne
  have hinL_ge1 := one_le_covering_number_of_nonempty (d i) (ε / L) U hU_ne
  have hout_ge1 := one_le_covering_number_of_nonempty (d j) ε (operator_image ϕ U)
    (hU_ne.image ϕ.func)
  obtain ⟨he_in, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hin_ge1 hin_fin
  obtain ⟨he_inL, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hinL_ge1 hinL_fin
  obtain ⟨he_out, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hout_ge1 hout_fin
  have hent_le : metric_entropy (d j) ε (operator_image ϕ U) ≤ metric_entropy (d i) (ε / L) U :=
    log2_ereal_mono hcov_le
  unfold mappingEntropyDiffComp
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
    subfamily_metric_entropy_singleton]
  unfold metric_entropy at hent_le ⊢
  rw [he_inL, he_out] at hent_le
  rw [he_in, he_inL, he_out, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have hreal_le :
      Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal ≤
        Real.logb 2 (covering_number (d i) (ε / L) U).toReal :=
    EReal.coe_le_coe_iff.mp hent_le
  linarith

/-! ## 命题 3.20：co-Lip 常数与熵差上界 (`CH03-P25-01`, `CH03-P25-02`) -/

/-- `CH03-P25-01`：命题 3.20（原像拉回与覆盖数下界）— 有限正 co-Lip 单条目 `0 < K_{i→j} < ⊤` 将像集 `ϕ(U)` 的任意有限 `ε`-内覆盖 `T` 拉回为 `U` 的有限 `ε / K_{i→j}`-内覆盖 `S` 且 `|S| ≤ |T|`，从而 `N_i(ε / K_{i→j}, U) ≤ N_j(ε, ϕ(U))`。 -/
theorem prop_3_20_covering_number_ge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (K : I → I → ENNReal) (i j : I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    (∀ [DecidableEq X] (T : Finset X),
      InternalEpsilonNet (d j) ε (operator_image ϕ U) T →
      ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card) ∧
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (operator_image ϕ U) := by
  have _ := hU_ne
  have _ := hU_dom
  have _ := hε_pos
  have _ := hε_fin
  have hK_ne0 : K i j ≠ 0 := ne_of_gt hK_pos
  have hK_netop : K i j ≠ ⊤ := ne_of_lt hK_fin
  have hpull : ∀ [DecidableEq X] (T : Finset X),
      InternalEpsilonNet (d j) ε (operator_image ϕ U) T →
      ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
    intro _ T hT
    let rep : { t // t ∈ T } → X := fun t => Classical.choose (hT.1 t.2)
    have hrep_spec : ∀ t : { t // t ∈ T }, rep t ∈ U ∧ ϕ.func (rep t) = t.1 :=
      fun t => Classical.choose_spec (hT.1 t.2)
    let S : Finset X := Finset.univ.image rep
    have hcard : S.card ≤ T.card := by
      calc
        S.card ≤ (Finset.univ : Finset { t // t ∈ T }).card := Finset.card_image_le
        _ = T.card := by simp
    refine ⟨S, ⟨?_, ?_⟩, hcard⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨t, _, rfl⟩
      exact (hrep_spec t).1
    · intro x hxU
      rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, htT, hd_xt⟩
      let ct := rep ⟨t, htT⟩
      have hct_U : ct ∈ U := (hrep_spec ⟨t, htT⟩).1
      have hct_eq : ϕ.func ct = t := (hrep_spec ⟨t, htT⟩).2
      refine ⟨ct, Finset.mem_image_of_mem rep (Finset.mem_univ _), ?_⟩
      have hsingle : K i j * d i x ct ≤ ∑ k : I, K k j * d k x ct :=
        Finset.single_le_sum (f := fun k : I => K k j * d k x ct)
          (fun _ _ => zero_le _) (Finset.mem_univ i)
      have hsum_le : ∑ k : I, K k j * d k x ct ≤ d j (ϕ.func x) t := by
        rw [← hct_eq]
        exact hK.2.2 x hxU ct hct_U j
      have hprod_lt : K i j * d i x ct < ε :=
        lt_of_le_of_lt (le_trans hsingle hsum_le) hd_xt
      by_contra hnot_lt
      have hge : ε / K i j ≤ d i x ct := le_of_not_gt hnot_lt
      have hmul_ge : K i j * (ε / K i j) ≤ K i j * d i x ct :=
        mul_le_mul_of_nonneg_left hge (zero_le _)
      have hcancel : K i j * (ε / K i j) = ε := by
        calc
          K i j * (ε / K i j) = ε * (K i j * (K i j)⁻¹) := by
            simp only [div_eq_mul_inv]
            ac_rfl
          _ = ε := by rw [ENNReal.mul_inv_cancel hK_ne0 hK_netop, mul_one]
      rw [hcancel] at hmul_ge
      exact (not_lt_of_ge hmul_ge) hprod_lt
  refine ⟨hpull, ?_⟩
  classical
  apply le_iInf₂
  intro T hT
  obtain ⟨S, hS_net, hcard_le⟩ := hpull T hT
  calc
    covering_number (d i) (ε / K i j) U
        ≤ (S.card : ENNReal) := iInf_le_of_le S (iInf_le_of_le hS_net le_rfl)
    _ ≤ (T.card : ENNReal) := by exact_mod_cast hcard_le

/-- `CH03-P25-02`：命题 3.20（良定性与熵差上界，允许输出熵无穷）— 当 `U` 在 `d_i` 下全有界且存在满足 `0 < K_{i→j} < ⊤` 的受限 co-Lip 矩阵时，即使输出熵为 `+∞`，映射熵差仍良定且满足
`\Delta E_{ε, i, j}(ϕ | U) ≤ E_{ε, i}(U) - E_{ε / K_{i→j}, i}(U)`。 -/
theorem prop_3_20_mappingEntropyDiff_upper_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (K : I → I → ENNReal) (i j : I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU_dom : U ⊆ dom ϕ)
    (htb : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    ∃ hdef : MappingEntropyDiffCompDefined d ϕ U i j ε,
      mappingEntropyDiffComp d ϕ U i j ε hdef ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hcov_ge := (prop_3_20_covering_number_ge d ϕ U K i j ε
    hU_ne hU_dom hε_pos hε_fin hK hK_pos hK_fin).2
  have hdiv_pos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hK_fin)
  have hdiv_fin : ε / K i j < ⊤ :=
    ENNReal.mul_lt_top hε_fin (ENNReal.inv_lt_top.mpr hK_pos)
  have hin_fin : covering_number (d i) ε U < ⊤ := htb ε hε_pos hε_fin
  have hinK_fin : covering_number (d i) (ε / K i j) U < ⊤ := htb (ε / K i j) hdiv_pos hdiv_fin
  have hin_sub_fin : subfamilyCoveringNumber d ({i} : Set I) ε U < ⊤ := by
    rwa [subfamilyCoveringNumber_singleton]
  have hdef : MappingEntropyDiffCompDefined d ϕ U i j ε :=
    ⟨hU_ne, hU_dom, Set.singleton_nonempty i, Set.singleton_nonempty j,
      hε_pos, hε_fin, Or.inl hin_sub_fin⟩
  refine ⟨hdef, ?_⟩
  have hin_ge1 := one_le_covering_number_of_nonempty (d i) ε U hU_ne
  have hinK_ge1 := one_le_covering_number_of_nonempty (d i) (ε / K i j) U hU_ne
  obtain ⟨he_in, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hin_ge1 hin_fin
  obtain ⟨he_inK, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hinK_ge1 hinK_fin
  unfold mappingEntropyDiffComp
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
    subfamily_metric_entropy_singleton]
  by_cases hout_fin : covering_number (d j) ε (operator_image ϕ U) < ⊤
  · have hout_ge1 := one_le_covering_number_of_nonempty (d j) ε (operator_image ϕ U)
      (hU_ne.image ϕ.func)
    obtain ⟨he_out, _⟩ := log2_ereal_eq_coe_of_one_le_lt_top hout_ge1 hout_fin
    have hent_ge : metric_entropy (d i) (ε / K i j) U ≤
        metric_entropy (d j) ε (operator_image ϕ U) := log2_ereal_mono hcov_ge
    unfold metric_entropy at hent_ge ⊢
    rw [he_inK, he_out] at hent_ge
    rw [he_in, he_inK, he_out, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have hreal_ge :
        Real.logb 2 (covering_number (d i) (ε / K i j) U).toReal ≤
          Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal :=
      EReal.coe_le_coe_iff.mp hent_ge
    linarith
  · have hout_top : covering_number (d j) ε (operator_image ϕ U) = ⊤ :=
      not_lt_top_iff.mp hout_fin
    have he_out_top : log2_ereal (covering_number (d j) ε (operator_image ϕ U)) = ⊤ := by
      simp [hout_top, log2_ereal]
    unfold metric_entropy
    rw [he_in, he_inK, he_out_top, ← EReal.coe_sub]
    have hbot : ((Real.logb 2 (covering_number (d i) ε U).toReal : ℝ) : EReal) - ⊤ = ⊥ := rfl
    rw [hbot]
    exact bot_le

end Ch03
