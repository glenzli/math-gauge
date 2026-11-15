import Ch03.Sec04_05
import Mathlib.Data.Set.Card
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset
 
/-! ### 3.6 映射熵差：有限集良定性注记与命题 3.18、3.19、3.20 (CH03-P22-01 .. CH03-P25-02) -/
 
/-- 非空有限集以自身为内覆盖中心集时，覆盖数正且有限（不超过基数）。 -/
theorem covering_number_le_toFinset_card {X : Type} (d : X → X → ENNReal)
    (hself : ∀ x : X, d x x = 0)
    (U : Set X) (hU_fin : U.Finite) {ε : ENNReal} (hε0 : 0 < ε) :
    covering_number d ε U ≤ (hU_fin.toFinset.card : ENNReal) ∧
    covering_number d ε U < ⊤ := by
  have hnet : InternalEpsilonNet d ε U hU_fin.toFinset := by
    refine ⟨by simp, fun x hx => ⟨x, hU_fin.mem_toFinset.mpr hx, ?_⟩⟩
    rw [hself x]
    exact hε0
  have hle : covering_number d ε U ≤ (hU_fin.toFinset.card : ENNReal) :=
    iInf_le_of_le hU_fin.toFinset (iInf_le_of_le hnet le_rfl)
  exact ⟨hle, lt_of_le_of_lt hle (ENNReal.natCast_lt_top _)⟩
 
/-- CH03-P22-01: 注（有限集上映射熵差的良定性）：非空有限 `U` 及任意两端非空子族的覆盖数正有限、熵为有限实数、熵差良定。 -/
theorem note_finite_set_mapping_entropy_diff_well_defined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (hU_fin : U.Finite)
    (hJin : Jin.Nonempty) (hJout : Jout.Nonempty)
    (hε0 : 0 < ε) (hεtop : ε < ⊤) :
    1 ≤ subfamily_covering_number d Jin ε U ∧
    subfamily_covering_number d Jin ε U ≤ (hU_fin.toFinset.card : ENNReal) ∧
    subfamily_covering_number d Jin ε U < ⊤ ∧
    1 ≤ subfamily_covering_number d Jout ε (operator_image ϕ U) ∧
    subfamily_covering_number d Jout ε (operator_image ϕ U) < ⊤ ∧
    (∃ rin : ℝ, 0 ≤ rin ∧ subfamily_metric_entropy d Jin ε U = (rin : EReal)) ∧
    (∃ rout : ℝ, 0 ≤ rout ∧
      subfamily_metric_entropy d Jout ε (operator_image ϕ U) = (rout : EReal)) ∧
    ∃ hwf : MappingEntropyDiffWellDefined d ϕ U Jin Jout ε,
      ∃ δ : ℝ, mappingEntropyDiff d ϕ U Jin Jout ε hwf = (δ : EReal) := by
  have hd_in := subfamily_pseudometric_is_extended d Jin hJin hd
  have hd_out := subfamily_pseudometric_is_extended d Jout hJout hd
  have hIm_ne : (operator_image ϕ U).Nonempty := hU_ne.image ϕ.func
  have hIm_fin : (operator_image ϕ U).Finite := hU_fin.image ϕ.func
  have h1_in := one_le_covering_number_of_nonempty (subfamily_pseudometric d Jin) ε U hU_ne
  rcases covering_number_le_toFinset_card (subfamily_pseudometric d Jin) hd_in.dist_self
      U hU_fin hε0 with ⟨hle_in, hlt_in⟩
  have h1_out := one_le_covering_number_of_nonempty (subfamily_pseudometric d Jout)
    ε (operator_image ϕ U) hIm_ne
  rcases covering_number_le_toFinset_card (subfamily_pseudometric d Jout) hd_out.dist_self
      (operator_image ϕ U) hIm_fin hε0 with ⟨_, hlt_out⟩
  have hin0 : covering_number (subfamily_pseudometric d Jin) ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one h1_in)
  have hout0 : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one h1_out)
  have hintop : covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤ :=
    lt_top_iff_ne_top.mp hlt_in
  have houttop : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) ≠ ⊤ :=
    lt_top_iff_ne_top.mp hlt_out
  have hwf : MappingEntropyDiffWellDefined d ϕ U Jin Jout ε :=
    ⟨hU_ne, hU, hJin, hJout, hε0, hεtop, Or.inl hlt_in⟩
  refine ⟨h1_in, hle_in, hlt_in, h1_out, hlt_out, ?_, ?_, hwf, ?_⟩
  · refine ⟨Real.logb 2 (covering_number (subfamily_pseudometric d Jin) ε U).toReal, ?_, ?_⟩
    · apply Real.logb_nonneg one_lt_two
      simpa using ENNReal.toReal_mono hintop h1_in
    · simp [subfamily_metric_entropy, log2_ereal, hin0, hintop]
  · refine ⟨Real.logb 2 (covering_number (subfamily_pseudometric d Jout)
        ε (operator_image ϕ U)).toReal, ?_, ?_⟩
    · apply Real.logb_nonneg one_lt_two
      simpa using ENNReal.toReal_mono houttop h1_out
    · simp [subfamily_metric_entropy, log2_ereal, hout0, houttop]
  · refine ⟨Real.logb 2 (covering_number (subfamily_pseudometric d Jin) ε U).toReal -
      Real.logb 2 (covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U)).toReal, ?_⟩
    unfold mappingEntropyDiff subfamily_covering_number
    simp [hlt_in, hlt_out]
 
/-! ### 命题 3.18：分量分划与映射熵差 (CH03-P23-01 .. 03) -/
 
/-- CH03-P23-01: 命题 3.18(i) 常值分量输出覆盖数为 `1`、熵为 `0`，映射熵差良定且等于输入熵（允许输入熵为 `+∞`）。 -/
theorem prop_3_18_i_const_entropy_diff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (hε0 : 0 < ε) (hεtop : ε < ⊤) (hj : j ∈ I_const d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) = 1 ∧
    metric_entropy (d j) ε (operator_image ϕ U) = 0 ∧
    ∃ hwf : MappingEntropyDiffSingleWellDefined d ϕ U j ε,
      mappingEntropyDiffSingle d ϕ U j ε hwf = metric_entropy (d j) ε U := by
  rcases hU_ne with ⟨u₀, hu₀⟩
  have hcov1 : covering_number (d j) ε (operator_image ϕ U) = 1 := by
    classical
    apply le_antisymm
    · have hnet : InternalEpsilonNet (d j) ε (operator_image ϕ U) {ϕ.func u₀} := by
        refine ⟨fun z hz => ?_, ?_⟩
        · rw [Finset.coe_singleton, Set.mem_singleton_iff] at hz
          rw [hz]
          exact ⟨u₀, hu₀, rfl⟩
        · rintro _ ⟨x, hxU, rfl⟩
          refine ⟨ϕ.func u₀, Finset.mem_singleton_self _, ?_⟩
          rw [hj x hxU u₀ hu₀]
          exact hε0
      exact le_trans (iInf_le_of_le {ϕ.func u₀} (iInf_le_of_le hnet le_rfl)) (by simp)
    · exact one_le_covering_number_of_nonempty (d j) ε (operator_image ϕ U)
        ⟨ϕ.func u₀, u₀, hu₀, rfl⟩
  have hent0 : metric_entropy (d j) ε (operator_image ϕ U) = 0 := by
    unfold metric_entropy log2_ereal
    rw [hcov1]
    simp
  have hwf : MappingEntropyDiffSingleWellDefined d ϕ U j ε := by
    refine ⟨⟨u₀, hu₀⟩, hU, Set.singleton_nonempty j, Set.singleton_nonempty j, hε0, hεtop, Or.inr ?_⟩
    rw [subfamily_covering_number_singleton, hcov1]
    exact ENNReal.one_lt_top
  refine ⟨hcov1, hent0, hwf, ?_⟩
  unfold mappingEntropyDiffSingle
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
      subfamily_metric_entropy_singleton, hent0, sub_zero]
 
/-- CH03-P23-02: 命题 3.18(ii-a) 恒等分量前向推中心与反向选代表元，证明覆盖数与度量熵相等。 -/
theorem prop_3_18_ii_a_id_covering_and_entropy_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (ε : ENNReal)
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (_hε0 : 0 < ε) (_hεtop : ε < ⊤) (hj : j ∈ I_id d ϕ U) :
    (∀ [DecidableEq X] (S : Finset X), InternalEpsilonNet (d j) ε U S →
      InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card) ∧
    (∀ [DecidableEq X] (T : Finset X), InternalEpsilonNet (d j) ε (operator_image ϕ U) T →
      ∃ S : Finset X, InternalEpsilonNet (d j) ε U S ∧ S.card ≤ T.card) ∧
    covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (operator_image ϕ U) = metric_entropy (d j) ε U := by
  have hiso := prop_3_1_iii_id_preserves_dist d hd ϕ U j hU hj
  have hfwd : ∀ [DecidableEq X] (S : Finset X), InternalEpsilonNet (d j) ε U S →
      InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card := by
    intro _ S hS
    refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
    · intro z hz
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨s, hs, rfl⟩
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro _ ⟨x, hxU, rfl⟩
      rcases hS.2 x hxU with ⟨s, hsS, hxs⟩
      refine ⟨ϕ.func s, Finset.mem_image_of_mem ϕ.func hsS, ?_⟩
      rw [hiso x hxU s (hS.1 hsS)]
      exact hxs
  have hbwd : ∀ [DecidableEq X] (T : Finset X), InternalEpsilonNet (d j) ε (operator_image ϕ U) T →
      ∃ S : Finset X, InternalEpsilonNet (d j) ε U S ∧ S.card ≤ T.card := by
    intro _ T hT
    let rep : {t // t ∈ T} → X := fun t => Classical.choose (hT.1 t.2)
    have hrep : ∀ t : {t // t ∈ T}, rep t ∈ U ∧ ϕ.func (rep t) = t.1 :=
      fun t => Classical.choose_spec (hT.1 t.2)
    let S : Finset X := T.attach.image rep
    refine ⟨S, ⟨?_, ?_⟩, ?_⟩
    · intro s hs
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hs) with ⟨t, _, rfl⟩
      exact (hrep t).1
    · intro x hxU
      rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, htT, hxt⟩
      refine ⟨rep ⟨t, htT⟩, Finset.mem_image_of_mem rep (Finset.mem_attach _ ⟨t, htT⟩), ?_⟩
      rw [← hiso x hxU (rep ⟨t, htT⟩) (hrep ⟨t, htT⟩).1, (hrep ⟨t, htT⟩).2]
      exact hxt
    · exact le_trans Finset.card_image_le (by simp)
  have hcov_eq : covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U := by
    classical
    apply le_antisymm
    · apply le_iInf₂
      intro S hS
      rcases hfwd S hS with ⟨hnet_out, hcard⟩
      exact le_trans
        (iInf_le_of_le (S.image ϕ.func) (iInf_le_of_le hnet_out le_rfl))
        (by exact_mod_cast hcard)
    · apply le_iInf₂
      intro T hT
      rcases hbwd T hT with ⟨S, hnet_in, hcard⟩
      exact le_trans
        (iInf_le_of_le S (iInf_le_of_le hnet_in le_rfl))
        (by exact_mod_cast hcard)
  exact ⟨hfwd, hbwd, hcov_eq, by simp [metric_entropy, hcov_eq]⟩
 
/-- CH03-P23-03: 命题 3.18(ii-b) 恒等分量仅在映射熵差良定时推出熵差为 `0`（不定义无穷减无穷）。 -/
theorem prop_3_18_ii_b_id_entropy_diff_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (ε : ENNReal)
    (hj : j ∈ I_id d ϕ U)
    (hwf : MappingEntropyDiffSingleWellDefined d ϕ U j ε) :
    mappingEntropyDiffSingle d ϕ U j ε hwf = 0 := by
  have hcov_eq := (prop_3_18_ii_a_id_covering_and_entropy_eq d hd ϕ U j ε
    hwf.1 hwf.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1 hj).2.2.1
  unfold mappingEntropyDiffSingle mappingEntropyDiff subfamily_covering_number
  simp only [subfamily_pseudometric_singleton]
  have hin_lt : covering_number (d j) ε U < ⊤ := by
    rcases hwf.2.2.2.2.2.2 with hin | hout
    · simpa [subfamily_covering_number_singleton] using hin
    · rw [subfamily_covering_number_singleton, hcov_eq] at hout
      exact hout
  have hout_lt : covering_number (d j) ε (operator_image ϕ U) < ⊤ := by
    rw [hcov_eq]; exact hin_lt
  simp [hin_lt, hcov_eq]
 
/-! ### 命题 3.19：单通道 Lip 上界与熵差下界 (CH03-P24-01 .. 02) -/
 
/-- CH03-P24-01: 命题 3.19 有限正 `L` 将 `ε/L` 内部输入覆盖推到 `ε` 输出覆盖，基数不增，给出覆盖数上界。 -/
theorem prop_3_19_covering_number_upper_bound {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal)
    (_hU_ne : U.Nonempty) (_hU : U ⊆ dom ϕ)
    (_hε0 : 0 < ε) (_hεtop : ε < ⊤)
    (hL0 : 0 < L) (hLtop : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    (∀ [DecidableEq X] (S : Finset X), InternalEpsilonNet (d i) (ε / L) U S →
      InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card) ∧
    covering_number (d j) ε (operator_image ϕ U) ≤ covering_number (d i) (ε / L) U := by
  have hL_ne0 : L ≠ 0 := ne_of_gt hL0
  have hL_netop : L ≠ ⊤ := lt_top_iff_ne_top.mp hLtop
  have hpush : ∀ [DecidableEq X] (S : Finset X), InternalEpsilonNet (d i) (ε / L) U S →
      InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card := by
    intro _ S hS
    refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
    · intro z hz
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨s, hs, rfl⟩
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro _ ⟨x, hxU, rfl⟩
      rcases hS.2 x hxU with ⟨c, hcS, hxc⟩
      refine ⟨ϕ.func c, Finset.mem_image_of_mem ϕ.func hcS, ?_⟩
      calc
        d j (ϕ.func x) (ϕ.func c) ≤ L * d i x c := hLip x hxU c (hS.1 hcS)
        _ = d i x c * L := mul_comm _ _
        _ < (ε / L) * L := ENNReal.mul_lt_mul_left hL_ne0 hL_netop hxc
        _ = ε := ENNReal.div_mul_cancel hL_ne0 hL_netop
  refine ⟨hpush, ?_⟩
  classical
  apply le_iInf₂
  intro S hS
  rcases hpush S hS with ⟨hnet_out, hcard⟩
  exact le_trans
    (iInf_le_of_le (S.image ϕ.func) (iInf_le_of_le hnet_out le_rfl))
    (by exact_mod_cast hcard)
 
/-- CH03-P24-02: 命题 3.19 输入全有界给出两端有限熵、映射熵差良定及熵差下界。 -/
theorem prop_3_19_entropy_diff_lower_bound {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (htb : IsTotallyBounded (d i) U)
    (hε0 : 0 < ε) (hεtop : ε < ⊤)
    (hL0 : 0 < L) (hLtop : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    metric_entropy (d i) ε U < ⊤ ∧
    metric_entropy (d i) (ε / L) U < ⊤ ∧
    metric_entropy (d j) ε (operator_image ϕ U) < ⊤ ∧
    ∃ hwf : MappingEntropyDiffCompWellDefined d ϕ U i j ε,
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        mappingEntropyDiffComp d ϕ U i j ε hwf := by
  have hcov_le := (prop_3_19_covering_number_upper_bound d ϕ U i j ε L
    hU_ne hU hε0 hεtop hL0 hLtop hLip).2
  have hdiv_pos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε0) (lt_top_iff_ne_top.mp hLtop)
  have hdiv_top : ε / L < ⊤ := ENNReal.div_lt_top (lt_top_iff_ne_top.mp hεtop) (ne_of_gt hL0)
  have hin_lt : covering_number (d i) ε U < ⊤ := htb ε hε0 hεtop
  have hdiv_cov_lt : covering_number (d i) (ε / L) U < ⊤ := htb (ε / L) hdiv_pos hdiv_top
  have hout_lt : covering_number (d j) ε (operator_image ϕ U) < ⊤ :=
    lt_of_le_of_lt hcov_le hdiv_cov_lt
  have hwf : MappingEntropyDiffCompWellDefined d ϕ U i j ε := by
    refine ⟨hU_ne, hU, Set.singleton_nonempty i, Set.singleton_nonempty j, hε0, hεtop, Or.inl ?_⟩
    simpa [subfamily_covering_number_singleton] using hin_lt
  have hent_le : metric_entropy (d j) ε (operator_image ϕ U) ≤ metric_entropy (d i) (ε / L) U :=
    log2_ereal_mono hcov_le
  refine ⟨(metric_entropy_lt_top_iff _ _ _).mpr hin_lt,
    (metric_entropy_lt_top_iff _ _ _).mpr hdiv_cov_lt,
    (metric_entropy_lt_top_iff _ _ _).mpr hout_lt, hwf, ?_⟩
  unfold mappingEntropyDiffComp
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
      subfamily_metric_entropy_singleton]
  exact EReal.sub_le_sub le_rfl hent_le
 
/-! ### 命题 3.20：co-Lip 常数与熵差上界 (CH03-P25-01 .. 02) -/
 
/-- CH03-P25-01: 命题 3.20 正有限 co-Lip 条目将内部输出中心原像拉回为 `ε/K_{i→j}` 输入内覆盖，证明覆盖数下界。 -/
theorem prop_3_20_covering_number_lower_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i j : I) (ε : ENNReal)
    (_hU_ne : U.Nonempty) (_hU : U ⊆ dom ϕ)
    (_hε0 : 0 < ε) (_hεtop : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK0 : 0 < K i j) (hKtop : K i j < ⊤) :
    (∀ [DecidableEq X] (T : Finset X), InternalEpsilonNet (d j) ε (operator_image ϕ U) T →
      ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card) ∧
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (operator_image ϕ U) := by
  have hK_ne0 : K i j ≠ 0 := ne_of_gt hK0
  have hK_netop : K i j ≠ ⊤ := lt_top_iff_ne_top.mp hKtop
  have hpull : ∀ [DecidableEq X] (T : Finset X), InternalEpsilonNet (d j) ε (operator_image ϕ U) T →
      ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
    intro _ T hT
    let rep : {t // t ∈ T} → X := fun t => Classical.choose (hT.1 t.2)
    have hrep : ∀ t : {t // t ∈ T}, rep t ∈ U ∧ ϕ.func (rep t) = t.1 :=
      fun t => Classical.choose_spec (hT.1 t.2)
    let S : Finset X := T.attach.image rep
    refine ⟨S, ⟨?_, ?_⟩, le_trans Finset.card_image_le (by simp)⟩
    · intro s hs
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hs) with ⟨t, _, rfl⟩
      exact (hrep t).1
    · intro x hxU
      rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, htT, hxt⟩
      let ct := rep ⟨t, htT⟩
      have hctU : ct ∈ U := (hrep ⟨t, htT⟩).1
      have hct_eq : ϕ.func ct = t := (hrep ⟨t, htT⟩).2
      have hmul_lt : K i j * d i x ct < ε := by
        calc
          K i j * d i x ct ≤ ∑ k : I, K k j * d k x ct :=
            Finset.single_le_sum (f := fun k => K k j * d k x ct)
              (fun _ _ => zero_le _) (Finset.mem_univ i)
          _ ≤ d j (ϕ.func x) (ϕ.func ct) := hK.2.2 x hxU ct hctU j
          _ = d j (ϕ.func x) t := by rw [hct_eq]
          _ < ε := hxt
      refine ⟨ct, Finset.mem_image_of_mem rep (Finset.mem_attach _ ⟨t, htT⟩), ?_⟩
      calc
        d i x ct = (K i j)⁻¹ * (K i j * d i x ct) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hK_ne0 hK_netop, one_mul]
        _ = (K i j * d i x ct) * (K i j)⁻¹ := mul_comm _ _
        _ < ε * (K i j)⁻¹ :=
          ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr hK_netop)
            (ENNReal.inv_ne_top.mpr hK_ne0) hmul_lt
        _ = ε / K i j := rfl
  refine ⟨hpull, ?_⟩
  classical
  apply le_iInf₂
  intro T hT
  rcases hpull T hT with ⟨S, hnet_in, hcard⟩
  exact le_trans
    (iInf_le_of_le S (iInf_le_of_le hnet_in le_rfl))
    (by exact_mod_cast hcard)
 
/-- CH03-P25-02: 命题 3.20 输入全有界（允许输出熵为 `+∞`）保证映射熵差良定及熵差上界。 -/
theorem prop_3_20_entropy_diff_upper_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i j : I) (ε : ENNReal)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (htb : IsTotallyBounded (d i) U)
    (hε0 : 0 < ε) (hεtop : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK0 : 0 < K i j) (hKtop : K i j < ⊤) :
    metric_entropy (d i) ε U < ⊤ ∧
    metric_entropy (d i) (ε / K i j) U < ⊤ ∧
    ∃ hwf : MappingEntropyDiffCompWellDefined d ϕ U i j ε,
      mappingEntropyDiffComp d ϕ U i j ε hwf ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hcov_ge := (prop_3_20_covering_number_lower_bound d ϕ U K i j ε
    hU_ne hU hε0 hεtop hK hK0 hKtop).2
  have hdiv_pos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε0) (lt_top_iff_ne_top.mp hKtop)
  have hdiv_top : ε / K i j < ⊤ := ENNReal.div_lt_top (lt_top_iff_ne_top.mp hεtop) (ne_of_gt hK0)
  have hin_lt : covering_number (d i) ε U < ⊤ := htb ε hε0 hεtop
  have hdiv_cov_lt : covering_number (d i) (ε / K i j) U < ⊤ := htb (ε / K i j) hdiv_pos hdiv_top
  have hwf : MappingEntropyDiffCompWellDefined d ϕ U i j ε := by
    refine ⟨hU_ne, hU, Set.singleton_nonempty i, Set.singleton_nonempty j, hε0, hεtop, Or.inl ?_⟩
    simpa [subfamily_covering_number_singleton] using hin_lt
  have hent_ge : metric_entropy (d i) (ε / K i j) U ≤ metric_entropy (d j) ε (operator_image ϕ U) :=
    log2_ereal_mono hcov_ge
  refine ⟨(metric_entropy_lt_top_iff _ _ _).mpr hin_lt,
    (metric_entropy_lt_top_iff _ _ _).mpr hdiv_cov_lt, hwf, ?_⟩
  unfold mappingEntropyDiffComp
  rw [mappingEntropyDiff_eq_sub, subfamily_metric_entropy_singleton,
      subfamily_metric_entropy_singleton]
  exact EReal.sub_le_sub le_rfl hent_ge
 
end Ch03
