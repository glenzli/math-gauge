import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Ch03.Partition
import Ch03.Scale
import Mathlib.Tactic

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

section MappingEntropyDifference

variable {X I : Type} {bot : X}

/-- **定义（映射熵差的良定性前提）**：输入与输出两端覆盖数至少有一个有限，排除 `∞ - ∞`。 -/
def MappingEntropyDiffWellDefined (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J_in J_out : Set I) (ε : ENNReal) (U : Set X) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ J_in.Nonempty ∧ J_out.Nonempty ∧ 0 < ε ∧ ε < ⊤ ∧
  (subfamily_covering_number d J_in ε U < ⊤ ∨
   subfamily_covering_number d J_out ε (ϕ.func '' U) < ⊤)

/-- **定义（映射熵差）**：`ΔE_{ε, J_in, J_out}(ϕ | U) := E_{ε, J_in}(U) - E_{ε, J_out}(ϕ(U))`。 -/
noncomputable def mappingEntropyDiff (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J_in J_out : Set I) (ε : ENNReal) (U : Set X) : EReal :=
  subfamily_metric_entropy d J_in ε U -
    subfamily_metric_entropy d J_out ε (ϕ.func '' U)

/-- 同子族简记 `ΔE_{ε, J}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffSame (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (ε : ENNReal) (U : Set X) : EReal :=
  mappingEntropyDiff d ϕ J J ε U

/-- 单分量简记 `ΔE_{ε, j}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffSingle (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (j : I) (ε : ENNReal) (U : Set X) : EReal :=
  mappingEntropyDiff d ϕ {j} {j} ε U

lemma mappingEntropyDiff_single_pair (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i j : I) (ε : ENNReal) (U : Set X) :
    mappingEntropyDiff d ϕ {i} {j} ε U =
      metric_entropy (d i) ε U - metric_entropy (d j) ε (ϕ.func '' U) := by
  simp [mappingEntropyDiff, subfamily_metric_entropy_singleton]

lemma metric_entropy_eq_coe_of_nonempty_of_lt_top {d : X → X → ENNReal} {ε : ENNReal}
    {U : Set X} (hUne : U.Nonempty) (hlt : covering_number d ε U < ⊤) :
    ∃ r : ℝ, 0 ≤ r ∧ metric_entropy d ε U = (r : EReal) := by
  have h1 : (1 : ENNReal) ≤ covering_number d ε U :=
    one_le_covering_number_of_nonempty d ε U hUne
  have h0 : covering_number d ε U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  have htop : covering_number d ε U ≠ ⊤ := ne_of_lt hlt
  refine ⟨Real.logb 2 (covering_number d ε U).toReal, ?_, ?_⟩
  · apply Real.logb_nonneg one_lt_two
    simpa using ENNReal.toReal_mono htop h1
  · simp [metric_entropy, log2_ereal, h0, htop]

lemma metric_entropy_eq_top_of_eq_top {d : X → X → ENNReal} {ε : ENNReal}
    {U : Set X} (htop : covering_number d ε U = ⊤) :
    metric_entropy d ε U = ⊤ := by
  simp [metric_entropy, log2_ereal, htop]

lemma metric_entropy_one {d : X → X → ENNReal} {ε : ENNReal} {U : Set X}
    (h1 : covering_number d ε U = 1) :
    metric_entropy d ε U = 0 := by
  simp [metric_entropy, log2_ereal, h1]

lemma mappingEntropyDiffWellDefined_not_both_top (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J_in J_out : Set I) (ε : ENNReal) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ϕ J_in J_out ε U) :
    ¬ (subfamily_metric_entropy d J_in ε U = ⊤ ∧
       subfamily_metric_entropy d J_out ε (ϕ.func '' U) = ⊤) := by
  rintro ⟨h1, h2⟩
  rcases hwd.2.2.2.2.2.2 with hin | hout
  · obtain ⟨r, _, hr⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hwd.1 hin
    rw [subfamily_metric_entropy_eq_metric_entropy, hr] at h1
    exact EReal.coe_ne_top r h1
  · obtain ⟨r, _, hr⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top (hwd.1.image ϕ.func) hout
    rw [subfamily_metric_entropy_eq_metric_entropy, hr] at h2
    exact EReal.coe_ne_top r h2

/-- **注（有限集上映射熵差的良定性）**：非空有限集上两端覆盖数均有限正，熵为有限实数，熵差为有限实数且良定。 -/
theorem note_finite_mapping_entropy_diff_well_defined (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J_in J_out : Set I) (ε : ENNReal) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (hUne : U.Nonempty) (hUfin : U.Finite) (hUdom : U ⊆ dom ϕ)
    (hJin : J_in.Nonempty) (hJout : J_out.Nonempty)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) :
    (0 < subfamily_covering_number d J_in ε U ∧
      subfamily_covering_number d J_in ε U < ⊤) ∧
    (0 < subfamily_covering_number d J_out ε (ϕ.func '' U) ∧
      subfamily_covering_number d J_out ε (ϕ.func '' U) < ⊤) ∧
    (∃ r₁ : ℝ, subfamily_metric_entropy d J_in ε U = (r₁ : EReal)) ∧
    (∃ r₂ : ℝ, subfamily_metric_entropy d J_out ε (ϕ.func '' U) = (r₂ : EReal)) ∧
    MappingEntropyDiffWellDefined d ϕ J_in J_out ε U ∧
    ∃ r : ℝ, mappingEntropyDiff d ϕ J_in J_out ε U = (r : EReal) := by
  have hcov_in_pos : 0 < subfamily_covering_number d J_in ε U :=
    lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty _ _ _ hUne)
  have hcov_in_fin : subfamily_covering_number d J_in ε U < ⊤ := by
    let S : Finset X := hUfin.toFinset
    have hnet : InternalEpsilonNet (subfamily_pseudometric d J_in) ε U S := by
      refine ⟨?_, ?_⟩
      · intro x hx
        exact hUfin.mem_toFinset.mp hx
      · intro x hx
        refine ⟨x, hUfin.mem_toFinset.mpr hx, ?_⟩
        have hself : subfamily_pseudometric d J_in x x = 0 :=
          (subfamily_pseudometric_is_extended d J_in hJin hd).dist_self x
        rw [hself]
        exact hε_pos
    exact lt_of_le_of_lt (covering_number_le_card _ ε U S hnet) (ENNReal.natCast_lt_top _)
  have himg_ne : (ϕ.func '' U).Nonempty := hUne.image ϕ.func
  have himg_fin : (ϕ.func '' U).Finite := hUfin.image ϕ.func
  have hcov_out_pos : 0 < subfamily_covering_number d J_out ε (ϕ.func '' U) :=
    lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty _ _ _ himg_ne)
  have hcov_out_fin : subfamily_covering_number d J_out ε (ϕ.func '' U) < ⊤ := by
    let T : Finset X := himg_fin.toFinset
    have hnet : InternalEpsilonNet (subfamily_pseudometric d J_out) ε (ϕ.func '' U) T := by
      refine ⟨?_, ?_⟩
      · intro y hy
        exact himg_fin.mem_toFinset.mp hy
      · intro y hy
        refine ⟨y, himg_fin.mem_toFinset.mpr hy, ?_⟩
        have hself : subfamily_pseudometric d J_out y y = 0 :=
          (subfamily_pseudometric_is_extended d J_out hJout hd).dist_self y
        rw [hself]
        exact hε_pos
    exact lt_of_le_of_lt (covering_number_le_card _ ε (ϕ.func '' U) T hnet)
      (ENNReal.natCast_lt_top _)
  obtain ⟨r₁, _, hr₁⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hcov_in_fin
  obtain ⟨r₂, _, hr₂⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hcov_out_fin
  rw [← subfamily_metric_entropy_eq_metric_entropy] at hr₁ hr₂
  have hwd : MappingEntropyDiffWellDefined d ϕ J_in J_out ε U :=
    ⟨hUne, hUdom, hJin, hJout, hε_pos, hε_fin, Or.inl hcov_in_fin⟩
  refine ⟨⟨hcov_in_pos, hcov_in_fin⟩, ⟨hcov_out_pos, hcov_out_fin⟩,
    ⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩, hwd, ⟨r₁ - r₂, ?_⟩⟩
  unfold mappingEntropyDiff
  rw [hr₁, hr₂]
  rfl

/-- **命题 3.18 (i)**：常值分量下输出覆盖数为 `1`、输出熵为 `0`、映射熵差等于输入熵（允许输入熵为 `+∞`）。 -/
theorem prop_3_18_const (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (ε : ENNReal) (j : I)
    (_hd : ExtendedPseudoMetric X bot (d j))
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hj : j ∈ I_const d ϕ U) :
    covering_number (d j) ε (ϕ.func '' U) = 1 ∧
    metric_entropy (d j) ε (ϕ.func '' U) = 0 ∧
    MappingEntropyDiffWellDefined d ϕ {j} {j} ε U ∧
    mappingEntropyDiffSame d ϕ {j} ε U = metric_entropy (d j) ε U := by
  rcases hUne with ⟨x₀, hx₀⟩
  have hcov1 : covering_number (d j) ε (ϕ.func '' U) = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (d j) ε (ϕ.func '' U) {ϕ.func x₀} := by
        constructor
        · intro z hz
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hz
          rw [hz]
          exact ⟨x₀, hx₀, rfl⟩
        · rintro y ⟨x, hx, rfl⟩
          refine ⟨ϕ.func x₀, Finset.mem_singleton_self _, ?_⟩
          rw [hj x hx x₀ hx₀]
          exact hε_pos
      simpa using covering_number_le_card (d j) ε (ϕ.func '' U) {ϕ.func x₀} hnet
    · exact one_le_covering_number_of_nonempty (d j) ε (ϕ.func '' U) ⟨ϕ.func x₀, x₀, hx₀, rfl⟩
  have hent0 : metric_entropy (d j) ε (ϕ.func '' U) = 0 := metric_entropy_one hcov1
  have hwd : MappingEntropyDiffWellDefined d ϕ {j} {j} ε U := by
    refine ⟨⟨x₀, hx₀⟩, hUdom, ⟨j, Set.mem_singleton j⟩, ⟨j, Set.mem_singleton j⟩,
      hε_pos, hε_fin, Or.inr ?_⟩
    rw [subfamily_covering_number, subfamily_pseudometric_singleton, hcov1]
    exact ENNReal.one_lt_top
  refine ⟨hcov1, hent0, hwd, ?_⟩
  unfold mappingEntropyDiffSame
  rw [mappingEntropyDiff_single_pair, hent0, sub_zero]

/-- **命题 3.18 (ii-a)**：恒等分量下输入与输出像集具有相同的覆盖数和度量熵。 -/
theorem prop_3_18_id_covering_entropy (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (ε : ENNReal) (j : I)
    (hd : ExtendedPseudoMetric X bot (d j))
    (_hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤)
    (hj : j ∈ I_id d ϕ U) :
    covering_number (d j) ε (ϕ.func '' U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (ϕ.func '' U) = metric_entropy (d j) ε U := by
  classical
  have hiso := prop_3_1_id_isometry d ϕ U j hd hUdom hj
  have hcov : covering_number (d j) ε (ϕ.func '' U) = covering_number (d j) ε U := by
    apply le_antisymm
    · apply le_iInf; intro S
      apply le_iInf; intro hSnet
      let T : Finset X := S.image ϕ.func
      have hTnet : InternalEpsilonNet (d j) ε (ϕ.func '' U) T := by
        constructor
        · intro z hz
          rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨s, hs, rfl⟩
          exact ⟨s, hSnet.1 hs, rfl⟩
        · rintro y ⟨x, hx, rfl⟩
          rcases hSnet.2 x hx with ⟨s, hs, hdist⟩
          refine ⟨ϕ.func s, Finset.mem_image_of_mem ϕ.func hs, ?_⟩
          rw [hiso x hx s (hSnet.1 hs)]
          exact hdist
      calc
        covering_number (d j) ε (ϕ.func '' U) ≤ (T.card : ENNReal) :=
          covering_number_le_card (d j) ε (ϕ.func '' U) T hTnet
        _ ≤ (S.card : ENNReal) := Nat.cast_le.mpr Finset.card_image_le
    · apply le_iInf; intro T
      apply le_iInf; intro hTnet
      let pick : X → X := fun t => if h : t ∈ ϕ.func '' U then Classical.choose h else bot
      let S : Finset X := T.image pick
      have hSnet : InternalEpsilonNet (d j) ε U S := by
        constructor
        · intro s hs
          rcases Finset.mem_image.mp (Finset.mem_coe.mp hs) with ⟨t, ht, rfl⟩
          have htimg : t ∈ ϕ.func '' U := hTnet.1 ht
          simp only [pick, dif_pos htimg]
          exact (Classical.choose_spec htimg).1
        · intro x hx
          rcases hTnet.2 (ϕ.func x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
          have htimg : t ∈ ϕ.func '' U := hTnet.1 ht
          let s := pick t
          have hs_mem : s ∈ S := Finset.mem_image_of_mem pick ht
          have hs_spec : s ∈ U ∧ ϕ.func s = t := by
            simp only [s, pick, dif_pos htimg]
            exact Classical.choose_spec htimg
          refine ⟨s, hs_mem, ?_⟩
          rw [← hiso x hx s hs_spec.1, hs_spec.2]
          exact hdist
      calc
        covering_number (d j) ε U ≤ (S.card : ENNReal) :=
          covering_number_le_card (d j) ε U S hSnet
        _ ≤ (T.card : ENNReal) := Nat.cast_le.mpr Finset.card_image_le
  refine ⟨hcov, ?_⟩
  simp [metric_entropy, hcov]

/-- **命题 3.18 (ii-b)**：恒等分量下仅在映射熵差良定时推出熵差为 `0`（避免 `∞ - ∞`）。 -/
theorem prop_3_18_id_diff_zero (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (ε : ENNReal) (j : I)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hj : j ∈ I_id d ϕ U)
    (hwd : MappingEntropyDiffWellDefined d ϕ {j} {j} ε U) :
    mappingEntropyDiffSame d ϕ {j} ε U = 0 := by
  have ⟨hcov_eq, hent_eq⟩ := prop_3_18_id_covering_entropy d ϕ U ε j hd hUne hUdom hε_pos hε_fin hj
  have hfin_in : covering_number (d j) ε U < ⊤ := by
    rcases hwd.2.2.2.2.2.2 with hin | hout
    · simpa [subfamily_covering_number, subfamily_pseudometric_singleton] using hin
    · rw [← hcov_eq]
      simpa [subfamily_covering_number, subfamily_pseudometric_singleton] using hout
  obtain ⟨r, _, hr⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in
  unfold mappingEntropyDiffSame
  rw [mappingEntropyDiff_single_pair, hent_eq, hr]
  simp

/-- **命题 3.19 (i, image 版)**：有限正单通道 Lip 上界 `L` 将 `ε/L`-输入内覆盖推前为像中心集 `S.image ϕ.func` 构成的 `ε`-输出内覆盖。 -/
theorem prop_3_19_lip_push_image [DecidableEq X] (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (ε L : ENNReal)
    (_hUdom : U ⊆ dom ϕ) (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤)
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    ∀ S : Finset X, InternalEpsilonNet (d i) (ε / L) U S →
      InternalEpsilonNet (d j) ε (ϕ.func '' U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card := by
  intro S hSnet
  refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro z hz
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨s, hs, rfl⟩
    exact ⟨s, hSnet.1 hs, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    rcases hSnet.2 x hx with ⟨s, hs, hdist⟩
    refine ⟨ϕ.func s, Finset.mem_image_of_mem ϕ.func hs, ?_⟩
    have h1 : d j (ϕ.func x) (ϕ.func s) ≤ L * d i x s := hLip x hx s (hSnet.1 hs)
    have h2 : L * d i x s < L * (ε / L) := by
      rw [mul_comm L, mul_comm L]
      exact ENNReal.mul_lt_mul_left (ne_of_gt hL_pos) (ne_of_lt hL_fin) hdist
    have h3 : L * (ε / L) = ε := ENNReal.mul_div_cancel (ne_of_gt hL_pos) (ne_of_lt hL_fin)
    exact lt_of_le_of_lt h1 (h3 ▸ h2)

/-- **命题 3.19 (i)**：有限正单通道 Lip 上界 `L` 将 `ε/L`-输入内覆盖推前为基数不超过的 `ε`-输出内覆盖。 -/
theorem prop_3_19_lip_covering_le (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (ε L : ENNReal)
    (hUdom : U ⊆ dom ϕ) (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    (∀ S : Finset X, InternalEpsilonNet (d i) (ε / L) U S →
      ∃ T : Finset X, InternalEpsilonNet (d j) ε (ϕ.func '' U) T ∧ T.card ≤ S.card) ∧
    covering_number (d j) ε (ϕ.func '' U) ≤ covering_number (d i) (ε / L) U := by
  classical
  have hpush : ∀ S : Finset X, InternalEpsilonNet (d i) (ε / L) U S →
      ∃ T : Finset X, InternalEpsilonNet (d j) ε (ϕ.func '' U) T ∧ T.card ≤ S.card := by
    intro S hSnet
    exact ⟨S.image ϕ.func, prop_3_19_lip_push_image d ϕ U i j ε L hUdom hε_pos hε_fin
      hL_pos hL_fin hLip S hSnet⟩
  refine ⟨hpush, ?_⟩
  apply le_iInf; intro S
  apply le_iInf; intro hSnet
  rcases hpush S hSnet with ⟨T, hTnet, hcard⟩
  exact le_trans (covering_number_le_card (d j) ε (ϕ.func '' U) T hTnet) (Nat.cast_le.mpr hcard)

/-- **命题 3.19 (ii)**：全有界输入域上的单通道 Lip 上界给出映射熵差下界及良定性。 -/
theorem prop_3_19_lip_entropy_diff (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (ε L : ENNReal)
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hTB : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    MappingEntropyDiffWellDefined d ϕ {i} {j} ε U ∧
    metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
      mappingEntropyDiff d ϕ {i} {j} ε U := by
  have hεL_pos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hL_fin)
  have hεL_fin : ε / L < ⊤ := ENNReal.div_lt_top (ne_of_lt hε_fin) (ne_of_gt hL_pos)
  have hcov_eps_fin : covering_number (d i) ε U < ⊤ := hTB ε hε_pos hε_fin
  have hcov_epsL_fin : covering_number (d i) (ε / L) U < ⊤ := hTB (ε / L) hεL_pos hεL_fin
  have hcov_le : covering_number (d j) ε (ϕ.func '' U) ≤ covering_number (d i) (ε / L) U :=
    (prop_3_19_lip_covering_le d ϕ U i j ε L hUdom hε_pos hε_fin hL_pos hL_fin hLip).2
  have hcov_out_fin : covering_number (d j) ε (ϕ.func '' U) < ⊤ :=
    lt_of_le_of_lt hcov_le hcov_epsL_fin
  have hwd : MappingEntropyDiffWellDefined d ϕ {i} {j} ε U := by
    refine ⟨hUne, hUdom, ⟨i, Set.mem_singleton i⟩, ⟨j, Set.mem_singleton j⟩,
      hε_pos, hε_fin, Or.inl ?_⟩
    simpa [subfamily_covering_number, subfamily_pseudometric_singleton] using hcov_eps_fin
  obtain ⟨r₁, _, hr₁⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hcov_eps_fin
  obtain ⟨r₂, _, hr₂⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hcov_epsL_fin
  obtain ⟨r₃, _, hr₃⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top (hUne.image ϕ.func) hcov_out_fin
  have hent_le : metric_entropy (d j) ε (ϕ.func '' U) ≤ metric_entropy (d i) (ε / L) U :=
    metric_entropy_le_of_covering_le hcov_le
  rw [hr₃, hr₂, EReal.coe_le_coe_iff] at hent_le
  refine ⟨hwd, ?_⟩
  rw [mappingEntropyDiff_single_pair, hr₁, hr₂, hr₃]
  change ((r₁ - r₂ : ℝ) : EReal) ≤ ((r₁ - r₃ : ℝ) : EReal)
  rw [EReal.coe_le_coe_iff]
  linarith

/-- **命题 3.20 (i)**：正有限 co-Lip 单个矩阵条目将输出 `ε`-内覆盖拉回为基数不超过的 `ε/K`-输入内覆盖。 -/
theorem prop_3_20_colip_covering_le [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (K : I → I → ENNReal) (i j : I) (ε : ENNReal)
    (_hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    (∀ T : Finset X, InternalEpsilonNet (d j) ε (ϕ.func '' U) T →
      ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card) ∧
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (ϕ.func '' U) := by
  classical
  have hpull : ∀ T : Finset X, InternalEpsilonNet (d j) ε (ϕ.func '' U) T →
      ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
    intro T hTnet
    let pick : X → X := fun t => if h : t ∈ ϕ.func '' U then Classical.choose h else bot
    let S : Finset X := T.image pick
    refine ⟨S, ⟨?_, ?_⟩, Finset.card_image_le⟩
    · intro s hs
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hs) with ⟨t, ht, rfl⟩
      have htimg : t ∈ ϕ.func '' U := hTnet.1 ht
      simp only [pick, dif_pos htimg]
      exact (Classical.choose_spec htimg).1
    · intro x hx
      rcases hTnet.2 (ϕ.func x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
      have htimg : t ∈ ϕ.func '' U := hTnet.1 ht
      let c := pick t
      have hc_mem : c ∈ S := Finset.mem_image_of_mem pick ht
      have hc_spec : c ∈ U ∧ ϕ.func c = t := by
        simp only [c, pick, dif_pos htimg]
        exact Classical.choose_spec htimg
      refine ⟨c, hc_mem, ?_⟩
      have hsingle : K i j * d i x c ≤ ∑ k : I, K k j * d k x c :=
        Finset.single_le_sum (f := fun k : I => K k j * d k x c)
          (fun _ _ => zero_le _) (Finset.mem_univ i)
      have hcolip : ∑ k : I, K k j * d k x c ≤ d j (ϕ.func x) (ϕ.func c) :=
        hK.2.2 x hx c hc_spec.1 j
      have hmul_lt : K i j * d i x c < ε := by
        rw [hc_spec.2] at hcolip
        exact lt_of_le_of_lt (le_trans hsingle hcolip) hdist
      calc
        d i x c = (K i j)⁻¹ * (K i j * d i x c) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt hK_pos) (ne_of_lt hK_fin), one_mul]
        _ < (K i j)⁻¹ * ε := by
          rw [mul_comm (K i j)⁻¹, mul_comm (K i j)⁻¹]
          exact ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr (ne_of_lt hK_fin))
            (ENNReal.inv_ne_top.mpr (ne_of_gt hK_pos)) hmul_lt
        _ = ε / K i j := by rw [div_eq_mul_inv, mul_comm]
  refine ⟨hpull, ?_⟩
  apply le_iInf; intro T
  apply le_iInf; intro hTnet
  rcases hpull T hTnet with ⟨S, hSnet, hcard⟩
  exact le_trans (covering_number_le_card (d i) (ε / K i j) U S hSnet) (Nat.cast_le.mpr hcard)

/-- **命题 3.20 (ii)**：正有限 co-Lip 常数给出映射熵差上界（允许输出熵为 `+∞`）。 -/
theorem prop_3_20_colip_entropy_diff [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (K : I → I → ENNReal) (i j : I) (ε : ENNReal)
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hTB : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K)
    (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    MappingEntropyDiffWellDefined d ϕ {i} {j} ε U ∧
    mappingEntropyDiff d ϕ {i} {j} ε U ≤
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hεK_pos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hK_fin)
  have hεK_fin : ε / K i j < ⊤ := ENNReal.div_lt_top (ne_of_lt hε_fin) (ne_of_gt hK_pos)
  have hcov_eps_fin : covering_number (d i) ε U < ⊤ := hTB ε hε_pos hε_fin
  have hcov_epsK_fin : covering_number (d i) (ε / K i j) U < ⊤ := hTB (ε / K i j) hεK_pos hεK_fin
  have hcov_le : covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (ϕ.func '' U) :=
    (prop_3_20_colip_covering_le d ϕ U K i j ε hUne hUdom hε_pos hε_fin hK hK_pos hK_fin).2
  have hwd : MappingEntropyDiffWellDefined d ϕ {i} {j} ε U := by
    refine ⟨hUne, hUdom, ⟨i, Set.mem_singleton i⟩, ⟨j, Set.mem_singleton j⟩,
      hε_pos, hε_fin, Or.inl ?_⟩
    simpa [subfamily_covering_number, subfamily_pseudometric_singleton] using hcov_eps_fin
  obtain ⟨r₁, _, hr₁⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hcov_eps_fin
  obtain ⟨r₂, _, hr₂⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hcov_epsK_fin
  refine ⟨hwd, ?_⟩
  rw [mappingEntropyDiff_single_pair, hr₁, hr₂]
  by_cases hcov_top : covering_number (d j) ε (ϕ.func '' U) = ⊤
  · rw [metric_entropy_eq_top_of_eq_top hcov_top]
    have hbot : ((r₁ : EReal) - ⊤) = ⊥ := by
      rw [sub_eq_add_neg]
      simp
    rw [hbot]
    exact bot_le
  · have hcov_out_fin : covering_number (d j) ε (ϕ.func '' U) < ⊤ :=
      lt_top_iff_ne_top.mpr hcov_top
    obtain ⟨r₃, _, hr₃⟩ := metric_entropy_eq_coe_of_nonempty_of_lt_top (hUne.image ϕ.func) hcov_out_fin
    have hent_le : metric_entropy (d i) (ε / K i j) U ≤ metric_entropy (d j) ε (ϕ.func '' U) :=
      metric_entropy_le_of_covering_le hcov_le
    rw [hr₂, hr₃, EReal.coe_le_coe_iff] at hent_le
    rw [hr₃]
    change ((r₁ - r₃ : ℝ) : EReal) ≤ ((r₁ - r₂ : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff]
    linarith

end MappingEntropyDifference

end Ch03
