import CH03.Core5

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X : Type} {I : Type} {bot : X}

theorem metric_entropy_eq_coe_of_cover_finite
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X)
    (h0 : covering_number d ε U ≠ 0) (htop : covering_number d ε U ≠ ⊤) :
    metric_entropy d ε U =
      ↑(Real.logb 2 (covering_number d ε U).toReal) := by
  unfold metric_entropy
  simp [log2_ereal, h0, htop]

theorem covering_number_pos_of_nonempty
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) (hU : U.Nonempty) :
    covering_number d ε U ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one
    (one_le_covering_number_of_nonempty d ε U hU))

theorem image_nonempty_of_nonempty (φ : Operator X bot) {U : Set X} (hU : U.Nonempty) :
    (φ.func '' U).Nonempty := by
  rcases hU with ⟨x, hx⟩
  exact ⟨φ.func x, ⟨x, hx, rfl⟩⟩

/-! ## Proposition 3.19 -/

theorem image_net_of_lip [DecidableEq X]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (L : ENNReal) (hLpos : 0 < L) (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L * d i x y)
    {ε : ENNReal} {S : Finset X}
    (hS : InternalEpsilonNet (d i) (ε / L) U S) :
    InternalEpsilonNet (d j) ε (φ.func '' U) (S.image φ.func) := by
  classical
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hS.2 x hx with ⟨s, hs, hdist⟩
    refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    have hmul : L * d i x s < ε := by
      have := (ENNReal.mul_lt_of_lt_div hdist : d i x s * L < ε)
      rwa [mul_comm] at this
    exact lt_of_le_of_lt (hLip x hx s (hS.1 hs)) hmul

theorem covering_number_image_le_of_lip
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (L : ENNReal) (hLpos : 0 < L)
    (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L * d i x y)
    (ε : ENNReal) :
    covering_number (d j) ε (φ.func '' U) ≤ covering_number (d i) (ε / L) U := by
  classical
  by_cases hfin : ∃ S : Finset X, InternalEpsilonNet (d i) (ε / L) U S
  · obtain ⟨S, hS, hcover, _⟩ := covering_number_attained (d i) (ε / L) U hfin
    calc
      covering_number (d j) ε (φ.func '' U)
          ≤ ((S.image φ.func).card : ENNReal) :=
            covering_number_le_card_of_net (image_net_of_lip d φ U i j L hLpos hLip hS)
      _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
      _ = covering_number (d i) (ε / L) U := hcover.symm
  · rw [(covering_number_eq_top_iff (d i) (ε / L) U).mpr hfin]
    exact le_top

theorem lip_entropy_diff_lower
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) (L ε : ENNReal)
    (hU : U.Nonempty) (hLpos : 0 < L) (hLtop : L ≠ ⊤)
    (hεpos : 0 < ε) (hεtop : ε ≠ ⊤)
    (hTB : TotallyBoundedOn (d i) U)
    (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L * d i x y) :
    erealSub (subfamily_metric_entropy d ({i} : Set I) ε U)
        (subfamily_metric_entropy d ({i} : Set I) (ε / L) U) ≤
      mappingEntropyDiff d φ U {i} {j} ε := by
  classical
  have hdivpos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hεpos) hLtop
  have hdivtop : ε / L ≠ ⊤ := ENNReal.div_ne_top hεtop (ne_of_gt hLpos)
  have hNin_top : covering_number (d i) ε U ≠ ⊤ := hTB ε hεpos hεtop
  have hNin2_top : covering_number (d i) (ε / L) U ≠ ⊤ := hTB (ε / L) hdivpos hdivtop
  have hNin0 : covering_number (d i) ε U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) ε U hU
  have hNin20 : covering_number (d i) (ε / L) U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) (ε / L) U hU
  have hcover := covering_number_image_le_of_lip d φ U i j L hLpos hLip ε
  have hNout_top : covering_number (d j) ε (φ.func '' U) ≠ ⊤ :=
    ne_top_of_le_ne_top hNin2_top hcover
  have hNout0 : covering_number (d j) ε (φ.func '' U) ≠ 0 :=
    covering_number_pos_of_nonempty (d j) ε (φ.func '' U)
      (image_nonempty_of_nonempty φ hU)
  have hEin : metric_entropy (d i) ε U =
      ↑(Real.logb 2 (covering_number (d i) ε U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) ε U hNin0 hNin_top
  have hEin2 : metric_entropy (d i) (ε / L) U =
      ↑(Real.logb 2 (covering_number (d i) (ε / L) U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) (ε / L) U hNin20 hNin2_top
  have hEout : metric_entropy (d j) ε (φ.func '' U) =
      ↑(Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d j) ε (φ.func '' U) hNout0 hNout_top
  have hlog : Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal ≤
      Real.logb 2 (covering_number (d i) (ε / L) U).toReal := by
    apply Real.logb_le_logb_of_le one_lt_two
    · exact ENNReal.toReal_pos hNout0 hNout_top
    · exact ENNReal.toReal_mono hNin2_top hcover
  unfold mappingEntropyDiff
  rw [subfamily_metric_entropy_singleton d i ε U,
    subfamily_metric_entropy_singleton d i (ε / L) U,
    subfamily_metric_entropy_singleton d j ε (φ.func '' U)]
  rw [hEin, hEin2, hEout, erealSub_coe_coe, erealSub_coe_coe]
  apply EReal.coe_le_coe
  linarith

/-! ## Proposition 3.20 -/

theorem preimage_net_of_colip
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (K : ENNReal) (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    {ε : ENNReal} {T : Finset X}
    (hT : InternalEpsilonNet (d j) ε (φ.func '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K) U S ∧ S.card ≤ T.card := by
  classical
  let rep : {t : X // t ∈ T} → X := fun t =>
    Classical.choose (hT.1 t.2)
  have hrepU : ∀ t : {t : X // t ∈ T}, rep t ∈ U := fun t =>
    (Classical.choose_spec (hT.1 t.2)).1
  have hrepval : ∀ t : {t : X // t ∈ T}, φ.func (rep t) = t.1 := fun t =>
    (Classical.choose_spec (hT.1 t.2)).2
  let S : Finset X := T.attach.image rep
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
      exact hrepU t
    · intro x hx
      rcases hT.2 (φ.func x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
      refine ⟨rep ⟨t, ht⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
      · have hval : φ.func (rep ⟨t, ht⟩) = t := hrepval ⟨t, ht⟩
        have hcoin : K * d i x (rep ⟨t, ht⟩) < ε := by
          calc
            K * d i x (rep ⟨t, ht⟩) ≤
                d j (φ.func x) (φ.func (rep ⟨t, ht⟩)) :=
              hco x hx (rep ⟨t, ht⟩) (hrepU ⟨t, ht⟩)
            _ = d j (φ.func x) t := by rw [hval]
            _ < ε := hdist
        rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hKpos)) (Or.inl hKtop)]
        rwa [mul_comm]
  · calc
      S.card ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach

theorem covering_number_le_image_of_colip
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (K : ENNReal) (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    (ε : ENNReal) :
    covering_number (d i) (ε / K) U ≤ covering_number (d j) ε (φ.func '' U) := by
  classical
  by_cases hfin : ∃ T : Finset X, InternalEpsilonNet (d j) ε (φ.func '' U) T
  · obtain ⟨T, hT, hcover, _⟩ :=
      covering_number_attained (d j) ε (φ.func '' U) hfin
    obtain ⟨S, hS, hcard⟩ := preimage_net_of_colip d φ U i j K hKpos hKtop hco hT
    calc
      covering_number (d i) (ε / K) U ≤ (S.card : ENNReal) :=
        covering_number_le_card_of_net hS
      _ ≤ (T.card : ENNReal) := by exact_mod_cast hcard
      _ = covering_number (d j) ε (φ.func '' U) := hcover.symm
  · rw [(covering_number_eq_top_iff (d j) ε (φ.func '' U)).mpr hfin]
    exact le_top

theorem erealSub_coe_top (x : ℝ) : erealSub (↑x : EReal) ⊤ = ⊥ := by
  simp [erealSub]

theorem erealSub_coe_coe_le_coe_coe {a b c d : ℝ} (h : a - c ≤ b - d) :
    (erealSub (↑a : EReal) (↑c : EReal)) ≤ erealSub (↑b : EReal) (↑d : EReal) := by
  rw [erealSub_coe_coe, erealSub_coe_coe]
  exact EReal.coe_le_coe h

theorem colip_entropy_diff_upper
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) (K ε : ENNReal)
    (hU : U.Nonempty) (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (hεpos : 0 < ε) (hεtop : ε ≠ ⊤)
    (hTB : TotallyBoundedOn (d i) U)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y)) :
    mappingEntropyDiff d φ U {i} {j} ε ≤
      erealSub (subfamily_metric_entropy d ({i} : Set I) ε U)
        (subfamily_metric_entropy d ({i} : Set I) (ε / K) U) := by
  classical
  have hdivpos : 0 < ε / K := ENNReal.div_pos (ne_of_gt hεpos) hKtop
  have hdivtop : ε / K ≠ ⊤ := ENNReal.div_ne_top hεtop (ne_of_gt hKpos)
  have hNin_top : covering_number (d i) ε U ≠ ⊤ := hTB ε hεpos hεtop
  have hNin2_top : covering_number (d i) (ε / K) U ≠ ⊤ := hTB (ε / K) hdivpos hdivtop
  have hNin0 : covering_number (d i) ε U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) ε U hU
  have hNin20 : covering_number (d i) (ε / K) U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) (ε / K) U hU
  have hEin : metric_entropy (d i) ε U =
      ↑(Real.logb 2 (covering_number (d i) ε U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) ε U hNin0 hNin_top
  have hEin2 : metric_entropy (d i) (ε / K) U =
      ↑(Real.logb 2 (covering_number (d i) (ε / K) U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) (ε / K) U hNin20 hNin2_top
  have hcover := covering_number_le_image_of_colip d φ U i j K hKpos hKtop hco ε
  by_cases houttop : covering_number (d j) ε (φ.func '' U) = ⊤
  · have hEout_top : metric_entropy (d j) ε (φ.func '' U) = ⊤ := by
      unfold metric_entropy
      simp [log2_ereal, houttop]
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_singleton d i ε U,
      subfamily_metric_entropy_singleton d i (ε / K) U,
      subfamily_metric_entropy_singleton d j ε (φ.func '' U)]
    rw [hEin, hEin2, hEout_top, erealSub_coe_top, erealSub_coe_coe]
    exact bot_le
  · have hNout0 : covering_number (d j) ε (φ.func '' U) ≠ 0 :=
      covering_number_pos_of_nonempty (d j) ε (φ.func '' U)
        (image_nonempty_of_nonempty φ hU)
    have hEout : metric_entropy (d j) ε (φ.func '' U) =
        ↑(Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal) :=
      metric_entropy_eq_coe_of_cover_finite (d j) ε (φ.func '' U) hNout0 houttop
    have hlog : Real.logb 2 (covering_number (d i) (ε / K) U).toReal ≤
        Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal := by
      apply Real.logb_le_logb_of_le one_lt_two
      · exact ENNReal.toReal_pos hNin20 hNin2_top
      · exact ENNReal.toReal_mono houttop hcover
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_singleton d i ε U,
      subfamily_metric_entropy_singleton d i (ε / K) U,
      subfamily_metric_entropy_singleton d j ε (φ.func '' U)]
    rw [hEin, hEin2, hEout, erealSub_coe_coe, erealSub_coe_coe]
    apply EReal.coe_le_coe
    linarith


theorem subfamily_pseudometric_self_zero
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (J : Set I) (x : X) :
    subfamily_pseudometric d J x x = 0 := by
  rw [subfamily_pseudometric, ENNReal.iSup_eq_zero]
  intro j
  exact hself j.1 x

theorem finite_mapping_entropy_diff_wellDefined
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (U : Set X) (hUfin : U.Finite)
    (Jin Jout : Set I) (ε : ENNReal) (hε : 0 < ε) (hεtop : ε ≠ ⊤) :
    MappingEntropyDiffWellDefined d φ U Jin Jout ε := by
  left
  exact finite_set_metric_entropy_ne_top (subfamily_pseudometric d Jin)
    (subfamily_pseudometric_self_zero d hself Jin) U hUfin hε
end formal_oet.vol_01.ch_03_operator_local_degeneracy
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

theorem finite_mapping_entropy_both_finite
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (U : Set X) (hUfin : U.Finite) (hUne : U.Nonempty)
    (Jin Jout : Set I) (hJin : Jin.Nonempty) (hJout : Jout.Nonempty)
    (ε : ENNReal) (hε : 0 < ε) (hεtop : ε ≠ ⊤) :
    covering_number (subfamily_pseudometric d Jin) ε U ≠ 0 ∧
    covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤ ∧
    covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) ≠ 0 ∧
    covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) ≠ ⊤ ∧
    subfamily_metric_entropy d Jin ε U ≠ ⊤ ∧
    subfamily_metric_entropy d Jin ε U ≠ ⊥ ∧
    subfamily_metric_entropy d Jout ε (φ.func '' U) ≠ ⊤ ∧
    subfamily_metric_entropy d Jout ε (φ.func '' U) ≠ ⊥ ∧
    MappingEntropyDiffWellDefined d φ U Jin Jout ε := by
  have hsubSelfIn : ∀ x, subfamily_pseudometric d Jin x x = 0 :=
    subfamily_pseudometric_self_zero d hself Jin
  have hsubSelfOut : ∀ x, subfamily_pseudometric d Jout x x = 0 :=
    subfamily_pseudometric_self_zero d hself Jout
  have hUimg : (φ.func '' U).Finite := hUfin.image φ.func
  have hUimgne : (φ.func '' U).Nonempty := image_nonempty_of_nonempty φ hUne
  have hNin0 : covering_number (subfamily_pseudometric d Jin) ε U ≠ 0 :=
    covering_number_pos_of_nonempty _ ε U hUne
  have hNinTop : covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤ :=
    finite_set_metric_entropy_ne_top (subfamily_pseudometric d Jin) hsubSelfIn U hUfin hε
      |> fun h => by
        by_contra htop
        apply h
        unfold metric_entropy
        simp [log2_ereal, htop]
  have hNout0 : covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) ≠ 0 :=
    covering_number_pos_of_nonempty _ ε (φ.func '' U) hUimgne
  have hNoutTop : covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) ≠ ⊤ :=
    finite_set_metric_entropy_ne_top (subfamily_pseudometric d Jout) hsubSelfOut
      (φ.func '' U) hUimg hε
      |> fun h => by
        by_contra htop
        apply h
        unfold metric_entropy
        simp [log2_ereal, htop]
  have hEinTop : subfamily_metric_entropy d Jin ε U ≠ ⊤ :=
    finite_set_metric_entropy_ne_top (subfamily_pseudometric d Jin) hsubSelfIn U hUfin hε
  have hEinBot : subfamily_metric_entropy d Jin ε U ≠ ⊥ :=
    metric_entropy_ne_bot_of_nonempty (subfamily_pseudometric d Jin) U hUne ε
  have hEoutTop : subfamily_metric_entropy d Jout ε (φ.func '' U) ≠ ⊤ :=
    finite_set_metric_entropy_ne_top (subfamily_pseudometric d Jout) hsubSelfOut
      (φ.func '' U) hUimg hε
  have hEoutBot : subfamily_metric_entropy d Jout ε (φ.func '' U) ≠ ⊥ :=
    metric_entropy_ne_bot_of_nonempty (subfamily_pseudometric d Jout) (φ.func '' U) hUimgne ε
  exact ⟨hNin0, hNinTop, hNout0, hNoutTop, hEinTop, hEinBot, hEoutTop, hEoutBot,
    Or.inl hEinTop⟩

end formal_oet.vol_01.ch_03_operator_local_degeneracy
