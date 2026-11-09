import Ch03.Coverage

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X I : Type} {bot : X}

section FiniteEntropy

/-- A finite set is its own internal cover. -/
theorem covering_number_lt_top_of_finite {dist : X → X → ENNReal} {U : Set X}
    (hd0 : ∀ x, dist x x = 0) (hU : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    covering_number dist ε U < ⊤ := by
  classical
  have hnet : InternalEpsilonNet dist ε U hU.toFinset := by
    constructor
    · simpa only [hU.coe_toFinset] using Subset.rfl
    · intro x hx
      exact ⟨x, hU.mem_toFinset.mpr hx, by rw [hd0]; exact hε⟩
  exact (covering_number_le_of_net hnet).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top _))

/-- A nonempty set with finite covering number has finite-real metric entropy. -/
theorem metric_entropy_eq_coe_of_cover_finite {dist : X → X → ENNReal} {U : Set X}
    (hU : U.Nonempty) {ε : ENNReal} (hfin : covering_number dist ε U < ⊤) :
    metric_entropy dist ε U = ↑(Real.logb 2 (covering_number dist ε U).toReal) := by
  have h0 : covering_number dist ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty dist ε U hU))
  exact log2_ereal_eq_coe h0 (ne_of_lt hfin)

/-- Nonempty finite sets have finite-real entropy and finite positive covering
number at every positive precision. -/
theorem finite_entropy_data {dist : X → X → ENNReal} {U : Set X}
    (hd0 : ∀ x, dist x x = 0) (hU : U.Finite) (hUne : U.Nonempty)
    {ε : ENNReal} (hε : 0 < ε) :
    covering_number dist ε U < ⊤ ∧ 0 < covering_number dist ε U ∧
      ∃ a : ℝ, metric_entropy dist ε U = ↑a := by
  have hfin := covering_number_lt_top_of_finite hd0 hU hε
  refine ⟨hfin, lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty dist ε U hUne),
    Real.logb 2 (covering_number dist ε U).toReal,
    metric_entropy_eq_coe_of_cover_finite hUne hfin⟩

/-- Note after Definition 3.6: mapping entropy difference is well-defined on
nonempty finite sets, with both entropies finite real. -/
theorem entropyDelta_finite (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    {U : Set X} (hU : U.Finite) (hUne : U.Nonempty)
    (Jin Jout : Set I) {ε : ENNReal} (hε : 0 < ε) :
    EntropyDeltaAdmissible d Jin Jout ε φ U ∧
      (∃ a : ℝ, subfamily_metric_entropy d Jin ε U = ↑a) ∧
      (∃ b : ℝ, subfamily_metric_entropy d Jout ε (φ.func '' U) = ↑b) := by
  have hself : ∀ (J : Set I) (x : X), subfamily_pseudometric d J x x = 0 := by
    intro J x
    exact subfamily_zero_iff.mpr (fun j hj => (hd j).dist_self x)
  have hin := finite_entropy_data (hself Jin) hU hUne hε
  have himgFin : (φ.func '' U).Finite := hU.image φ.func
  have himgNe : (φ.func '' U).Nonempty := hUne.image φ.func
  have hout := finite_entropy_data (hself Jout) himgFin himgNe hε
  exact ⟨Or.inl hin.1, hin.2.2, hout.2.2⟩

end FiniteEntropy

section IdentityCoverage

variable (d : I → X → X → ENNReal)

/-- Forward centre-push for an isometry on the evaluation domain. -/
theorem covering_number_image_le_of_isometry (φ : Operator X bot) {j : I} {U : Set X}
    (hdist : ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) = d j x y) (ε : ENNReal) :
    covering_number (d j) ε (φ.func '' U) ≤ covering_number (d j) ε U := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  let T := S.image φ.func
  have hT : InternalEpsilonNet (d j) ε (φ.func '' U) T := by
    constructor
    · intro t ht
      change t ∈ T at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨s, hS.1 hs, rfl⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨s, hs, hxs⟩ := hS.2 x hx
      exact ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, by rw [hdist x hx s (hS.1 hs)]; exact hxs⟩
  exact (covering_number_le_of_net hT).trans (by exact_mod_cast Finset.card_image_le)

/-- Reverse centre-pullback for an isometry on the evaluation domain. -/
theorem covering_number_le_image_of_isometry (φ : Operator X bot) {j : I} {U : Set X}
    (hdist : ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) = d j x y) (ε : ENNReal) :
    covering_number (d j) ε U ≤ covering_number (d j) ε (φ.func '' U) := by
  classical
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  let pre : X → X := fun t => if ht : t ∈ φ.func '' U then Classical.choose ht else bot
  have pre_mem (t : X) (ht : t ∈ T) : pre t ∈ U := by
    have ht' : t ∈ φ.func '' U := hT.1 ht
    simp only [pre, dif_pos ht']
    exact (Classical.choose_spec ht').1
  have pre_spec (t : X) (ht : t ∈ T) : φ.func (pre t) = t := by
    have ht' : t ∈ φ.func '' U := hT.1 ht
    simp only [pre, dif_pos ht']
    exact (Classical.choose_spec ht').2
  let S := T.image pre
  have hS : InternalEpsilonNet (d j) ε U S := by
    constructor
    · intro s hs
      change s ∈ S at hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact pre_mem t ht
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := hT.2 (φ.func x) ⟨x, hx, rfl⟩
      refine ⟨pre t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
      rw [← hdist x hx (pre t) (pre_mem t ht), pre_spec t ht]
      exact hxt
  exact (covering_number_le_of_net hS).trans (by exact_mod_cast Finset.card_image_le)

end IdentityCoverage

section EntropyDeltaBounds

variable [Fintype I] (d : I → X → X → ENNReal)

/-- Proposition 3.18(i). -/
theorem constComponent_entropyDelta (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {U : Set X} (hU : U.Nonempty) {j : I}
    (hj : j ∈ constComponents d φ U) {ε : ENNReal} (hε : 0 < ε) :
    covering_number (d j) ε (φ.func '' U) = 1 ∧
      metric_entropy (d j) ε (φ.func '' U) = 0 ∧
      entropyDelta d ({j} : Set I) ({j} : Set I) ε φ U = metric_entropy (d j) ε U := by
  have hN := covering_number_image_eq_one_of_const d φ hU hj ε hε
  refine ⟨hN, ?_, ?_⟩
  · simp [metric_entropy, hN, log2_ereal]
  · rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]
    simp [metric_entropy, hN, log2_ereal]

/-- Proposition 3.18(ii-a). -/
theorem idComponent_covering_entropy_eq (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {U : Set X} {j : I} (hj : j ∈ idComponents d φ U) (ε : ENNReal) :
    covering_number (d j) ε (φ.func '' U) = covering_number (d j) ε U ∧
      metric_entropy (d j) ε (φ.func '' U) = metric_entropy (d j) ε U := by
  have hdist := idComponent_dist_eq d hd φ U hj
  have hN := le_antisymm (covering_number_image_le_of_isometry d φ hdist ε)
    (covering_number_le_image_of_isometry d φ hdist ε)
  exact ⟨hN, by simp [metric_entropy, hN]⟩

/-- Proposition 3.18(ii-b): only the admissible case is subtracted. -/
theorem idComponent_entropyDelta_eq_zero (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {U : Set X} (hU : U.Nonempty) {j : I}
    (hj : j ∈ idComponents d φ U) {ε : ENNReal}
    (hadm : EntropyDeltaAdmissible d ({j} : Set I) ({j} : Set I) ε φ U) :
    entropyDelta d ({j} : Set I) ({j} : Set I) ε φ U = 0 := by
  have hN := (idComponent_covering_entropy_eq d hd φ hj ε).1
  have hfin : covering_number (d j) ε U < ⊤ := by
    cases hadm with
    | inl h => simpa [subfamily_pseudometric_singleton] using h
    | inr h => rw [subfamily_pseudometric_singleton, hN] at h; exact h
  have h0 : covering_number (d j) ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty (d j) ε U hU))
  have hent := metric_entropy_eq_coe_of_cover_finite hU hfin
  rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]
  rw [(idComponent_covering_entropy_eq d hd φ hj ε).2, hent]
  exact EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)

/-- Proposition 3.19, covering-number inequality at precision `ε / L`. -/
theorem covering_number_image_le_of_scalar_lip
    (φ : Operator X bot) {i j : I} {U : Set X} {L ε : ENNReal}
    (hL0 : 0 < L) (hLtop : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ L * d i x y) :
    covering_number (d j) ε (φ.func '' U) ≤ covering_number (d i) (ε / L) U := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  let T := S.image φ.func
  have hT : InternalEpsilonNet (d j) ε (φ.func '' U) T := by
    constructor
    · intro t ht
      change t ∈ T at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨s, hS.1 hs, rfl⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨s, hs, hxs⟩ := hS.2 x hx
      refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
      apply lt_of_le_of_lt (hLip x hx s (hS.1 hs))
      calc
        L * d i x s < L * (ε / L) := ENNReal.mul_lt_mul_right (ne_of_gt hL0) (ne_of_lt hLtop) hxs
        _ = ε := by rw [mul_comm]; exact ENNReal.div_mul_cancel (ne_of_gt hL0) (ne_of_lt hLtop)
  exact (covering_number_le_of_net hT).trans (by exact_mod_cast Finset.card_image_le)

/-- Proposition 3.20, covering-number lower bound from pulling back internal
output centres. -/
theorem covering_number_le_image_of_colip
    (φ : Operator X bot) {i j : I} {U : Set X} (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d φ U K) {ε : ENNReal}
    (hK0 : 0 < K i j) (hKtop : K i j < ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (φ.func '' U) := by
  classical
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  let pre : X → X := fun t => if ht : t ∈ φ.func '' U then Classical.choose ht else bot
  have pre_mem (t : X) (ht : t ∈ T) : pre t ∈ U := by
    have ht' : t ∈ φ.func '' U := hT.1 ht
    simp only [pre, dif_pos ht']
    exact (Classical.choose_spec ht').1
  have pre_spec (t : X) (ht : t ∈ T) : φ.func (pre t) = t := by
    have ht' : t ∈ φ.func '' U := hT.1 ht
    simp only [pre, dif_pos ht']
    exact (Classical.choose_spec ht').2
  let S := T.image pre
  have hS : InternalEpsilonNet (d i) (ε / K i j) U S := by
    constructor
    · intro s hs
      change s ∈ S at hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact pre_mem t ht
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := hT.2 (φ.func x) ⟨x, hx, rfl⟩
      refine ⟨pre t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
      have hsingle : K i j * d i x (pre t) ≤ ∑ k : I, K k j * d k x (pre t) := by
        exact Finset.single_le_sum (fun k hk => zero_le (K k j * d k x (pre t))) (Finset.mem_univ i)
      have hco := hK.2.2 x hx (pre t) (pre_mem t ht) j
      have hlt : K i j * d i x (pre t) < ε := by
        apply hsingle.trans_lt
        apply hco.trans_lt
        rw [pre_spec t ht]
        exact hxt
      apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hK0)) (Or.inl (ne_of_lt hKtop))).mpr
      simpa [mul_comm] using hlt
  exact (covering_number_le_of_net hS).trans (by exact_mod_cast Finset.card_image_le)

/-- Proposition 3.19: finite positive `L` gives the stated entropy-difference
lower bound; total boundedness makes all three entropies finite real. -/
theorem entropyDelta_ge_of_scalar_lip
    (φ : Operator X bot) {i j : I} {U : Set X} (hU : U.Nonempty)
    (htb : InternallyTotallyBounded (d i) U) {L ε : ENNReal}
    (hε0 : 0 < ε) (hεtop : ε < ⊤) (hL0 : 0 < L) (hLtop : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ L * d i x y) :
    EntropyDeltaAdmissible d ({i} : Set I) ({j} : Set I) ε φ U ∧
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        entropyDelta d ({i} : Set I) ({j} : Set I) ε φ U := by
  have hdiv0 : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε0) (ne_of_lt hLtop)
  have hdivtop : ε / L < ⊤ := ENNReal.div_lt_top (ne_of_lt hεtop) (ne_of_gt hL0)
  have hfinA := htb ε hε0 hεtop
  have hfinB := htb (ε / L) hdiv0 hdivtop
  have hN := covering_number_image_le_of_scalar_lip d φ hL0 hLtop hLip (ε := ε)
  have hfinC : covering_number (d j) ε (φ.func '' U) < ⊤ := hN.trans_lt hfinB
  have hA := metric_entropy_eq_coe_of_cover_finite hU hfinA
  have hB := metric_entropy_eq_coe_of_cover_finite hU hfinB
  have hC := metric_entropy_eq_coe_of_cover_finite (hU.image φ.func) hfinC
  have hlog : metric_entropy (d j) ε (φ.func '' U) ≤ metric_entropy (d i) (ε / L) U :=
    log2_ereal_monotone hN
  rw [hB, hC] at hlog
  refine ⟨Or.inl (by simpa [subfamily_pseudometric_singleton] using hfinA), ?_⟩
  rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton,
    hA, hB, hC, ← EReal.coe_sub, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left (EReal.coe_le_coe_iff.mp hlog) _)

/-- Proposition 3.20: the co-Lip entropy-difference upper bound.  The output
entropy may be infinite, in which case the left side is `-∞`. -/
theorem entropyDelta_le_of_colip
    (φ : Operator X bot) {i j : I} {U : Set X} (hU : U.Nonempty)
    (htb : InternallyTotallyBounded (d i) U) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d φ U K) {ε : ENNReal}
    (hε0 : 0 < ε) (hεtop : ε < ⊤) (hK0 : 0 < K i j) (hKtop : K i j < ⊤) :
    EntropyDeltaAdmissible d ({i} : Set I) ({j} : Set I) ε φ U ∧
      entropyDelta d ({i} : Set I) ({j} : Set I) ε φ U ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hdiv0 : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε0) (ne_of_lt hKtop)
  have hdivtop : ε / K i j < ⊤ := ENNReal.div_lt_top (ne_of_lt hεtop) (ne_of_gt hK0)
  have hfinA := htb ε hε0 hεtop
  have hfinB := htb (ε / K i j) hdiv0 hdivtop
  have hN := covering_number_le_image_of_colip d φ K hK hK0 hKtop (ε := ε)
  have hA := metric_entropy_eq_coe_of_cover_finite hU hfinA
  have hB := metric_entropy_eq_coe_of_cover_finite hU hfinB
  have hlog : metric_entropy (d i) (ε / K i j) U ≤ metric_entropy (d j) ε (φ.func '' U) :=
    log2_ereal_monotone hN
  refine ⟨Or.inl (by simpa [subfamily_pseudometric_singleton] using hfinA), ?_⟩
  rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]
  by_cases hCtop : covering_number (d j) ε (φ.func '' U) = ⊤
  · have hC : metric_entropy (d j) ε (φ.func '' U) = ⊤ := by simp [metric_entropy, log2_ereal, hCtop]
    rw [hA, hB, hC, EReal.sub_top]
    exact bot_le
  · have hfinC : covering_number (d j) ε (φ.func '' U) < ⊤ := lt_top_iff_ne_top.mpr hCtop
    have hC := metric_entropy_eq_coe_of_cover_finite (hU.image φ.func) hfinC
    rw [hB, hC] at hlog
    rw [hA, hB, hC, ← EReal.coe_sub, ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left (EReal.coe_le_coe_iff.mp hlog) _)

end EntropyDeltaBounds

end OET.Ch03
