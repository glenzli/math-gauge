import CH03.Core3

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X : Type} {I : Type} {bot : X}

/-! ## Covering and entropy interface (D07) -/

/-- Total boundedness on a set: every finite positive precision admits a finite
internal cover. -/
def TotallyBoundedOn (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε ≠ ⊤ → covering_number d ε U ≠ ⊤

theorem covering_number_le_card_of_net {d : X → X → ENNReal} {ε : ENNReal}
    {U : Set X} {S : Finset X} (hS : InternalEpsilonNet d ε U S) :
    covering_number d ε U ≤ (S.card : ENNReal) := by
  unfold covering_number
  exact iInf_le_of_le S (iInf_le_of_le hS le_rfl)

theorem log2_ereal_mono {a b : ENNReal} (h : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  by_cases ha0 : a = 0
  · simp [log2_ereal, ha0]
  · by_cases hb0 : b = 0
    · have hab : a ≤ 0 := by simpa [hb0] using h
      exact False.elim (ha0 (le_antisymm hab (zero_le _)))
    · by_cases hbt : b = ⊤
      · simp [log2_ereal, ha0, hb0, hbt]
      · have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt h
        simp only [log2_ereal, if_neg ha0, if_neg hat, if_neg hb0, if_neg hbt]
        exact EReal.coe_le_coe
          (Real.logb_le_logb_of_le one_lt_two
            (ENNReal.toReal_pos ha0 hat) (ENNReal.toReal_mono hbt h))

theorem covering_number_eq_one_of_forall_zero
    (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty) (ε : ENNReal)
    (hε : 0 < ε) (hzero : ∀ x ∈ U, ∀ y ∈ U, d x y = 0) :
    covering_number d ε U = 1 := by
  apply le_antisymm
  · rcases hU with ⟨x0, hx0⟩
    have hnet : InternalEpsilonNet d ε U {x0} := by
      constructor
      · intro x hx
        have hx' : x = x0 := by simpa using hx
        simpa [hx'] using hx0
      · intro x hx
        refine ⟨x0, by simp, ?_⟩
        rw [hzero x hx x0 hx0]
        exact hε
    calc
      covering_number d ε U ≤ (({x0} : Finset X).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 1 := by simp
  · exact one_le_covering_number_of_nonempty d ε U hU

/-! ## Proposition 3.16 -/

theorem threshold_ball_subset_fiber
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τN : ENNReal}
    (hth : τN ≤ zeroingMatrix d φ A j i) :
    ∀ x ∈ A, ∀ y ∈ A, d i y x < τN →
      y ∈ Fiber d φ ({j} : Set I) (φ.func x) A := by
  intro x hx y hya hy
  refine ⟨hya, ?_⟩
  intro k hk
  simp only [Set.mem_singleton_iff] at hk
  subst k
  apply below_unified_radius_output_zero d hd φ A i j hya hx
  exact lt_of_lt_of_le hy hth

theorem covering_number_image_le_of_threshold
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τN : ENNReal}
    (hτpos : 0 < τN) (hth : τN ≤ zeroingMatrix d φ A j i)
    (B : Set X) (hBA : B ⊆ A) (ε : ENNReal) (hε : 0 < ε) :
    covering_number (d j) ε (φ.func '' B) ≤ covering_number (d i) τN B := by
  classical
  by_cases hfin : ∃ S : Finset X, InternalEpsilonNet (d i) τN B S
  · obtain ⟨S, hS, hcover, hmin⟩ :=
      covering_number_attained (d i) τN B hfin
    have hSimg : InternalEpsilonNet (d j) ε (φ.func '' B) (S.image φ.func) := by
      constructor
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
        exact ⟨s, hS.1 hs, rfl⟩
      · intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        rcases hS.2 a ha with ⟨s, hs, hdist⟩
        refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
        have hsA : s ∈ A := hBA (hS.1 hs)
        have haA : a ∈ A := hBA ha
        have hfib := threshold_ball_subset_fiber d hd φ A i j hth s hsA a haA hdist
        have hout := hfib.2 j (by simp)
        exact lt_of_le_of_lt (le_of_eq hout) hε
    calc
      covering_number (d j) ε (φ.func '' B)
          ≤ ((S.image φ.func).card : ENNReal) := covering_number_le_card_of_net hSimg
      _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
      _ = covering_number (d i) τN B := hcover.symm
  · have htop : covering_number (d i) τN B = ⊤ :=
      (covering_number_eq_top_iff (d i) τN B).mpr hfin
    rw [htop]
    exact le_top

theorem entropy_image_le_of_threshold
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τN : ENNReal}
    (hτpos : 0 < τN) (hτtop : τN ≠ ⊤)
    (hth : τN ≤ zeroingMatrix d φ A j i)
    (B : Set X) (hBA : B ⊆ A) (hB : B.Nonempty) (ε : ENNReal) (hε : 0 < ε) :
    metric_entropy (d j) ε (φ.func '' B) ≤ metric_entropy (d i) τN B := by
  unfold metric_entropy
  exact log2_ereal_mono
    (covering_number_image_le_of_threshold d hd φ A i j hτpos hth B hBA ε hε)

/-! ## Corollary 3.17 -/

theorem small_domain_zeroing_iff
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τσ τN : ENNReal}
    (hA : A.Nonempty) (hτpos : 0 < τN) (hτtop : τN ≠ ⊤)
    (hdiam : diameterScale d i A < τσ) (hτ : τσ ≤ τN) :
    τN ≤ zeroingMatrix d φ A j i ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (φ.func x) (φ.func y) = 0 := by
  constructor
  · intro hth x hx y hy
    have hdiamxy : d i x y ≤ diameterScale d i A := by
      exact le_iSup_of_le (⟨x, hx⟩ : {x : X // x ∈ A})
        (le_iSup_of_le (⟨y, hy⟩ : {y : X // y ∈ A}) le_rfl)
    have hlt : d i x y < zeroingMatrix d φ A j i :=
      lt_of_le_of_lt hdiamxy (lt_of_lt_of_le hdiam (le_trans hτ hth))
    exact below_unified_radius_output_zero d hd φ A i j hx hy hlt
  · intro hzero
    have hmat_top : zeroingMatrix d φ A j i = ⊤ := by
      apply le_antisymm le_top
      apply le_iInf
      intro x
      change ⊤ ≤ pointwiseRadius (d i) (fun a b => d j a b = 0) φ x.1 A
      exact top_le_iff.mpr (pointwiseRadius_eq_top_iff.mpr (by
        intro r hr0 hrtop
        refine ⟨hr0, hrtop, ?_⟩
        intro y hy _
        exact hzero y hy x.1 x.2))
    rw [hmat_top]
    exact le_top

theorem small_domain_image_covering_eq_one
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τσ τN ε : ENNReal}
    (hA : A.Nonempty) (hτpos : 0 < τN) (hτtop : τN ≠ ⊤)
    (hdiam : diameterScale d i A < τσ) (hτ : τσ ≤ τN)
    (hth : τN ≤ zeroingMatrix d φ A j i) (hε : 0 < ε) :
    covering_number (d j) ε (φ.func '' A) = 1 := by
  have hzero : ∀ x ∈ A, ∀ y ∈ A, d j (φ.func x) (φ.func y) = 0 :=
    (small_domain_zeroing_iff d hd φ A i j hA hτpos hτtop hdiam hτ).mp hth
  apply covering_number_eq_one_of_forall_zero (d j) (φ.func '' A)
  · rcases hA with ⟨x, hx⟩
    exact ⟨φ.func x, ⟨x, hx, rfl⟩⟩
  · exact hε
  · intro u hu v hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    exact hzero x hx y hy

/-! ## Finite sets and entropy differences (D08, Notes 3.22) -/

theorem finite_set_covering_ne_top
    (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hUfin : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    covering_number d ε U ≠ ⊤ := by
  intro htop
  have hnet : InternalEpsilonNet d ε U hUfin.toFinset := by
    constructor
    · intro x hx
      exact hUfin.mem_toFinset.mp hx
    · intro x hx
      refine ⟨x, hUfin.mem_toFinset.mpr hx, ?_⟩
      rw [hself x]
      exact hε
  have hle := covering_number_le_card_of_net hnet
  rw [htop] at hle
  exact ENNReal.natCast_ne_top hUfin.toFinset.card (top_le_iff.mp hle)

theorem finite_set_metric_entropy_ne_top
    (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hUfin : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    metric_entropy d ε U ≠ ⊤ := by
  have htop := finite_set_covering_ne_top d hself U hUfin hε
  unfold metric_entropy
  by_cases h0 : covering_number d ε U = 0
  · simp [log2_ereal, h0]
  · simp [log2_ereal, h0, htop]

theorem metric_entropy_ne_bot_of_nonempty
    (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty) (ε : ENNReal) :
    metric_entropy d ε U ≠ ⊥ := by
  have hnonneg := metric_entropy_nonneg d ε U hU
  intro hbot
  have h : (0 : EReal) ≤ ⊥ := by simpa [hbot] using hnonneg
  exact (not_le_of_gt (EReal.bot_lt_coe 0)) h

noncomputable def erealSub (a b : EReal) : EReal :=
  if a = ⊤ then (if b = ⊤ then 0 else ⊤)
  else if a = ⊥ then (if b = ⊥ then 0 else ⊥)
  else if b = ⊤ then ⊥
  else if b = ⊥ then ⊤
  else ↑(a.toReal - b.toReal)

theorem erealSub_coe_coe (x y : ℝ) : erealSub ↑x ↑y = ↑(x - y) := by
  simp [erealSub]

theorem erealSub_self (a : EReal) : erealSub a a = 0 := by
  by_cases htop : a = ⊤
  · simp [erealSub, htop]
  · by_cases hbot : a = ⊥
    · simp [erealSub, hbot]
    · have hcoe : a = ↑a.toReal := (EReal.coe_toReal htop hbot).symm
      rw [hcoe]
      simp [erealSub]

theorem erealSub_eq_self_of_right_zero {a : EReal} (hbot : a ≠ ⊥) :
    erealSub a 0 = a := by
  by_cases htop : a = ⊤
  · simp [erealSub, htop]
  · have hcoe : a = ↑a.toReal := (EReal.coe_toReal htop hbot).symm
    rw [hcoe]
    norm_num [erealSub]

noncomputable def mappingEntropyDiff
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : EReal :=
  erealSub (subfamily_metric_entropy d Jin ε U)
    (subfamily_metric_entropy d Jout ε (φ.func '' U))

/-- The entropy difference is defined when not both entropies are `+∞`. -/
def MappingEntropyDiffWellDefined
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  subfamily_metric_entropy d Jin ε U ≠ ⊤ ∨
    subfamily_metric_entropy d Jout ε (φ.func '' U) ≠ ⊤

end formal_oet.vol_01.ch_03_operator_local_degeneracy
