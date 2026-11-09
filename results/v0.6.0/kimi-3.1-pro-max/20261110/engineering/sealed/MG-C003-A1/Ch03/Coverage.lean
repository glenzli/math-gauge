import Ch03.Radius

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X I : Type} {bot : X}

section Thresholds

/-- Lemma 3.13: the four threshold combinations are exhaustive. -/
theorem thresholdType_four_cases (σ : InputScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (hA : A.Nonempty) (τσ τN : ENNReal) (i j : I) :
    thresholdType σ d f A hA τσ τN i j = (1, 1) ∨
      thresholdType σ d f A hA τσ τN i j = (1, 0) ∨
      thresholdType σ d f A hA τσ τN i j = (0, 1) ∨
      thresholdType σ d f A hA τσ τN i j = (0, 0) := by
  unfold thresholdType
  by_cases h1 : σ.scale i ⟨A, hA⟩ < τσ <;> by_cases h2 :
    componentUniformAnnihilationRadius d f i ({j} : Set I) A ≥ τN <;>
    simp [h1, h2]

/-- Lemma 3.13(i): increasing the scale threshold enlarges the first-indicator
one set. -/
theorem threshold_first_monotone (σ : InputScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (hA : A.Nonempty) {τσ τσ' τN : ENNReal}
    (hτ : τσ ≤ τσ') :
    {p : I × I | (thresholdType σ d f A hA τσ τN p.1 p.2).1 = 1} ⊆
      {p : I × I | (thresholdType σ d f A hA τσ' τN p.1 p.2).1 = 1} := by
  rintro ⟨i, j⟩ hp
  by_cases h : σ.scale i ⟨A, hA⟩ < τσ
  · have h' : σ.scale i ⟨A, hA⟩ < τσ' := h.trans_le hτ
    simp [thresholdType, h, h']
  · simp [thresholdType, h] at hp

/-- Lemma 3.13(ii): increasing the annihilation threshold shrinks the
second-indicator one set. -/
theorem threshold_second_antitone (σ : InputScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (hA : A.Nonempty) {τσ τN τN' : ENNReal}
    (hτ : τN ≤ τN') :
    {p : I × I | (thresholdType σ d f A hA τσ τN' p.1 p.2).2 = 1} ⊆
      {p : I × I | (thresholdType σ d f A hA τσ τN p.1 p.2).2 = 1} := by
  rintro ⟨i, j⟩ hp
  by_cases h : componentUniformAnnihilationRadius d f i ({j} : Set I) A ≥ τN'
  · have h' : componentUniformAnnihilationRadius d f i ({j} : Set I) A ≥ τN := hτ.trans h
    simp [thresholdType, h, h']
  · simp [thresholdType, h] at hp

/-- Proposition 3.14(i), for an arbitrary monotone input scale family. -/
theorem scale_domain_antitone (σ : InputScaleFamily X I) {A B : Set X}
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A) (i : I) :
    σ.scale i ⟨B, hB⟩ ≤ σ.scale i ⟨A, hA⟩ := σ.monotone i hBA

theorem scale_threshold_of_subset (σ : InputScaleFamily X I) {A B : Set X}
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A) {τσ : ENNReal}
    (h : σ.scale i ⟨A, hA⟩ < τσ) : σ.scale i ⟨B, hB⟩ < τσ :=
  (scale_domain_antitone σ hA hB hBA i).trans_lt h

end Thresholds

section Log

/-- Monotonicity of the frozen base-two logarithm on `ENNReal`, including the
`0 ↦ -∞` and `+∞ ↦ +∞` conventions. -/
theorem log2_ereal_monotone {a b : ENNReal} (hab : a ≤ b) : log2_ereal a ≤ log2_ereal b := by
  by_cases ha0 : a = 0
  · simp [log2_ereal, ha0]
  by_cases hbtop : b = ⊤
  · simp [log2_ereal, hbtop]
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    exact ha0 (le_antisymm hab (zero_le _))
  have hatop : a ≠ ⊤ := by
    intro ha
    subst a
    exact hbtop (top_unique hab)
  simp only [log2_ereal, if_neg ha0, if_neg hatop, if_neg hb0, if_neg hbtop]
  apply EReal.coe_le_coe_iff.mpr
  exact Real.logb_le_logb_of_le one_lt_two (ENNReal.toReal_pos ha0 hatop)
    (ENNReal.toReal_mono hbtop hab)

theorem log2_ereal_eq_coe {a : ENNReal} (ha0 : a ≠ 0) (hatop : a ≠ ⊤) :
    log2_ereal a = ↑(Real.logb 2 a.toReal) := by simp [log2_ereal, ha0, hatop]

end Log

section Coverage

variable [Fintype I] (d : I → X → X → ENNReal)

/-- Proposition 3.16(i). -/
theorem ball_subset_fib_of_uniformRadius_ge (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A : Set X} {τN : ENNReal}
    (hτ : τN ≤ uniformAnnihilationRadiusOn f (d i) (d j) A) (x : X) (hx : x ∈ A) :
    ball (d i) x τN ∩ A ⊆ FibSingle d f j (f.func x) A := by
  intro y hy
  refine ⟨hy.2, ?_⟩
  have hdist : d i y x < uniformAnnihilationRadiusOn f (d i) (d j) A :=
    lt_of_lt_of_le hy.1 (hτ)
  exact output_zero_of_dist_lt_uniformRadius d hd f hy.2 hx hdist

/-- Proposition 3.16(ii-a): map every internal input centre and take the
infimum over all input nets.  This also covers empty `B` and the absence of a
finite input cover. -/
theorem covering_number_image_le_of_uniformRadius_ge
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A B : Set X} {ε τN : ENNReal}
    (hε : 0 < ε) (hBA : B ⊆ A) (hτ : τN ≤ uniformAnnihilationRadiusOn f (d i) (d j) A) :
    covering_number (d j) ε (f.func '' B) ≤ covering_number (d i) τN B := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  let T : Finset X := S.image f.func
  have hT : InternalEpsilonNet (d j) ε (f.func '' B) T := by
    constructor
    · intro t ht
      change t ∈ T at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨s, hS.1 hs, rfl⟩
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨s, hs, has⟩ := hS.2 a ha
      refine ⟨f.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
      have hzero : d j (f.func a) (f.func s) = 0 := by
        apply output_zero_of_dist_lt_uniformRadius d hd f (hBA ha) (hBA (hS.1 hs))
        exact has.trans_le hτ
      rw [hzero]
      exact hε
  calc
    covering_number (d j) ε (f.func '' B) ≤ (T.card : ENNReal) := covering_number_le_of_net hT
    _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le

/-- Proposition 3.16(ii-b). -/
theorem metric_entropy_image_le_of_uniformRadius_ge
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A B : Set X} {ε τN : ENNReal}
    (hε : 0 < ε) (hBA : B ⊆ A) (hτ : τN ≤ uniformAnnihilationRadiusOn f (d i) (d j) A) :
    metric_entropy (d j) ε (f.func '' B) ≤ metric_entropy (d i) τN B := by
  exact log2_ereal_monotone (covering_number_image_le_of_uniformRadius_ge d hd f hε hBA hτ)

/-- Corollary 3.17, exact equivalence under `diam < τσ ≤ τN`. -/
theorem uniformRadius_ge_iff_output_zero_of_diam_lt
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A : Set X} (hA : A.Nonempty)
    {τσ τN : ENNReal} (hdiam : diameter (d i) A < τσ) (hτ : τσ ≤ τN) :
    τN ≤ uniformAnnihilationRadiusOn f (d i) (d j) A ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro hr x hx y hy
    apply output_zero_of_dist_lt_uniformRadius d hd f hx hy
    calc
      d i x y ≤ diameter (d i) A := by
        exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
      _ < τσ := hdiam
      _ ≤ τN := hτ
      _ ≤ uniformAnnihilationRadiusOn f (d i) (d j) A := hr
  · intro hzero
    have hc : j ∈ constComponents d f A := hzero
    have h := uniformRadius_top_of_const_subfamily d f hA
      (J := ({j} : Set I)) (fun k hk => by rw [show k = j from hk]; exact hc) i
    rw [componentUniformRadius_single] at h
    rw [h.2]
    exact le_top

/-- Corollary 3.17: a nonempty zero-distance image has internal covering
number exactly one at every precision. -/
theorem covering_number_image_eq_one_of_const
    (f : Operator X bot) {j : I} {A : Set X} (hA : A.Nonempty)
    (hzero : ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0) (ε : ENNReal) (hε : 0 < ε) :
    covering_number (d j) ε (f.func '' A) = 1 := by
  obtain ⟨a, ha⟩ := hA
  apply le_antisymm
  · have hnet : InternalEpsilonNet (d j) ε (f.func '' A) {f.func a} := by
      constructor
      · simp only [Finset.coe_singleton, singleton_subset_iff]
        exact ⟨a, ha, rfl⟩
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨f.func a, Finset.mem_singleton_self _, by rw [hzero x hx a ha]; exact hε⟩
    simpa using covering_number_le_of_net hnet
  · exact one_le_covering_number_of_nonempty (d j) ε (f.func '' A) ⟨f.func a, ⟨a, ha, rfl⟩⟩

end Coverage

end OET.Ch03
