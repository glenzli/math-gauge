/-
Formalization of Chapter 3 (Sections 3.4 & 3.5: Input Scale, Threshold Classification,
Local Nullification, and Covering Numbers)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.NullificationRadius

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.4: Input Scale Family and Threshold Classification (CH03-D06) -/

/-- Monotone input scale family `σ_i` on nonempty subsets of `X`. -/
structure InputScaleFamily (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i : I, ∀ A₁ A₂ : Set X, A₁.Nonempty → A₁ ⊆ A₂ → scale i A₁ ≤ scale i A₂

/-- Default diameter scale `diam_{d_i}(A) = sup_{x, y ∈ A} d_i(x, y)`. -/
noncomputable def diamScaleFun {X I : Type} (d : I → X → X → ENNReal) (i : I) (A : Set X) :
    ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d i x y

/-- The diameter scale family satisfies the input scale monotonicity axiom. -/
noncomputable def diamScale {X I : Type} (d : I → X → X → ENNReal) : InputScaleFamily X I where
  scale := diamScaleFun d
  mono := by
    intro i A₁ A₂ _ hsub
    apply iSup₂_le
    intro x hx
    apply iSup₂_le
    intro y hy
    exact le_iSup₂_of_le x (hsub hx) (le_iSup₂_of_le y (hsub hy) le_rfl)

/-- Threshold classification `Type_{f, A}(i, j) ∈ {0, 1}²` (represented as `Fin 2 × Fin 2`).
First entry is `1` iff `σ_i(A) < τ_σ`; second entry is `1` iff `\underline{r}^N_{f, i, j}|_A ≥ τ_N`. -/
noncomputable def thresholdType {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    (τ_σ τ_N : ENNReal) (f : Operator X bot) (A : Set X) (i j : I) : Fin 2 × Fin 2 :=
  (if σ.scale i A < τ_σ then 1 else 0,
   if τ_N ≤ uniformNullRadiusCompOn d f i j A then 1 else 0)

/-! ### Covering Number, Entropy, and Total Boundedness Interface (CH03-D07) -/

/-- Subfamily covering number `N_J(ε, U) := N(d_J, ε, U)`. -/
noncomputable def subfamily_covering_number {X I : Type}
    (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) ε U

theorem subfamily_covering_number_singleton {X I : Type}
    (d : I → X → X → ENNReal) (i : I) (ε : ENNReal) (U : Set X) :
    subfamily_covering_number d ({i} : Set I) ε U = covering_number (d i) ε U := by
  simp [subfamily_covering_number, subfamily_pseudometric_singleton]

/-- Total boundedness of `U` with respect to extended pseudometric `d`:
`N(r, U) < +∞` for every finite positive `r ∈ (0, +∞)`. -/
def IsTotallyBounded {X : Type} (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

/-- Correspondence between frozen `InternalEpsilonNet` and the textbook ball-union definition. -/
theorem internalEpsilonNet_iff_ball {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (centers : Finset X) :
    InternalEpsilonNet d ε U centers ↔
      (↑centers : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ centers, ball d c ε := by
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
    exact ⟨c, hc, hdist⟩

theorem covering_number_le_of_net {X : Type} {d : X → X → ENNReal}
    {ε : ENNReal} {U : Set X} {centers : Finset X}
    (hnet : InternalEpsilonNet d ε U centers) :
    covering_number d ε U ≤ (centers.card : ENNReal) :=
  iInf_le_of_le centers (iInf_le_of_le hnet le_rfl)

theorem le_covering_number_iff {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (k : ENNReal) :
    k ≤ covering_number d ε U ↔
      ∀ centers : Finset X, InternalEpsilonNet d ε U centers → k ≤ (centers.card : ENNReal) := by
  simp only [covering_number, le_iInf_iff]

theorem covering_number_eq_zero_iff {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) :
    covering_number d ε U = 0 ↔ U = ∅ := by
  constructor
  · intro h0
    by_contra hne
    have hnon : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have h1 := one_le_covering_number_of_nonempty d ε U hnon
    rw [h0] at h1
    exact not_le_of_gt zero_lt_one h1
  · intro heq
    subst heq
    exact covering_number_empty d ε

/-- Monotonicity of `log2_ereal` on `ENNReal`. -/
theorem log2_ereal_mono {a b : ENNReal} (hab : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  by_cases ha0 : a = 0
  · subst ha0
    simp [log2_ereal]
  · by_cases hbtop : b = ⊤
    · subst hbtop
      simp [log2_ereal]
    · have hatop : a ≠ ⊤ := ne_top_of_le_ne_top hbtop hab
      have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha0) hab)
      simp only [log2_ereal, if_neg ha0, if_neg hatop, if_neg hb0, if_neg hbtop]
      apply EReal.coe_le_coe_iff.mpr
      exact Real.logb_le_logb_of_le one_lt_two
        (ENNReal.toReal_pos ha0 hatop)
        (ENNReal.toReal_mono hbtop hab)

@[simp] theorem log2_ereal_one : log2_ereal 1 = 0 := by
  simp [log2_ereal]

@[simp] theorem log2_ereal_two : log2_ereal 2 = 1 := by
  have h20 : (2 : ENNReal) ≠ 0 := by simp
  have h2t : (2 : ENNReal) ≠ ⊤ := by simp
  simp only [log2_ereal, if_neg h20, if_neg h2t, ENNReal.toReal_ofNat]
  rw [Real.logb_self_eq_one one_lt_two]
  rfl

theorem metric_entropy_mono_of_covering_number_le {X Y : Type}
    {d₁ : X → X → ENNReal} {d₂ : Y → Y → ENNReal}
    {ε₁ ε₂ : ENNReal} {U₁ : Set X} {U₂ : Set Y}
    (h : covering_number d₁ ε₁ U₁ ≤ covering_number d₂ ε₂ U₂) :
    metric_entropy d₁ ε₁ U₁ ≤ metric_entropy d₂ ε₂ U₂ :=
  log2_ereal_mono h

theorem metric_entropy_eq_coe_of_nonempty_of_lt_top {X : Type}
    {d : X → X → ENNReal} {ε : ENNReal} {U : Set X}
    (hU : U.Nonempty) (hfin : covering_number d ε U < ⊤) :
    metric_entropy d ε U = ↑(Real.logb 2 (covering_number d ε U).toReal) := by
  have hne0 : covering_number d ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty d ε U hU))
  have hnetop : covering_number d ε U ≠ ⊤ := ne_of_lt hfin
  simp [metric_entropy, log2_ereal, hne0, hnetop]

theorem metric_entropy_eq_top_iff {X : Type}
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) :
    metric_entropy d ε U = ⊤ ↔ covering_number d ε U = ⊤ := by
  by_cases h0 : covering_number d ε U = 0
  · simp [metric_entropy, log2_ereal, h0]
  · by_cases ht : covering_number d ε U = ⊤
    · simp [metric_entropy, log2_ereal, ht]
    · simp [metric_entropy, log2_ereal, h0, ht]

/-! ### Lemma 3.13: Four-Way Threshold Classification and Monotonicity (CH03-P16-01..03) -/

/-- Lemma 3.13 (exhaustiveness and mutual exclusivity of the four cells). -/
theorem lemma_3_13_partition {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    (τ_σ τ_N : ENNReal) (f : Operator X bot) (A : Set X) (i j : I) :
    (thresholdType d σ τ_σ τ_N f A i j = (1, 1) ↔
        σ.scale i A < τ_σ ∧ τ_N ≤ uniformNullRadiusCompOn d f i j A) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (1, 0) ↔
        σ.scale i A < τ_σ ∧ uniformNullRadiusCompOn d f i j A < τ_N) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (0, 1) ↔
        τ_σ ≤ σ.scale i A ∧ τ_N ≤ uniformNullRadiusCompOn d f i j A) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (0, 0) ↔
        τ_σ ≤ σ.scale i A ∧ uniformNullRadiusCompOn d f i j A < τ_N) ∧
    (thresholdType d σ τ_σ τ_N f A i j = (1, 1) ∨
     thresholdType d σ τ_σ τ_N f A i j = (1, 0) ∨
     thresholdType d σ τ_σ τ_N f A i j = (0, 1) ∨
     thresholdType d σ τ_σ τ_N f A i j = (0, 0)) := by
  unfold thresholdType
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A <;>
      simp [h1, h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A
    · simp [h1, h2, not_lt.mpr h2]
    · simp [h1, h2, lt_of_not_ge h2]
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A
    · simp [h1, h2, not_le.mpr h1]
    · simp [h1, h2]
    · simp [h1, h2, le_of_not_gt h1]
    · simp [h1, h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A
    · simp [h1, h2]
    · simp [h1, h2, not_le.mpr h1]
    · simp [h1, h2, not_lt.mpr h2]
    · simp [h1, h2, le_of_not_gt h1, lt_of_not_ge h2]
  · by_cases h1 : σ.scale i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusCompOn d f i j A <;>
      simp [h1, h2]

/-- Lemma 3.13(i): Increasing `τ_σ` monotonically enlarges the set of channels with first entry `1`. -/
theorem lemma_3_13_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    {τ_σ τ_σ' : ENNReal} (τ_N : ENNReal) (f : Operator X bot) (A : Set X)
    (hτ : τ_σ ≤ τ_σ') :
    { p : I × I | (thresholdType d σ τ_σ τ_N f A p.1 p.2).1 = 1 } ⊆
      { p : I × I | (thresholdType d σ τ_σ' τ_N f A p.1 p.2).1 = 1 } := by
  intro ⟨i, j⟩ hp
  simp only [thresholdType, Set.mem_setOf_eq] at hp ⊢
  split_ifs at hp with hlt
  · rw [if_pos (lt_of_lt_of_le hlt hτ)]
  · exact ((by decide : (0 : Fin 2) ≠ 1) hp).elim

/-- Lemma 3.13(ii): Increasing `τ_N` monotonically shrinks the set of channels with second entry `1`. -/
theorem lemma_3_13_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : InputScaleFamily X I)
    (τ_σ : ENNReal) {τ_N τ_N' : ENNReal} (f : Operator X bot) (A : Set X)
    (hτ : τ_N ≤ τ_N') :
    { p : I × I | (thresholdType d σ τ_σ τ_N' f A p.1 p.2).2 = 1 } ⊆
      { p : I × I | (thresholdType d σ τ_σ τ_N f A p.1 p.2).2 = 1 } := by
  intro ⟨i, j⟩ hp
  simp only [thresholdType, Set.mem_setOf_eq] at hp ⊢
  split_ifs at hp with hge
  · rw [if_pos (le_trans hτ hge)]
  · exact ((by decide : (0 : Fin 2) ≠ 1) hp).elim

/-! ### Proposition 3.14: Monotonicity under Domain Refinement (CH03-P17-01..04) -/

/-- Proposition 3.14(i): For any monotone input scale family, `∅ ≠ B ⊆ A` implies
`σ_i(B) ≤ σ_i(A)` and preserves `σ_i(·) < τ_σ`. -/
theorem prop_3_14_i {X I : Type} {bot : X}
    (σ : InputScaleFamily X I) (f : Operator X bot) (A B : Set X) (i : I) (τ_σ : ENNReal)
    (hBne : B.Nonempty) (hBA : B ⊆ A) (_hAdom : A ⊆ dom f) :
    σ.scale i B ≤ σ.scale i A ∧ (σ.scale i A < τ_σ → σ.scale i B < τ_σ) := by
  have hle := σ.mono i B A hBne hBA
  exact ⟨hle, fun hlt => lt_of_le_of_lt hle hlt⟩

/-- Proposition 3.14(ii-a): Shrinking the evaluation domain from `A` to `B ⊆ A` does not
decrease the pointwise nullification radius at any fixed `x ∈ B`. -/
theorem prop_3_14_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X) (i j : I) {x : X}
    (hBA : B ⊆ A) (_hAdom : A ⊆ dom f) (_hxB : x ∈ B) :
    pointwiseNullRadiusComp d f i j A x ≤ pointwiseNullRadiusComp d f i j B x := by
  apply sSup_le
  intro r hr
  apply le_sSup
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro z hz hdist
  exact hr.2.2 z (hBA hz) hdist

/-- Proposition 3.14(ii-b): Simultaneously shrinking the evaluation domain and the infimum
base set from `A` to `B` does not decrease the uniform nullification radius. -/
theorem prop_3_14_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X) (i j : I)
    (_hBne : B.Nonempty) (hBA : B ⊆ A) (hAdom : A ⊆ dom f) :
    uniformNullRadiusCompOn d f i j A ≤ uniformNullRadiusCompOn d f i j B := by
  calc
    uniformNullRadiusCompOn d f i j A
        ≤ uniformNullRadius (d i) (d j) f B A := by
          apply le_iInf₂
          intro x hxB
          exact iInf₂_le x (hBA hxB)
    _ ≤ uniformNullRadiusCompOn d f i j B := by
          apply le_iInf₂
          intro x hxB
          exact le_trans (iInf₂_le x hxB) (prop_3_14_ii_a d f A B i j hBA hAdom hxB)

/-- Proposition 3.14(iii): Counterexample showing the reverse scale judgment fails
(`A = {0, 1}`, `B = {0}`, `τ_σ = 1/2` on `ℝ ⊔ {⊥}`). -/
theorem prop_3_14_iii_counterexample :
    let d : Unit → RealWithBot → RealWithBot → ENNReal := fun _ => realWithBotDist
    let A : Set RealWithBot := {some 0, some 1}
    let B : Set RealWithBot := {some 0}
    let τ_σ : ENNReal := ENNReal.ofReal (1 / 2)
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot none (d u)) ∧
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (@operator_identity RealWithBot none) ∧
    0 < τ_σ ∧ τ_σ < ⊤ ∧
    diamScaleFun d () B = 0 ∧
    diamScaleFun d () B < τ_σ ∧
    diamScaleFun d () A = 1 ∧
    τ_σ ≤ diamScaleFun d () A := by
  intro d A B τ_σ
  have hdiamB : diamScaleFun d () B = 0 := by
    apply le_antisymm _ (zero_le _)
    apply iSup₂_le; intro x hx
    apply iSup₂_le; intro y hy
    rcases hx with rfl; rcases hy with rfl
    simp [d, realWithBotDist]
  have hdiamA : diamScaleFun d () A = 1 := by
    apply le_antisymm
    · apply iSup₂_le; intro x hx
      apply iSup₂_le; intro y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [d, realWithBotDist]
    · apply le_iSup₂_of_le (some 0) (Or.inl rfl)
      apply le_iSup₂_of_le (some 1) (Or.inr rfl)
      simp [d, realWithBotDist]
  have hτ_pos : 0 < τ_σ := ENNReal.ofReal_pos.mpr (by norm_num)
  have hτ_fin : τ_σ < ⊤ := ENNReal.ofReal_lt_top
  have hτ_le1 : τ_σ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine ⟨fun _ => realWithBotDist_extendedPseudoMetric, ⟨some 0, rfl⟩,
    by intro x hx; rcases hx with rfl; exact Or.inl rfl,
    by intro x hx; rcases hx with rfl | rfl <;> simp [dom, operator_identity],
    hτ_pos, hτ_fin, hdiamB, by rw [hdiamB]; exact hτ_pos, hdiamA, by rw [hdiamA]; exact hτ_le1⟩

/-! ### Proposition 3.15: Separation Threshold Given by Uniform Nullification Radius (CH03-P18-01..03) -/

/-- Proposition 3.15(i): Input distance strictly below `\underline{r}^N_{f, i, j}|_A` forces
output zero-distance. -/
theorem prop_3_15_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I)
    (_hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hlt : d i x y < uniformNullRadiusCompOn d f i j A) :
    d j (f.func x) (f.func y) = 0 := by
  have hpt : d i x y < pointwiseNullRadiusComp d f i j A x :=
    lt_of_lt_of_le hlt (iInf₂_le x hx)
  exact prop_3_11_radius d hd f A i j hAdom hx hy hpt

/-- Proposition 3.15(ii): Positive output separation implies input distance at least
`\underline{r}^N_{f, i, j}|_A`. -/
theorem prop_3_15_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hpos : 0 < d j (f.func x) (f.func y)) :
    uniformNullRadiusCompOn d f i j A ≤ d i x y := by
  by_contra hlt
  have hzero := prop_3_15_i d hd f A i j hAne hAdom hx hy (lt_of_not_ge hlt)
  exact (ne_of_gt hpos) hzero

/-- Proposition 3.15(iii): When `\underline{r}^N_{f, i, j}|_A < τ_N`, for every finite positive `α`
with `\underline{r}^N < α < τ_N`, there exist `x, y ∈ A` and finite positive `ε` such that
`d_i(x, y) < α` and `ε ≤ d_j(f(x), f(y))` (handling both finite and infinite output distance). -/
theorem prop_3_15_iii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (_hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N α : ENNReal)
    (_hAne : A.Nonempty) (_hAdom : A ⊆ dom f)
    (_hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hα_gt : uniformNullRadiusCompOn d f i j A < α) (hα_lt : α < τ_N) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  have hα_pos : 0 < α := lt_of_le_of_lt (zero_le _) hα_gt
  have hα_fin : α < ⊤ := lt_trans hα_lt hτ_fin
  have hex_y : ∃ y ∈ A, pointwiseNullRadiusComp d f i j A y < α := by
    by_contra hall
    push Not at hall
    have hle : α ≤ uniformNullRadiusCompOn d f i j A := le_iInf₂ hall
    exact not_lt_of_ge hle hα_gt
  rcases hex_y with ⟨y, hyA, hy_lt⟩
  have hnot_legal : ¬ IsLegalNullRadius (d i) (d j) f A y α := fun hleg =>
    not_le_of_gt hy_lt (le_sSup hleg)
  have hex_x : ∃ x ∈ A, d i x y < α ∧ d j (f.func x) (f.func y) ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hnot_legal ⟨hα_pos, hα_fin, hno⟩
  rcases hex_x with ⟨x, hxA, hdx, hdy_ne0⟩
  have hdy_pos : 0 < d j (f.func x) (f.func y) := pos_iff_ne_zero.mpr hdy_ne0
  by_cases htop : d j (f.func x) (f.func y) = ⊤
  · refine ⟨x, hxA, y, hyA, 1, zero_lt_one, ENNReal.one_lt_top, hdx, ?_⟩
    rw [htop]; exact le_top
  · refine ⟨x, hxA, y, hyA, d j (f.func x) (f.func y), hdy_pos, lt_top_iff_ne_top.mpr htop,
      hdx, le_rfl⟩

/-! ### Proposition 3.16: Fiber Inclusion and Covering-Number / Entropy Bounds (CH03-P19-01..03) -/

/-- Proposition 3.16(i): If `\underline{r}^N_{f, i, j}|_A ≥ τ_N`, every `τ_N`-ball centered at
`x ∈ A` is contained in `Fib_{f, j}(f(x) | A)`. -/
theorem prop_3_16_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (_hτ_pos : 0 < τ_N) (_hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ x ∈ A, ball (d i) x τ_N ∩ A ⊆ compFiberSingle d f j A (f.func x) := by
  intro x hx y ⟨hball, hy⟩
  refine ⟨hy, ?_⟩
  have hlt : d i y x < uniformNullRadiusCompOn d f i j A := lt_of_lt_of_le hball hge
  exact prop_3_15_i d hd f A i j hAne hAdom hy hx hlt

/-- Proposition 3.16(ii-a): For every `B ⊆ A` (including empty `B` and infinite covering number)
and every finite positive `ε`, `N_j(ε, f(B)) ≤ N_i(τ_N, B)`. -/
theorem prop_3_16_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ B ⊆ A, ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number (d j) ε (operator_image f B) ≤ covering_number (d i) τ_N B := by
  classical
  intro B hBA ε hε_pos _hε_fin
  rw [le_covering_number_iff]
  intro S hS
  have hnet_img : InternalEpsilonNet (d j) ε (operator_image f B) (S.image f.func) := by
    constructor
    · intro y hy
      rcases Finset.mem_image.mp (by simpa using hy) with ⟨s, hs, rfl⟩
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro y ⟨b, hbB, rfl⟩
      rcases hS.2 b hbB with ⟨s, hs, hdist⟩
      have hfib := prop_3_16_i d hd f A i j τ_N hAne hAdom hτ_pos hτ_fin hge
        s (hBA (hS.1 hs)) ⟨hdist, hBA hbB⟩
      refine ⟨f.func s, Finset.mem_image_of_mem f.func hs, ?_⟩
      rw [hfib.2]
      exact hε_pos
  calc
    covering_number (d j) ε (operator_image f B)
        ≤ ((S.image f.func).card : ENNReal) := covering_number_le_of_net hnet_img
    _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le

/-- Proposition 3.16(ii-b): For nonempty `B ⊆ A`, `E_{ε, j}(f(B)) ≤ E_{τ_N, i}(B)`. -/
theorem prop_3_16_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (hτ_pos : 0 < τ_N) (hτ_fin : τ_N < ⊤)
    (hge : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ B ⊆ A, B.Nonempty → ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      metric_entropy (d j) ε (operator_image f B) ≤ metric_entropy (d i) τ_N B := by
  intro B hBA _hBne ε hε_pos hε_fin
  exact metric_entropy_mono_of_covering_number_le
    (prop_3_16_ii_a d hd f A i j τ_N hAne hAdom hτ_pos hτ_fin hge B hBA ε hε_pos hε_fin)

/-! ### Counterexample after Proposition 3.16: Pointwise Positive Radius Cannot Replace Uniform Threshold (CH03-P20-01) -/

/-- Post-Proposition 3.16 counterexample (for any admissible `0 < a ≤ 1` with `2a < τ`):
on Counterexample 3.1's `stepOp` and `stepU`, `B = {-a, a} ⊆ stepU` satisfies
`N_1(τ, B) = 1 < 2 = N_1(1/2, f(B))`. -/
theorem post_prop_3_16_counterexample_for_a (τ : ENNReal) (a : ℝ)
    (ha_pos : 0 < a) (ha_le1 : a ≤ 1) (h2a_lt : ENNReal.ofReal (2 * a) < τ) :
    let B : Set RealWithBot := {some (-a), some a}
    B ⊆ stepU ∧
    covering_number realWithBotDist τ B = 1 ∧
    covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) = 2 ∧
    covering_number realWithBotDist τ B <
      covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) := by
  classical
  intro B
  have hτ_pos : 0 < τ := lt_of_le_of_lt (zero_le _) h2a_lt
  have hB_sub : B ⊆ stepU := by
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨-a, rfl, Or.inl ⟨by linarith, by linarith⟩⟩
    · exact ⟨a, rfl, Or.inr ⟨ha_pos, ha_le1⟩⟩
  have hB_ne : B.Nonempty := ⟨some a, Or.inr rfl⟩
  have hcovB : covering_number realWithBotDist τ B = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist τ B {some a} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc; exact Or.inr rfl
        · intro x hx
          refine ⟨some a, Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl
          · have hdist : realWithBotDist (some (-a)) (some a) = ENNReal.ofReal (2 * a) := by
              simp only [realWithBotDist]
              congr 1
              rw [show -a - a = -(2 * a) by ring, abs_neg, abs_of_pos (by linarith)]
            rw [hdist]
            exact h2a_lt
          · simp [realWithBotDist, hτ_pos]
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty realWithBotDist τ B hB_ne
  have himgB : operator_image stepOp B = {some 0, some 1} := by
    ext z
    simp only [operator_image, B, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · left; simp [stepOp, show -a < 0 by linarith]
      · right; simp [stepOp, not_lt.mpr (le_of_lt ha_pos)]
    · rintro (rfl | rfl)
      · exact ⟨some (-a), Or.inl rfl, by simp [stepOp, show -a < 0 by linarith]⟩
      · exact ⟨some a, Or.inr rfl, by simp [stepOp, not_lt.mpr (le_of_lt ha_pos)]⟩
  have hcovImg : covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) = 2 := by
    rw [himgB]
    have hne01 : (some (0 : ℝ) : RealWithBot) ≠ some 1 := by simp
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist (ENNReal.ofReal (1 / 2))
          ({some 0, some 1} : Set RealWithBot) {some 0, some 1} := by
        constructor
        · intro c hc
          simp only [Finset.coe_insert, Finset.coe_singleton] at hc
          exact hc
        · intro x hx
          rcases hx with rfl | rfl
          · refine ⟨some 0, by simp, ?_⟩
            simp only [realWithBotDist, sub_self, abs_zero, ENNReal.ofReal_zero]
            exact ENNReal.ofReal_pos.mpr (by norm_num)
          · refine ⟨some 1, by simp, ?_⟩
            simp only [realWithBotDist, sub_self, abs_zero, ENNReal.ofReal_zero]
            exact ENNReal.ofReal_pos.mpr (by norm_num)
      have hcard : ({some (0 : ℝ), some (1 : ℝ)} : Finset RealWithBot).card = 2 := by
        rw [Finset.card_pair hne01]
      simpa [hcard] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      have h0 : some (0 : ℝ) ∈ S := by
        rcases hS.2 (some 0) (Or.inl rfl) with ⟨c, hcS, hdist⟩
        rcases hS.1 hcS with rfl | rfl
        · exact hcS
        · exfalso
          simp only [realWithBotDist] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp hdist
          norm_num at hlt
      have h1 : some (1 : ℝ) ∈ S := by
        rcases hS.2 (some 1) (Or.inr rfl) with ⟨c, hcS, hdist⟩
        rcases hS.1 hcS with rfl | rfl
        · exfalso
          simp only [realWithBotDist] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp hdist
          norm_num at hlt
        · exact hcS
      have hsub : ({some (0 : ℝ), some (1 : ℝ)} : Finset RealWithBot) ⊆ S := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption
      have hcard : 2 ≤ S.card := by
        calc
          2 = ({some (0 : ℝ), some (1 : ℝ)} : Finset RealWithBot).card :=
              (Finset.card_pair hne01).symm
          _ ≤ S.card := Finset.card_le_card hsub
      exact_mod_cast hcard
  refine ⟨hB_sub, hcovB, hcovImg, ?_⟩
  rw [hcovB, hcovImg]
  exact ENNReal.one_lt_two

/-- Post-Proposition 3.16 counterexample on Counterexample 3.1's `stepOp` and `stepU`:
for every finite positive `τ`, there exists `0 < a ≤ 1` with `2a < τ` such that
`B = {-a, a} ⊆ stepU` satisfies `N_1(τ, B) = 1 < 2 = N_1(1/2, f(B))`. -/
theorem post_prop_3_16_counterexample (τ : ENNReal) (hτ_pos : 0 < τ) (hτ_fin : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      let B : Set RealWithBot := {some (-a), some a}
      B ⊆ stepU ∧
      covering_number realWithBotDist τ B = 1 ∧
      covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) = 2 ∧
      covering_number realWithBotDist τ B <
        covering_number realWithBotDist (ENNReal.ofReal (1 / 2)) (operator_image stepOp B) := by
  have hτ_real_pos : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ_pos) (ne_of_lt hτ_fin)
  let a : ℝ := min 1 (τ.toReal / 4)
  have ha_pos : 0 < a := lt_min zero_lt_one (by linarith)
  have ha_le1 : a ≤ 1 := min_le_left _ _
  have h2a_lt_real : 2 * a < τ.toReal := by
    have : a ≤ τ.toReal / 4 := min_le_right _ _
    linarith
  have h2a_lt : ENNReal.ofReal (2 * a) < τ := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hτ_fin)]
    exact (ENNReal.ofReal_lt_ofReal_iff hτ_real_pos).mpr h2a_lt_real
  exact ⟨a, ha_pos, ha_le1, h2a_lt, post_prop_3_16_counterexample_for_a τ a ha_pos ha_le1 h2a_lt⟩

/-! ### Corollary 3.17: Global Nullification Criterion on Small Input Domains (CH03-P21-01..02) -/

/-- Corollary 3.17 (equivalence): Under `diam_{d_i}(A) < τ_σ ≤ τ_N`,
`\underline{r}^N_{f, i, j}|_A ≥ τ_N` iff `∀ x, y ∈ A, d_j(f(x), f(y)) = 0`. -/
theorem cor_3_17_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_σ τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (_hτσ_pos : 0 < τ_σ) (_hτσ_fin : τ_σ < ⊤)
    (_hτN_pos : 0 < τ_N) (_hτN_fin : τ_N < ⊤)
    (hdiam : diamScaleFun d i A < τ_σ) (hτ_le : τ_σ ≤ τ_N) :
    τ_N ≤ uniformNullRadiusCompOn d f i j A ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro hge x hx y hy
    have hdx : d i x y < uniformNullRadiusCompOn d f i j A := by
      calc
        d i x y ≤ diamScaleFun d i A :=
            le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
        _ < τ_σ := hdiam
        _ ≤ τ_N := hτ_le
        _ ≤ uniformNullRadiusCompOn d f i j A := hge
    exact prop_3_15_i d hd f A i j hAne hAdom hx hy hdx
  · intro hconst
    have htop : uniformNullRadiusCompOn d f i j A = ⊤ := by
      apply top_unique
      apply le_iInf₂
      intro y hy
      rw [pointwiseNullRadius_eq_top_of_all_finite_pos]
      intro r hr0 hrt
      exact ⟨hr0, hrt, fun x hx _ => hconst x hx y hy⟩
    rw [htop]
    exact le_top

/-- Corollary 3.17 (covering number = 1): When the equivalent condition holds on nonempty `A`,
`N_j(ε, f(A)) = 1` for every finite positive `ε`. -/
theorem cor_3_17_covering_one {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (f : Operator X bot) (A : Set X) (i j : I) (τ_σ τ_N : ENNReal)
    (hAne : A.Nonempty) (hAdom : A ⊆ dom f)
    (hτσ_pos : 0 < τ_σ) (hτσ_fin : τ_σ < ⊤)
    (hτN_pos : 0 < τ_N) (hτN_fin : τ_N < ⊤)
    (hdiam : diamScaleFun d i A < τ_σ) (hτ_le : τ_σ ≤ τ_N)
    (hcond : τ_N ≤ uniformNullRadiusCompOn d f i j A) :
    ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number (d j) ε (operator_image f A) = 1 := by
  have hconst := (cor_3_17_iff d hd f A i j τ_σ τ_N hAne hAdom
    hτσ_pos hτσ_fin hτN_pos hτN_fin hdiam hτ_le).mp hcond
  intro ε hε_pos _hε_fin
  rcases hAne with ⟨x₀, hx₀⟩
  have himg_ne : (operator_image f A).Nonempty := ⟨f.func x₀, ⟨x₀, hx₀, rfl⟩⟩
  apply le_antisymm
  · have hnet : InternalEpsilonNet (d j) ε (operator_image f A) {f.func x₀} := by
      constructor
      · intro c hc
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
        subst hc
        exact ⟨x₀, hx₀, rfl⟩
      · rintro y ⟨x, hxA, rfl⟩
        refine ⟨f.func x₀, Finset.mem_singleton_self _, ?_⟩
        rw [hconst x hxA x₀ hx₀]
        exact hε_pos
    simpa using covering_number_le_of_net hnet
  · exact one_le_covering_number_of_nonempty (d j) ε (operator_image f A) himg_ne

end Ch03
