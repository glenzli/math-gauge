import CH03.Core2

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X : Type} {I : Type} {bot : X}

/-! ## Proposition 3.8 -/

theorem fiber_eq_U_of_subset_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I) (U : Set X)
    (hJ : J ⊆ Iconst d φ U) {y : X} (hy : y ∈ U) :
    Fiber d φ J (φ.func y) U = U := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro j hj
    exact hJ hj x hx y hy

theorem pointwiseZeroRadiusJ_eq_top_of_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I) (J : Set I)
    (U : Set X) (hJ : J ⊆ Iconst d φ U) {y : X} (hy : y ∈ U) :
    pointwiseZeroRadiusJ d φ i J y U = ⊤ := by
  rw [pointwiseZeroRadiusJ, pointwiseRadius_eq_top_iff]
  intro r hr0 hrtop
  refine ⟨hr0, hrtop, ?_⟩
  intro x hx _
  intro j hj
  exact hJ hj x hx y hy

theorem unifiedZeroRadiusJ_eq_top_of_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I) (J : Set I)
    (U : Set X) (hU : U.Nonempty) (hJ : J ⊆ Iconst d φ U) :
    unifiedZeroRadiusJ d φ i J U = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro y
  change ⊤ ≤ pointwiseZeroRadiusJ d φ i J y.1 U
  rw [pointwiseZeroRadiusJ_eq_top_of_const d φ i J U hJ y.2]

/-! ## Proposition 3.9 -/

theorem fiber_id_component_target
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U) (i : I)
    (hi : i ∈ Iid d φ U) :
    Fiber d φ ({i} : Set I) (φ.func y) U = {x | x ∈ U ∧ d i x y = 0} :=
  fiber_id_component d hd φ U y hy i hi

theorem pointwiseRadius_ge_of_ball_subset
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U) (i : I)
    (hi : i ∈ Iid d φ U) {r0 : ENNReal}
    (hr0pos : 0 < r0) (hr0top : r0 ≠ ⊤)
    (hball : ∀ x ∈ U, d i x y < r0 → d i x y = 0) :
    r0 ≤ pointwiseZeroRadius d φ i i y U := by
  apply le_pointwiseRadius_of_legal
  refine ⟨hr0pos, hr0top, ?_⟩
  intro x hx hlt
  have hxy : d i x y = 0 := hball x hx hlt
  have hiso := id_component_isometry d hd φ U i hi x hx y hy
  rw [hiso, hxy]

/-! ## Proposition 3.10 -/

theorem pointwiseZeroRadiusJ_eq_finset_inf
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I)
    (J : Finset I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    pointwiseZeroRadiusJ d φ i (J : Set I) y U =
      J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y U) := by
  apply le_antisymm
  · apply Finset.le_inf' hJ
    intro j hj
    apply iSup_le
    intro r
    apply le_pointwiseRadius_of_legal
    refine ⟨r.2.1, r.2.2.1, ?_⟩
    intro x hx hlt
    exact r.2.2.2 x hx hlt j hj
  · apply le_of_forall_lt
    intro c hc
    have hmpos : 0 < J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y U) :=
      lt_of_le_of_lt (zero_le c) hc
    obtain ⟨dmid, hcd, hdm⟩ := exists_between hc
    have hdpos : 0 < dmid := lt_of_le_of_lt (zero_le c) hcd
    have hlegal : LegalRadius (d i) (fun a b => ∀ j ∈ (J : Set I), d j a b = 0)
        φ y U dmid := by
      refine ⟨hdpos, ?_, ?_⟩
      · by_contra htop
        have : (⊤ : ENNReal) < J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y U) := by
          simpa [htop] using hdm
        exact not_top_lt this
      · intro x hx hlt
        intro j hj
        have hltj : dmid < pointwiseZeroRadius d φ i j y U :=
          lt_of_lt_of_le hdm (Finset.inf'_le (fun j => pointwiseZeroRadius d φ i j y U) hj)
        rcases (lt_iSup_iff.mp hltj) with ⟨s, hslt⟩
        have hslegal : LegalRadius (d i) (fun a b => d j a b = 0) φ y U s.1 := s.2
        have hmidlegal : LegalRadius (d i) (fun a b => d j a b = 0) φ y U dmid :=
          legalRadius_mono hdpos (le_of_lt hslt) hslegal
        exact hmidlegal.2.2 x hx hlt
    have hle : dmid ≤ pointwiseZeroRadiusJ d φ i (J : Set I) y U :=
      le_pointwiseRadius_of_legal hlegal
    exact lt_of_lt_of_le hcd hle

theorem unifiedZeroRadiusJ_eq_finset_inf
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I)
    (J : Finset I) (hJ : J.Nonempty) (U : Set X) (hU : U.Nonempty) :
    unifiedZeroRadiusJ d φ i (J : Set I) U =
      J.inf' hJ (fun j => zeroingMatrix d φ U j i) := by
  unfold unifiedZeroRadiusJ zeroingMatrix unifiedRadius
  apply le_antisymm
  · apply Finset.le_inf' hJ
    intro j hj
    apply le_iInf
    intro y
    calc
      (⨅ y : {y : X // y ∈ U},
          pointwiseRadius (d i) (fun a b => ∀ j ∈ (J : Set I), d j a b = 0) φ y.1 U)
          ≤ pointwiseRadius (d i) (fun a b => ∀ j ∈ (J : Set I), d j a b = 0) φ y.1 U :=
            iInf_le _ y
      _ = J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y.1 U) := by
            exact pointwiseZeroRadiusJ_eq_finset_inf d φ i J hJ y.1 U
      _ ≤ pointwiseZeroRadius d φ i j y.1 U :=
            Finset.inf'_le (fun j => pointwiseZeroRadius d φ i j y.1 U) hj
  · apply le_iInf
    intro y
    change (J.inf' hJ (fun j =>
        ⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U)) ≤
      pointwiseZeroRadiusJ d φ i (J : Set I) y.1 U
    rw [pointwiseZeroRadiusJ_eq_finset_inf d φ i J hJ y.1 U]
    apply Finset.le_inf' hJ
    intro j hj
    calc
      (J.inf' hJ (fun j =>
          ⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U))
          ≤ (⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U) :=
            Finset.inf'_le (fun j =>
              ⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U) hj
      _ ≤ pointwiseZeroRadius d φ i j y.1 U := iInf_le _ y

theorem unifiedZeroRadiusJ_antitone_output
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I)
    {J K : Set I} (hJK : J ⊆ K) (A : Set X) :
    unifiedZeroRadiusJ d φ i K A ≤ unifiedZeroRadiusJ d φ i J A := by
  unfold unifiedZeroRadiusJ unifiedRadius
  apply iInf_mono
  intro y
  apply iSup_le
  intro r
  apply le_pointwiseRadius_of_legal
  exact ⟨r.2.1, r.2.2.1, fun x hx hlt j hj => r.2.2.2 x hx hlt j (hJK hj)⟩


/-! ## Proposition 3.11 -/

theorem fiber_member_output_zero
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) {y y' : X}
    (hy' : y' ∈ Fiber d φ ({j} : Set I) (φ.func y) U) :
    d j (φ.func y) (φ.func y') = 0 := by
  have h := hy'.2 j (by simp)
  rw [(hd j).symm]
  exact h

theorem pointwise_radius_truncation
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) {y y' : X}
    (hy' : y' ∈ U)
    (hlt : d i y y' < pointwiseZeroRadius d φ i j y U) :
    d j (φ.func y) (φ.func y') = 0 := by
  unfold pointwiseZeroRadius pointwiseRadius at hlt
  rcases lt_iSup_iff.mp hlt with ⟨r, hrlt⟩
  have hsym : d i y' y < r.1 := by
    rwa [(hd i).symm] at hrlt
  have hout := r.2.2.2 y' hy' hsym
  change d j (φ.func y') (φ.func y) = 0 at hout
  rwa [(hd j).symm] at hout

theorem composite_fiber_truncation
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) (i j : I) {x x' : X}
    (hx : φ1.func x ∈ U) (hx' : φ1.func x' ∈ U)
    (hmem : φ1.func x' ∈ Fiber d φ2 ({j} : Set I) (φ2.func (φ1.func x)) U) :
    d j ((φ2 * φ1).func x) ((φ2 * φ1).func x') = 0 := by
  exact fiber_member_output_zero d hd φ2 U i j hmem

/-! ## Proposition 3.12 -/

theorem unified_comp_radius_preserve
    (d : I → X → X → ENNReal) (φ1 φ2 : Operator X bot) (i j l : I) (U : Set X)
    (hpres : ∀ y ∈ φ1.func '' U, ∀ y' ∈ φ1.func '' U,
      d l y y' = 0 → d j (φ2.func y) (φ2.func y') = 0) :
    unifiedRadius (d i) (fun a b => d l a b = 0) φ1 U U ≤
      unifiedRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) U U := by
  unfold unifiedRadius
  apply le_iInf
  intro y
  refine le_trans (iInf_le (fun y : {y : X // y ∈ U} =>
    pointwiseRadius (d i) (fun a b => d l a b = 0) φ1 y.1 U) y) ?_
  apply iSup_le
  intro r
  apply le_pointwiseRadius_of_legal
  refine ⟨r.2.1, r.2.2.1, ?_⟩
  intro x hx hlt
  have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
  have hφy : φ1.func y.1 ∈ φ1.func '' U := ⟨y.1, y.2, rfl⟩
  have hz : d l (φ1.func x) (φ1.func y.1) = 0 := r.2.2.2 x hx hlt
  exact hpres _ hφx _ hφy hz

theorem unified_comp_radius_lip_pullback
    (d : I → X → X → ENNReal) (φ1 φ2 : Operator X bot) (i j l : I) (U : Set X)
    (L : ENNReal) (hLpos : 0 < L) (hLtop : L ≠ ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d l (φ1.func x) (φ1.func y) ≤ L * d i x y) :
    unifiedRadius (d l) (fun a b => d j a b = 0) φ2 (φ1.func '' U) (φ1.func '' U) / L ≤
      unifiedRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) U U := by
  unfold unifiedRadius
  let p2 : X → ENNReal := fun z =>
    pointwiseRadius (d l) (fun a b => d j a b = 0) φ2 z (φ1.func '' U)
  let pc : X → ENNReal := fun y =>
    pointwiseRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) y U
  have hpoint : ∀ y ∈ U, p2 (φ1.func y) / L ≤ pc y := by
    intro y hy
    rw [ENNReal.div_le_iff (ne_of_gt hLpos) hLtop]
    apply iSup_le
    intro r
    have hrlegal : LegalRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) y U (r.1 / L) := by
      refine ⟨ENNReal.div_pos (ne_of_gt r.2.1) hLtop,
        ENNReal.div_ne_top r.2.2.1 (ne_of_gt hLpos), ?_⟩
      intro x hx hlt
      have hLx : L * d i x y < r.1 := by
        have := (ENNReal.mul_lt_of_lt_div hlt : d i x y * L < r.1)
        rwa [mul_comm] at this
      have hstep : d l (φ1.func x) (φ1.func y) < r.1 :=
        lt_of_le_of_lt (hLip x hx y hy) hLx
      exact r.2.2.2 (φ1.func x) ⟨x, hx, rfl⟩ hstep
    have hle : r.1 / L ≤ pc y := le_pointwiseRadius_of_legal hrlegal
    calc
      r.1 = (r.1 / L) * L := by rw [ENNReal.div_mul_cancel (ne_of_gt hLpos) hLtop]
      _ ≤ pc y * L := by gcongr
  have h1 : (⨅ z : {z : X // z ∈ φ1.func '' U}, p2 z.1) / L ≤
      (⨅ y : {y : X // y ∈ U}, p2 (φ1.func y.1) / L) := by
    apply le_iInf
    intro y
    exact ENNReal.div_le_div_right
      (iInf_le (fun z : {z : X // z ∈ φ1.func '' U} => p2 z.1)
        ⟨φ1.func y.1, ⟨y.1, y.2, rfl⟩⟩) L
  have h2 : (⨅ y : {y : X // y ∈ U}, p2 (φ1.func y.1) / L) ≤
      (⨅ y : {y : X // y ∈ U}, pc y.1) := by
    apply iInf_mono
    intro y
    exact hpoint y.1 y.2
  exact le_trans h1 h2

/-! ## Input scales and threshold classification (D06, Lemma 3.13) -/

/-- A monotone family of input scale functions. -/
structure InputScaleFamily (X : Type) (I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i : I, ∀ {A B : Set X}, A ⊆ B → scale i A ≤ scale i B

/-- Diameter scale associated to a component pseudometric. -/
noncomputable def diameterScale (d : I → X → X → ENNReal) (i : I) (A : Set X) : ENNReal :=
  ⨆ x : {x : X // x ∈ A}, ⨆ y : {y : X // y ∈ A}, d i x.1 y.1

theorem diameterScale_mono (d : I → X → X → ENNReal) (i : I) {A B : Set X}
    (hAB : A ⊆ B) :
    diameterScale d i A ≤ diameterScale d i B := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  exact le_iSup_of_le ⟨x.1, hAB x.2⟩ (le_iSup_of_le ⟨y.1, hAB y.2⟩ le_rfl)

theorem inputScaleFamily_mono {σ : InputScaleFamily X I} (i : I) {A B : Set X}
    (hAB : A ⊆ B) : σ.scale i A ≤ σ.scale i B := σ.mono i hAB

/-- The two-threshold classification of a channel. -/
noncomputable def thresholdType (σ : InputScaleFamily X I) (τσ τN : ENNReal)
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    Bool × Bool :=
  (decide (σ.scale i A < τσ), decide (τN ≤ zeroingMatrix d φ A j i))

theorem thresholdType_exhaustive (σ : InputScaleFamily X I) (τσ τN : ENNReal)
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    thresholdType σ τσ τN d φ A i j = (true, true) ∨
    thresholdType σ τσ τN d φ A i j = (true, false) ∨
    thresholdType σ τσ τN d φ A i j = (false, true) ∨
    thresholdType σ τσ τN d φ A i j = (false, false) := by
  unfold thresholdType
  by_cases h1 : σ.scale i A < τσ <;> by_cases h2 : τN ≤ zeroingMatrix d φ A j i <;>
    simp [h1, h2]

theorem thresholdType_fst_mono (σ : InputScaleFamily X I)
    {τσ τσ' τN : ENNReal} (hτ : τσ ≤ τσ')
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    (h : (thresholdType σ τσ τN d φ A i j).1 = true) :
    (thresholdType σ τσ' τN d φ A i j).1 = true := by
  unfold thresholdType at h ⊢
  simp only [Prod.fst] at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  exact lt_of_lt_of_le h hτ

theorem thresholdType_snd_antitone (σ : InputScaleFamily X I)
    {τN τN' τσ : ENNReal} (hτ : τN ≤ τN')
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    (h : (thresholdType σ τσ τN' d φ A i j).2 = true) :
    (thresholdType σ τσ τN d φ A i j).2 = true := by
  unfold thresholdType at h ⊢
  simp only [Prod.snd] at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  exact le_trans hτ h

/-! ## Proposition 3.14 -/

theorem scale_threshold_domain_mono (σ : InputScaleFamily X I) (i : I)
    {B A : Set X} (hBA : B ⊆ A) {τσ : ENNReal}
    (h : σ.scale i A < τσ) : σ.scale i B < τσ :=
  lt_of_le_of_lt (inputScaleFamily_mono i hBA) h

theorem pointwiseRadius_domain_antitone
    (din : X → X → ENNReal) (P : X → X → Prop) (φ : Operator X bot)
    {B A : Set X} (hBA : B ⊆ A) {y : X} (hy : y ∈ B) :
    pointwiseRadius din P φ y A ≤ pointwiseRadius din P φ y B := by
  apply iSup_le
  intro r
  apply le_pointwiseRadius_of_legal
  refine ⟨r.2.1, r.2.2.1, ?_⟩
  intro x hx hlt
  exact r.2.2.2 x (hBA hx) hlt

theorem unifiedRadius_domain_antitone
    (din : X → X → ENNReal) (P : X → X → Prop) (φ : Operator X bot)
    {B A : Set X} (hBA : B ⊆ A) (hB : B.Nonempty) :
    unifiedRadius din P φ A A ≤ unifiedRadius din P φ B B := by
  unfold unifiedRadius
  have h1 : (⨅ y : {y : X // y ∈ A}, pointwiseRadius din P φ y.1 A) ≤
      (⨅ y : {y : X // y ∈ B}, pointwiseRadius din P φ y.1 A) := by
    apply le_iInf
    intro y
    exact iInf_le _ (⟨y.1, hBA y.2⟩ : {y : X // y ∈ A})
  have h2 : (⨅ y : {y : X // y ∈ B}, pointwiseRadius din P φ y.1 A) ≤
      (⨅ y : {y : X // y ∈ B}, pointwiseRadius din P φ y.1 B) := by
    apply iInf_mono
    intro y
    exact pointwiseRadius_domain_antitone din P φ hBA y.2
  exact le_trans h1 h2

/-! ## Proposition 3.15 -/

theorem below_unified_radius_output_zero
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A)
    (hlt : d i x y < zeroingMatrix d φ A j i) :
    d j (φ.func x) (φ.func y) = 0 := by
  unfold zeroingMatrix unifiedRadius at hlt
  have hltp : d i x y < pointwiseRadius (d i) (fun a b => d j a b = 0) φ x A :=
    lt_of_lt_of_le hlt (iInf_le _ (⟨x, hx⟩ : {x : X // x ∈ A}))
  unfold pointwiseRadius at hltp
  rcases lt_iSup_iff.mp hltp with ⟨r, hrlt⟩
  have hsym : d i y x < r.1 := by
    rwa [(hd i).symm] at hrlt
  have hout := r.2.2.2 y hy hsym
  change d j (φ.func y) (φ.func x) = 0 at hout
  rwa [(hd j).symm] at hout

theorem output_positive_input_ge_unified_radius
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A)
    (hpos : 0 < d j (φ.func x) (φ.func y)) :
    zeroingMatrix d φ A j i ≤ d i x y := by
  by_contra hnot
  have hlt : d i x y < zeroingMatrix d φ A j i := lt_of_not_ge hnot
  have hzero := below_unified_radius_output_zero d hd φ A i j hx hy hlt
  exact (ne_of_gt hpos) hzero

theorem unified_radius_deficiency_witness
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    {τN α : ENNReal} (hbelow : zeroingMatrix d φ A j i < τN)
    (hα : zeroingMatrix d φ A j i < α) (hατ : α < τN) :
    ∃ x ∈ A, ∃ y ∈ A, d i x y < α ∧
      ∃ ε : ENNReal, 0 < ε ∧ ε ≠ ⊤ ∧ ε ≤ d j (φ.func x) (φ.func y) := by
  unfold zeroingMatrix unifiedRadius at hα
  rcases iInf_lt_iff.mp hα with ⟨y, hy⟩
  have hαpos : 0 < α := lt_of_le_of_lt (zero_le _) hα
  have hαtop : α ≠ ⊤ := ne_top_of_lt hατ
  have hnotball : ¬ ∀ x ∈ A, d i x y.1 < α →
      d j (φ.func x) (φ.func y.1) = 0 := by
    intro hall
    have hlegal : LegalRadius (d i) (fun a b => d j a b = 0) φ y.1 A α :=
      ⟨hαpos, hαtop, hall⟩
    exact (not_lt_of_ge (le_pointwiseRadius_of_legal hlegal)) hy
  push Not at hnotball
  rcases hnotball with ⟨x, hxA, hdist, hout⟩
  refine ⟨x, hxA, y.1, y.2, hdist, ?_⟩
  have houtpos : 0 < d j (φ.func x) (φ.func y.1) :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hout)
  by_cases htop : d j (φ.func x) (φ.func y.1) = ⊤
  · exact ⟨1, zero_lt_one, ENNReal.one_ne_top, by simp [htop]⟩
  · exact ⟨d j (φ.func x) (φ.func y.1), houtpos, htop, le_rfl⟩

end formal_oet.vol_01.ch_03_operator_local_degeneracy
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

theorem thresholdType_pairwise_distinct :
    ((true, true) : Bool × Bool) ≠ (true, false) ∧
    ((true, true) : Bool × Bool) ≠ (false, true) ∧
    ((true, true) : Bool × Bool) ≠ (false, false) ∧
    ((true, false) : Bool × Bool) ≠ (false, true) ∧
    ((true, false) : Bool × Bool) ≠ (false, false) ∧
    ((false, true) : Bool × Bool) ≠ (false, false) := by
  decide

end formal_oet.vol_01.ch_03_operator_local_degeneracy
