import Ch03.ExamplesBase

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-- The step operator on the real line with an absorbing point. -/
noncomputable def stepOp : Operator RealBase none where
  func
    | none => none
    | some x => some (if x < 0 then 0 else 1)
  preserves_bot := rfl

def stepDomainReal : Set ℝ := Set.Ico (-1) 0 ∪ Set.Ioc 0 1

def stepDomain : Set RealBase := some '' stepDomainReal

theorem stepDomain_nonempty : stepDomain.Nonempty := ⟨some 1, ⟨1, Or.inr ⟨zero_lt_one, le_rfl⟩, rfl⟩⟩

theorem stepDomain_subset_dom : stepDomain ⊆ dom stepOp := by
  rintro x ⟨y, hy, rfl⟩
  simp [dom, stepOp]

/-- Counterexample 3.1: the legal finite positive radii at `y` have supremum
exactly `|y|`. -/
theorem step_pointRadius (y : ℝ) (hy : y ∈ stepDomainReal) :
    annihilationRadius stepOp usualDist usualDist (some y) stepDomain = ENNReal.ofReal |y| := by
  have hy0 : y ≠ 0 := by
    rcases hy with hy | hy
    · exact ne_of_lt hy.2
    · exact ne_of_gt hy.1
  apply le_antisymm
  · apply sSup_le
    intro r hr
    by_contra hnr
    have hgt : ENNReal.ofReal |y| < r := lt_of_not_ge hnr
    have hreal : |y| < r.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) (ne_of_lt hr.2.1)).mp hgt
    have hδ : 0 < r.toReal - |y| := sub_pos.mpr hreal
    let a := min 1 ((r.toReal - |y|) / 2)
    have ha0 : 0 < a := lt_min zero_lt_one (half_pos hδ)
    have ha1 : a ≤ 1 := min_le_left _ _
    have haδ : a < r.toReal - |y| :=
      (min_le_right _ _).trans_lt (half_lt_self hδ)
    rcases hy with hyneg | hypos
    · let x := a
      have hxD : x ∈ stepDomainReal := Or.inr ⟨ha0, ha1⟩
      have hball : some x ∈ ball usualDist (some y) r ∩ stepDomain := by
        refine ⟨?_, ⟨x, hxD, rfl⟩⟩
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (ne_of_lt hr.2.1)).mpr
        have habs : |x - y| = x + |y| := by
          rw [abs_of_neg hyneg.2]
          apply abs_of_pos
          dsimp [x]
          linarith [ha0, hyneg.2]
        rw [habs]
        linarith
      have hz := (hr.2.2 hball).2
      have hstep : stepOp.func (some x) = some 1 := by
        simp [stepOp, not_lt.mpr (show 0 ≤ x from ha0.le)]
      have hstepy : stepOp.func (some y) = some 0 := by simp [stepOp, hyneg.2]
      rw [hstep, hstepy] at hz
      norm_num [usualDist, optionDist] at hz
    · let x := -a
      have hxD : x ∈ stepDomainReal := by
        apply Or.inl
        constructor
        · dsimp [x]; linarith [ha1]
        · dsimp [x]; exact neg_lt_zero.mpr ha0
      have hball : some x ∈ ball usualDist (some y) r ∩ stepDomain := by
        refine ⟨?_, ⟨x, hxD, rfl⟩⟩
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (ne_of_lt hr.2.1)).mpr
        have habs : |x - y| = -x + |y| := by
          rw [abs_of_pos hypos.1]
          rw [abs_of_neg (show x - y < 0 by dsimp [x]; linarith [ha0, hypos.1])]
          ring
        rw [habs]
        dsimp [x]
        have haδ' : a < r.toReal - y := by simpa [abs_of_pos hypos.1] using haδ
        linarith
      have hz := (hr.2.2 hball).2
      have hstep : stepOp.func (some x) = some 0 := by
        simp [stepOp, show x < 0 from neg_lt_zero.mpr ha0]
      have hstepy : stepOp.func (some y) = some 1 := by simp [stepOp, not_lt.mpr hypos.1.le]
      rw [hstep, hstepy] at hz
      norm_num [usualDist, optionDist] at hz
  · apply le_annihilationRadius_of_forall_lt
    intro r hr0 hrt hrM
    intro x hx
    rcases hx.2 with ⟨x, hxD, rfl⟩
    have hdist : |x - y| < r.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (ne_of_lt hrt)).mp hx.1
    have hry : r.toReal < |y| := by
      have h := (ENNReal.toReal_lt_toReal (ne_of_lt hrt) ENNReal.ofReal_ne_top).mpr hrM
      simpa [ENNReal.toReal_ofReal (abs_nonneg y)] using h
    have habs : |x - y| < |y| := hdist.trans hry
    have hsame : (x < 0 ∧ y < 0) ∨ (0 ≤ x ∧ 0 ≤ y) := by
      by_cases hyneg : y < 0
      · left
        refine ⟨?_, hyneg⟩
        by_contra hxn
        have hx0 : 0 ≤ x := le_of_not_gt hxn
        have heq : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr (hyneg.le.trans hx0))
        rw [heq, abs_of_neg hyneg] at habs
        linarith
      · right
        have hy0 : 0 ≤ y := le_of_not_gt hyneg
        refine ⟨?_, hy0⟩
        by_contra hxn
        have hxneg : x < 0 := lt_of_not_ge hxn
        have heq : |x - y| = y - x := by
          rw [abs_of_nonpos (sub_nonpos.mpr (hxneg.le.trans hy0))]
          ring
        rw [heq, abs_of_nonneg hy0] at habs
        linarith
    refine ⟨⟨x, hxD, rfl⟩, ?_⟩
    cases hsame with
    | inl h => simp [stepOp, h.1, h.2]
    | inr h => simp [stepOp, not_lt.mpr h.1, not_lt.mpr h.2]

/-- The legal radii at `y` are exactly the finite positive radii at most
`|y|`; in particular the endpoint is legal. -/
theorem step_legalRadii (y : ℝ) (hy : y ∈ stepDomainReal) :
    annihilatingRadii stepOp usualDist usualDist (some y) stepDomain =
      {r | 0 < r ∧ r < ⊤ ∧ r ≤ ENNReal.ofReal |y|} := by
  ext r
  constructor
  · intro hr
    refine ⟨hr.1, hr.2.1, ?_⟩
    rw [← step_pointRadius y hy]
    exact le_sSup hr
  · rintro ⟨hr0, hrt, hrle⟩
    refine ⟨hr0, hrt, ?_⟩
    intro x hx
    rcases hx.2 with ⟨x, hxD, rfl⟩
    have hdist : |x - y| < r.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (ne_of_lt hrt)).mp hx.1
    have hry : r.toReal ≤ |y| := by
      have h := (ENNReal.toReal_le_toReal (ne_of_lt hrt) ENNReal.ofReal_ne_top).mpr hrle
      simpa [ENNReal.toReal_ofReal (abs_nonneg y)] using h
    have habs : |x - y| < |y| := hdist.trans_le hry
    have hsame : (x < 0 ∧ y < 0) ∨ (0 ≤ x ∧ 0 ≤ y) := by
      by_cases hyneg : y < 0
      · left
        refine ⟨?_, hyneg⟩
        by_contra hxn
        have hx0 : 0 ≤ x := le_of_not_gt hxn
        have heq : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr (hyneg.le.trans hx0))
        rw [heq, abs_of_neg hyneg] at habs
        linarith
      · right
        have hy0 : 0 ≤ y := le_of_not_gt hyneg
        refine ⟨?_, hy0⟩
        by_contra hxn
        have hxneg : x < 0 := lt_of_not_ge hxn
        have heq : |x - y| = y - x := by
          rw [abs_of_nonpos (sub_nonpos.mpr (hxneg.le.trans hy0))]
          ring
        rw [heq, abs_of_nonneg hy0] at habs
        linarith
    refine ⟨⟨x, hxD, rfl⟩, ?_⟩
    cases hsame with
    | inl h => simp [stepOp, h.1, h.2]
    | inr h => simp [stepOp, not_lt.mpr h.1, not_lt.mpr h.2]

/-- Every pointwise radius is strictly positive. -/
theorem step_pointRadius_pos {y : ℝ} (hy : y ∈ stepDomainReal) :
    0 < annihilationRadius stepOp usualDist usualDist (some y) stepDomain := by
  rw [step_pointRadius y hy]
  apply ENNReal.ofReal_pos.mpr
  apply abs_pos.mpr
  rcases hy with hy | hy
  · exact ne_of_lt hy.2
  · exact ne_of_gt hy.1

/-- Counterexample 3.1: the uniform radius on the fixed domain is zero. -/
theorem step_uniformRadius_zero :
    uniformAnnihilationRadiusOn stepOp usualDist usualDist stepDomain = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra hn
  have hpos : 0 < uniformAnnihilationRadiusOn stepOp usualDist usualDist stepDomain :=
    lt_of_not_ge hn
  obtain ⟨r, hr0, hrU⟩ := exists_between hpos
  have hrt : r < ⊤ := hrU.trans_le le_top
  let a := min 1 (r.toReal / 2)
  have hrt0 : 0 < r.toReal := by
    have := (ENNReal.toReal_lt_toReal (ne_of_lt hrt) (ne_of_lt hrt))
    exact (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))
  have ha0 : 0 < a := lt_min zero_lt_one (half_pos hrt0)
  have ha1 : a ≤ 1 := min_le_left _ _
  have har : a < r.toReal := (min_le_right _ _).trans_lt (half_lt_self hrt0)
  have haD : a ∈ stepDomainReal := Or.inr ⟨ha0, ha1⟩
  have hle : uniformAnnihilationRadiusOn stepOp usualDist usualDist stepDomain ≤
      annihilationRadius stepOp usualDist usualDist (some a) stepDomain :=
    iInf_le (fun y : stepDomain => annihilationRadius stepOp usualDist usualDist y.1 stepDomain)
      ⟨some a, ⟨a, haD, rfl⟩⟩
  rw [step_pointRadius a haD, abs_of_pos ha0] at hle
  have har' : ENNReal.ofReal a < r :=
    (ENNReal.ofReal_lt_iff_lt_toReal ha0.le (ne_of_lt hrt)).mpr har
  exact (not_lt_of_ge hle) (har'.trans hrU)

/-- The two-point output of the step map has covering number two at radius
`1/2`. -/
theorem step_two_point_output_covering {a : ℝ} (ha : 0 < a) :
    covering_number usualDist (1 / 2 : ENNReal) (stepOp.func '' ({some (-a), some a} : Set RealBase)) = 2 := by
  have himage : stepOp.func '' ({some (-a), some a} : Set RealBase) = {some 0, some 1} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | hx
      · simp [stepOp, neg_lt_zero.mpr ha]
      · have : x = some a := by simpa using hx
        subst x
        simp [stepOp, not_lt.mpr ha.le]
    · intro hz
      rcases hz with rfl | hz
      · exact ⟨some (-a), by simp, by simp [stepOp, neg_lt_zero.mpr ha]⟩
      · have : z = some 1 := by simpa using hz
        subst z
        exact ⟨some a, by simp, by simp [stepOp, not_lt.mpr ha.le]⟩
  rw [himage]
  apply le_antisymm
  · have hnet : InternalEpsilonNet usualDist (1 / 2 : ENNReal) {some 0, some 1} {some 0, some 1} := by
      constructor
      · simp
      · intro x hx
        rcases hx with rfl | hx
        · exact ⟨some 0, by simp, by norm_num [usualDist, optionDist]⟩
        · have : x = some 1 := by simpa using hx
          subst x
          exact ⟨some 1, by simp, by norm_num [usualDist, optionDist]⟩
    simpa using covering_number_le_of_net hnet
  · apply le_covering_number_of_card
    intro S hS
    have hsub : ({some 0, some 1} : Finset RealBase) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · obtain ⟨c, hc, hxc⟩ := hS.2 (some 0) (by simp)
        have hc' : c ∈ ({some 0, some 1} : Set RealBase) := hS.1 hc
        rcases hc' with rfl | hc'
        · exact hc
        · have : c = some 1 := by simpa using hc'
          subst c
          norm_num [usualDist, optionDist] at hxc
      · obtain ⟨c, hc, hxc⟩ := hS.2 (some 1) (by simp)
        have hc' : c ∈ ({some 0, some 1} : Set RealBase) := hS.1 hc
        rcases hc' with rfl | hc'
        · norm_num [usualDist, optionDist] at hxc
        · have : c = some 1 := by simpa using hc'
          subst c
          exact hc
    have hc := Finset.card_le_card hsub
    norm_num at hc ⊢
    exact hc

/-- The post-Proposition-3.16 counterexample: for every finite positive `τ`,
choose `0 < a ≤ 1` with `2a < τ`; the two-point input has covering number one
but its step image has covering number two at radius `1/2`. -/
theorem step_pointwise_positive_not_uniform_covering {τ : ENNReal} (hτ0 : 0 < τ) (hτtop : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ (2 * a : ℝ) < τ.toReal ∧
      ({some (-a), some a} : Set RealBase) ⊆ stepDomain ∧
      covering_number usualDist τ ({some (-a), some a} : Set RealBase) = 1 ∧
      covering_number usualDist (1 / 2 : ENNReal)
        (stepOp.func '' ({some (-a), some a} : Set RealBase)) = 2 := by
  have hτreal : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ0) (ne_of_lt hτtop)
  let a := min 1 (τ.toReal / 4)
  have ha0 : 0 < a := lt_min zero_lt_one (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have ha2 : 2 * a < τ.toReal := by
    have h := (min_le_right 1 (τ.toReal / 4)).trans_lt (by linarith : τ.toReal / 4 < τ.toReal / 2)
    dsimp [a]
    linarith
  refine ⟨a, ha0, ha1, ha2, ?_, ?_, step_two_point_output_covering ha0⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨-a, Or.inl ⟨by linarith, neg_lt_zero.mpr ha0⟩, rfl⟩
    · have : x = some a := by simpa using hx
      subst x
      exact ⟨a, Or.inr ⟨ha0, ha1⟩, rfl⟩
  · apply le_antisymm
    · have hnet : InternalEpsilonNet usualDist τ {some (-a), some a} {some (-a)} := by
        constructor
        · simp
        · intro x hx
          rcases hx with rfl | hx
          · exact ⟨some (-a), by simp, by simpa [usualDist, optionDist] using hτ0⟩
          · have : x = some a := by simpa using hx
            subst x
            refine ⟨some (-a), by simp, ?_⟩
            apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (ne_of_lt hτtop)).mpr
            have heq : |a - (-a)| = 2 * a := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity : 0 < 2 * a)]
            rw [heq]
            exact ha2
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty usualDist τ _ ⟨some (-a), by simp⟩

end OET.Ch03
