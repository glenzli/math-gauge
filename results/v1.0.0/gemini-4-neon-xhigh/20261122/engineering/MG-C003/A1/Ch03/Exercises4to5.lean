/-
Formalization of Chapter 3 (Section 3.7: Exercises 3.4 and 3.5)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.MappingEntropyDiff

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Shared Single-Component Family on `ℝ ⊔ {⊥}` -/

/-- Single-component gauge family on `ℝ ⊔ {⊥}` given by the usual Euclidean distance. -/
noncomputable def realWithBotDistFamily : Unit → RealWithBot → RealWithBot → ENNReal :=
  fun _ => realWithBotDist

theorem realWithBotDistFamily_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric RealWithBot none (realWithBotDistFamily u) :=
  fun _ => realWithBotDist_extendedPseudoMetric

/-- Closed real interval `[a, b]` embedded in `ℝ ⊔ {⊥}`. -/
def realIcc (a b : ℝ) : Set RealWithBot :=
  { z | ∃ x : ℝ, z = some x ∧ a ≤ x ∧ x ≤ b }

theorem diamScaleFun_realIcc {a b : ℝ} (hab : a ≤ b) :
    diamScaleFun realWithBotDistFamily () (realIcc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup₂_le
    rintro z₁ ⟨x, rfl, hxa, hxb⟩
    apply iSup₂_le
    rintro z₂ ⟨y, rfl, hya, hyb⟩
    simp only [realWithBotDistFamily, realWithBotDist]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;> linarith
  · apply le_iSup₂_of_le (some a) ⟨a, rfl, le_rfl, hab⟩
    apply le_iSup₂_of_le (some b) ⟨b, rfl, hab, le_rfl⟩
    simp only [realWithBotDistFamily, realWithBotDist]
    rw [show a - b = -(b - a) by ring, abs_neg, abs_of_nonneg (sub_nonneg.mpr hab)]

/-! ### Exercise 3.4: Threshold Classification under Changing Input Domains (CH03-P29-01..05) -/

/-- Floor operator `f(x) = ⌊x⌋` on `ℝ`, `f(⊥) = ⊥`. -/
noncomputable def floorOp : Operator RealWithBot none where
  func
    | none => none
    | some x => some (⌊x⌋ : ℝ)
  preserves_bot := rfl

def ex34D1 : Set RealWithBot := realIcc 0 (1 / 2)
def ex34D2 : Set RealWithBot := realIcc (9 / 10) (11 / 10)
def ex34D3 : Set RealWithBot := {some 0, some 2}
def ex34D4 : Set RealWithBot := realIcc 0 2

/-- Helper: If `D` contains `[c, 1]` for some `c < 1`, then `r^N_{floorOp}(1 | D) = 0`. -/
theorem floorOp_pointwise_zero_at_one {D : Set RealWithBot} {c : ℝ}
    (hc : c < 1) (hsub : ∀ x : ℝ, c ≤ x → x ≤ 1 → some x ∈ D) :
    pointwiseNullRadiusComp realWithBotDistFamily floorOp () () D (some 1) = 0 := by
  apply pointwiseNullRadius_eq_zero_of_no_legal
  rintro r ⟨hr0, hrt, hrad⟩
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt)
  let x : ℝ := max c (1 - r.toReal / 2)
  have hx_ge : c ≤ x := le_max_left _ _
  have hx_lt1 : x < 1 := max_lt hc (by linarith)
  have hx_in : some x ∈ D := hsub x hx_ge (le_of_lt hx_lt1)
  have hdist : realWithBotDistFamily () (some x) (some 1) < r := by
    simp only [realWithBotDistFamily, realWithBotDist]
    rw [← ENNReal.ofReal_toReal (ne_of_lt hrt)]
    apply (ENNReal.ofReal_lt_ofReal_iff hr_real_pos).mpr
    rw [abs_of_neg (by linarith)]
    have hx_ge2 : 1 - r.toReal / 2 ≤ x := le_max_right _ _
    linarith
  have hout := hrad (some x) hx_in hdist
  have hfl_lt : (⌊x⌋ : ℤ) < 1 := Int.floor_lt.mpr (by simpa using hx_lt1)
  have hfl1 : (⌊(1 : ℝ)⌋ : ℤ) = 1 := Int.floor_one
  simp only [realWithBotDistFamily, floorOp, realWithBotDist, hfl1] at hout
  have hne_real : ((⌊x⌋ : ℤ) : ℝ) ≠ (1 : ℝ) := by
    intro hEq
    have hEqInt : (⌊x⌋ : ℤ) = 1 := by exact_mod_cast hEq
    omega
  have habs_pos : 0 < |((⌊x⌋ : ℤ) : ℝ) - ((1 : ℤ) : ℝ)| := by
    rw [abs_pos, sub_ne_zero]
    simpa using hne_real
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr habs_pos)) hout

/-- Exercise 3.4(i-a) (CH03-P29-01): `D = [0, 1/2]` has `diam = 1/2`, uniform nullification
radius `= +∞`, and threshold type `(1, 1)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_a :
    ex34D1.Nonempty ∧
    ex34D1 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D1 = ENNReal.ofReal (1 / 2) ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D1 = ⊤ ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D1 () () = (1, 1) := by
  have hne : ex34D1.Nonempty := ⟨some 0, ⟨0, rfl, le_rfl, by norm_num⟩⟩
  have hdom : ex34D1 ⊆ dom floorOp := by
    rintro z ⟨x, rfl, _⟩; simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D1 = ENNReal.ofReal (1 / 2) := by
    simpa [ex34D1] using diamScaleFun_realIcc (a := (0 : ℝ)) (b := 1 / 2) (by norm_num)
  have hconst : ∀ x ∈ ex34D1, ∀ y ∈ ex34D1,
      realWithBotDistFamily () (floorOp.func x) (floorOp.func y) = 0 := by
    rintro z₁ ⟨x, rfl, hx0, hx1⟩ z₂ ⟨y, rfl, hy0, hy1⟩
    have hfx : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx0, by linarith⟩
    have hfy : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hy0, by linarith⟩
    simp [realWithBotDistFamily, floorOp, hfx, hfy, realWithBotDist]
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D1 = ⊤ := by
    apply top_unique
    apply le_iInf₂
    intro y hy
    rw [pointwiseNullRadius_eq_top_of_all_finite_pos]
    intro r hr0 hrt
    exact ⟨hr0, hrt, fun x hx _ => hconst x hx y hy⟩
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D1 () () = (1, 1) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D1 () ()).1]
    refine ⟨?_, ?_⟩
    · change diamScaleFun realWithBotDistFamily () ex34D1 < 1
      rw [hdiam, ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
    · rw [hrad]; exact le_top
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(i-b) (CH03-P29-02): `D = [9/10, 11/10]` has `diam = 1/5`, uniform nullification
radius `= 0`, and threshold type `(1, 0)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_b :
    ex34D2.Nonempty ∧
    ex34D2 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D2 = ENNReal.ofReal (1 / 5) ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D2 = 0 ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D2 () () = (1, 0) := by
  have hne : ex34D2.Nonempty := ⟨some 1, ⟨1, rfl, by norm_num, by norm_num⟩⟩
  have hdom : ex34D2 ⊆ dom floorOp := by
    rintro z ⟨x, rfl, _⟩; simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D2 = ENNReal.ofReal (1 / 5) := by
    have h := diamScaleFun_realIcc (a := (9 / 10 : ℝ)) (b := 11 / 10) (by norm_num)
    have hsub : (11 / 10 : ℝ) - 9 / 10 = 1 / 5 := by norm_num
    simpa [ex34D2, hsub] using h
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D2 = 0 := by
    apply le_antisymm _ (zero_le _)
    have h1 : some (1 : ℝ) ∈ ex34D2 := ⟨1, rfl, by norm_num, by norm_num⟩
    have hpt := floorOp_pointwise_zero_at_one (D := ex34D2) (c := 9 / 10) (by norm_num)
      (fun x hx1 hx2 => ⟨x, rfl, hx1, by linarith⟩)
    calc
      uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D2
          ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D2 (some 1) :=
            iInf₂_le (some 1) h1
      _ = 0 := hpt
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D2 () () = (1, 0) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D2 () ()).2.1]
    refine ⟨?_, ?_⟩
    · change diamScaleFun realWithBotDistFamily () ex34D2 < 1
      rw [hdiam, ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
    · rw [hrad]; exact zero_lt_one
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(i-c) (CH03-P29-03): `D = {0, 2}` has `diam = 2`, uniform nullification radius `= 2`,
and threshold type `(0, 1)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_c :
    ex34D3.Nonempty ∧
    ex34D3 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D3 = 2 ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 = 2 ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D3 () () = (0, 1) := by
  have hne : ex34D3.Nonempty := ⟨some 0, Or.inl rfl⟩
  have hdom : ex34D3 ⊆ dom floorOp := by
    intro z hz; rcases hz with rfl | rfl <;> simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D3 = 2 := by
    apply le_antisymm
    · apply iSup₂_le; intro x hx
      apply iSup₂_le; intro y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        norm_num [realWithBotDistFamily, realWithBotDist]
    · apply le_iSup₂_of_le (some 0) (Or.inl rfl)
      apply le_iSup₂_of_le (some 2) (Or.inr rfl)
      norm_num [realWithBotDistFamily, realWithBotDist]
  have hpt : ∀ y ∈ ex34D3,
      pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D3 y = 2 := by
    intro y hy
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨_, _, hrad⟩
      by_contra hgt
      have h2lt : (2 : ENNReal) < r := lt_of_not_ge hgt
      rcases hy with rfl | rfl
      · have hdist : realWithBotDistFamily () (some 2) (some 0) < r := by
          simpa [realWithBotDistFamily, realWithBotDist] using h2lt
        have hout := hrad (some 2) (Or.inr rfl) hdist
        simp [realWithBotDistFamily, floorOp, realWithBotDist] at hout
      · have hdist : realWithBotDistFamily () (some 0) (some 2) < r := by
          simpa [realWithBotDistFamily, realWithBotDist] using h2lt
        have hout := hrad (some 0) (Or.inl rfl) hdist
        simp [realWithBotDistFamily, floorOp, realWithBotDist] at hout
    · apply le_sSup
      refine ⟨by norm_num, ENNReal.ofNat_lt_top, ?_⟩
      intro x hx hdist
      have hxy : x = y := by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exfalso; simp [realWithBotDistFamily, realWithBotDist] at hdist
        · exfalso; simp [realWithBotDistFamily, realWithBotDist] at hdist
        · rfl
      subst hxy
      exact realWithBotDist_extendedPseudoMetric.dist_self _
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 = 2 := by
    apply le_antisymm
    · calc
        uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3
            ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D3 (some 0) :=
              iInf₂_le (some 0) (Or.inl rfl)
        _ = 2 := hpt (some 0) (Or.inl rfl)
    · apply le_iInf₂
      intro y hy
      change 2 ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D3 y
      rw [hpt y hy]
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D3 () () = (0, 1) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D3 () ()).2.2.1]
    refine ⟨?_, ?_⟩
    · change 1 ≤ diamScaleFun realWithBotDistFamily () ex34D3
      rw [hdiam]; norm_num
    · rw [hrad]; norm_num
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(i-d) (CH03-P29-04): `D = [0, 2]` has `diam = 2`, uniform nullification radius `= 0`,
and threshold type `(0, 0)` for `τ_σ = τ_N = 1`. -/
theorem exercise_3_4_i_d :
    ex34D4.Nonempty ∧
    ex34D4 ⊆ dom floorOp ∧
    diamScaleFun realWithBotDistFamily () ex34D4 = 2 ∧
    uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D4 = 0 ∧
    thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D4 () () = (0, 0) := by
  have hne : ex34D4.Nonempty := ⟨some 0, ⟨0, rfl, le_rfl, by norm_num⟩⟩
  have hdom : ex34D4 ⊆ dom floorOp := by
    rintro z ⟨x, rfl, _⟩; simp [dom, floorOp]
  have hdiam : diamScaleFun realWithBotDistFamily () ex34D4 = 2 := by
    simpa [ex34D4] using diamScaleFun_realIcc (a := (0 : ℝ)) (b := 2) (by norm_num)
  have hrad : uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D4 = 0 := by
    apply le_antisymm _ (zero_le _)
    have h1 : some (1 : ℝ) ∈ ex34D4 := ⟨1, rfl, by norm_num, by norm_num⟩
    have hpt := floorOp_pointwise_zero_at_one (D := ex34D4) (c := 0) zero_lt_one
      (fun x hx1 hx2 => ⟨x, rfl, hx1, by linarith⟩)
    calc
      uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D4
          ≤ pointwiseNullRadiusComp realWithBotDistFamily floorOp () () ex34D4 (some 1) :=
            iInf₂_le (some 1) h1
      _ = 0 := hpt
  have htype : thresholdType realWithBotDistFamily (diamScale realWithBotDistFamily) 1 1
      floorOp ex34D4 () () = (0, 0) := by
    rw [(lemma_3_13_partition realWithBotDistFamily (diamScale realWithBotDistFamily)
      1 1 floorOp ex34D4 () ()).2.2.2.1]
    refine ⟨?_, ?_⟩
    · change 1 ≤ diamScaleFun realWithBotDistFamily () ex34D4
      rw [hdiam]; norm_num
    · rw [hrad]; exact zero_lt_one
  exact ⟨hne, hdom, hdiam, hrad, htype⟩

/-- Exercise 3.4(ii) (CH03-P29-05): Without the diameter condition, `\underline{r}^N_{f, d, d}|_D ≥ 1`
does NOT imply global output zero-distance on `D`. Counterexample: `D = {0, 2}` from (i-c),
whose positive uniform nullification radius `2` arises from the point-separation gap `≥ 2` in `D`. -/
theorem exercise_3_4_ii :
    ¬ (∀ D : Set RealWithBot, D.Nonempty → D ⊆ dom floorOp →
        1 ≤ uniformNullRadiusCompOn realWithBotDistFamily floorOp () () D →
        ∀ x ∈ D, ∀ y ∈ D, realWithBotDist (floorOp.func x) (floorOp.func y) = 0) ∧
    (ex34D3.Nonempty ∧ ex34D3 ⊆ dom floorOp ∧
      1 ≤ uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 ∧
      realWithBotDist (floorOp.func (some 0)) (floorOp.func (some 2)) = 2 ∧
      ∀ x ∈ ex34D3, ∀ y ∈ ex34D3, x ≠ y → 2 ≤ realWithBotDist x y) := by
  have h3 := exercise_3_4_i_c
  have hge1 : 1 ≤ uniformNullRadiusCompOn realWithBotDistFamily floorOp () () ex34D3 := by
    rw [h3.2.2.2.1]; norm_num
  have hdiff : realWithBotDist (floorOp.func (some 0)) (floorOp.func (some 2)) = 2 := by
    norm_num [floorOp, realWithBotDist]
  have hgap : ∀ x ∈ ex34D3, ∀ y ∈ ex34D3, x ≠ y → 2 ≤ realWithBotDist x y := by
    intro x hx y hy hne
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hne rfl).elim
    · norm_num [realWithBotDist]
    · norm_num [realWithBotDist]
    · exact (hne rfl).elim
  refine ⟨?_, h3.1, h3.2.1, hge1, hdiff, hgap⟩
  intro hall
  have h0 := hall ex34D3 h3.1 h3.2.1 hge1 (some 0) (Or.inl rfl) (some 2) (Or.inr rfl)
  rw [hdiff] at h0
  norm_num at h0

/-! ### Exercise 3.5: Image Rearrangement and Covering Estimates (CH03-P30-01..04) -/

/-- Four-point domain `U = {0, 1, 2, 3} ⊂ ℝ ⊔ {⊥}` for Exercise 3.5. -/
def ex35U : Set RealWithBot := {some 0, some 1, some 2, some 3}

/-- Operator `f` on `U = {0, 1, 2, 3}` (identity on `U`, `⊥` outside `U`). -/
noncomputable def ex35f : Operator RealWithBot none where
  func
    | none => none
    | some x =>
        if x = 0 then some 0
        else if x = 1 then some 1
        else if x = 2 then some 2
        else if x = 3 then some 3
        else none
  preserves_bot := rfl

/-- Operator `g` on `U = {0, 1, 2, 3}` sending `0 ↦ 0, 1 ↦ 3, 2 ↦ 1, 3 ↦ 2`, and `⊥` outside `U`. -/
noncomputable def ex35g : Operator RealWithBot none where
  func
    | none => none
    | some x =>
        if x = 0 then some 0
        else if x = 1 then some 3
        else if x = 2 then some 1
        else if x = 3 then some 2
        else none
  preserves_bot := rfl

/-- Exercise 3.5(i) (CH03-P30-01): Complete piecewise formula (including all endpoints) for
`N(ε, {0, 1, 2, 3})` over all finite positive `ε`, plus the external-center obstruction at
`ε = 7/4` with `3/2 ∉ U`. -/
theorem exercise_3_5_i :
    (∀ ε : ENNReal, 0 < ε → ε ≤ 1 → covering_number realWithBotDist ε ex35U = 4) ∧
    (∀ ε : ENNReal, 1 < ε → ε ≤ 2 → covering_number realWithBotDist ε ex35U = 2) ∧
    (∀ ε : ENNReal, 2 < ε → ε < ⊤ → covering_number realWithBotDist ε ex35U = 1) ∧
    (ex35U ⊆ ball realWithBotDist (some (3 / 2)) (ENNReal.ofReal (7 / 4)) ∧
      some (3 / 2) ∉ ex35U ∧
      ¬ InternalEpsilonNet realWithBotDist (ENNReal.ofReal (7 / 4)) ex35U {some (3 / 2)} ∧
      covering_number realWithBotDist (ENNReal.ofReal (7 / 4)) ex35U = 2) := by
  classical
  have h1 : ∀ ε : ENNReal, 0 < ε → ε ≤ 1 → covering_number realWithBotDist ε ex35U = 4 := by
    intro ε hε_pos hε_le1
    let s4 : Finset RealWithBot := {some 0, some 1, some 2, some 3}
    have hs4_card : s4.card = 4 := by
      have h01 : some (0 : ℝ) ≠ some 1 := by simp
      have h02 : some (0 : ℝ) ≠ some 2 := by simp
      have h03 : some (0 : ℝ) ≠ some 3 := by simp
      have h12 : some (1 : ℝ) ≠ some 2 := by simp
      have h13 : some (1 : ℝ) ≠ some 3 := by simp
      have h23 : some (2 : ℝ) ≠ some 3 := by simp
      simp [s4, h01, h02, h03, h12, h13, h23]
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist ε ex35U s4 := by
        constructor
        · intro c hc
          simp only [s4, Finset.coe_insert, Finset.coe_singleton] at hc
          exact hc
        · intro x hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨some 0, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
          · exact ⟨some 1, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
          · exact ⟨some 2, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
          · exact ⟨some 3, by simp [s4], by simp [realWithBotDist, hε_pos]⟩
      simpa [hs4_card] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      have hmem_all : s4 ⊆ S := by
        intro x hx
        have hxU : x ∈ ex35U := by
          simp only [s4, Finset.mem_insert, Finset.mem_singleton] at hx
          exact hx
        rcases hS.2 x hxU with ⟨c, hcS, hdist⟩
        have hlt1 : realWithBotDist x c < 1 := lt_of_lt_of_le hdist hε_le1
        have hxc : x = c := by
          rcases hxU with rfl | rfl | rfl | rfl <;> rcases hS.1 hcS with rfl | rfl | rfl | rfl
          · rfl
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · rfl
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · rfl
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · exfalso; norm_num [realWithBotDist] at hlt1
          · rfl
        rwa [hxc]
      have hcard : 4 ≤ S.card := by
        rw [← hs4_card]; exact Finset.card_le_card hmem_all
      exact_mod_cast hcard
  have h2 : ∀ ε : ENNReal, 1 < ε → ε ≤ 2 → covering_number realWithBotDist ε ex35U = 2 := by
    intro ε hε_gt1 hε_le2
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist ε ex35U {some 0, some 2} := by
        constructor
        · intro c hc
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hc
          rcases hc with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
        · intro x hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨some 0, by simp, by simp [realWithBotDist, lt_trans zero_lt_one hε_gt1]⟩
          · exact ⟨some 0, by simp, by simpa [realWithBotDist] using hε_gt1⟩
          · exact ⟨some 2, by simp, by simp [realWithBotDist, lt_trans zero_lt_one hε_gt1]⟩
          · exact ⟨some 2, by simp, by
              have h32 : realWithBotDist (some 3) (some 2) = 1 := by norm_num [realWithBotDist]
              rw [h32]; exact hε_gt1⟩
      have hcard : ({some (0 : ℝ), some (2 : ℝ)} : Finset RealWithBot).card = 2 := by
        rw [Finset.card_pair (by simp)]
      simpa [hcard] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      rcases hS.2 (some 0) (Or.inl rfl) with ⟨c₀, hc₀S, hdist₀⟩
      rcases hS.2 (some 3) (Or.inr (Or.inr (Or.inr rfl))) with ⟨c₃, hc₃S, hdist₃⟩
      have hc₀_lt2 : realWithBotDist (some 0) c₀ < 2 := lt_of_lt_of_le hdist₀ hε_le2
      have hc₃_lt2 : realWithBotDist (some 3) c₃ < 2 := lt_of_lt_of_le hdist₃ hε_le2
      have hne : c₀ ≠ c₃ := by
        intro hEq
        subst hEq
        rcases hS.1 hc₀S with rfl | rfl | rfl | rfl
        · norm_num [realWithBotDist] at hc₃_lt2
        · norm_num [realWithBotDist] at hc₃_lt2
        · norm_num [realWithBotDist] at hc₀_lt2
        · norm_num [realWithBotDist] at hc₀_lt2
      have hsub : ({c₀, c₃} : Finset RealWithBot) ⊆ S := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption
      have hcard : 2 ≤ S.card := by
        calc
          2 = ({c₀, c₃} : Finset RealWithBot).card := (Finset.card_pair hne).symm
          _ ≤ S.card := Finset.card_le_card hsub
      exact_mod_cast hcard
  have h3 : ∀ ε : ENNReal, 2 < ε → ε < ⊤ → covering_number realWithBotDist ε ex35U = 1 := by
    intro ε hε_gt2 _hε_fin
    apply le_antisymm
    · have hnet : InternalEpsilonNet realWithBotDist ε ex35U {some 1} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc; exact Or.inr (Or.inl rfl)
        · intro x hx
          refine ⟨some 1, Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl
          · have h1lt2 : (1 : ENNReal) < 2 := ENNReal.one_lt_two
            simpa [realWithBotDist] using lt_trans h1lt2 hε_gt2
          · simp [realWithBotDist, lt_trans (show (0 : ENNReal) < 2 by norm_num) hε_gt2]
          · have h21 : realWithBotDist (some 2) (some 1) = 1 := by norm_num [realWithBotDist]
            rw [h21]
            exact lt_trans ENNReal.one_lt_two hε_gt2
          · have h31 : realWithBotDist (some 3) (some 1) = 2 := by norm_num [realWithBotDist]
            rw [h31]
            exact hε_gt2
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty _ _ _ ⟨some 0, Or.inl rfl⟩
  have h74_gt1 : (1 : ENNReal) < ENNReal.ofReal (7 / 4) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h74_le2 : ENNReal.ofReal (7 / 4) ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hball_ext : ex35U ⊆ ball realWithBotDist (some (3 / 2)) (ENNReal.ofReal (7 / 4)) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      (simp only [ball, Set.mem_setOf_eq, realWithBotDist]
       apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 7 / 4)).mpr
       norm_num)
  have hnot_mem : some (3 / 2 : ℝ) ∉ ex35U := by
    rintro (h | h | h | h) <;> (injection h with h'; norm_num at h')
  have hnot_net : ¬ InternalEpsilonNet realWithBotDist (ENNReal.ofReal (7 / 4)) ex35U {some (3 / 2)} := by
    intro hnet
    exact hnot_mem (hnet.1 (Finset.mem_singleton_self _))
  exact ⟨h1, h2, h3, hball_ext, hnot_mem, hnot_net, h2 _ h74_gt1 h74_le2⟩

/-- Exercise 3.5(ii) (CH03-P30-02): Domains, images (`f(U) = g(U) = U`), identical covering numbers
at all finite positive `ε`, and zero mapping entropy difference for both `f` and `g`. -/
theorem exercise_3_5_ii :
    dom ex35f = ex35U ∧
    dom ex35g = ex35U ∧
    operator_image ex35f ex35U = ex35U ∧
    operator_image ex35g ex35U = ex35U ∧
    ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number realWithBotDist ε (operator_image ex35f ex35U) =
        covering_number realWithBotDist ε ex35U ∧
      covering_number realWithBotDist ε (operator_image ex35g ex35U) =
        covering_number realWithBotDist ε ex35U ∧
      covering_number realWithBotDist ε (operator_image ex35f ex35U) =
        covering_number realWithBotDist ε (operator_image ex35g ex35U) ∧
      MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35f ex35U ∧
      MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35g ex35U ∧
      (∀ hwd, mappingEntropyDiffCompSame realWithBotDistFamily () ε ex35f ex35U hwd = 0) ∧
      (∀ hwd, mappingEntropyDiffCompSame realWithBotDistFamily () ε ex35g ex35U hwd = 0) := by
  have hdomf : dom ex35f = ex35U := by
    ext z
    cases z with
    | none => simp [dom, ex35f, ex35U]
    | some x =>
        simp only [dom, ex35f, ex35U, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, Option.some.injEq]
        by_cases h0 : x = 0
        · simp [h0]
        · by_cases h1 : x = 1
          · simp [h1]
          · by_cases h2 : x = 2
            · simp [h2]
            · by_cases h3 : x = 3
              · simp [h3]
              · simp [h0, h1, h2, h3]
  have hdomg : dom ex35g = ex35U := by
    ext z
    cases z with
    | none => simp [dom, ex35g, ex35U]
    | some x =>
        simp only [dom, ex35g, ex35U, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, Option.some.injEq]
        by_cases h0 : x = 0
        · simp [h0]
        · by_cases h1 : x = 1
          · simp [h1]
          · by_cases h2 : x = 2
            · simp [h2]
            · by_cases h3 : x = 3
              · simp [h3]
              · simp [h0, h1, h2, h3]
  have himgf : operator_image ex35f ex35U = ex35U := by
    ext z
    simp only [operator_image, ex35U, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩ <;> norm_num [ex35f]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨some 0, Or.inl rfl, by norm_num [ex35f]⟩
      · exact ⟨some 1, Or.inr (Or.inl rfl), by norm_num [ex35f]⟩
      · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex35f]⟩
      · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), by norm_num [ex35f]⟩
  have himgg : operator_image ex35g ex35U = ex35U := by
    ext z
    simp only [operator_image, ex35U, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩ <;> norm_num [ex35g]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨some 0, Or.inl rfl, by norm_num [ex35g]⟩
      · exact ⟨some 2, Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex35g]⟩
      · exact ⟨some 3, Or.inr (Or.inr (Or.inr rfl)), by norm_num [ex35g]⟩
      · exact ⟨some 1, Or.inr (Or.inl rfl), by norm_num [ex35g]⟩
  have hU_ne : ex35U.Nonempty := ⟨some 0, Or.inl rfl⟩
  have hU_fin : ex35U.Finite := by
    simp only [ex35U]
    exact ((Set.finite_singleton _).insert _).insert _ |>.insert _
  refine ⟨hdomf, hdomg, himgf, himgg, ?_⟩
  intro ε hε_pos hε_fin
  have hcov_fin : covering_number realWithBotDist ε ex35U < ⊤ :=
    lt_of_le_of_lt (covering_number_le_card_of_finite realWithBotDist_extendedPseudoMetric hε_pos hU_fin)
      (ENNReal.natCast_lt_top _)
  have hwdf : MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35f ex35U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]; exact Or.inl hcov_fin
  have hwdg : MappingEntropyDiffWellDefined realWithBotDistFamily {()} {()} ε ex35g ex35U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]; exact Or.inl hcov_fin
  refine ⟨by rw [himgf], by rw [himgg], by rw [himgf, himgg], hwdf, hwdg, ?_, ?_⟩
  · intro hwd
    change mappingEntropyDiffComp realWithBotDistFamily () () ε ex35f ex35U hwd = 0
    rw [mappingEntropyDiffComp_eq, himgf]
    change metric_entropy realWithBotDist ε ex35U - metric_entropy realWithBotDist ε ex35U = 0
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU_ne hcov_fin]
    exact_mod_cast sub_self _
  · intro hwd
    change mappingEntropyDiffComp realWithBotDistFamily () () ε ex35g ex35U hwd = 0
    rw [mappingEntropyDiffComp_eq, himgg]
    change metric_entropy realWithBotDist ε ex35U - metric_entropy realWithBotDist ε ex35U = 0
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU_ne hcov_fin]
    exact_mod_cast sub_self _

/-- Exercise 3.5(iii-a) (CH03-P30-03): Minimal scalar Lip constants on `U = {0, 1, 2, 3}` are
`L_f = 1` for `f` and `L_g = 3` for `g`, with both sufficiency and necessity proved. -/
theorem exercise_3_5_iii_a :
    (∀ x ∈ ex35U, ∀ y ∈ ex35U,
      realWithBotDist (ex35f.func x) (ex35f.func y) ≤ 1 * realWithBotDist x y) ∧
    (∀ L : ENNReal,
      (∀ x ∈ ex35U, ∀ y ∈ ex35U,
        realWithBotDist (ex35f.func x) (ex35f.func y) ≤ L * realWithBotDist x y) →
      1 ≤ L) ∧
    (∀ x ∈ ex35U, ∀ y ∈ ex35U,
      realWithBotDist (ex35g.func x) (ex35g.func y) ≤ 3 * realWithBotDist x y) ∧
    (∀ L : ENNReal,
      (∀ x ∈ ex35U, ∀ y ∈ ex35U,
        realWithBotDist (ex35g.func x) (ex35g.func y) ≤ L * realWithBotDist x y) →
      3 ≤ L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [ex35f, realWithBotDist]
  · intro L hL
    have h := hL (some 0) (Or.inl rfl) (some 1) (Or.inr (Or.inl rfl))
    norm_num [ex35f, realWithBotDist] at h
    exact h
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      (simp only [ex35g, realWithBotDist]; norm_num)
  · intro L hL
    have h := hL (some 0) (Or.inl rfl) (some 1) (Or.inr (Or.inl rfl))
    norm_num [ex35g, realWithBotDist] at h
    exact h

/-- Exercise 3.5(iii-b) (CH03-P30-04): At `ε = 7/4`, apply Proposition 3.19's covering-number
upper bound with optimal `L_f = 1` and `L_g = 3` and compare with the true covering numbers:
for `f`, bound `N(7/4, U) = 2` equals the true `2`; for `g`, bound `N(7/12, U) = 4` strictly
exceeds the true `2`. -/
theorem exercise_3_5_iii_b :
    let ε : ENNReal := ENNReal.ofReal (7 / 4)
    covering_number realWithBotDist ε (operator_image ex35f ex35U) ≤
      covering_number realWithBotDist (ε / 1) ex35U ∧
    covering_number realWithBotDist ε (operator_image ex35g ex35U) ≤
      covering_number realWithBotDist (ε / 3) ex35U ∧
    covering_number realWithBotDist ε (operator_image ex35f ex35U) = 2 ∧
    covering_number realWithBotDist (ε / 1) ex35U = 2 ∧
    covering_number realWithBotDist ε (operator_image ex35f ex35U) =
      covering_number realWithBotDist (ε / 1) ex35U ∧
    covering_number realWithBotDist ε (operator_image ex35g ex35U) = 2 ∧
    covering_number realWithBotDist (ε / 3) ex35U = 4 ∧
    covering_number realWithBotDist ε (operator_image ex35g ex35U) <
      covering_number realWithBotDist (ε / 3) ex35U := by
  intro ε
  have hε_pos : 0 < ε := ENNReal.ofReal_pos.mpr (by norm_num)
  have hε_fin : ε < ⊤ := ENNReal.ofReal_lt_top
  have hlip := exercise_3_5_iii_a
  have hbound_f : covering_number realWithBotDist ε (operator_image ex35f ex35U) ≤
      covering_number realWithBotDist (ε / 1) ex35U :=
    prop_3_19_covering_le realWithBotDistFamily ex35f ex35U () () ε 1
      hε_pos hε_fin zero_lt_one ENNReal.one_lt_top hlip.1
  have hbound_g : covering_number realWithBotDist ε (operator_image ex35g ex35U) ≤
      covering_number realWithBotDist (ε / 3) ex35U :=
    prop_3_19_covering_le realWithBotDistFamily ex35g ex35U () () ε 3
      hε_pos hε_fin (by norm_num) ENNReal.ofNat_lt_top hlip.2.2.1
  have hcovU74 : covering_number realWithBotDist ε ex35U = 2 := exercise_3_5_i.2.2.2.2.2.2
  have himgs := exercise_3_5_ii
  have htrue_f : covering_number realWithBotDist ε (operator_image ex35f ex35U) = 2 := by
    rw [himgs.2.2.1, hcovU74]
  have htrue_g : covering_number realWithBotDist ε (operator_image ex35g ex35U) = 2 := by
    rw [himgs.2.2.2.1, hcovU74]
  have hest_f : covering_number realWithBotDist (ε / 1) ex35U = 2 := by
    rw [div_one, hcovU74]
  have h712_eq : ε / 3 = ENNReal.ofReal (7 / 12) := by
    change ENNReal.ofReal (7 / 4) / (3 : ENNReal) = ENNReal.ofReal (7 / 12)
    rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have h712_pos : 0 < ε / 3 := by
    rw [h712_eq]; exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h712_le1 : ε / 3 ≤ 1 := by
    rw [h712_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hest_g : covering_number realWithBotDist (ε / 3) ex35U = 4 :=
    exercise_3_5_i.1 (ε / 3) h712_pos h712_le1
  refine ⟨hbound_f, hbound_g, htrue_f, hest_f, by rw [htrue_f, hest_f], htrue_g, hest_g, ?_⟩
  rw [htrue_g, hest_g]
  norm_num

end Ch03
