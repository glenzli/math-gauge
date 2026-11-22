/-
Formalization of Chapter 3 (Section 3.3: Nullification Radius and Nullification Matrix)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.FiberFactorization

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.3: Pointwise Nullification Radius (CH03-D04) -/

/-- Admissibility of a finite positive radius `r ∈ (0, +∞)` at base point `y` on domain `U`. -/
def IsLegalNullRadius {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0

theorem isLegalNullRadius_iff_ball {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X) (r : ENNReal) :
    IsLegalNullRadius d_in d_out ϕ U y r ↔
      0 < r ∧ r < ⊤ ∧ ball d_in y r ∩ U ⊆ { x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0 } := by
  constructor
  · rintro ⟨hr0, hrt, h⟩
    refine ⟨hr0, hrt, ?_⟩
    rintro x ⟨hball, hxU⟩
    exact ⟨hxU, h x hxU hball⟩
  · rintro ⟨hr0, hrt, h⟩
    refine ⟨hr0, hrt, ?_⟩
    intro x hxU hlt
    exact (h ⟨hlt, hxU⟩).2

theorem isLegalNullRadius_subfamily_iff_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X)
    (y : X) (r : ENNReal) :
    IsLegalNullRadius (d i) (subfamily_pseudometric d J) ϕ U y r ↔
      0 < r ∧ r < ⊤ ∧ ball (d i) y r ∩ U ⊆ compFiber d ϕ J U (ϕ.func y) :=
  isLegalNullRadius_iff_ball (d i) (subfamily_pseudometric d J) ϕ U y r

theorem isLegalNullRadius_mono_down {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X}
    {r₁ r₂ : ENNReal} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂)
    (h₂ : IsLegalNullRadius d_in d_out ϕ U y r₂) :
    IsLegalNullRadius d_in d_out ϕ U y r₁ := by
  refine ⟨hr₁, lt_of_le_of_lt hle h₂.2.1, ?_⟩
  intro x hx hlt
  exact h₂.2.2 x hx (lt_of_lt_of_le hlt hle)

/-- Pointwise nullification inradius `r^N_{ϕ, d_in, d_out}(y | U)`. -/
noncomputable def pointwiseNullRadius {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X) : ENNReal :=
  sSup { r : ENNReal | IsLegalNullRadius d_in d_out ϕ U y r }

/-- Subfamily abbreviation `r^N_{ϕ, i, J}(y | U)`. -/
noncomputable def pointwiseNullRadiusSubfamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) (y : X) :
    ENNReal :=
  pointwiseNullRadius (d i) (subfamily_pseudometric d J) ϕ U y

/-- Single-component abbreviation `r^N_{ϕ, i, j}(y | U)`. -/
noncomputable def pointwiseNullRadiusComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) (y : X) : ENNReal :=
  pointwiseNullRadius (d i) (d j) ϕ U y

/-- Global pointwise nullification radius `r^N_{ϕ, d_in, d_out}(y)` on `dom ϕ`. -/
noncomputable def pointwiseNullRadiusGlobal {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) : ENNReal :=
  pointwiseNullRadius d_in d_out ϕ (dom ϕ) y

theorem pointwiseNullRadiusSubfamily_singleton {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) (y : X) :
    pointwiseNullRadiusSubfamily d ϕ i ({j} : Set I) U y =
      pointwiseNullRadiusComp d ϕ i j U y := by
  simp [pointwiseNullRadiusSubfamily, pointwiseNullRadiusComp, subfamily_pseudometric_singleton]

theorem pointwiseNullRadius_eq_zero_of_no_legal {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X}
    (hnone : ∀ r : ENNReal, ¬ IsLegalNullRadius d_in d_out ϕ U y r) :
    pointwiseNullRadius d_in d_out ϕ U y = 0 := by
  have hempty : { r : ENNReal | IsLegalNullRadius d_in d_out ϕ U y r } = ∅ := by
    ext r; simp [hnone r]
  simp [pointwiseNullRadius, hempty]

theorem pointwiseNullRadius_eq_top_of_all_finite_pos {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X}
    (hall : ∀ r : ENNReal, 0 < r → r < ⊤ → IsLegalNullRadius d_in d_out ϕ U y r) :
    pointwiseNullRadius d_in d_out ϕ U y = ⊤ := by
  by_contra hne
  have hlt : pointwiseNullRadius d_in d_out ϕ U y < ⊤ := lt_top_iff_ne_top.mpr hne
  let r : ENNReal := pointwiseNullRadius d_in d_out ϕ U y + 1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one le_add_self
  have hrt : r < ⊤ := ENNReal.add_lt_top.mpr ⟨hlt, ENNReal.one_lt_top⟩
  have hmem : r ∈ { s : ENNReal | IsLegalNullRadius d_in d_out ϕ U y s } := hall r hr0 hrt
  have hle : r ≤ pointwiseNullRadius d_in d_out ϕ U y := le_sSup hmem
  have hgt : pointwiseNullRadius d_in d_out ϕ U y < r := by
    change pointwiseNullRadius d_in d_out ϕ U y < pointwiseNullRadius d_in d_out ϕ U y + 1
    exact ENNReal.lt_add_right hne one_ne_zero
  exact not_le_of_gt hgt hle

theorem le_pointwiseNullRadius_of_all_lt_legal {X : Type} {bot : X}
    {d_in d_out : X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {y : X} {M : ENNReal}
    (h : ∀ r : ENNReal, 0 < r → r < M → IsLegalNullRadius d_in d_out ϕ U y r) :
    M ≤ pointwiseNullRadius d_in d_out ϕ U y := by
  by_cases hM0 : M = 0
  · subst hM0; exact zero_le _
  · refine le_of_forall_lt fun c hc => ?_
    by_cases hc0 : c = 0
    · subst hc0
      obtain ⟨r, hr0, hrM⟩ := exists_between (pos_iff_ne_zero.mpr hM0)
      exact lt_of_lt_of_le hr0 (le_sSup (h r hr0 hrM))
    · obtain ⟨r, hcr, hrM⟩ := exists_between hc
      have hr0 : 0 < r := lt_trans (pos_iff_ne_zero.mpr hc0) hcr
      exact lt_of_lt_of_le hcr (le_sSup (h r hr0 hrM))

/-! ### Uniform Nullification Radius and Nullification Matrix (CH03-D05) -/

/-- Uniform nullification radius `\underline{r}^N_{ϕ, d_in, d_out}(A | U)` over base set `A`
with evaluation domain `U`. -/
noncomputable def uniformNullRadius {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, pointwiseNullRadius d_in d_out ϕ U y

/-- Uniform nullification radius on `U` (`A = U`): `\underline{r}^N_{ϕ, d_in, d_out}|_U`. -/
noncomputable def uniformNullRadiusOn {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  uniformNullRadius d_in d_out ϕ U U

/-- Subfamily uniform nullification radius on `U`: `\underline{r}^N_{ϕ, i, J}|_U`. -/
noncomputable def uniformNullRadiusSubfamilyOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  uniformNullRadiusOn (d i) (subfamily_pseudometric d J) ϕ U

/-- Component uniform nullification radius on `U`: `\underline{r}^N_{ϕ, i, j}|_U`. -/
noncomputable def uniformNullRadiusCompOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) : ENNReal :=
  uniformNullRadiusOn (d i) (d j) ϕ U

/-- Global uniform nullification radius (`A = U = dom ϕ`). -/
noncomputable def uniformNullRadiusGlobal {X : Type} {bot : X}
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) : ENNReal :=
  uniformNullRadiusOn d_in d_out ϕ (dom ϕ)

/-- Nullification matrix `N(ϕ)|_U` indexed as `(output j, input i)`:
`[N(ϕ)|_U]_{ji} := \underline{r}^N_{ϕ, i, j}|_U`. -/
noncomputable def nullificationMatrix {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : I → I → ENNReal :=
  fun j i => uniformNullRadiusCompOn d ϕ i j U

/-- Global nullification matrix `N(ϕ) = N(ϕ)|_{dom ϕ}`. -/
noncomputable def nullificationMatrixGlobal {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : I → I → ENNReal :=
  nullificationMatrix d ϕ (dom ϕ)

/-! ### Reusable Real Line with Absorbing Element `ℝ ⊔ {⊥}` -/

/-- The real line extended with a distinct absorbing element `none` (`⊥`). -/
abbrev RealWithBot : Type := Option ℝ

/-- Usual Euclidean distance on `ℝ` extended with absorbing-element isolation. -/
noncomputable def realWithBotDist : RealWithBot → RealWithBot → ENNReal
  | none, none => 0
  | some _, none => ⊤
  | none, some _ => ⊤
  | some x, some y => ENNReal.ofReal |x - y|

theorem realWithBotDist_extendedPseudoMetric :
    ExtendedPseudoMetric RealWithBot none realWithBotDist where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := by
    intro x
    cases x <;> simp [realWithBotDist]
  symm := by
    intro x y
    cases x <;> cases y <;> simp [realWithBotDist, abs_sub_comm]
  triangle := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [realWithBotDist]
    rename_i a b c
    calc
      ENNReal.ofReal |a - c| ≤ ENNReal.ofReal (|a - b| + |b - c|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le a b c)
      _ = ENNReal.ofReal |a - b| + ENNReal.ofReal |b - c| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  isolate_bot := by
    intro x hx
    cases x
    · exact (hx rfl).elim
    · rfl

/-! ### Counterexample 3.1: Everywhere-Positive Pointwise Radius with Zero Uniform Infimum (CH03-P10-01..03) -/

/-- Step operator `f(x) = 0` for `x < 0`, `f(x) = 1` for `x ≥ 0`, `f(⊥) = ⊥`. -/
noncomputable def stepOp : Operator RealWithBot none where
  func
    | none => none
    | some x => if x < 0 then some 0 else some 1
  preserves_bot := rfl

/-- Punctured interval `U = [-1, 0) ∪ (0, 1] ⊂ ℝ ⊔ {⊥}`. -/
def stepU : Set RealWithBot :=
  { z | ∃ x : ℝ, z = some x ∧ ((-1 ≤ x ∧ x < 0) ∨ (0 < x ∧ x ≤ 1)) }

/-- Counterexample 3.1 (CH03-P10-01): Legality of the space, step operator, and evaluation domain `U`. -/
theorem counterexample_3_1_valid :
    ExtendedPseudoMetric RealWithBot none realWithBotDist ∧
    stepU.Nonempty ∧
    stepU ⊆ dom stepOp := by
  refine ⟨realWithBotDist_extendedPseudoMetric, ⟨some 1, ⟨1, rfl, Or.inr ⟨zero_lt_one, le_rfl⟩⟩⟩, ?_⟩
  rintro z ⟨x, rfl, _⟩
  simp only [dom, Set.mem_setOf_eq, stepOp]
  split_ifs <;> simp

/-- Counterexample 3.1 (CH03-P10-02): For every `y = some t ∈ stepU`, the legal finite positive
radii are precisely `(0, |t|]`, so `r^N_{f, d, d}(some t | stepU) = |t| > 0`. -/
theorem counterexample_3_1_pointwise {t : ℝ} (ht : some t ∈ stepU) :
    (∀ r : ENNReal,
      IsLegalNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) r ↔
        0 < r ∧ r ≤ ENNReal.ofReal |t|) ∧
    pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) =
      ENNReal.ofReal |t| ∧
    0 < pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) := by
  rcases ht with ⟨t', ht', hbounds⟩
  injection ht' with hteq
  subst hteq
  have ht_ne : t ≠ 0 := by
    rcases hbounds with ⟨_, hlt⟩ | ⟨hgt, _⟩
    · exact ne_of_lt hlt
    · exact ne_of_gt hgt
  have habs_pos : 0 < |t| := abs_pos.mpr ht_ne
  have hlegal_iff : ∀ r : ENNReal,
      IsLegalNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) r ↔
        0 < r ∧ r ≤ ENNReal.ofReal |t| := by
    intro r
    constructor
    · rintro ⟨hr0, hrt, hrad⟩
      refine ⟨hr0, ?_⟩
      by_contra hnotle
      have hgt : ENNReal.ofReal |t| < r := lt_of_not_ge hnotle
      have htoReal_gt : |t| < r.toReal := by
        rw [← ENNReal.ofReal_toReal (ne_of_lt hrt)] at hgt
        exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))).mp hgt
      let δ : ℝ := min 1 ((r.toReal - |t|) / 2)
      have hδ_pos : 0 < δ := lt_min zero_lt_one (by linarith)
      have hδ_le1 : δ ≤ 1 := min_le_left _ _
      have hδ_lt : δ < r.toReal - |t| := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      rcases hbounds with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
      · -- `t < 0`, pick `x = δ ∈ (0, 1] ⊆ stepU`
        have hxU : some δ ∈ stepU := ⟨δ, rfl, Or.inr ⟨hδ_pos, hδ_le1⟩⟩
        have hdist : realWithBotDist (some δ) (some t) < r := by
          rw [realWithBotDist, ← ENNReal.ofReal_toReal (ne_of_lt hrt)]
          apply (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))).mpr
          rw [abs_of_pos (show 0 < δ - t by linarith)]
          rw [abs_of_neg ht_neg] at hδ_lt
          linarith
        have hout := hrad (some δ) hxU hdist
        simp only [stepOp, if_neg (not_lt.mpr (le_of_lt hδ_pos)), if_pos ht_neg,
          realWithBotDist] at hout
        norm_num at hout
      · -- `t > 0`, pick `x = -δ ∈ [-1, 0) ⊆ stepU`
        have hxU : some (-δ) ∈ stepU := ⟨-δ, rfl, Or.inl ⟨by linarith, by linarith⟩⟩
        have hdist : realWithBotDist (some (-δ)) (some t) < r := by
          rw [realWithBotDist, ← ENNReal.ofReal_toReal (ne_of_lt hrt)]
          apply (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt))).mpr
          rw [abs_of_neg (show -δ - t < 0 by linarith)]
          rw [abs_of_pos ht_pos] at hδ_lt
          linarith
        have hout := hrad (some (-δ)) hxU hdist
        simp only [stepOp, if_pos (show -δ < 0 by linarith),
          if_neg (not_lt.mpr (le_of_lt ht_pos)), realWithBotDist] at hout
        norm_num at hout
    · rintro ⟨hr0, hrle⟩
      refine ⟨hr0, lt_of_le_of_lt hrle ENNReal.ofReal_lt_top, ?_⟩
      rintro z ⟨x, rfl, hxbounds⟩ hdist
      have hlt_abs : |x - t| < |t| := by
        have hlt_enn : ENNReal.ofReal |x - t| < ENNReal.ofReal |t| :=
          lt_of_lt_of_le hdist hrle
        exact (ENNReal.ofReal_lt_ofReal_iff habs_pos).mp hlt_enn
      rcases hbounds with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
      · have hx_neg : x < 0 := by
          rw [abs_of_neg ht_neg] at hlt_abs
          have := (abs_lt.mp hlt_abs).2
          linarith
        simp [stepOp, hx_neg, ht_neg, realWithBotDist]
      · have hx_pos : 0 < x := by
          rw [abs_of_pos ht_pos] at hlt_abs
          have := (abs_lt.mp hlt_abs).1
          linarith
        simp [stepOp, not_lt.mpr (le_of_lt hx_pos), not_lt.mpr (le_of_lt ht_pos), realWithBotDist]
  have hrad_eq :
      pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) =
        ENNReal.ofReal |t| := by
    apply le_antisymm
    · apply sSup_le
      intro r hr
      exact ((hlegal_iff r).mp hr).2
    · apply le_sSup
      exact (hlegal_iff (ENNReal.ofReal |t|)).mpr ⟨ENNReal.ofReal_pos.mpr habs_pos, le_rfl⟩
  refine ⟨hlegal_iff, hrad_eq, ?_⟩
  rw [hrad_eq]
  exact ENNReal.ofReal_pos.mpr habs_pos

/-- Counterexample 3.1 (CH03-P10-03): Uniform nullification radius on `stepU` is `0`. -/
theorem counterexample_3_1_uniform_zero :
    uniformNullRadiusOn realWithBotDist realWithBotDist stepOp stepU = 0 := by
  apply le_antisymm _ (zero_le _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  let t : ℝ := min 1 ((ε : ℝ) / 2)
  have ht_pos : 0 < t := lt_min zero_lt_one (by positivity)
  have ht_le1 : t ≤ 1 := min_le_left _ _
  have htU : some t ∈ stepU := ⟨t, rfl, Or.inr ⟨ht_pos, ht_le1⟩⟩
  have hpt := (counterexample_3_1_pointwise htU).2.1
  calc
    uniformNullRadiusOn realWithBotDist realWithBotDist stepOp stepU
        ≤ pointwiseNullRadius realWithBotDist realWithBotDist stepOp stepU (some t) :=
          iInf₂_le (some t) htU
    _ = ENNReal.ofReal |t| := hpt
    _ = ENNReal.ofReal t := by rw [abs_of_pos ht_pos]
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (le_trans (min_le_right _ _) (by linarith))
    _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal

/-! ### Proposition 3.8: Constant Components and Uniform Nullification Radius (CH03-P11-01..03) -/

/-- Proposition 3.8(i-a): If `J ⊆ I_const(ϕ | U)`, then every image-target fiber equals `U`. -/
theorem prop_3_8_i_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (_hUne : U.Nonempty) (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty)
    (hJconst : J ⊆ I_const d ϕ U) :
    ∀ y ∈ U, compFiber d ϕ J U (ϕ.func y) = U := by
  intro y hy
  ext x
  simp only [compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff,
    and_iff_left_iff_imp]
  intro hx j hj
  exact hJconst hj x hx y hy

/-- Proposition 3.8(i-b): If `J ⊆ I_const(ϕ | U)`, then for every input index `i`,
every pointwise radius and the uniform nullification radius equal `+∞`. -/
theorem prop_3_8_i_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty)
    (hJconst : J ⊆ I_const d ϕ U) :
    ∀ i : I,
      (∀ y ∈ U, pointwiseNullRadiusSubfamily d ϕ i J U y = ⊤) ∧
      uniformNullRadiusSubfamilyOn d ϕ i J U = ⊤ := by
  intro i
  have hpt : ∀ y ∈ U, pointwiseNullRadiusSubfamily d ϕ i J U y = ⊤ := by
    intro y hy
    apply pointwiseNullRadius_eq_top_of_all_finite_pos
    intro r hr0 hrt
    rw [isLegalNullRadius_subfamily_iff_fiber]
    refine ⟨hr0, hrt, ?_⟩
    rw [prop_3_8_i_a d ϕ U J hUne hU hJ hJconst y hy]
    exact Set.inter_subset_right
  refine ⟨hpt, ?_⟩
  apply top_unique
  apply le_iInf₂
  intro y hy
  change ⊤ ≤ pointwiseNullRadiusSubfamily d ϕ i J U y
  rw [hpt y hy]

/-- Counterexample pseudometric family on `SwapSpace` for Proposition 3.8(ii):
component `i` assigns `d_i(a, b) = ∞`, and every other component assigns `d_k(a, b) = 1`. -/
def infInputDist {I : Type} [DecidableEq I] (i : I) (k : I) : SwapSpace → SwapSpace → ENNReal
  | .bot, .bot => 0
  | .bot, .a => ⊤
  | .bot, .b => ⊤
  | .a, .bot => ⊤
  | .b, .bot => ⊤
  | .a, .a => 0
  | .b, .b => 0
  | .a, .b => if k = i then ⊤ else 1
  | .b, .a => if k = i then ⊤ else 1

theorem infInputDist_extendedPseudoMetric {I : Type} [DecidableEq I] (i : I) :
    ∀ k : I, ExtendedPseudoMetric SwapSpace .bot (infInputDist i k) := by
  intro k
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by intro x; cases x <;> rfl
      symm := by intro x y; cases x <;> cases y <;> rfl
      triangle := by
        intro x y z
        by_cases hk : k = i <;>
          cases x <;> cases y <;> cases z <;> simp [infInputDist, hk]
      isolate_bot := by
        intro x hx
        cases x
        · exact (hx rfl).elim
        · rfl
        · rfl }

/-- Proposition 3.8(ii): For any index type `I` and any pair `(i, j)` (covering both `i = j`
and `i ≠ j`), `[N(id)|_U]_{ji} = +∞` does not imply `j ∈ I_const(id | U)`. -/
theorem prop_3_8_ii_counterexample {I : Type} [DecidableEq I] (i j : I) :
    (∀ k : I, ExtendedPseudoMetric SwapSpace .bot (infInputDist i k)) ∧
    swapU.Nonempty ∧
    swapU ⊆ dom (@operator_identity SwapSpace .bot) ∧
    nullificationMatrix (infInputDist i) (@operator_identity SwapSpace .bot) swapU j i = ⊤ ∧
    j ∉ I_const (infInputDist i) (@operator_identity SwapSpace .bot) swapU := by
  refine ⟨infInputDist_extendedPseudoMetric i, ⟨.a, Or.inl rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, operator_identity]
  · apply top_unique
    apply le_iInf₂
    intro y hy
    rw [pointwiseNullRadius_eq_top_of_all_finite_pos]
    intro r hr0 hrt
    refine ⟨hr0, hrt, ?_⟩
    intro x hx hdist
    have hxy : x = y := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · simp [infInputDist] at hdist
      · simp [infInputDist] at hdist
      · rfl
    subst hxy
    exact (infInputDist_extendedPseudoMetric i j).dist_self _
  · intro hconst
    have h := hconst .a (Or.inl rfl) .b (Or.inr rfl)
    by_cases hji : j = i <;> simp [operator_identity, infInputDist, hji] at h

/-- Explicit `i = j` instance of Proposition 3.8(ii). -/
theorem prop_3_8_ii_eq {I : Type} [DecidableEq I] (i : I) :
    nullificationMatrix (infInputDist i) (@operator_identity SwapSpace .bot) swapU i i = ⊤ ∧
    i ∉ I_const (infInputDist i) (@operator_identity SwapSpace .bot) swapU :=
  let h := prop_3_8_ii_counterexample i i
  ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- Explicit `i ≠ j` instance of Proposition 3.8(ii). -/
theorem prop_3_8_ii_ne {I : Type} [DecidableEq I] {i j : I} (_hne : i ≠ j) :
    nullificationMatrix (infInputDist i) (@operator_identity SwapSpace .bot) swapU j i = ⊤ ∧
    j ∉ I_const (infInputDist i) (@operator_identity SwapSpace .bot) swapU ∧
    infInputDist i i .a .b = ⊤ ∧ infInputDist i j .a .b = 1 := by
  have h := prop_3_8_ii_counterexample i j
  refine ⟨h.2.2.2.1, h.2.2.2.2, by simp [infInputDist], by simp [infInputDist, _hne.symm]⟩

/-! ### Proposition 3.9: Fibers and Nullification Radius of Identity Components (CH03-P12-01..02) -/

/-- Proposition 3.9(i): For `i ∈ I_id(ϕ | U)` and `y ∈ U`, `Fib_{ϕ, i}(ϕ(y) | U)` equals
the input zero-distance class `{x ∈ U | d_i(x, y) = 0}`. -/
theorem prop_3_9_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X)
    (hU : U ⊆ dom ϕ) (hy : y ∈ U) (hi : i ∈ I_id d ϕ U) :
    compFiberSingle d ϕ i U (ϕ.func y) = { x ∈ U | d i x y = 0 } := by
  ext x
  simp only [compFiberSingle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hzero⟩
    rw [prop_3_1_iii d ϕ U i (hd i) hU hi x hx y hy] at hzero
    exact ⟨hx, hzero⟩
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, ?_⟩
    rw [prop_3_1_iii d ϕ U i (hd i) hU hi x hx y hy]
    exact hzero

/-- Proposition 3.9(ii): If `i ∈ I_id(ϕ | U)` and a finite positive `r₀` ball inside `U`
contains only input zero-distance points, then `r^N_{ϕ, i, i}(y | U) ≥ r₀ > 0`. -/
theorem prop_3_9_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X) (r₀ : ENNReal)
    (hU : U ⊆ dom ϕ) (hy : y ∈ U) (hi : i ∈ I_id d ϕ U)
    (hr₀_pos : 0 < r₀) (hr₀_fin : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ { x ∈ U | d i x y = 0 }) :
    r₀ ≤ pointwiseNullRadiusComp d ϕ i i U y ∧ 0 < pointwiseNullRadiusComp d ϕ i i U y := by
  have hlegal : IsLegalNullRadius (d i) (d i) ϕ U y r₀ := by
    rw [isLegalNullRadius_iff_ball]
    refine ⟨hr₀_pos, hr₀_fin, ?_⟩
    have hfib := prop_3_9_i d hd ϕ U i y hU hy hi
    simpa [compFiberSingle] using hball.trans hfib.symm.subset
  have hle : r₀ ≤ pointwiseNullRadiusComp d ϕ i i U y := le_sSup hlegal
  exact ⟨hle, lt_of_lt_of_le hr₀_pos hle⟩

/-! ### Proposition 3.10: Component Minimum Formula for Uniform Nullification Radius (CH03-P13-01..03) -/

/-- Proposition 3.10 (pointwise): For a finite nonempty output subfamily `J`,
`r^N_{ϕ, i, J}(y | U) = min_{j ∈ J} r^N_{ϕ, i, j}(y | U)`. -/
theorem prop_3_10_pointwise {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    pointwiseNullRadiusSubfamily d ϕ i J U y =
      ⨅ j ∈ J, pointwiseNullRadiusComp d ϕ i j U y ∧
    pointwiseNullRadiusSubfamily d ϕ i J U y =
      J.toFinite.toFinset.inf' (by simpa [Set.Finite.toFinset_nonempty] using hJ)
        (fun j => pointwiseNullRadiusComp d ϕ i j U y) := by
  have hinf : pointwiseNullRadiusSubfamily d ϕ i J U y =
      ⨅ j ∈ J, pointwiseNullRadiusComp d ϕ i j U y := by
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply sSup_le
      intro r hr
      apply le_sSup
      refine ⟨hr.1, hr.2.1, ?_⟩
      intro x hx hlt
      exact (subfamily_pseudometric_eq_zero_iff d J _ _).mp (hr.2.2 x hx hlt) j hj
    · apply le_pointwiseNullRadius_of_all_lt_legal
      intro r hr0 hrlt
      refine ⟨hr0, lt_of_lt_of_le hrlt le_top, ?_⟩
      intro x hx hdx
      rw [subfamily_pseudometric_eq_zero_iff]
      intro j hj
      have hrj : r < pointwiseNullRadiusComp d ϕ i j U y :=
        lt_of_lt_of_le hrlt (iInf₂_le j hj)
      rcases lt_sSup_iff.mp hrj with ⟨r', hr'legal, hrr'⟩
      exact hr'legal.2.2 x hx (lt_trans hdx hrr')
  refine ⟨hinf, ?_⟩
  rw [hinf]
  let s := J.toFinite.toFinset
  have hs : s.Nonempty := by simpa [s, Set.Finite.toFinset_nonempty] using hJ
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro j hj
    exact iInf₂_le j (by simpa [s] using hj)
  · apply le_iInf₂
    intro j hj
    exact Finset.inf'_le (f := fun j => pointwiseNullRadiusComp d ϕ i j U y) (by simpa [s] using hj)

/-- Proposition 3.10 (uniform): Exchanging base-point infimum and finite nonempty minimum gives
`\underline{r}^N_{ϕ, i, J}|_U = min_{j ∈ J} [N(ϕ)|_U]_{ji}`. -/
theorem prop_3_10_uniform {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X)
    (_hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    uniformNullRadiusSubfamilyOn d ϕ i J U =
      ⨅ j ∈ J, nullificationMatrix d ϕ U j i ∧
    uniformNullRadiusSubfamilyOn d ϕ i J U =
      J.toFinite.toFinset.inf' (by simpa [Set.Finite.toFinset_nonempty] using hJ)
        (fun j => nullificationMatrix d ϕ U j i) := by
  have hinf : uniformNullRadiusSubfamilyOn d ϕ i J U =
      ⨅ j ∈ J, nullificationMatrix d ϕ U j i := by
    apply le_antisymm
    · apply le_iInf₂
      intro j hj
      apply le_iInf₂
      intro y hy
      calc
        uniformNullRadiusSubfamilyOn d ϕ i J U
            ≤ pointwiseNullRadiusSubfamily d ϕ i J U y := iInf₂_le y hy
        _ = ⨅ k ∈ J, pointwiseNullRadiusComp d ϕ i k U y :=
            (prop_3_10_pointwise d ϕ i J U y hU hJ).1
        _ ≤ pointwiseNullRadiusComp d ϕ i j U y := iInf₂_le j hj
    · apply le_iInf₂
      intro y hy
      change (⨅ j ∈ J, nullificationMatrix d ϕ U j i) ≤ pointwiseNullRadiusSubfamily d ϕ i J U y
      rw [(prop_3_10_pointwise d ϕ i J U y hU hJ).1]
      apply le_iInf₂
      intro j hj
      calc
        (⨅ k ∈ J, nullificationMatrix d ϕ U k i)
            ≤ nullificationMatrix d ϕ U j i := iInf₂_le j hj
        _ ≤ pointwiseNullRadiusComp d ϕ i j U y := iInf₂_le y hy
  refine ⟨hinf, ?_⟩
  rw [hinf]
  let s := J.toFinite.toFinset
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro j hj
    exact iInf₂_le j (by simpa [s] using hj)
  · apply le_iInf₂
    intro j hj
    exact Finset.inf'_le (f := fun j => nullificationMatrix d ϕ U j i) (by simpa [s] using hj)

/-- Proposition 3.10 (antitonicity): If `J ⊆ K`, then
`\underline{r}^N_{ϕ, i, K}|_U ≤ \underline{r}^N_{ϕ, i, J}|_U`. -/
theorem prop_3_10_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J K : Set I) (U : Set X)
    (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) (hK : K.Nonempty) (hJK : J ⊆ K) :
    uniformNullRadiusSubfamilyOn d ϕ i K U ≤ uniformNullRadiusSubfamilyOn d ϕ i J U := by
  rw [(prop_3_10_uniform d ϕ i K U hUne hU hK).1, (prop_3_10_uniform d ϕ i J U hUne hU hJ).1]
  apply le_iInf₂
  intro j hj
  exact iInf₂_le j (hJK hj)

/-! ### Proposition 3.11: Single-Step Criterion for Fiber Truncation (CH03-P14-01..03) -/

/-- Proposition 3.11 (fiber condition): Membership in `Fib_{ϕ₂, j}(ϕ₂(y) | U₂)` implies
`d_j(ϕ₂(y), ϕ₂(y')) = 0`. -/
theorem prop_3_11_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) {y y' : X}
    (_hU₂ : U₂ ⊆ dom ϕ₂) (_hy : y ∈ U₂) (_hy' : y' ∈ U₂)
    (hfib : y' ∈ compFiberSingle d ϕ₂ j U₂ (ϕ₂.func y)) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rw [(hd j).symm]
  exact hfib.2

/-- Proposition 3.11 (radius condition): Strictly smaller input distance than `r^N_{ϕ₂, i, j}(y | U₂)`
extracts a legal finite positive radius `ρ` and gives `d_j(ϕ₂(y), ϕ₂(y')) = 0`. -/
theorem prop_3_11_radius {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₂ : Operator X bot) (U₂ : Set X) (i j : I) {y y' : X}
    (hU₂ : U₂ ⊆ dom ϕ₂) (hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hlt : d i y y' < pointwiseNullRadiusComp d ϕ₂ i j U₂ y) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rcases lt_sSup_iff.mp hlt with ⟨ρ, hρ_legal, hlt_ρ⟩
  have hmem : y' ∈ compFiberSingle d ϕ₂ j U₂ (ϕ₂.func y) := by
    refine ⟨hy', hρ_legal.2.2 y' hy' ?_⟩
    rw [(hd i).symm]
    exact hlt_ρ
  exact prop_3_11_fiber d hd ϕ₂ U₂ j hU₂ hy hy' hmem

/-- Proposition 3.11 (composite specialization): If `ϕ₁(x), ϕ₁(x') ∈ U₂` and `ϕ₁(x')` lies in
`Fib_{ϕ₂, j}(ϕ₂(ϕ₁(x)) | U₂)`, then `d_j((ϕ₂ ∘ ϕ₁)(x), (ϕ₂ ∘ ϕ₁)(x')) = 0`. -/
theorem prop_3_11_compose {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) {x x' : X}
    (hU₂ : U₂ ⊆ dom ϕ₂) (_hx : x ∈ dom ϕ₁) (_hx' : x' ∈ dom ϕ₁)
    (hfx : ϕ₁.func x ∈ U₂) (hfx' : ϕ₁.func x' ∈ U₂)
    (hfib : ϕ₁.func x' ∈ compFiberSingle d ϕ₂ j U₂ (ϕ₂.func (ϕ₁.func x))) :
    d j ((operator_compose ϕ₂ ϕ₁).func x) ((operator_compose ϕ₂ ϕ₁).func x') = 0 :=
  prop_3_11_fiber d hd ϕ₂ U₂ j hU₂ hfx hfx' hfib

/-! ### Proposition 3.12: Composition Lower Bounds for Uniform Nullification Radius (CH03-P15-01..02) -/

/-- Proposition 3.12(i): If `ϕ₂` preserves zero-distance from `d_l` to `d_j` on the actual
intermediate image `ϕ₁(U)`, then `[N(ϕ₂ ∘ ϕ₁)|_U]_{ji} ≥ [N(ϕ₁)|_U]_{li}`. -/
theorem prop_3_12_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I)
    (_hUne : U.Nonempty) (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁))
    (hpres : ∀ y ∈ operator_image ϕ₁ U, ∀ y' ∈ operator_image ϕ₁ U,
      d l y y' = 0 → d j (ϕ₂.func y) (ϕ₂.func y') = 0) :
    nullificationMatrix d ϕ₁ U l i ≤
      nullificationMatrix d (operator_compose ϕ₂ ϕ₁) U j i := by
  have hU1 : U ⊆ dom ϕ₁ := hU.trans (dom_operator_compose_subset_left ϕ₂ ϕ₁)
  apply le_iInf₂
  intro x hx
  apply le_pointwiseNullRadius_of_all_lt_legal
  intro r hr0 hrlt
  refine ⟨hr0, lt_of_lt_of_le hrlt le_top, ?_⟩
  intro x' hx' hdx
  have hdx_symm : d i x x' < pointwiseNullRadiusComp d ϕ₁ i l U x := by
    rw [(hd i).symm]
    exact lt_of_lt_of_le (lt_trans hdx hrlt) (iInf₂_le x hx)
  have hl0 : d l (ϕ₁.func x) (ϕ₁.func x') = 0 :=
    prop_3_11_radius d hd ϕ₁ U i l hU1 hx hx' hdx_symm
  rw [(hd j).symm]
  exact hpres (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func x') ⟨x', hx', rfl⟩ hl0

/-- Proposition 3.12(ii): Pullback via a finite positive single-channel Lip upper bound `L` on `U`:
`[N(ϕ₂ ∘ ϕ₁)|_U]_{ji} ≥ [N(ϕ₂)|_{ϕ₁(U)}]_{jl} / L` (handling both `0` and `∞` on the RHS). -/
theorem prop_3_12_ii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I) (L : ENNReal)
    (_hUne : U.Nonempty) (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁))
    (_hL_pos : 0 < L) (_hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x') :
    nullificationMatrix d ϕ₂ (operator_image ϕ₁ U) j l / L ≤
      nullificationMatrix d (operator_compose ϕ₂ ϕ₁) U j i := by
  have hU2 : operator_image ϕ₁ U ⊆ dom ϕ₂ := image_subset_dom_of_compose ϕ₂ ϕ₁ hU
  apply le_iInf₂
  intro x hx
  apply le_pointwiseNullRadius_of_all_lt_legal
  intro r hr0 hrlt
  have hrt : r < ⊤ := lt_of_lt_of_le hrlt le_top
  refine ⟨hr0, hrt, ?_⟩
  intro x' hx' hdx
  have hLr_lt : L * r < nullificationMatrix d ϕ₂ (operator_image ϕ₁ U) j l := by
    rw [mul_comm]
    exact ENNReal.mul_lt_of_lt_div hrlt
  have hdl_lt : d l (ϕ₁.func x) (ϕ₁.func x') <
      pointwiseNullRadiusComp d ϕ₂ l j (operator_image ϕ₁ U) (ϕ₁.func x) := by
    calc
      d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x' := hLip x hx x' hx'
      _ = L * d i x' x := by rw [(hd i).symm]
      _ ≤ L * r := mul_le_mul_right (le_of_lt hdx) L
      _ < nullificationMatrix d ϕ₂ (operator_image ϕ₁ U) j l := hLr_lt
      _ ≤ pointwiseNullRadiusComp d ϕ₂ l j (operator_image ϕ₁ U) (ϕ₁.func x) :=
          iInf₂_le (ϕ₁.func x) ⟨x, hx, rfl⟩
  rw [(hd j).symm]
  exact prop_3_11_radius d hd ϕ₂ (operator_image ϕ₁ U) l j hU2
    ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩ hdl_lt

end Ch03
