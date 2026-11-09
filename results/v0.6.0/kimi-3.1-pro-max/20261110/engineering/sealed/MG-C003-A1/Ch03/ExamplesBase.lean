import Ch03.Entropy

namespace OET.Ch03

set_option maxHeartbeats 1600000

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-- Real points together with the absorbing point. -/
abbrev RealBase := Option ℝ

/-- Extend a real-valued distance by absorption isolation. -/
def optionDist (ρ : ℝ → ℝ → ℝ) : RealBase → RealBase → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => ENNReal.ofReal (ρ x y)

theorem optionDist_extended (ρ : ℝ → ℝ → ℝ)
    (h0 : ∀ x, ρ x x = 0) (hsymm : ∀ x y, ρ x y = ρ y x)
    (htri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (hnonneg : ∀ x y, 0 ≤ ρ x y) :
    ExtendedPseudoMetric RealBase none (optionDist ρ) := by
  refine ⟨⟨some 0, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | none => rfl
    | some x => simp [optionDist, h0]
  · intro x y
    cases x <;> cases y <;> simp [optionDist, hsymm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [optionDist]
    rw [← ENNReal.ofReal_add (hnonneg _ _) (hnonneg _ _)]
    exact ENNReal.ofReal_le_ofReal (htri _ _ _)
  · intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x => rfl

/-- Usual distance on the real part. -/
def usualDist : RealBase → RealBase → ENNReal := optionDist (fun x y => |x - y|)

theorem usualDist_extended : ExtendedPseudoMetric RealBase none usualDist := by
  apply optionDist_extended
  · intro x; simp
  · intro x y; exact abs_sub_comm x y
  · intro x y z; exact abs_sub_le x y z
  · intro x y; exact abs_nonneg _

/-- Absolute-value readout pseudometric on the real part. -/
def absReadDist : RealBase → RealBase → ENNReal := optionDist (fun x y => |(|x| - |y|)|)

theorem absReadDist_extended : ExtendedPseudoMetric RealBase none absReadDist := by
  apply optionDist_extended
  · intro x; simp
  · intro x y; exact abs_sub_comm _ _
  · intro x y z; exact abs_sub_le |x| |y| |z|
  · intro x y; exact abs_nonneg _

@[simp] theorem usualDist_some (x y : ℝ) :
    usualDist (some x) (some y) = ENNReal.ofReal |x - y| := rfl

@[simp] theorem absReadDist_some (x y : ℝ) :
    absReadDist (some x) (some y) = ENNReal.ofReal |(|x| - |y|)| := rfl

/-- Discrete distance with absorbing-point isolation on `Option (Fin n)`. -/
def finDist {n : ℕ} (x y : Option (Fin n)) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else 1

theorem finDist_extended {n : ℕ} [NeZero n] :
    ExtendedPseudoMetric (Option (Fin n)) none finDist := by
  refine ⟨⟨some ⟨0, NeZero.pos n⟩, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [finDist]
  · intro x y
    by_cases h : x = y
    · subst y; simp [finDist]
    · simp [finDist, h, Ne.symm h, or_comm]
  · intro x y z
    simp only [finDist]
    split_ifs <;> simp_all
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some x => simp [finDist]

/-- Two-point swap counterexample data. -/
def swapOp : Operator (Option (Fin 2)) none where
  func
    | none => none
    | some k => some (if k = 0 then 1 else 0)
  preserves_bot := rfl

def swapDomain : Set (Option (Fin 2)) := {some 0, some 1}

def swapGauge : Unit → Option (Fin 2) → Option (Fin 2) → ENNReal := fun _ => finDist

theorem swap_image : swapOp.func '' swapDomain = swapDomain := by
  ext x
  cases x with
  | none => simp [swapDomain, swapOp]
  | some k =>
      fin_cases k <;> simp [swapDomain, swapOp]

theorem swap_active : () ∈ actComponents swapGauge swapOp swapDomain := by
  constructor
  · intro hc
    have h := hc (some 0) (by simp [swapDomain]) (some 1) (by simp [swapDomain])
    simp [swapGauge, finDist, swapOp] at h
  · intro hi
    have h := hi.2 (some 0) (by simp [swapDomain])
    simp [swapGauge, finDist, swapOp] at h

theorem swap_composite_id : () ∈ idComponents swapGauge (operator_compose swapOp swapOp) swapDomain := by
  constructor
  · intro hc
    have h := hc (some 0) (by simp [swapDomain]) (some 1) (by simp [swapDomain])
    simp [swapGauge, finDist, swapOp, operator_compose] at h
  · intro x hx
    rcases hx with (rfl | hx)
    · norm_num [swapGauge, finDist, swapOp, operator_compose]
    · have : x = some 1 := by simpa [swapDomain] using hx
      subst x
      norm_num [swapGauge, finDist, swapOp, operator_compose]

theorem swap_second_active : () ∈ actComponents swapGauge swapOp (swapOp.func '' swapDomain) := by
  rw [swap_image]
  exact swap_active

/-- Note after Proposition 3.2: both reverse inclusions fail for the same
legal two-point swap. -/
theorem swap_reverse_inclusions_fail :
    ¬ (actComponents swapGauge swapOp swapDomain ∪
        actComponents swapGauge swapOp (swapOp.func '' swapDomain)) ⊆
      actComponents swapGauge (operator_compose swapOp swapOp) swapDomain ∧
    ¬ idComponents swapGauge (operator_compose swapOp swapOp) swapDomain ⊆
      idComponents swapGauge swapOp swapDomain ∩
        idComponents swapGauge swapOp (swapOp.func '' swapDomain) := by
  constructor
  · intro h
    have ha : () ∈ actComponents swapGauge swapOp swapDomain ∪
        actComponents swapGauge swapOp (swapOp.func '' swapDomain) := Or.inl swap_active
    have hcomp := h ha
    exact hcomp.2 swap_composite_id
  · intro h
    have hboth := h swap_composite_id
    exact swap_active.2 hboth.1

/-- Seven-point, two-component counterexample for Proposition 3.3(ii).
Component `0` identifies points 4 and 5; component `1` is discrete. -/
def sevenDist (k : Fin 2) (x y : Option (Fin 7)) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else
    if k = 0 ∧
      ((x = some 4 ∧ y = some 5) ∨ (x = some 5 ∧ y = some 4)) then 0 else 1

theorem sevenDist_extended (k : Fin 2) :
    ExtendedPseudoMetric (Option (Fin 7)) none (sevenDist k) := by
  refine ⟨⟨some 0, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp_all [sevenDist]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [sevenDist]
  · intro x y z
    fin_cases k <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [sevenDist]
  · intro x hx
    fin_cases x <;> simp_all [sevenDist]

def sevenInner : Operator (Option (Fin 7)) none where
  func
    | none => none
    | some 0 => some 4
    | some 1 => some 5
    | some _ => none
  preserves_bot := rfl

def sevenOuter : Operator (Option (Fin 7)) none where
  func
    | none => none
    | some 4 => some 2
    | some 5 => some 3
    | some _ => none
  preserves_bot := rfl

def sevenDomain : Set (Option (Fin 7)) := {some 0, some 1}

/-- Proposition 3.3(ii): inner constancy need not survive the outer map. -/
theorem seven_inner_const_not_composite :
    (0 : Fin 2) ∈ constComponents sevenDist sevenInner sevenDomain ∧
    (0 : Fin 2) ∉ constComponents sevenDist (operator_compose sevenOuter sevenInner) sevenDomain := by
  constructor
  · intro x hx y hy
    simp only [sevenDomain, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [sevenDist, sevenInner]
  · intro hc
    have h := hc (some 0) (by simp [sevenDomain]) (some 1) (by simp [sevenDomain])
    simp [sevenDist, sevenInner, sevenOuter, operator_compose] at h

/-- Input distance `+∞` on two distinct nonabsorbing points; the second
component has unit distance instead. -/
def twoPointDist (k : Fin 2) (x y : Option (Fin 2)) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if k = 0 then ⊤ else 1

theorem twoPointDist_extended (k : Fin 2) :
    ExtendedPseudoMetric (Option (Fin 2)) none (twoPointDist k) := by
  refine ⟨⟨some 0, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp_all [twoPointDist]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [twoPointDist]
  · intro x y z
    fin_cases k <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [twoPointDist]
  · intro x hx
    fin_cases x <;> simp_all [twoPointDist]

def twoPointDomain : Set (Option (Fin 2)) := {some 0, some 1}

def twoPointId : Operator (Option (Fin 2)) none := operator_identity

/-- Proposition 3.8(ii), simultaneously covering `i = j` and `i ≠ j`: an
infinite matrix entry for the identity need not be a constant component. -/
theorem infinite_uniformRadius_not_const (j : Fin 2) :
    annihilationMatrix twoPointDist twoPointId twoPointDomain j 0 = ⊤ ∧
      j ∉ constComponents twoPointDist twoPointId twoPointDomain := by
  have hpoint : ∀ y ∈ twoPointDomain,
      annihilationRadius twoPointId (twoPointDist 0) (twoPointDist j) y twoPointDomain = ⊤ := by
    intro y hy
    rw [annihilationRadius, sSup_eq_top]
    intro b hb
    refine ⟨b + 1, ⟨by positivity, ENNReal.add_lt_top.mpr ⟨hb, ENNReal.one_lt_top⟩, ?_⟩,
      ENNReal.lt_add_right (ne_of_lt hb) (by simp)⟩
    intro x hx
    have hxy : x = y := by
      have hlt : twoPointDist 0 x y < b + 1 := hx.1
      cases x with
      | none => simp [twoPointDomain] at hx
      | some x =>
          cases y with
          | none => simp [twoPointDomain] at hy
          | some y =>
              fin_cases x <;> fin_cases y <;> simp_all [twoPointDist]
    subst x
    exact ⟨hy, by simp [twoPointId, (twoPointDist_extended j).dist_self]⟩
  constructor
  · change componentUniformAnnihilationRadius twoPointDist twoPointId 0 ({j} : Set (Fin 2))
      twoPointDomain = ⊤
    rw [componentUniformRadius_single]
    apply top_unique
    apply le_iInf
    intro y
    rw [hpoint y.1 y.2]
  · intro hc
    have h := hc (some 0) (by simp [twoPointDomain]) (some 1) (by simp [twoPointDomain])
    fin_cases j <;> simp [twoPointDist, twoPointId, operator_identity] at h

end OET.Ch03
