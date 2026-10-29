import ExtendedData

namespace MathGauge.F112

open ENNReal

variable {X : Type*}

/-- Division by a nonzero finite extended nonnegative real. -/
private lemma div_le_iff_mul_of_finite_nonzero
    (a b c : ℝ≥0∞) (hb0 : b ≠ 0) (hbtop : b ≠ ∞) :
    a / b ≤ c ↔ a ≤ c * b := by
  first
  | exact ENNReal.div_le_iff hb0 hbtop
  | exact ENNReal.div_le_iff_le_mul hb0 hbtop
  |
    have hinv : b⁻¹ * b = 1 := by
      first
      | exact ENNReal.inv_mul_cancel hb0 hbtop
      | simpa only [mul_comm] using ENNReal.mul_inv_cancel hb0 hbtop
      | exact ENNReal.inv_mul_cancel ⟨hb0, hbtop⟩
      | simpa only [mul_comm] using
          ENNReal.mul_inv_cancel ⟨hb0, hbtop⟩
      | exact?
    have hinv' : b * b⁻¹ = 1 := by
      simpa only [mul_comm] using hinv
    constructor
    · intro h
      have h' := mul_le_mul_right' h b
      simpa only [div_eq_mul_inv, mul_assoc, hinv, mul_one] using h'
    · intro h
      have h' := mul_le_mul_right' h b⁻¹
      simpa only [div_eq_mul_inv, mul_assoc, hinv', mul_one] using h'

private lemma zero_of_bound {d e : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : Bound d e c) : ZeroCompatible d e := by
  intro x hx
  have h : e x ≤ 0 := by
    simpa only [hx, mul_zero] using hc x
  exact le_antisymm h (zero_le _)

private lemma ratio_le_of_bound {d e : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : Bound d e c) : ratioSup d e ≤ c := by
  unfold ratioSup
  refine iSup_le fun x => ?_
  exact
    (div_le_iff_mul_of_finite_nonzero
      (e x) (d x) c x.property.1 x.property.2).2 (hc x)

/-- Characterization of every feasible coefficient, including `∞`. -/
theorem bound_iff (d e : X → ℝ≥0∞) (c : ℝ≥0∞) :
    Bound d e c ↔
      ZeroCompatible d e ∧
        ratioSup d e ≤ c ∧
        (c ≠ 0 ∨ TopCompatible d e) := by
  classical
  constructor
  · intro hc
    refine ⟨zero_of_bound hc, ratio_le_of_bound hc, ?_⟩
    by_cases hc0 : c = 0
    · right
      intro x _
      have h : e x ≤ 0 := by
        simpa only [hc0, zero_mul] using hc x
      exact le_antisymm h (zero_le _)
    · exact Or.inl hc0
  · rintro ⟨hz, hr, hor⟩
    intro x
    by_cases hd0 : d x = 0
    · simpa only [hd0, mul_zero] using
        (le_of_eq (hz x hd0))
    · by_cases hdtop : d x = ∞
      · rcases hor with hc0 | ht
        · have hm : c * ∞ = ∞ := by
            first
            | exact ENNReal.mul_top hc0
            | simpa only [mul_comm] using ENNReal.top_mul hc0
            | simp [hc0]
            | exact?
          rw [hdtop, hm]
          exact le_top
        · rw [ht x hdtop]
          exact zero_le _
      · apply
          (div_le_iff_mul_of_finite_nonzero
            (e x) (d x) c hd0 hdtop).1
        have hratio : e x / d x ≤ ratioSup d e := by
          unfold ratioSup
          exact le_iSup
            (fun y : {y : X // d y ≠ 0 ∧ d y ≠ ∞} =>
              e y / d y)
            ⟨x, hd0, hdtop⟩
        exact le_trans hratio hr

/-- A finite feasible coefficient exists exactly when `Z` holds and `r` is finite. -/
theorem finite_exists_iff (d e : X → ℝ≥0∞) :
    (∃ c : ℝ≥0∞, c ≠ ∞ ∧ Bound d e c) ↔
      ZeroCompatible d e ∧ ratioSup d e ≠ ∞ := by
  classical
  constructor
  · rintro ⟨c, hcfin, hc⟩
    refine ⟨zero_of_bound hc, ?_⟩
    intro hr
    have hrle : ratioSup d e ≤ c := ratio_le_of_bound hc
    have htopc : ∞ ≤ c := by
      simpa only [hr] using hrle
    exact hcfin (le_antisymm le_top htopc)
  · rintro ⟨hz, hr⟩
    let c : ℝ≥0∞ := max (ratioSup d e) 1
    have hrlt : ratioSup d e < ∞ := by
      rcases lt_or_eq_of_le
          (show ratioSup d e ≤ ∞ from le_top) with h | h
      · exact h
      · exact False.elim (hr h)
    have hcfin : c ≠ ∞ := by
      have h : c < ∞ := by
        dsimp [c]
        exact max_lt_iff.mpr ⟨hrlt, by simp⟩
      exact ne_of_lt h
    have hcpos : (0 : ℝ≥0∞) < c := by
      dsimp [c]
      exact lt_of_lt_of_le (by simp) (le_max_right _ _)
    refine ⟨c, hcfin, (bound_iff d e c).2 ?_⟩
    refine ⟨hz, ?_, Or.inl (ne_of_gt hcpos)⟩
    dsimp [c]
    exact le_max_left _ _

/-- Every least finite feasible coefficient equals `r`. -/
theorem least_eq_ratioSup {d e : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : LeastFinite d e c) : c = ratioSup d e := by
  classical
  rcases hc with ⟨hcfin, hbound, hminimal⟩
  have hrle : ratioSup d e ≤ c := ratio_le_of_bound hbound
  refine le_antisymm ?_ hrle
  by_contra hn
  have hrc : ratioSup d e < c := lt_of_not_ge hn
  obtain ⟨b, hrb, hbc⟩ := exists_between hrc
  have hb0 : b ≠ 0 := by
    have hpos : (0 : ℝ≥0∞) < b :=
      lt_of_le_of_lt (zero_le (ratioSup d e)) hrb
    exact ne_of_gt hpos
  have hbfin : b ≠ ∞ := by
    intro hbtop
    have htopc : ∞ ≤ c := by
      simpa only [hbtop] using (le_of_lt hbc)
    exact hcfin (le_antisymm le_top htopc)
  have hbbound : Bound d e b :=
    (bound_iff d e b).2
      ⟨zero_of_bound hbound, le_of_lt hrb, Or.inl hb0⟩
  exact (not_le_of_gt hbc) (hminimal b hbfin hbbound)

/-- Existence criterion for a least finite feasible coefficient. -/
theorem least_exists_iff (d e : X → ℝ≥0∞) :
    (∃ c : ℝ≥0∞, LeastFinite d e c) ↔
      ZeroCompatible d e ∧
        ratioSup d e ≠ ∞ ∧
        (ratioSup d e ≠ 0 ∨ TopCompatible d e) := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    have heq : c = ratioSup d e := least_eq_ratioSup hc
    have hcfin : c ≠ ∞ := hc.1
    have hbound : Bound d e c := hc.2.1
    have hcase : c ≠ 0 ∨ TopCompatible d e :=
      ((bound_iff d e c).1 hbound).2.2
    rw [heq] at hcfin hcase
    exact ⟨zero_of_bound hbound, hcfin, hcase⟩
  · rintro ⟨hz, hrfin, hcase⟩
    refine ⟨ratioSup d e, hrfin, ?_, ?_⟩
    · exact (bound_iff d e (ratioSup d e)).2
        ⟨hz, le_rfl, hcase⟩
    · intro b _ hb
      exact ratio_le_of_bound hb

/-- A one-point example with infinite `d` and nonzero finite `e`. -/
def exampleD (_ : Unit) : ℝ≥0∞ := ∞

def exampleE (_ : Unit) : ℝ≥0∞ := 1

theorem example_bound_one : Bound exampleD exampleE 1 := by
  intro x
  simp [exampleD, exampleE]

theorem example_zeroCompatible : ZeroCompatible exampleD exampleE :=
  zero_of_bound example_bound_one

theorem example_not_topCompatible :
    ¬ TopCompatible exampleD exampleE := by
  intro ht
  have h : (1 : ℝ≥0∞) = 0 := ht () rfl
  exact one_ne_zero h

theorem example_ratioSup : ratioSup exampleD exampleE = 0 := by
  apply le_antisymm
  · unfold ratioSup
    refine iSup_le fun x => ?_
    exact False.elim (x.property.2 rfl)
  · exact zero_le _

/-- The example has a finite feasible coefficient, but no least one. -/
theorem example_finite_but_no_least :
    (∃ c : ℝ≥0∞, c ≠ ∞ ∧ Bound exampleD exampleE c) ∧
      ¬ (∃ c : ℝ≥0∞, LeastFinite exampleD exampleE c) := by
  constructor
  · exact ⟨1, by simp, example_bound_one⟩
  · intro hex
    have hcase :=
      ((least_exists_iff exampleD exampleE).1 hex).2.2
    rcases hcase with hn | ht
    · exact hn example_ratioSup
    · exact example_not_topCompatible ht

end MathGauge.F112
