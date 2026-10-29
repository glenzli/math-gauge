import ExtendedBounds

namespace MathGauge.F112

open ENNReal
variable {X : Type*}

theorem finite_bound_exists_iff (d e : X → ℝ≥0∞) :
    (∃ c, c ≠ ∞ ∧ Bound d e c) ↔ ZeroCompatible d e ∧ ratioSup d e ≠ ∞ := by
  constructor
  · rintro ⟨c, hc, hb⟩
    obtain ⟨hz, hr, _⟩ := (bound_iff d e c).mp hb
    exact ⟨hz, ne_top_of_le_ne_top hc hr⟩
  · rintro ⟨hz, hr⟩
    refine ⟨ratioSup d e + 1, by simpa using hr, ?_⟩
    apply (bound_iff d e _).mpr
    refine ⟨hz, le_add_right le_rfl, ?_⟩
    intro h0
    have h1 : (1 : ℝ≥0∞) ≤ ratioSup d e + 1 := le_add_left le_rfl
    rw [h0] at h1
    exact False.elim (by simpa using h1)

theorem least_coefficient_eq (d e : X → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : LeastFinite d e c) : c = ratioSup d e := by
  obtain ⟨hcfin, hcb, hmin⟩ := hc
  obtain ⟨hz, hrc, _⟩ := (bound_iff d e c).mp hcb
  apply le_antisymm _ hrc
  by_contra h
  have hlt : ratioSup d e < c := lt_of_not_ge h
  obtain ⟨b, hrb, hbc⟩ := exists_between hlt
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hrb)
  have hbfin : b ≠ ∞ := ne_top_of_le_ne_top hcfin hbc.le
  have hbb : Bound d e b := (bound_iff d e b).mpr ⟨hz, hrb.le, fun h0 => False.elim (hb0 h0)⟩
  exact (not_le_of_gt hbc) (hmin b hbfin hbb)

theorem least_finite_exists_iff (d e : X → ℝ≥0∞) :
    (∃ c, LeastFinite d e c) ↔
    ZeroCompatible d e ∧ ratioSup d e ≠ ∞ ∧ (ratioSup d e = 0 → TopCompatible d e) := by
  constructor
  · rintro ⟨c, hc⟩
    have heq := least_coefficient_eq d e hc
    subst c
    exact ⟨((bound_iff d e _).mp hc.2.1).1, hc.1,
      ((bound_iff d e _).mp hc.2.1).2.2⟩
  · rintro ⟨hz, hr, ht⟩
    refine ⟨ratioSup d e, hr, (bound_iff d e _).mpr ⟨hz, le_rfl, ht⟩, ?_⟩
    intro b hb hbb
    exact ((bound_iff d e b).mp hbb).2.1

#print axioms finite_bound_exists_iff
#print axioms least_finite_exists_iff
#print axioms least_coefficient_eq

end MathGauge.F112
