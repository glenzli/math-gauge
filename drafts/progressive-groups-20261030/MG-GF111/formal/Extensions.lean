import BoundaryExample

namespace MathGauge.F111
open ENNReal
variable {X : Type*}

theorem bound_iff_regular (d e : X → ℝ≥0∞)
    (hd : ∀ x, d x ≠ 0 ∧ d x ≠ ∞) (c : ℝ≥0∞) :
    Bound d e c ↔ ratioSup d e ≤ c := by
  exact ⟨fun h => (ratio_le_iff d e c).mpr (fun x _ _ => h x),
    fun h x => (ratio_le_iff d e c).mp h x (hd x).1 (hd x).2⟩

theorem bound_iff_no_top (d e : X → ℝ≥0∞) (hd : ∀ x, d x ≠ ∞) (c : ℝ≥0∞) :
    Bound d e c ↔ ZeroCompatible d e ∧ ratioSup d e ≤ c := by
  rw [bound_iff]
  exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,fun _ x hx => False.elim (hd x hx)⟩⟩

theorem least_regular (d e : X → ℝ≥0∞) (hd : ∀ x, d x ≠ 0 ∧ d x ≠ ∞)
    (hr : ratioSup d e ≠ ∞) : LeastFinite d e (ratioSup d e) := by
  refine ⟨hr, (bound_iff_regular d e hd _).mpr le_rfl, ?_⟩
  intro b _ hb; exact (bound_iff_regular d e hd b).mp hb

theorem empty_ratio [IsEmpty X] (d e : X → ℝ≥0∞) : ratioSup d e = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro x
  exact isEmptyElim x.val

theorem empty_least [IsEmpty X] (d e : X → ℝ≥0∞) : LeastFinite d e 0 :=
  ⟨by simp, fun x => isEmptyElim x, fun _ _ _ => bot_le⟩

theorem boundary_zero_compatible : ZeroCompatible sourceValue targetValue := by
  intro x hx; simp [sourceValue] at hx

theorem boundary_not_top_compatible : ¬ TopCompatible sourceValue targetValue := by
  intro h; have := h () rfl; simpa [targetValue] using this

theorem boundary_bound_iff (c : ℝ≥0∞) : Bound sourceValue targetValue c ↔ c ≠ 0 := by
  rw [bound_iff, boundary_ratio]
  constructor
  · rintro ⟨_, _, h⟩ hc; exact boundary_not_top_compatible (h hc)
  · intro h; exact ⟨boundary_zero_compatible, bot_le, fun hc => False.elim (h hc)⟩

theorem boundary_finite_iff (c : ℝ≥0∞) :
    (c ≠ ∞ ∧ Bound sourceValue targetValue c) ↔ 0 < c ∧ c < ∞ := by
  rw [boundary_bound_iff, lt_top_iff_ne_top, pos_iff_ne_zero, and_comm]


def LocalFiniteBounds (d e : X → ℝ≥0∞) : Prop :=
  ∀ F : Finset X, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ x ∈ F, e x ≤ c * d x

theorem natural_local_bounds : LocalFiniteBounds (fun _ : ℕ => 1) (fun n => (n : ℝ≥0∞)) := by
  intro F
  refine ⟨(F.sup id : ℕ), by simp, ?_⟩
  intro n hn
  simp only [mul_one]
  exact_mod_cast (Finset.le_sup (f := id) hn)

theorem natural_no_global_bound :
    ¬ ∃ c : ℝ≥0∞, c ≠ ∞ ∧ Bound (fun _ : ℕ => 1) (fun n => (n : ℝ≥0∞)) c := by
  rintro ⟨c, hc, hb⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hc
  have he := hb n
  simp only [mul_one] at he
  exact (not_le_of_gt hn) he

theorem natural_ratio_top :
    ratioSup (fun _ : ℕ => 1) (fun n => (n : ℝ≥0∞)) = ∞ := by
  by_contra hn
  apply natural_no_global_bound
  apply (finite_bound_exists_iff _ _).mpr
  refine ⟨?_, hn⟩
  intro n hz; simp at hz

theorem uniform_local_implies_global (d e : X → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ F : Finset X, ∃ c : ℝ≥0∞, c ≤ C ∧ ∀ x ∈ F, e x ≤ c * d x) :
    Bound d e C := by
  classical
  intro x
  obtain ⟨c, hc, hb⟩ := h {x}
  exact (hb x (by simp)).trans (mul_le_mul_right' hc (d x))

end MathGauge.F111
