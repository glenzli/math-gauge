import BoundaryExample

namespace MathGauge.F112
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


variable {Y : Type*}

def sumData (a : X → ℝ≥0∞) (b : Y → ℝ≥0∞) : X ⊕ Y → ℝ≥0∞ := Sum.elim a b

theorem bound_sum_iff (d₁ e₁ : X → ℝ≥0∞) (d₂ e₂ : Y → ℝ≥0∞) (c : ℝ≥0∞) :
    Bound (sumData d₁ d₂) (sumData e₁ e₂) c ↔ Bound d₁ e₁ c ∧ Bound d₂ e₂ c := by
  constructor
  · intro h; exact ⟨fun x => h (.inl x), fun y => h (.inr y)⟩
  · rintro ⟨h₁,h₂⟩ (x | y)
    · exact h₁ x
    · exact h₂ y

theorem bound_mono {d e : X → ℝ≥0∞} {a b : ℝ≥0∞}
    (hab : a ≤ b) (ha : Bound d e a) : Bound d e b :=
  fun x => (ha x).trans (mul_le_mul_right' hab (d x))

theorem least_sum (d₁ e₁ : X → ℝ≥0∞) (d₂ e₂ : Y → ℝ≥0∞) {a b : ℝ≥0∞}
    (ha : LeastFinite d₁ e₁ a) (hb : LeastFinite d₂ e₂ b) :
    LeastFinite (sumData d₁ d₂) (sumData e₁ e₂) (max a b) := by
  refine ⟨?_, (bound_sum_iff _ _ _ _ _).mpr
    ⟨bound_mono (le_max_left _ _) ha.2.1, bound_mono (le_max_right _ _) hb.2.1⟩, ?_⟩
  · exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ha.1) (lt_top_iff_ne_top.mpr hb.1))
  · intro c hc h
    obtain ⟨h₁,h₂⟩ := (bound_sum_iff _ _ _ _ _).mp h
    exact max_le (ha.2.2 c hc h₁) (hb.2.2 c hc h₂)

def oneData (_ : Unit) : ℝ≥0∞ := 1

theorem one_bound_iff (c : ℝ≥0∞) : Bound oneData oneData c ↔ 1 ≤ c := by
  simp [Bound, oneData]

theorem one_least : LeastFinite oneData oneData 1 :=
  ⟨by simp, (one_bound_iff _).mpr le_rfl, fun c _ hc => (one_bound_iff c).mp hc⟩

theorem mixed_bound_iff (c : ℝ≥0∞) :
    Bound (sumData sourceValue oneData) (sumData targetValue oneData) c ↔ 1 ≤ c := by
  rw [bound_sum_iff, boundary_bound_iff, one_bound_iff]
  exact ⟨And.right, fun hc => ⟨ne_of_gt (lt_of_lt_of_le zero_lt_one hc), hc⟩⟩

theorem mixed_least :
    LeastFinite (sumData sourceValue oneData) (sumData targetValue oneData) 1 :=
  ⟨by simp, (mixed_bound_iff 1).mpr le_rfl, fun c _ hc => (mixed_bound_iff c).mp hc⟩

theorem reverse_decomposition_counterexample :
    LeastFinite (sumData sourceValue oneData) (sumData targetValue oneData) 1 ∧
    LeastFinite oneData oneData 1 ∧ ¬ ∃ c, LeastFinite sourceValue targetValue c :=
  ⟨mixed_least, one_least, boundary_not_attained⟩

end MathGauge.F112
