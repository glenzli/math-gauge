import ExtendedData
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

namespace MathGauge.F112

open ENNReal
variable {X : Type*}

/-! ### 辅助引理：ratioSup 的基本性质与 ENNReal 乘除转换 -/

lemma le_ratioSup {d e : X → ℝ≥0∞} (x : X) (h0 : d x ≠ 0) (ht : d x ≠ ∞) :
    e x / d x ≤ ratioSup d e :=
  le_iSup (fun j : {x : X // d x ≠ 0 ∧ d x ≠ ∞} => e j.1 / d j.1) ⟨x, h0, ht⟩

lemma ratioSup_le {d e : X → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x, d x ≠ 0 → d x ≠ ∞ → e x / d x ≤ c) :
    ratioSup d e ≤ c :=
  iSup_le (fun ⟨x, h0, ht⟩ => h x h0 ht)

theorem div_le_of_le_mul {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ∞) (h : a ≤ c * b) :
    a / b ≤ c := by
  have h1 : a * b⁻¹ ≤ (c * b) * b⁻¹ := by gcongr
  have h2 : (c * b) * b⁻¹ = c := by
    rw [mul_assoc, ENNReal.mul_inv_cancel hb0 hbt, mul_one]
  rw [div_eq_mul_inv]
  exact h1.trans (le_of_eq h2)

theorem le_mul_of_div_le {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbt : b ≠ ∞) (h : a / b ≤ c) :
    a ≤ c * b := by
  have hdiv : a * b⁻¹ ≤ c := by
    rwa [div_eq_mul_inv] at h
  have h1 : (a * b⁻¹) * b ≤ c * b := by
    gcongr
  have h2 : (a * b⁻¹) * b = a := by
    rw [mul_assoc, mul_comm b⁻¹ b, ENNReal.mul_inv_cancel hb0 hbt, mul_one]
  exact (le_of_eq h2.symm).trans h1

/-! ### 可行性与必要条件 -/

lemma bound_implies_zeroCompatible {d e : X → ℝ≥0∞} {c : ℝ≥0∞} (h : Bound d e c) :
    ZeroCompatible d e := by
  intro x hx
  have hle : e x ≤ c * d x := h x
  rw [hx, mul_zero] at hle
  exact le_antisymm hle (zero_le _)

lemma bound_implies_ratioSup_le {d e : X → ℝ≥0∞} {c : ℝ≥0∞} (h : Bound d e c) :
    ratioSup d e ≤ c := by
  apply ratioSup_le
  intro x h0 ht
  exact div_le_of_le_mul h0 ht (h x)

lemma bound_zero_implies_topCompatible {d e : X → ℝ≥0∞} (h : Bound d e 0) :
    TopCompatible d e := by
  intro x hx
  have hle : e x ≤ 0 * d x := h x
  rw [hx, zero_mul] at hle
  exact le_antisymm hle (zero_le _)

lemma bound_of_ratioSup_le {d e : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hZ : ZeroCompatible d e) (hr : ratioSup d e ≤ c) (hc : c ≠ 0) :
    Bound d e c := by
  intro x
  by_cases h0 : d x = 0
  · have hex : e x = 0 := hZ x h0
    have hcd : c * d x = 0 := by rw [h0, mul_zero]
    exact le_of_eq (hex.trans hcd.symm)
  · by_cases ht : d x = ∞
    · have hcd : c * d x = ∞ := by rw [ht, ENNReal.mul_top hc]
      rw [hcd]
      exact le_top
    · have hle : e x / d x ≤ c := (le_ratioSup x h0 ht).trans hr
      exact le_mul_of_div_le h0 ht hle

lemma bound_zero_of_conditions {d e : X → ℝ≥0∞}
    (hZ : ZeroCompatible d e) (hH : TopCompatible d e) (hr : ratioSup d e = 0) :
    Bound d e 0 := by
  intro x
  by_cases h0 : d x = 0
  · have hex : e x = 0 := hZ x h0
    have hcd : 0 * d x = 0 := by rw [h0, mul_zero]
    exact le_of_eq (hex.trans hcd.symm)
  · by_cases ht : d x = ∞
    · have hex : e x = 0 := hH x ht
      have hcd : 0 * d x = 0 := by rw [ht, zero_mul]
      exact le_of_eq (hex.trans hcd.symm)
    · have hle : e x / d x ≤ 0 := (le_ratioSup x h0 ht).trans (le_of_eq hr)
      exact le_mul_of_div_le h0 ht hle

lemma bound_ratioSup {d e : X → ℝ≥0∞}
    (hZ : ZeroCompatible d e) (hH : ratioSup d e = 0 → TopCompatible d e) :
    Bound d e (ratioSup d e) := by
  by_cases hr : ratioSup d e = 0
  · rw [hr]
    exact bound_zero_of_conditions hZ (hH hr) hr
  · exact bound_of_ratioSup_le hZ le_rfl hr

/-! ### 定理 1：有限可行系数存在的充要条件 -/

theorem exists_finite_bound_iff (d e : X → ℝ≥0∞) :
    (∃ c, c ≠ ∞ ∧ Bound d e c) ↔ ZeroCompatible d e ∧ ratioSup d e ≠ ∞ := by
  constructor
  · rintro ⟨c, hc_top, hc_bound⟩
    refine ⟨bound_implies_zeroCompatible hc_bound, ?_⟩
    have hr_le := bound_implies_ratioSup_le hc_bound
    intro hr_top
    rw [hr_top] at hr_le
    exact hc_top (top_unique hr_le)
  · rintro ⟨hZ, hr_top⟩
    by_cases hr0 : ratioSup d e = 0
    · refine ⟨1, one_ne_top, bound_of_ratioSup_le hZ ?_ one_ne_zero⟩
      rw [hr0]
      exact zero_le 1
    · exact ⟨ratioSup d e, hr_top, bound_of_ratioSup_le hZ le_rfl hr0⟩

/-! ### 定理 2 & 3：最小可行系数的唯一公式与存在充要条件 -/

lemma leastFinite_le_ratioSup {d e : X → ℝ≥0∞} {c : ℝ≥0∞} (h : LeastFinite d e c) :
    c ≤ ratioSup d e := by
  rcases h with ⟨_, hc_bound, h_least⟩
  have hZ : ZeroCompatible d e := bound_implies_zeroCompatible hc_bound
  by_contra hc_le
  have hlt : ratioSup d e < c := not_le.mp hc_le
  rcases exists_between hlt with ⟨b, hrb, hbc⟩
  have hb_top : b ≠ ∞ := fun hb => hbc.not_le (hb ▸ le_top)
  have hb_zero : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le _) hrb)
  have hb_bound : Bound d e b := bound_of_ratioSup_le hZ (le_of_lt hrb) hb_zero
  exact hbc.not_le (h_least b hb_top hb_bound)

/-- 最小值公式：若最小有限可行系数存在，其值必为 ratioSup d e -/
theorem least_finite_eq (d e : X → ℝ≥0∞) (c : ℝ≥0∞) (h : LeastFinite d e c) :
    c = ratioSup d e :=
  le_antisymm (leastFinite_le_ratioSup h) (bound_implies_ratioSup_le h.2.1)

/-- ratioSup d e 本身为最小有限可行系数的充要条件 -/
theorem least_finite_ratioSup_iff (d e : X → ℝ≥0∞) :
    LeastFinite d e (ratioSup d e) ↔
      ZeroCompatible d e ∧ ratioSup d e ≠ ∞ ∧ (ratioSup d e = 0 → TopCompatible d e) := by
  constructor
  · intro h
    refine ⟨bound_implies_zeroCompatible h.2.1, h.1, ?_⟩
    intro hr
    have hbound : Bound d e 0 := by
      have := h.2.1
      rwa [hr] at this
    exact bound_zero_implies_topCompatible hbound
  · rintro ⟨hZ, hr_top, hH⟩
    refine ⟨hr_top, bound_ratioSup hZ hH, ?_⟩
    intro b _ hb_bound
    exact bound_implies_ratioSup_le hb_bound

/-- 最小有限可行系数存在的充要条件 -/
theorem exists_least_finite_iff (d e : X → ℝ≥0∞) :
    (∃ c, LeastFinite d e c) ↔
      ZeroCompatible d e ∧ ratioSup d e ≠ ∞ ∧ (ratioSup d e = 0 → TopCompatible d e) := by
  constructor
  · rintro ⟨c, hc⟩
    have hc_eq : c = ratioSup d e := least_finite_eq d e c hc
    rw [hc_eq] at hc
    exact (least_finite_ratioSup_iff d e).mp hc
  · intro h
    exact ⟨ratioSup d e, (least_finite_ratioSup_iff d e).mpr h⟩

/-- 综合充要条件：系数 c 为最小有限可行系数的充要条件 -/
theorem least_finite_iff (d e : X → ℝ≥0∞) (c : ℝ≥0∞) :
    LeastFinite d e c ↔
      c = ratioSup d e ∧ ZeroCompatible d e ∧ ratioSup d e ≠ ∞ ∧ (ratioSup d e = 0 → TopCompatible d e) := by
  constructor
  · intro hc
    have hc_eq : c = ratioSup d e := least_finite_eq d e c hc
    have hrest := (least_finite_ratioSup_iff d e).mp (hc_eq ▸ hc)
    exact ⟨hc_eq, hrest⟩
  · rintro ⟨rfl, hrest⟩
    exact (least_finite_ratioSup_iff d e).mpr hrest

/-! ### 反例验证：“存在有限可行系数”不保证“存在最小有限可行系数” -/

def counter_d : Unit → ℝ≥0∞ := fun _ => ∞

def counter_e : Unit → ℝ≥0∞ := fun _ => 1

theorem counter_exists_finite_bound :
    ∃ c, c ≠ ∞ ∧ Bound counter_d counter_e c := by
  refine ⟨1, one_ne_top, ?_⟩
  intro x
  change (1 : ℝ≥0∞) ≤ 1 * ∞
  rw [one_mul]
  exact le_top

lemma counter_ratioSup_eq_zero : ratioSup counter_d counter_e = 0 := by
  apply le_antisymm
  · apply ratioSup_le
    intro x _ ht
    exact (ht rfl).elim
  · exact zero_le _

theorem counter_not_exists_least_finite :
    ¬ ∃ c, LeastFinite counter_d counter_e c := by
  rintro ⟨c, hc⟩
  have hc_eq : c = 0 := by
    rw [least_finite_eq counter_d counter_e c hc]
    exact counter_ratioSup_eq_zero
  have hbound : Bound counter_d counter_e c := hc.2.1
  rw [hc_eq] at hbound
  have h1 : (1 : ℝ≥0∞) ≤ 0 := by
    have := hbound ()
    change (1 : ℝ≥0∞) ≤ 0 * ∞ at this
    rwa [zero_mul] at this
  exact one_ne_zero (le_antisymm h1 (zero_le _))

/-- 核心反例现象：存在有限可行系数，但不存在最小有限可行系数 -/
theorem counter_example_phenomenon :
    (∃ c, c ≠ ∞ ∧ Bound counter_d counter_e c) ∧
    (¬ ∃ c, LeastFinite counter_d counter_e c) :=
  ⟨counter_exists_finite_bound, counter_not_exists_least_finite⟩

end MathGauge.F112
