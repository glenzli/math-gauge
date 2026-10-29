### 数学结论分析与公式总结

在扩展非负实数算术（$\overline{\mathbb{R}}_{\ge 0} = [0, +\infty]$，其中规定 $0 \cdot (+\infty) = 0$）下，对任意集合 $X$ 及函数 $d, e : X \to [0, +\infty]$，设：
- $Z:\ \forall x,\ d(x) = 0 \implies e(x) = 0$（`ZeroCompatible`）；
- $H:\ \forall x,\ d(x) = +\infty \implies e(x) = 0$（`TopCompatible`）；
- $r = \sup \left\{ \dfrac{e(x)}{d(x)} : 0 < d(x) < +\infty \right\}$（`ratioSup`，空集上确界为 $0$）。

#### 1. 有限可行系数存在的充要条件
有限可行系数存在（即 $\exists c \in [0, +\infty),\ \forall x,\ e(x) \le c\,d(x)$）的充要条件为：
\[
Z \ \wedge\ r < +\infty
\]
- **必要性**：若存在有限可行系数 $c < +\infty$，则对 $d(x)=0$ 有 $e(x) \le c \cdot 0 = 0 \implies e(x)=0$（$Z$ 必须成立）；对满足 $0 < d(x) < +\infty$ 的点，均有 $\frac{e(x)}{d(x)} \le c$，从而 $r \le c < +\infty$。
- **充分性**：若 $Z$ 成立且 $r < +\infty$：当 $r > 0$ 时取 $c = r$；当 $r = 0$ 时取 $c = 1$。因为 $c > 0$，所以对任何 $d(x) = +\infty$ 的点，都有 $c \cdot d(x) = c \cdot (+\infty) = +\infty \ge e(x)$；对 $d(x) = 0$ 的点由 $Z$ 保证 $e(x) = 0 \le c \cdot 0$；对有限正值点由 $c \ge r$ 保证可行。因此 $c$ 是有限可行系数。注意：存在有限可行系数**不需要** $H$。

#### 2. 最小有限可行系数存在的充要条件
最小有限可行系数存在（即 $\exists c,\ \text{LeastFinite } d\ e\ c$）的充要条件为：
\[
Z \ \wedge\ r < +\infty \ \wedge\ (r = 0 \implies H)
\]
（等价表述为 $Z \wedge r < +\infty \wedge (H \vee r > 0)$）。
- **必要性**：若存在最小有限可行系数 $c$，则 $c$ 首先是有限可行系数，故 $Z$ 成立且 $r \le c < +\infty$。进一步可知可行系数的最小值必定满足 $c = r$。若 $r = 0$，则 $c = 0$ 可行，因此对 $d(x) = +\infty$ 必有 $e(x) \le 0 \cdot (+\infty) = 0$，即 $H$ 必然成立。
- **充分性**：若条件成立，则 $r < +\infty$ 且 $r$ 本身就是一个可行系数（$r > 0$ 时在无穷大点自动满足 $r \cdot (+\infty) = +\infty \ge e(x)$；$r = 0$ 时由 $H$ 保证在无穷大点 $e(x) = 0 \le 0 \cdot (+\infty)$）。又因对任意可行系数 $b$ 必有 $r \le b$，故 $r$ 是最小有限可行系数。

#### 3. 存在时的最小值公式
当最小有限可行系数存在时，其最小值公式恒为：
\[
c_{\min} = r = \sup \left\{ \frac{e(x)}{d(x)} : 0 < d(x) < +\infty \right\}
\]

#### 4. 反例形式化验证
取实际数据：$X = \text{Unit}$，
\[
d(*) = +\infty,\qquad e(*) = 1.
\]
- 该数据下，$d(x) \ne 0$，因此 $Z$ 平凡成立；不存在满足 $0 < d(x) < +\infty$ 的点，故空集上确界 $r = 0 < +\infty$。
- **存在有限可行系数**：取 $c = 1$，有 $e(*) = 1 \le 1 \cdot d(*) = 1 \cdot (+\infty) = +\infty$，故 $c = 1$ 是有限可行系数。
- **不存在最小有限可行系数**：有限可行系数的集合为 $(0, +\infty)$（$c = 0$ 不可行，因为 $0 \cdot (+\infty) = 0 < 1$；任意 $c > 0$ 均可行，因为 $c \cdot (+\infty) = +\infty \ge 1$）。在 $(0, +\infty)$ 内不存在最小值。

---

### Lean 代码实现

#### 文件 1：`ExtendedData.lean`
背景定义文件。

```lean
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

namespace MathGauge.F112

open ENNReal
variable {X : Type*}

def Bound (d e : X → ℝ≥0∞) (c : ℝ≥0∞) : Prop := ∀ x, e x ≤ c * d x

def ZeroCompatible (d e : X → ℝ≥0∞) : Prop := ∀ x, d x = 0 → e x = 0

def TopCompatible (d e : X → ℝ≥0∞) : Prop := ∀ x, d x = ∞ → e x = 0

noncomputable def ratioSup (d e : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ x : {x : X // d x ≠ 0 ∧ d x ≠ ∞}, e x / d x

def LeastFinite (d e : X → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  c ≠ ∞ ∧ Bound d e c ∧ ∀ b, b ≠ ∞ → Bound d e b → c ≤ b

end MathGauge.F112
```

---

#### 文件 2：`Solution.lean`
完整形式化证明及反例验证。

```lean
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
```

---

### 各主要声明与数学结论对应说明

1. `exists_finite_bound_iff`：
   - **数学结论**：有限可行系数存在的充要条件为 $Z \wedge r < +\infty$。
2. `least_finite_eq`：
   - **数学结论**：若最小有限可行系数存在，其值唯一且等于 $r$（即 $c = \text{ratioSup } d\ e$）。
3. `exists_least_finite_iff`：
   - **数学结论**：最小有限可行系数存在的充要条件为 $Z \wedge r < +\infty \wedge (r = 0 \implies H)$。
4. `least_finite_iff`：
   - **数学结论**：系数 $c$ 是最小有限可行系数的充要条件为 $c = r$ 且上述充要条件成立。
5. `counter_d` 与 `counter_e`：
   - **数学结论**：在 $X = \text{Unit}$ 上定义的一组具体实测数据（$d(*) = +\infty, e(*) = 1$）。
6. `counter_example_phenomenon`（结合 `counter_exists_finite_bound` 与 `counter_not_exists_least_finite`）：
   - **数学结论**：形式化验证了对该组数据，满足 $\exists c \ne +\infty,\ \text{Bound } d\ e\ c$，但 $\neg \exists c,\ \text{LeastFinite } d\ e\ c$。
