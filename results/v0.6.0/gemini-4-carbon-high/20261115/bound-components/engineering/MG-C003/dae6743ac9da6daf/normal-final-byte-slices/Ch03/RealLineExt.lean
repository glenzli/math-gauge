import Ch03.Defs

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open Set

/-!
# 带吸收元的扩展实直线模型 (`ℝ ⊔ {⊥}`)

供反例 3.1、命题 3.14(iii)、命题 3.16 后反例及习题 3.1/3.3/3.4/3.5 共用。
-/

/-- 带指定吸收元 `bot` 的实直线 `ℝ ⊔ {⊥}`。 -/
inductive RealWithBot : Type
  | bot : RealWithBot
  | ofReal (x : ℝ) : RealWithBot

theorem ofReal_injective : Function.Injective RealWithBot.ofReal := by
  intro x y h
  injection h

@[simp] theorem ofReal_ne_bot (x : ℝ) : RealWithBot.ofReal x ≠ RealWithBot.bot := by
  intro h
  cases h

@[simp] theorem bot_ne_ofReal (x : ℝ) : RealWithBot.bot ≠ RealWithBot.ofReal x := by
  intro h
  cases h

@[simp] theorem ofReal_eq_iff {x y : ℝ} :
    RealWithBot.ofReal x = RealWithBot.ofReal y ↔ x = y :=
  ⟨fun h => ofReal_injective h, fun h => h ▸ rfl⟩

/-- 由读数函数 `q : ℝ → ℝ` 诱导的带吸收元隔离扩展伪度量 `|q(x) - q(y)|`。 -/
noncomputable def realPullbackExtDist (q : ℝ → ℝ) :
    RealWithBot → RealWithBot → ENNReal
  | .bot, .bot => 0
  | .ofReal x, .ofReal y => ENNReal.ofReal |q x - q y|
  | .bot, .ofReal _ => ⊤
  | .ofReal _, .bot => ⊤

/-- 任意读数函数 `q : ℝ → ℝ` 诱导的 `realPullbackExtDist q` 均满足扩展伪度量公理。 -/
theorem realPullbackExtDist_isExtendedPseudoMetric (q : ℝ → ℝ) :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot (realPullbackExtDist q) where
  nonabsorbing := ⟨RealWithBot.ofReal 0, ofReal_ne_bot 0⟩
  dist_self := by
    rintro (_ | x)
    · rfl
    · simp [realPullbackExtDist]
  symm := by
    rintro (_ | x) (_ | y)
    · rfl
    · rfl
    · rfl
    · simp [realPullbackExtDist, abs_sub_comm]
  triangle := by
    rintro (_ | x) (_ | y) (_ | z)
    · simp [realPullbackExtDist]
    · simp [realPullbackExtDist]
    · simp [realPullbackExtDist]
    · simp [realPullbackExtDist]
    · simp [realPullbackExtDist]
    · simp [realPullbackExtDist]
    · simp [realPullbackExtDist]
    · simp only [realPullbackExtDist]
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub_le (q x) (q y) (q z))
  isolate_bot := by
    rintro (_ | x) hx
    · exact False.elim (hx rfl)
    · rfl

/-- 实数部分采用通常欧氏距离 `|x - y|`、吸收元与实数距离为 `+∞` 的扩展伪度量。 -/
noncomputable def realStdExtDist : RealWithBot → RealWithBot → ENNReal :=
  realPullbackExtDist id

/-- `realStdExtDist` 是 `RealWithBot` 上的合法扩展伪度量。 -/
theorem realStdExtDist_isExtendedPseudoMetric :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realStdExtDist :=
  realPullbackExtDist_isExtendedPseudoMetric id

@[simp] theorem realStdExtDist_ofReal (x y : ℝ) :
    realStdExtDist (.ofReal x) (.ofReal y) = ENNReal.ofReal |x - y| := rfl

@[simp] theorem realStdExtDist_bot_bot :
    realStdExtDist .bot .bot = 0 := rfl

@[simp] theorem realStdExtDist_ofReal_bot (x : ℝ) :
    realStdExtDist (.ofReal x) .bot = ⊤ := rfl

@[simp] theorem realStdExtDist_bot_ofReal (x : ℝ) :
    realStdExtDist .bot (.ofReal x) = ⊤ := rfl

/-- 实数部分采用绝对值读数伪度量 `||x| - |y||`、吸收元隔离的扩展伪度量。 -/
noncomputable def realAbsModExtDist : RealWithBot → RealWithBot → ENNReal :=
  realPullbackExtDist abs

/-- `realAbsModExtDist` 是 `RealWithBot` 上的合法扩展伪度量。 -/
theorem realAbsModExtDist_isExtendedPseudoMetric :
    ExtendedPseudoMetric RealWithBot RealWithBot.bot realAbsModExtDist :=
  realPullbackExtDist_isExtendedPseudoMetric abs

@[simp] theorem realAbsModExtDist_ofReal (x y : ℝ) :
    realAbsModExtDist (.ofReal x) (.ofReal y) = ENNReal.ofReal |(|x| - |y|)| := rfl

@[simp] theorem realAbsModExtDist_bot_bot :
    realAbsModExtDist .bot .bot = 0 := rfl

@[simp] theorem realAbsModExtDist_ofReal_bot (x : ℝ) :
    realAbsModExtDist (.ofReal x) .bot = ⊤ := rfl

@[simp] theorem realAbsModExtDist_bot_ofReal (x : ℝ) :
    realAbsModExtDist .bot (.ofReal x) = ⊤ := rfl

/-- 将实函数 `g : ℝ → ℝ` 保吸收元延拓为 `RealWithBot` 上的算子。 -/
def liftRealMap (g : ℝ → ℝ) : Operator RealWithBot RealWithBot.bot where
  func
    | .bot => .bot
    | .ofReal x => .ofReal (g x)
  preserves_bot := rfl

@[simp] theorem liftRealMap_ofReal (g : ℝ → ℝ) (x : ℝ) :
    (liftRealMap g).func (.ofReal x) = .ofReal (g x) := rfl

@[simp] theorem liftRealMap_bot (g : ℝ → ℝ) :
    (liftRealMap g).func .bot = .bot := rfl

theorem dom_liftRealMap (g : ℝ → ℝ) :
    dom (liftRealMap g) = Set.range RealWithBot.ofReal := by
  ext p
  cases p with
  | bot => simp [dom, liftRealMap]
  | ofReal x => simp [dom, liftRealMap]

theorem ofReal_image_subset_dom_liftRealMap (g : ℝ → ℝ) (S : Set ℝ) :
    RealWithBot.ofReal '' S ⊆ dom (liftRealMap g) := by
  rw [dom_liftRealMap]
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- 单分量指标族封装（通常实数距离）。 -/
noncomputable def realStdGauge : Unit → RealWithBot → RealWithBot → ENNReal :=
  fun _ => realStdExtDist

theorem realStdGauge_isExtendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric RealWithBot RealWithBot.bot (realStdGauge u) :=
  fun _ => realStdExtDist_isExtendedPseudoMetric

/-- 单分量指标族封装（绝对值模长伪度量 `||x| - |y||`）。 -/
noncomputable def realAbsModGauge : Unit → RealWithBot → RealWithBot → ENNReal :=
  fun _ => realAbsModExtDist

theorem realAbsModGauge_isExtendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric RealWithBot RealWithBot.bot (realAbsModGauge u) :=
  fun _ => realAbsModExtDist_isExtendedPseudoMetric

end Ch03
