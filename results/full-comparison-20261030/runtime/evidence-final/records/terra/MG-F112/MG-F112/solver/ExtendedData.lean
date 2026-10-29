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
