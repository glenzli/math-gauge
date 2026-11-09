import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Tactic

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

universe u v

variable {X : Type} {I : Type} {bot : X}

/-- The constant-output components, with the convention that this class has
priority over the identity class. -/
def constComponents (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = 0}

/-- Identity components are nonconstant components which fix every point up to
zero distance in their own component. -/
def idComponents (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d φ U ∧ ∀ x ∈ U, d i (φ.func x) x = 0}

/-- The remaining components are active. -/
def actComponents (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d φ U ∧ i ∉ idComponents d φ U}

/-- Computational fibre with an arbitrary target. -/
def Fib (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (φ.func x) y = 0}

/-- Single-component computational fibre. -/
def FibSingle (d : I → X → X → ENNReal) (φ : Operator X bot)
    (j : I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ d j (φ.func x) y = 0}

/-- Point-equality relation on ordered pairs from the evaluation domain. -/
def pointRel (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ φ.func p.1 = φ.func p.2}

/-- Gauge-zero-distance relation on ordered pairs from the evaluation domain. -/
def zeroRel (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (φ.func p.1) (φ.func p.2)}

/-- The zero-distance fibre preorder. -/
def FiberGe (d : I → X → X → ENNReal) (φ ψ : Operator X bot) (U : Set X) : Prop :=
  zeroRel d φ U ⊆ zeroRel d ψ U

/-- Finite positive radii for which the restricted input ball lies in the
output zero-distance class.  `sSup ∅ = 0` in `ENNReal`, as required. -/
def annihilatingRadii (φ : Operator X bot) (din dout : X → X → ENNReal)
    (y : X) (U : Set X) : Set ENNReal :=
  {r | 0 < r ∧ r < ⊤ ∧
    ball din y r ∩ U ⊆ {x | x ∈ U ∧ dout (φ.func x) (φ.func y) = 0}}

/-- Pointwise annihilation inner radius. -/
noncomputable def annihilationRadius (φ : Operator X bot)
    (din dout : X → X → ENNReal) (y : X) (U : Set X) : ENNReal :=
  sSup (annihilatingRadii φ din dout y U)

/-- Component notation for the pointwise annihilation radius. -/
noncomputable def componentAnnihilationRadius (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  annihilationRadius φ (d i) (subfamily_pseudometric d J) y U

/-- Uniform annihilation radius over a base-point set `A`, while balls are
still evaluated relative to `U`. -/
noncomputable def uniformAnnihilationRadius (φ : Operator X bot)
    (din dout : X → X → ENNReal) (A U : Set X) : ENNReal :=
  ⨅ y : A, annihilationRadius φ din dout y.1 U

/-- Uniform radius over all points of the evaluation domain. -/
noncomputable def uniformAnnihilationRadiusOn (φ : Operator X bot)
    (din dout : X → X → ENNReal) (U : Set X) : ENNReal :=
  uniformAnnihilationRadius φ din dout U U

/-- Component notation for the uniform radius on the evaluation domain. -/
noncomputable def componentUniformAnnihilationRadius (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  uniformAnnihilationRadiusOn φ (d i) (subfamily_pseudometric d J) U

/-- Rows are output components and columns are input components. -/
noncomputable def annihilationMatrix (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) : I → I → ENNReal :=
  fun j i => componentUniformAnnihilationRadius d φ i ({j} : Set I) U

/-- A monotone family of scales on nonempty subsets. -/
structure InputScaleFamily (X : Type) (I : Type) where
  scale : I → {A : Set X // A.Nonempty} → ENNReal
  monotone : ∀ i, Monotone (scale i)

/-- Diameter scale, also defined by the same formula on empty sets for
convenience in elementary examples. -/
noncomputable def diameter (dist : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, dist x y

/-- The diameter scale as an input scale family. -/
noncomputable def diameterScaleFamily (d : I → X → X → ENNReal) : InputScaleFamily X I where
  scale i A := diameter (d i) A.1
  monotone i := by
    intro A B hAB
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le x (le_iSup_of_le (hAB hx) (le_iSup_of_le y (le_iSup_of_le (hAB hy) le_rfl)))

/-- The two binary threshold indicators, in the order (scale, annihilation). -/
noncomputable def thresholdType (σ : InputScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (hA : A.Nonempty) (τσ τN : ENNReal) (i j : I) : ℕ × ℕ :=
  (if σ.scale i ⟨A, hA⟩ < τσ then 1 else 0,
   if componentUniformAnnihilationRadius d f i ({j} : Set I) A ≥ τN then 1 else 0)

/-- The two-ended metric-entropy difference. -/
noncomputable def entropyDelta (d : I → X → X → ENNReal) (Jin Jout : Set I)
    (ε : ENNReal) (φ : Operator X bot) (U : Set X) : EReal :=
  subfamily_metric_entropy d Jin ε U - subfamily_metric_entropy d Jout ε (φ.func '' U)

/-- The definition excludes the indeterminate `+∞ - +∞` case. -/
def EntropyDeltaAdmissible (d : I → X → X → ENNReal) (Jin Jout : Set I)
    (ε : ENNReal) (φ : Operator X bot) (U : Set X) : Prop :=
  covering_number (subfamily_pseudometric d Jin) ε U < ⊤ ∨
    covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) < ⊤

/-- Total boundedness expressed through finite internal covering numbers. -/
def InternallyTotallyBounded (dist : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε < ⊤ → covering_number dist ε U < ⊤

@[simp] theorem mem_constComponents {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {i : I} :
    i ∈ constComponents d φ U ↔ ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = 0 := Iff.rfl

@[simp] theorem mem_idComponents {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {i : I} :
    i ∈ idComponents d φ U ↔
      i ∉ constComponents d φ U ∧ ∀ x ∈ U, d i (φ.func x) x = 0 := Iff.rfl

@[simp] theorem mem_actComponents {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {i : I} :
    i ∈ actComponents d φ U ↔ i ∉ constComponents d φ U ∧ i ∉ idComponents d φ U := Iff.rfl

@[simp] theorem mem_Fib {d : I → X → X → ENNReal} {φ : Operator X bot}
    {J : Set I} {y : X} {U : Set X} {x : X} :
    x ∈ Fib d φ J y U ↔ x ∈ U ∧ subfamily_pseudometric d J (φ.func x) y = 0 := Iff.rfl

@[simp] theorem mem_FibSingle {d : I → X → X → ENNReal} {φ : Operator X bot}
    {j : I} {y : X} {U : Set X} {x : X} :
    x ∈ FibSingle d φ j y U ↔ x ∈ U ∧ d j (φ.func x) y = 0 := Iff.rfl

theorem subfamily_zero_iff {d : I → X → X → ENNReal} {J : Set I} {x y : X} :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  simp [subfamily_pseudometric]

theorem fib_eq_single (d : I → X → X → ENNReal) (φ : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    Fib d φ ({j} : Set I) y U = FibSingle d φ j y U := by
  ext x
  simp [subfamily_pseudometric_singleton]

theorem componentRadius_single (d : I → X → X → ENNReal) (φ : Operator X bot)
    (i j : I) (y : X) (U : Set X) :
    componentAnnihilationRadius d φ i ({j} : Set I) y U =
      annihilationRadius φ (d i) (d j) y U := by
  rw [componentAnnihilationRadius, subfamily_pseudometric_singleton]

theorem componentUniformRadius_single (d : I → X → X → ENNReal) (φ : Operator X bot)
    (i j : I) (U : Set X) :
    componentUniformAnnihilationRadius d φ i ({j} : Set I) U =
      uniformAnnihilationRadiusOn φ (d i) (d j) U := by
  simp only [componentUniformAnnihilationRadius, uniformAnnihilationRadiusOn,
    uniformAnnihilationRadius, subfamily_pseudometric_singleton]

/-- The frozen covering-number construction is the internal-centre minimum
used by this chapter. -/
theorem covering_number_representation {X : Type} (dist : X → X → ENNReal)
    (ε : ENNReal) (U : Set X)
    (hfinite : ∃ centers : Finset X, InternalEpsilonNet dist ε U centers) :
    ∃ centers : Finset X, InternalEpsilonNet dist ε U centers ∧
      covering_number dist ε U = (centers.card : ENNReal) ∧
      ∀ other : Finset X, InternalEpsilonNet dist ε U other → centers.card ≤ other.card :=
  covering_number_attained dist ε U hfinite

theorem covering_number_le_of_net {X : Type} {dist : X → X → ENNReal}
    {ε : ENNReal} {U : Set X} {centers : Finset X}
    (h : InternalEpsilonNet dist ε U centers) :
    covering_number dist ε U ≤ (centers.card : ENNReal) := by
  exact iInf_le_of_le centers (iInf_le_of_le h le_rfl)

theorem le_covering_number_of_card {X : Type} {dist : X → X → ENNReal}
    {ε : ENNReal} {U : Set X} {n : ℕ}
    (h : ∀ centers : Finset X, InternalEpsilonNet dist ε U centers → n ≤ centers.card) :
    (n : ENNReal) ≤ covering_number dist ε U := by
  apply le_iInf
  intro centers
  apply le_iInf
  intro hc
  exact_mod_cast h centers hc

theorem covering_number_eq_natCast {X : Type} {dist : X → X → ENNReal}
    {ε : ENNReal} {U : Set X} {n : ℕ} {centers : Finset X}
    (hnet : InternalEpsilonNet dist ε U centers) (hcard : centers.card = n)
    (hmin : ∀ other : Finset X, InternalEpsilonNet dist ε U other → n ≤ other.card) :
    covering_number dist ε U = n := by
  apply le_antisymm
  · simpa [hcard] using covering_number_le_of_net hnet
  · exact le_covering_number_of_card hmin

end OET.Ch03
