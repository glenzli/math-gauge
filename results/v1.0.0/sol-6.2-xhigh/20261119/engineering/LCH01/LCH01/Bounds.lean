import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

open scoped BigOperators

namespace LCH01

open formal_oet.vol_01.ch_01_foundations (ExtendedPseudoMetric Operator dom)

/-- A finite, nonempty family of extended pseudometrics with the same absorbing point. -/
structure GaugeFamily (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  isExtended : ∀ i, ExtendedPseudoMetric X bot (dist i)

abbrev CoeffMatrix (I : Type) := Matrix I I ENNReal

/-- The coefficient from an input component to an output component. -/
def entry {I : Type} (M : CoeffMatrix I) (input output : I) : ENNReal :=
  M output input

theorem entry_mul {I : Type} [Fintype I] (A B : CoeffMatrix I) (i j : I) :
    entry (A * B) i j = ∑ k : I, entry A k j * entry B i k :=
  Matrix.mul_apply

/-- The weighted sum for output component `j` and input vector `v`. -/
noncomputable def rowSum {I : Type} [Fintype I] (M : CoeffMatrix I) (v : I → ENNReal) (j : I) :
    ENNReal :=
  ∑ i : I, entry M i j * v i

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def IsRestrictedLip (G : GaugeFamily X I bot) (φ : Operator X bot)
    (U : Set X) (L : CoeffMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.dist j (φ.func x) (φ.func y) ≤ rowSum L (fun i => G.dist i x y) j

def IsLip (G : GaugeFamily X I bot) (φ : Operator X bot) (L : CoeffMatrix I) : Prop :=
  IsRestrictedLip G φ (dom φ) L

def restrictedLipMatrices (G : GaugeFamily X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) :=
  {L | IsRestrictedLip G φ U L}

def lipMatrices (G : GaugeFamily X I bot) (φ : Operator X bot) : Set (CoeffMatrix I) :=
  {L | IsLip G φ L}

def IsRestrictedCoLip (G : GaugeFamily X I bot) (φ : Operator X bot)
    (U : Set X) (K : CoeffMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      rowSum K (fun i => G.dist i x y) j ≤ G.dist j (φ.func x) (φ.func y)

def restrictedCoLipMatrices (G : GaugeFamily X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) :=
  {K | IsRestrictedCoLip G φ U K}

end LCH01
