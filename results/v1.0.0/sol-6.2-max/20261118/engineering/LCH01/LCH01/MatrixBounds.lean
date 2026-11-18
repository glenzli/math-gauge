import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

open scoped BigOperators ENNReal
open formal_oet.vol_01.ch_01_foundations

namespace LCH01

/-- A finite, nonempty family of extended pseudometrics with a shared absorbing point. -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ℝ≥0∞
  component : ∀ i : I, ExtendedPseudoMetric X bot (dist i)

/-- Rows are outputs and columns are inputs. -/
abbrev BoundMatrix (I : Type) := Matrix I I ℝ≥0∞

namespace BoundMatrix

/-- The coefficient of the channel from input `i` to output `j`. -/
def coeff {I : Type} (M : BoundMatrix I) (i j : I) : ℝ≥0∞ := M j i

/-- The extended nonnegative weighted sum at output `j`. -/
noncomputable def rowSum {I : Type} [Fintype I]
    (M : BoundMatrix I) (j : I) (v : I → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, M.coeff i j * v i

theorem mul_coeff {I : Type} [Fintype I] (B A : BoundMatrix I) (i j : I) :
    coeff (B * A) i j = ∑ k, B.coeff k j * A.coeff i k :=
  Matrix.mul_apply

end BoundMatrix

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def IsRestrictedLipMatrix (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.dist j (φ.func x) (φ.func y) ≤ L.rowSum j (fun i => G.dist i x y)

def IsLipMatrix (G : Gauge X I bot) (φ : Operator X bot) (L : BoundMatrix I) : Prop :=
  IsRestrictedLipMatrix G φ (dom φ) L

theorem isLipMatrix_iff (G : Gauge X I bot) (φ : Operator X bot) (L : BoundMatrix I) :
    IsLipMatrix G φ L ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
        G.dist j (φ.func x) (φ.func y) ≤ L.rowSum j (fun i => G.dist i x y) :=
  ⟨fun h => h.2, fun h => ⟨Set.Subset.rfl, h⟩⟩

def lipMatrices (G : Gauge X I bot) (φ : Operator X bot) : Set (BoundMatrix I) :=
  { L | IsLipMatrix G φ L }

def restrictedLipMatrices (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) :=
  { L | IsRestrictedLipMatrix G φ U L }

def IsRestrictedCoLipMatrix (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ U.Nonempty ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      K.rowSum j (fun i => G.dist i x y) ≤ G.dist j (φ.func x) (φ.func y)

def restrictedCoLipMatrices (G : Gauge X I bot) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) :=
  { K | IsRestrictedCoLipMatrix G φ U K }

theorem coLip_term_le {G : Gauge X I bot} {φ : Operator X bot}
    {U : Set X} {K : BoundMatrix I} (hK : K ∈ restrictedCoLipMatrices G φ U)
    (i j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K.coeff i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  calc
    _ ≤ K.rowSum j (fun k => G.dist k x y) :=
      Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)
    _ ≤ _ := hK.2.2 x hx y hy j

end LCH01
