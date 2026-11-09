import OperatorBounds.Defs

set_option linter.unusedSectionVars false

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace formal_oet.ch_02_operator_bounds

section FiniteNonemptyIndex

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I]
variable {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X}

/-- A diagonal matrix row reduces to its diagonal entry.  This is the direct
off-diagonal-zero specialization used for same-component channels. -/
theorem diagonal_row_vanishes {L : GaugeMatrix I} {j : I}
    (hdiag : IsDiagonalMatrix L) :
    SingleInputRow L j j := by
  intro k hk
  exact hdiag k j hk

/-- Explicit accessor for the domain condition of a restricted Lip matrix. -/
theorem IsLipMatrixOn.subset_dom {L : GaugeMatrix I} (hL : IsLipMatrixOn d ϕ U L) :
    U ⊆ dom ϕ := hL.1

/-- Explicit accessor for the pointwise Lip inequality of a restricted Lip matrix. -/
theorem IsLipMatrixOn.bound {L : GaugeMatrix I} (hL : IsLipMatrixOn d ϕ U L) :
    LipBoundOn d ϕ U L := hL.2

/-- Explicit accessor for nonemptiness of the domain of a restricted co-Lip matrix. -/
theorem IsCoLipMatrixOn.nonempty {K : GaugeMatrix I} (hK : IsCoLipMatrixOn d ϕ U K) :
    U.Nonempty := hK.1

/-- Explicit accessor for the domain condition of a restricted co-Lip matrix. -/
theorem IsCoLipMatrixOn.subset_dom {K : GaugeMatrix I} (hK : IsCoLipMatrixOn d ϕ U K) :
    U ⊆ dom ϕ := hK.2.1

/-- Explicit accessor for the pointwise co-Lip inequality of a restricted co-Lip
matrix. -/
theorem IsCoLipMatrixOn.bound {K : GaugeMatrix I} (hK : IsCoLipMatrixOn d ϕ U K) :
    CoLipBoundOn d ϕ U K := hK.2.2

/-- Membership in a restricted Lip certificate family is exactly the restricted
Lip predicate. -/
@[simp] theorem mem_lipMatricesOn_iff {L : GaugeMatrix I} :
    L ∈ lipMatricesOn d ϕ U ↔ IsLipMatrixOn d ϕ U L := Iff.rfl

/-- Membership in the global Lip certificate family is exactly the global Lip
predicate. -/
@[simp] theorem mem_lipMatrices_iff {L : GaugeMatrix I} :
    L ∈ lipMatrices d ϕ ↔ IsLipMatrix d ϕ L := Iff.rfl

/-- Membership in a restricted co-Lip certificate family is exactly the restricted
co-Lip predicate, including nonemptiness of `U` and `U ⊆ dom(ϕ)`. -/
@[simp] theorem mem_coLipMatricesOn_iff {K : GaugeMatrix I} :
    K ∈ coLipMatricesOn d ϕ U ↔ IsCoLipMatrixOn d ϕ U K := Iff.rfl

/-- Membership in the global co-Lip certificate family is exactly the global co-Lip
predicate. -/
@[simp] theorem mem_coLipMatrices_iff {K : GaugeMatrix I} :
    K ∈ coLipMatrices d ϕ ↔ IsCoLipMatrix d ϕ K := Iff.rfl

end FiniteNonemptyIndex

end formal_oet.ch_02_operator_bounds
