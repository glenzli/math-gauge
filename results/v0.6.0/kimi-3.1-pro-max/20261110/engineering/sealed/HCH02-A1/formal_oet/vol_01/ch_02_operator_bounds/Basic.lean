import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators ENNReal
open formal_oet.vol_01.ch_01_foundations

universe u v

/-- HC02-D03.  A bound matrix is stored input first: `M i j` is the
coefficient from input component `i` to output component `j`. -/
abbrev BoundMatrix (I : Type u) := I → I → ENNReal

/-- HC02-D03.  The usual displayed matrix has output `j` as its row and
input `i` as its column. -/
def displayMatrix {I : Type u} (M : BoundMatrix I) : Matrix I I ENNReal :=
  fun j i => M i j

/-- Convert an ordinarily displayed matrix back to input-first storage. -/
def inputMatrix {I : Type u} (A : Matrix I I ENNReal) : BoundMatrix I :=
  fun i j => A j i

@[simp] theorem inputMatrix_displayMatrix {I : Type u} (M : BoundMatrix I) :
    inputMatrix (displayMatrix M) = M := rfl

@[simp] theorem displayMatrix_inputMatrix {I : Type u} (A : Matrix I I ENNReal) :
    displayMatrix (inputMatrix A) = A := rfl

/-- HC02-D03.  This is `(M₂ M₁) i j = ∑ k, M₂ k j * M₁ i k`. -/
noncomputable def boundMul {I : Type u} [Fintype I] (M₂ M₁ : BoundMatrix I) : BoundMatrix I :=
  fun i j => ∑ k : I, M₂ k j * M₁ i k

@[simp] theorem boundMul_apply {I : Type u} [Fintype I]
    (M₂ M₁ : BoundMatrix I) (i j : I) :
    boundMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k := rfl

/-- HC02-D03: input-first multiplication is ordinary matrix multiplication
after exchanging rows and columns. -/
theorem displayMatrix_boundMul {I : Type u} [Fintype I] (M₂ M₁ : BoundMatrix I) :
    displayMatrix (boundMul M₂ M₁) = displayMatrix M₂ * displayMatrix M₁ := by
  ext j i
  simp [displayMatrix, boundMul, Matrix.mul_apply]

/-- HC02-D04.  The identity uses the Kronecker delta, with input index first. -/
noncomputable def boundIdentity {I : Type u} : BoundMatrix I := by
  classical
  exact fun i j => if i = j then 1 else 0

/-- HC02-D04.  The ordered product of `A 0, ..., A (n-1)` is
`A (n-1) * ... * A 0`; the empty product is the identity. -/
noncomputable def orderedProduct {I : Type u} [Fintype I] (A : ℕ → BoundMatrix I) :
    ℕ → BoundMatrix I
  | 0 => boundIdentity
  | n + 1 => boundMul (A n) (orderedProduct A n)

@[simp] theorem orderedProduct_zero {I : Type u} [Fintype I] (A : ℕ → BoundMatrix I) :
    orderedProduct A 0 = boundIdentity := rfl

/-- HC02-D01.  Restricted Lipschitz certificates.  Membership includes the
stated restriction-domain condition. -/
def IsRestrictedLip {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : BoundMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- HC02-D01.  The family of restricted Lipschitz certificates. -/
def restrictedLipCertificates {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {L | IsRestrictedLip d ϕ U L}

/-- HC02-D01.  Global certificates are certificates on `dom ϕ`. -/
def lipCertificates {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (BoundMatrix I) :=
  restrictedLipCertificates d ϕ (dom ϕ)

/-- HC02-D02.  Restricted co-Lipschitz certificates, including nonemptiness
of the restriction domain as part of the definition. -/
def IsRestrictedCoLip {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

/-- HC02-D02.  The family of restricted co-Lipschitz certificates. -/
def restrictedCoLipCertificates {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {K | IsRestrictedCoLip d ϕ U K}

/-- HC02-D02.  Global co-Lipschitz certificates use `dom ϕ`; in particular,
this family is defined only when that domain is nonempty. -/
def coLipCertificates {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (BoundMatrix I) :=
  restrictedCoLipCertificates d ϕ (dom ϕ)

/-- HC02-P04.  Entrywise infimum over a family of matrix certificates. -/
noncomputable def entryInf {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun L : BoundMatrix I => L i j) '' restrictedLipCertificates d ϕ U)

/-- HC02-D07.  A component channel is an input/output pair. -/
abbrev ComponentChannel (I : Type u) := I × I

/-- HC02-D07.  In output row `j`, only input position `i` may be nonzero. -/
def RowSparse {I : Type u} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- HC02-D07.  Existence of a single supporting input in output row `j`. -/
def RowDecoupled {I : Type u} (L : BoundMatrix I) (j : I) : Prop :=
  ∃ i : I, RowSparse L i j

/-- HC02-D07.  In input column `i`, only output position `j` may be nonzero. -/
def ColumnSparse {I : Type u} (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- HC02-D07.  Existence of a single supporting output in input column `i`. -/
def ColumnDecoupled {I : Type u} (L : BoundMatrix I) (i : I) : Prop :=
  ∃ j : I, ColumnSparse L i j

/-- HC02-D07.  A completely decoupled certificate is diagonal. -/
def Diagonal {I : Type u} (L : BoundMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- HC02-D08.  Feasible scalar constants for one component channel. -/
def scalarFeasible {X : Type} {I : Type u} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  {lam | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y}

/-- HC02-D08.  The optimal single-channel constant.  In `ENNReal`,
`sInf ∅ = ∞`, exactly as required by the text. -/
noncomputable def channelLip {X : Type} {I : Type u} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (scalarFeasible d ϕ U i j)

/-- HC02-D05.  The actual input domain after zero steps is `U`; after the
next step it is the image under that step. -/
def actualDomain {X : Type} {bot : X} (U : Set X)
    (ϕ : ℕ → Operator X bot) : ℕ → Set X
  | 0 => U
  | n + 1 => (ϕ n).func '' actualDomain U ϕ n

/-- HC02-D04/D05.  The finite operator chain in application order. -/
def operatorChain {X : Type} {bot : X} (ϕ : ℕ → Operator X bot) :
    ℕ → Operator X bot
  | 0 => OperatorChain []
  | n + 1 => OperatorChain [ϕ n, operatorChain ϕ n]

/-- HC02-D05.  Every local Lip bound is imposed on the actual input domain
of its own step; no final-composite bound occurs in this predicate. -/
def LipChainValid {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (L : ℕ → BoundMatrix I) : ℕ → Prop
  | 0 => True
  | n + 1 => LipChainValid d U ϕ L n ∧
      L n ∈ restrictedLipCertificates d (ϕ n) (actualDomain U ϕ n)

/-- HC02-D05.  The analogous local co-Lip chain data. -/
def CoLipChainValid {X : Type} {I : Type u} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (K : ℕ → BoundMatrix I) : ℕ → Prop
  | 0 => True
  | n + 1 => CoLipChainValid d U ϕ K n ∧
      K n ∈ restrictedCoLipCertificates d (ϕ n) (actualDomain U ϕ n)

/-- HC02-D06.  Complete finite index paths.  `single` is the unique empty
intermediate sequence at length one.  `snoc` appends one final edge; the old
terminal index becomes the last intermediate index. -/
inductive IndexPath (I : Type u) : ℕ → I → I → Type u where
  | single (i j : I) : IndexPath I 1 i j
  | snoc {n : ℕ} {i k : I} (p : IndexPath I n i k) (j : I) : IndexPath I (n + 1) i j

namespace IndexPath

/-- HC02-D06.  The intermediate index sequence `(k₁,...,k_{n-1})`. -/
def intermediate {I : Type u} {n : ℕ} {i j : I} : IndexPath I n i j → List I
  | .single _ _ => []
  | .snoc (k := k) p _ => intermediate p ++ [k]

/-- HC02-D06.  The path weight, namely the product of its edge entries in
application order. -/
noncomputable def weight {I : Type u} (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I} :
    IndexPath I n i j → ENNReal
  | .single i j => A 0 i j
  | .snoc (n := n) (k := k) p j => weight A p * A n k j

/-- HC02-D06.  Every edge on the path is strictly positive. -/
def AllPositive {I : Type u} (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I} :
    IndexPath I n i j → Prop
  | .single i j => 0 < A 0 i j
  | .snoc (n := n) (k := k) p j => AllPositive A p ∧ 0 < A n k j

/-- HC02-D06.  At least one edge on the path is zero. -/
def HasZero {I : Type u} (A : ℕ → BoundMatrix I) {n : ℕ} {i j : I} :
    IndexPath I n i j → Prop
  | .single i j => A 0 i j = 0
  | .snoc (n := n) (k := k) p j => HasZero A p ∨ A n k j = 0

end IndexPath

end formal_oet.vol_01.ch_02_operator_bounds
