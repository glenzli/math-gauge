以下为完整 Lean 源码与对齐清单。`Main.lean` 已在本地通过 `lake build`，并且抽查的 `#print axioms` 仅显示 `propext`、`Classical.choice`、`Quot.sound`。

```lean filename=Main.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# Operator bounds on an extended gauge space

This file formalizes the mathematical content of the historical Chapter 2,
`source/02-operator-bounds.md`, on top of the frozen Chapter 1 modules.
Matrices are stored input-first: an entry `M i j` describes the coefficient
from the input component `d i` to the output component `d j`.
-/

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace formal_oet.vol_01.ch_02_operator_bounds

universe v

variable {X : Type} {I : Type v}

section Basic

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Input-first coefficient matrices.  The first index is the input component
and the second index is the output component. -/
abbrev CoeffMatrix (I : Type v) : Type v := I → I → ENNReal

/-- Composition of input-first coefficient matrices.  If `M₂` follows `M₁`
along a chain, the composite coefficient from `i` to `j` is
`∑ k, M₂ k j * M₁ i k`. -/
noncomputable def matMul (M₂ M₁ : CoeffMatrix I) : CoeffMatrix I :=
  fun i j => ∑ k : I, M₂ k j * M₁ i k

@[simp]
theorem matMul_apply (M₂ M₁ : CoeffMatrix I) (i j : I) :
    matMul M₂ M₁ i j = ∑ k : I, M₂ k j * M₁ i k :=
  rfl

/-- The ordinary row-by-column matrix associated with an input-first matrix;
the ordinary row index is the output index `j`, and the ordinary column index
is the input index `i`. -/
def toOrdinaryMatrix (M : CoeffMatrix I) : Matrix I I ENNReal :=
  fun j i => M i j

@[simp]
theorem toOrdinaryMatrix_apply (M : CoeffMatrix I) (j i : I) :
    toOrdinaryMatrix M j i = M i j :=
  rfl

/-- In ordinary row-by-column notation, the chapter's composite matrix is the
usual product of the ordinary matrices. -/
theorem toOrdinaryMatrix_matMul (M₂ M₁ : CoeffMatrix I) :
    toOrdinaryMatrix (matMul M₂ M₁) =
      toOrdinaryMatrix M₂ * toOrdinaryMatrix M₁ := by
  ext j i
  simp [toOrdinaryMatrix, matMul, Matrix.mul_apply]

/-- The identity coefficient matrix, with entries `δ i j`. -/
noncomputable def matId : CoeffMatrix I :=
  fun i j => if i = j then 1 else 0

@[simp]
theorem matId_apply (i j : I) : matId (I := I) i j = if i = j then 1 else 0 :=
  rfl

/-- The identity coefficient matrix is a left unit for `matMul`. -/
theorem matId_matMul (M : CoeffMatrix I) : matMul matId M = M := by
  funext i j
  rw [matMul_apply]
  rw [Finset.sum_eq_single j]
  · simp [matId]
  · intro k _ hk
    simp [matId, hk, Ne.symm hk]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The identity coefficient matrix is a right unit for `matMul`. -/
theorem matMul_matId (M : CoeffMatrix I) : matMul M matId = M := by
  funext i j
  rw [matMul_apply]
  rw [Finset.sum_eq_single i]
  · simp [matId]
  · intro k _ hk
    simp [matId, hk, Ne.symm hk]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Matrix composition is associative. -/
theorem matMul_assoc (M₃ M₂ M₁ : CoeffMatrix I) :
    matMul (matMul M₃ M₂) M₁ = matMul M₃ (matMul M₂ M₁) := by
  funext i j
  simp only [matMul_apply]
  calc
    (∑ k : I, (∑ l : I, M₃ l j * M₂ k l) * M₁ i k)
        = ∑ k : I, ∑ l : I, (M₃ l j * M₂ k l) * M₁ i k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ = ∑ l : I, ∑ k : I, (M₃ l j * M₂ k l) * M₁ i k := by
          rw [Finset.sum_comm]
    _ = ∑ l : I, M₃ l j * ∑ k : I, M₂ k l * M₁ i k := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- An operator is Lipschitz on `U` with coefficient matrix `L` when `U` is
contained in its domain and the displayed componentwise upper bound holds. -/
def IsLipOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : CoeffMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y

/-- The family of all legal Lipschitz upper-bound certificates on `U`. -/
def LipFamily (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (CoeffMatrix I) :=
  {L | IsLipOn d φ U L}

/-- The family of legal Lipschitz matrices on the whole domain of `φ`. -/
def LipFamilyFull (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (CoeffMatrix I) :=
  LipFamily d φ (dom φ)

/-- An operator is co-Lipschitz on a nonempty `U` with coefficient matrix `K`
when `U ⊆ dom φ` and the displayed componentwise lower bound holds. -/
def IsCoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : CoeffMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

/-- The family of all legal co-Lipschitz lower-bound certificates on `U`. -/
def CoLipFamily (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (CoeffMatrix I) :=
  {K | IsCoLipOn d φ U K}

/-- The set of scalar constants satisfying the single-channel upper bound from
input component `i` to output component `j` on `U`. -/
def ScalarFeasible (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : Set ENNReal :=
  {lam | ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ lam * d i x y}

/-- The single-channel Lipschitz constant, defined as the infimum of the
feasible scalar constants. -/
noncomputable def singleChannelLipConstant
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I) :
    ENNReal :=
  sInf (ScalarFeasible d φ U i j)

/-- A component channel is simply a pair of input and output indices. -/
abbrev Channel (I : Type v) : Type v := I × I

/-- The row support condition for output component `j`: only the input index
`i` may have a nonzero coefficient in row `j`. -/
def RowSupport (L : CoeffMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- A matrix is row-decoupled at output `j` if some single input index supports
the whole row. -/
def RowDecoupled (L : CoeffMatrix I) (j : I) : Prop :=
  ∃ i : I, RowSupport L i j

/-- The column support condition for input component `i`: only the output
index `j` may have a nonzero coefficient in column `i`. -/
def ColumnSupport (L : CoeffMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- A matrix is column-decoupled at input `i` if some single output index
supports the whole column. -/
def ColumnDecoupled (L : CoeffMatrix I) (i : I) : Prop :=
  ∃ j : I, ColumnSupport L i j

/-- A matrix is diagonal when every off-diagonal entry is zero. -/
def IsDiagonal (L : CoeffMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- A diagonal upper-bound certificate gives a completely decoupled system of
scalar component bounds. -/
def CompletelyDecoupled (L : CoeffMatrix I) : Prop :=
  IsDiagonal L

end Basic

section OperatorChains

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- The identity operator. -/
def opId : Operator X bot :=
  ⟨id, rfl⟩

/-- Composition of operators, written in ordinary function-composition order:
`opComp ψ φ` is `ψ ∘ φ`. -/
def opComp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

@[simp]
theorem opComp_apply (ψ φ : Operator X bot) (x : X) :
    (opComp ψ φ).func x = ψ.func (φ.func x) :=
  rfl

@[simp]
theorem opId_apply (x : X) : (opId (X := X) (bot := bot)).func x = x :=
  rfl

/-- The finite ordered product `φ₀ ∘ ⋯ ∘ φₙ₋₁`, represented by a `Fin n`
family in execution order. -/
noncomputable def opProd : (n : Nat) → (Fin n → Operator X bot) → Operator X bot
  | 0, _ => opId
  | n + 1, φ => opComp (φ (Fin.last n)) (opProd n (fun i => φ i.castSucc))

/-- The finite ordered product of input-first matrices in the same order as
`opProd`: `M₀` is applied first and `Mₙ₋₁` last, so the last matrix is on the
left. -/
noncomputable def matProd : (n : Nat) → (Fin n → CoeffMatrix I) → CoeffMatrix I
  | 0, _ => matId
  | n + 1, M => matMul (M (Fin.last n)) (matProd n (fun i => M i.castSucc))

@[simp]
theorem opProd_zero (φ : Fin 0 → Operator X bot) :
    opProd 0 φ = opId :=
  rfl

@[simp]
theorem opProd_succ {n : Nat} (φ : Fin (n + 1) → Operator X bot) :
    opProd (n + 1) φ =
      opComp (φ (Fin.last n)) (opProd n (fun i => φ i.castSucc)) :=
  rfl

@[simp]
theorem matProd_zero (M : Fin 0 → CoeffMatrix I) :
    matProd 0 M = matId :=
  rfl

@[simp]
theorem matProd_succ {n : Nat} (M : Fin (n + 1) → CoeffMatrix I) :
    matProd (n + 1) M =
      matMul (M (Fin.last n)) (matProd n (fun i => M i.castSucc)) :=
  rfl

/-- The actual input domain of the `m`-th step of a chain.  It is defined
recursively by the chapter's rule `U₀ = U`, `U_{m+1} = φ_m(U_m)`. -/
noncomputable def stepInput {n : Nat} (φ : Fin n → Operator X bot) (U : Set X) :
    (m : Nat) → m ≤ n → Set X
  | 0, _ => U
  | m + 1, hm =>
      (φ ⟨m, Nat.lt_of_succ_le hm⟩).func '' stepInput φ U m (Nat.le_of_succ_le hm)

@[simp]
theorem stepInput_zero {n : Nat} (φ : Fin n → Operator X bot) (U : Set X)
    (h : 0 ≤ n) :
    stepInput φ U 0 h = U := by
  simp [stepInput]

theorem stepInput_succ {n : Nat} (φ : Fin n → Operator X bot) (U : Set X)
    (m : Nat) (hm : m + 1 ≤ n) :
    stepInput φ U (m + 1) hm =
      (φ ⟨m, Nat.lt_of_succ_le hm⟩).func ''
        stepInput φ U m (Nat.le_of_succ_le hm) := by
  simp [stepInput]

/-- Taking a prefix of the operator family leaves all earlier input domains
unchanged. -/
theorem stepInput_prefix {n : Nat} (φ : Fin (n + 1) → Operator X bot)
    (U : Set X) :
    ∀ (m : Nat) (hm : m ≤ n),
      stepInput (fun i : Fin n => φ i.castSucc) U m hm =
        stepInput φ U m (le_trans hm (Nat.le_succ n)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp [stepInput]
  | succ m ih =>
      intro hm
      rw [stepInput_succ, stepInput_succ]
      simp only [ih (Nat.le_of_succ_le hm)]
      congr 1

/-- The actual image of the prefix of a chain. -/
noncomputable def prefixImage {n : Nat} (φ : Fin n → Operator X bot) (U : Set X)
    (m : Nat) (hm : m ≤ n) : Set X :=
  stepInput φ U m hm

end OperatorChains

section ChainImages

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- The actual image after `m` steps is the image of the corresponding prefix
composite operator. -/
theorem stepInput_eq_opProd_image {n : Nat} (φ : Fin n → Operator X bot)
    (U : Set X) :
    ∀ (m : Nat) (hm : m ≤ n),
      stepInput φ U m hm =
        (opProd m (fun i : Fin m => φ (Fin.castLE hm i))).func '' U := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp [stepInput, opProd, opId]
  | succ m ih =>
      intro hm
      have hm0 : m ≤ n := Nat.le_of_succ_le hm
      have hlast : (Fin.castLE hm (Fin.last m) : Fin n) =
          ⟨m, Nat.lt_of_succ_le hm⟩ := by
        ext
        simp [Fin.castLE]
      have hfam : (fun i : Fin m => φ (Fin.castLE hm (Fin.castSucc i))) =
          (fun i : Fin m => φ (Fin.castLE hm0 i)) := by
        funext i
        congr 1
      rw [stepInput_succ, ih hm0]
      rw [show opProd (m + 1)
          (fun i : Fin (m + 1) => φ (Fin.castLE hm i)) =
          opComp (φ ⟨m, Nat.lt_of_succ_le hm⟩)
            (opProd m (fun i : Fin m => φ (Fin.castLE hm0 i))) by
        ext x
        simp only [opProd, opComp, Function.comp_apply]
        rw [hlast]
        congr 1]
      rw [← Set.image_comp]
      rfl

end ChainImages

section ChainDomains

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Membership in the domain of a composite operator. -/
theorem mem_dom_opComp {ψ φ : Operator X bot} {x : X} :
    x ∈ dom (opComp ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  constructor
  · intro hx
    have hφ : φ.func x ≠ bot := by
      intro hbot
      apply hx
      simp [dom, opComp_apply, hbot, ψ.preserves_bot]
    constructor
    · simpa [dom] using hφ
    · simpa [dom, opComp_apply] using hx
  · rintro ⟨hφ, hψ⟩
    simpa [dom, opComp_apply] using hψ

/-- The actual input domain of every step of a chain is contained in the
domain of that step's operator, under the chapter's starting-domain
hypothesis. -/
theorem stepInput_subset_dom_of_chain_dom {n : Nat}
    (φ : Fin n → Operator X bot) (U : Set X)
    (hU : U ⊆ dom (opProd n φ)) :
    ∀ (m : Nat) (hm : m < n),
      stepInput φ U m (Nat.le_of_lt hm) ⊆ dom (φ ⟨m, hm⟩) := by
  induction n with
  | zero =>
      intro m hm
      omega
  | succ n ih =>
      have hUpre : U ⊆ dom (opProd n (fun i : Fin n => φ i.castSucc)) := by
        intro x hx
        have hxfull : x ∈ dom (opProd (n + 1) φ) := hU hx
        rw [show opProd (n + 1) φ =
            opComp (φ (Fin.last n)) (opProd n (fun i : Fin n => φ i.castSucc)) by
              rfl] at hxfull
        exact (mem_dom_opComp.mp hxfull).1
      have hUlast : ∀ x ∈ U,
          (opProd n (fun i : Fin n => φ i.castSucc)).func x ∈ dom (φ (Fin.last n)) := by
        intro x hx
        have hxfull : x ∈ dom (opProd (n + 1) φ) := hU hx
        rw [show opProd (n + 1) φ =
            opComp (φ (Fin.last n)) (opProd n (fun i : Fin n => φ i.castSucc)) by
              rfl] at hxfull
        exact (mem_dom_opComp.mp hxfull).2
      intro m hm
      by_cases hmn : m < n
      · have hprefix := stepInput_prefix φ U m (Nat.le_of_lt hmn)
        rw [← hprefix]
        have hsubset := ih (fun i : Fin n => φ i.castSucc) hUpre m hmn
        simpa using hsubset
      · have hmn_eq : m = n := by omega
        subst m
        have himage := stepInput_eq_opProd_image φ U n (Nat.le_succ n)
        rw [himage]
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have hl := hUlast x hx
        simpa using hl

end ChainDomains

section Families

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Restricting a full-domain Lipschitz certificate to a subset of the domain
preserves legality. -/
theorem lipFamilyFull_subset_lipFamily
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom φ) :
    LipFamilyFull d φ ⊆ LipFamily d φ U := by
  intro L hL
  exact ⟨fun x hx => hL.1 (hU hx), fun x hx y hy j => hL.2 x (hU hx) y (hU hy) j⟩

/-- Shrinking the evaluation domain only enlarges the family of legal
Lipschitz certificates. -/
theorem lipFamily_mono
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) :
    LipFamily d φ V ⊆ LipFamily d φ U := by
  intro L hL
  exact ⟨fun x hx => hL.1 (hUV hx),
    fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- The entrywise infimum of a Lipschitz certificate family. -/
noncomputable def lipEntryInf
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I) :
    ENNReal :=
  sInf ((fun L : CoeffMatrix I => L i j) '' LipFamily d φ U)

/-- If the evaluation domain shrinks, the entrywise infimum of the legal
Lipschitz matrices cannot increase. -/
theorem lipEntryInf_antitone
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (i j : I) :
    lipEntryInf d φ U i j ≤ lipEntryInf d φ V i j := by
  apply sInf_le_sInf
  rintro a ⟨L, hL, rfl⟩
  exact ⟨L, lipFamily_mono d φ hUV hL, rfl⟩

/-- In the one-component case, a legal Lipschitz matrix reduces to the expected
scalar upper bound for its only diagonal entry. -/
theorem lip_single_component [Unique I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {L : CoeffMatrix I} (hL : L ∈ LipFamily d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  have h := hL.2 x hx y hy j
  rw [Finset.sum_eq_single j] at h
  · exact h
  · intro k _ hk
    exact (hk (Subsingleton.elim k j)).elim
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

end Families

section TwoStep

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Two-step Lipschitz composition law. -/
theorem lip_comp
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    {U₁ : Set X} {L₁ L₂ : CoeffMatrix I}
    (hU₁ : U₁ ⊆ dom (opComp φ₂ φ₁))
    (hL₁ : L₁ ∈ LipFamily d φ₁ U₁)
    (hL₂ : L₂ ∈ LipFamily d φ₂ (φ₁.func '' U₁)) :
    matMul L₂ L₁ ∈ LipFamily d (opComp φ₂ φ₁) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : φ₁.func x ∈ φ₁.func '' U₁ := ⟨x, hx, rfl⟩
  have hy₂ : φ₁.func y ∈ φ₁.func '' U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((opComp φ₂ φ₁).func x) ((opComp φ₂ φ₁).func y)
        = d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := rfl
    _ ≤ ∑ k : I, L₂ k j * d k (φ₁.func x) (φ₁.func y) :=
          hL₂.2 (φ₁.func x) hx₂ (φ₁.func y) hy₂ j
    _ ≤ ∑ k : I, L₂ k j * (∑ i : I, L₁ i k * d i x y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (hL₁.2 x hx y hy k) (L₂ k j)
    _ = ∑ k : I, ∑ i : I, L₂ k j * (L₁ i k * d i x y) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, L₂ k j * (L₁ i k * d i x y) := by
          rw [Finset.sum_comm]
    _ = ∑ i : I, (∑ k : I, L₂ k j * L₁ i k) * d i x y := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ i : I, matMul L₂ L₁ i j * d i x y := by
          simp [matMul_apply]

/-- Two-step co-Lipschitz composition law. -/
theorem colip_comp
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    {U₁ : Set X} {K₁ K₂ : CoeffMatrix I}
    (hU₁ : U₁ ⊆ dom (opComp φ₂ φ₁))
    (hK₁ : K₁ ∈ CoLipFamily d φ₁ U₁)
    (hK₂ : K₂ ∈ CoLipFamily d φ₂ (φ₁.func '' U₁)) :
    matMul K₂ K₁ ∈ CoLipFamily d (opComp φ₂ φ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : φ₁.func x ∈ φ₁.func '' U₁ := ⟨x, hx, rfl⟩
  have hy₂ : φ₁.func y ∈ φ₁.func '' U₁ := ⟨y, hy, rfl⟩
  calc
    (∑ i : I, matMul K₂ K₁ i j * d i x y)
        = ∑ i : I, (∑ k : I, K₂ k j * K₁ i k) * d i x y := by
          simp [matMul_apply]
    _ = ∑ i : I, ∑ k : I, K₂ k j * (K₁ i k * d i x y) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ k : I, ∑ i : I, K₂ k j * (K₁ i k * d i x y) := by
          rw [Finset.sum_comm]
    _ = ∑ k : I, K₂ k j * (∑ i : I, K₁ i k * d i x y) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
    _ ≤ ∑ k : I, K₂ k j * d k (φ₁.func x) (φ₁.func y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (hK₁.2.2 x hx y hy k) (K₂ k j)
    _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) :=
          hK₂.2.2 (φ₁.func x) hx₂ (φ₁.func y) hy₂ j

end TwoStep

section IdentityAndZero

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- A zero output distance and a strictly positive input distance force the
corresponding co-Lipschitz coefficient to vanish. -/
theorem colip_coeff_eq_zero_of_output_zero
    (d : I → X → X → ENNReal) (φ : Operator X bot)
    {K : CoeffMatrix I} (hK : K ∈ CoLipFamily d φ (dom φ))
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hzero : d j (φ.func x) (φ.func y) = 0)
    (hpos : 0 < d i x y) :
    K i j = 0 := by
  have hle := hK.2.2 x hx y hy j
  rw [hzero] at hle
  have hsum_nonneg : 0 ≤ ∑ k : I, K k j * d k x y := zero_le _
  have hsum_zero : (∑ k : I, K k j * d k x y) = 0 :=
    le_antisymm hle hsum_nonneg
  have hterm : K i j * d i x y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le _)).mp hsum_zero i
      (Finset.mem_univ i)
  rcases (mul_eq_zero.mp hterm) with hKij | hd
  · exact hKij
  · exact (ne_of_gt hpos hd).elim

/-- The identity matrix is a legal Lipschitz certificate for the identity
operator on every subset of its domain. -/
theorem matId_mem_lip_opId
    (d : I → X → X → ENNReal) (U : Set X)
    (hUdom : U ⊆ dom (opId (X := X) (bot := bot))) :
    matId ∈ LipFamily d (opId (X := X) (bot := bot)) U := by
  refine ⟨hUdom, ?_⟩
  intro x hx y hy j
  simp [opId, matId, Finset.sum_ite_eq']

/-- The identity matrix is a legal co-Lipschitz certificate for the identity
operator on every nonempty subset of its domain. -/
theorem matId_mem_colip_opId
    (d : I → X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    (hUdom : U ⊆ dom (opId (X := X) (bot := bot))) :
    matId ∈ CoLipFamily d (opId (X := X) (bot := bot)) U := by
  refine ⟨hU, hUdom, ?_⟩
  intro x hx y hy j
  simp [opId, matId, Finset.sum_ite_eq']

end IdentityAndZero

section ChainCertificates

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Finite Lip certificate product along an actual image-domain chain. -/
theorem lip_fin_chain {n : Nat}
    (d : I → X → X → ENNReal) (φ : Fin n → Operator X bot)
    (L : Fin n → CoeffMatrix I) (U : Set X)
    (hU : U ⊆ dom (opProd n φ))
    (hStep : ∀ m : Fin n,
      L m ∈ LipFamily d (φ m)
        (stepInput φ U m.val (Nat.le_of_lt m.isLt))) :
    matProd n L ∈ LipFamily d (opProd n φ) U := by
  induction n with
  | zero =>
      simpa [matProd, opProd] using
        (matId_mem_lip_opId (d := d) (U := U) (by simpa [opProd] using hU))
  | succ n ih =>
      let φ₀ : Fin n → Operator X bot := fun i => φ i.castSucc
      let L₀ : Fin n → CoeffMatrix I := fun i => L i.castSucc
      have hU₀ : U ⊆ dom (opProd n φ₀) := by
        intro x hx
        have hxfull : x ∈ dom (opProd (n + 1) φ) := hU hx
        rw [show opProd (n + 1) φ =
            opComp (φ (Fin.last n)) (opProd n (fun i : Fin n => φ i.castSucc)) by
              rfl] at hxfull
        exact (mem_dom_opComp.mp hxfull).1
      have hStep₀ : ∀ m : Fin n,
          L₀ m ∈ LipFamily d (φ₀ m)
            (stepInput φ₀ U m.val (Nat.le_of_lt m.isLt)) := by
        intro m
        have h := hStep (Fin.castSucc m)
        have hEq : stepInput φ U (Fin.castSucc m).val
            (Nat.le_of_lt (Fin.castSucc m).isLt) =
            stepInput φ₀ U m.val (Nat.le_of_lt m.isLt) := by
          have hp := stepInput_prefix φ U m.val (Nat.le_of_lt m.isLt)
          simpa [φ₀, Fin.val_castSucc] using hp.symm
        rw [hEq] at h
        simpa [L₀] using h
      have hprod₀ : matProd n L₀ ∈ LipFamily d (opProd n φ₀) U :=
        ih φ₀ L₀ hU₀ hStep₀
      have hUcomp : U ⊆ dom (opComp (φ (Fin.last n)) (opProd n φ₀)) := by
        simpa [opProd, φ₀] using hU
      have hlast : L (Fin.last n) ∈
          LipFamily d (φ (Fin.last n)) ((opProd n φ₀).func '' U) := by
        have h := hStep (Fin.last n)
        have hEq : stepInput φ U (Fin.last n).val
            (Nat.le_of_lt (Fin.last n).isLt) = (opProd n φ₀).func '' U := by
          have himage := stepInput_eq_opProd_image φ U n (Nat.le_succ n)
          simpa [φ₀, Fin.val_last] using himage
        rw [hEq] at h
        exact h
      have hcomp := lip_comp d (opProd n φ₀) (φ (Fin.last n))
        hUcomp hprod₀ hlast
      simpa [matProd, opProd, φ₀, L₀] using hcomp

/-- Finite co-Lip certificate product along an actual image-domain chain. -/
theorem colip_fin_chain {n : Nat}
    (d : I → X → X → ENNReal) (φ : Fin n → Operator X bot)
    (K : Fin n → CoeffMatrix I) (U : Set X) (hUne : U.Nonempty)
    (hU : U ⊆ dom (opProd n φ))
    (hStep : ∀ m : Fin n,
      K m ∈ CoLipFamily d (φ m)
        (stepInput φ U m.val (Nat.le_of_lt m.isLt))) :
    matProd n K ∈ CoLipFamily d (opProd n φ) U := by
  induction n with
  | zero =>
      simpa [matProd, opProd] using
        (matId_mem_colip_opId (d := d) (U := U) hUne
          (by simpa [opProd] using hU))
  | succ n ih =>
      let φ₀ : Fin n → Operator X bot := fun i => φ i.castSucc
      let K₀ : Fin n → CoeffMatrix I := fun i => K i.castSucc
      have hU₀ : U ⊆ dom (opProd n φ₀) := by
        intro x hx
        have hxfull : x ∈ dom (opProd (n + 1) φ) := hU hx
        rw [show opProd (n + 1) φ =
            opComp (φ (Fin.last n)) (opProd n (fun i : Fin n => φ i.castSucc)) by
              rfl] at hxfull
        exact (mem_dom_opComp.mp hxfull).1
      have hStep₀ : ∀ m : Fin n,
          K₀ m ∈ CoLipFamily d (φ₀ m)
            (stepInput φ₀ U m.val (Nat.le_of_lt m.isLt)) := by
        intro m
        have h := hStep (Fin.castSucc m)
        have hEq : stepInput φ U (Fin.castSucc m).val
            (Nat.le_of_lt (Fin.castSucc m).isLt) =
            stepInput φ₀ U m.val (Nat.le_of_lt m.isLt) := by
          have hp := stepInput_prefix φ U m.val (Nat.le_of_lt m.isLt)
          simpa [φ₀, Fin.val_castSucc] using hp.symm
        rw [hEq] at h
        simpa [K₀] using h
      have hprod₀ : matProd n K₀ ∈ CoLipFamily d (opProd n φ₀) U :=
        ih φ₀ K₀ hU₀ hStep₀
      have hUcomp : U ⊆ dom (opComp (φ (Fin.last n)) (opProd n φ₀)) := by
        simpa [opProd, φ₀] using hU
      have hlast : K (Fin.last n) ∈
          CoLipFamily d (φ (Fin.last n)) ((opProd n φ₀).func '' U) := by
        have h := hStep (Fin.last n)
        have hEq : stepInput φ U (Fin.last n).val
            (Nat.le_of_lt (Fin.last n).isLt) = (opProd n φ₀).func '' U := by
          have himage := stepInput_eq_opProd_image φ U n (Nat.le_succ n)
          simpa [φ₀, Fin.val_last] using himage
        rw [hEq] at h
        exact h
      have hcomp := colip_comp d (opProd n φ₀) (φ (Fin.last n))
        hUcomp hprod₀ hlast
      simpa [matProd, opProd, φ₀, K₀] using hcomp

/-- Positive-length co-Lip chain product; nonemptiness of the starting domain
is supplied by the first step certificate. -/
theorem colip_fin_chain_positive {n : Nat} (hn : 1 ≤ n)
    (d : I → X → X → ENNReal) (φ : Fin n → Operator X bot)
    (K : Fin n → CoeffMatrix I) (U : Set X)
    (hU : U ⊆ dom (opProd n φ))
    (hStep : ∀ m : Fin n,
      K m ∈ CoLipFamily d (φ m)
        (stepInput φ U m.val (Nat.le_of_lt m.isLt))) :
    matProd n K ∈ CoLipFamily d (opProd n φ) U := by
  have h0 : (0 : Nat) < n := lt_of_lt_of_le Nat.zero_lt_one hn
  exact colip_fin_chain d φ K U (hStep ⟨0, h0⟩).1 hU hStep

end ChainCertificates

section Perturbation

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- A pointwise perturbation bound for two operators on a common domain. -/
def PointwisePerturbation
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot) (U : Set X)
    (δ : I → ENNReal) : Prop :=
  U ⊆ dom φ₁ ∩ dom φ₂ ∧
    ∀ z ∈ U, ∀ j : I, d j (φ₁.func z) (φ₂.func z) ≤ δ j

/-- Forward point-pair image-distance perturbation bound. -/
theorem perturbation_forward
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {U : Set X} {δ : I → ENNReal}
    (hδ : PointwisePerturbation d φ₁ φ₂ U δ)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₂.func x) (φ₂.func y) ≤
      d j (φ₁.func x) (φ₁.func y) + δ j + δ j := by
  have hleft : d j (φ₂.func x) (φ₁.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ.2 x hx j
  have hright : d j (φ₁.func y) (φ₂.func y) ≤ δ j := hδ.2 y hy j
  calc
    d j (φ₂.func x) (φ₂.func y)
        ≤ d j (φ₂.func x) (φ₁.func x) + d j (φ₁.func x) (φ₂.func y) :=
          (hd j).triangle _ _ _
    _ ≤ d j (φ₂.func x) (φ₁.func x) +
          (d j (φ₁.func x) (φ₁.func y) + d j (φ₁.func y) (φ₂.func y)) :=
          add_le_add_right ((hd j).triangle _ _ _) _
    _ ≤ δ j + (d j (φ₁.func x) (φ₁.func y) + δ j) :=
          add_le_add hleft (add_le_add le_rfl hright)
    _ = d j (φ₁.func x) (φ₁.func y) + δ j + δ j := by
          rw [add_comm (δ j) (d j (φ₁.func x) (φ₁.func y) + δ j)]

/-- Reverse point-pair image-distance perturbation bound. -/
theorem perturbation_backward
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {U : Set X} {δ : I → ENNReal}
    (hδ : PointwisePerturbation d φ₁ φ₂ U δ)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₁.func x) (φ₁.func y) ≤
      d j (φ₂.func x) (φ₂.func y) + δ j + δ j := by
  have hδ' : PointwisePerturbation d φ₂ φ₁ U δ := by
    refine ⟨?_, ?_⟩
    · intro z hz
      exact ⟨(hδ.1 hz).2, (hδ.1 hz).1⟩
    · intro z hz j
      rw [(hd j).symm]
      exact hδ.2 z hz j
  exact perturbation_forward d hd φ₂ φ₁ hδ' hx hy j

/-- Perturbation plus a Lipschitz certificate gives an additive output bound. -/
theorem perturbation_lip_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {U : Set X} {δ : I → ENNReal}
    (hδ : PointwisePerturbation d φ₁ φ₂ U δ)
    {L : CoeffMatrix I} (hL : L ∈ LipFamily d φ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ₂.func x) (φ₂.func y) ≤
      (∑ i : I, L i j * d i x y) + δ j + δ j := by
  calc
    d j (φ₂.func x) (φ₂.func y)
        ≤ d j (φ₁.func x) (φ₁.func y) + δ j + δ j :=
          perturbation_forward d hd φ₁ φ₂ hδ hx hy j
    _ ≤ (∑ i : I, L i j * d i x y) + δ j + δ j := by
          simpa only [add_assoc] using
            add_le_add_left (hL.2 x hx y hy j) (δ j + δ j)

/-- Perturbation plus a co-Lipschitz certificate gives an additive lower
bound. -/
theorem perturbation_colip_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {U : Set X} {δ : I → ENNReal}
    (hδ : PointwisePerturbation d φ₁ φ₂ U δ)
    {K : CoeffMatrix I} (hK : K ∈ CoLipFamily d φ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K i j * d i x y) ≤
      d j (φ₂.func x) (φ₂.func y) + δ j + δ j := by
  calc
    (∑ i : I, K i j * d i x y)
        ≤ d j (φ₁.func x) (φ₁.func y) := hK.2.2 x hx y hy j
    _ ≤ d j (φ₂.func x) (φ₂.func y) + δ j + δ j :=
          perturbation_backward d hd φ₁ φ₂ hδ hx hy j

end Perturbation

section PathCriteria

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- The edge weight at layer `m` of a complete index path. -/
def pathEdge {n : Nat} (M : Fin n → CoeffMatrix I) (k : Fin (n + 1) → I)
    (m : Fin n) : ENNReal :=
  M m (k m.castSucc) (k m.succ)

/-- Every complete index path from `i` to `j` contains a zero edge. -/
def PathHasZero {n : Nat} (M : Fin n → CoeffMatrix I) (i j : I) : Prop :=
  ∀ k : Fin (n + 1) → I, k 0 = i → k (Fin.last n) = j →
    ∃ m : Fin n, pathEdge M k m = 0

/-- Some complete index path from `i` to `j` has all edges strictly positive. -/
def PathAllPositive {n : Nat} (M : Fin n → CoeffMatrix I) (i j : I) : Prop :=
  ∃ k : Fin (n + 1) → I, k 0 = i ∧ k (Fin.last n) = j ∧
    ∀ m : Fin n, 0 < pathEdge M k m

@[simp]
theorem matProd_one (M : Fin 1 → CoeffMatrix I) :
    matProd 1 M = M 0 := by
  rw [matProd_succ, matProd_zero, matMul_matId]
  congr 1

/-- A canonical path for the one-matrix case. -/
def onePath (i j : I) : Fin 2 → I :=
  fun t => if t.val = 0 then i else j

@[simp]
theorem onePath_zero (i j : I) : onePath i j 0 = i := by
  simp [onePath]

@[simp]
theorem onePath_last (i j : I) : onePath i j (Fin.last 1) = j := by
  simp [onePath, Fin.last]

theorem pathHasZero_one (M : Fin 1 → CoeffMatrix I) (i j : I) :
    PathHasZero M i j ↔ M 0 i j = 0 := by
  constructor
  · intro h
    rcases h (onePath i j) (onePath_zero i j) (onePath_last i j) with ⟨m, hm⟩
    fin_cases m
    simpa [pathEdge, onePath] using hm
  · intro h k hk0 hklast
    have hk1 : k 1 = j := by simpa [Fin.last] using hklast
    refine ⟨0, ?_⟩
    simpa [pathEdge, hk0, hk1] using h

theorem pathAllPositive_one (M : Fin 1 → CoeffMatrix I) (i j : I) :
    PathAllPositive M i j ↔ 0 < M 0 i j := by
  constructor
  · rintro ⟨k, hk0, hklast, hpos⟩
    have hk1 : k 1 = j := by simpa [Fin.last] using hklast
    have h := hpos 0
    simpa [pathEdge, hk0, hk1] using h
  · intro h
    refine ⟨onePath i j, onePath_zero i j, onePath_last i j, ?_⟩
    intro m
    fin_cases m
    simpa [pathEdge, onePath] using h

end PathCriteria

section PathInduction

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Strict positivity of a product in `ENNReal` is equivalent to strict
positivity of both factors. -/
theorem ennreal_pos_mul_iff {a b : ENNReal} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    have hne : a * b ≠ 0 := ne_of_gt h
    have ha : a ≠ 0 := fun ha => hne (by rw [ha, zero_mul])
    have hb : b ≠ 0 := fun hb => hne (by rw [hb, mul_zero])
    exact ⟨pos_iff_ne_zero.mpr ha, pos_iff_ne_zero.mpr hb⟩
  · rintro ⟨ha, hb⟩
    exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb))

/-- A full-path edge away from the final layer is the corresponding edge of
the initial path. -/
theorem pathEdge_prefix {N : Nat} (M : Fin (N + 1) → CoeffMatrix I)
    (k : Fin (N + 2) → I) (r : Fin N) :
    pathEdge M k r.castSucc =
      pathEdge (fun i : Fin N => M i.castSucc) (Fin.init k) r := by
  simp only [pathEdge, Fin.init]
  rw [Fin.succ_castSucc]

/-- Zero criterion after splitting off the last matrix. -/
theorem matProd_succ_zero_iff {N : Nat}
    (M : Fin (N + 1) → CoeffMatrix I) (i j : I) :
    matProd (N + 1) M i j = 0 ↔
      ∀ kprev : I,
        M (Fin.last N) kprev j = 0 ∨
          matProd N (fun r : Fin N => M r.castSucc) i kprev = 0 := by
  rw [matProd_succ, matMul_apply]
  constructor
  · intro h kprev
    have hterm : M (Fin.last N) kprev j *
        matProd N (fun r : Fin N => M r.castSucc) i kprev = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le _)).mp h kprev
        (Finset.mem_univ kprev)
    exact mul_eq_zero.mp hterm
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le _)).mpr
    intro kprev _
    exact mul_eq_zero.mpr (h kprev)

/-- Positive criterion after splitting off the last matrix. -/
theorem matProd_succ_pos_iff {N : Nat}
    (M : Fin (N + 1) → CoeffMatrix I) (i j : I) :
    0 < matProd (N + 1) M i j ↔
      ∃ kprev : I,
        0 < M (Fin.last N) kprev j *
          matProd N (fun r : Fin N => M r.castSucc) i kprev := by
  rw [matProd_succ, matMul_apply]
  simpa using
    (Finset.sum_pos_iff (s := Finset.univ)
      (f := fun kprev : I => M (Fin.last N) kprev j *
        matProd N (fun r : Fin N => M r.castSucc) i kprev))

end PathInduction

section PathHelpers

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Extending a prefix path by the final vertex preserves every earlier edge. -/
theorem pathEdge_snoc {N : Nat} (M : Fin (N + 1) → CoeffMatrix I)
    (q : Fin (N + 1) → I) (j : I) (r : Fin N) :
    pathEdge M (Fin.snoc q j) r.castSucc =
      pathEdge (fun i : Fin N => M i.castSucc) q r := by
  rw [pathEdge_prefix]
  rw [Fin.init_snoc]

/-- The last edge of a path extended by `j`. -/
theorem pathEdge_snoc_last {N : Nat} (M : Fin (N + 1) → CoeffMatrix I)
    (q : Fin (N + 1) → I) (j : I) :
    pathEdge M (Fin.snoc q j) (Fin.last N) =
      M (Fin.last N) (q (Fin.last N)) j := by
  simp [pathEdge, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

end PathHelpers

section PathSuccessor

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- One successor step of the path criteria, using the criteria for the
prefix product. -/
theorem path_criteria_succ {N : Nat}
    (hzero : ∀ (M : Fin N → CoeffMatrix I) (i j : I),
      matProd N M i j = 0 ↔ PathHasZero M i j)
    (hpos : ∀ (M : Fin N → CoeffMatrix I) (i j : I),
      0 < matProd N M i j ↔ PathAllPositive M i j)
    (M : Fin (N + 1) → CoeffMatrix I) (i j : I) :
    (matProd (N + 1) M i j = 0 ↔ PathHasZero M i j) ∧
      (0 < matProd (N + 1) M i j ↔ PathAllPositive M i j) := by
  let M₀ : Fin N → CoeffMatrix I := fun r => M r.castSucc
  constructor
  · constructor
    · intro h k hk0 hklast
      let kprev : I := k (Fin.castSucc (Fin.last N))
      rcases (matProd_succ_zero_iff M i j).mp h kprev with hlast | hpre
      · refine ⟨Fin.last N, ?_⟩
        simpa [pathEdge, kprev, hlast, Fin.succ_last, hklast] using hlast
      · have hz : PathHasZero M₀ i kprev := (hzero M₀ i kprev).mp hpre
        rcases hz (Fin.init k) (by simpa [Fin.init] using hk0)
            (by simp [Fin.init, kprev]) with ⟨r, hr⟩
        refine ⟨r.castSucc, ?_⟩
        rw [pathEdge_prefix]
        simpa [M₀] using hr
    · intro hpath
      apply (matProd_succ_zero_iff M i j).mpr
      intro kprev
      by_cases hlast : M (Fin.last N) kprev j = 0
      · exact Or.inl hlast
      · right
        by_contra hpre
        have hprepos : 0 < matProd N M₀ i kprev := pos_iff_ne_zero.mpr hpre
        have hlastpos : 0 < M (Fin.last N) kprev j := pos_iff_ne_zero.mpr hlast
        rcases (hpos M₀ i kprev).mp hprepos with ⟨q, hq0, hqlast, hqpos⟩
        let k : Fin (N + 2) → I := Fin.snoc q j
        have hk0 : k 0 = i := by simp [k, hq0]
        have hklast : k (Fin.last (N + 1)) = j := by simp [k]
        rcases hpath k hk0 hklast with ⟨m, hm⟩
        have hallpos : 0 < pathEdge M k m := by
          rcases Fin.eq_castSucc_or_eq_last m with ⟨r, rfl⟩ | hmlast
          · rw [pathEdge_snoc]
            exact hqpos r
          · subst m
            rw [pathEdge_snoc_last]
            simpa [hqlast] using hlastpos
        exact (ne_of_gt hallpos hm)
  · constructor
    · intro hprod
      rcases (matProd_succ_pos_iff M i j).mp hprod with ⟨kprev, hprodterm⟩
      rcases ennreal_pos_mul_iff.mp hprodterm with ⟨hlastpos, hprepos⟩
      rcases (hpos M₀ i kprev).mp hprepos with ⟨q, hq0, hqlast, hqpos⟩
      refine ⟨Fin.snoc q j, ?_, ?_, ?_⟩
      · simp [hq0]
      · simp
      · intro m
        rcases Fin.eq_castSucc_or_eq_last m with ⟨r, rfl⟩ | hmlast
        · rw [pathEdge_snoc]
          exact hqpos r
        · subst m
          rw [pathEdge_snoc_last]
          simpa [hqlast] using hlastpos
    · rintro ⟨k, hk0, hklast, hkpos⟩
      let kprev : I := k (Fin.castSucc (Fin.last N))
      have hlastpos : 0 < M (Fin.last N) kprev j := by
        have h := hkpos (Fin.last N)
        simpa [pathEdge, kprev, Fin.succ_last, hklast] using h
      have hprepos : 0 < matProd N M₀ i kprev := by
        apply (hpos M₀ i kprev).mpr
        refine ⟨Fin.init k, ?_, ?_, ?_⟩
        · simpa [Fin.init] using hk0
        · simp [Fin.init, kprev]
        · intro r
          rw [← pathEdge_prefix M k r]
          exact hkpos r.castSucc
      rw [matProd_succ_pos_iff]
      exact ⟨kprev, ennreal_pos_mul_iff.mpr ⟨hlastpos, hprepos⟩⟩

end PathSuccessor

section MainPathTheorem

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- Zero and positive path criteria for a finite matrix product of positive
length. -/
theorem matProd_path_criteria :
    ∀ (n : Nat), 1 ≤ n → ∀ (M : Fin n → CoeffMatrix I) (i j : I),
      (matProd n M i j = 0 ↔ PathHasZero M i j) ∧
        (0 < matProd n M i j ↔ PathAllPositive M i j) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro hn M i j
      cases n with
      | zero =>
          constructor
          · rw [matProd_one]
            exact (pathHasZero_one M i j).symm
          · rw [matProd_one]
            exact (pathAllPositive_one M i j).symm
      | succ m =>
          have hprev := ih (by omega : 1 ≤ Nat.succ m)
          exact path_criteria_succ
            (fun M i j => (hprev M i j).1)
            (fun M i j => (hprev M i j).2) M i j

/-- Product entry vanishes exactly when every complete index path has a zero
edge. -/
theorem matProd_eq_zero_iff_all_paths_have_zero {n : Nat} (hn : 1 ≤ n)
    (M : Fin n → CoeffMatrix I) (i j : I) :
    matProd n M i j = 0 ↔ PathHasZero M i j :=
  (matProd_path_criteria n hn M i j).1

/-- Product entry is strictly positive exactly when some complete index path
has all positive edges. -/
theorem matProd_pos_iff_exists_all_positive_path {n : Nat} (hn : 1 ≤ n)
    (M : Fin n → CoeffMatrix I) (i j : I) :
    0 < matProd n M i j ↔ PathAllPositive M i j :=
  (matProd_path_criteria n hn M i j).2

end MainPathTheorem

section ScalarBounds

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- The set of feasible scalar channel constants is upward closed. -/
theorem scalarFeasible_upward
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {lam₀ lam₁ : ENNReal}
    (h₀ : lam₀ ∈ ScalarFeasible d φ U i j) (hle : lam₀ ≤ lam₁) :
    lam₁ ∈ ScalarFeasible d φ U i j := by
  intro x hx y hy
  exact le_trans (h₀ x hx y hy) (mul_le_mul_left hle (d i x y))

/-- A positive output distance at zero input distance makes the scalar
feasible set empty. -/
theorem scalarFeasible_eq_empty_of_zero_input_pos_output
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : d i x y = 0) (hpos : 0 < d j (φ.func x) (φ.func y)) :
    ScalarFeasible d φ U i j = ∅ := by
  ext lam
  constructor
  · intro hlam
    have h := hlam x hx y hy
    rw [hzero, mul_zero] at h
    exact False.elim ((not_le_of_gt hpos) h)
  · intro h
    exact False.elim h

/-- Under the preceding zero-input/positive-output hypothesis the infimum is
`+∞`. -/
theorem singleChannelLipConstant_eq_top_of_zero_input_pos_output
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : d i x y = 0) (hpos : 0 < d j (φ.func x) (φ.func y)) :
    singleChannelLipConstant d φ U i j = ⊤ := by
  rw [singleChannelLipConstant,
    scalarFeasible_eq_empty_of_zero_input_pos_output d φ U i j hx hy hzero hpos,
    sInf_empty]

/-- Every constant strictly above a finite infimum is feasible. -/
theorem scalarFeasible_of_gt_sInf
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {a lam : ENNReal}
    (ha : a = singleChannelLipConstant d φ U i j)
    (hafin : a < ⊤) (hlt : a < lam) :
    lam ∈ ScalarFeasible d φ U i j := by
  let S := ScalarFeasible d φ U i j
  have hSne : S.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have : a = ⊤ := by
      rw [ha, singleChannelLipConstant]
      change sInf S = ⊤
      rw [hempty, sInf_empty]
    exact (ne_of_lt hafin) this
  have hex : ∃ μ ∈ S, μ < lam := by
    by_contra hnone
    have hlower : ∀ μ ∈ S, lam ≤ μ := by
      intro μ hμ
      exact le_of_not_gt (fun hμlt => hnone ⟨μ, hμ, hμlt⟩)
    have hlamle : lam ≤ sInf S := le_sInf hlower
    have hlamle_a : lam ≤ a := by
      simpa [S, singleChannelLipConstant, ha] using hlamle
    exact (not_lt_of_ge hlamle_a) hlt
  rcases hex with ⟨μ, hμ, hμlt⟩
  exact scalarFeasible_upward d φ U i j hμ (le_of_lt hμlt)

/-- If the infimum is zero, every finite positive scalar constant is feasible. -/
theorem scalarFeasible_of_sInf_eq_zero
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {a lam : ENNReal}
    (ha : a = singleChannelLipConstant d φ U i j) (ha0 : a = 0)
    (hlam0 : 0 < lam) (hlamfin : lam < ⊤) :
    lam ∈ ScalarFeasible d φ U i j := by
  have hfin0 : a < ⊤ := by simpa [ha0] using ENNReal.coe_lt_top (r := 0)
  have hlt : a < lam := by simpa [ha0] using hlam0
  exact scalarFeasible_of_gt_sInf d φ U i j ha hfin0 hlt

/-- Finiteness of the infimum is equivalent to the existence of a finite
feasible scalar constant. -/
theorem singleChannelLipConstant_lt_top_iff_exists_finite_feasible
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {a : ENNReal} (ha : a = singleChannelLipConstant d φ U i j) :
    a < ⊤ ↔ ∃ lam : ENNReal, lam < ⊤ ∧ lam ∈ ScalarFeasible d φ U i j := by
  constructor
  · intro hafin
    have hlt : a < a + 1 :=
      ENNReal.lt_add_right (ne_of_lt hafin) zero_lt_one.ne'
    have hfin : a + 1 < ⊤ :=
      ENNReal.add_lt_top.mpr ⟨hafin, ENNReal.one_lt_top⟩
    exact ⟨a + 1, hfin, scalarFeasible_of_gt_sInf d φ U i j ha hafin hlt⟩
  · rintro ⟨lam, hlamfin, hlam⟩
    have hle : a ≤ lam := by
      rw [ha, singleChannelLipConstant]
      exact sInf_le hlam
    exact lt_of_le_of_lt hle hlamfin

end ScalarBounds

section InfimumAttainment

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- For finite positive `a` and `B`, if `a * B < A`, there is a strictly
larger finite scalar `lam` still satisfying `lam * B < A`. -/
theorem exists_gt_mul_lt_of_finite_pos {a B A : ENNReal}
    (ha0 : 0 < a) (hafin : a < ⊤) (hB0 : 0 < B) (hBfin : B < ⊤)
    (hAB : a * B < A) :
    ∃ lam : ENNReal, a < lam ∧ lam * B < A := by
  by_cases hAtop : A = ⊤
  · have hlamfin : a + 1 < ⊤ :=
      ENNReal.add_lt_top.mpr ⟨hafin, ENNReal.one_lt_top⟩
    have hlt : a < a + 1 :=
      ENNReal.lt_add_right (ne_of_lt hafin) zero_lt_one.ne'
    refine ⟨a + 1, hlt, ?_⟩
    rw [hAtop]
    exact ENNReal.mul_lt_top hlamfin hBfin
  · have hAfin : A < ⊤ := lt_top_iff_ne_top.mpr hAtop
    let a' : NNReal := a.toNNReal
    let b : NNReal := B.toNNReal
    let A' : NNReal := A.toNNReal
    have hb0 : 0 < b := ENNReal.toNNReal_pos (ne_of_gt hB0) (ne_of_lt hBfin)
    have hmul_fin : a * B < ⊤ := lt_trans hAB hAfin
    have hlt' : a' * b < A' := by
      have h :=
        (ENNReal.toNNReal_lt_toNNReal (ne_of_lt hmul_fin) (ne_of_lt hAfin)).mpr hAB
      simpa [a', b, A', ENNReal.toNNReal_mul] using h
    have ha'_lt : a' < A' / b := by
      rw [lt_div_iff₀ hb0]
      exact hlt'
    rcases exists_between ha'_lt with ⟨lam', hlam'_gt, hlam'_lt⟩
    refine ⟨(lam' : ENNReal), ?_, ?_⟩
    · have haeq : (a' : ENNReal) = a := ENNReal.coe_toNNReal (ne_of_lt hafin)
      rw [← haeq]
      exact ENNReal.coe_lt_coe.mpr hlam'_gt
    · have hbeq : (b : ENNReal) = B := ENNReal.coe_toNNReal (ne_of_lt hBfin)
      have hAeq : (A' : ENNReal) = A := ENNReal.coe_toNNReal (ne_of_lt hAfin)
      rw [← hbeq, ← hAeq, ← ENNReal.coe_mul]
      apply ENNReal.coe_lt_coe.mpr
      calc
        lam' * b < (A' / b) * b := mul_lt_mul_of_pos_right hlam'_lt hb0
        _ = A' := div_mul_cancel₀ A' (ne_of_gt hb0)

/-- A finite positive single-channel infimum is itself feasible. -/
theorem singleChannelLipConstant_mem_of_pos_lt_top
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    {a : ENNReal} (ha : a = singleChannelLipConstant d φ U i j)
    (ha0 : 0 < a) (hafin : a < ⊤) :
    a ∈ ScalarFeasible d φ U i j := by
  intro x hx y hy
  by_contra hnot
  let B : ENNReal := d i x y
  let A : ENNReal := d j (φ.func x) (φ.func y)
  have hAB : a * B < A := lt_of_not_ge hnot
  have hlamfin : a + 1 < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hafin, ENNReal.one_lt_top⟩
  have hlam_gt : a < a + 1 :=
    ENNReal.lt_add_right (ne_of_lt hafin) zero_lt_one.ne'
  by_cases hB0 : B = 0
  · have hApos : 0 < A := by simpa [B, hB0] using hAB
    have hprod : (a + 1) * B < A := by simpa [B, hB0] using hApos
    have hlamS := scalarFeasible_of_gt_sInf d φ U i j ha hafin hlam_gt
    have hineq := hlamS x hx y hy
    exact (not_lt_of_ge hineq) hprod
  · have hBpos : 0 < B := pos_iff_ne_zero.mpr hB0
    have hBfin : B < ⊤ := by
      by_contra hBtop
      have hBtop' : B = ⊤ := le_antisymm le_top (le_of_not_gt hBtop)
      rw [hBtop'] at hAB
      have hmul : a * (⊤ : ENNReal) = ⊤ := ENNReal.mul_top (ne_of_gt ha0)
      rw [hmul] at hAB
      exact (not_lt_of_ge le_top) hAB
    rcases exists_gt_mul_lt_of_finite_pos ha0 hafin hBpos hBfin hAB with
      ⟨lam, hlam_gt', hprod⟩
    have hlamS := scalarFeasible_of_gt_sInf d φ U i j ha hafin hlam_gt'
    have hineq := hlamS x hx y hy
    exact (not_lt_of_ge hineq) hprod

end InfimumAttainment

section Counterexample

/-- The extended discrete metric on `Fin 3`, infinity off the diagonal. -/
def counterD (x y : Fin 3) : ENNReal :=
  if x = y then 0 else ⊤

/-- The counterexample is a genuine one-component extended gauge space. -/
@[reducible]
def counterGauge : ExtendedPseudoMetric (Fin 3) 0 counterD where
  nonabsorbing := ⟨1, by decide⟩
  dist_self := by
    intro x
    simp [counterD]
  symm := by
    intro x y
    by_cases h : x = y
    · subst y
      simp [counterD]
    · have hyx : y ≠ x := fun hyx => h hyx.symm
      simp [counterD, h, hyx]
  triangle := by
    intro x y z
    by_cases hxz : x = z
    · subst z
      simp [counterD]
    · have hxz' : counterD x z = ⊤ := by simp [counterD, hxz]
      rw [hxz']
      by_cases hxy : x = y
      · subst y
        simp [counterD, hxz]
      · simp [counterD, hxy]
  isolate_bot := by
    intro x hx
    simp [counterD, hx]

/-- The identity operator on the counterexample space. -/
def counterOp : Operator (Fin 3) 0 :=
  ⟨id, rfl⟩

/-- A two-point nonempty subset of the identity operator's domain. -/
def counterU : Set (Fin 3) := {1, 2}

/-- The counterexample's scalar feasible set is exactly the positive half-line. -/
theorem counter_scalarFeasible_iff (lam : ENNReal) :
    lam ∈ ScalarFeasible (fun _ : Unit => counterD) counterOp counterU () () ↔
      0 < lam := by
  constructor
  · intro h
    have hineq : counterD (counterOp.func 1) (counterOp.func 2) ≤
        lam * counterD 1 2 := by
      simpa using h 1 (by simp [counterU]) 2 (by simp [counterU])
    have h12 : counterD 1 2 = ⊤ := by simp [counterD]
    simp only [counterOp, id] at hineq
    rw [h12] at hineq
    by_contra hlam
    have hlam0 : lam = 0 := le_antisymm (le_of_not_gt hlam) (zero_le _)
    rw [hlam0, zero_mul] at hineq
    exact (not_le_of_gt (ENNReal.coe_lt_top (r := 0))) hineq
  · intro hlam x hx y hy
    change counterD (counterOp.func x) (counterOp.func y) ≤ lam * counterD x y
    by_cases hxy : x = y
    · subst y
      simp [counterD]
    · have hxy' : counterD x y = ⊤ := by simp [counterD, hxy]
      simp only [counterOp, id]
      rw [hxy']
      rw [ENNReal.mul_top (ne_of_gt hlam)]

/-- The counterexample's single-channel infimum is zero. -/
theorem counter_singleChannelLipConstant_eq_zero :
    singleChannelLipConstant (fun _ : Unit => counterD) counterOp counterU () () = 0 := by
  apply le_antisymm
  · rw [singleChannelLipConstant]
    rw [sInf_le_iff]
    intro b hb
    by_contra hb0
    have hbpos : 0 < b := lt_of_not_ge hb0
    rcases exists_between hbpos with ⟨c, hc0, hcb⟩
    have hcS : c ∈ ScalarFeasible (fun _ : Unit => counterD) counterOp counterU () () :=
      (counter_scalarFeasible_iff c).mpr hc0
    exact (not_lt_of_ge (hb hcS)) hcb
  · exact zero_le _

/-- Zero is not a feasible scalar constant in the counterexample. -/
theorem counter_zero_not_mem :
    (0 : ENNReal) ∉
      ScalarFeasible (fun _ : Unit => counterD) counterOp counterU () () := by
  rw [counter_scalarFeasible_iff]
  exact lt_irrefl 0

/-- A legal extended gauge space, legal operator and nonempty legal evaluation
domain for which the single-channel infimum is zero but zero is not feasible. -/
theorem zero_infimum_not_attained_counterexample :
    ∃ (d : Unit → Fin 3 → Fin 3 → ENNReal) (φ : Operator (Fin 3) 0)
      (U : Set (Fin 3)),
      (∀ i : Unit, ExtendedPseudoMetric (Fin 3) 0 (d i)) ∧
      U.Nonempty ∧ U ⊆ dom φ ∧
      singleChannelLipConstant d φ U () () = 0 ∧
      0 ∉ ScalarFeasible d φ U () () := by
  refine ⟨fun _ => counterD, counterOp, counterU, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    exact counterGauge
  · exact ⟨1, by simp [counterU]⟩
  · intro x hx
    simp [counterU] at hx
    rcases hx with rfl | rfl <;> simp [dom, counterOp]
  · exact counter_singleChannelLipConstant_eq_zero
  · exact counter_zero_not_mem

end Counterexample

section Channels

variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- A zero entry makes its contribution to the corresponding output sum zero. -/
theorem term_eq_zero_of_coeff_zero
    (d : I → X → X → ENNReal) {L : CoeffMatrix I} {i j : I}
    (hij : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by
  rw [hij, zero_mul]

/-- A zero entry can be deleted from the corresponding output sum. -/
theorem sum_erase_of_coeff_zero
    (d : I → X → X → ENNReal) {L : CoeffMatrix I} {i j : I}
    (hij : L i j = 0) (x y : X) :
    (∑ k : I, L k j * d k x y) =
      ∑ k ∈ Finset.univ \ {i}, L k j * d k x y := by
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)]
  simp [hij]

/-- A row supported at input `i` gives the single-input scalar upper bound. -/
theorem lip_bound_of_row_support
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {L : CoeffMatrix I} (hL : L ∈ LipFamily d φ U)
    {i j : I} (hrow : RowSupport L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  have h := hL.2 x hx y hy j
  have hsum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hk
      rw [hrow k hk, zero_mul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simpa [hsum] using h

/-- A column supported at output `j` makes every other output contribution of
input `i` vanish. -/
theorem column_support_term_zero
    (d : I → X → X → ENNReal) {L : CoeffMatrix I} {i j : I}
    (hcol : ColumnSupport L i j) {k : I} (hk : k ≠ j) (x y : X) :
    L i k * d i x y = 0 := by
  rw [hcol k hk, zero_mul]

/-- A diagonal Lipschitz matrix gives a scalar upper bound for every component. -/
theorem lip_diagonal_bound
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {L : CoeffMatrix I} (hL : L ∈ LipFamily d φ U) (hdiag : IsDiagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  exact lip_bound_of_row_support d φ hL (fun k hk => hdiag k j hk) hx hy

/-- A one-row Lip certificate and any co-Lip certificate give a two-sided
scalar bound at that output component. -/
theorem bilateral_bound_of_lip_row
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {L K : CoeffMatrix I} (hL : L ∈ LipFamily d φ U)
    (hK : K ∈ CoLipFamily d φ U) {j : I}
    (hrow : ∀ k : I, k ≠ j → L k j = 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · have hco := hK.2.2 x hx y hy j
    have hterm : K j j * d j x y ≤ ∑ k : I, K k j * d k x y := by
      simpa using
        (Finset.single_le_sum (s := Finset.univ)
          (f := fun k : I => K k j * d k x y)
          (fun k _ => zero_le _) (Finset.mem_univ j))
    exact le_trans hterm hco
  · exact lip_bound_of_row_support d φ hL hrow hx hy

/-- If every row is supported only on its diagonal input, every component has a
two-sided scalar bound. -/
theorem all_components_bilateral_bounds
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {L K : CoeffMatrix I} (hL : L ∈ LipFamily d φ U)
    (hK : K ∈ CoLipFamily d φ U)
    (hrow : ∀ j k : I, k ≠ j → L k j = 0) :
    ∀ (j : I) {x y : X}, x ∈ U → y ∈ U →
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro j x y hx hy
  exact bilateral_bound_of_lip_row d φ hL hK (hrow j) hx hy

/-- The preceding componentwise bounds together with finite diagonal scalar
coefficients. -/
theorem all_components_finite_bilateral_bounds
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {L K : CoeffMatrix I} (hL : L ∈ LipFamily d φ U)
    (hK : K ∈ CoLipFamily d φ U)
    (hrow : ∀ j k : I, k ≠ j → L k j = 0)
    (hLfin : ∀ j : I, L j j < ⊤) (hKfin : ∀ j : I, K j j < ⊤) :
    ∀ (j : I) {x y : X}, x ∈ U → y ∈ U →
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ L j j * d j x y ∧
        K j j < ⊤ ∧ L j j < ⊤ := by
  intro j x y hx hy
  rcases all_components_bilateral_bounds d φ hL hK hrow j hx hy with ⟨hlo, hhi⟩
  exact ⟨hlo, hhi, hKfin j, hLfin j⟩

/-- A positive co-Lip channel preserves strict distinguishability of input
points. -/
theorem colip_positive_channel_preserves_distinguishability
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {K : CoeffMatrix I} (hK : K ∈ CoLipFamily d φ U)
    {i j : I} (hKpos : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdist : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hco := hK.2.2 x hx y hy j
  have hterm : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
    simpa using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : I => K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i))
  have hprod : 0 < K i j * d i x y :=
    pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hKpos) (ne_of_gt hdist))
  exact lt_of_lt_of_le hprod (le_trans hterm hco)

/-- The all-components zero-distance relation, with an index type universe
matching the chapter's arbitrary finite family. -/
def GaugeZero (d : I → X → X → ENNReal) (x y : X) : Prop :=
  ∀ i : I, d i x y = 0

/-- The universe-polymorphic zero-distance relation agrees with the frozen
Chapter 1 relation whenever both are applicable. -/
theorem gaugeZero_iff_gaugeZeroRelated {J : Type} {d : J → X → X → ENNReal}
    {x y : X} :
    GaugeZero d x y ↔ GaugeZeroRelated d x y :=
  Iff.rfl

/-- Strictly positive diagonal co-Lip entries reflect the gauge zero-distance
relation. -/
theorem colip_positive_diagonal_reflects_gauge_zero
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    {K : CoeffMatrix I} (hK : K ∈ CoLipFamily d φ U)
    (hdiag : ∀ j : I, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZero d (φ.func x) (φ.func y)) :
    GaugeZero d x y := by
  intro j
  by_cases hj : d j x y = 0
  · exact hj
  · have hjpos : 0 < d j x y := pos_iff_ne_zero.mpr hj
    have houtpos :=
      colip_positive_channel_preserves_distinguishability d φ hK (hdiag j) hx hy hjpos
    exact (ne_of_gt houtpos (hzero j)).elim

end Channels
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "HC02-D01",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.CoeffMatrix"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsLipOn"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.LipFamily"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.LipFamilyFull"}
      ],
      "representation": "CoeffMatrix I := I→I→ENNReal is input-first. IsLipOn requires U⊆dom φ and ∀x,y∈U,∀j, d j(φx)(φy)≤∑i L i j*d i x y. LipFamily is the legal certificate set; LipFamilyFull uses U=dom φ. I is finite and nonempty; all coefficients and distances are ENNReal.",
      "dependencies": []
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsCoLipOn"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.CoLipFamily"}
      ],
      "representation": "IsCoLipOn requires U.Nonempty, U⊆dom φ, and ∀x,y∈U,∀j, ∑i K i j*d i x y≤d j(φx)(φy). CoLipFamily is the legal lower-bound certificate set. Coefficients are arbitrary ENNReal values, so 0 and ∞ are allowed.",
      "dependencies": []
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.CoeffMatrix"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul_apply"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toOrdinaryMatrix"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toOrdinaryMatrix_apply"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.toOrdinaryMatrix_matMul"}
      ],
      "representation": "Storage M i j is input i to output j. matMul M2 M1 i j=∑k M2 k j*M1 i k. toOrdinaryMatrix places output j as row and input i as column; toOrdinaryMatrix_apply records row j,column i=M i j, and toOrdinaryMatrix_matMul proves ordinary matrix multiplication gives the chapter composite.",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matId"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matId_matMul"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matMul_matId"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_zero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_succ"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_one"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.opProd"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.opProd_zero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.opProd_succ"}
      ],
      "representation": "matId is δij with both unit laws. matProd 0=M identity, matProd(n+1) M=matMul(M last)(matProd n prefix), matProd_one gives the unique one-step matrix. opProd is the parallel ordered operator product with identity at zero and last operator on the left at a successor, matching Lk...L1.",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.stepInput"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.stepInput_zero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.stepInput_succ"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.stepInput_eq_opProd_image"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.stepInput_subset_dom_of_chain_dom"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_fin_chain"}
      ],
      "representation": "stepInput recursively defines U0=U and U(m+1)=φm(Um). stepInput_eq_opProd_image identifies Um with the prefix-composite image; stepInput_subset_dom_of_chain_dom proves Um⊆dom φm from U1⊆dom ck. lip_fin_chain builds the composite certificate only from step certificates on the actual input domains.",
      "dependencies": ["HC02-D01", "HC02-D04"]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathEdge"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.PathHasZero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.PathAllPositive"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_path_criteria"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathHasZero_one"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathAllPositive_one"}
      ],
      "representation": "A complete path is k:Fin(n+1)→I with k0=i, k(last)=j, so all intermediate sequences are quantified. pathEdge M k m=M m(k m)(k(m+1)) with no positivity restriction. PathHasZero says every complete path has a zero edge; PathAllPositive says some complete path has all edges positive. The n=1 lemmas reduce to the unique empty intermediate sequence and M 0 i j.",
      "dependencies": ["HC02-D03", "HC02-D04"]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.Channel"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.RowSupport"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.RowDecoupled"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ColumnSupport"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ColumnDecoupled"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsDiagonal"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.CompletelyDecoupled"}
      ],
      "representation": "Channel=I×I. RowSupport L i j means ∀k≠i,L k j=0 and RowDecoupled L j means ∃i,RowSupport L i j. ColumnSupport L i j means ∀k≠j,L i k=0 and ColumnDecoupled L i means ∃j,ColumnSupport L i j. IsDiagonal means ∀i≠j,L i j=0; CompletelyDecoupled names this diagonal certificate.",
      "dependencies": []
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ScalarFeasible"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConstant"}
      ],
      "representation": "ScalarFeasible d φ U i j={lam:ENNReal | ∀x,y∈U, d j(φx)(φy)≤lam*d i x y}; U⊆dom φ is an ambient side condition of channel statements. singleChannelLipConstant is sInf of that set, so the empty infimum is ∞. It is not identified with a matrix entry.",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_single_component"}
      ],
      "representation": "For [Unique I], any L∈LipFamily d φ U satisfies d j(φx)(φy)≤L j j*d j x y for x,y∈U: the finite sum collapses to its unique term.",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamilyFull_subset_lipFamily"}
      ],
      "representation": "If U⊆dom φ, then LipFamilyFull d φ⊆LipFamily d φ U: full-domain Lip certificates restrict to U.",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipFamily_mono"}
      ],
      "representation": "If U⊆V, then LipFamily d φ V⊆LipFamily d φ U: shrinking the evaluation domain enlarges the legal certificate family.",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipEntryInf"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipEntryInf_antitone"}
      ],
      "representation": "lipEntryInf d φ U i j=sInf{(L i j)|L∈LipFamily d φ U}. For U⊆V, lipEntryInf U i j≤lipEntryInf V i j.",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_comp"}
      ],
      "representation": "If U1⊆dom(φ2∘φ1), L1 is legal for φ1 on U1 and L2 is legal for φ2 on the actual image φ1(U1), then matMul L2 L1 is legal for φ2∘φ1 on U1. The proof applies the two pointwise Lip inequalities and swaps finite sums.",
      "dependencies": ["HC02-D01", "HC02-D03"]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_coeff_eq_zero_of_output_zero"}
      ],
      "representation": "If x,y∈dom φ, d j(φx)(φy)=0 and d i x y>0, then every global co-Lip K has K i j=0. This uses co-Lip lower boundedness, nonnegativity, and positivity of d i x y.",
      "dependencies": ["HC02-D02"]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_comp"}
      ],
      "representation": "With U2=φ1(U1), legal K1 and K2 give matMul K2 K1 legal for φ2∘φ1 on the nonempty U1; nonemptiness comes from K1.",
      "dependencies": ["HC02-D02", "HC02-D03"]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.PointwisePerturbation"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_forward"}
      ],
      "representation": "PointwisePerturbation records U⊆dom φ1∩dom φ2 and ∀z∈U,∀j,d j(φ1z)(φ2z)≤δj. perturbation_forward proves d j(φ2x)(φ2y)≤d j(φ1x)(φ1y)+δj+δj for x,y∈U.",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_backward"}
      ],
      "representation": "Under the same perturbation hypotheses, d j(φ1x)(φ1y)≤d j(φ2x)(φ2y)+δj+δj, by swapping φ1,φ2 in P08 and using symmetry.",
      "dependencies": ["HC02-P08"]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_lip_bound"}
      ],
      "representation": "If also L∈LipFamily d φ1 U, then d j(φ2x)(φ2y)≤(∑i L i j*d i x y)+δj+δj for x,y∈U.",
      "dependencies": ["HC02-D01", "HC02-P08"]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.perturbation_colip_bound"}
      ],
      "representation": "If also K∈CoLipFamily d φ1 U, then (∑i K i j*d i x y)≤d j(φ2x)(φ2y)+δj+δj.",
      "dependencies": ["HC02-D02", "HC02-P09"]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_fin_chain"}
      ],
      "representation": "For any length n, if every step L m is Lip on the actual domain stepInput φ U m, then matProd n L is Lip for opProd n φ on U. Only single-step certificates are assumed, not a final composite bound.",
      "dependencies": ["HC02-D05", "HC02-P05", "HC02-P14"]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_fin_chain"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_fin_chain_positive"}
      ],
      "representation": "colip_fin_chain gives the finite co-Lip product with nonempty U; colip_fin_chain_positive treats n≥1 and obtains nonemptiness from the first co-Lip step. It uses the same actual image domains as P12.",
      "dependencies": ["HC02-D02", "HC02-D05", "HC02-P07", "HC02-P15"]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matId_mem_lip_opId"}
      ],
      "representation": "For any U⊆dom(id_X), matId is legal Lip for opId on U, formalizing c0=id_X with empty matrix product matId.",
      "dependencies": ["HC02-D01", "HC02-D04"]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matId_mem_colip_opId"}
      ],
      "representation": "For nonempty U⊆dom(id_X), the same matId is legal co-Lip for opId on U, including U.Nonempty.",
      "dependencies": ["HC02-D02", "HC02-D04"]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_eq_zero_iff_all_paths_have_zero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_path_criteria"}
      ],
      "representation": "For n≥1, (matProd n M)i j=0 iff every complete path from i to j has some zero layer entry. pathHasZero_one is the n=1 reduction; matProd_path_criteria proves zero and positive criteria simultaneously.",
      "dependencies": ["HC02-D04", "HC02-D06"]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_pos_iff_exists_all_positive_path"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.matProd_path_criteria"}
      ],
      "representation": "For n≥1, 0<(matProd n M)i j iff some complete path from i to j has all layer entries strictly positive. At n=1 this is the unique empty sequence and M 0 i j>0.",
      "dependencies": ["HC02-D04", "HC02-D06"]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalarFeasible_eq_empty_of_zero_input_pos_output"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConstant_eq_top_of_zero_input_pos_output"}
      ],
      "representation": "If x,y∈U, d i x y=0 and 0<d j(φx)(φy), every scalar candidate gives output≤lam*0=0, so ScalarFeasible is empty and its infimum is ∞.",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConstant_mem_of_pos_lt_top"}
      ],
      "representation": "If a is the single-channel infimum, 0<a<∞, then a∈ScalarFeasible; the full pointwise scalar inequality holds at a. The proof constructs strict finite candidates above a and uses upward closure.",
      "dependencies": ["HC02-D08", "HC02-P21"]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalarFeasible_upward"}
      ],
      "representation": "If lam0 is feasible and lam0≤lam1, then lam1 is feasible; the feasible scalar family is upward closed.",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalarFeasible_of_gt_sInf"}
      ],
      "representation": "If a is the infimum, a<∞ and a<lam (including lam=∞), then lam is feasible. This covers the positive finite-infimum context and is slightly stronger.",
      "dependencies": ["HC02-D08", "HC02-P20"]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.scalarFeasible_of_sInf_eq_zero"}
      ],
      "representation": "If the infimum is 0, every lam with 0<lam<∞ is feasible. It does not claim that 0 itself is feasible.",
      "dependencies": ["HC02-D08", "HC02-P21"]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counterD"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counterGauge"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counterOp"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counterU"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counter_scalarFeasible_iff"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counter_singleChannelLipConstant_eq_zero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.counter_zero_not_mem"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.zero_infimum_not_attained_counterexample"}
      ],
      "representation": "On Fin 3 with bot=0, counterD is 0 on the diagonal and ∞ off it, and counterGauge proves all extended-pseudometric axioms. counterOp is the identity, counterU={1,2} is nonempty and lies in dom(identity). The feasible scalars are exactly {lam|0<lam}; the infimum is 0 but 0 is not feasible.",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.singleChannelLipConstant_lt_top_iff_exists_finite_feasible"}
      ],
      "representation": "For a=the single-channel infimum, a<∞ iff there is some lam<∞ in ScalarFeasible. The forward direction uses a+1 and P21; the reverse uses sInf≤lam.",
      "dependencies": ["HC02-D08", "HC02-P21"]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.term_eq_zero_of_coeff_zero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_erase_of_coeff_zero"}
      ],
      "representation": "If L i j=0, the term L i j*d i x y is 0 with no finiteness restriction on d i x y, and the output sum equals the same sum over univ\\{i}; the input-i term is removed.",
      "dependencies": []
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_bound_of_row_support"}
      ],
      "representation": "If L∈LipFamily and RowSupport L i j, then d j(φx)(φy)≤L i j*d i x y for x,y∈U; the unique input i need not equal j.",
      "dependencies": ["HC02-D01", "HC02-D07"]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.column_support_term_zero"}
      ],
      "representation": "If ColumnSupport L i j, then every k≠j satisfies L i k*d i x y=0; in this upper-bound certificate input i contributes only to output j.",
      "dependencies": ["HC02-D07"]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_diagonal_bound"}
      ],
      "representation": "A diagonal L∈LipFamily gives, for every j and x,y∈U, d j(φx)(φy)≤L j j*d j x y; this is the row-support theorem with i=j.",
      "dependencies": ["HC02-D01", "HC02-D07"]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.bilateral_bound_of_lip_row"}
      ],
      "representation": "For L∈LipFamily and K∈CoLipFamily on the same U, the sole row hypothesis ∀k≠j,L k j=0 yields K j j*d j x y≤d j(φx)(φy)≤L j j*d j x y. No analogous sparsity is required of K.",
      "dependencies": ["HC02-D01", "HC02-D02", "HC02-D07"]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.all_components_bilateral_bounds"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.all_components_finite_bilateral_bounds"}
      ],
      "representation": "If the P29 Lip diagonal-row condition holds for all j, all componentwise two-sided bounds hold. The finite version additionally assumes L j j<∞ and K j j<∞ and returns the bounds together with those finiteness assertions.",
      "dependencies": ["HC02-P29", "HC02-D07"]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_positive_channel_preserves_distinguishability"}
      ],
      "representation": "If K∈CoLipFamily and K i j>0, then x,y∈U and d i x y>0 imply d j(φx)(φy)>0; the co-Lip sum is lower-bounded by the positive term K i j*d i x y.",
      "dependencies": ["HC02-D02", "HC02-D07"]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.GaugeZero"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.gaugeZero_iff_gaugeZeroRelated"},
        {"file": "Main.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.colip_positive_diagonal_reflects_gauge_zero"}
      ],
      "representation": "GaugeZero means ∀i,d i x y=0 and gaugeZero_iff_gaugeZeroRelated identifies it with the frozen Chapter 1 relation. If K is co-Lip and every diagonal K j j>0, then GaugeZero d(φx)(φy) implies GaugeZero d x y for x,y∈U, using P31 componentwise.",
      "dependencies": ["HC02-D02", "HC02-D07", "HC02-P31"]
    }
  ]
}
```

完成情况：40/40 个义务均标记为 `complete`，未保留 `sorry`、`admit`、自定义公理或跳过内核检查的设施。本地已成功编译 `Main.lean`，并验证 `alignment.json` 恰好覆盖 `HC02-D01`–`HC02-D08` 与 `HC02-P01`–`HC02-P32`。

未完成或未确认范围：无。唯一需要说明的表示选择是：原文 `ScalarFeasible` 定义外部的 `U ⊆ dom φ` 语境在 Lean 中由相应通道定理的前提承担，而不是作为该集合定义本身的字段；这不改变原文的量词或结论。