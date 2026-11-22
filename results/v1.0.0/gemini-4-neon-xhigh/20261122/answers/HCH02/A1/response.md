以下为第 2 章历史冻结原文（`source/02-operator-bounds.md`，来源：Zhe Li / Glen Li / glenzli, *The Operator Evolution Theory*, https://glenzli.com/books/oet/, CC BY 4.0）及 `obligations.json` 全部 40 项义务的完整 Lean 4.29.1 形式化交付。

```lean filename=Ch02/MatrixCore.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# Chapter 2 Core Representations: Matrices, Operator Chains, and Index Paths

Formalizes the core algebraic and combinatorial representations for Chapter 2
(`02-operator-bounds.md`):
- Input-first gauge matrices `M i j` (input `i` to output `j`), their display
  transposition to ordinary row-by-column `Matrix I I ENNReal` (row `j`, col `i`),
  and composition multiplication `(M2 · M1)_{i → j} = ∑ k, M2_{k → j} * M1_{i → k}`.
- Identity matrix, empty matrix product, and ordered finite products matching
  application order `ϕ₁, …, ϕₖ ↦ Lₖ · … · L₁`.
- Operator composition, finite operator chains (linked to Chapter 1's `OperatorChain`),
  and recursively defined actual intermediate image domains `U_{m+1} = ϕₘ(Uₘ)`.
- Finite index paths with fixed endpoints `k₀ = i`, `kₙ = j`, unrestricted intermediate
  sequences `(k₁, …, k_{n-1})`, path weights, all-positive and has-zero predicates,
  and the exact path-sum expansion of finite matrix products.
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Gauge Matrices, Display Convention, and Multiplication (HC02-D03) -/

/-- Input-first matrix over `ENNReal`: `M i j` denotes entry `M_{i → j}` from input
component `i` to output component `j`. -/
abbrev GaugeMatrix (I : Type) : Type := I → I → ENNReal

/-- Display representation as a standard `Matrix I I ENNReal` where output index `j`
labels rows and input index `i` labels columns: `(toDisplayMatrix M) j i = M i j`. -/
def toDisplayMatrix {I : Type} (M : GaugeMatrix I) : Matrix I I ENNReal :=
  fun j i => M i j

/-- Inverse conversion from a standard row-by-column matrix (`j`-th row, `i`-th column)
to input-first storage `M_{i → j}`. -/
def ofDisplayMatrix {I : Type} (A : Matrix I I ENNReal) : GaugeMatrix I :=
  fun i j => A j i

@[simp]
theorem toDisplayMatrix_apply {I : Type} (M : GaugeMatrix I) (j i : I) :
    toDisplayMatrix M j i = M i j :=
  rfl

@[simp]
theorem ofDisplayMatrix_apply {I : Type} (A : Matrix I I ENNReal) (i j : I) :
    ofDisplayMatrix A i j = A j i :=
  rfl

/-- Equivalence between input-first `GaugeMatrix I` and display `Matrix I I ENNReal`. -/
def toDisplayMatrixEquiv (I : Type) : GaugeMatrix I ≃ Matrix I I ENNReal where
  toFun := toDisplayMatrix
  invFun := ofDisplayMatrix
  left_inv _ := rfl
  right_inv _ := rfl

/-- Composition multiplication of gauge matrices:
`(matMul M2 M1) i j = ∑ k : I, M2 k j * M1 i k`, corresponding to `(M2 · M1)_{i → j}`. -/
noncomputable def matMul {I : Type} [Fintype I] (M2 M1 : GaugeMatrix I) : GaugeMatrix I :=
  fun i j => ∑ k : I, M2 k j * M1 i k

@[simp]
theorem matMul_apply {I : Type} [Fintype I] (M2 M1 : GaugeMatrix I) (i j : I) :
    matMul M2 M1 i j = ∑ k : I, M2 k j * M1 i k :=
  rfl

/-- Composition multiplication matches ordinary matrix multiplication in display
representation (output index `j` as row, input index `i` as column). -/
theorem toDisplayMatrix_matMul {I : Type} [Fintype I] (M2 M1 : GaugeMatrix I) :
    toDisplayMatrix (matMul M2 M1) = toDisplayMatrix M2 * toDisplayMatrix M1 := by
  ext j i
  simp [toDisplayMatrix, matMul, Matrix.mul_apply]

/-- Gauge matrix multiplication is associative. -/
theorem matMul_assoc {I : Type} [Fintype I] (M3 M2 M1 : GaugeMatrix I) :
    matMul (matMul M3 M2) M1 = matMul M3 (matMul M2 M1) := by
  funext i j
  simp only [matMul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-! ### 2. Identity Matrix, Empty Product, and Ordered Finite Products (HC02-D04) -/

/-- Identity gauge matrix `δ_{i → j}` (1 on the diagonal, 0 off-diagonal). -/
noncomputable def idMatrix {I : Type} : GaugeMatrix I :=
  fun i j => by
    classical
    exact if i = j then 1 else 0

@[simp]
theorem idMatrix_apply_eq {I : Type} (i : I) : idMatrix i i = 1 := by
  unfold idMatrix
  simp

theorem idMatrix_apply_ne {I : Type} {i j : I} (h : i ≠ j) : idMatrix i j = 0 := by
  unfold idMatrix
  simp [h]

theorem toDisplayMatrix_idMatrix {I : Type} [DecidableEq I] :
    toDisplayMatrix (idMatrix (I := I)) = (1 : Matrix I I ENNReal) := by
  ext j i
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := Ne.symm h
    simp [toDisplayMatrix, idMatrix_apply_ne h, h']

@[simp]
theorem matMul_idMatrix {I : Type} [Fintype I] (M : GaugeMatrix I) :
    matMul M idMatrix = M := by
  funext i j
  simp only [matMul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    rw [idMatrix_apply_ne hki.symm, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

@[simp]
theorem idMatrix_matMul {I : Type} [Fintype I] (M : GaugeMatrix I) :
    matMul idMatrix M = M := by
  funext i j
  simp only [matMul_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [idMatrix_apply_ne hkj, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Ordered finite product of a list of gauge matrices given in operator application
order `[M₁, …, Mₖ]`, producing `Mₖ · … · M₁`. Empty list yields `idMatrix`;
singleton `[M]` yields `M`. -/
noncomputable def matProd {I : Type} [Fintype I] : List (GaugeMatrix I) → GaugeMatrix I
  | [] => idMatrix
  | [M] => M
  | M :: M' :: Ms => matMul (matProd (M' :: Ms)) M

@[simp]
theorem matProd_nil {I : Type} [Fintype I] :
    matProd ([] : List (GaugeMatrix I)) = idMatrix :=
  rfl

@[simp]
theorem matProd_singleton {I : Type} [Fintype I] (M : GaugeMatrix I) :
    matProd [M] = M :=
  rfl

theorem matProd_cons {I : Type} [Fintype I] (M : GaugeMatrix I) (Ms : List (GaugeMatrix I)) :
    matProd (M :: Ms) = matMul (matProd Ms) M := by
  cases Ms with
  | nil => simp [matProd]
  | cons M' Ms' => rfl

@[simp]
theorem matProd_two {I : Type} [Fintype I] (M1 M2 : GaugeMatrix I) :
    matProd [M1, M2] = matMul M2 M1 :=
  rfl

theorem matProd_append {I : Type} [Fintype I] (Ms1 Ms2 : List (GaugeMatrix I)) :
    matProd (Ms1 ++ Ms2) = matMul (matProd Ms2) (matProd Ms1) := by
  induction Ms1 with
  | nil => simp
  | cons M Ms ih =>
      simp only [List.cons_append, matProd_cons, ih, matMul_assoc]

theorem matProd_snoc {I : Type} [Fintype I] (Ms : List (GaugeMatrix I)) (M : GaugeMatrix I) :
    matProd (Ms ++ [M]) = matMul M (matProd Ms) := by
  rw [matProd_append, matProd_singleton]

/-- Ordered product in input-first storage corresponds to reversed-list product of
standard display matrices (`[M₁, …, Mₖ] ↦ Mₖ · … · M₁`). -/
theorem toDisplayMatrix_matProd {I : Type} [Fintype I] [DecidableEq I]
    (Ms : List (GaugeMatrix I)) :
    toDisplayMatrix (matProd Ms) = (Ms.reverse.map toDisplayMatrix).prod := by
  induction Ms using List.reverseRecOn with
  | nil =>
      simp [toDisplayMatrix_idMatrix]
  | append_singleton Ms M ih =>
      rw [matProd_snoc, toDisplayMatrix_matMul, ih, List.reverse_append]
      simp

/-- Ordered finite product of a `Fin k`-indexed sequence of gauge matrices in
application order `M 0, M 1, …, M (k - 1)`, yielding `M (k - 1) · … · M 0`. -/
noncomputable def finMatProd {I : Type} [Fintype I] {k : ℕ} (M : Fin k → GaugeMatrix I) :
    GaugeMatrix I :=
  matProd (List.ofFn M)

@[simp]
theorem finMatProd_zero {I : Type} [Fintype I] (M : Fin 0 → GaugeMatrix I) :
    finMatProd M = idMatrix := by
  simp [finMatProd]

@[simp]
theorem finMatProd_one {I : Type} [Fintype I] (M : Fin 1 → GaugeMatrix I) :
    finMatProd M = M 0 := by
  simp [finMatProd]

theorem finMatProd_two {I : Type} [Fintype I] (M : Fin 2 → GaugeMatrix I) :
    finMatProd M = matMul (M 1) (M 0) := by
  simp [finMatProd, List.ofFn_succ]

theorem finMatProd_succ_head {I : Type} [Fintype I] {k : ℕ} (M : Fin (k + 1) → GaugeMatrix I) :
    finMatProd M = matMul (finMatProd (fun t : Fin k => M t.succ)) (M 0) := by
  rw [finMatProd, List.ofFn_succ, matProd_cons]
  rfl

theorem finMatProd_succ_last {I : Type} [Fintype I] {k : ℕ} (M : Fin (k + 1) → GaugeMatrix I) :
    finMatProd M = matMul (M (Fin.last k)) (finMatProd (fun t : Fin k => M t.castSucc)) := by
  rw [finMatProd, List.ofFn_succ', List.concat_eq_append, matProd_snoc]
  rfl

/-! ### 3. Operator Composition, Finite Chains, and Recursive Image Domains (HC02-D05) -/

/-- Identity operator `id_X ∈ X_op`. -/
def idOp {X : Type} {bot : X} : Operator X bot :=
  ⟨id, rfl⟩

/-- Binary composition `ϕ₂ ∘ ϕ₁ ∈ X_op`. -/
def compOp {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) : Operator X bot :=
  ⟨ϕ2.func ∘ ϕ1.func, by simp [ϕ1.preserves_bot, ϕ2.preserves_bot]⟩

/-- Common domain `dom(ϕ₁, ϕ₂) = dom(ϕ₁) ∩ dom(ϕ₂)`. -/
def commonDom2 {X : Type} {bot : X} (ϕ1 ϕ2 : Operator X bot) : Set X :=
  dom ϕ1 ∩ dom ϕ2

@[simp]
theorem idOp_func {X : Type} {bot : X} (x : X) : (idOp (bot := bot)).func x = x :=
  rfl

@[simp]
theorem compOp_func {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) (x : X) :
    (compOp ϕ2 ϕ1).func x = ϕ2.func (ϕ1.func x) :=
  rfl

@[simp]
theorem compOp_idOp {X : Type} {bot : X} (ϕ : Operator X bot) : compOp ϕ idOp = ϕ := by
  ext x
  rfl

@[simp]
theorem idOp_compOp {X : Type} {bot : X} (ϕ : Operator X bot) : compOp idOp ϕ = ϕ := by
  ext x
  rfl

theorem compOp_assoc {X : Type} {bot : X} (ϕ3 ϕ2 ϕ1 : Operator X bot) :
    compOp (compOp ϕ3 ϕ2) ϕ1 = compOp ϕ3 (compOp ϕ2 ϕ1) := by
  ext x
  rfl

/-- `dom(ϕ₂ ∘ ϕ₁) ⊆ dom(ϕ₁)`, using `ϕ₂(⊥) = ⊥`. -/
theorem dom_compOp_subset_left {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) :
    dom (compOp ϕ2 ϕ1) ⊆ dom ϕ1 := by
  intro x hx h1
  apply hx
  simp [compOp, h1, ϕ2.preserves_bot]

/-- If `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)`, then the actual image `U₂ = ϕ₁(U₁)` lies in `dom(ϕ₂)`. -/
theorem operator_image_subset_dom_of_subset_dom_compOp {X : Type} {bot : X}
    (ϕ2 ϕ1 : Operator X bot) {U1 : Set X} (hU1 : U1 ⊆ dom (compOp ϕ2 ϕ1)) :
    operator_image ϕ1 U1 ⊆ dom ϕ2 := by
  rintro y ⟨x, hx, rfl⟩
  exact hU1 hx

/-- Image of a composite equals successive images: `(ϕ₂ ∘ ϕ₁)(U) = ϕ₂(ϕ₁(U))`. -/
theorem operator_image_compOp {X : Type} {bot : X} (ϕ2 ϕ1 : Operator X bot) (U : Set X) :
    operator_image (compOp ϕ2 ϕ1) U = operator_image ϕ2 (operator_image ϕ1 U) := by
  unfold operator_image compOp
  exact Set.image_comp ϕ2.func ϕ1.func U

/-- Finite operator composition from a list in application order `[ϕ₁, …, ϕₖ]`,
producing `cₖ = ϕₖ ∘ … ∘ ϕ₁` with `c₀ = id_X`. -/
def applyChain {X : Type} {bot : X} : List (Operator X bot) → Operator X bot
  | [] => idOp
  | ϕ :: ϕs => compOp (applyChain ϕs) ϕ

@[simp]
theorem applyChain_nil {X : Type} {bot : X} :
    applyChain ([] : List (Operator X bot)) = idOp :=
  rfl

@[simp]
theorem applyChain_cons {X : Type} {bot : X} (ϕ : Operator X bot) (ϕs : List (Operator X bot)) :
    applyChain (ϕ :: ϕs) = compOp (applyChain ϕs) ϕ :=
  rfl

@[simp]
theorem applyChain_singleton {X : Type} {bot : X} (ϕ : Operator X bot) :
    applyChain [ϕ] = ϕ := by
  simp

theorem applyChain_two {X : Type} {bot : X} (ϕ1 ϕ2 : Operator X bot) :
    applyChain [ϕ1, ϕ2] = compOp ϕ2 ϕ1 := by
  simp

theorem applyChain_append {X : Type} {bot : X} (ϕs1 ϕs2 : List (Operator X bot)) :
    applyChain (ϕs1 ++ ϕs2) = compOp (applyChain ϕs2) (applyChain ϕs1) := by
  induction ϕs1 with
  | nil => simp
  | cons ϕ ϕs ih =>
      simp [ih, compOp_assoc]

theorem applyChain_snoc {X : Type} {bot : X} (ϕs : List (Operator X bot)) (ϕ : Operator X bot) :
    applyChain (ϕs ++ [ϕ]) = compOp ϕ (applyChain ϕs) := by
  rw [applyChain_append, applyChain_singleton]

/-- Equivalence with Chapter 1's `OperatorChain` (which composes head-outermost):
applying `[ϕ₁, …, ϕₖ]` equals `OperatorChain [ϕₖ, …, ϕ₁]`. -/
theorem applyChain_eq_operatorChain_reverse {X : Type} {bot : X} (ϕs : List (Operator X bot)) :
    applyChain ϕs = OperatorChain ϕs.reverse := by
  induction ϕs using List.reverseRecOn with
  | nil =>
      ext x
      rfl
  | append_singleton ϕs ϕ ih =>
      rw [applyChain_snoc, ih, List.reverse_append]
      ext x
      rfl

/-- Finite operator composition `cₖ = ϕₖ ∘ … ∘ ϕ₁` for a `Fin k`-indexed family in
application order `ϕ 0, ϕ 1, …, ϕ (k - 1)`. -/
def finChainOp {X : Type} {bot : X} {k : ℕ} (ϕ : Fin k → Operator X bot) : Operator X bot :=
  applyChain (List.ofFn ϕ)

@[simp]
theorem finChainOp_zero {X : Type} {bot : X} (ϕ : Fin 0 → Operator X bot) :
    finChainOp ϕ = idOp := by
  simp [finChainOp]

@[simp]
theorem finChainOp_one {X : Type} {bot : X} (ϕ : Fin 1 → Operator X bot) :
    finChainOp ϕ = ϕ 0 := by
  simp [finChainOp]

theorem finChainOp_two {X : Type} {bot : X} (ϕ : Fin 2 → Operator X bot) :
    finChainOp ϕ = compOp (ϕ 1) (ϕ 0) := by
  simp [finChainOp, List.ofFn_succ]

theorem finChainOp_succ_head {X : Type} {bot : X} {k : ℕ} (ϕ : Fin (k + 1) → Operator X bot) :
    finChainOp ϕ = compOp (finChainOp (fun t : Fin k => ϕ t.succ)) (ϕ 0) := by
  rw [finChainOp, List.ofFn_succ, applyChain_cons]
  rfl

theorem finChainOp_succ_last {X : Type} {bot : X} {k : ℕ} (ϕ : Fin (k + 1) → Operator X bot) :
    finChainOp ϕ = compOp (ϕ (Fin.last k)) (finChainOp (fun t : Fin k => ϕ t.castSucc)) := by
  rw [finChainOp, List.ofFn_succ', List.concat_eq_append, applyChain_snoc]
  rfl

/-- Structural helper defining recursive intermediate actual domains along a chain. -/
private def chainDomainAux {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U1 : Set X) : (r : ℕ) → r ≤ k → Set X
  | 0, _ => U1
  | r + 1, hr =>
      operator_image (ϕ ⟨r, hr⟩) (chainDomainAux ϕ U1 r (Nat.le_of_succ_le hr))

/-- Recursively defined actual intermediate domains along a finite chain:
`chainDomain ϕ U1 0 = U₁` and `chainDomain ϕ U1 (m + 1) = ϕₘ(Uₘ)`. -/
def chainDomain {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U1 : Set X) (m : Fin (k + 1)) : Set X :=
  chainDomainAux ϕ U1 m.val (Nat.le_of_lt_succ m.isLt)

@[simp]
theorem chainDomain_zero {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U1 : Set X) :
    chainDomain ϕ U1 0 = U1 :=
  rfl

theorem chainDomain_succ {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U1 : Set X) (m : Fin k) :
    chainDomain ϕ U1 m.succ = operator_image (ϕ m) (chainDomain ϕ U1 m.castSucc) :=
  rfl

/-- Prefix invariance of `chainDomain`: dropping the final step preserves all earlier
intermediate domains `U₁, …, U_{k+1}`. -/
theorem chainDomain_prefix {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin (k + 1) → Operator X bot) (U1 : Set X) (m : Fin (k + 1)) :
    chainDomain (fun t : Fin k => ϕ t.castSucc) U1 m = chainDomain ϕ U1 m.castSucc := by
  rcases m with ⟨r, hr⟩
  induction r with
  | zero => rfl
  | succ r ih =>
      have hr' : r < k + 1 := Nat.lt_of_succ_lt hr
      change operator_image (ϕ ⟨r, Nat.lt_trans (Nat.lt_of_succ_lt_succ hr) (Nat.lt_succ_self k)⟩)
          (chainDomain (fun t : Fin k => ϕ t.castSucc) U1 ⟨r, hr'⟩) =
        operator_image (ϕ ⟨r, Nat.lt_trans (Nat.lt_of_succ_lt_succ hr) (Nat.lt_succ_self k)⟩)
          (chainDomain ϕ U1 ⟨r, Nat.lt_trans hr' (Nat.lt_succ_self (k + 1))⟩)
      rw [ih hr']
      rfl

/-- The final recursive image equals the full composite image: `U_{k+1} = cₖ(U₁)`. -/
theorem chainDomain_last_eq_operator_image {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) (U1 : Set X) :
    chainDomain ϕ U1 (Fin.last k) = operator_image (finChainOp ϕ) U1 := by
  induction k with
  | zero =>
      simp [finChainOp, operator_image, idOp]
  | succ k ih =>
      rw [show Fin.last (k + 1) = (Fin.last k).succ by ext; simp]
      rw [chainDomain_succ]
      rw [← chainDomain_prefix ϕ U1 (Fin.last k)]
      rw [ih (fun t : Fin k => ϕ t.castSucc)]
      rw [finChainOp_succ_last, operator_image_compOp]

/-- Starting from `U₁ ⊆ dom(cₖ)`, every intermediate actual domain satisfies
`Uₘ ⊆ dom(ϕₘ)`. -/
theorem chainDomain_subset_dom {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) {U1 : Set X} (hU1 : U1 ⊆ dom (finChainOp ϕ)) :
    ∀ m : Fin k, chainDomain ϕ U1 m.castSucc ⊆ dom (ϕ m) := by
  induction k with
  | zero =>
      intro m
      exact Fin.elim0 m
  | succ k ih =>
      let ϕ' : Fin k → Operator X bot := fun t => ϕ t.castSucc
      have hcomp : finChainOp ϕ = compOp (ϕ (Fin.last k)) (finChainOp ϕ') :=
        finChainOp_succ_last ϕ
      have hU1_comp : U1 ⊆ dom (compOp (ϕ (Fin.last k)) (finChainOp ϕ')) := by
        simpa [hcomp] using hU1
      have hU1_pref : U1 ⊆ dom (finChainOp ϕ') :=
        Set.Subset.trans hU1_comp (dom_compOp_subset_left _ _)
      intro m
      refine Fin.lastCases ?_ ?_ m
      · rw [← chainDomain_prefix ϕ U1 (Fin.last k), chainDomain_last_eq_operator_image]
        exact operator_image_subset_dom_of_subset_dom_compOp _ _ hU1_comp
      · intro t
        rw [← chainDomain_prefix ϕ U1 t.castSucc]
        exact ih ϕ' hU1_pref t

/-- Nonemptiness propagates along all intermediate actual domains `Uₘ`. -/
theorem chainDomain_nonempty {X : Type} {bot : X} {k : ℕ}
    (ϕ : Fin k → Operator X bot) {U1 : Set X} (hU1 : U1.Nonempty) (m : Fin (k + 1)) :
    (chainDomain ϕ U1 m).Nonempty := by
  rcases m with ⟨r, hr⟩
  induction r with
  | zero => exact hU1
  | succ r ih =>
      have hr' : r < k + 1 := Nat.lt_of_succ_lt hr
      exact (ih hr').image _

/-! ### 4. Finite Index Paths and Exact Matrix-Product Expansion (HC02-D06) -/

/-- All unrestricted intermediate index sequences `(k₁, …, k_{n-1})` for a chain of
length `n ≥ 1`. When `n = 1`, `Fin 0 → I` has a unique empty sequence. -/
abbrev MidIndexSeq (I : Type) (n : ℕ) : Type := Fin (n - 1) → I

/-- When `n = 1`, there is a unique empty intermediate index sequence. -/
@[implicit_reducible]
def midIndexSeqOneUnique (I : Type) : Unique (MidIndexSeq I 1) where
  default := Fin.elim0
  uniq f := by
    funext t
    exact Fin.elim0 t

/-- Augmented node sequence `(k₀, k₁, …, kₙ)` with fixed endpoints `k₀ = i` and `kₙ = j`
and intermediate indices given by `mid : MidIndexSeq I n`. -/
def pathNode {I : Type} (n : ℕ) (i j : I) (mid : MidIndexSeq I n) (t : Fin (n + 1)) : I :=
  if h0 : t.val = 0 then
    i
  else if h : t.val < n then
    mid ⟨t.val - 1, by omega⟩
  else
    j

@[simp]
theorem pathNode_zero {I : Type} (n : ℕ) (i j : I) (mid : MidIndexSeq I n) :
    pathNode n i j mid 0 = i := by
  simp [pathNode]

theorem pathNode_last {I : Type} (n : ℕ) (hn : 1 ≤ n) (i j : I) (mid : MidIndexSeq I n) :
    pathNode n i j mid (Fin.last n) = j := by
  unfold pathNode
  have h0 : n ≠ 0 := by omega
  simp [h0]

theorem pathNode_mid {I : Type} (n : ℕ) (i j : I) (mid : MidIndexSeq I n) (r : Fin (n - 1)) :
    pathNode n i j mid ⟨r.val + 1, by omega⟩ = mid r := by
  unfold pathNode
  have hlt : r.val + 1 < n := by omega
  simp [hlt]

/-- Single-step matrix entry `M^{(m)}_{k_{m-1} → k_m}` along step `m : Fin n` of a path. -/
def pathEdgeWeight {I : Type} (n : ℕ) (M : Fin n → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I n) (m : Fin n) : ENNReal :=
  M m (pathNode n i j mid m.castSucc) (pathNode n i j mid m.succ)

/-- Total multiplicative weight of a path across all `n` layers. -/
noncomputable def pathWeight {I : Type} (n : ℕ) (M : Fin n → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I n) : ENNReal :=
  ∏ m : Fin n, pathEdgeWeight n M i j mid m

/-- Predicate asserting that every step entry along the path is strictly positive. -/
def PathAllPos {I : Type} (n : ℕ) (M : Fin n → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I n) : Prop :=
  ∀ m : Fin n, 0 < pathEdgeWeight n M i j mid m

/-- Predicate asserting that at least one step entry along the path equals zero. -/
def PathHasZero {I : Type} (n : ℕ) (M : Fin n → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I n) : Prop :=
  ∃ m : Fin n, pathEdgeWeight n M i j mid m = 0

/-- For `n = 1`, the unique empty intermediate sequence has edge weight `M 0 i j`. -/
@[simp]
theorem pathEdgeWeight_one {I : Type} (M : Fin 1 → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I 1) (m : Fin 1) :
    pathEdgeWeight 1 M i j mid m = M 0 i j := by
  fin_cases m
  simp [pathEdgeWeight, pathNode]

/-- For `n = 1`, the unique empty intermediate sequence has path weight `M 0 i j`. -/
@[simp]
theorem pathWeight_one {I : Type} (M : Fin 1 → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I 1) :
    pathWeight 1 M i j mid = M 0 i j := by
  simp [pathWeight]

/-- A finite product of `ENNReal` values equals `0` iff some factor equals `0`. -/
theorem finset_prod_eq_zero_iff_ennreal {α : Type*} (s : Finset α) (f : α → ENNReal) :
    (∏ a ∈ s, f a) = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, mul_eq_zero, ih]
      simp

/-- A path's multiplicative weight is `0` iff at least one step entry is `0`. -/
theorem pathWeight_eq_zero_iff {I : Type} (n : ℕ) (M : Fin n → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I n) :
    pathWeight n M i j mid = 0 ↔ PathHasZero n M i j mid := by
  unfold pathWeight PathHasZero
  rw [finset_prod_eq_zero_iff_ennreal]
  simp

/-- A path's multiplicative weight is strictly positive iff every step entry is strictly
positive. -/
theorem pathWeight_pos_iff {I : Type} (n : ℕ) (M : Fin n → GaugeMatrix I) (i j : I)
    (mid : MidIndexSeq I n) :
    0 < pathWeight n M i j mid ↔ PathAllPos n M i j mid := by
  rw [pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff]
  unfold PathHasZero PathAllPos
  push Not
  simp [pos_iff_ne_zero]

/-- Equivalence splitting an intermediate sequence of length `n` (`n ≥ 1`) into its
prefix of length `n - 1` and its last element `kₙ`. -/
private def midIndexSeqSplitEquiv (I : Type) (n : ℕ) (hn : 1 ≤ n) :
    MidIndexSeq I (n + 1) ≃ I × MidIndexSeq I n where
  toFun mid :=
    (mid ⟨n - 1, by omega⟩, fun r : Fin (n - 1) => mid ⟨r.val, by omega⟩)
  invFun p r :=
    if h : r.val < n - 1 then
      p.2 ⟨r.val, h⟩
    else
      p.1
  left_inv mid := by
    funext r
    by_cases h : r.val < n - 1
    · simp [h]
    · have hr : r.val = n - 1 := by omega
      simp only [h, ↓reduceDIte]
      congr 1
      ext
      exact hr.symm
  right_inv p := by
    rcases p with ⟨k, mid'⟩
    ext
    · simp
    · rename_i r
      simp [r.isLt]

private theorem pathNode_split_castSucc {I : Type} (n : ℕ) (hn : 1 ≤ n)
    (i j k : I) (mid' : MidIndexSeq I n) (t : Fin (n + 1)) :
    pathNode (n + 1) i j ((midIndexSeqSplitEquiv I n hn).symm (k, mid')) t.castSucc =
      pathNode n i k mid' t := by
  unfold pathNode midIndexSeqSplitEquiv
  by_cases h0 : t.val = 0
  · simp [h0]
  · by_cases hlt : t.val < n
    · have hlt1 : t.val < n + 1 := Nat.lt_trans hlt (Nat.lt_succ_self n)
      have hsub : t.val - 1 < n - 1 := by omega
      simp [h0, hlt, hlt1, hsub]
    · have ht : t.val = n := by omega
      have hlt1 : t.val < n + 1 := by omega
      have hsub : ¬ t.val - 1 < n - 1 := by omega
      simp [h0, hlt, hlt1, hsub]

/-- Exact path-sum expansion of an ordered finite matrix product for all `n ≥ 1`. -/
theorem finMatProd_apply_eq_sum_paths {I : Type} [Fintype I] :
    ∀ (n : ℕ), 1 ≤ n → ∀ (M : Fin n → GaugeMatrix I) (i j : I),
      finMatProd M i j = ∑ mid : MidIndexSeq I n, pathWeight n M i j mid
  | 0, hn, _, _, _ => absurd hn (by decide)
  | 1, _, M, i, j => by
      haveI : Unique (MidIndexSeq I 1) := midIndexSeqOneUnique I
      rw [finMatProd_one, Fintype.sum_unique, pathWeight_one]
  | n + 2, _, M, i, j => by
      have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      let M' : Fin (n + 1) → GaugeMatrix I := fun t => M t.castSucc
      have ih := finMatProd_apply_eq_sum_paths (n + 1) hn M'
      rw [finMatProd_succ_last, matMul_apply]
      calc
        ∑ k : I, M (Fin.last (n + 1)) k j * finMatProd M' i k
            = ∑ k : I, M (Fin.last (n + 1)) k j *
                (∑ mid' : MidIndexSeq I (n + 1), pathWeight (n + 1) M' i k mid') := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [ih i k]
        _ = ∑ k : I, ∑ mid' : MidIndexSeq I (n + 1),
              M (Fin.last (n + 1)) k j * pathWeight (n + 1) M' i k mid' := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [Finset.mul_sum]
        _ = ∑ p : I × MidIndexSeq I (n + 1),
              M (Fin.last (n + 1)) p.1 j * pathWeight (n + 1) M' i p.1 p.2 := by
              rw [Fintype.sum_prod_type]
        _ = ∑ mid : MidIndexSeq I (n + 2), pathWeight (n + 2) M i j mid := by
              refine Fintype.sum_equiv (midIndexSeqSplitEquiv I (n + 1) hn).symm _ _ ?_
              rintro ⟨k, mid'⟩
              let mid := (midIndexSeqSplitEquiv I (n + 1) hn).symm (k, mid')
              change M (Fin.last (n + 1)) k j * pathWeight (n + 1) M' i k mid' =
                pathWeight (n + 2) M i j mid
              rw [show pathWeight (n + 2) M i j mid =
                  (∏ m : Fin (n + 1), pathEdgeWeight (n + 2) M i j mid m.castSucc) *
                    pathEdgeWeight (n + 2) M i j mid (Fin.last (n + 1)) from
                Fin.prod_univ_castSucc (fun m : Fin (n + 2) => pathEdgeWeight (n + 2) M i j mid m)]
              rw [mul_comm]
              congr 1
              · unfold pathWeight
                refine Finset.prod_congr rfl ?_
                intro m _
                unfold pathEdgeWeight
                have h1 := pathNode_split_castSucc (n + 1) hn i j k mid' m.castSucc
                have h2 := pathNode_split_castSucc (n + 1) hn i j k mid' m.succ
                have hc1 : (m.castSucc : Fin (n + 2)).castSucc = m.castSucc.castSucc := rfl
                have hc2 : (m.succ : Fin (n + 2)).castSucc = m.castSucc.succ := by
                  ext; simp
                rw [hc1] at h1
                rw [hc2] at h2
                simp only [M', mid, h1, h2]
              · unfold pathEdgeWeight
                have h1 := pathNode_split_castSucc (n + 1) hn i j k mid' (Fin.last (n + 1))
                have hlast1 : pathNode (n + 1) i k mid' (Fin.last (n + 1)) = k :=
                  pathNode_last (n + 1) hn i k mid'
                have hlast2 : pathNode (n + 2) i j mid (Fin.last (n + 2)) = j :=
                  pathNode_last (n + 2) (by omega) i j mid
                have hsucc : (Fin.last (n + 1) : Fin (n + 2)).succ = Fin.last (n + 2) := by
                  ext; simp
                rw [hlast1] at h1
                simp only [mid, h1, hsucc, hlast2]

end OetCh02
```

```lean filename=Ch02/MatrixBounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02.MatrixCore

/-!
# Chapter 2 Matrix Bounds: Lipschitz & co-Lipschitz Certificates, Two-Step Composition, and Perturbation

Formalizes Section 2.1 (definitions, basic restriction/monotonicity facts, two-step
composition laws, co-Lip vanishing criterion, and two-operator perturbation bounds)
from `source/02-operator-bounds.md` (`HC02-D01`, `HC02-D02`, `HC02-P01`–`HC02-P11`).
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Global and Restricted Lipschitz Matrix Certificates (HC02-D01) -/

/-- A gauge matrix `L` is a legal global Lipschitz matrix for `ϕ` if for all `x, y ∈ dom(ϕ)`
and all `j ∈ I`, `d_j(ϕ(x), ϕ(y)) ≤ ∑ i, L_{i → j} * d_i(x, y)`. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Certificate family `ℒ(ϕ)` of all legal global Lipschitz matrices of `ϕ`. -/
def LipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- A gauge matrix `L` is a legal restricted Lipschitz matrix for `ϕ` on `U` if
`U ⊆ dom(ϕ)` and for all `x, y ∈ U` and `j ∈ I`,
`d_j(ϕ(x), ϕ(y)) ≤ ∑ i, L_{i → j} * d_i(x, y)`. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Certificate family `ℒ(ϕ)|_U` of all legal restricted Lipschitz matrices of `ϕ` on `U`. -/
def RestrictedLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem lipSet_eq_restrictedLipSet_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    LipSet d ϕ = RestrictedLipSet d ϕ (dom ϕ) := by
  ext L
  simp [LipSet, RestrictedLipSet, IsLipMatrix, IsRestrictedLipMatrix]

/-- Generalized Lip convention: `∞ * 0 = 0`, so an `∞` entry contributes `0` when `d_i(x, y) = 0`. -/
theorem top_entry_mul_zero {X I : Type} (d : I → X → X → ENNReal)
    (L : GaugeMatrix I) {i j : I} {x y : X}
    (hL : L i j = ⊤) (hd : d i x y = 0) :
    L i j * d i x y = 0 := by
  rw [hL, hd, mul_zero]

/-- Generalized Lip convention: when `L_{i → j} = ∞` and `d_i(x, y) > 0`, the term is `∞`
and the Lip inequality holds trivially. -/
theorem top_entry_lip_ineq_trivial {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (L : GaugeMatrix I) {i j : I} {x y : X}
    (hL : L i j = ⊤) (hd : 0 < d i x y) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, L k j * d k x y := by
  have hterm : L i j * d i x y = ⊤ := by
    rw [hL, ENNReal.top_mul hd.ne']
  have hsum_top : (∑ k : I, L k j * d k x y) = ⊤ :=
    top_unique (hterm ▸ Finset.single_le_sum (f := fun k => L k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i))
  rw [hsum_top]
  exact le_top

/-! ### 2. Single-Component Degeneration and Restriction Monotonicity (HC02-P01–P04) -/

/--
OET anchor: h-c4369c63c86cbacf (`HC02-P01`)
When `I = {i}`, the Lipschitz matrix condition degenerates to the single scalar
inequality `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)` on `dom(ϕ)`.
-/
theorem isLipMatrix_iff_scalar_of_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hI : ∀ k : I, k = i) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  have hsum : ∀ x y : X, (∑ k : I, L k i * d k x y) = L i i * d i x y := by
    intro x y
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      exact absurd (hI k) hki
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  constructor
  · intro hL x hx y hy
    simpa [hsum x y] using hL x hx y hy i
  · intro hscalar x hx y hy j
    have hj : j = i := hI j
    subst hj
    rw [hsum x y]
    exact hscalar x hx y hy

/-- `HC02-P01` stated directly with `Fintype.card I = 1`. -/
theorem isLipMatrix_iff_scalar_of_card_eq_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  apply isLipMatrix_iff_scalar_of_singleton d ϕ L i
  intro k
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨a, ha⟩
  rw [ha k, ha i]

/--
`HC02-P02`: For `U ⊆ dom(ϕ)`, every global Lip certificate restricts to `U`:
`ℒ(ϕ) ⊆ ℒ(ϕ)|_U`.
-/
theorem lipSet_subset_restrictedLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    LipSet d ϕ ⊆ RestrictedLipSet d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/--
`HC02-P03`: Shrinking the evaluation domain enlarges the restricted Lip certificate family:
if `U ⊆ V`, then `ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U` (in particular for `U ⊆ V ⊆ dom(ϕ)`).
-/
theorem restrictedLipSet_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) :
    RestrictedLipSet d ϕ V ⊆ RestrictedLipSet d ϕ U := by
  intro L hL
  exact ⟨Set.Subset.trans hUV hL.1, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- Entrywise infimum `a_{i → j}(U) := inf { M_{i → j} : M ∈ ℒ(ϕ)|_U }` (`HC02-P04`). -/
noncomputable def entrywiseLipInf {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf { c : ENNReal | ∃ M ∈ RestrictedLipSet d ϕ U, M i j = c }

/--
`HC02-P04`: Shrinking the domain cannot increase the entrywise infimum of restricted Lip
certificates: if `U ⊆ V`, then `a_{i → j}(U) ≤ a_{i → j}(V)`.
-/
theorem entrywiseLipInf_mono {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (i j : I) :
    entrywiseLipInf d ϕ U i j ≤ entrywiseLipInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro c ⟨M, hM, rfl⟩
  exact ⟨M, restrictedLipSet_antitone d ϕ hUV hM, rfl⟩

/-! ### 3. Two-Step Lipschitz Composition Law (HC02-P05) -/

/--
OET anchor: h-193cebcc1a7f9259 (`HC02-P05`)
**Proposition (Lip matrix composition law)**:
For `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` and `U₂ = ϕ₁(U₁)`, if `L₁ ∈ ℒ(ϕ₁)|_{U₁}` and `L₂ ∈ ℒ(ϕ₂)|_{U₂}`,
then `L₂ · L₁ ∈ ℒ(ϕ₂ ∘ ϕ₁)|_{U₁}`.
-/
theorem restrictedLipSet_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (hU1 : U1 ⊆ dom (compOp ϕ2 ϕ1))
    {L1 L2 : GaugeMatrix I}
    (hL1 : L1 ∈ RestrictedLipSet d ϕ1 U1)
    (hL2 : L2 ∈ RestrictedLipSet d ϕ2 (operator_image ϕ1 U1)) :
    matMul L2 L1 ∈ RestrictedLipSet d (compOp ϕ2 ϕ1) U1 := by
  refine ⟨hU1, ?_⟩
  intro x hx y hy j
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  calc
    d j ((compOp ϕ2 ϕ1).func x) ((compOp ϕ2 ϕ1).func y)
        = d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) := rfl
    _ ≤ ∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y) :=
          hL2.2 (ϕ1.func x) hx2 (ϕ1.func y) hy2 j
    _ ≤ ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_right (hL1.2 x hx y hy k) (L2 k j)
    _ = ∑ k : I, ∑ i : I, L2 k j * (L1 i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, L2 k j * (L1 i k * d i x y) := Finset.sum_comm
    _ = ∑ i : I, (∑ k : I, L2 k j * L1 i k) * d i x y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [mul_assoc]
    _ = ∑ i : I, matMul L2 L1 i j * d i x y := rfl

/-! ### 4. Restricted co-Lipschitz Matrix Certificates (HC02-D02) -/

/-- A gauge matrix `K` is a legal restricted co-Lipschitz matrix for `ϕ` on `U` if
`U` is nonempty, `U ⊆ dom(ϕ)`, and for all `x, y ∈ U` and `j ∈ I`,
`∑ i, K_{i → j} * d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))`. -/
def IsCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- Certificate family `𝒦(ϕ)|_U` of all legal restricted co-Lipschitz matrices of `ϕ` on `U`.
Membership always includes `U ≠ ∅` (`U.Nonempty`) and `U ⊆ dom(ϕ)`. -/
def CoLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsCoLipMatrix d ϕ U K }

theorem coLipSet_nonempty_of_mem {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ CoLipSet d ϕ U) : U.Nonempty :=
  hK.1

theorem coLipSet_ne_empty_of_mem {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ CoLipSet d ϕ U) : U ≠ ∅ :=
  hK.1.ne_empty

theorem coLipSet_subset_dom_of_mem {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ CoLipSet d ϕ U) : U ⊆ dom ϕ :=
  hK.2.1

/-! ### 5. co-Lipschitz Vanishing Criterion and Two-Step Composition Law (HC02-P06, P07) -/

/-- General restricted-domain form of the co-Lip vanishing pair criterion. -/
theorem coLip_entry_eq_zero_of_pair_on {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ U)
    {i j : I} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_out : d j (ϕ.func x) (ϕ.func y) = 0) (h_in : 0 < d i x y) :
    K i j = 0 := by
  have hle : K i j * d i x y ≤ 0 := by
    calc
      K i j * d i x y
          ≤ ∑ k : I, K k j * d k x y :=
            Finset.single_le_sum (f := fun k => K k j * d k x y)
              (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
      _ = 0 := h_out
  have hmul : K i j * d i x y = 0 := le_antisymm hle (zero_le _)
  rcases mul_eq_zero.mp hmul with hK0 | hd0
  · exact hK0
  · exact absurd hd0 h_in.ne'

/--
OET anchor: h-88784dcbfff0ea66 (`HC02-P06`)
**Remark (Point-pair criterion for co-Lip channel degeneration)**:
If there exist `x, y ∈ dom(ϕ)` with `d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`,
then every global co-Lip matrix `K ∈ 𝒦(ϕ)|_{dom(ϕ)}` satisfies `K_{i → j} = 0`.
-/
theorem coLip_entry_eq_zero_of_pair {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ (dom ϕ))
    {i j : I} {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    (h_out : d j (ϕ.func x) (ϕ.func y) = 0) (h_in : 0 < d i x y) :
    K i j = 0 :=
  coLip_entry_eq_zero_of_pair_on d ϕ (dom ϕ) hK hx hy h_out h_in

/--
OET anchor: h-0f256e6f1d38a612 (`HC02-P07`)
**Proposition (co-Lip matrix composition law)**:
For `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` and `U₂ = ϕ₁(U₁)`, if `K₁ ∈ 𝒦(ϕ₁)|_{U₁}` and `K₂ ∈ 𝒦(ϕ₂)|_{U₂}`,
then `K₂ · K₁ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}` (which in particular certifies `U₁.Nonempty`).
-/
theorem coLipSet_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (hU1 : U1 ⊆ dom (compOp ϕ2 ϕ1))
    {K1 K2 : GaugeMatrix I}
    (hK1 : K1 ∈ CoLipSet d ϕ1 U1)
    (hK2 : K2 ∈ CoLipSet d ϕ2 (operator_image ϕ1 U1)) :
    matMul K2 K1 ∈ CoLipSet d (compOp ϕ2 ϕ1) U1 := by
  refine ⟨hK1.1, hU1, ?_⟩
  intro x hx y hy j
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matMul K2 K1 i j * d i x y
        = ∑ i : I, (∑ k : I, K2 k j * K1 i k) * d i x y := rfl
    _ = ∑ i : I, ∑ k : I, K2 k j * (K1 i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [mul_assoc]
    _ = ∑ k : I, ∑ i : I, K2 k j * (K1 i k * d i x y) := Finset.sum_comm
    _ = ∑ k : I, K2 k j * (∑ i : I, K1 i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.mul_sum]
    _ ≤ ∑ k : I, K2 k j * d k (ϕ1.func x) (ϕ1.func y) := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_right (hK1.2.2 x hx y hy k) (K2 k j)
    _ ≤ d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) :=
          hK2.2.2 (ϕ1.func x) hx2 (ϕ1.func y) hy2 j
    _ = d j ((compOp ϕ2 ϕ1).func x) ((compOp ϕ2 ϕ1).func y) := rfl

/-! ### 6. Two-Operator Pairwise Image-Distance Perturbation Bounds (HC02-P08–P11) -/

/--
OET anchor: h-b959b42f25710105 (i), forward direction (`HC02-P08`)
If `U ⊆ dom(ϕ₁, ϕ₂)` and `d_j(ϕ₁(z), ϕ₂(z)) ≤ δ_j` on `U`, then
`d_j(ϕ₂(x), ϕ₂(y)) ≤ d_j(ϕ₁(x), ϕ₁(y)) + 2 * δ_j`.
-/
theorem perturbation_dist_forward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (_hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
  intro x hx y hy j
  have h1 : d j (ϕ2.func x) (ϕ1.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  have h2 : d j (ϕ1.func y) (ϕ2.func y) ≤ δ j := hδ y hy j
  calc
    d j (ϕ2.func x) (ϕ2.func y)
        ≤ d j (ϕ2.func x) (ϕ1.func x) + d j (ϕ1.func x) (ϕ2.func y) :=
          (hd j).triangle _ _ _
    _ ≤ d j (ϕ2.func x) (ϕ1.func x) +
          (d j (ϕ1.func x) (ϕ1.func y) + d j (ϕ1.func y) (ϕ2.func y)) :=
          add_le_add_right ((hd j).triangle _ _ _) _
    _ = d j (ϕ1.func x) (ϕ1.func y) +
          (d j (ϕ2.func x) (ϕ1.func x) + d j (ϕ1.func y) (ϕ2.func y)) :=
          add_left_comm _ _ _
    _ ≤ d j (ϕ1.func x) (ϕ1.func y) + (δ j + δ j) :=
          add_le_add_right (add_le_add h1 h2) _
    _ = d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
          rw [two_mul]

/-- Explicit additive form `+ δ_j + δ_j` of `HC02-P08`. -/
theorem perturbation_dist_forward_add {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j := by
  intro x hx y hy j
  simpa [two_mul, add_assoc] using
    perturbation_dist_forward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

/--
OET anchor: h-b959b42f25710105 (i), reverse direction (`HC02-P09`)
Under the same premises, swapping `ϕ₁` and `ϕ₂` yields
`d_j(ϕ₁(x), ϕ₁(y)) ≤ d_j(ϕ₂(x), ϕ₂(y)) + 2 * δ_j`.
-/
theorem perturbation_dist_backward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  have hU' : U ⊆ commonDom2 ϕ2 ϕ1 := by
    simpa [commonDom2, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ j : I, d j (ϕ2.func z) (ϕ1.func z) ≤ δ j := by
    intro z hz j
    rw [(hd j).symm]
    exact hδ z hz j
  exact perturbation_dist_forward d hd ϕ2 ϕ1 U hU' δ hδ'

/-- Explicit additive form `+ δ_j + δ_j` of `HC02-P09`. -/
theorem perturbation_dist_backward_add {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + δ j + δ j := by
  intro x hx y hy j
  simpa [two_mul, add_assoc] using
    perturbation_dist_backward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

/--
OET anchor: h-b959b42f25710105 (ii) (`HC02-P10`)
**Lip upper-bound bridge**: If in addition `L₁ ∈ ℒ(ϕ₁)|_U`, then
`d_j(ϕ₂(x), ϕ₂(y)) ≤ ∑ i, L₁_{i → j} * d_i(x, y) + 2 * δ_j`.
-/
theorem perturbation_lip_bridge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {L1 : GaugeMatrix I} (hL1 : L1 ∈ RestrictedLipSet d ϕ1 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j := by
  intro x hx y hy j
  calc
    d j (ϕ2.func x) (ϕ2.func y)
        ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j :=
          perturbation_dist_forward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j
    _ ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j :=
          add_le_add_left (hL1.2 x hx y hy j) _

/-- Swapped Lip upper-bound bridge (line 178 remark): transferring `L₂ ∈ ℒ(ϕ₂)|_U` to `ϕ₁`. -/
theorem perturbation_lip_bridge_swap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {L2 : GaugeMatrix I} (hL2 : L2 ∈ RestrictedLipSet d ϕ2 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ (∑ i : I, L2 i j * d i x y) + 2 * δ j := by
  intro x hx y hy j
  calc
    d j (ϕ1.func x) (ϕ1.func y)
        ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j :=
          perturbation_dist_backward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j
    _ ≤ (∑ i : I, L2 i j * d i x y) + 2 * δ j :=
          add_le_add_left (hL2.2 x hx y hy j) _

/--
OET anchor: h-b959b42f25710105 (iii) (`HC02-P11`)
**co-Lip lower-bound bridge**: If in addition `K₁ ∈ 𝒦(ϕ₁)|_U`, then
`∑ i, K₁_{i → j} * d_i(x, y) ≤ d_j(ϕ₂(x), ϕ₂(y)) + 2 * δ_j`.
-/
theorem perturbation_coLip_bridge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {K1 : GaugeMatrix I} (hK1 : K1 ∈ CoLipSet d ϕ1 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K1 i j * d i x y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  intro x hx y hy j
  calc
    ∑ i : I, K1 i j * d i x y
        ≤ d j (ϕ1.func x) (ϕ1.func y) := hK1.2.2 x hx y hy j
    _ ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j :=
          perturbation_dist_backward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

/-- Swapped co-Lip lower-bound bridge (line 178 remark): transferring `K₂ ∈ 𝒦(ϕ₂)|_U` to `ϕ₁`. -/
theorem perturbation_coLip_bridge_swap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {K2 : GaugeMatrix I} (hK2 : K2 ∈ CoLipSet d ϕ2 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K2 i j * d i x y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
  intro x hx y hy j
  calc
    ∑ i : I, K2 i j * d i x y
        ≤ d j (ϕ2.func x) (ϕ2.func y) := hK2.2.2 x hx y hy j
    _ ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j :=
          perturbation_dist_forward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

end OetCh02
```

```lean filename=Ch02/ChainBounds.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02.MatrixCore
import Ch02.MatrixBounds

/-!
# Chapter 2 Finite-Chain Bounds and Path-Based Zero/Positivity Criteria

Formalizes the finite-composition local matrix bounds (Corollary `#h-c80171fa685dc795`),
the zero-step identity certificates (Remark `#h-11006ddd8c43bfec`), and the path-based
zero/positivity criteria for finite matrix products (Proposition `#h-e4154c34e95d3c23`)
from `source/02-operator-bounds.md` (`HC02-D05`, `HC02-P12`–`HC02-P17`).
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Stepwise Chain Data Structures (HC02-D05) -/

/-- Stepwise data for a finite operator chain `cₖ = ϕₖ ∘ … ∘ ϕ₁` equipped with local
Lipschitz matrix certificates `L^{(m)} ∈ ℒ(ϕₘ)|_{Uₘ}` on the actual recursive domains
`U₁ ⊆ dom(cₖ)`, `U_{m+1} = ϕₘ(Uₘ)`. Contains only step-level data (never the composite bound). -/
structure LipChainData {X I : Type} (bot : X) [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  startDomain : Set X
  startDomain_subset : startDomain ⊆ dom (finChainOp ops)
  stepMatrices : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k,
    stepMatrices m ∈ RestrictedLipSet d (ops m) (chainDomain ops startDomain m.castSucc)

/-- Stepwise data for a finite operator chain `cₖ = ϕₖ ∘ … ∘ ϕ₁` equipped with local
co-Lipschitz matrix certificates `K^{(m)} ∈ 𝒦(ϕₘ)|_{Uₘ}` on the actual recursive domains
`U₁ ⊆ dom(cₖ)`, `U_{m+1} = ϕₘ(Uₘ)`. Each `step_valid m` includes nonemptiness of `Uₘ`.
Contains only step-level data (never the composite bound). -/
structure CoLipChainData {X I : Type} (bot : X) [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  startDomain : Set X
  startDomain_subset : startDomain ⊆ dom (finChainOp ops)
  stepMatrices : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k,
    stepMatrices m ∈ CoLipSet d (ops m) (chainDomain ops startDomain m.castSucc)

/-- Dropping the final step of a length `k + 1` Lipschitz chain yields a valid prefix chain. -/
def LipChainData.prefix {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : LipChainData bot d (k + 1)) :
    LipChainData bot d k where
  ops := fun t => chain.ops t.castSucc
  startDomain := chain.startDomain
  startDomain_subset := by
    have hcomp : finChainOp chain.ops =
        compOp (chain.ops (Fin.last k)) (finChainOp (fun t : Fin k => chain.ops t.castSucc)) :=
      finChainOp_succ_last chain.ops
    exact Set.Subset.trans chain.startDomain_subset
      (hcomp ▸ dom_compOp_subset_left _ _)
  stepMatrices := fun t => chain.stepMatrices t.castSucc
  step_valid := fun m => by
    rw [chainDomain_prefix chain.ops chain.startDomain m.castSucc]
    exact chain.step_valid m.castSucc

/-- Dropping the final step of a length `k + 1` co-Lipschitz chain yields a valid prefix chain. -/
def CoLipChainData.prefix {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : CoLipChainData bot d (k + 1)) :
    CoLipChainData bot d k where
  ops := fun t => chain.ops t.castSucc
  startDomain := chain.startDomain
  startDomain_subset := by
    have hcomp : finChainOp chain.ops =
        compOp (chain.ops (Fin.last k)) (finChainOp (fun t : Fin k => chain.ops t.castSucc)) :=
      finChainOp_succ_last chain.ops
    exact Set.Subset.trans chain.startDomain_subset
      (hcomp ▸ dom_compOp_subset_left _ _)
  stepMatrices := fun t => chain.stepMatrices t.castSucc
  step_valid := fun m => by
    rw [chainDomain_prefix chain.ops chain.startDomain m.castSucc]
    exact chain.step_valid m.castSucc

/-! ### 2. Finite-Chain Local Matrix Bounds (HC02-P12, HC02-P13) -/

/--
OET anchor: h-c80171fa685dc795 (i) (`HC02-P12`)
**Corollary (Local Lip matrix bound for finite compositions)**:
For `k ≥ 1`, if each step has a valid local Lip matrix `L^{(m)} ∈ ℒ(ϕₘ)|_{Uₘ}` on the
actual intermediate domain `Uₘ`, then `L^{(k)} · … · L^{(1)} ∈ ℒ(cₖ)|_{U₁}`.
-/
theorem finChain_lip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (chain : LipChainData bot d k),
      finMatProd chain.stepMatrices ∈
        RestrictedLipSet d (finChainOp chain.ops) chain.startDomain
  | 0, hk, _ => absurd hk (by decide)
  | 1, _, chain => by
      rw [finMatProd_one, finChainOp_one]
      exact chain.step_valid 0
  | k + 2, _, chain => by
      have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_pref := finChain_lip_bound d (k + 1) hk chain.prefix
      have h_last_dom :
          chainDomain chain.ops chain.startDomain (Fin.last (k + 1)).castSucc =
            operator_image (finChainOp chain.prefix.ops) chain.startDomain := by
        rw [← chainDomain_prefix chain.ops chain.startDomain (Fin.last (k + 1))]
        exact chainDomain_last_eq_operator_image chain.prefix.ops chain.startDomain
      have h_last :
          chain.stepMatrices (Fin.last (k + 1)) ∈
            RestrictedLipSet d (chain.ops (Fin.last (k + 1)))
              (operator_image (finChainOp chain.prefix.ops) chain.startDomain) := by
        rw [← h_last_dom]
        exact chain.step_valid (Fin.last (k + 1))
      rw [finMatProd_succ_last, finChainOp_succ_last]
      have hU1 : chain.startDomain ⊆
          dom (compOp (chain.ops (Fin.last (k + 1))) (finChainOp chain.prefix.ops)) := by
        simpa [LipChainData.prefix, finChainOp_succ_last] using chain.startDomain_subset
      exact restrictedLipSet_comp d (finChainOp chain.prefix.ops)
        (chain.ops (Fin.last (k + 1))) chain.startDomain hU1 h_pref h_last

/-- Unpacked version of `HC02-P12` taking the step operators and matrices directly. -/
theorem finChain_lip_bound_unpacked {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) (U1 : Set X) (hU1 : U1 ⊆ dom (finChainOp ϕ))
    (L : Fin k → GaugeMatrix I)
    (hL : ∀ m : Fin k, L m ∈ RestrictedLipSet d (ϕ m) (chainDomain ϕ U1 m.castSucc)) :
    finMatProd L ∈ RestrictedLipSet d (finChainOp ϕ) U1 :=
  finChain_lip_bound d k hk ⟨ϕ, U1, hU1, L, hL⟩

/--
OET anchor: h-c80171fa685dc795 (ii) (`HC02-P13`)
**Corollary (Local co-Lip matrix bound for finite compositions)**:
For `k ≥ 1`, if each step has a valid local co-Lip matrix `K^{(m)} ∈ 𝒦(ϕₘ)|_{Uₘ}` on the
actual intermediate domain `Uₘ` (each carrying nonemptiness of `Uₘ`), then
`K^{(k)} · … · K^{(1)} ∈ 𝒦(cₖ)|_{U₁}`.
-/
theorem finChain_coLip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (chain : CoLipChainData bot d k),
      finMatProd chain.stepMatrices ∈
        CoLipSet d (finChainOp chain.ops) chain.startDomain
  | 0, hk, _ => absurd hk (by decide)
  | 1, _, chain => by
      rw [finMatProd_one, finChainOp_one]
      exact chain.step_valid 0
  | k + 2, _, chain => by
      have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_pref := finChain_coLip_bound d (k + 1) hk chain.prefix
      have h_last_dom :
          chainDomain chain.ops chain.startDomain (Fin.last (k + 1)).castSucc =
            operator_image (finChainOp chain.prefix.ops) chain.startDomain := by
        rw [← chainDomain_prefix chain.ops chain.startDomain (Fin.last (k + 1))]
        exact chainDomain_last_eq_operator_image chain.prefix.ops chain.startDomain
      have h_last :
          chain.stepMatrices (Fin.last (k + 1)) ∈
            CoLipSet d (chain.ops (Fin.last (k + 1)))
              (operator_image (finChainOp chain.prefix.ops) chain.startDomain) := by
        rw [← h_last_dom]
        exact chain.step_valid (Fin.last (k + 1))
      rw [finMatProd_succ_last, finChainOp_succ_last]
      have hU1 : chain.startDomain ⊆
          dom (compOp (chain.ops (Fin.last (k + 1))) (finChainOp chain.prefix.ops)) := by
        simpa [CoLipChainData.prefix, finChainOp_succ_last] using chain.startDomain_subset
      exact coLipSet_comp d (finChainOp chain.prefix.ops)
        (chain.ops (Fin.last (k + 1))) chain.startDomain hU1 h_pref h_last

/-- Unpacked version of `HC02-P13` taking the step operators and matrices directly. -/
theorem finChain_coLip_bound_unpacked {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) (U1 : Set X) (hU1 : U1 ⊆ dom (finChainOp ϕ))
    (K : Fin k → GaugeMatrix I)
    (hK : ∀ m : Fin k, K m ∈ CoLipSet d (ϕ m) (chainDomain ϕ U1 m.castSucc)) :
    finMatProd K ∈ CoLipSet d (finChainOp ϕ) U1 :=
  finChain_coLip_bound d k hk ⟨ϕ, U1, hU1, K, hK⟩

/-! ### 3. Zero-Step Identity Certificates (HC02-P14, HC02-P15) -/

/-- Exact identity-matrix summation formula: `∑ i, I_{i → j} * d_i(x, y) = d_j(x, y)`. -/
theorem idMatrix_sum_eq_dist {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, idMatrix i j * d i x y) = d j x y := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [idMatrix_apply_ne hij, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/--
OET anchor: h-11006ddd8c43bfec (`HC02-P14`)
For any `U ⊆ dom(id_X)`, the identity matrix `I` is a valid restricted Lip matrix for `id_X`.
-/
theorem idMatrix_mem_restrictedLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X} (hU : U ⊆ dom (idOp (bot := bot))) :
    idMatrix ∈ RestrictedLipSet d (idOp (bot := bot)) U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  simp [idMatrix_sum_eq_dist]

/-- Zero-step (`k = 0`) boundary formulation of `HC02-P14`:
for `c₀ = id_X`, empty product `= I`, and nonempty `U ⊆ dom(c₀)`, `I ∈ ℒ(c₀)|_U`. -/
theorem zeroStep_lip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (ϕ : Fin 0 → Operator X bot) (L : Fin 0 → GaugeMatrix I)
    {U : Set X} (_hU_ne : U.Nonempty) (hU : U ⊆ dom (finChainOp ϕ)) :
    finMatProd L ∈ RestrictedLipSet d (finChainOp ϕ) U := by
  rw [finMatProd_zero, finChainOp_zero]
  exact idMatrix_mem_restrictedLipSet d (by simpa [finChainOp_zero] using hU)

/--
OET anchor: h-11006ddd8c43bfec (`HC02-P15`)
For any nonempty `U ⊆ dom(id_X)`, the identity matrix `I` is a valid restricted co-Lip
matrix for `id_X`.
-/
theorem idMatrix_mem_coLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (idOp (bot := bot))) :
    idMatrix ∈ CoLipSet d (idOp (bot := bot)) U := by
  refine ⟨hU_ne, hU, ?_⟩
  intro x _ y _ j
  simp [idMatrix_sum_eq_dist]

/-- Zero-step (`k = 0`) boundary formulation of `HC02-P15`:
for `c₀ = id_X`, empty product `= I`, and nonempty `U ⊆ dom(c₀)`, `I ∈ 𝒦(c₀)|_U`. -/
theorem zeroStep_coLip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (ϕ : Fin 0 → Operator X bot) (K : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (finChainOp ϕ)) :
    finMatProd K ∈ CoLipSet d (finChainOp ϕ) U := by
  rw [finMatProd_zero, finChainOp_zero]
  exact idMatrix_mem_coLipSet d hU_ne (by simpa [finChainOp_zero] using hU)

/-- Combined intersection form of Remark `#h-11006ddd8c43bfec`:
`I ∈ ℒ(id_X)|_U ∩ 𝒦(id_X)|_U` for any nonempty `U ⊆ dom(id_X)`. -/
theorem idMatrix_mem_restrictedLipSet_inter_coLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (idOp (bot := bot))) :
    idMatrix ∈ RestrictedLipSet d (idOp (bot := bot)) U ∩ CoLipSet d (idOp (bot := bot)) U :=
  ⟨idMatrix_mem_restrictedLipSet d hU, idMatrix_mem_coLipSet d hU_ne hU⟩

/-! ### 4. Zero and Positivity Criteria for Finite Matrix Products (HC02-P16, HC02-P17) -/

/-- General algebraic zero criterion for finite `ENNReal` matrix products (`n ≥ 1`):
`(M^{(n)} · … · M^{(1)})_{i → j} = 0` iff every intermediate index sequence has at least
one zero step entry. -/
theorem finMatProd_apply_eq_zero_iff {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    finMatProd M i j = 0 ↔ ∀ mid : MidIndexSeq I n, PathHasZero n M i j mid := by
  rw [finMatProd_apply_eq_sum_paths n hn M i j, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

/-- General algebraic positivity criterion for finite `ENNReal` matrix products (`n ≥ 1`):
`(M^{(n)} · … · M^{(1)})_{i → j} > 0` iff there exists at least one intermediate index
sequence whose step entries are all strictly positive. -/
theorem finMatProd_apply_pos_iff {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < finMatProd M i j ↔ ∃ mid : MidIndexSeq I n, PathAllPos n M i j mid := by
  rw [pos_iff_ne_zero, ne_eq, finMatProd_apply_eq_zero_iff n hn M i j]
  push Not
  constructor
  · rintro ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [← pathWeight_pos_iff, pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff]
    exact hmid
  · rintro ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [← pathWeight_eq_zero_iff, ← ne_eq, ← pos_iff_ne_zero, pathWeight_pos_iff]
    exact hmid

/--
OET anchor: h-e4154c34e95d3c23 (i) (`HC02-P16`)
**Proposition (Zero criterion for finite Lip matrix product entries)**:
Along a finite operator chain (`n ≥ 1`) with local Lip certificates `L^{(m)} ∈ ℒ(ϕₘ)|_{Uₘ}`,
`[L^{(n)} · … · L^{(1)}]_{i → j} = 0` iff every intermediate index sequence `(k₁, …, k_{n-1})`
contains at least one layer `m` with `[L^{(m)}]_{k_{m-1} → k_m} = 0`.
-/
theorem lipChain_prod_entry_eq_zero_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (n : ℕ) (hn : 1 ≤ n)
    (chain : LipChainData bot d n) (i j : I) :
    finMatProd chain.stepMatrices i j = 0 ↔
      ∀ mid : MidIndexSeq I n, PathHasZero n chain.stepMatrices i j mid :=
  finMatProd_apply_eq_zero_iff n hn chain.stepMatrices i j

/-- `n = 1` degeneration of `HC02-P16`: the unique empty intermediate sequence reduces
the path criterion directly to `[L^{(1)}]_{i → j} = 0`. -/
theorem lipChain_prod_entry_eq_zero_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (chain : LipChainData bot d 1) (i j : I) :
    (∀ mid : MidIndexSeq I 1, PathHasZero 1 chain.stepMatrices i j mid) ↔
      chain.stepMatrices 0 i j = 0 := by
  rw [← lipChain_prod_entry_eq_zero_iff d 1 le_rfl chain i j, finMatProd_one]

/--
OET anchor: h-e4154c34e95d3c23 (ii) (`HC02-P17`)
**Proposition (Positivity criterion for finite co-Lip matrix product entries)**:
Along a finite operator chain (`n ≥ 1`) with local co-Lip certificates `K^{(m)} ∈ 𝒦(ϕₘ)|_{Uₘ}`,
`[K^{(n)} · … · K^{(1)}]_{i → j} > 0` iff there exists at least one intermediate index sequence
`(k₁, …, k_{n-1})` along which every step entry `[K^{(m)}]_{k_{m-1} → k_m} > 0`.
-/
theorem coLipChain_prod_entry_pos_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (n : ℕ) (hn : 1 ≤ n)
    (chain : CoLipChainData bot d n) (i j : I) :
    0 < finMatProd chain.stepMatrices i j ↔
      ∃ mid : MidIndexSeq I n, PathAllPos n chain.stepMatrices i j mid :=
  finMatProd_apply_pos_iff n hn chain.stepMatrices i j

/-- `n = 1` degeneration of `HC02-P17`: the unique empty intermediate sequence reduces
the path criterion directly to `[K^{(1)}]_{i → j} > 0`. -/
theorem coLipChain_prod_entry_pos_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (chain : CoLipChainData bot d 1) (i j : I) :
    (∃ mid : MidIndexSeq I 1, PathAllPos 1 chain.stepMatrices i j mid) ↔
      0 < chain.stepMatrices 0 i j := by
  rw [← coLipChain_prod_entry_pos_iff d 1 le_rfl chain i j, finMatProd_one]

end OetCh02
```

```lean filename=Ch02/ChannelDecoupling.lean
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02.MatrixCore
import Ch02.MatrixBounds

/-!
# Chapter 2 Component Channels, Decoupling, Single-Channel Constants, and Distinguishability

Formalizes Section 2.2 (`#h-7fa97eb6e24d5527`) of `source/02-operator-bounds.md`:
- Component channels, row/column sparsity and decoupling, diagonal certificates (`HC02-D07`).
- Single-channel feasible scalar family and optimal constant (`HC02-D08`) with all
  boundary/attainment properties and explicit counterexample (`HC02-P18`–`HC02-P24`).
- Zero-entry removal, row/column/diagonal simplification (`HC02-P25`–`HC02-P28`).
- Two-sided diagonal scalar bounds and finite-coefficient branch (`HC02-P29`, `HC02-P30`).
- Positive co-Lip channel distinguishability preservation and diagonal reflection of
  the gauge zero-distance relation (`HC02-P31`, `HC02-P32`).
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Component Channels, Row/Column Sparsity, and Diagonal Structure (HC02-D07) -/

/-- A component channel `(i, j) ∈ I × I` from input component `d_i` to output component `d_j`. -/
abbrev Channel (I : Type) : Type := I × I

/-- Channel isolation in an upper-bound certificate `L`: `L_{i → j} = 0`. -/
def ChannelIsolated {I : Type} (L : GaugeMatrix I) (c : Channel I) : Prop :=
  L c.1 c.2 = 0

/-- Positive lower-bound transmission in a co-Lip certificate `K`: `K_{i → j} > 0`. -/
def ChannelPosLowerBound {I : Type} (K : GaugeMatrix I) (c : Channel I) : Prop :=
  0 < K c.1 c.2

/-- Single-row sparsity `Row(L, i, j)`: in row `j` (fixed output `j`), every input entry
`k ≠ i` vanishes (`∀ k ≠ i, L_{k → j} = 0`). -/
def RowSparse {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → L k j = 0

/-- Matrix-level row decoupling at output `j`: row `j` has at most one nonzero entry. -/
def MatrixRowDecoupled {I : Type} (L : GaugeMatrix I) (j : I) : Prop :=
  ∃ i : I, RowSparse L i j

/-- Operator-level row decoupling (`HC02-D07`, line 313): `ϕ` is row-decoupled on `U`
at output component `d_j` if there exists `L ∈ ℒ(ϕ)|_U` whose `j`-th row has at most
one nonzero entry. -/
def IsRowDecoupled {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, MatrixRowDecoupled L j

/-- Single-column sparsity `Col(L, i, j)`: in column `i` (fixed input `i`), every output
entry `k ≠ j` vanishes (`∀ k ≠ j, L_{i → k} = 0`). -/
def ColSparse {I : Type} (L : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ j → L i k = 0

/-- Matrix-level column decoupling at input `i`: column `i` has at most one nonzero entry. -/
def MatrixColDecoupled {I : Type} (L : GaugeMatrix I) (i : I) : Prop :=
  ∃ j : I, ColSparse L i j

/-- Operator-level column decoupling (`HC02-D07`, line 315): `ϕ` is column-decoupled on `U`
at input component `d_i` if there exists `L ∈ ℒ(ϕ)|_U` whose `i`-th column has at most
one nonzero entry. -/
def IsColDecoupled {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ RestrictedLipSet d ϕ U, MatrixColDecoupled L i

/-- Diagonal gauge matrix: all off-diagonal entries vanish (`∀ i ≠ j, L_{i → j} = 0`). -/
def IsDiagonalMatrix {I : Type} (L : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → L i j = 0

/-- Completely decoupled upper-bound system (`HC02-D07`, line 317):
a legal restricted Lip certificate `L ∈ ℒ(ϕ)|_U` that is diagonal. -/
def IsCompletelyDecoupled {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  L ∈ RestrictedLipSet d ϕ U ∧ IsDiagonalMatrix L

theorem isDiagonalMatrix_iff_forall_rowSparse {I : Type} (L : GaugeMatrix I) :
    IsDiagonalMatrix L ↔ ∀ j : I, RowSparse L j j := by
  constructor
  · intro h j k hkj
    exact h k j hkj
  · intro h i j hij
    exact h j i hij

theorem isDiagonalMatrix_iff_forall_colSparse {I : Type} (L : GaugeMatrix I) :
    IsDiagonalMatrix L ↔ ∀ i : I, ColSparse L i i := by
  constructor
  · intro h i k hki
    exact h i k hki.symm
  · intro h i j hij
    exact h i j hij.symm

/-! ### 2. Single-Channel Feasible Scalar Family and Infimum (HC02-D08, HC02-P18–P24) -/

/-- Feasible scalar Lipschitz constant family `S_{i → j}(ϕ; U)` for channel `(i, j)` on `U`:
`{ λ ∈ ENNReal | ∀ x, y ∈ U, d_j(ϕ(x), ϕ(y)) ≤ λ * d_i(x, y) }` (`HC02-D08`). -/
def SingleChannelLipFeasible {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { lam : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ lam * d i x y }

/-- Single-channel Lipschitz constant `L̲_{i → j}(ϕ; U) := inf S_{i → j}(ϕ; U)` (`HC02-D08`).
By `ENNReal` `sInf`, an empty feasible set automatically yields `⊤` (`+∞`).
This is defined independently of any matrix certificate entry `L_{i → j}`. -/
noncomputable def singleChannelLipConst {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (SingleChannelLipFeasible d ϕ U i j)

theorem singleChannelLipConst_eq_top_of_empty {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hempty : SingleChannelLipFeasible d ϕ U i j = ∅) :
    singleChannelLipConst d ϕ U i j = ⊤ := by
  simp [singleChannelLipConst, hempty]

/--
`HC02-P18`: If there exist `x, y ∈ U` with `d_i(x, y) = 0` and `d_j(ϕ(x), ϕ(y)) > 0`,
then no `λ ∈ ENNReal` (including `∞`) satisfies the single-channel bound, so
`S_{i → j} = ∅` and `L̲_{i → j}(ϕ; U) = +∞`.
-/
theorem singleChannelLipFeasible_eq_empty_of_zero_pos {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_in : d i x y = 0) (h_out : 0 < d j (ϕ.func x) (ϕ.func y)) :
    SingleChannelLipFeasible d ϕ U i j = ∅ ∧
      singleChannelLipConst d ϕ U i j = ⊤ := by
  have hempty : SingleChannelLipFeasible d ϕ U i j = ∅ := by
    ext lam
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hlam
    have hle := hlam x hx y hy
    rw [h_in, mul_zero] at hle
    exact not_lt_of_ge hle h_out
  exact ⟨hempty, singleChannelLipConst_eq_top_of_empty d ϕ U i j hempty⟩

/--
`HC02-P20`: The feasible scalar set `S_{i → j}` is upward closed:
if `λ₀ ∈ S` and `λ₀ ≤ λ₁`, then `λ₁ ∈ S`.
-/
theorem singleChannelLipFeasible_upward_closed {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam0 lam1 : ENNReal}
    (h0 : lam0 ∈ SingleChannelLipFeasible d ϕ U i j) (hle : lam0 ≤ lam1) :
    lam1 ∈ SingleChannelLipFeasible d ϕ U i j := by
  intro x hx y hy
  exact le_trans (h0 x hx y hy) (mul_le_mul_left hle (d i x y))

/-- General lemma: any `λ > L̲_{i → j}(ϕ; U)` (allowing `λ = +∞`) belongs to `S_{i → j}`. -/
theorem mem_singleChannelLipFeasible_of_const_lt {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam : ENNReal} (hlt : singleChannelLipConst d ϕ U i j < lam) :
    lam ∈ SingleChannelLipFeasible d ϕ U i j := by
  have hnotle : ¬ lam ≤ sInf (SingleChannelLipFeasible d ϕ U i j) := not_le_of_gt hlt
  have hex : ∃ lam0 ∈ SingleChannelLipFeasible d ϕ U i j, ¬ lam ≤ lam0 := by
    by_contra hall
    push Not at hall
    exact hnotle (le_sInf hall)
  rcases hex with ⟨lam0, hlam0, hnot⟩
  exact singleChannelLipFeasible_upward_closed d ϕ U i j hlam0 (le_of_lt (lt_of_not_ge hnot))

/--
`HC02-P21`: In the positive finite infimum context `0 < a < ∞`, every `λ > a`
(including `λ = ∞`) belongs to `S`.
-/
theorem mem_singleChannelLipFeasible_of_gt_pos_finite {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (_hpos : 0 < singleChannelLipConst d ϕ U i j)
    (_hfin : singleChannelLipConst d ϕ U i j < ⊤)
    {lam : ENNReal} (hlt : singleChannelLipConst d ϕ U i j < lam) :
    lam ∈ SingleChannelLipFeasible d ϕ U i j :=
  mem_singleChannelLipFeasible_of_const_lt d ϕ U i j hlt

/--
`HC02-P19` (lines 279–297): When `0 < a < ∞` where `a = L̲_{i → j}(ϕ; U)`,
the infimum is attained: `a ∈ S_{i → j}`, i.e., `d_j(ϕ(x), ϕ(y)) ≤ a * d_i(x, y)`
holds for all `x, y ∈ U`.
-/
theorem singleChannelLipConst_mem_of_pos_lt_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hpos : 0 < singleChannelLipConst d ϕ U i j)
    (hfin : singleChannelLipConst d ϕ U i j < ⊤) :
    singleChannelLipConst d ϕ U i j ∈ SingleChannelLipFeasible d ϕ U i j := by
  set a := singleChannelLipConst d ϕ U i j
  intro x hx y hy
  set A := d j (ϕ.func x) (ϕ.func y)
  set B := d i x y
  by_cases hB0 : B = 0
  · have htop_mem : (⊤ : ENNReal) ∈ SingleChannelLipFeasible d ϕ U i j :=
      mem_singleChannelLipFeasible_of_gt_pos_finite d ϕ U i j hpos hfin hfin
    have hA0 : A ≤ (⊤ : ENNReal) * B := htop_mem x hx y hy
    rw [hB0, mul_zero] at hA0 ⊢
    exact hA0
  · by_cases hBtop : B = ⊤
    · rw [hBtop, ENNReal.mul_top hpos.ne']
      exact le_top
    · by_contra hnotle
      have hlt : a * B < A := lt_of_not_ge hnotle
      have ha_lt_div : a < A / B :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mpr hlt
      obtain ⟨lam, ha_lt_lam, hlam_lt_div⟩ := exists_between ha_lt_div
      have hlam_mem : lam ∈ SingleChannelLipFeasible d ϕ U i j :=
        mem_singleChannelLipFeasible_of_gt_pos_finite d ϕ U i j hpos hfin ha_lt_lam
      have hA_le : A ≤ lam * B := hlam_mem x hx y hy
      have hlamB_lt : lam * B < A :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp hlam_lt_div
      exact not_lt_of_ge hA_le hlamB_lt

/--
`HC02-P22` (Remark `#h-57de7918859a9de2`, lines 299–305):
When `L̲_{i → j}(ϕ; U) = 0`, every finite positive `λ` (`0 < λ < ∞`) is a valid
single-channel scalar certificate (`λ ∈ S_{i → j}`).
-/
theorem mem_singleChannelLipFeasible_of_const_eq_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (hzero : singleChannelLipConst d ϕ U i j = 0)
    {lam : ENNReal} (hpos : 0 < lam) (_hfin : lam < ⊤) :
    lam ∈ SingleChannelLipFeasible d ϕ U i j := by
  apply mem_singleChannelLipFeasible_of_const_lt d ϕ U i j
  rw [hzero]
  exact hpos

/--
`HC02-P24` (Remark `#h-57de7918859a9de2`, lines 299–309):
Whether or not the infimum is attained, `L̲_{i → j}(ϕ; U) < ∞` holds iff there exists
a finite constant `λ < ∞` satisfying the single-channel bound on all `x, y ∈ U`.
-/
theorem singleChannelLipConst_lt_top_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) :
    singleChannelLipConst d ϕ U i j < ⊤ ↔
      ∃ lam : ENNReal, lam < ⊤ ∧ lam ∈ SingleChannelLipFeasible d ϕ U i j := by
  constructor
  · intro hfin
    by_cases h0 : singleChannelLipConst d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact mem_singleChannelLipFeasible_of_const_eq_zero d ϕ U i j h0 zero_lt_one ENNReal.one_lt_top
    · have hpos : 0 < singleChannelLipConst d ϕ U i j := pos_iff_ne_zero.mpr h0
      exact ⟨singleChannelLipConst d ϕ U i j, hfin,
        singleChannelLipConst_mem_of_pos_lt_top d ϕ U i j hpos hfin⟩
  · rintro ⟨lam, hlam_fin, hlam_mem⟩
    exact lt_of_le_of_lt (sInf_le hlam_mem) hlam_fin

/-! ### 3. Counterexample: Zero Single-Channel Infimum Not Attained by `0` (HC02-P23) -/

/-- Explicit two-component extended pseudometric family on `Option Bool` (with absorbing
element `bot = none`):
- `d false` assigns `0` on the diagonal and `⊤` between distinct points;
- `d true` assigns `0` on the diagonal, `⊤` to `none`, and `1` between distinct non-`bot` points. -/
def zeroInfCounterexampleDist : Bool → Option Bool → Option Bool → ENNReal
  | false, x, y => if x = y then 0 else ⊤
  | true, x, y => if x = y then 0 else if x = none ∨ y = none then ⊤ else 1

theorem zeroInfCounterexample_extendedPseudoMetric :
    ∀ i : Bool, ExtendedPseudoMetric (Option Bool) none (zeroInfCounterexampleDist i) := by
  intro i
  cases i with
  | false =>
      refine
        { nonabsorbing := ⟨some false, Option.some_ne_none false⟩
          dist_self := fun x => by simp [zeroInfCounterexampleDist]
          symm := fun x y => by
            by_cases h : x = y
            · subst h; simp [zeroInfCounterexampleDist]
            · have h' : y ≠ x := Ne.symm h
              simp [zeroInfCounterexampleDist, h, h']
          triangle := fun x y z => by
            by_cases hxz : x = z
            · subst hxz; simp [zeroInfCounterexampleDist]
            · by_cases hxy : x = y
              · subst hxy; simp [zeroInfCounterexampleDist, hxz]
              · simp [zeroInfCounterexampleDist, hxz, hxy]
          isolate_bot := fun x hx => by simp [zeroInfCounterexampleDist, hx] }
  | true =>
      refine
        { nonabsorbing := ⟨some false, Option.some_ne_none false⟩
          dist_self := fun x => by simp [zeroInfCounterexampleDist]
          symm := fun x y => by
            cases x <;> cases y <;> simp [zeroInfCounterexampleDist]
            · rename_i a b
              by_cases h : a = b
              · subst h; simp
              · have h' : b ≠ a := Ne.symm h
                simp [h, h']
          triangle := fun x y z => by
            cases x with
            | none =>
                cases y with
                | none =>
                    cases z <;> simp [zeroInfCounterexampleDist]
                | some b =>
                    cases z <;> simp [zeroInfCounterexampleDist]
            | some a =>
                cases y with
                | none =>
                    cases z <;> simp [zeroInfCounterexampleDist]
                | some b =>
                    cases z with
                    | none => simp [zeroInfCounterexampleDist]
                    | some c =>
                        cases a <;> cases b <;> cases c <;>
                          simp [zeroInfCounterexampleDist]
          isolate_bot := fun x hx => by
            cases x with
            | none => exact absurd rfl hx
            | some a => simp [zeroInfCounterexampleDist] }

/-- Nonempty valid domain `U = {some false, some true} ⊆ dom(id)`. -/
def zeroInfCounterexampleU : Set (Option Bool) :=
  {some false, some true}

theorem zeroInfCounterexampleU_nonempty : zeroInfCounterexampleU.Nonempty :=
  ⟨some false, by simp [zeroInfCounterexampleU]⟩

theorem zeroInfCounterexampleU_subset_dom :
    zeroInfCounterexampleU ⊆ dom (idOp (bot := (none : Option Bool))) := by
  intro x hx
  rcases hx with rfl | rfl <;> simp [dom, idOp]

/-- Every positive `λ` belongs to `S_{false → true}(id; U)`, so the infimum is `0`. -/
theorem zeroInfCounterexample_const_eq_zero :
    singleChannelLipConst zeroInfCounterexampleDist (idOp (bot := (none : Option Bool)))
      zeroInfCounterexampleU false true = 0 := by
  have hpos_mem : ∀ lam : ENNReal, 0 < lam →
      lam ∈ SingleChannelLipFeasible zeroInfCounterexampleDist
        (idOp (bot := (none : Option Bool))) zeroInfCounterexampleU false true := by
    intro lam hlam x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [zeroInfCounterexampleDist, ENNReal.mul_top hlam.ne']
  have hle_pos : ∀ lam : ENNReal, 0 < lam →
      singleChannelLipConst zeroInfCounterexampleDist (idOp (bot := (none : Option Bool)))
        zeroInfCounterexampleU false true ≤ lam :=
    fun lam hlam => sInf_le (hpos_mem lam hlam)
  by_contra hne
  set a := singleChannelLipConst zeroInfCounterexampleDist (idOp (bot := (none : Option Bool)))
    zeroInfCounterexampleU false true
  have ha_pos : 0 < a := pos_iff_ne_zero.mpr hne
  obtain ⟨lam, h0_lt_lam, hlam_lt_a⟩ := exists_between ha_pos
  exact not_lt_of_ge (hle_pos lam h0_lt_lam) hlam_lt_a

/-- Yet `λ = 0` is NOT feasible because `d_false(x, y) = ∞`, `0 * ∞ = 0`, while `d_true(x, y) = 1`. -/
theorem zeroInfCounterexample_zero_not_mem :
    (0 : ENNReal) ∉ SingleChannelLipFeasible zeroInfCounterexampleDist
      (idOp (bot := (none : Option Bool))) zeroInfCounterexampleU false true := by
  intro h0
  have hle := h0 (some false) (by simp [zeroInfCounterexampleU])
    (some true) (by simp [zeroInfCounterexampleU])
  simp [zeroInfCounterexampleDist] at hle

/--
`HC02-P23`: Explicit counterexample proving that in a legal extended gauge space with
a legal operator `ϕ` and nonempty valid `U ⊆ dom(ϕ)`, one can have `L̲_{i → j}(ϕ; U) = 0`
while `0 ∉ S_{i → j}(ϕ; U)`.
-/
theorem exists_zero_singleChannelLipConst_not_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
      singleChannelLipConst d ϕ U i j = 0 ∧
      (0 : ENNReal) ∉ SingleChannelLipFeasible d ϕ U i j :=
  ⟨Option Bool, Bool, none, inferInstance, inferInstance,
    zeroInfCounterexampleDist, zeroInfCounterexample_extendedPseudoMetric,
    idOp, zeroInfCounterexampleU, false, true,
    zeroInfCounterexampleU_nonempty, zeroInfCounterexampleU_subset_dom,
    zeroInfCounterexample_const_eq_zero, zeroInfCounterexample_zero_not_mem⟩

/-- Remark `#h-57de7918859a9de2` (`HC02-D08` separation note): the single-channel constant
`L̲_{i → j}(ϕ; U)` is genuinely distinct from a Lip matrix entry `[L]_{i → j}`:
in a legal extended gauge space, there exists `L ∈ ℒ(ϕ)|_U` with `L_{i → j} = 0`
while `L̲_{i → j}(ϕ; U) = +∞`. -/
theorem exists_singleChannelLipConst_ne_lipMatrix_entry :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i : I, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) (i j : I),
      L ∈ RestrictedLipSet d ϕ U ∧
      L i j = 0 ∧
      singleChannelLipConst d ϕ U i j = ⊤ ∧
      singleChannelLipConst d ϕ U i j ≠ L i j := by
  let d : Bool → Option Bool → Option Bool → ENNReal
    | false, x, y => if x = y then 0 else if x = none ∨ y = none then ⊤ else 0
    | true, x, y => if x = y then 0 else if x = none ∨ y = none then ⊤ else 1
  have hd : ∀ i : Bool, ExtendedPseudoMetric (Option Bool) none (d i) := by
    intro i
    cases i with
    | false =>
        refine
          { nonabsorbing := ⟨some false, Option.some_ne_none false⟩
            dist_self := fun x => by simp [d]
            symm := fun x y => by cases x <;> cases y <;> simp [d]
            triangle := fun x y z => by
              cases x with
              | none => cases y <;> cases z <;> simp [d]
              | some a =>
                  cases y with
                  | none => cases z <;> simp [d]
                  | some b =>
                      cases z with
                      | none => simp [d]
                      | some c => cases a <;> cases b <;> cases c <;> simp [d]
            isolate_bot := fun x hx => by
              cases x with
              | none => exact absurd rfl hx
              | some a => simp [d] }
    | true =>
        exact zeroInfCounterexample_extendedPseudoMetric true
  have hL : idMatrix ∈ RestrictedLipSet d (idOp (bot := (none : Option Bool)))
      zeroInfCounterexampleU := by
    refine ⟨zeroInfCounterexampleU_subset_dom, ?_⟩
    intro x _ y _ j
    rw [Finset.sum_eq_single j]
    · simp [idOp]
    · intro k _ hkj
      rw [idMatrix_apply_ne hkj, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have htop : singleChannelLipConst d (idOp (bot := (none : Option Bool)))
      zeroInfCounterexampleU false true = ⊤ := by
    have hpair := singleChannelLipFeasible_eq_empty_of_zero_pos d (idOp (bot := none))
      zeroInfCounterexampleU false true
      (x := some false) (y := some true)
      (by simp [zeroInfCounterexampleU]) (by simp [zeroInfCounterexampleU])
      (by simp [d]) (by simp [d])
    exact hpair.2
  have h0 : idMatrix false true = 0 := idMatrix_apply_ne (by decide)
  refine ⟨Option Bool, Bool, none, inferInstance, inferInstance, d, hd,
    idOp, zeroInfCounterexampleU, idMatrix, false, true, hL, h0, htop, ?_⟩
  rw [htop, h0]
  exact ENNReal.top_ne_zero

/-! ### 4. Zero-Entry Removal and Row/Column/Diagonal Simplifications (HC02-P25–P28) -/

/--
`HC02-P25` (part 1): If `L_{i → j} = 0`, then `L_{i → j} * d_i(x, y) = 0`
even when `d_i(x, y) = +∞` (by `0 * ∞ = 0` in `ENNReal`).
-/
theorem zero_entry_term_eq_zero {X I : Type}
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) {i j : I}
    (h0 : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by
  rw [h0, zero_mul]

/--
`HC02-P25` (part 2, `DecidableEq`-free form):
If `L_{i → j} = 0`, any finset `s : Finset I` containing all `r ≠ i` (for instance `I \ {i}`)
gives the exact same output-`j` sum, removing input `i` even when `d_i(x, y) = +∞`.
-/
theorem sum_eq_sum_of_zero_entry {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) {i j : I}
    (h0 : L i j = 0) (s : Finset I) (hs : ∀ r : I, r ≠ i → r ∈ s) (x y : X) :
    (∑ k : I, L k j * d k x y) = ∑ k ∈ s, L k j * d k x y := by
  symm
  refine Finset.sum_subset (Finset.subset_univ s) ?_
  intro k _ hks
  have hki : k = i := by
    by_contra hne
    exact hks (hs k hne)
  subst hki
  exact zero_entry_term_eq_zero d L h0 x y

/--
`HC02-P25` (part 2, `Finset.erase` form):
If `L_{i → j} = 0`, the `i`-th input term can be erased from the output-`j` sum.
-/
theorem sum_erase_of_zero_entry {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) {i j : I}
    (h0 : L i j = 0) (x y : X) :
    (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y :=
  sum_eq_sum_of_zero_entry d L h0 (Finset.univ.erase i) (fun r hr => by simp [hr]) x y

/--
`HC02-P25` (certificate inequality form, `DecidableEq`-free):
If `L ∈ ℒ(ϕ)|_U` and `L_{i → j} = 0`, input `d_i` can be omitted from the `d_j` upper bound.
-/
theorem restrictedLip_of_zero_entry_compl {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (h0 : L i j = 0) (s : Finset I) (hs : ∀ r : I, r ≠ i → r ∈ s) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ s, L k j * d k x y := by
  intro x hx y hy
  rw [← sum_eq_sum_of_zero_entry d L h0 s hs x y]
  exact hL.2 x hx y hy j

/--
`HC02-P25` (certificate inequality form with `Finset.univ.erase`):
If `L ∈ ℒ(ϕ)|_U` and `L_{i → j} = 0`, input `d_i` does not participate in the `d_j` upper bound.
-/
theorem restrictedLip_erase_of_zero_entry {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (h0 : L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y :=
  restrictedLip_of_zero_entry_compl d ϕ U hL h0 (Finset.univ.erase i) (fun r hr => by simp [hr])

/--
`HC02-P26` (line 313): If `L ∈ ℒ(ϕ)|_U` and row `j` is supported at a single input `i`
(`∀ k ≠ i, L_{k → j} = 0`, where `i` need not equal `j`), then
`d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)` for all `x, y ∈ U`.
-/
theorem restrictedLip_of_rowSparse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hrow : RowSparse L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [hrow k hki, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hsum]
  exact hL.2 x hx y hy j

/-- Corollary of `HC02-P26`: a row-sparse entry `L_{i → j}` is a feasible single-channel scalar
constant, so `L̲_{i → j}(ϕ; U) ≤ L_{i → j}`. -/
theorem rowSparse_entry_mem_singleChannel {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hrow : RowSparse L i j) :
    L i j ∈ SingleChannelLipFeasible d ϕ U i j ∧
      singleChannelLipConst d ϕ U i j ≤ L i j := by
  have hmem : L i j ∈ SingleChannelLipFeasible d ϕ U i j :=
    restrictedLip_of_rowSparse d ϕ U hL hrow
  exact ⟨hmem, sInf_le hmem⟩

/-- Operator-level consequence of row decoupling (`HC02-P26`): if `ϕ` is row-decoupled
at output `j`, some certificate `L ∈ ℒ(ϕ)|_U` and input `i` yield the scalar bound
`d_j(ϕ(x), ϕ(y)) ≤ L_{i → j} * d_i(x, y)`. -/
theorem isRowDecoupled_scalar_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I)
    (hdec : IsRowDecoupled d ϕ U j) :
    ∃ L ∈ RestrictedLipSet d ϕ U, ∃ i : I,
      RowSparse L i j ∧
      ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  rcases hdec with ⟨L, hL, i, hrow⟩
  exact ⟨L, hL, i, hrow, restrictedLip_of_rowSparse d ϕ U hL hrow⟩

/--
`HC02-P27` (line 315): If `L ∈ ℒ(ϕ)|_U` has column `i` supported at most at output `j`
(`∀ k ≠ j, L_{i → k} = 0`), then for every `k ≠ j` and all `x, y ∈ U`,
`L_{i → k} * d_i(x, y) = 0`, and input `d_i` contributes nothing to the output-`k` bound
(i.e. every `s : Finset I` covering `I \ {i}` already bounds `d_k(ϕ(x), ϕ(y))`).
-/
theorem colSparse_zero_contribution {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hcol : ColSparse L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      L i k * d i x y = 0 ∧
      ∀ s : Finset I, (∀ r : I, r ≠ i → r ∈ s) →
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ r ∈ s, L r k * d r x y := by
  intro k hkj x hx y hy
  have h0 : L i k = 0 := hcol k hkj
  refine ⟨zero_entry_term_eq_zero d L h0 x y, ?_⟩
  intro s hs
  exact restrictedLip_of_zero_entry_compl d ϕ U hL h0 s hs x hx y hy

/-- `Finset.erase` variant of `HC02-P27`. -/
theorem colSparse_erase_bound {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    {i j : I} (hcol : ColSparse L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      L i k * d i x y = 0 ∧
      d k (ϕ.func x) (ϕ.func y) ≤ ∑ r ∈ Finset.univ.erase i, L r k * d r x y := by
  intro k hkj x hx y hy
  have h0 : L i k = 0 := hcol k hkj
  exact ⟨zero_entry_term_eq_zero d L h0 x y,
    restrictedLip_erase_of_zero_entry d ϕ U hL h0 x hx y hy⟩

/--
`HC02-P28` (lines 317–319): If `L ∈ ℒ(ϕ)|_U` is diagonal (`∀ i ≠ j, L_{i → j} = 0`),
then every component `j ∈ I` satisfies the scalar upper bound
`d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)` for all `x, y ∈ U`.
-/
theorem restrictedLip_of_diagonal {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L : GaugeMatrix I} (hL : L ∈ RestrictedLipSet d ϕ U)
    (hdiag : IsDiagonalMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact restrictedLip_of_rowSparse d ϕ U hL ((isDiagonalMatrix_iff_forall_rowSparse L).mp hdiag j)

/-! ### 5. Two-Sided Diagonal Scalar Bounds and Finite Branch (HC02-P29, HC02-P30) -/

/--
OET anchor: h-6a98a58b5bc95360 (`HC02-P29`)
**Lemma (Two-sided scalar bound from a diagonal-only Lip row)**:
Given `L ∈ ℒ(ϕ)|_U` and `K ∈ 𝒦(ϕ)|_U`, assuming ONLY that row `j` of `L` is supported
on the diagonal (`∀ k ≠ j, L_{k → j} = 0`), every `x, y ∈ U` satisfies
`K_{j → j} * d_j(x, y) ≤ d_j(ϕ(x), ϕ(y)) ≤ L_{j → j} * d_j(x, y)`.
-/
theorem diagonal_two_sided_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U)
    (hK : K ∈ CoLipSet d ϕ U)
    (j : I) (hrow : RowSparse L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  refine ⟨?_, restrictedLip_of_rowSparse d ϕ U hL hrow x hx y hy⟩
  calc
    K j j * d j x y
        ≤ ∑ k : I, K k j * d k x y :=
          Finset.single_le_sum (f := fun k => K k j * d k x y)
            (fun _ _ => zero_le _) (Finset.mem_univ j)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
`HC02-P30` (part 1, line 338): If the diagonal-row condition on `L` holds for all `j ∈ I`,
then the two-sided scalar inequality holds simultaneously for every component `j ∈ I`.
-/
theorem componentwise_two_sided_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U)
    (hK : K ∈ CoLipSet d ϕ U)
    (hrow_all : ∀ j : I, RowSparse L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => diagonal_two_sided_bound d ϕ U hL hK j (hrow_all j)

/--
`HC02-P30` (part 2, finite-coefficient branch, line 338):
If in addition `L_{j → j} < ∞` and `K_{j → j} < ∞` for all `j ∈ I`, then the componentwise
two-sided bounds have finite nonnegative real (`NNReal`) scaling coefficients `k, l`.
-/
theorem componentwise_finite_two_sided_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {L K : GaugeMatrix I}
    (hL : L ∈ RestrictedLipSet d ϕ U)
    (hK : K ∈ CoLipSet d ϕ U)
    (hrow_all : ∀ j : I, RowSparse L j j)
    (hL_fin : ∀ j : I, L j j < ⊤)
    (hK_fin : ∀ j : I, K j j < ⊤) :
    ∀ j : I, ∃ k l : NNReal,
      (k : ENNReal) = K j j ∧ (l : ENNReal) = L j j ∧
      ∀ x ∈ U, ∀ y ∈ U,
        (k : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ (l : ENNReal) * d j x y := by
  intro j
  refine ⟨(K j j).toNNReal, (L j j).toNNReal,
    ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne, ?_⟩
  rw [ENNReal.coe_toNNReal (hK_fin j).ne, ENNReal.coe_toNNReal (hL_fin j).ne]
  exact componentwise_two_sided_bound d ϕ U hL hK hrow_all j

/-! ### 6. Positive co-Lip Distinguishability Preservation & Zero-Distance Reflection (HC02-P31, P32) -/

/--
OET anchor: h-f82672ec0dd48f28 (i) (`HC02-P31`)
**Proposition (Distinguishability preservation along positive co-Lip channels)**:
If `K ∈ 𝒦(ϕ)|_U` and `K_{i → j} > 0`, then for all `x, y ∈ U`,
`d_i(x, y) > 0 → d_j(ϕ(x), ϕ(y)) > 0`.
-/
theorem coLip_preserves_distinguishability {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ U)
    {i j : I} (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdpos
  have hmul_pos : 0 < K i j * d i x y := ENNReal.mul_pos hpos.ne' hdpos.ne'
  have hle : K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    calc
      K i j * d i x y
          ≤ ∑ k : I, K k j * d k x y :=
            Finset.single_le_sum (f := fun k => K k j * d k x y)
              (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  exact lt_of_lt_of_le hmul_pos hle

/--
OET anchor: h-f82672ec0dd48f28 (ii) (`HC02-P32`)
**Proposition (Reflection of gauge zero-distance relation from positive diagonal co-Lip)**:
If `K ∈ 𝒦(ϕ)|_U` and `K_{j → j} > 0` for all `j ∈ I`, then for all `x, y ∈ U`,
`ϕ(x) ∼_G ϕ(y) → x ∼_G y`.
-/
theorem coLip_reflects_gaugeZeroRelated {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ U)
    (hdiag_pos : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout : 0 < d j (ϕ.func x) (ϕ.func y) :=
    coLip_preserves_distinguishability d ϕ U hK (hdiag_pos j) x hx y hy hpos
  rw [hrel j] at hout
  exact lt_irrefl 0 hout

end OetCh02
```

```lean filename=Main.lean
import Ch02.MatrixCore
import Ch02.MatrixBounds
import Ch02.ChainBounds
import Ch02.ChannelDecoupling

/-!
# Chapter 2 (`02-operator-bounds.md`) Complete Lean 4 Formalization Entry Point

Imports all target modules formalizing Chapter 2 of *The Operator Evolution Theory*
(historical snapshot `02-operator-bounds.md`):
- `Ch02.MatrixCore`: Gauge matrices, display convention, ordered products, finite operator
  chains, actual recursive domains, and index paths.
- `Ch02.MatrixBounds`: Global/restricted Lipschitz & co-Lipschitz certificate families,
  single-component degeneration, domain monotonicity, entrywise infimum monotonicity,
  two-step composition laws, co-Lip vanishing criterion, and pairwise perturbation bounds.
- `Ch02.ChainBounds`: Stepwise chain data, finite-composition Lip/co-Lip bounds,
  zero-step identity certificates, and path-based zero/positivity product criteria.
- `Ch02.ChannelDecoupling`: Component channels, row/column/diagonal decoupling,
  single-channel Lipschitz constants and counterexample, two-sided diagonal bounds,
  and positive co-Lip distinguishability preservation & zero-distance reflection.
-/
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
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.IsLipMatrix"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.LipSet"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.IsRestrictedLipMatrix"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.RestrictedLipSet"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.lipSet_eq_restrictedLipSet_dom"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.top_entry_mul_zero"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.top_entry_lip_ineq_trivial"
        }
      ],
      "representation": "在 [Fintype I]、d : I → X → X → ENNReal 与保吸收元算子 ϕ : Operator X bot 下，定义全域合法 Lip 矩阵谓词/集合 IsLipMatrix、LipSet（对应 ℒ(ϕ)）与受限合法 Lip 矩阵谓词/集合 IsRestrictedLipMatrix、RestrictedLipSet（对应 ℒ(ϕ)|_U，内含 U ⊆ dom ϕ 与 ∀ x,y ∈ U, ∀ j, d j (ϕ.func x) (ϕ.func y) ≤ ∑ i, L i j * d i x y）。所有矩阵条目与距离均取 ENNReal（满足 0 * ⊤ = 0），并证明 LipSet d ϕ = RestrictedLipSet d ϕ (dom ϕ) 及 +∞ 条目约定。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.IsCoLipMatrix"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.CoLipSet"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.coLipSet_nonempty_of_mem"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.coLipSet_ne_empty_of_mem"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.coLipSet_subset_dom_of_mem"
        }
      ],
      "representation": "定义 IsCoLipMatrix 与证书族 CoLipSet（对应 𝒦(ϕ)|_U），成员资格显式包含 U.Nonempty（等价于 U ≠ ∅）、U ⊆ dom ϕ 以及 ∀ x,y ∈ U, ∀ j, ∑ i, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)；K : GaugeMatrix I 取值于 ENNReal，0 与 ⊤ (+∞) 均为合法条目。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.GaugeMatrix"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.toDisplayMatrix"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.ofDisplayMatrix"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.toDisplayMatrixEquiv"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matMul"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.toDisplayMatrix_matMul"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matMul_assoc"
        }
      ],
      "representation": "以 GaugeMatrix I := I → I → ENNReal 实现输入优先存储（M i j 表示 M_{i → j}）；以 toDisplayMatrix / ofDisplayMatrix / toDisplayMatrixEquiv 对应标准行列矩阵 Matrix I I ENNReal（第 j 行第 i 列为 M i j）；定义 matMul M2 M1 i j = ∑ k, M2 k j * M1 i k 并证明其与显示矩阵乘法完全一致（toDisplayMatrix_matMul）且满足结合律。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.idMatrix"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.idMatrix_apply_eq"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.idMatrix_apply_ne"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.toDisplayMatrix_idMatrix"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matMul_idMatrix"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.idMatrix_matMul"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matProd"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matProd_nil"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matProd_singleton"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.matProd_two"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.toDisplayMatrix_matProd"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finMatProd"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finMatProd_zero"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finMatProd_one"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finMatProd_two"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finMatProd_succ_last"
        }
      ],
      "representation": "定义单位矩阵 idMatrix（δ_{i → j}）并证明与显示单位矩阵一致及左右单位律；定义列表有序乘积 matProd 与 Fin k 索引乘积 finMatProd，施行顺序 [M₁, …, Mₖ] 对应 Mₖ · … · M₁，空乘积为 idMatrix，k = 1 时恒等于唯一矩阵 M 0。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.idOp"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.compOp"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.commonDom2"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.dom_compOp_subset_left"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.operator_image_subset_dom_of_subset_dom_compOp"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.operator_image_compOp"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.applyChain"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.applyChain_eq_operatorChain_reverse"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finChainOp"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.chainDomain"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.chainDomain_zero"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.chainDomain_succ"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.chainDomain_last_eq_operator_image"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.chainDomain_subset_dom"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.LipChainData"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.CoLipChainData"
        }
      ],
      "representation": "定义算子复合 compOp、有限链复合 applyChain / finChainOp（并证明与第1章 OperatorChain 的反转对应 applyChain_eq_operatorChain_reverse）以及递归实际像域 chainDomain（U₁ = startDomain，U_{m+1} = ϕₘ(Uₘ)）。证明 U₁ ⊆ dom cₖ 蕴含每步 Uₘ ⊆ dom ϕₘ（chainDomain_subset_dom）且 U_{k+1} = cₖ(U₁)（chainDomain_last_eq_operator_image）。LipChainData 与 CoLipChainData 仅存储逐步算子、起始域、逐步矩阵及各实际输入域上的单步界，绝不以最终复合界为字段。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.MidIndexSeq"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.midIndexSeqOneUnique"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathNode"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathNode_zero"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathNode_last"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathNode_mid"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathEdgeWeight"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathWeight"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.PathAllPos"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.PathHasZero"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathWeight_one"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathWeight_eq_zero_iff"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.pathWeight_pos_iff"
        },
        {
          "file": "Ch02/MatrixCore.lean",
          "name": "OetCh02.finMatProd_apply_eq_sum_paths"
        }
      ],
      "representation": "以 MidIndexSeq I n := Fin (n - 1) → I 无正性约束地遍历全部中间指标序列（n = 1 时由 midIndexSeqOneUnique 给出唯一空序列）；pathNode 固定起止端 k₀ = i、kₙ = j；pathWeight 为各层边权 pathEdgeWeight 之乘积；PathAllPos 与 PathHasZero 分别为所有边 > 0 与存在某边 = 0；并证明矩阵乘积精确等于全体路径权重之和（finMatProd_apply_eq_sum_paths）。",
      "dependencies": [
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.Channel"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.ChannelIsolated"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.ChannelPosLowerBound"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.RowSparse"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.MatrixRowDecoupled"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.IsRowDecoupled"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.ColSparse"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.MatrixColDecoupled"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.IsColDecoupled"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.IsDiagonalMatrix"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.IsCompletelyDecoupled"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.isDiagonalMatrix_iff_forall_rowSparse"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.isDiagonalMatrix_iff_forall_colSparse"
        }
      ],
      "representation": "定义分量通道 Channel I := I × I、通道隔离/正下界传递谓词、单行稀疏 RowSparse L i j (∀ k ≠ i, L k j = 0) 与行解耦 MatrixRowDecoupled / IsRowDecoupled、单列稀疏 ColSparse L i j (∀ k ≠ j, L i k = 0) 与列解耦 MatrixColDecoupled / IsColDecoupled、以及对角矩阵 IsDiagonalMatrix (∀ i ≠ j, L i j = 0) 与完全解耦体系 IsCompletelyDecoupled。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.SingleChannelLipFeasible"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.singleChannelLipConst"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.singleChannelLipConst_eq_top_of_empty"
        }
      ],
      "representation": "独立于任何 Lip 矩阵证书条目定义单通道可行标量族 SingleChannelLipFeasible d ϕ U i j = {λ : ENNReal | ∀ x,y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ λ * d i x y} 与单通道 Lip 常数 singleChannelLipConst d ϕ U i j = sInf (SingleChannelLipFeasible d ϕ U i j)，满足 sInf ∅ = ⊤。另在同文件以 exists_singleChannelLipConst_ne_lipMatrix_entry 显式见证单通道常数与 Lip 矩阵条目为不同对象。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.isLipMatrix_iff_scalar_of_singleton"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.isLipMatrix_iff_scalar_of_card_eq_one"
        }
      ],
      "representation": "对应注 #h-c4369c63c86cbacf：当指标集为单元素 I = {i}（以 ∀ k, k = i 或 Fintype.card I = 1 刻画）时，证明 L ∈ LipSet d ϕ 充要于 ∀ x,y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.lipSet_subset_restrictedLipSet"
        }
      ],
      "representation": "对应原文第 25 行：对任意 U ⊆ dom ϕ，证明 LipSet d ϕ ⊆ RestrictedLipSet d ϕ U。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.restrictedLipSet_antitone"
        }
      ],
      "representation": "对应原文第 25 行：对任意 U ⊆ V（特别含 U ⊆ V ⊆ dom ϕ），证明 RestrictedLipSet d ϕ V ⊆ RestrictedLipSet d ϕ U（评估域缩小则证书族反单调扩大）。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.entrywiseLipInf"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.entrywiseLipInf_mono"
        }
      ],
      "representation": "对应原文第 25 行：定义逐条目下确界 entrywiseLipInf d ϕ U i j = sInf {c | ∃ M ∈ RestrictedLipSet d ϕ U, M i j = c}，并证明 U ⊆ V 蕴含 entrywiseLipInf d ϕ U i j ≤ entrywiseLipInf d ϕ V i j。",
      "dependencies": [
        "HC02-D01",
        "HC02-P03"
      ]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.restrictedLipSet_comp"
        }
      ],
      "representation": "对应命题 #h-193cebcc1a7f9259：设 U₁ ⊆ dom (compOp ϕ2 ϕ1) 且 U₂ = operator_image ϕ1 U₁，若 L1 ∈ RestrictedLipSet d ϕ1 U₁ 且 L2 ∈ RestrictedLipSet d ϕ2 U₂，则 matMul L2 L1 ∈ RestrictedLipSet d (compOp ϕ2 ϕ1) U₁。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.coLip_entry_eq_zero_of_pair"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.coLip_entry_eq_zero_of_pair_on"
        }
      ],
      "representation": "对应注 #h-88784dcbfff0ea66：若存在 x,y ∈ dom ϕ 使 d j (ϕ.func x) (ϕ.func y) = 0 且 0 < d i x y，则任一全域 co-Lip 证书 K ∈ CoLipSet d ϕ (dom ϕ) 必满足 K i j = 0（亦给出一般受限域版本 coLip_entry_eq_zero_of_pair_on）。",
      "dependencies": [
        "HC02-D02"
      ]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.coLipSet_comp"
        }
      ],
      "representation": "对应命题 #h-0f256e6f1d38a612：在 U₁ ⊆ dom (compOp ϕ2 ϕ1) 与 U₂ = operator_image ϕ1 U₁ 下，若 K1 ∈ CoLipSet d ϕ1 U₁ 且 K2 ∈ CoLipSet d ϕ2 U₂，则 matMul K2 K1 ∈ CoLipSet d (compOp ϕ2 ϕ1) U₁（由 CoLipSet 定义自动含 U₁.Nonempty）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_dist_forward"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_dist_forward_add"
        }
      ],
      "representation": "对应命题 #h-b959b42f25710105 (i) 正向：在扩展伪度量族 hd、U ⊆ commonDom2 ϕ1 ϕ2 与 ∀ z ∈ U, j, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j 条件下，证明 d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j（及等价展开形式 + δ j + δ j）。",
      "dependencies": [
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_dist_backward"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_dist_backward_add"
        }
      ],
      "representation": "对应命题 #h-b959b42f25710105 (i) 反向：相同前提下交换 ϕ1, ϕ2，证明 d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j（及 + δ j + δ j 形式）。",
      "dependencies": [
        "HC02-D05",
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_lip_bridge"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_lip_bridge_swap"
        }
      ],
      "representation": "对应命题 #h-b959b42f25710105 (ii) 及对称说明：若另有 L1 ∈ RestrictedLipSet d ϕ1 U，则 d j (ϕ2.func x) (ϕ2.func y) ≤ (∑ i, L1 i j * d i x y) + 2 * δ j（并含 ϕ1, ϕ2 交换版本）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D05",
        "HC02-P08",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_coLip_bridge"
        },
        {
          "file": "Ch02/MatrixBounds.lean",
          "name": "OetCh02.perturbation_coLip_bridge_swap"
        }
      ],
      "representation": "对应命题 #h-b959b42f25710105 (iii) 及对称说明：若另有 K1 ∈ CoLipSet d ϕ1 U，则 ∑ i, K1 i j * d i x y ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j（并含 ϕ1, ϕ2 交换版本）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D05",
        "HC02-P08",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.finChain_lip_bound"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.finChain_lip_bound_unpacked"
        }
      ],
      "representation": "对应推论 #h-c80171fa685dc795 (i)：对任意长度 k ≥ 1 的 LipChainData（逐步矩阵在实际像域 Uₘ 上合法），按两步复合律做有限归纳，证明 finMatProd chain.stepMatrices ∈ RestrictedLipSet d (finChainOp chain.ops) chain.startDomain。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04",
        "HC02-D05",
        "HC02-P05"
      ]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.finChain_coLip_bound"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.finChain_coLip_bound_unpacked"
        }
      ],
      "representation": "对应推论 #h-c80171fa685dc795 (ii)：对任意长度 k ≥ 1 的 CoLipChainData（每步 CoLipSet 均含非空性），按两步 co-Lip 复合律做有限归纳，证明 finMatProd chain.stepMatrices ∈ CoLipSet d (finChainOp chain.ops) chain.startDomain。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04",
        "HC02-D05",
        "HC02-P07"
      ]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.idMatrix_sum_eq_dist"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.idMatrix_mem_restrictedLipSet"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.zeroStep_lip_bound"
        }
      ],
      "representation": "对应注 #h-11006ddd8c43bfec 的 Lip 部分：k = 0 时 c₀ = idOp、空乘积 = idMatrix，由 idMatrix_sum_eq_dist 证明对任意（非空）U ⊆ dom idOp 有 idMatrix ∈ RestrictedLipSet d idOp U（及 finMatProd L ∈ RestrictedLipSet d (finChainOp ϕ) U）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04",
        "HC02-D05"
      ]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.idMatrix_mem_coLipSet"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.zeroStep_coLip_bound"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.idMatrix_mem_restrictedLipSet_inter_coLipSet"
        }
      ],
      "representation": "对应注 #h-11006ddd8c43bfec 的 co-Lip 与交集部分：对同一非空 U ⊆ dom idOp，证明 idMatrix ∈ CoLipSet d idOp U（及零步链形式 zeroStep_coLip_bound 与交集形式 I ∈ ℒ(id)|_U ∩ 𝒦(id)|_U）。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04",
        "HC02-D05",
        "HC02-P14"
      ]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.finMatProd_apply_eq_zero_iff"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.lipChain_prod_entry_eq_zero_iff"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.lipChain_prod_entry_eq_zero_one"
        }
      ],
      "representation": "对应命题 #h-e4154c34e95d3c23 (i)：在长度 n ≥ 1 的实际 Lip 证书链 LipChainData bot d n 下，由路径和展开证明 finMatProd chain.stepMatrices i j = 0 充要于对所有 mid : MidIndexSeq I n 均有 PathHasZero n chain.stepMatrices i j mid；并以 lipChain_prod_entry_eq_zero_one 显式给出 n = 1 退化为 L^{(1)}_{i → j} = 0。",
      "dependencies": [
        "HC02-D04",
        "HC02-D05",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.finMatProd_apply_pos_iff"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.coLipChain_prod_entry_pos_iff"
        },
        {
          "file": "Ch02/ChainBounds.lean",
          "name": "OetCh02.coLipChain_prod_entry_pos_one"
        }
      ],
      "representation": "对应命题 #h-e4154c34e95d3c23 (ii)：在长度 n ≥ 1 的实际 co-Lip 证书链 CoLipChainData bot d n 下，证明 0 < finMatProd chain.stepMatrices i j 充要于存在 mid : MidIndexSeq I n 满足 PathAllPos n chain.stepMatrices i j mid；并以 coLipChain_prod_entry_pos_one 显式给出 n = 1 唯一空序列退化为 0 < K^{(1)}_{i → j}。",
      "dependencies": [
        "HC02-D04",
        "HC02-D05",
        "HC02-D06",
        "HC02-P16"
      ]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.singleChannelLipFeasible_eq_empty_of_zero_pos"
        }
      ],
      "representation": "对应原文第 275 行：若存在 x,y ∈ U 使 d i x y = 0 且 0 < d j (ϕ.func x) (ϕ.func y)，则因 ∀ λ : ENNReal 有 λ * 0 = 0（含 λ = ⊤），故 SingleChannelLipFeasible d ϕ U i j = ∅ 且 singleChannelLipConst d ϕ U i j = ⊤。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.singleChannelLipConst_mem_of_pos_lt_top"
        }
      ],
      "representation": "对应原文第 277–297 行：当 0 < a < ⊤（a = singleChannelLipConst d ϕ U i j）时，严格沿原文对 B = d i x y 分 B = 0、B = ⊤ 与 0 < B < ⊤ 三类情形证明 a ∈ SingleChannelLipFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P21"
      ]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.singleChannelLipFeasible_upward_closed"
        }
      ],
      "representation": "对应原文第 283 行：若 lam0 ∈ SingleChannelLipFeasible d ϕ U i j 且 lam0 ≤ lam1，则 lam1 ∈ SingleChannelLipFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.mem_singleChannelLipFeasible_of_const_lt"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.mem_singleChannelLipFeasible_of_gt_pos_finite"
        }
      ],
      "representation": "对应原文第 283 行：在 0 < a < ⊤ 语境（以及一般 a < lam，允许 lam = ⊤）下，由下确界定义与向上封闭性证明任意 lam > a 均属于 SingleChannelLipFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P20"
      ]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.mem_singleChannelLipFeasible_of_const_eq_zero"
        }
      ],
      "representation": "对应注 #h-57de7918859a9de2 第 301、305 行：当 singleChannelLipConst d ϕ U i j = 0 时，任意满足 0 < lam < ⊤ 的有限正常数均属于 SingleChannelLipFeasible d ϕ U i j。",
      "dependencies": [
        "HC02-D08",
        "HC02-P21"
      ]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexampleDist"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexample_extendedPseudoMetric"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexampleU"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexampleU_nonempty"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexampleU_subset_dom"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexample_const_eq_zero"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zeroInfCounterexample_zero_not_mem"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.exists_zero_singleChannelLipConst_not_attained"
        }
      ],
      "representation": "构造合法扩展规范空间（X = Option Bool，bot = none，I = Bool，两个分量均证明满足 ExtendedPseudoMetric）、合法算子 ϕ = idOp 与非空合法子集 U = {some false, some true} ⊆ dom idOp，证明通道 (false, true) 的单通道下确界为 0 但 0 ∉ SingleChannelLipFeasible（因 d_false = ⊤、0 * ⊤ = 0 < 1 = d_true）。",
      "dependencies": [
        "HC02-D05",
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.singleChannelLipConst_lt_top_iff"
        }
      ],
      "representation": "对应注 #h-57de7918859a9de2 第 301–307 行：证明 singleChannelLipConst d ϕ U i j < ⊤ 充要于存在有限常数 lam < ⊤ 属于 SingleChannelLipFeasible d ϕ U i j（正向分 a = 0 与 0 < a < ⊤ 两支，分别由 HC02-P22 与 HC02-P19 给出有限可行常数）。",
      "dependencies": [
        "HC02-D08",
        "HC02-P19",
        "HC02-P22"
      ]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.zero_entry_term_eq_zero"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.sum_eq_sum_of_zero_entry"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.sum_erase_of_zero_entry"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.restrictedLip_of_zero_entry_compl"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.restrictedLip_erase_of_zero_entry"
        }
      ],
      "representation": "对应原文第 15 与 311 行：当 L i j = 0 时，对任意 d i x y : ENNReal（含 ⊤）均有 L i j * d i x y = 0，故输出分量 j 的求和中可移除输入项 i（提供一般有限集覆盖形式及 Finset.univ.erase i 形式，并在合法 Lip 证书下给出删除该项后的上界）。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.restrictedLip_of_rowSparse"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.rowSparse_entry_mem_singleChannel"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.isRowDecoupled_scalar_bound"
        }
      ],
      "representation": "对应原文第 313 行：对任意 i, j ∈ I（不要求 i = j），若 L ∈ RestrictedLipSet d ϕ U 且 RowSparse L i j（∀ k ≠ i, L k j = 0），则 ∀ x,y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y；并给出与单通道可行集及 IsRowDecoupled 的推论。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.colSparse_zero_contribution"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.colSparse_erase_bound"
        }
      ],
      "representation": "对应原文第 315 行：若 L ∈ RestrictedLipSet d ϕ U 且输入 i 列满足 ColSparse L i j（∀ k ≠ j, L i k = 0），则对一切 k ≠ j 与 x,y ∈ U，L i k * d i x y = 0 且输出分量 k 的上界可在移除输入 i 后成立，即输入 i 在该证书中至多向输出 j 贡献。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-P25"
      ]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.restrictedLip_of_diagonal"
        }
      ],
      "representation": "对应原文第 317–319 行：若 L ∈ RestrictedLipSet d ϕ U 且 IsDiagonalMatrix L，则对所有 j ∈ I 及 x,y ∈ U 均有 d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.diagonal_two_sided_bound"
        }
      ],
      "representation": "对应引理 #h-6a98a58b5bc95360：给定 L ∈ RestrictedLipSet d ϕ U 与 K ∈ CoLipSet d ϕ U，仅假设 RowSparse L j j（不对 K 施加稀疏假设），证明 ∀ x,y ∈ U, K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧ d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.componentwise_two_sided_bound"
        },
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.componentwise_finite_two_sided_bound"
        }
      ],
      "representation": "对应原文第 338 行：若 ∀ j, RowSparse L j j，则 componentwise_two_sided_bound 同时给出所有分量的标量双侧界；若进一步有 ∀ j, L j j < ⊤ 且 ∀ j, K j j < ⊤，则 componentwise_finite_two_sided_bound 给出显式有限非负实数 NNReal 标量系数 k, l 实现该双侧界。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D07",
        "HC02-P29"
      ]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.coLip_preserves_distinguishability"
        }
      ],
      "representation": "对应命题 #h-f82672ec0dd48f28 (i) 及第 311 行：给定 K ∈ CoLipSet d ϕ U 且 0 < K i j，证明对所有 x,y ∈ U，0 < d i x y 蕴含 0 < d j (ϕ.func x) (ϕ.func y)。",
      "dependencies": [
        "HC02-D02"
      ]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {
          "file": "Ch02/ChannelDecoupling.lean",
          "name": "OetCh02.coLip_reflects_gaugeZeroRelated"
        }
      ],
      "representation": "对应命题 #h-f82672ec0dd48f28 (ii)：给定 K ∈ CoLipSet d ϕ U 且 ∀ j, 0 < K j j，证明对所有 x,y ∈ U，GaugeZeroRelated d (ϕ.func x) (ϕ.func y) 蕴含 GaugeZeroRelated d x y（严格复用第1章 GaugeZeroRelated）。",
      "dependencies": [
        "HC02-D02",
        "HC02-P31"
      ]
    }
  ]
}
```

### 完成度与对齐确认

- **完整性与严格对齐**：**已经完整完成且严格对齐整章**（`source/02-operator-bounds.md` 全文及 `obligations.json` 全部 **40/40** 项义务均已形式化、证明并通过本地 Lean 4.29.1 内核编译检查，零错误、零警告）。
- **验证与公理审计结果**：
  - 全部 5 份目标模块（[Ch02/MatrixCore.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/Ch02/MatrixCore.lean)、[Ch02/MatrixBounds.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/Ch02/MatrixBounds.lean)、[Ch02/ChainBounds.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/Ch02/ChainBounds.lean)、[Ch02/ChannelDecoupling.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/Ch02/ChannelDecoupling.lean)、[Main.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/Main.lean)）在固定前置模块 `formal_oet/`（未作任何修改或覆盖）与固定 Mathlib 环境下全部无错无警告通过编译。
  - 对 [alignment.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/alignment.json) 中列出的全部 146 项声明（及附加分离见证定理共 147 项声明）执行了 `#print axioms` 内核公理审计，仅依赖允许的标准公理 `propext`、`Classical.choice`、`Quot.sound`，无任何 `sorry`、`admit`、自定义公理或跳过内核检查机制。
  - [alignment.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/HCH02/physical-2/session/work/alignment.json) 已通过自动化检查：恰好覆盖全部 40 个义务 ID、所有声明真实存在、依赖图为无环 DAG。
- **未完成或未确认的范围**：**无**。