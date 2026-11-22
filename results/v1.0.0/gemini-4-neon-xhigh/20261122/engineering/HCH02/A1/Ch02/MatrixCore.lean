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
