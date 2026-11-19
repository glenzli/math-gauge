{}
已完成 [obligations.json](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v6/attempts/LCH02/physical-1/session/work/obligations.json) 全部 20 项义务（`CH02-D01`–`CH02-D06`、`CH02-P01`–`CH02-P14`）的 Lean 4.29.1 形式化与内核验证，未修改冻结前置模块 [gauge_space.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v6/attempts/LCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean) 与 [operator_space.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v6/attempts/LCH02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean)，未使用 `sorry`、`admit` 或额外公理（仅依赖标准逻辑公理 `propext`、`Classical.choice`、`Quot.sound`）。交付文件亦同步保存在 [OperatorBounds.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v6/attempts/LCH02/physical-1/session/work/LCH02/OperatorBounds.lean)、[Main.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v6/attempts/LCH02/physical-1/session/work/Main.lean) 与 [alignment.json](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v6/attempts/LCH02/physical-1/session/work/alignment.json)。

> **理论来源署名**：Zhe Li (Glen Li / glenzli), ORCID `https://orcid.org/0009-0006-6536-3453`, *The Operator Evolution Theory*, `https://glenzli.com/books/oet/`, `https://gitlab.com/glenzli/oet-public`, CC BY 4.0。

```lean filename=LCH02/OperatorBounds.lean
/-
Theoretical source attribution:
Zhe Li (also known as Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, Chapter 2 (Operator Bounds, §2.1),
https://glenzli.com/books/oet/, https://gitlab.com/glenzli/oet-public,
licensed under CC BY 4.0 (https://creativecommons.org/licenses/by/4.0/).
Lean 4 formalization of the LCH02 obligation ledger.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

open formal_oet.vol_01.ch_01_foundations

/-!
# Chapter 2: Operator Bounds (§2.1 Matrix Bounds and Finite Composition)

This module formalizes all 20 obligations (`CH02-D01` through `CH02-D06` and
`CH02-P01` through `CH02-P14`) specified in `obligations.json` for case `LCH02`.
-/

section DomainHelpers

/-- Membership in the domain of a two-step composite operator `ϕ₂ * ϕ₁` implies
membership in `dom ϕ₁` and that the `ϕ₁`-image lies in `dom ϕ₂`. -/
theorem mem_dom_comp_iff {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (x : X) :
    x ∈ dom (ϕ₂ * ϕ₁) ↔ x ∈ dom ϕ₁ ∧ ϕ₁.func x ∈ dom ϕ₂ := by
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    intro hbot
    apply hx
    change ϕ₂.func (ϕ₁.func x) = bot
    rw [hbot, ϕ₂.preserves_bot]
  · rintro ⟨_, hx₂⟩
    exact hx₂

/-- If `U₁ ⊆ dom (ϕ₂ * ϕ₁)`, then `U₁ ⊆ dom ϕ₁` and the exact intermediate image
`U₂ = ϕ₁(U₁)` satisfies `U₂ ⊆ dom ϕ₂`. -/
theorem subset_dom_and_image_subset_dom_of_subset_dom_comp {X : Type} {bot : X}
    {ϕ₁ ϕ₂ : Operator X bot} {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) :
    U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ((mem_dom_comp_iff ϕ₁ ϕ₂ x).mp (hU₁ hx)).1
  · rintro y ⟨x, hx, rfl⟩
    exact ((mem_dom_comp_iff ϕ₁ ϕ₂ x).mp (hU₁ hx)).2

end DomainHelpers

/-! ## CH02-D03: Input/Output Matrix Index Convention and Multiplication -/

/-- Extended nonnegative matrix over index type `I`, following the textbook row/column
convention where rows index output components `j : I` and columns index input components `i : I`. -/
abbrev GaugeMatrix (I : Type) : Type := Matrix I I ENNReal

/-- Input-to-output entry accessor `M_{i → j} := (M)_{j i}` (row `j`, column `i`). -/
def ioEntry {I : Type} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

/-- Construct a `GaugeMatrix I` from an input-to-output channel specification `(i, j) ↦ M_{i → j}`. -/
def ofIOEntry {I : Type} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of fun j i => f i j

@[simp]
theorem ioEntry_ofIOEntry {I : Type} (f : I → I → ENNReal) (i j : I) :
    ioEntry (ofIOEntry f) i j = f i j := rfl

@[simp]
theorem ofIOEntry_ioEntry {I : Type} (M : GaugeMatrix I) :
    ofIOEntry (ioEntry M) = M := rfl

/-- Entrywise expansion of algebraic matrix multiplication under the `i → j` convention:
`(M₂ * M₁)_{i → j} = ∑ k, M₂_{k → j} * M₁_{i → k}`. -/
theorem ioEntry_mul {I : Type} [Fintype I]
    (M₂ M₁ : GaugeMatrix I) (i j : I) :
    ioEntry (M₂ * M₁) i j = ∑ k : I, ioEntry M₂ k j * ioEntry M₁ i k :=
  Matrix.mul_apply

/-! ## CH02-D01: Global and Restricted Lipschitz Matrix Predicates and Certificate Families -/

/-- Global Lipschitz matrix predicate on `dom ϕ`:
for all `x, y ∈ dom ϕ` and `j : I`, `d_j(ϕ(x), ϕ(y)) ≤ ∑ i, L_{i → j} * d_i(x, y)`. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, ioEntry L i j * d i x y

/-- Global Lipschitz certificate family `mathscr_L(ϕ)`. -/
def LipCertFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- Subset-restricted Lipschitz matrix predicate on `U ⊆ dom ϕ`:
requires `U ⊆ dom ϕ` and the Lipschitz inequality for all `x, y ∈ U` and `j : I`. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, ioEntry L i j * d i x y

/-- Subset-restricted Lipschitz certificate family `mathscr_L(ϕ)|_U`. -/
def RestrictedLipCertFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

/-- Restricting the Lipschitz certificate family to `dom ϕ` recovers `mathscr_L(ϕ)`. -/
@[simp]
theorem restrictedLipCertFamily_dom_eq {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    RestrictedLipCertFamily d ϕ (dom ϕ) = LipCertFamily d ϕ := by
  ext L
  simp [RestrictedLipCertFamily, IsRestrictedLipMatrix, LipCertFamily, IsLipMatrix]

/-! ## CH02-D02: Restricted co-Lipschitz Matrix Predicate (with Nonemptiness) and Certificate Family -/

/-- Subset-restricted co-Lipschitz matrix predicate on a nonempty subset `U ⊆ dom ϕ`:
includes `U.Nonempty`, `U ⊆ dom ϕ`, and for all `x, y ∈ U` and `j : I`,
`∑ i, K_{i → j} * d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))`. -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    (∑ i : I, ioEntry K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

/-- Subset-restricted co-Lipschitz certificate family `mathscr_K(ϕ)|_U` (carrying `U.Nonempty`). -/
def RestrictedCoLipCertFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

/-! ## CH02-D04: Identity Matrix, Empty Product, and Ordered Nonempty Product -/

/-- Identity matrix `I` on gauge components (`I_{i → j} = 1` if `i = j`, else `0`). -/
noncomputable def idMatrix {I : Type} : GaugeMatrix I := by
  classical
  exact (1 : Matrix I I ENNReal)

theorem ioEntry_idMatrix {I : Type} [DecidableEq I] (i j : I) :
    ioEntry idMatrix i j = if i = j then 1 else 0 := by
  classical
  simp [ioEntry, idMatrix, Matrix.one_apply, eq_comm]

@[simp]
theorem ioEntry_idMatrix_self {I : Type} (i : I) :
    ioEntry idMatrix i i = 1 := by
  classical
  simp [ioEntry, idMatrix]

theorem ioEntry_idMatrix_of_ne {I : Type} {i j : I} (h : i ≠ j) :
    ioEntry idMatrix i j = 0 := by
  classical
  simp [ioEntry, idMatrix, h.symm]

/-- Empty matrix composition product (`k = 0`), defined as the identity matrix `idMatrix`. -/
noncomputable def emptyMatrixProd {I : Type} : GaugeMatrix I :=
  idMatrix

/-- General `k`-step ordered matrix product `M^{(k)} * ⋯ * M^{(1)}` for `k ≥ 0`,
with `k = 0` yielding `emptyMatrixProd = idMatrix`. -/
noncomputable def matrixChainProd {I : Type} [Fintype I] :
    (k : ℕ) → (Fin k → GaugeMatrix I) → GaugeMatrix I
  | 0, _ => emptyMatrixProd
  | k + 1, M => M (Fin.last k) * matrixChainProd k (M ∘ Fin.castSucc)

@[simp]
theorem matrixChainProd_zero {I : Type} [Fintype I]
    (M : Fin 0 → GaugeMatrix I) :
    matrixChainProd 0 M = idMatrix := rfl

@[simp]
theorem matrixChainProd_succ {I : Type} [Fintype I]
    (k : ℕ) (M : Fin (k + 1) → GaugeMatrix I) :
    matrixChainProd (k + 1) M = M (Fin.last k) * matrixChainProd k (M ∘ Fin.castSucc) := rfl

/-- Ordered nonempty matrix product `M^{(n)} * ⋯ * M^{(1)}` for `n ≥ 1` (`1 ≤ n`).
When `n = 1`, this evaluates directly to `M^{(1)}`. -/
noncomputable def nonemptyMatrixProd {I : Type} [Fintype I] :
    (n : ℕ) → (hn : 1 ≤ n) → (Fin n → GaugeMatrix I) → GaugeMatrix I
  | 0, hn, _ => absurd hn (Nat.not_succ_le_zero 0)
  | 1, _, M => M ⟨0, Nat.zero_lt_one⟩
  | m + 2, _, M =>
      M (Fin.last (m + 1)) *
        nonemptyMatrixProd (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) (M ∘ Fin.castSucc)

@[simp]
theorem nonemptyMatrixProd_one {I : Type} [Fintype I]
    (hn : 1 ≤ 1) (M : Fin 1 → GaugeMatrix I) :
    nonemptyMatrixProd 1 hn M = M 0 := rfl

theorem nonemptyMatrixProd_succ {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n + 1) (M : Fin (n + 1) → GaugeMatrix I) :
    nonemptyMatrixProd (n + 1) hn' M =
      M (Fin.last n) * nonemptyMatrixProd n hn (M ∘ Fin.castSucc) := by
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ m => rfl

@[simp]
theorem nonemptyMatrixProd_two {I : Type} [Fintype I]
    (hn : 1 ≤ 2) (M : Fin 2 → GaugeMatrix I) :
    nonemptyMatrixProd 2 hn M = M 1 * M 0 := rfl

/-- For `n ≥ 1`, the ordered nonempty matrix product agrees with `matrixChainProd`. -/
theorem nonemptyMatrixProd_eq_matrixChainProd {I : Type} [Fintype I] :
    ∀ (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I),
      nonemptyMatrixProd n hn M = matrixChainProd n M
  | 0, hn, _ => absurd hn (Nat.not_succ_le_zero 0)
  | 1, _, M => by
      classical
      simp [nonemptyMatrixProd, matrixChainProd, emptyMatrixProd, idMatrix]
  | m + 2, _, M => by
      have ih := nonemptyMatrixProd_eq_matrixChainProd (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)) (M ∘ Fin.castSucc)
      change M (Fin.last (m + 1)) *
          nonemptyMatrixProd (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) (M ∘ Fin.castSucc) =
        M (Fin.last (m + 1)) * matrixChainProd (m + 1) (M ∘ Fin.castSucc)
      rw [ih]

/-! ## CH02-D05: Actual Intermediate Image Domains and Chain Representation Correspondence -/

/-- Step-indexed finite composite operator `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1` (`c_0 = id_X`),
where `ϕ m` represents step `m + 1` in execution order (`m : Fin k`). -/
def stepChainComp {X : Type} {bot : X} :
    (k : ℕ) → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => operator_identity
  | k + 1, ϕ => ϕ (Fin.last k) * stepChainComp k (ϕ ∘ Fin.castSucc)

@[simp]
theorem stepChainComp_zero {X : Type} {bot : X} (ϕ : Fin 0 → Operator X bot) :
    stepChainComp 0 ϕ = operator_identity := rfl

@[simp]
theorem stepChainComp_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) :
    stepChainComp (k + 1) ϕ = ϕ (Fin.last k) * stepChainComp k (ϕ ∘ Fin.castSucc) := rfl

@[simp]
theorem stepChainComp_one {X : Type} {bot : X} (ϕ : Fin 1 → Operator X bot) :
    stepChainComp 1 ϕ = ϕ 0 := by
  change ϕ 0 * (1 : Operator X bot) = ϕ 0
  exact mul_one (ϕ 0)

/-- Correspondence between step-indexed `stepChainComp` and `OperatorChain` from
`formal_oet.vol_01.ch_01_foundations.operator_space`:
`c_k = ϕ_k ∘ ⋯ ∘ ϕ_1` equals `OperatorChain` applied to the reversed step list `[ϕ_k, …, ϕ_1]`. -/
theorem stepChainComp_eq_operatorChain_reverse {X : Type} {bot : X} :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot),
      stepChainComp k ϕ = OperatorChain (List.ofFn ϕ).reverse
  | 0, _ => rfl
  | k + 1, ϕ => by
      rw [stepChainComp_succ, stepChainComp_eq_operatorChain_reverse k (ϕ ∘ Fin.castSucc)]
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
      rfl

/-- Inverse correspondence: `OperatorChain ϕs` on a composition-order list `ϕs` equals
`stepChainComp` on the execution-order reversed indexing. -/
theorem operatorChain_eq_stepChainComp {X : Type} {bot : X}
    (ϕs : List (Operator X bot)) :
    OperatorChain ϕs =
      stepChainComp ϕs.length (fun m => ϕs.reverse[m.1]'(by simp)) := by
  rw [stepChainComp_eq_operatorChain_reverse]
  congr 1
  have hfn : (List.ofFn fun m : Fin ϕs.length => ϕs.reverse[m.1]'(by simp)) = ϕs.reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp
  rw [hfn, List.reverse_reverse]

/-- Actual intermediate image domains `U_1, U_2, …, U_{k+1}` along a `k`-step chain:
`U_1` at index `0`, and `U_{m+1} = ϕ_m(U_m)` at index `m.succ`. -/
def stepDomain {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕ m) Um)

@[simp]
theorem stepDomain_zero {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) :
    stepDomain k ϕ U₁ 0 = U₁ := rfl

@[simp]
theorem stepDomain_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    stepDomain k ϕ U₁ m.succ = operator_image (ϕ m) (stepDomain k ϕ U₁ m.castSucc) := by
  simp [stepDomain]

/-- Prefix stability of intermediate image domains when extending a chain by one step. -/
theorem stepDomain_castSucc_succ {X : Type} {bot : X}
    (k : ℕ) (ϕ : Fin (k + 1) → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) :
    stepDomain (k + 1) ϕ U₁ m.castSucc = stepDomain k (ϕ ∘ Fin.castSucc) U₁ m := by
  refine Fin.induction ?_ ?_ m
  · simp
  · intro r ih
    rw [← Fin.succ_castSucc, stepDomain_succ, stepDomain_succ, ih]
    rfl

/-- Exact terminal image identity: `U_{k+1} = c_k(U_1)`. -/
theorem stepDomain_last {X : Type} {bot : X} :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) (U₁ : Set X),
      stepDomain k ϕ U₁ (Fin.last k) = operator_image (stepChainComp k ϕ) U₁
  | 0, _, U₁ => by
      change U₁ = id '' U₁
      simp
  | k + 1, ϕ, U₁ => by
      have hlast : (Fin.last (k + 1)) = (Fin.last k).succ := rfl
      rw [hlast, stepDomain_succ, stepDomain_castSucc_succ,
        stepDomain_last k (ϕ ∘ Fin.castSucc) U₁]
      simp [operator_image, Set.image_image]
      rfl

/-- Domain containment propagation along a chain:
if `U₁ ⊆ dom (c_k)`, then every actual intermediate input domain satisfies `U_m ⊆ dom (ϕ_m)`. -/
theorem stepDomain_subset_dom {X : Type} {bot : X} :
    ∀ (k : ℕ) (ϕ : Fin k → Operator X bot) {U₁ : Set X},
      U₁ ⊆ dom (stepChainComp k ϕ) →
      ∀ m : Fin k, stepDomain k ϕ U₁ m.castSucc ⊆ dom (ϕ m)
  | 0, _, _, _, m => Fin.elim0 m
  | k + 1, ϕ, U₁, hU₁, m => by
      rw [stepChainComp_succ] at hU₁
      rcases subset_dom_and_image_subset_dom_of_subset_dom_comp hU₁ with ⟨hU₁_pre, hUk_last⟩
      refine Fin.lastCases ?_ ?_ m
      · rw [stepDomain_castSucc_succ, stepDomain_last]
        exact hUk_last
      · intro r
        rw [stepDomain_castSucc_succ]
        exact stepDomain_subset_dom k (ϕ ∘ Fin.castSucc) hU₁_pre r

/-! ## CH02-D06: Finite Index Paths and All-Positive Path Predicate -/

/-- Endpoint-pinned index path `(k_0, k_1, …, k_n)` of length `n` in `I` with
`k_0 = i` and `k_n = j`. -/
@[ext]
structure IndexPath (I : Type) (n : ℕ) (i j : I) where
  vertex : Fin (n + 1) → I
  start_eq : vertex 0 = i
  end_eq : vertex (Fin.last n) = j

/-- Equivalence between endpoint-pinned paths `IndexPath I n i j` (for `n ≥ 1`) and
sequences of `n - 1` intermediate indices `(k_1, …, k_{n-1})`. -/
def indexPathEquivIntermediate {I : Type} (n : ℕ) (hn : 1 ≤ n) (i j : I) :
    IndexPath I n i j ≃ (Fin (n - 1) → I) where
  toFun p := fun r => p.vertex ⟨r.1 + 1, by omega⟩
  invFun ks :=
    { vertex := fun r =>
        if hr0 : r.1 = 0 then i
        else if hrn : r.1 = n then j
        else ks ⟨r.1 - 1, by omega⟩
      start_eq := by simp
      end_eq := by
        have hn0 : n ≠ 0 := by omega
        simp [Fin.last, hn0] }
  left_inv p := by
    ext r
    dsimp
    split_ifs with hr0 hrn
    · have hr : r = 0 := Fin.ext hr0
      rw [hr, p.start_eq]
    · have hr : r = Fin.last n := Fin.ext hrn
      rw [hr, p.end_eq]
    · congr 1
      ext
      dsimp
      omega
  right_inv ks := by
    ext r
    have h2 : r.1 + 1 ≠ n := by omega
    simp [h2]

/-- When `n = 1`, there is a unique index path from `i` to `j` (with empty intermediate sequence
and endpoints `k_0 = i`, `k_1 = j`). -/
instance indexPathUniqueOne {I : Type} (i j : I) : Unique (IndexPath I 1 i j) where
  default :=
    { vertex := fun r => if r.1 = 0 then i else j
      start_eq := rfl
      end_eq := rfl }
  uniq p := by
    ext r
    fin_cases r
    · exact p.start_eq
    · exact p.end_eq

/-- Matrix entry along step `m` of path `p`: `[M^{(m)}]_{k_{m-1} → k_m}`. -/
def pathStepEntry {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → GaugeMatrix I) (p : IndexPath I n i j) (m : Fin n) : ENNReal :=
  ioEntry (M m) (p.vertex m.castSucc) (p.vertex m.succ)

/-- All-positive path predicate: every single-step matrix entry along `p` is strictly positive. -/
def IsPositivePath {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → GaugeMatrix I) (p : IndexPath I n i j) : Prop :=
  ∀ m : Fin n, 0 < pathStepEntry M p m

/-- Zero-factor path predicate: at least one step along `p` has matrix entry equal to zero. -/
def HasZeroStep {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → GaugeMatrix I) (p : IndexPath I n i j) : Prop :=
  ∃ m : Fin n, pathStepEntry M p m = 0

/-! ## CH02-P01: Single-Component Sum Degenerates to Scalar Lipschitz Bound -/

/-- Note (`oet-c4369c63c86cbacf`): when `I = {i}` (`∀ j : I, j = i`), the global Lipschitz matrix
condition degenerates to the scalar inequality `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)`. -/
theorem lip_matrix_iff_scalar_of_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hI : ∀ j : I, j = i) :
    L ∈ LipCertFamily d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ ioEntry L i i * d i x y := by
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext j
    simp [hI j]
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    rwa [huniv, Finset.sum_singleton] at h
  · intro hscalar x hx y hy j
    rw [hI j, huniv, Finset.sum_singleton]
    exact hscalar x hx y hy

/-- Variant of `CH02-P01` stated directly under `Fintype.card I = 1` (`|I| = 1` and `i ∈ I`). -/
theorem lip_matrix_iff_scalar_of_card_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    L ∈ LipCertFamily d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ ioEntry L i i * d i x y := by
  apply lip_matrix_iff_scalar_of_singleton d ϕ L i
  intro j
  exact Fintype.card_le_one_iff.mp hcard.le j i

/-! ## CH02-P02 & CH02-P03: Anti-Monotonicity and Restriction of Lipschitz Certificate Families -/

/-- Lemma 2.1 (`oet-4ff5c58d71e1651f`, part 1): if `U ⊆ V ⊆ dom ϕ`, then
`mathscr_L(ϕ)|_V ⊆ mathscr_L(ϕ)|_U`. -/
theorem restricted_lip_cert_family_anti {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipCertFamily d ϕ V ⊆ RestrictedLipCertFamily d ϕ U := by
  intro L hL
  refine ⟨hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/-- Lemma 2.1 (`oet-4ff5c58d71e1651f`, part 2): for any `U ⊆ dom ϕ`,
`mathscr_L(ϕ) ⊆ mathscr_L(ϕ)|_U`. -/
theorem lip_cert_family_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom ϕ) :
    LipCertFamily d ϕ ⊆ RestrictedLipCertFamily d ϕ U := by
  rw [← restrictedLipCertFamily_dom_eq d ϕ]
  exact restricted_lip_cert_family_anti d ϕ hU Set.Subset.rfl

/-! ## CH02-P04: Two-Step Lipschitz Composition Law -/

/-- Proposition 2.2 (`oet-193cebcc1a7f9259`): for `U₁ ⊆ dom (ϕ₂ * ϕ₁)` and exact intermediate
image `U₂ = ϕ₁(U₁)`, if `L₁ ∈ mathscr_L(ϕ₁)|_{U₁}` and `L₂ ∈ mathscr_L(ϕ₂)|_{U₂}`, then
`L₂ * L₁ ∈ mathscr_L(ϕ₂ * ϕ₁)|_{U₁}`. -/
theorem restricted_lip_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ RestrictedLipCertFamily d ϕ₁ U₁)
    (hL₂ : L₂ ∈ RestrictedLipCertFamily d ϕ₂ (operator_image ϕ₁ U₁)) :
    L₂ * L₁ ∈ RestrictedLipCertFamily d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
      = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, ioEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
        hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ ≤ ∑ k : I, ioEntry L₂ k j * (∑ i : I, ioEntry L₁ i k * d i x y) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (hL₁.2 x hx y hy k) (zero_le _)
    _ = ∑ k : I, ∑ i : I, ioEntry L₂ k j * (ioEntry L₁ i k * d i x y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, (ioEntry L₂ k j * ioEntry L₁ i k) * d i x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc]
    _ = ∑ i : I, ioEntry (L₂ * L₁) i j * d i x y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ioEntry_mul, Finset.sum_mul]

/-! ## CH02-P05 & CH02-P06: Anti-Monotonicity and Restriction of co-Lipschitz Certificate Families -/

/-- Lemma 2.3 (`oet-893b1d33535f7245`, part 1): if `∅ ≠ U ⊆ V ⊆ dom ϕ`, then
`mathscr_K(ϕ)|_V ⊆ mathscr_K(ϕ)|_U`. -/
theorem restricted_colip_cert_family_anti {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U V : Set X} (hUne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedCoLipCertFamily d ϕ V ⊆ RestrictedCoLipCertFamily d ϕ U := by
  intro K hK
  refine ⟨hUne, hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/-- Lemma 2.3 (`oet-893b1d33535f7245`, part 2): for any nonempty `U ⊆ dom ϕ`,
`mathscr_K(ϕ)|_{dom ϕ} ⊆ mathscr_K(ϕ)|_U`. -/
theorem global_colip_cert_family_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {U : Set X} (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    RestrictedCoLipCertFamily d ϕ (dom ϕ) ⊆ RestrictedCoLipCertFamily d ϕ U :=
  restricted_colip_cert_family_anti d ϕ hUne hU Set.Subset.rfl

/-! ## CH02-P07: Zero Output Distance and Positive Input Distance Force co-Lip Entry to Zero -/

/-- Note (`oet-88784dcbfff0ea66`): if there exist `x, y ∈ dom ϕ` such that
`d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`, then every global co-Lipschitz certificate
`K ∈ mathscr_K(ϕ)|_{dom ϕ}` satisfies `K_{i → j} = 0`. -/
theorem colip_entry_eq_zero_of_output_zero_input_pos {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I)
    (hxy : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    {K : GaugeMatrix I} (hK : K ∈ RestrictedCoLipCertFamily d ϕ (dom ϕ)) :
    ioEntry K i j = 0 := by
  rcases hxy with ⟨x, hx, y, hy, hout, hin⟩
  have hle : ioEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    calc
      ioEntry K i j * d i x y
        ≤ ∑ k : I, ioEntry K k j * d k x y :=
          Finset.single_le_sum (f := fun k => ioEntry K k j * d k x y)
            (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  rw [hout] at hle
  have hmul_zero : ioEntry K i j * d i x y = 0 := nonpos_iff_eq_zero.mp hle
  rcases mul_eq_zero.mp hmul_zero with hK0 | hd0
  · exact hK0
  · exact absurd hd0 hin.ne'

/-! ## CH02-P08: Two-Step co-Lipschitz Composition Law (Nonemptiness and Exact Image Domain) -/

/-- If `U₁ ⊆ dom (ϕ₂ * ϕ₁)` and `K₁ ∈ mathscr_K(ϕ₁)|_{U₁}`, then `U₁` and the exact intermediate
image `U₂ = ϕ₁(U₁)` are both nonempty and `U₂ ⊆ dom ϕ₂`. -/
theorem image_nonempty_and_subset_dom_of_colip {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ₁ ϕ₂ : Operator X bot}
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {K₁ : GaugeMatrix I} (hK₁ : K₁ ∈ RestrictedCoLipCertFamily d ϕ₁ U₁) :
    U₁.Nonempty ∧ (operator_image ϕ₁ U₁).Nonempty ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  refine ⟨hK₁.1, hK₁.1.image ϕ₁.func, ?_⟩
  exact (subset_dom_and_image_subset_dom_of_subset_dom_comp hU₁).2

/-- Proposition 2.4 (`oet-0f256e6f1d38a612`): for `U₁ ⊆ dom (ϕ₂ * ϕ₁)` and `U₂ = ϕ₁(U₁)`,
if `K₁ ∈ mathscr_K(ϕ₁)|_{U₁}` and `K₂ ∈ mathscr_K(ϕ₂)|_{U₂}`, then
`K₂ * K₁ ∈ mathscr_K(ϕ₂ * ϕ₁)|_{U₁}`. -/
theorem restricted_colip_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ RestrictedCoLipCertFamily d ϕ₁ U₁)
    (hK₂ : K₂ ∈ RestrictedCoLipCertFamily d ϕ₂ (operator_image ϕ₁ U₁)) :
    K₂ * K₁ ∈ RestrictedCoLipCertFamily d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    (∑ i : I, ioEntry (K₂ * K₁) i j * d i x y)
      = ∑ i : I, (∑ k : I, ioEntry K₂ k j * ioEntry K₁ i k) * d i x y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ioEntry_mul]
    _ = ∑ i : I, ∑ k : I, (ioEntry K₂ k j * ioEntry K₁ i k) * d i x y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, ioEntry K₂ k j * (ioEntry K₁ i k * d i x y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
          rw [mul_assoc]
    _ = ∑ k : I, ioEntry K₂ k j * (∑ i : I, ioEntry K₁ i k * d i x y) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
    _ ≤ ∑ k : I, ioEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_left (hK₁.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
          hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

/-! ## CH02-P09 & CH02-P10: Positive-Length Chain Lipschitz and co-Lipschitz Bounds -/

/-- Corollary 2.5(i) (`oet-c80171fa685dc795`): for any positive-length chain `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`
(`k ≥ 1`) with `U₁ ⊆ dom (c_k)` and step-local certificates `L^{(m)} ∈ mathscr_L(ϕ_m)|_{U_m}`,
the ordered product satisfies `L^{(k)} * ⋯ * L^{(1)} ∈ mathscr_L(c_k)|_{U₁}`. -/
theorem step_chain_lip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (ϕ : Fin k → Operator X bot) {U₁ : Set X}
      (_ : U₁ ⊆ dom (stepChainComp k ϕ))
      (L : Fin k → GaugeMatrix I)
      (_ : ∀ m : Fin k, L m ∈ RestrictedLipCertFamily d (ϕ m) (stepDomain k ϕ U₁ m.castSucc)),
      nonemptyMatrixProd k hk L ∈ RestrictedLipCertFamily d (stepChainComp k ϕ) U₁
  | 0, hk, _, _, _, _, _ => absurd hk (Nat.not_succ_le_zero 0)
  | 1, _, ϕ, U₁, _, L, hL => by
      have h0 := hL 0
      simpa [nonemptyMatrixProd, stepChainComp] using h0
  | m + 2, _, ϕ, U₁, hU₁, L, hL => by
      rw [stepChainComp_succ] at hU₁ ⊢
      have hU₁_pre : U₁ ⊆ dom (stepChainComp (m + 1) (ϕ ∘ Fin.castSucc)) :=
        (subset_dom_and_image_subset_dom_of_subset_dom_comp hU₁).1
      have hL_pre : ∀ r : Fin (m + 1),
          (L ∘ Fin.castSucc) r ∈ RestrictedLipCertFamily d ((ϕ ∘ Fin.castSucc) r)
            (stepDomain (m + 1) (ϕ ∘ Fin.castSucc) U₁ r.castSucc) := by
        intro r
        have hr := hL r.castSucc
        rwa [stepDomain_castSucc_succ] at hr
      have ih := step_chain_lip_bound d (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
        (ϕ ∘ Fin.castSucc) hU₁_pre (L ∘ Fin.castSucc) hL_pre
      have hL_last := hL (Fin.last (m + 1))
      rw [stepDomain_castSucc_succ, stepDomain_last] at hL_last
      exact restricted_lip_comp d (stepChainComp (m + 1) (ϕ ∘ Fin.castSucc))
        (ϕ (Fin.last (m + 1))) hU₁ ih hL_last

/-- Corollary 2.5(i) phrased directly with `OperatorChain (List.ofFn ϕ).reverse`. -/
theorem step_chain_lip_bound_operatorChain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (OperatorChain (List.ofFn ϕ).reverse))
    (L : Fin k → GaugeMatrix I)
    (hL : ∀ m : Fin k, L m ∈ RestrictedLipCertFamily d (ϕ m) (stepDomain k ϕ U₁ m.castSucc)) :
    nonemptyMatrixProd k hk L ∈
      RestrictedLipCertFamily d (OperatorChain (List.ofFn ϕ).reverse) U₁ := by
  rw [← stepChainComp_eq_operatorChain_reverse] at hU₁ ⊢
  exact step_chain_lip_bound d k hk ϕ hU₁ L hL

/-- Corollary 2.5(ii) (`oet-c80171fa685dc795`): for any positive-length chain `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`
(`k ≥ 1`) with `U₁ ⊆ dom (c_k)` and step-local certificates `K^{(m)} ∈ mathscr_K(ϕ_m)|_{U_m}`,
the ordered product satisfies `K^{(k)} * ⋯ * K^{(1)} ∈ mathscr_K(c_k)|_{U₁}`. -/
theorem step_chain_colip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (ϕ : Fin k → Operator X bot) {U₁ : Set X}
      (_ : U₁ ⊆ dom (stepChainComp k ϕ))
      (K : Fin k → GaugeMatrix I)
      (_ : ∀ m : Fin k, K m ∈ RestrictedCoLipCertFamily d (ϕ m) (stepDomain k ϕ U₁ m.castSucc)),
      nonemptyMatrixProd k hk K ∈ RestrictedCoLipCertFamily d (stepChainComp k ϕ) U₁
  | 0, hk, _, _, _, _, _ => absurd hk (Nat.not_succ_le_zero 0)
  | 1, _, ϕ, U₁, _, K, hK => by
      have h0 := hK 0
      simpa [nonemptyMatrixProd, stepChainComp] using h0
  | m + 2, _, ϕ, U₁, hU₁, K, hK => by
      rw [stepChainComp_succ] at hU₁ ⊢
      have hU₁_pre : U₁ ⊆ dom (stepChainComp (m + 1) (ϕ ∘ Fin.castSucc)) :=
        (subset_dom_and_image_subset_dom_of_subset_dom_comp hU₁).1
      have hK_pre : ∀ r : Fin (m + 1),
          (K ∘ Fin.castSucc) r ∈ RestrictedCoLipCertFamily d ((ϕ ∘ Fin.castSucc) r)
            (stepDomain (m + 1) (ϕ ∘ Fin.castSucc) U₁ r.castSucc) := by
        intro r
        have hr := hK r.castSucc
        rwa [stepDomain_castSucc_succ] at hr
      have ih := step_chain_colip_bound d (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
        (ϕ ∘ Fin.castSucc) hU₁_pre (K ∘ Fin.castSucc) hK_pre
      have hK_last := hK (Fin.last (m + 1))
      rw [stepDomain_castSucc_succ, stepDomain_last] at hK_last
      exact restricted_colip_comp d (stepChainComp (m + 1) (ϕ ∘ Fin.castSucc))
        (ϕ (Fin.last (m + 1))) hU₁ ih hK_last

/-- Corollary 2.5(ii) phrased directly with `OperatorChain (List.ofFn ϕ).reverse`. -/
theorem step_chain_colip_bound_operatorChain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (OperatorChain (List.ofFn ϕ).reverse))
    (K : Fin k → GaugeMatrix I)
    (hK : ∀ m : Fin k, K m ∈ RestrictedCoLipCertFamily d (ϕ m) (stepDomain k ϕ U₁ m.castSucc)) :
    nonemptyMatrixProd k hk K ∈
      RestrictedCoLipCertFamily d (OperatorChain (List.ofFn ϕ).reverse) U₁ := by
  rw [← stepChainComp_eq_operatorChain_reverse] at hU₁ ⊢
  exact step_chain_colip_bound d k hk ϕ hU₁ K hK

/-! ## CH02-P11 & CH02-P12: Identity Matrix Certificate for Zero-Step Identity Operator -/

/-- Exact identity sum `∑ i, I_{i → j} * d_i(x, y) = d_j(x, y)` in `ENNReal`. -/
theorem sum_idMatrix_mul_dist {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, ioEntry idMatrix i j * d i x y) = d j x y := by
  classical
  simp [ioEntry_idMatrix]

/-- Note (`oet-11006ddd8c43bfec`, Lip part): for any `U ⊆ dom (id_X)`, the identity matrix
`idMatrix` belongs to `mathscr_L(id_X)|_U`. -/
theorem idMatrix_mem_restricted_lip_identity {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedLipCertFamily d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  rw [sum_idMatrix_mul_dist]
  exact le_rfl

/-- Zero-step chain (`k = 0`) Lipschitz certificate: `matrixChainProd 0 M = idMatrix` belongs to
`mathscr_L(c_0)|_U` for any `U ⊆ dom (c_0)`. -/
theorem zero_step_lip_cert {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot) (M : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU : U ⊆ dom (stepChainComp 0 ϕ)) :
    matrixChainProd 0 M ∈ RestrictedLipCertFamily d (stepChainComp 0 ϕ) U :=
  idMatrix_mem_restricted_lip_identity d hU

/-- Note (`oet-11006ddd8c43bfec`, co-Lip part): for any nonempty `U ⊆ dom (id_X)`, the identity
matrix `idMatrix` belongs to `mathscr_K(id_X)|_U`. -/
theorem idMatrix_mem_restricted_colip_identity {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hUne : U.Nonempty) (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedCoLipCertFamily d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hUne, hU, ?_⟩
  intro x _ y _ j
  rw [sum_idMatrix_mul_dist]
  exact le_rfl

/-- Zero-step chain (`k = 0`) co-Lipschitz certificate: `matrixChainProd 0 M = idMatrix` belongs to
`mathscr_K(c_0)|_U` for any nonempty `U ⊆ dom (c_0)`. -/
theorem zero_step_colip_cert {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Fin 0 → Operator X bot) (M : Fin 0 → GaugeMatrix I)
    {U : Set X} (hUne : U.Nonempty) (hU : U ⊆ dom (stepChainComp 0 ϕ)) :
    matrixChainProd 0 M ∈ RestrictedCoLipCertFamily d (stepChainComp 0 ϕ) U :=
  idMatrix_mem_restricted_colip_identity d hUne hU

/-- Combined zero-step certificate statement matching the textbook intersection
`I ∈ mathscr_L(id_X)|_U ∩ mathscr_K(id_X)|_U` on any nonempty `U ⊆ dom (id_X)`. -/
theorem idMatrix_mem_lip_inter_colip_identity {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hUne : U.Nonempty) (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedLipCertFamily d (operator_identity (X := X) (bot := bot)) U ∩
      RestrictedCoLipCertFamily d (operator_identity (X := X) (bot := bot)) U :=
  ⟨idMatrix_mem_restricted_lip_identity d hU, idMatrix_mem_restricted_colip_identity d hUne hU⟩

/-! ## CH02-P14 & CH02-P13: Positivity and Zero-Value Criteria for Finite Nonempty Matrix Products -/

private theorem ennreal_sum_pos_iff {I : Type} [Fintype I] (f : I → ENNReal) :
    0 < (∑ k : I, f k) ↔ ∃ k : I, 0 < f k := by
  constructor
  · intro hpos
    by_contra hnone
    push Not at hnone
    have hzero : (∑ k : I, f k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      exact nonpos_iff_eq_zero.mp (hnone k)
    exact hpos.ne' hzero
  · rintro ⟨k, hk⟩
    exact lt_of_lt_of_le hk (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ k))

private theorem ennreal_mul_pos_iff {a b : ENNReal} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp [pos_iff_ne_zero, mul_eq_zero, not_or]

/-- Proposition 2.6(ii) (`oet-e4154c34e95d3c23`): for any `n ≥ 1`, `[M^{(n)} ⋯ M^{(1)}]_{i → j} > 0`
if and only if there exists at least one index path from `i` to `j` along which all step entries
are strictly positive. -/
theorem nonemptyMatrixProd_entry_pos_iff {I : Type} [Fintype I] :
    ∀ (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I),
      0 < ioEntry (nonemptyMatrixProd n hn M) i j ↔
        ∃ p : IndexPath I n i j, IsPositivePath M p
  | 0, hn, _, _, _ => absurd hn (Nat.not_succ_le_zero 0)
  | 1, _, M, i, j => by
      constructor
      · intro hpos
        refine ⟨default, fun m => ?_⟩
        fin_cases m
        simpa [pathStepEntry, default] using hpos
      · rintro ⟨p, hp⟩
        have h0 := hp 0
        dsimp [pathStepEntry] at h0
        have hend : p.vertex 1 = j := p.end_eq
        rw [p.start_eq, hend] at h0
        exact h0
  | m + 2, _, M, i, j => by
      set n := m + 1
      have hn : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le m)
      change 0 < ioEntry (M (Fin.last n) * nonemptyMatrixProd n hn (M ∘ Fin.castSucc)) i j ↔
        ∃ p : IndexPath I (n + 1) i j, IsPositivePath M p
      rw [ioEntry_mul, ennreal_sum_pos_iff]
      constructor
      · rintro ⟨k, hk⟩
        rw [ennreal_mul_pos_iff] at hk
        rcases hk with ⟨hk_last, hk_pre⟩
        rw [nonemptyMatrixProd_entry_pos_iff n hn (M ∘ Fin.castSucc) i k] at hk_pre
        rcases hk_pre with ⟨p₀, hp₀⟩
        refine ⟨{
          vertex := Fin.snoc p₀.vertex j
          start_eq := by
            have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
            rw [h0, Fin.snoc_castSucc, p₀.start_eq]
          end_eq := by simp [Fin.snoc_last]
        }, ?_⟩
        intro r
        refine Fin.lastCases ?_ ?_ r
        · dsimp [pathStepEntry]
          simp [Fin.snoc_last, Fin.snoc_castSucc, p₀.end_eq, hk_last, n]
        · intro r₀
          dsimp [pathStepEntry]
          rw [Fin.snoc_castSucc, ← Fin.castSucc_succ, Fin.snoc_castSucc]
          exact hp₀ r₀
      · rintro ⟨p, hp⟩
        let k := p.vertex (Fin.last n).castSucc
        refine ⟨k, ?_⟩
        rw [ennreal_mul_pos_iff]
        refine ⟨?_, ?_⟩
        · have hlast := hp (Fin.last n)
          dsimp [pathStepEntry] at hlast
          have hend : p.vertex (Fin.last (n + 1)) = j := p.end_eq
          rw [hend] at hlast
          exact hlast
        · rw [nonemptyMatrixProd_entry_pos_iff n hn (M ∘ Fin.castSucc) i k]
          refine ⟨{
            vertex := p.vertex ∘ Fin.castSucc
            start_eq := p.start_eq
            end_eq := rfl
          }, ?_⟩
          intro r₀
          have hr₀ := hp r₀.castSucc
          dsimp [pathStepEntry] at hr₀ ⊢
          exact hr₀

/-- Explicit `n = 1` degeneration for Proposition 2.6(ii): existence of a positive path for `n = 1`
degenerates to `[M^{(1)}]_{i → j} > 0`. -/
theorem nonemptyMatrixProd_one_entry_pos_iff {I : Type} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (0 < ioEntry (nonemptyMatrixProd 1 le_rfl M) i j ↔ 0 < ioEntry (M 0) i j) ∧
      ((∃ p : IndexPath I 1 i j, IsPositivePath M p) ↔ 0 < ioEntry (M 0) i j) := by
  refine ⟨Iff.rfl, ?_⟩
  exact (nonemptyMatrixProd_entry_pos_iff 1 le_rfl M i j).symm

/-- Proposition 2.6(ii) stated directly over intermediate index tuples `(k_1, …, k_{n-1})`. -/
theorem nonemptyMatrixProd_entry_pos_iff_intermediate {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < ioEntry (nonemptyMatrixProd n hn M) i j ↔
      ∃ ks : Fin (n - 1) → I,
        IsPositivePath M ((indexPathEquivIntermediate n hn i j).symm ks) := by
  rw [nonemptyMatrixProd_entry_pos_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨indexPathEquivIntermediate n hn i j p, ?_⟩
    simpa using hp
  · rintro ⟨ks, hks⟩
    exact ⟨(indexPathEquivIntermediate n hn i j).symm ks, hks⟩

/-- Proposition 2.6(i) (`oet-e4154c34e95d3c23`): for any `n ≥ 1`, `[M^{(n)} ⋯ M^{(1)}]_{i → j} = 0`
if and only if every index path from `i` to `j` contains at least one zero-entry step. -/
theorem nonemptyMatrixProd_entry_eq_zero_iff {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    ioEntry (nonemptyMatrixProd n hn M) i j = 0 ↔
      ∀ p : IndexPath I n i j, HasZeroStep M p := by
  have hpos := nonemptyMatrixProd_entry_pos_iff n hn M i j
  rw [← not_iff_not] at hpos
  simpa only [pos_iff_ne_zero, Classical.not_not, not_exists, IsPositivePath,
    Classical.not_forall, HasZeroStep] using hpos

/-- Explicit `n = 1` degeneration for Proposition 2.6(i): every path for `n = 1` having a zero
step degenerates to `[M^{(1)}]_{i → j} = 0`. -/
theorem nonemptyMatrixProd_one_entry_eq_zero_iff {I : Type} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (ioEntry (nonemptyMatrixProd 1 le_rfl M) i j = 0 ↔ ioEntry (M 0) i j = 0) ∧
      ((∀ p : IndexPath I 1 i j, HasZeroStep M p) ↔ ioEntry (M 0) i j = 0) := by
  refine ⟨Iff.rfl, ?_⟩
  exact (nonemptyMatrixProd_entry_eq_zero_iff 1 le_rfl M i j).symm

/-- Proposition 2.6(i) stated directly over intermediate index tuples `(k_1, …, k_{n-1})`. -/
theorem nonemptyMatrixProd_entry_eq_zero_iff_intermediate {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    ioEntry (nonemptyMatrixProd n hn M) i j = 0 ↔
      ∀ ks : Fin (n - 1) → I,
        HasZeroStep M ((indexPathEquivIntermediate n hn i j).symm ks) := by
  rw [nonemptyMatrixProd_entry_eq_zero_iff]
  constructor
  · intro hall ks
    exact hall ((indexPathEquivIntermediate n hn i j).symm ks)
  · intro hall p
    have hp := hall (indexPathEquivIntermediate n hn i j p)
    simpa using hp
```

```lean filename=Main.lean
/-
Theoretical source attribution:
Zhe Li (also known as Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, Chapter 2 (Operator Bounds, §2.1),
https://glenzli.com/books/oet/, https://gitlab.com/glenzli/oet-public,
licensed under CC BY 4.0 (https://creativecommons.org/licenses/by/4.0/).
Lean 4 formalization entry point for case LCH02.
-/
import LCH02.OperatorBounds
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "IsLipMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "LipCertFamily"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "IsRestrictedLipMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "RestrictedLipCertFamily"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "restrictedLipCertFamily_dom_eq"
        }
      ],
      "representation": "算子 ϕ : Operator X bot（定义域 dom ϕ = {x | ϕ.func x ≠ bot}），分量扩展伪度量族 d : I → X → X → ENNReal（[Fintype I]），矩阵 L : GaugeMatrix I。全域谓词 IsLipMatrix 量化 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I，断言 d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, ioEntry L i j * d i x y；LipCertFamily 定义全域证书族 mathscr_L(ϕ)。受限谓词 IsRestrictedLipMatrix 包含定义域约束 U ⊆ dom ϕ 并对 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I 断言同一放缩不等式；RestrictedLipCertFamily 定义受限证书族 mathscr_L(ϕ)|_U，且 restrictedLipCertFamily_dom_eq 验证 U = dom ϕ 时与全域族一致。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "IsRestrictedCoLipMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "RestrictedCoLipCertFamily"
        }
      ],
      "representation": "对算子 ϕ : Operator X bot、子集 U : Set X 与矩阵 K : GaugeMatrix I，IsRestrictedCoLipMatrix 显式包含非空性条件 U.Nonempty、定义域约束 U ⊆ dom ϕ，以及全称量化下界不等式 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, (∑ i : I, ioEntry K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)。RestrictedCoLipCertFamily 定义受限 co-Lip 证书族 mathscr_K(ϕ)|_U = {K | IsRestrictedCoLipMatrix d ϕ U K}，凡属该族均携带 U ≠ ∅ 与 U ⊆ dom ϕ。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "GaugeMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ioEntry"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ofIOEntry"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ioEntry_ofIOEntry"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ofIOEntry_ioEntry"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ioEntry_mul"
        }
      ],
      "representation": "GaugeMatrix I := Matrix I I ENNReal 取行指标为输出分量 j : I、列指标为输入分量 i : I；ioEntry M i j := M j i 精确实现原文 (M)_{ji} = M_{i → j} 的输入到输出通道指标约定，ofIOEntry 与往返引理给出通道函数与矩阵的双射对应。代数矩阵乘法直接使用 Matrix 乘法 M₂ * M₁，并由 ioEntry_mul 验证 (M₂ * M₁)_{i → j} = ∑ k : I, M₂_{k → j} * M₁_{i → k}（遵循 ENNReal 的 0 * ⊤ = 0 算术）。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "idMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ioEntry_idMatrix"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ioEntry_idMatrix_self"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "ioEntry_idMatrix_of_ne"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "emptyMatrixProd"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "matrixChainProd"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_one"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_succ"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_eq_matrixChainProd"
        }
      ],
      "representation": "idMatrix 定义扩展非负单位矩阵 I（对角元 1、非对角元 0）；emptyMatrixProd := idMatrix 定义零步空复合乘积，matrixChainProd 对任意 k : ℕ 及 M : Fin k → GaugeMatrix I 递归给出 M^{(k)} * ⋯ * M^{(1)}（k = 0 时取 emptyMatrixProd）；nonemptyMatrixProd 对 n : ℕ、1 ≤ n 及 M : Fin n → GaugeMatrix I 定义有序非空乘积 M^{(n)} * ⋯ * M^{(1)}（n = 1 时直接求值为 M 0，递推步左乘 M (Fin.last n)），并由 nonemptyMatrixProd_eq_matrixChainProd 证明 n ≥ 1 时两者相等。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepChainComp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepChainComp_eq_operatorChain_reverse"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "operatorChain_eq_stepChainComp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepDomain"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepDomain_zero"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepDomain_succ"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepDomain_last"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "stepDomain_subset_dom"
        }
      ],
      "representation": "stepChainComp k ϕ 按执行步序 ϕ : Fin k → Operator X bot 定义有限复合 c_k = ϕ_k ∘ ⋯ ∘ ϕ_1（k = 0 取 operator_identity）；stepChainComp_eq_operatorChain_reverse 与 operatorChain_eq_stepChainComp 给出与前置模块 OperatorChain ((List.ofFn ϕ).reverse) 的双向精确等价对应。stepDomain k ϕ U₁ : Fin (k + 1) → Set X 递归定义实际中间像域 U_1 = U₁ 及 U_{m+1} = operator_image (ϕ m) U_m，stepDomain_last 证明终点像域 U_{k+1} = c_k(U_1)，stepDomain_subset_dom 证明 U₁ ⊆ dom(c_k) 蕴含每步 U_m ⊆ dom(ϕ_m)。",
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "IndexPath"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "indexPathEquivIntermediate"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "indexPathUniqueOne"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "pathStepEntry"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "IsPositivePath"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "HasZeroStep"
        }
      ],
      "representation": "IndexPath I n i j 表示满足起止约定 k_0 = i、k_n = j 的顶点序列 vertex : Fin (n + 1) → I；indexPathEquivIntermediate 给出 1 ≤ n 时 IndexPath I n i j 与中间指标序列 Fin (n - 1) → I 的双射等价，indexPathUniqueOne 证明 n = 1 时存在唯一路径（对应空中间序列）。pathStepEntry M p m 提取第 m 步矩阵条目 [M^{(m)}]_{k_{m-1} → k_m}，IsPositivePath 定义全正路径谓词 ∀ m : Fin n, 0 < pathStepEntry M p m，HasZeroStep 定义含零因子路径谓词 ∃ m : Fin n, pathStepEntry M p m = 0。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "lip_matrix_iff_scalar_of_singleton"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "lip_matrix_iff_scalar_of_card_one"
        }
      ],
      "representation": "对任意有限指标集 I、单元素条件 I = {i}（∀ j : I, j = i）或基数条件 Fintype.card I = 1（配合 i : I），证明 L ∈ LipCertFamily d ϕ 当且仅当标量 Lip 不等式 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ ioEntry L i i * d i x y 成立。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "restricted_lip_cert_family_anti"
        }
      ],
      "representation": "固定算子 ϕ : Operator X bot，在前提 U ⊆ V 与 V ⊆ dom ϕ 下，证明受限 Lip 证书族的反单调包含关系 RestrictedLipCertFamily d ϕ V ⊆ RestrictedLipCertFamily d ϕ U。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "subset_dom_and_image_subset_dom_of_subset_dom_comp"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "restricted_lip_comp"
        }
      ],
      "representation": "对复合算子 ϕ₂ * ϕ₁（即 ϕ₂ ∘ ϕ₁）与起始子集 U₁ ⊆ dom (ϕ₂ * ϕ₁)，subset_dom_and_image_subset_dom_of_subset_dom_comp 证明 U₁ ⊆ dom ϕ₁ 且精确中间像域 U₂ = operator_image ϕ₁ U₁ ⊆ dom ϕ₂；restricted_lip_comp 在 L₁ ∈ mathscr_L(ϕ₁)|_{U₁} 与 L₂ ∈ mathscr_L(ϕ₂)|_{U₂} 前提下证明按次序乘积 L₂ * L₁ ∈ mathscr_L(ϕ₂ * ϕ₁)|_{U₁}。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "restricted_colip_cert_family_anti"
        }
      ],
      "representation": "固定算子 ϕ : Operator X bot，在非空与包含前提 U.Nonempty、U ⊆ V、V ⊆ dom ϕ 下，证明受限 co-Lip 证书族的反单调包含关系 RestrictedCoLipCertFamily d ϕ V ⊆ RestrictedCoLipCertFamily d ϕ U。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "colip_entry_eq_zero_of_output_zero_input_pos"
        }
      ],
      "representation": "对算子 ϕ : Operator X bot 与通道 (i, j)，在存在性前提 ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y（允许有限正值或 +∞）及 K ∈ RestrictedCoLipCertFamily d ϕ (dom ϕ) 下，证明对应条目 ioEntry K i j = 0。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "image_nonempty_and_subset_dom_of_colip"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "restricted_colip_comp"
        }
      ],
      "representation": "对复合算子 ϕ₂ * ϕ₁、U₁ ⊆ dom (ϕ₂ * ϕ₁) 及精确中间像域 U₂ = operator_image ϕ₁ U₁，image_nonempty_and_subset_dom_of_colip 由 K₁ ∈ mathscr_K(ϕ₁)|_{U₁} 导出 U₁.Nonempty、U₂.Nonempty 与 U₂ ⊆ dom ϕ₂；restricted_colip_comp 进一步结合 K₂ ∈ mathscr_K(ϕ₂)|_{U₂} 证明 K₂ * K₁ ∈ mathscr_K(ϕ₂ * ϕ₁)|_{U₁}。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "sum_idMatrix_mul_dist"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "idMatrix_mem_restricted_lip_identity"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "zero_step_lip_cert"
        }
      ],
      "representation": "对恒等算子 operator_identity（即 c_0 = id_X）与任意子集 U ⊆ dom operator_identity，由恒等求和引理 sum_idMatrix_mul_dist 证明单位矩阵 idMatrix ∈ RestrictedLipCertFamily d operator_identity U，并给出 k = 0 空乘积形式 zero_step_lip_cert。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05"
      ]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "idMatrix_mem_restricted_colip_identity"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "zero_step_colip_cert"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "idMatrix_mem_lip_inter_colip_identity"
        }
      ],
      "representation": "对恒等算子 operator_identity 与任意非空子集 U（U.Nonempty 且 U ⊆ dom operator_identity），证明 idMatrix ∈ RestrictedCoLipCertFamily d operator_identity U、零步链形式 zero_step_colip_cert，以及交集形式 idMatrix ∈ mathscr_L(id_X)|_U ∩ mathscr_K(id_X)|_U。",
      "dependencies": [
        "CH02-D01",
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P11"
      ]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_entry_pos_iff"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_one_entry_pos_iff"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_entry_pos_iff_intermediate"
        }
      ],
      "representation": "对任意 n ≥ 1（hn : 1 ≤ n）、矩阵族 M : Fin n → GaugeMatrix I 与指标 i, j : I，nonemptyMatrixProd_entry_pos_iff 证明 0 < ioEntry (nonemptyMatrixProd n hn M) i j ↔ ∃ p : IndexPath I n i j, IsPositivePath M p；nonemptyMatrixProd_entry_pos_iff_intermediate 给出中间指标序列 Fin (n - 1) → I 的等价形式；nonemptyMatrixProd_one_entry_pos_iff 显式刻画 n = 1 时退化为单个条目 0 < ioEntry (M 0) i j。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06"
      ]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "lip_cert_family_subset_restricted"
        }
      ],
      "representation": "固定算子 ϕ : Operator X bot，对任意子集 U ⊆ dom ϕ，将受限 Lip 反单调引理特化到 V = dom ϕ，证明全域证书可限制：LipCertFamily d ϕ ⊆ RestrictedLipCertFamily d ϕ U。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-P02"
      ]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "global_colip_cert_family_subset_restricted"
        }
      ],
      "representation": "固定算子 ϕ : Operator X bot，对任意非空子集 U（U.Nonempty 且 U ⊆ dom ϕ），将受限 co-Lip 反单调引理特化到 V = dom ϕ，证明全域 co-Lip 证书可限制：RestrictedCoLipCertFamily d ϕ (dom ϕ) ⊆ RestrictedCoLipCertFamily d ϕ U。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-P05"
      ]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "step_chain_lip_bound"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "step_chain_lip_bound_operatorChain"
        }
      ],
      "representation": "对任意正长度链 k ≥ 1（hk : 1 ≤ k）、算子序列 ϕ : Fin k → Operator X bot、起始域 U₁ ⊆ dom (stepChainComp k ϕ) 及逐步局部证书 ∀ m : Fin k, L m ∈ RestrictedLipCertFamily d (ϕ m) (stepDomain k ϕ U₁ m.castSucc)，通过对两步 Lip 复合律做有限归纳证明 nonemptyMatrixProd k hk L ∈ RestrictedLipCertFamily d (stepChainComp k ϕ) U₁，并给出 OperatorChain 等价形式。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P04"
      ]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "step_chain_colip_bound"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "step_chain_colip_bound_operatorChain"
        }
      ],
      "representation": "对任意正长度链 k ≥ 1（hk : 1 ≤ k）、算子序列 ϕ : Fin k → Operator X bot、起始域 U₁ ⊆ dom (stepChainComp k ϕ) 及逐步局部证书 ∀ m : Fin k, K m ∈ RestrictedCoLipCertFamily d (ϕ m) (stepDomain k ϕ U₁ m.castSucc)（首步自动携带 U₁.Nonempty），通过对两步 co-Lip 复合律做有限归纳证明 nonemptyMatrixProd k hk K ∈ RestrictedCoLipCertFamily d (stepChainComp k ϕ) U₁，并给出 OperatorChain 等价形式。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P08"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_entry_eq_zero_iff"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_one_entry_eq_zero_iff"
        },
        {
          "file": "LCH02/OperatorBounds.lean",
          "name": "nonemptyMatrixProd_entry_eq_zero_iff_intermediate"
        }
      ],
      "representation": "对任意 n ≥ 1（hn : 1 ≤ n）、矩阵族 M : Fin n → GaugeMatrix I 与指标 i, j : I，nonemptyMatrixProd_entry_eq_zero_iff 证明 ioEntry (nonemptyMatrixProd n hn M) i j = 0 ↔ ∀ p : IndexPath I n i j, HasZeroStep M p；nonemptyMatrixProd_entry_eq_zero_iff_intermediate 给出中间指标序列 Fin (n - 1) → I 的等价形式；nonemptyMatrixProd_one_entry_eq_zero_iff 显式刻画 n = 1 时退化为单个条目 ioEntry (M 0) i j = 0。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06",
        "CH02-P14"
      ]
    }
  ]
}
```
