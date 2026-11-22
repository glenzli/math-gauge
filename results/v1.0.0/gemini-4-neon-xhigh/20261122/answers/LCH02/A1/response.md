已完成 `LCH02`（《算子演化论》第一卷第 2 章有限复合与路径节群，全部 20 项义务）的 Lean 4.29.1 形式化交付与全量内核校验：

- **模块结构**：[LCH02/GaugeMatrix.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/LCH02/physical-1/session/work/LCH02/GaugeMatrix.lean)、[LCH02/IndexPath.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/LCH02/physical-1/session/work/LCH02/IndexPath.lean)、[LCH02/LipBounds.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/LCH02/physical-1/session/work/LCH02/LipBounds.lean)、[LCH02/FiniteComposition.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/LCH02/physical-1/session/work/LCH02/FiniteComposition.lean)、[Main.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/LCH02/physical-1/session/work/Main.lean) 与 [alignment.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/LCH02/physical-1/session/work/alignment.json)。
- **校验结果**：在冻结环境（Lean 4.29.1 + Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6` + 原样导入 `formal_oet`）下零报错、零警告编译通过；对清单中全部 71 个声明执行 `#check` 与 `#print axioms`，仅依赖 `propext`、`Classical.choice`、`Quot.sound`，无 `sorry`/`admit`/新增公理；`formal_oet/` 与 `.visible-input/` 未作任何修改。
- **来源署名**：本形式化基于 Zhe Li (Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453, *The Operator Evolution Theory*, Volume I, v1.0.0, https://glenzli.com/books/oet/, licensed under CC BY 4.0。

---

```lean filename=LCH02/GaugeMatrix.lean
/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace LCH02

universe u

/--
Extended nonnegative matrix indexed by a gauge component index set `I`.
Following §2.1 of OET Vol. I, rows index output components `j` and columns index
input components `i`, so the `(j, i)` matrix entry represents `M_{i → j}`.
-/
abbrev GaugeMatrix (I : Type u) := Matrix I I ENNReal

/--
The entry `M_{i → j}` from input component `i` to output component `j`,
stored at row `j` and column `i`: `(M)_{j, i} = M_{i → j}`.
-/
def matrixEntry {I : Type u} (M : GaugeMatrix I) (i j : I) : ENNReal :=
  M j i

/-- Construct a `GaugeMatrix` from its `i → j` entry function. -/
def gaugeMatrixOfEntries {I : Type u} (f : I → I → ENNReal) : GaugeMatrix I :=
  Matrix.of fun j i => f i j

@[simp] theorem matrixEntry_ofEntries {I : Type u} (f : I → I → ENNReal) (i j : I) :
    matrixEntry (gaugeMatrixOfEntries f) i j = f i j :=
  rfl

@[ext] theorem gaugeMatrix_ext {I : Type u} {A B : GaugeMatrix I}
    (h : ∀ i j : I, matrixEntry A i j = matrixEntry B i j) : A = B := by
  ext j i
  exact h i j

/--
Multiplication of extended nonnegative gauge matrices.
With rows as outputs and columns as inputs, `(A · B)_{i → j} = ∑ k, A_{k → j} * B_{i → k}`.
-/
noncomputable def gaugeMatrixMul {I : Type u} [Fintype I] (A B : GaugeMatrix I) : GaugeMatrix I :=
  A * B

@[simp] theorem gaugeMatrixMul_eq_mul {I : Type u} [Fintype I] (A B : GaugeMatrix I) :
    gaugeMatrixMul A B = A * B :=
  rfl

theorem matrixEntry_gaugeMatrixMul {I : Type u} [Fintype I]
    (A B : GaugeMatrix I) (i j : I) :
    matrixEntry (gaugeMatrixMul A B) i j =
      ∑ k : I, matrixEntry A k j * matrixEntry B i k := by
  simp [matrixEntry, gaugeMatrixMul, Matrix.mul_apply]

theorem gaugeMatrixMul_assoc {I : Type u} [Fintype I]
    (A B C : GaugeMatrix I) :
    gaugeMatrixMul (gaugeMatrixMul A B) C = gaugeMatrixMul A (gaugeMatrixMul B C) := by
  simp [gaugeMatrixMul, Matrix.mul_assoc]

/-- The identity gauge matrix `I`. -/
def idMatrix {I : Type u} [DecidableEq I] : GaugeMatrix I :=
  (1 : Matrix I I ENNReal)

@[simp] theorem idMatrix_eq_one {I : Type u} [DecidableEq I] :
    (idMatrix : GaugeMatrix I) = 1 :=
  rfl

@[simp] theorem matrixEntry_idMatrix {I : Type u} [DecidableEq I] (i j : I) :
    matrixEntry (idMatrix : GaugeMatrix I) i j = if i = j then 1 else 0 := by
  simp [matrixEntry, idMatrix, Matrix.one_apply, eq_comm]

@[simp] theorem gaugeMatrixMul_idMatrix {I : Type u} [Fintype I] [DecidableEq I]
    (A : GaugeMatrix I) :
    gaugeMatrixMul A idMatrix = A := by
  simp [gaugeMatrixMul, idMatrix]

@[simp] theorem idMatrix_gaugeMatrixMul {I : Type u} [Fintype I] [DecidableEq I]
    (A : GaugeMatrix I) :
    gaugeMatrixMul idMatrix A = A := by
  simp [gaugeMatrixMul, idMatrix]

/--
Ordered nonempty product of `n + 1` matrices `M^(1), ..., M^(n+1)` in composition order:
`M^(n+1) · M^(n) · ... · M^(1)`.
Here `M 0` is the first (innermost) matrix `M^(1)` and `M (Fin.last n)` is the last
(outermost) matrix `M^(n+1)`.
-/
noncomputable def orderedMatrixProdNonempty {I : Type u} [Fintype I] :
    {n : Nat} → (Fin (n + 1) → GaugeMatrix I) → GaugeMatrix I
  | 0, M => M 0
  | _ + 1, M =>
      gaugeMatrixMul (M (Fin.last _)) (orderedMatrixProdNonempty (fun m => M m.castSucc))

@[simp] theorem orderedMatrixProdNonempty_zero {I : Type u} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) :
    orderedMatrixProdNonempty M = M 0 :=
  rfl

theorem orderedMatrixProdNonempty_succ {I : Type u} [Fintype I] {n : Nat}
    (M : Fin (n + 2) → GaugeMatrix I) :
    orderedMatrixProdNonempty M =
      gaugeMatrixMul (M (Fin.last (n + 1))) (orderedMatrixProdNonempty (fun m => M m.castSucc)) :=
  rfl

theorem orderedMatrixProdNonempty_succ_left {I : Type u} [Fintype I] {n : Nat}
    (M : Fin (n + 2) → GaugeMatrix I) :
    orderedMatrixProdNonempty M =
      gaugeMatrixMul (orderedMatrixProdNonempty (fun m => M m.succ)) (M 0) := by
  induction n with
  | zero =>
      simp [orderedMatrixProdNonempty, Fin.last]
  | succ k ih =>
      rw [orderedMatrixProdNonempty_succ]
      have h_init :
          orderedMatrixProdNonempty (fun m : Fin (k + 2) => M m.castSucc) =
            gaugeMatrixMul
              (orderedMatrixProdNonempty (fun m : Fin (k + 1) => M m.succ.castSucc))
              (M 0) :=
        ih (fun m => M m.castSucc)
      rw [h_init, ← gaugeMatrixMul_assoc]
      rfl

/--
Ordered finite product of `n` matrices in composition order `M^(n) · ... · M^(1)`,
with the empty product (`n = 0`) defined as the identity matrix `idMatrix`.
-/
noncomputable def orderedMatrixProd {I : Type u} [Fintype I] [DecidableEq I] :
    {n : Nat} → (Fin n → GaugeMatrix I) → GaugeMatrix I
  | 0, _ => idMatrix
  | _ + 1, M => orderedMatrixProdNonempty M

@[simp] theorem orderedMatrixProd_zero {I : Type u} [Fintype I] [DecidableEq I]
    (M : Fin 0 → GaugeMatrix I) :
    orderedMatrixProd M = idMatrix :=
  rfl

@[simp] theorem orderedMatrixProd_one {I : Type u} [Fintype I] [DecidableEq I]
    (M : Fin 1 → GaugeMatrix I) :
    orderedMatrixProd M = M 0 :=
  rfl

theorem orderedMatrixProd_eq_nonempty {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (M : Fin (n + 1) → GaugeMatrix I) :
    orderedMatrixProd M = orderedMatrixProdNonempty M :=
  rfl

theorem orderedMatrixProd_succ {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (M : Fin (n + 1) → GaugeMatrix I) :
    orderedMatrixProd M =
      gaugeMatrixMul (M (Fin.last n)) (orderedMatrixProd (fun m => M m.castSucc)) := by
  cases n with
  | zero =>
      simp [orderedMatrixProd, orderedMatrixProdNonempty]
  | succ k =>
      rfl

/--
List-based composition-order product for chronological lists `[M^(1), ..., M^(n)]`,
evaluating to `M^(n) · ... · M^(1)` and `idMatrix` on the empty list.
-/
noncomputable def listMatrixProd {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List (GaugeMatrix I)) : GaugeMatrix I :=
  Ms.reverse.prod

@[simp] theorem listMatrixProd_nil {I : Type u} [Fintype I] [DecidableEq I] :
    listMatrixProd ([] : List (GaugeMatrix I)) = idMatrix :=
  rfl

@[simp] theorem listMatrixProd_singleton {I : Type u} [Fintype I] [DecidableEq I]
    (M : GaugeMatrix I) :
    listMatrixProd [M] = M := by
  simp [listMatrixProd]

theorem listMatrixProd_concat {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List (GaugeMatrix I)) (M : GaugeMatrix I) :
    listMatrixProd (Ms ++ [M]) = gaugeMatrixMul M (listMatrixProd Ms) := by
  simp [listMatrixProd, gaugeMatrixMul]

theorem orderedMatrixProd_eq_listMatrixProd {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (M : Fin n → GaugeMatrix I) :
    orderedMatrixProd M = listMatrixProd (List.ofFn M) := by
  induction n with
  | zero =>
      simp [orderedMatrixProd, listMatrixProd]
  | succ k ih =>
      rw [orderedMatrixProd_succ, List.ofFn_succ', List.concat_eq_append, listMatrixProd_concat]
      rw [ih (fun m => M m.castSucc)]

end LCH02
```

```lean filename=LCH02/IndexPath.lean
/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import LCH02.GaugeMatrix

namespace LCH02

universe u

/--
A finite index path of length `n` from input component `i` to output component `j`:
`nodes 0 = k_0 = i`, intermediate indices `k_1, ..., k_{n-1}`, and `nodes (Fin.last n) = k_n = j`.
-/
@[ext]
structure IndexPath (I : Type u) (n : Nat) (i j : I) where
  nodes : Fin (n + 1) → I
  start_eq : nodes 0 = i
  end_eq : nodes (Fin.last n) = j

/--
The single-step matrix entry `[M^(m)]_{k_{m-1} → k_m}` along step `s` of a path `p`.
-/
def IndexPath.stepEntry {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) (s : Fin n) : ENNReal :=
  matrixEntry (M s) (p.nodes s.castSucc) (p.nodes s.succ)

/--
Construct a length-`(m + 1)` index path from endpoints `i, j` and an intermediate
index sequence `mid : Fin m → I` representing `(k_1, ..., k_m)`.
When `m = 0` (`n = 1`), `mid` is the unique empty sequence and the path is `[i, j]`.
-/
def IndexPath.ofMiddle {I : Type u} {m : Nat} (i j : I) (mid : Fin m → I) :
    IndexPath I (m + 1) i j where
  nodes := Fin.cons i (Fin.snoc mid j)
  start_eq := by simp
  end_eq := by
    have hlast : Fin.last (m + 1) = (Fin.last m).succ := by
      ext
      simp
    rw [hlast, Fin.cons_succ, Fin.snoc_last]

/-- Extract the intermediate index sequence `(k_1, ..., k_m)` of a length-`(m + 1)` path. -/
def IndexPath.middle {I : Type u} {m : Nat} {i j : I}
    (p : IndexPath I (m + 1) i j) : Fin m → I :=
  fun t => p.nodes t.castSucc.succ

/--
Exact bijection between length-`(m + 1)` index paths from `i` to `j`
and intermediate index sequences `(k_1, ..., k_m) : Fin m → I`.
-/
def indexPathEquivMiddle {I : Type u} (m : Nat) (i j : I) :
    IndexPath I (m + 1) i j ≃ (Fin m → I) where
  toFun := IndexPath.middle
  invFun := IndexPath.ofMiddle i j
  left_inv p := by
    ext x
    refine Fin.cases ?_ ?_ x
    · simp [IndexPath.ofMiddle, p.start_eq]
    · intro y
      refine Fin.lastCases ?_ ?_ y
      · have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
          ext
          simp
        simp [IndexPath.ofMiddle, hlast, p.end_eq]
      · intro t
        simp [IndexPath.ofMiddle, IndexPath.middle]
  right_inv mid := by
    funext t
    simp [IndexPath.ofMiddle, IndexPath.middle]

noncomputable instance instFintypeIndexPath {I : Type u} [Fintype I]
    (m : Nat) (i j : I) : Fintype (IndexPath I (m + 1) i j) :=
  Fintype.ofEquiv (Fin m → I) (indexPathEquivMiddle m i j).symm

instance instUniqueIndexPathOne {I : Type u} (i j : I) :
    Unique (IndexPath I 1 i j) where
  default := IndexPath.ofMiddle i j Fin.elim0
  uniq p := by
    apply (indexPathEquivMiddle 0 i j).injective
    funext t
    exact Fin.elim0 t

/-- The product of single-step matrix entries along a path `p`. -/
noncomputable def pathWeight {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) : ENNReal :=
  ∏ s : Fin n, p.stepEntry M s

/-- Predicate stating that every single-step matrix entry along path `p` is strictly positive. -/
def IsPositivePath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) : Prop :=
  ∀ s : Fin n, 0 < p.stepEntry M s

/-- Predicate stating that at least one single-step matrix entry along path `p` is zero. -/
def HasZeroFactorPath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) : Prop :=
  ∃ s : Fin n, p.stepEntry M s = 0

theorem not_isPositivePath_iff_hasZeroFactorPath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    ¬ IsPositivePath M p ↔ HasZeroFactorPath M p := by
  simp [IsPositivePath, HasZeroFactorPath, pos_iff_ne_zero]

theorem not_hasZeroFactorPath_iff_isPositivePath {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    ¬ HasZeroFactorPath M p ↔ IsPositivePath M p := by
  rw [← not_isPositivePath_iff_hasZeroFactorPath, not_not]

private theorem finset_prod_eq_zero_iff_ennreal {α : Type*} (s : Finset α) (f : α → ENNReal) :
    (∏ a ∈ s, f a) = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, mul_eq_zero, ih]
      simp

theorem pathWeight_eq_zero_iff {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    pathWeight M p = 0 ↔ HasZeroFactorPath M p := by
  simpa [pathWeight, HasZeroFactorPath] using
    finset_prod_eq_zero_iff_ennreal (Finset.univ : Finset (Fin n)) (fun s => p.stepEntry M s)

theorem pathWeight_pos_iff {I : Type u} {n : Nat}
    (M : Fin n → GaugeMatrix I) {i j : I} (p : IndexPath I n i j) :
    0 < pathWeight M p ↔ IsPositivePath M p := by
  rw [pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff, ← not_isPositivePath_iff_hasZeroFactorPath,
    not_not]

private theorem ofMiddle_snoc_castSucc {I : Type u} {m : Nat}
    (i j k : I) (mid : Fin m → I) (t : Fin (m + 2)) :
    (IndexPath.ofMiddle i j (Fin.snoc mid k)).nodes t.castSucc =
      (IndexPath.ofMiddle i k mid).nodes t := by
  refine Fin.cases ?_ ?_ t
  · simp [IndexPath.ofMiddle]
  · intro y
    have hsucc : y.succ.castSucc = y.castSucc.succ := by
      ext
      simp
    rw [hsucc]
    simp [IndexPath.ofMiddle]

private def middleSnocEquiv {I : Type u} (m : Nat) :
    (I × (Fin m → I)) ≃ (Fin (m + 1) → I) where
  toFun p := Fin.snoc p.2 p.1
  invFun f := (f (Fin.last m), fun t => f t.castSucc)
  left_inv p := by
    rcases p with ⟨k, mid⟩
    ext
    · simp
    · simp
  right_inv f := by
    funext x
    refine Fin.lastCases ?_ ?_ x
    · simp
    · intro t
      simp

/--
Path expansion formula for an ordered nonempty product of `m + 1` extended nonnegative matrices,
summed over all intermediate index sequences `mid : Fin m → I`.
-/
theorem matrixEntry_orderedMatrixProdNonempty_eq_sum_middle {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j =
      ∑ mid : Fin m → I, pathWeight M (IndexPath.ofMiddle i j mid) := by
  induction m generalizing j with
  | zero =>
      simp only [orderedMatrixProdNonempty_zero, Fintype.sum_unique, pathWeight,
        Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one, IndexPath.stepEntry]
      have h0 : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
      have h1 : (0 : Fin 1).succ = Fin.last 1 := rfl
      rw [h0, h1, (IndexPath.ofMiddle i j default).start_eq,
        (IndexPath.ofMiddle i j default).end_eq]
  | succ m ih =>
      rw [orderedMatrixProdNonempty_succ, matrixEntry_gaugeMatrixMul]
      have h_expand :
          (∑ k : I, matrixEntry (M (Fin.last (m + 1))) k j *
              matrixEntry (orderedMatrixProdNonempty (fun s : Fin (m + 1) => M s.castSucc)) i k) =
            ∑ k : I, ∑ mid : Fin m → I,
              matrixEntry (M (Fin.last (m + 1))) k j *
                pathWeight (fun s : Fin (m + 1) => M s.castSucc) (IndexPath.ofMiddle i k mid) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ih (fun s : Fin (m + 1) => M s.castSucc) k, Finset.mul_sum]
      rw [h_expand, ← Fintype.sum_prod_type']
      refine Fintype.sum_equiv (middleSnocEquiv m) _ _ ?_
      rintro ⟨k, mid⟩
      dsimp [middleSnocEquiv, pathWeight]
      symm
      rw [Fin.prod_univ_castSucc, mul_comm]
      congr 1
      · dsimp [IndexPath.stepEntry]
        have h_prev := ofMiddle_snoc_castSucc i j k mid (Fin.last (m + 1))
        rw [(IndexPath.ofMiddle i k mid).end_eq] at h_prev
        rw [h_prev, (IndexPath.ofMiddle i j (Fin.snoc mid k)).end_eq]
      · refine Finset.prod_congr rfl ?_
        intro s _
        dsimp [IndexPath.stepEntry]
        have h1 := ofMiddle_snoc_castSucc i j k mid s.castSucc
        have h2 := ofMiddle_snoc_castSucc i j k mid s.succ
        have hs : s.castSucc.succ = s.succ.castSucc := by
          ext
          simp
        rw [h1, hs, h2]

/--
Path expansion formula written as a sum over all `p : IndexPath I (m + 1) i j`.
-/
theorem matrixEntry_orderedMatrixProdNonempty_eq_sum_paths {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j =
      ∑ p : IndexPath I (m + 1) i j, pathWeight M p := by
  rw [matrixEntry_orderedMatrixProdNonempty_eq_sum_middle]
  symm
  refine Fintype.sum_equiv (indexPathEquivMiddle m i j) _ _ ?_
  intro p
  have h_inv : IndexPath.ofMiddle i j (indexPathEquivMiddle m i j p) = p :=
    (indexPathEquivMiddle m i j).left_inv p
  rw [h_inv]

/--
**Proposition 2.6 (i) (Zero-value criterion for finite nonempty matrix products)**:
For any `m + 1 ≥ 1` extended nonnegative matrices `M^(1), ..., M^(m+1)` and any `i, j ∈ I`,
`[M^(m+1) · ... · M^(1)]_{i → j} = 0` iff every length-`(m + 1)` index path from `i` to `j`
contains at least one zero factor. Covers `n = 1` (`m = 0`).
-/
theorem orderedMatrixProdNonempty_entry_eq_zero_iff {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j = 0 ↔
      ∀ p : IndexPath I (m + 1) i j, HasZeroFactorPath M p := by
  rw [matrixEntry_orderedMatrixProdNonempty_eq_sum_paths, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

/--
Intermediate-sequence formulation of Proposition 2.6 (i), quantifying explicitly over
`(k_1, ..., k_{n-1}) : Fin m → I` with fixed endpoints `k_0 = i`, `k_n = j`.
-/
theorem orderedMatrixProdNonempty_entry_eq_zero_iff_middle {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProdNonempty M) i j = 0 ↔
      ∀ mid : Fin m → I, HasZeroFactorPath M (IndexPath.ofMiddle i j mid) := by
  rw [matrixEntry_orderedMatrixProdNonempty_eq_sum_middle, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

/--
Proposition 2.6 (i) stated for `orderedMatrixProd` at any length `n ≥ 1`.
-/
theorem orderedMatrixProd_entry_eq_zero_iff {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    matrixEntry (orderedMatrixProd M) i j = 0 ↔
      ∀ p : IndexPath I n i j, HasZeroFactorPath M p := by
  cases n with
  | zero =>
      omega
  | succ m =>
      exact orderedMatrixProdNonempty_entry_eq_zero_iff M i j

/--
Explicit `n = 1` degeneration of Proposition 2.6 (i): the path condition reduces to
the single matrix entry `[M^(1)]_{i → j} = 0`.
-/
theorem orderedMatrixProdNonempty_entry_eq_zero_iff_one {I : Type u} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (∀ p : IndexPath I 1 i j, HasZeroFactorPath M p) ↔ matrixEntry (M 0) i j = 0 := by
  rw [← orderedMatrixProdNonempty_entry_eq_zero_iff M i j, orderedMatrixProdNonempty_zero]

/--
**Proposition 2.6 (ii) (Positivity criterion for finite nonempty matrix products)**:
For any `m + 1 ≥ 1` extended nonnegative matrices `M^(1), ..., M^(m+1)` and any `i, j ∈ I`,
`[M^(m+1) · ... · M^(1)]_{i → j} > 0` iff there exists at least one length-`(m + 1)` index path
from `i` to `j` whose every single-step matrix entry is strictly positive. Covers `n = 1` (`m = 0`).
-/
theorem orderedMatrixProdNonempty_entry_pos_iff {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (orderedMatrixProdNonempty M) i j ↔
      ∃ p : IndexPath I (m + 1) i j, IsPositivePath M p := by
  rw [pos_iff_ne_zero, ne_eq, orderedMatrixProdNonempty_entry_eq_zero_iff]
  push Not
  simp [not_hasZeroFactorPath_iff_isPositivePath]

/--
Intermediate-sequence formulation of Proposition 2.6 (ii), quantifying explicitly over
`(k_1, ..., k_{n-1}) : Fin m → I` with fixed endpoints `k_0 = i`, `k_n = j`.
-/
theorem orderedMatrixProdNonempty_entry_pos_iff_middle {I : Type u} [Fintype I]
    {m : Nat} (M : Fin (m + 1) → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (orderedMatrixProdNonempty M) i j ↔
      ∃ mid : Fin m → I, IsPositivePath M (IndexPath.ofMiddle i j mid) := by
  rw [pos_iff_ne_zero, ne_eq, orderedMatrixProdNonempty_entry_eq_zero_iff_middle]
  push Not
  simp [not_hasZeroFactorPath_iff_isPositivePath]

/--
Proposition 2.6 (ii) stated for `orderedMatrixProd` at any length `n ≥ 1`.
-/
theorem orderedMatrixProd_entry_pos_iff {I : Type u} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < matrixEntry (orderedMatrixProd M) i j ↔
      ∃ p : IndexPath I n i j, IsPositivePath M p := by
  cases n with
  | zero =>
      omega
  | succ m =>
      exact orderedMatrixProdNonempty_entry_pos_iff M i j

/--
Explicit `n = 1` degeneration of Proposition 2.6 (ii): the path condition reduces to
the single matrix entry `[M^(1)]_{i → j} > 0`.
-/
theorem orderedMatrixProdNonempty_entry_pos_iff_one {I : Type u} [Fintype I]
    (M : Fin 1 → GaugeMatrix I) (i j : I) :
    (∃ p : IndexPath I 1 i j, IsPositivePath M p) ↔ 0 < matrixEntry (M 0) i j := by
  rw [← orderedMatrixProdNonempty_entry_pos_iff M i j, orderedMatrixProdNonempty_zero]

end LCH02
```

```lean filename=LCH02/LipBounds.lean
/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.GaugeMatrix

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

/--
**Definition (Global Lipschitz matrix)**:
A gauge matrix `L` is a valid global Lipschitz matrix for operator `ϕ` if for all
`x, y ∈ dom ϕ` and all output components `j ∈ I`,
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} · d_i(x, y)`.
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y

/-- The family `ℒ(ϕ)` of all valid global Lipschitz matrices for `ϕ`. -/
def LipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
**Definition (Subset-restricted Lipschitz matrix)**:
For a subset `U ⊆ dom ϕ`, `L` is a valid restricted Lipschitz matrix for `ϕ` on `U`
if `U ⊆ dom ϕ` and for all `x, y ∈ U` and all `j ∈ I`,
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} · d_i(x, y)`.
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y

/-- The family `ℒ(ϕ)|_U` of all valid restricted Lipschitz matrices for `ϕ` on `U`. -/
def RestrictedLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem isLipMatrix_iff_restricted_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsLipMatrix d ϕ L ↔ IsRestrictedLipMatrix d ϕ (dom ϕ) L := by
  simp [IsLipMatrix, IsRestrictedLipMatrix]

theorem lipFamily_eq_restricted_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    LipFamily d ϕ = RestrictedLipFamily d ϕ (dom ϕ) := by
  ext L
  exact isLipMatrix_iff_restricted_dom d ϕ L

/--
**Definition (Subset-restricted co-Lipschitz matrix)**:
For a nonempty subset `U ⊆ dom ϕ`, `K` is a valid restricted co-Lipschitz matrix for `ϕ` on `U`
if `U.Nonempty`, `U ⊆ dom ϕ`, and for all `x, y ∈ U` and all `j ∈ I`,
`∑_{i ∈ I} K_{i → j} · d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))`.
Following §2.1, every appearance of `𝒦(ϕ)|_U` enforces the nonemptiness condition `U ≠ ∅`.
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, matrixEntry K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

/-- The family `𝒦(ϕ)|_U` of all valid restricted co-Lipschitz matrices for `ϕ` on `U`. -/
def RestrictedCoLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

theorem restrictedCoLipFamily_nonempty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ RestrictedCoLipFamily d ϕ U) : U.Nonempty :=
  hK.1

theorem restrictedCoLipFamily_subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ RestrictedCoLipFamily d ϕ U) : U ⊆ dom ϕ :=
  hK.2.1

theorem restrictedCoLipFamily_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    RestrictedCoLipFamily d ϕ ∅ = ∅ := by
  ext K
  simp [RestrictedCoLipFamily, IsRestrictedCoLipMatrix]

/--
**Remark (Scalar Lip bound in the single-component case)**:
When `I = {i}` (every index equals `i`), the Lip matrix condition degenerates to the
single scalar inequality `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} · d_i(x, y)` for `x, y ∈ dom ϕ`.
-/
theorem isLipMatrix_iff_scalar_of_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hI : ∀ k : I, k = i) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y := by
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext k
    simp [hI k]
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    simpa [huniv] using h
  · intro hscalar x hx y hy j
    have hj : j = i := hI j
    subst hj
    simpa [huniv] using hscalar x hx y hy

/--
Single-component scalar Lip bound formulated directly with `Fintype.card I = 1` and `i : I`.
-/
theorem isLipMatrix_iff_scalar_of_card_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y := by
  apply isLipMatrix_iff_scalar_of_singleton d ϕ L i
  intro k
  exact Fintype.card_le_one_iff.mp hcard.le k i

/-- Single-component scalar Lip bound for `[Unique I]`. -/
theorem isLipMatrix_iff_scalar_unique {X I : Type} {bot : X} [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d default (ϕ.func x) (ϕ.func y) ≤ matrixEntry L default default * d default x y :=
  isLipMatrix_iff_scalar_of_singleton d ϕ L default Unique.eq_default

/--
**Lemma 2.1 (Antimonotonicity of restricted Lip families)**:
If `U ⊆ V ⊆ dom ϕ`, then `ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U`.
-/
theorem restrictedLipFamily_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipFamily d ϕ V ⊆ RestrictedLipFamily d ϕ U := by
  intro L hL
  refine ⟨hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
**Lemma 2.1 (Restriction of global Lip certificates)**:
For any `U ⊆ dom ϕ`, `ℒ(ϕ) ⊆ ℒ(ϕ)|_U`.
-/
theorem lipFamily_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom ϕ) :
    LipFamily d ϕ ⊆ RestrictedLipFamily d ϕ U := by
  rw [lipFamily_eq_restricted_dom]
  exact restrictedLipFamily_antitone d ϕ hU Set.Subset.rfl

/-- Domain inclusion for composition: `dom (ϕ₂ ∘ ϕ₁) ⊆ dom ϕ₁`. -/
theorem dom_mul_subset_dom_right {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) :
    dom (ϕ₂ * ϕ₁) ⊆ dom ϕ₁ := by
  intro x hx hbot
  apply hx
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [hbot, ϕ₂.preserves_bot]

/-- Image-domain inclusion for composition: if `U₁ ⊆ dom (ϕ₂ ∘ ϕ₁)`, then `ϕ₁(U₁) ⊆ dom ϕ₂`. -/
theorem operator_image_subset_dom_left_of_subset_dom_mul {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) :
    operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU₁ hx

/-- Exact characterization of subsets of `dom (ϕ₂ ∘ ϕ₁)`. -/
theorem subset_dom_mul_iff {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U₁ : Set X) :
    U₁ ⊆ dom (ϕ₂ * ϕ₁) ↔ U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  constructor
  · intro hU₁
    exact ⟨hU₁.trans (dom_mul_subset_dom_right ϕ₁ ϕ₂),
      operator_image_subset_dom_left_of_subset_dom_mul ϕ₁ ϕ₂ hU₁⟩
  · rintro ⟨_, hU₂⟩ x hx
    exact hU₂ ⟨x, hx, rfl⟩

/-- Nonemptiness is preserved by taking the operator image `ϕ(U)`. -/
theorem operator_image_nonempty {X : Type} {bot : X}
    (ϕ : Operator X bot) {U : Set X} (hU : U.Nonempty) :
    (operator_image ϕ U).Nonempty := by
  rcases hU with ⟨x, hx⟩
  exact ⟨ϕ.func x, x, hx, rfl⟩

/--
**Proposition 2.2 (Two-step Lip matrix composition law)**:
For `ϕ₂ ∘ ϕ₁` and `U₁ ⊆ dom (ϕ₂ ∘ ϕ₁)` with exact intermediate image `U₂ = ϕ₁(U₁)`,
if `L₁ ∈ ℒ(ϕ₁)|_{U₁}` and `L₂ ∈ ℒ(ϕ₂)|_{U₂}`, then `L₂ · L₁ ∈ ℒ(ϕ₂ ∘ ϕ₁)|_{U₁}`.
-/
theorem restrictedLipFamily_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ RestrictedLipFamily d ϕ₁ U₁)
    (hL₂ : L₂ ∈ RestrictedLipFamily d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul L₂ L₁ ∈ RestrictedLipFamily d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
        = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, matrixEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
        hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ ≤ ∑ k : I, matrixEntry L₂ k j * (∑ i : I, matrixEntry L₁ i k * d i x y) := by
        refine Finset.sum_le_sum ?_
        intro k _
        exact mul_le_mul_of_nonneg_left (hL₁.2 x hx y hy k) (zero_le _)
    _ = ∑ k : I, ∑ i : I, matrixEntry L₂ k j * (matrixEntry L₁ i k * d i x y) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, (matrixEntry L₂ k j * matrixEntry L₁ i k) * d i x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [mul_assoc]
    _ = ∑ i : I, (∑ k : I, matrixEntry L₂ k j * matrixEntry L₁ i k) * d i x y := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← Finset.sum_mul]
    _ = ∑ i : I, matrixEntry (gaugeMatrixMul L₂ L₁) i j * d i x y := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [matrixEntry_gaugeMatrixMul]

/--
**Lemma 2.3 (Antimonotonicity of nonempty restricted co-Lip families)**:
If `∅ ≠ U ⊆ V ⊆ dom ϕ`, then `𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U`.
-/
theorem restrictedCoLipFamily_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hU_ne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedCoLipFamily d ϕ V ⊆ RestrictedCoLipFamily d ϕ U := by
  intro K hK
  refine ⟨hU_ne, hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/--
**Lemma 2.3 (Restriction of global co-Lip certificates)**:
For any nonempty subset `U ⊆ dom ϕ`, `𝒦(ϕ)|_{dom ϕ} ⊆ 𝒦(ϕ)|_U`.
-/
theorem globalCoLipFamily_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    RestrictedCoLipFamily d ϕ (dom ϕ) ⊆ RestrictedCoLipFamily d ϕ U :=
  restrictedCoLipFamily_antitone d ϕ hU_ne hU Set.Subset.rfl

/--
**Remark (Sufficient condition for a restricted co-Lip entry to be zero)**:
If `K ∈ 𝒦(ϕ)|_U` and there exist `x, y ∈ U` with `d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`,
then `K_{i → j} = 0`.
-/
theorem restrictedCoLip_entry_eq_zero_of_collapse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {K : GaugeMatrix I} (hK : K ∈ RestrictedCoLipFamily d ϕ U)
    {i j : I}
    (h_pair : ∃ x ∈ U, ∃ y ∈ U, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y) :
    matrixEntry K i j = 0 := by
  rcases h_pair with ⟨x, hx, y, hy, hzero, hpos⟩
  have hterm_le_sum :
      matrixEntry K i j * d i x y ≤ ∑ k : I, matrixEntry K k j * d k x y :=
    Finset.single_le_sum (fun k _ => zero_le (matrixEntry K k j * d k x y)) (Finset.mem_univ i)
  have hprod_le_zero : matrixEntry K i j * d i x y ≤ 0 := by
    calc
      matrixEntry K i j * d i x y
          ≤ ∑ k : I, matrixEntry K k j * d k x y := hterm_le_sum
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hzero
  have hprod_eq_zero : matrixEntry K i j * d i x y = 0 :=
    le_antisymm hprod_le_zero (zero_le _)
  rcases mul_eq_zero.mp hprod_eq_zero with hK0 | hd0
  · exact hK0
  · exact absurd hd0 (ne_of_gt hpos)

/--
**Remark (Sufficient condition for a global co-Lip entry to be zero)**:
If there exist `x, y ∈ dom ϕ` with `d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`,
then every global co-Lip matrix `K ∈ 𝒦(ϕ)|_{dom ϕ}` satisfies `K_{i → j} = 0`.
-/
theorem globalCoLip_entry_eq_zero_of_collapse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {K : GaugeMatrix I} (hK : K ∈ RestrictedCoLipFamily d ϕ (dom ϕ))
    {i j : I}
    (h_pair : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y) :
    matrixEntry K i j = 0 :=
  restrictedCoLip_entry_eq_zero_of_collapse d ϕ hK h_pair

/--
**Proposition 2.4 (Two-step co-Lip matrix composition law)**:
For `ϕ₂ ∘ ϕ₁` and `U₁ ⊆ dom (ϕ₂ ∘ ϕ₁)` with exact intermediate image `U₂ = ϕ₁(U₁)`,
if `K₁ ∈ 𝒦(ϕ₁)|_{U₁}` and `K₂ ∈ 𝒦(ϕ₂)|_{U₂}` (both carrying nonemptiness),
then `K₂ · K₁ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}`.
-/
theorem restrictedCoLipFamily_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ RestrictedCoLipFamily d ϕ₁ U₁)
    (hK₂ : K₂ ∈ RestrictedCoLipFamily d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul K₂ K₁ ∈ RestrictedCoLipFamily d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matrixEntry (gaugeMatrixMul K₂ K₁) i j * d i x y
        = ∑ i : I, (∑ k : I, matrixEntry K₂ k j * matrixEntry K₁ i k) * d i x y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [matrixEntry_gaugeMatrixMul]
    _ = ∑ i : I, ∑ k : I, (matrixEntry K₂ k j * matrixEntry K₁ i k) * d i x y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, matrixEntry K₂ k j * (matrixEntry K₁ i k * d i x y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [mul_assoc]
    _ = ∑ k : I, matrixEntry K₂ k j * (∑ i : I, matrixEntry K₁ i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [← Finset.mul_sum]
    _ ≤ ∑ k : I, matrixEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_of_nonneg_left (hK₁.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
          hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

/-- Exact evaluation identity for the identity gauge matrix on any distance family. -/
theorem sum_idMatrix_mul_dist {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, matrixEntry (idMatrix : GaugeMatrix I) i j * d i x y) = d j x y := by
  simp only [matrixEntry_idMatrix]
  simp

/--
**Remark (Zero-step identity operator — Lip certificate)**:
For any `U ⊆ dom id_X`, the identity matrix satisfies `I ∈ ℒ(id_X)|_U`.
-/
theorem idMatrix_mem_restrictedLipFamily_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedLipFamily d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  change d j x y ≤ ∑ i : I, matrixEntry (idMatrix : GaugeMatrix I) i j * d i x y
  rw [sum_idMatrix_mul_dist]

/-- Global Lip certificate for the identity operator: `I ∈ ℒ(id_X)`. -/
theorem idMatrix_mem_lipFamily_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    idMatrix ∈ LipFamily d (operator_identity (X := X) (bot := bot)) := by
  rw [lipFamily_eq_restricted_dom]
  exact idMatrix_mem_restrictedLipFamily_identity d Set.Subset.rfl

/--
**Remark (Zero-step identity operator — co-Lip certificate)**:
For any nonempty `U ⊆ dom id_X`, the identity matrix satisfies `I ∈ 𝒦(id_X)|_U`.
-/
theorem idMatrix_mem_restrictedCoLipFamily_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedCoLipFamily d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, ?_⟩
  intro x _ y _ j
  change (∑ i : I, matrixEntry (idMatrix : GaugeMatrix I) i j * d i x y) ≤ d j x y
  rw [sum_idMatrix_mul_dist]

/--
Combined zero-step identity remark:
for any nonempty `U ⊆ dom id_X`, `I ∈ ℒ(id_X)|_U ∩ 𝒦(id_X)|_U`.
-/
theorem idMatrix_mem_restrictedLip_inter_coLip_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈
      RestrictedLipFamily d (operator_identity (X := X) (bot := bot)) U ∩
        RestrictedCoLipFamily d (operator_identity (X := X) (bot := bot)) U :=
  ⟨idMatrix_mem_restrictedLipFamily_identity d hU,
    idMatrix_mem_restrictedCoLipFamily_identity d hU_ne hU⟩

end LCH02
```

```lean filename=LCH02/FiniteComposition.lean
/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.GaugeMatrix
import LCH02.LipBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

/--
Finite composition `c_k = ϕ_k ∘ ... ∘ ϕ_1` of operators given in chronological step order
`ϕs : Fin k → Operator X bot` (where `ϕs 0 = ϕ_1` acts first and `ϕs (Fin.last _) = ϕ_k` acts last).
For `k = 0`, `c_0 = id_X = operator_identity`.
-/
def chainCompose {X : Type} {bot : X} :
    {k : Nat} → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => operator_identity
  | _ + 1, ϕs => ϕs (Fin.last _) * chainCompose (fun m => ϕs m.castSucc)

@[simp] theorem chainCompose_zero {X : Type} {bot : X} (ϕs : Fin 0 → Operator X bot) :
    chainCompose ϕs = operator_identity :=
  rfl

@[simp] theorem chainCompose_one {X : Type} {bot : X} (ϕs : Fin 1 → Operator X bot) :
    chainCompose ϕs = ϕs 0 := by
  change ϕs 0 * operator_identity = ϕs 0
  exact mul_one (ϕs 0)

theorem chainCompose_succ {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) :
    chainCompose ϕs = ϕs (Fin.last k) * chainCompose (fun m => ϕs m.castSucc) :=
  rfl

theorem chainCompose_eq_listProd {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) :
    chainCompose ϕs = (List.ofFn ϕs).reverse.prod := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [chainCompose_succ, List.ofFn_succ', List.concat_eq_append]
      simp [ih (fun m => ϕs m.castSucc)]

/--
Chain representation correspondence (forward):
the chronological composition `c_k = ϕ_k ∘ ... ∘ ϕ_1` coincides with the frozen prerequisite
`OperatorChain` applied to the reversed (outermost-first) list `[ϕ_k, ..., ϕ_1]`.
-/
theorem chainCompose_eq_operatorChain_reverse {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) :
    chainCompose ϕs = OperatorChain (List.ofFn ϕs).reverse := by
  rw [chainCompose_eq_listProd, operator_chain_eq_prod]

/--
Extract chronological step operators `(ϕ_1, ..., ϕ_k)` from an outermost-first list
`ops = [ϕ_k, ..., ϕ_1]` as used by `OperatorChain`.
-/
def stepsOfOperatorChain {X : Type} {bot : X} (ops : List (Operator X bot)) :
    Fin ops.length → Operator X bot :=
  fun m => ops.reverse[m.val]'(by simp [m.isLt])

theorem list_ofFn_stepsOfOperatorChain {X : Type} {bot : X} (ops : List (Operator X bot)) :
    List.ofFn (stepsOfOperatorChain ops) = ops.reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [stepsOfOperatorChain]

/--
Chain representation correspondence (backward):
every `OperatorChain ops` equals `chainCompose (stepsOfOperatorChain ops)`.
-/
theorem operatorChain_eq_chainCompose {X : Type} {bot : X}
    (ops : List (Operator X bot)) :
    OperatorChain ops = chainCompose (stepsOfOperatorChain ops) := by
  rw [chainCompose_eq_operatorChain_reverse, list_ofFn_stepsOfOperatorChain, List.reverse_reverse]

/--
Actual intermediate image domains `U_1, U_2, ..., U_{k+1}` along a finite operator chain:
- `intermediateDomain ϕs U₁ 0 = U₁`
- `intermediateDomain ϕs U₁ (m + 1) = ϕ_m(U_m)` (`operator_image (ϕs m) (U_m)`).
Index `m.castSucc` is the actual input domain `U_m` of step `m`.
-/
def intermediateDomain {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕs m) Um)

@[simp] theorem intermediateDomain_zero {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) :
    intermediateDomain ϕs U₁ 0 = U₁ :=
  Fin.induction_zero _ _

theorem intermediateDomain_succ {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    intermediateDomain ϕs U₁ m.succ =
      operator_image (ϕs m) (intermediateDomain ϕs U₁ m.castSucc) :=
  Fin.induction_succ _ _ m

/-- Intermediate domains of a prefix chain match the initial segment of the full chain. -/
theorem intermediateDomain_prefix {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) (U₁ : Set X) (t : Fin (k + 1)) :
    intermediateDomain (fun m : Fin k => ϕs m.castSucc) U₁ t =
      intermediateDomain ϕs U₁ t.castSucc := by
  refine Fin.induction ?_ ?_ t
  · simp [intermediateDomain_zero]
  · intro m ih
    have hsucc : m.succ.castSucc = m.castSucc.succ := by
      ext
      simp
    rw [intermediateDomain_succ, hsucc, intermediateDomain_succ, ih]

theorem operator_image_identity {X : Type} {bot : X} (U : Set X) :
    operator_image (operator_identity (X := X) (bot := bot)) U = U := by
  ext x
  simp [operator_image, operator_identity]

theorem operator_image_mul {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    operator_image (ϕ₂ * ϕ₁) U = operator_image ϕ₂ (operator_image ϕ₁ U) := by
  ext z
  simp [operator_image]
  rfl

/-- The final intermediate image domain `U_{k+1}` equals the image of `U₁` under `c_k`. -/
theorem intermediateDomain_last {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) :
    intermediateDomain ϕs U₁ (Fin.last k) = operator_image (chainCompose ϕs) U₁ := by
  induction k with
  | zero =>
      simp [intermediateDomain_zero, chainCompose_zero, operator_image_identity]
  | succ k ih =>
      have hlast : Fin.last (k + 1) = (Fin.last k).succ := by
        ext
        simp
      rw [hlast, intermediateDomain_succ, ← intermediateDomain_prefix,
        ih (fun m => ϕs m.castSucc), chainCompose_succ, operator_image_mul]

/--
Domain propagation along a finite chain (proof step of Corollary 2.5):
if `U₁ ⊆ dom c_k`, then every actual intermediate domain satisfies `U_m ⊆ dom ϕ_m`.
-/
theorem intermediateDomain_subset_dom {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs)) :
    ∀ m : Fin k, intermediateDomain ϕs U₁ m.castSucc ⊆ dom (ϕs m) := by
  induction k with
  | zero =>
      intro m
      exact Fin.elim0 m
  | succ k ih =>
      rw [chainCompose_succ, subset_dom_mul_iff] at hU₁
      rcases hU₁ with ⟨hU₁_init, hU_last⟩
      intro m
      refine Fin.lastCases ?_ ?_ m
      · rw [← intermediateDomain_prefix, intermediateDomain_last]
        exact hU_last
      · intro m'
        rw [← intermediateDomain_prefix]
        exact ih (fun i => ϕs i.castSucc) hU₁_init m'

/-- Nonemptiness propagation: if `U₁` is nonempty, every intermediate domain `U_m` is nonempty. -/
theorem intermediateDomain_nonempty {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) {U₁ : Set X} (hU₁ : U₁.Nonempty) :
    ∀ t : Fin (k + 1), (intermediateDomain ϕs U₁ t).Nonempty := by
  intro t
  refine Fin.induction ?_ ?_ t
  · simpa [intermediateDomain_zero] using hU₁
  · intro m ih
    rw [intermediateDomain_succ]
    exact operator_image_nonempty (ϕs m) ih

/--
**Corollary 2.5 (i) (Local Lip matrix bound for finite composition, `k + 1 ≥ 1`)**:
For any positive-length chain `c_{k+1} = ϕ_{k+1} ∘ ... ∘ ϕ_1` and `U₁ ⊆ dom c_{k+1}`,
if each step `m` has a local Lip certificate `L^(m) ∈ ℒ(ϕ_m)|_{U_m}` on the actual
intermediate domain `U_m`, then the ordered product `L^(k+1) · ... · L^(1)` lies in
`ℒ(c_{k+1})|_{U₁}`.
-/
theorem chain_restrictedLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ls : Fin (k + 1) → GaugeMatrix I)
    (hLs : ∀ m : Fin (k + 1),
      Ls m ∈ RestrictedLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProdNonempty Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U₁ := by
  induction k with
  | zero =>
      have h0 := hLs 0
      simpa [chainCompose_one, orderedMatrixProdNonempty_zero, intermediateDomain_zero] using h0
  | succ k ih =>
      let ϕs_init : Fin (k + 1) → Operator X bot := fun m => ϕs m.castSucc
      let Ls_init : Fin (k + 1) → GaugeMatrix I := fun m => Ls m.castSucc
      have hU₁_split : U₁ ⊆ dom (ϕs (Fin.last (k + 1)) * chainCompose ϕs_init) := hU₁
      have hU₁_init : U₁ ⊆ dom (chainCompose ϕs_init) :=
        (subset_dom_mul_iff (chainCompose ϕs_init) (ϕs (Fin.last (k + 1))) U₁).mp hU₁_split |>.1
      have hLs_init : ∀ m : Fin (k + 1),
          Ls_init m ∈ RestrictedLipFamily d (ϕs_init m) (intermediateDomain ϕs_init U₁ m.castSucc) := by
        intro m
        rw [intermediateDomain_prefix]
        exact hLs m.castSucc
      have h_init := ih ϕs_init hU₁_init Ls_init hLs_init
      have h_last : Ls (Fin.last (k + 1)) ∈
          RestrictedLipFamily d (ϕs (Fin.last (k + 1)))
            (operator_image (chainCompose ϕs_init) U₁) := by
        have h := hLs (Fin.last (k + 1))
        rw [← intermediateDomain_prefix, intermediateDomain_last] at h
        exact h
      rw [chainCompose_succ, orderedMatrixProdNonempty_succ]
      exact restrictedLipFamily_comp d (chainCompose ϕs_init) (ϕs (Fin.last (k + 1)))
        hU₁_split h_init h_last

/--
Corollary 2.5 (i) stated for `orderedMatrixProd` at any positive length `1 ≤ k`.
-/
theorem chain_restrictedLipFamily_of_pos {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : Nat} (hk : 1 ≤ k)
    (ϕs : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ls : Fin k → GaugeMatrix I)
    (hLs : ∀ m : Fin k,
      Ls m ∈ RestrictedLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProd Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U₁ := by
  cases k with
  | zero =>
      omega
  | succ k' =>
      exact chain_restrictedLipFamily d ϕs hU₁ Ls hLs

/--
**Corollary 2.5 (ii) (Local co-Lip matrix bound for finite composition, `k + 1 ≥ 1`)**:
For any positive-length chain `c_{k+1} = ϕ_{k+1} ∘ ... ∘ ϕ_1` and `U₁ ⊆ dom c_{k+1}`,
if each step `m` has a local co-Lip certificate `K^(m) ∈ 𝒦(ϕ_m)|_{U_m}` on the actual
intermediate domain `U_m`, then the ordered product `K^(k+1) · ... · K^(1)` lies in
`𝒦(c_{k+1})|_{U₁}`.
-/
theorem chain_restrictedCoLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ks : Fin (k + 1) → GaugeMatrix I)
    (hKs : ∀ m : Fin (k + 1),
      Ks m ∈ RestrictedCoLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProdNonempty Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U₁ := by
  induction k with
  | zero =>
      have h0 := hKs 0
      simpa [chainCompose_one, orderedMatrixProdNonempty_zero, intermediateDomain_zero] using h0
  | succ k ih =>
      let ϕs_init : Fin (k + 1) → Operator X bot := fun m => ϕs m.castSucc
      let Ks_init : Fin (k + 1) → GaugeMatrix I := fun m => Ks m.castSucc
      have hU₁_split : U₁ ⊆ dom (ϕs (Fin.last (k + 1)) * chainCompose ϕs_init) := hU₁
      have hU₁_init : U₁ ⊆ dom (chainCompose ϕs_init) :=
        (subset_dom_mul_iff (chainCompose ϕs_init) (ϕs (Fin.last (k + 1))) U₁).mp hU₁_split |>.1
      have hKs_init : ∀ m : Fin (k + 1),
          Ks_init m ∈
            RestrictedCoLipFamily d (ϕs_init m) (intermediateDomain ϕs_init U₁ m.castSucc) := by
        intro m
        rw [intermediateDomain_prefix]
        exact hKs m.castSucc
      have h_init := ih ϕs_init hU₁_init Ks_init hKs_init
      have h_last : Ks (Fin.last (k + 1)) ∈
          RestrictedCoLipFamily d (ϕs (Fin.last (k + 1)))
            (operator_image (chainCompose ϕs_init) U₁) := by
        have h := hKs (Fin.last (k + 1))
        rw [← intermediateDomain_prefix, intermediateDomain_last] at h
        exact h
      rw [chainCompose_succ, orderedMatrixProdNonempty_succ]
      exact restrictedCoLipFamily_comp d (chainCompose ϕs_init) (ϕs (Fin.last (k + 1)))
        hU₁_split h_init h_last

/--
Corollary 2.5 (ii) stated for `orderedMatrixProd` at any positive length `1 ≤ k`.
-/
theorem chain_restrictedCoLipFamily_of_pos {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : Nat} (hk : 1 ≤ k)
    (ϕs : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ks : Fin k → GaugeMatrix I)
    (hKs : ∀ m : Fin k,
      Ks m ∈ RestrictedCoLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProd Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U₁ := by
  cases k with
  | zero =>
      omega
  | succ k' =>
      exact chain_restrictedCoLipFamily d ϕs hU₁ Ks hKs

/--
**Remark (Zero-step boundary `k = 0`, Lip certificate)**:
For the empty chain `c_0 = id_X` and empty matrix product `I`,
`orderedMatrixProd Ls ∈ ℒ(c_0)|_U` for every `U ⊆ dom c_0`.
-/
theorem zeroStep_chain_restrictedLipFamily {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal)
    (ϕs : Fin 0 → Operator X bot) (Ls : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU : U ⊆ dom (chainCompose ϕs)) :
    orderedMatrixProd Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U := by
  simpa [chainCompose_zero, orderedMatrixProd_zero] using
    idMatrix_mem_restrictedLipFamily_identity d hU

/--
**Remark (Zero-step boundary `k = 0`, co-Lip certificate)**:
For the empty chain `c_0 = id_X` and empty matrix product `I`,
`orderedMatrixProd Ks ∈ 𝒦(c_0)|_U` for every nonempty `U ⊆ dom c_0`.
-/
theorem zeroStep_chain_restrictedCoLipFamily {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal)
    (ϕs : Fin 0 → Operator X bot) (Ks : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (chainCompose ϕs)) :
    orderedMatrixProd Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U := by
  simpa [chainCompose_zero, orderedMatrixProd_zero] using
    idMatrix_mem_restrictedCoLipFamily_identity d hU_ne hU

end LCH02
```

```lean filename=Main.lean
/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import LCH02.GaugeMatrix
import LCH02.IndexPath
import LCH02.LipBounds
import LCH02.FiniteComposition
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
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.IsLipMatrix" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.LipFamily" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.IsRestrictedLipMatrix" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.RestrictedLipFamily" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.isLipMatrix_iff_restricted_dom" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.lipFamily_eq_restricted_dom" }
      ],
      "representation": "点空间 X、吸收元 bot、有限指标集 I（[Fintype I]）、分量扩展非负距离族 d : I → X → X → ENNReal 与算子 ϕ : Operator X bot（导入自 formal_oet）；全域 Lip 矩阵谓词 IsLipMatrix d ϕ L 量化 ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I 要求 d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y，证书族 LipFamily d ϕ 对应 ℒ(ϕ)；受限 Lip 矩阵谓词 IsRestrictedLipMatrix d ϕ U L 显式要求 U ⊆ dom ϕ 且对所有 x, y ∈ U 与 j : I 满足同一放缩不等式，证书族 RestrictedLipFamily d ϕ U 对应 ℒ(ϕ)|_U，并证明 U = dom ϕ 时两者等价。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.IsRestrictedCoLipMatrix" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.RestrictedCoLipFamily" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedCoLipFamily_nonempty" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedCoLipFamily_subset_dom" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedCoLipFamily_empty" }
      ],
      "representation": "受限 co-Lip 矩阵谓词 IsRestrictedCoLipMatrix d ϕ U K 显式包含非空性条件 U.Nonempty、定义域条件 U ⊆ dom ϕ，以及 ∀ x ∈ U, ∀ y ∈ U, ∀ j : I, (∑ i : I, matrixEntry K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)；证书族 RestrictedCoLipFamily d ϕ U 对应 𝒦(ϕ)|_U（当 U = ∅ 时证书族为空，对应原文“凡出现 𝒦(ϕ)|_U 均包含 U ≠ ∅”）。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.GaugeMatrix" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.matrixEntry" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.gaugeMatrixOfEntries" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.gaugeMatrixMul" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.matrixEntry_gaugeMatrixMul" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.gaugeMatrixMul_assoc" }
      ],
      "representation": "扩展非负矩阵表示为 GaugeMatrix I := Matrix I I ENNReal（条目取值于 ENNReal 对应 ℝ̄_+，遵循 0·∞=0 与 a·∞=∞ 算术约定）；按原文输出为行、输入为列约定，matrixEntry M i j := M j i 对应 (M)_{j,i} = M_{i→j}；gaugeMatrixMul A B := A * B 满足 matrixEntry_gaugeMatrixMul：(A · B)_{i→j} = ∑ k : I, A_{k→j} * B_{i→k}，且结合律成立。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.idMatrix" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.matrixEntry_idMatrix" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.orderedMatrixProdNonempty" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.orderedMatrixProd" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.listMatrixProd" },
        { "file": "LCH02/GaugeMatrix.lean", "name": "LCH02.orderedMatrixProd_eq_listMatrixProd" }
      ],
      "representation": "单位矩阵 idMatrix := (1 : Matrix I I ENNReal) 满足 matrixEntry idMatrix i j = if i = j then 1 else 0；对按步序给出的非空有限矩阵族 M : Fin (n + 1) → GaugeMatrix I（M 0 为 M^(1)，M (Fin.last n) 为 M^(n+1)），orderedMatrixProdNonempty M 计算复合序乘积 M^(n+1) · ... · M^(1)（n = 0 时为 M 0，无需 DecidableEq I）；orderedMatrixProd 对任意长度 n : Nat 扩展该乘积并在空乘积 n = 0 时取 idMatrix；listMatrixProd Ms := Ms.reverse.prod 给出列表形式并与 orderedMatrixProd 一致。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.chainCompose" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.chainCompose_eq_operatorChain_reverse" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.stepsOfOperatorChain" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.operatorChain_eq_chainCompose" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.intermediateDomain" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.intermediateDomain_zero" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.intermediateDomain_succ" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.intermediateDomain_last" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.intermediateDomain_subset_dom" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.intermediateDomain_nonempty" }
      ],
      "representation": "按执行步序 ϕs : Fin k → Operator X bot（ϕs 0 = ϕ_1 最先作用，ϕs (Fin.last _) = ϕ_k 最后作用），chainCompose ϕs 定义 c_k = ϕ_k ∘ ... ∘ ϕ_1 且 c_0 = operator_identity；通过 chainCompose_eq_operatorChain_reverse 与 operatorChain_eq_chainCompose 双向建立其与前置冻结定义 formal_oet.vol_01.ch_01_foundations.OperatorChain（表头最后作用）的精确反转对应；intermediateDomain ϕs U₁ : Fin (k + 1) → Set X 递归定义实际中间像域 U_1 = U₁、U_{m+1} = operator_image (ϕs m) U_m，并证明末像域等于 operator_image (chainCompose ϕs) U₁、U₁ ⊆ dom c_k 蕴含各步 U_m ⊆ dom ϕ_m 以及非空性逐级保持。",
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.IndexPath" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.IndexPath.stepEntry" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.IndexPath.ofMiddle" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.IndexPath.middle" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.indexPathEquivMiddle" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.pathWeight" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.IsPositivePath" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.HasZeroFactorPath" }
      ],
      "representation": "IndexPath I n i j 表示长度 n、起点 nodes 0 = i（k_0 = i）、终点 nodes (Fin.last n) = j（k_n = j）的有限指标路径；indexPathEquivMiddle 建立 IndexPath I (m + 1) i j 与中间指标序列 (k_1, ..., k_m) : Fin m → I 的显式双射（m = 0 即 n = 1 时唯一对应空序列）；p.stepEntry M s 给出单步条目 [M^(s)]_{k_{s-1}→k_s}；IsPositivePath M p 定义全正路径谓词 ∀ s : Fin n, 0 < p.stepEntry M s，HasZeroFactorPath M p 定义含零因子谓词 ∃ s : Fin n, p.stepEntry M s = 0，pathWeight M p 为沿路径各单步条目连乘。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.isLipMatrix_iff_scalar_of_singleton" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.isLipMatrix_iff_scalar_of_card_one" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.isLipMatrix_iff_scalar_unique" }
      ],
      "representation": "在单分量情形下（分别以 ∀ k : I, k = i、Fintype.card I = 1 ∧ i : I 以及 [Unique I] 表述 |I| = 1 且 I = {i}），证明 IsLipMatrix d ϕ L 当且仅当对所有 x, y ∈ dom ϕ 有标量不等式 d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedLipFamily_antitone" }
      ],
      "representation": "对应引理 2.1 第一部分：固定算子 ϕ 与子集 U ⊆ V ⊆ dom ϕ，证明 RestrictedLipFamily d ϕ V ⊆ RestrictedLipFamily d ϕ U（即 ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U）。",
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedLipFamily_comp" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.subset_dom_mul_iff" }
      ],
      "representation": "对应命题 2.2：对复合算子 ϕ₂ * ϕ₁（即 ϕ₂ ∘ ϕ₁）、起始子集 U₁ ⊆ dom (ϕ₂ * ϕ₁) 及精确中间像域 U₂ = operator_image ϕ₁ U₁（subset_dom_mul_iff 显式保证 U₁ ⊆ dom ϕ₁ 且 U₂ ⊆ dom ϕ₂），若 L₁ ∈ RestrictedLipFamily d ϕ₁ U₁ 且 L₂ ∈ RestrictedLipFamily d ϕ₂ (operator_image ϕ₁ U₁)，则按乘积次序 gaugeMatrixMul L₂ L₁ ∈ RestrictedLipFamily d (ϕ₂ * ϕ₁) U₁。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedCoLipFamily_antitone" }
      ],
      "representation": "对应引理 2.3 第一部分：固定算子 ϕ 与满足 U.Nonempty、U ⊆ V、V ⊆ dom ϕ 的子集，证明 RestrictedCoLipFamily d ϕ V ⊆ RestrictedCoLipFamily d ϕ U（即 𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U）。",
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.globalCoLip_entry_eq_zero_of_collapse" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedCoLip_entry_eq_zero_of_collapse" }
      ],
      "representation": "对应“co-Lip 条目为零的充分条件”注：若存在 x, y ∈ dom ϕ 使 d j (ϕ.func x) (ϕ.func y) = 0 且 0 < d i x y，则任一全域 co-Lip 矩阵 K ∈ RestrictedCoLipFamily d ϕ (dom ϕ) 满足 matrixEntry K i j = 0；同时给出任意受限域 U 上的更一般形式 restrictedCoLip_entry_eq_zero_of_collapse。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.restrictedCoLipFamily_comp" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.operator_image_nonempty" }
      ],
      "representation": "对应命题 2.4：对复合算子 ϕ₂ * ϕ₁、起始子集 U₁ ⊆ dom (ϕ₂ * ϕ₁) 及精确中间像域 U₂ = operator_image ϕ₁ U₁（operator_image_nonempty 保持非空性），若 K₁ ∈ RestrictedCoLipFamily d ϕ₁ U₁ 且 K₂ ∈ RestrictedCoLipFamily d ϕ₂ (operator_image ϕ₁ U₁)（两者均含非空性与定义域条件），则 gaugeMatrixMul K₂ K₁ ∈ RestrictedCoLipFamily d (ϕ₂ * ϕ₁) U₁。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.idMatrix_mem_restrictedLipFamily_identity" },
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.idMatrix_mem_lipFamily_identity" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.zeroStep_chain_restrictedLipFamily" }
      ],
      "representation": "对应“零步复合的单位矩阵证书”注的 Lip 部分：对任意 U ⊆ dom operator_identity，证明 idMatrix ∈ RestrictedLipFamily d operator_identity U（因而对非空 U 亦成立，且全域有 idMatrix ∈ LipFamily d operator_identity）；zeroStep_chain_restrictedLipFamily 显式将零步链 c_0 = chainCompose ϕs 与空矩阵乘积 orderedMatrixProd Ls 对接至此结论。",
      "dependencies": ["CH02-D01", "CH02-D04", "CH02-D05"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.idMatrix_mem_restrictedCoLipFamily_identity" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.zeroStep_chain_restrictedCoLipFamily" }
      ],
      "representation": "对应“零步复合的单位矩阵证书”注的 co-Lip 部分：对任意非空 U ⊆ dom operator_identity，证明 idMatrix ∈ RestrictedCoLipFamily d operator_identity U；zeroStep_chain_restrictedCoLipFamily 显式将零步链 c_0 = chainCompose ϕs 与空矩阵乘积 orderedMatrixProd Ks 对接至此结论。",
      "dependencies": ["CH02-D02", "CH02-D04", "CH02-D05"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProdNonempty_entry_pos_iff" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProdNonempty_entry_pos_iff_middle" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProd_entry_pos_iff" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProdNonempty_entry_pos_iff_one" }
      ],
      "representation": "对应命题 2.6 (ii) 及 n = 1 退化说明：对任意正长度 n = m + 1 ≥ 1（涵盖 m = 0 即 n = 1）的扩展非负矩阵族 M 及任意 i, j : I，证明 0 < matrixEntry (orderedMatrixProdNonempty M) i j 当且仅当存在全正路径 p : IndexPath I (m + 1) i j 使 IsPositivePath M p（等价地存在中间指标序列 mid : Fin m → I 沿路径各单步条目严格正）；并给出 1 ≤ n 的 orderedMatrixProd 版本及 n = 1 退化引理。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P13"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.lipFamily_subset_restricted" }
      ],
      "representation": "对应引理 2.1 第二部分：对任意 U ⊆ dom ϕ，证明 LipFamily d ϕ ⊆ RestrictedLipFamily d ϕ U（即 ℒ(ϕ) ⊆ ℒ(ϕ)|_U）。",
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/LipBounds.lean", "name": "LCH02.globalCoLipFamily_subset_restricted" }
      ],
      "representation": "对应引理 2.3 第二部分：对任意非空子集 U ⊆ dom ϕ，证明 RestrictedCoLipFamily d ϕ (dom ϕ) ⊆ RestrictedCoLipFamily d ϕ U（即 𝒦(ϕ)|_{dom ϕ} ⊆ 𝒦(ϕ)|_U）。",
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.chain_restrictedLipFamily" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.chain_restrictedLipFamily_of_pos" }
      ],
      "representation": "对应推论 2.5 (i)：对任意正长度链 c_k = chainCompose ϕs（k = k' + 1 ≥ 1，以及 1 ≤ k 版本）、起始子集 U₁ ⊆ dom (chainCompose ϕs) 与逐步 Lip 证书族 ∀ m, Ls m ∈ RestrictedLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)，对命题 2.2 做有限归纳证得连乘矩阵 orderedMatrixProdNonempty Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U₁（即 L^(k) · ... · L^(1) ∈ ℒ(c_k)|_{U₁}）。",
      "dependencies": ["CH02-D01", "CH02-D04", "CH02-D05", "CH02-P04"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.chain_restrictedCoLipFamily" },
        { "file": "LCH02/FiniteComposition.lean", "name": "LCH02.chain_restrictedCoLipFamily_of_pos" }
      ],
      "representation": "对应推论 2.5 (ii)：对任意正长度链 c_k = chainCompose ϕs（k = k' + 1 ≥ 1，以及 1 ≤ k 版本）、起始子集 U₁ ⊆ dom (chainCompose ϕs) 与逐步 co-Lip 证书族 ∀ m, Ks m ∈ RestrictedCoLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)，对命题 2.4 做有限归纳证得连乘矩阵 orderedMatrixProdNonempty Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U₁（即 K^(k) · ... · K^(1) ∈ 𝒦(c_k)|_{U₁}）。",
      "dependencies": ["CH02-D02", "CH02-D04", "CH02-D05", "CH02-P08"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProdNonempty_entry_eq_zero_iff" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProdNonempty_entry_eq_zero_iff_middle" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProd_entry_eq_zero_iff" },
        { "file": "LCH02/IndexPath.lean", "name": "LCH02.orderedMatrixProdNonempty_entry_eq_zero_iff_one" }
      ],
      "representation": "对应命题 2.6 (i) 及 n = 1 退化说明：对任意正长度 n = m + 1 ≥ 1（涵盖 m = 0 即 n = 1）的扩展非负矩阵族 M 及任意 i, j : I，证明 matrixEntry (orderedMatrixProdNonempty M) i j = 0 当且仅当每条路径 p : IndexPath I (m + 1) i j 满足 HasZeroFactorPath M p（等价地对每个中间指标序列 mid : Fin m → I 存在至少一层 m 使单步矩阵条目为 0）；并给出 1 ≤ n 的 orderedMatrixProd 版本及 n = 1 退化引理。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    }
  ]
}
```