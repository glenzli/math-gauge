import OperatorBounds.Chains
import Mathlib.Data.Fintype.BigOperators

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal

variable {X I : Type} {bot : X} {n : ℕ}

/-- A path with n + 1 edges has n unrestricted intermediate indices. -/
def pathVertex (i j : I) (p : Fin n → I) : Fin (n + 2) → I :=
  Fin.cons i (Fin.snoc p j)

@[simp] theorem pathVertex_start (i j : I) (p : Fin n → I) :
    pathVertex i j p 0 = i := by simp [pathVertex]

@[simp] theorem pathVertex_middle (i j : I) (p : Fin n → I) (m : Fin n) :
    pathVertex i j p m.castSucc.succ = p m := by simp [pathVertex]

@[simp] theorem pathVertex_end (i j : I) (p : Fin n → I) :
    pathVertex i j p (Fin.last (n + 1)) = j := by
  rw [← Fin.succ_last]
  simp [pathVertex]

def pathTupleEquiv (i j : I) :
    (Fin n → I) ≃ {q : Fin (n + 2) → I // q 0 = i ∧ q (Fin.last (n + 1)) = j} where
  toFun p := ⟨pathVertex i j p, pathVertex_start i j p, pathVertex_end i j p⟩
  invFun q m := q.val m.castSucc.succ
  left_inv p := funext (pathVertex_middle i j p)
  right_inv q := by
    apply Subtype.ext
    funext m
    change pathVertex i j (fun k : Fin n => q.val k.castSucc.succ) m = q.val m
    cases m using Fin.cases with
    | zero => exact (pathVertex_start _ _ _).trans q.property.1.symm
    | succ m =>
      cases m using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, pathVertex_end]
        exact q.property.2.symm
      | cast k => exact pathVertex_middle _ _ _ k

def pathEdge (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I)
    (m : Fin (n + 1)) : ℝ≥0∞ :=
  M m (pathVertex i j p m.castSucc) (pathVertex i j p m.succ)

noncomputable def pathWeight (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) :
    ℝ≥0∞ :=
  ∏ m, pathEdge M i j p m

def PathHasZero (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) : Prop :=
  ∃ m, pathEdge M i j p m = 0

def PathPositive (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) : Prop :=
  ∀ m, 0 < pathEdge M i j p m

theorem empty_path_unique (p : Fin 0 → I) : p = (fun m => Fin.elim0 m) :=
  funext fun m => Fin.elim0 m

@[simp] theorem pathWeight_singleton (M : Fin 1 → BoundMatrix I) (i j : I)
    (p : Fin 0 → I) : pathWeight M i j p = M 0 i j := by
  rw [pathWeight, Fin.prod_univ_one]
  change M 0 (pathVertex i j p 0) (pathVertex i j p (Fin.last 1)) = _
  rw [pathVertex_start, pathVertex_end]

private theorem pathVertex_succ_cons (i j k : I) (p : Fin n → I) (m : Fin (n + 2)) :
    pathVertex i j (Fin.cons k p) m.succ = pathVertex k j p m := by
  simp [pathVertex, ← Fin.cons_snoc_eq_snoc_cons]

private theorem pathEdge_cons_first (M : Fin (n + 2) → BoundMatrix I)
    (i j k : I) (p : Fin n → I) : pathEdge M i j (Fin.cons k p) 0 = M 0 i k := by
  change M 0 (pathVertex i j (Fin.cons k p) 0)
    (pathVertex i j (Fin.cons k p) (0 : Fin (n + 1)).castSucc.succ) = _
  rw [pathVertex_start, pathVertex_middle, Fin.cons_zero]

private theorem pathWeight_cons (M : Fin (n + 2) → BoundMatrix I) (i j k : I)
    (p : Fin n → I) :
    pathWeight M i j (Fin.cons k p) =
      M 0 i k * pathWeight (fun m : Fin (n + 1) => M m.succ) k j p := by
  unfold pathWeight
  rw [Fin.prod_univ_succ, pathEdge_cons_first]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  unfold pathEdge
  rw [Fin.castSucc_succ, pathVertex_succ_cons, pathVertex_succ_cons]

theorem pathWeight_eq_zero_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) :
    pathWeight M i j p = 0 ↔ PathHasZero M i j p := by
  simp [pathWeight, PathHasZero, Finset.prod_eq_zero_iff]

theorem pathWeight_pos_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) :
    0 < pathWeight M i j p ↔ PathPositive M i j p := by
  rw [pos_iff_ne_zero, Ne, pathWeight_eq_zero_iff]
  simp only [PathHasZero, PathPositive, not_exists, pos_iff_ne_zero]

theorem singleton_path_criteria (M : Fin 1 → BoundMatrix I) (i j : I) (p : Fin 0 → I) :
    (PathHasZero M i j p ↔ M 0 i j = 0) ∧ (PathPositive M i j p ↔ 0 < M 0 i j) := by
  rw [← pathWeight_eq_zero_iff, ← pathWeight_pos_iff, pathWeight_singleton]
  exact ⟨Iff.rfl, Iff.rfl⟩

variable [Fintype I]

theorem matrixProduct_eq_path_sum (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    matrixProduct (List.ofFn M) i j = ∑ p : Fin n → I, pathWeight M i j p := by
  classical
  induction n generalizing i j with
  | zero =>
    letI : Unique (Fin 0 → I) := ⟨⟨fun m => Fin.elim0 m⟩, empty_path_unique⟩
    simp [List.ofFn_succ]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => I)
    calc
      _ = ∑ k : I, matrixProduct (List.ofFn fun m : Fin (n + 1) => M m.succ) k j * M 0 i k := by
        rw [List.ofFn_succ]
        rfl
      _ = ∑ k : I, ∑ p : Fin n → I, pathWeight M i j (Fin.cons k p) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [ih, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        rw [pathWeight_cons, mul_comm]
      _ = _ := by
        rw [← Fintype.sum_prod_type']
        exact e.sum_comp (fun p => pathWeight M i j p)

theorem matrixProduct_zero_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    matrixProduct (List.ofFn M) i j = 0 ↔ ∀ p, PathHasZero M i j p := by
  rw [matrixProduct_eq_path_sum, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le _)]
  simp [pathWeight_eq_zero_iff]

theorem matrixProduct_pos_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    0 < matrixProduct (List.ofFn M) i j ↔ ∃ p, PathPositive M i j p := by
  rw [matrixProduct_eq_path_sum, Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
  simp [pathWeight_pos_iff]

theorem chain_lip_zero_iff {d : I → X → X → ℝ≥0∞} {U : Set X}
    (ops : Fin (n + 1) → Operator X bot) (L K : Fin (n + 1) → BoundMatrix I)
    (_hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (_hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L)
    (_hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K)
    (i j : I) :
    matrixProduct (List.ofFn L) i j = 0 ↔ ∀ p, PathHasZero L i j p :=
  matrixProduct_zero_iff L i j

theorem chain_coLip_pos_iff {d : I → X → X → ℝ≥0∞} {U : Set X}
    (ops : Fin (n + 1) → Operator X bot) (L K : Fin (n + 1) → BoundMatrix I)
    (_hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (_hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L)
    (_hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K)
    (i j : I) :
    0 < matrixProduct (List.ofFn K) i j ↔ ∃ p, PathPositive K i j p :=
  matrixProduct_pos_iff K i j

end HCH02
