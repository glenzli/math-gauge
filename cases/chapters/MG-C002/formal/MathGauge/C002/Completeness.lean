import MathGauge.C002.SourceBridge
import Mathlib.Data.Matrix.Mul

namespace MathGauge.C002

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

noncomputable section

variable {X I : Type} {bot : X} [Fintype I]

abbrev Channel (I : Type) := I × I

def SingleInputRow (L : I → I → ENNReal) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0

def DiagonalMatrix (L : I → I → ENNReal) : Prop := ∀ i j, i ≠ j → L i j = 0

theorem diagonal_scalar_bound (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : I → I → ENNReal) (hL : IsLipMatrix d φ U L)
    (hdiag : DiagonalMatrix L) :
    ∀ j x, x ∈ U → ∀ y, y ∈ U → d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact lip_bound_of_single_input_row d φ U L j j hL (fun k hk => hdiag k j hk) x hx y hy

/-- The storage order `L i j` is input then output; the displayed matrix has output rows. -/
def displayed_matrix (L : I → I → ENNReal) : Matrix I I ENNReal := fun j i => L i j

theorem displayed_matrix_mul (L₂ L₁ : I → I → ENNReal) :
    displayed_matrix (matrix_mul L₂ L₁) = displayed_matrix L₂ * displayed_matrix L₁ := rfl

def restricted_lip_family (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :=
  {L | IsLipMatrix d φ U L}

def global_lip_family (d : I → X → X → ENNReal) (φ : Operator X bot) :=
  restricted_lip_family d φ (dom φ)

def restricted_colip_family (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :=
  {K | IsCoLipMatrix d φ U K}

def global_colip_family (d : I → X → X → ENNReal) (φ : Operator X bot) :=
  restricted_colip_family d φ (dom φ)

/-- Exact input domain of a new outer step, in the right-to-left list encoding. -/
theorem actual_image_domain_cons (φ : Operator X bot) (tail : List (Operator X bot))
    (U : Set X) :
    (OperatorChain (φ :: tail)).func '' U = φ.func '' ((OperatorChain tail).func '' U) := by
  simpa only [OperatorChain] using Set.image_comp φ.func (OperatorChain tail).func U

/-- Per-step lists contain only the actual local hypotheses, not the desired composite bound. -/
theorem list_lip_certificates_product {d : I → X → X → ENNReal}
    {φs : List (Operator X bot)} {U : Set X} {Ls : List (I → I → ENNReal)}
    (h : RightChainLipCertificateList d φs U Ls) :
    IsLipMatrix d (OperatorChain φs) U (matrix_list_mul Ls) := by
  apply right_chain_lip_matrix
  induction h with
  | nil U hU => exact RightChainLipBounded.nil U hU
  | cons φ tail U L Ls ht hφ ih =>
      exact RightChainLipBounded.cons φ tail U L (matrix_list_mul Ls) ih hφ

theorem list_colip_certificates_product {d : I → X → X → ENNReal}
    {φs : List (Operator X bot)} {U : Set X} {Ks : List (I → I → ENNReal)}
    (h : RightChainCoLipCertificateList d φs U Ks) :
    IsCoLipMatrix d (OperatorChain φs) U (matrix_list_mul Ks) := by
  apply right_chain_colip_matrix
  induction h with
  | nil U hU hne => exact RightChainCoLipBounded.nil U hU hne
  | cons φ tail U K Ks ht hφ ih =>
      exact RightChainCoLipBounded.cons φ tail U K (matrix_list_mul Ks) ih hφ

/-- All finite index paths; no positivity condition is built into a path. -/
inductive MatrixPath : List (I → I → ENNReal) → I → I → Type
  | nil (i : I) : MatrixPath [] i i
  | cons {Ms : List (I → I → ENNReal)} {i k : I}
      (M : I → I → ENNReal) (j : I) (tail : MatrixPath Ms i k) :
      MatrixPath (M :: Ms) i j

def MatrixPath.all_positive : {Ms : List (I → I → ENNReal)} → {i j : I} →
    MatrixPath Ms i j → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons (k := k) M j tail => 0 < M k j ∧ tail.all_positive

def MatrixPath.has_zero : {Ms : List (I → I → ENNReal)} → {i j : I} →
    MatrixPath Ms i j → Prop
  | _, _, _, .nil _ => False
  | _, _, _, .cons (k := k) M j tail => M k j = 0 ∨ tail.has_zero

def MatrixPath.vertices : {Ms : List (I → I → ENNReal)} → {i j : I} →
    MatrixPath Ms i j → List I
  | _, _, _, .nil i => [i]
  | _, _, _, .cons _ j tail => j :: tail.vertices

theorem MatrixPath.vertices_length {Ms : List (I → I → ENNReal)} {i j : I}
    (p : MatrixPath Ms i j) : p.vertices.length = Ms.length + 1 := by
  induction p with
  | nil => rfl
  | cons M j tail ih => simp [MatrixPath.vertices, ih]

theorem MatrixPath.not_positive_iff_has_zero {Ms : List (I → I → ENNReal)} {i j : I}
    (p : MatrixPath Ms i j) : ¬ p.all_positive ↔ p.has_zero := by
  induction p with
  | nil => simp [MatrixPath.all_positive, MatrixPath.has_zero]
  | cons M j tail ih =>
      simp only [MatrixPath.all_positive, MatrixPath.has_zero, not_and_or, ih,
        not_lt, nonpos_iff_eq_zero]

theorem positive_path_representation (Ms : List (I → I → ENNReal)) (i j : I) :
    ExistsPositivePath Ms i j ↔ ∃ p : MatrixPath Ms i j, p.all_positive := by
  constructor
  · intro h
    induction h with
    | nil_path i => exact ⟨.nil i, trivial⟩
    | cons_path M Ms i k j hM hp ih =>
        rcases ih with ⟨p, hpos⟩
        exact ⟨.cons M j p, hM, hpos⟩
  · rintro ⟨p, hp⟩
    induction p with
    | nil i => exact ExistsPositivePath.nil_path i
    | cons M j tail ih =>
        exact ExistsPositivePath.cons_path M _ _ _ j hp.1 (ih hp.2)

/-- OET anchor: h-e4154c34e95d3c23. Every index path has an actual zero edge. -/
theorem matrix_product_zero_iff_every_path_has_zero (Ms : List (I → I → ENNReal)) (i j : I) :
    matrix_list_mul Ms i j = 0 ↔ ∀ p : MatrixPath Ms i j, p.has_zero := by
  rw [list_matrix_mul_eq_zero_iff, positive_path_representation]
  simp only [not_exists]
  exact forall_congr' (fun p => p.not_positive_iff_has_zero)

/-- OET anchor: h-e4154c34e95d3c23. Existence quantifies all finite index paths. -/
theorem matrix_product_positive_iff_some_path_positive
    (Ms : List (I → I → ENNReal)) (i j : I) :
    0 < matrix_list_mul Ms i j ↔ ∃ p : MatrixPath Ms i j, p.all_positive := by
  exact (list_matrix_mul_pos_iff Ms i j).trans (positive_path_representation Ms i j)

theorem matrix_product_singleton (M : I → I → ENNReal) (i j : I) :
    matrix_list_mul [M] i j = M i j := by
  classical
  simp [matrix_list_mul, matrix_mul, matrix_id]

theorem singleton_paths_boundary (M : I → I → ENNReal) (i j : I) :
    ((∀ p : MatrixPath [M] i j, p.has_zero) ↔ M i j = 0) ∧
      ((∃ p : MatrixPath [M] i j, p.all_positive) ↔ 0 < M i j) := by
  rw [← matrix_product_zero_iff_every_path_has_zero,
    ← matrix_product_positive_iff_some_path_positive, matrix_product_singleton]
  exact ⟨Iff.rfl, Iff.rfl⟩

end
end MathGauge.C002
