import FiniteCongruences

noncomputable section
open MathGauge.R101
namespace MathGauge.GR101
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem ambiguity_le_obstruction_space (A B C : Submodule R M) :
    ambiguity A B C ≤ obstruction_space A B C := by
  exact sup_le (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans le_sup_left))
    (le_inf le_sup_right le_sup_right)

def obstructionQuotientMap (A B C : Submodule R M) :
    obstruction_space A B C →ₗ[R] obstruction_image A B C :=
  ((ambiguity A B C).mkQ.comp (obstruction_space A B C).subtype).codRestrict
    (obstruction_image A B C) (fun h => ⟨h.val, h.property, rfl⟩)

theorem obstructionQuotientMap_surjective (A B C : Submodule R M) :
    Function.Surjective (obstructionQuotientMap A B C) := by
  rintro ⟨y, x, hx, he⟩
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem obstructionQuotientMap_kernel (A B C : Submodule R M) :
    (obstructionQuotientMap A B C).ker =
      (ambiguity A B C).comap (obstruction_space A B C).subtype := by
  ext x
  change obstructionQuotientMap A B C x = 0 ↔ x.val ∈ ambiguity A B C
  rw [Subtype.ext_iff]
  change (Submodule.Quotient.mk x.val : M ⧸ ambiguity A B C) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

/-- The literal quotient H/L is canonically the image of H in M/L. -/
def obstructionQuotientEquiv (A B C : Submodule R M) :
    (obstruction_space A B C ⧸ (ambiguity A B C).comap (obstruction_space A B C).subtype)
      ≃ₗ[R] obstruction_image A B C :=
  (Submodule.quotEquivOfEq _ _ (obstructionQuotientMap_kernel A B C).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (obstructionQuotientMap_surjective A B C))

theorem obstructionQuotientEquiv_on_class (A B C : Submodule R M)
    (h : obstruction_space A B C) :
    (obstructionQuotientEquiv A B C (Submodule.Quotient.mk h)).val =
      (ambiguity A B C).mkQ h.val := rfl

/- A genuine permutation of the same three records changes both the obstruction
   quotient and the first failed extension, while the final solution set is fixed. -/
def orderSpaces : Fin 3 → Submodule ℚ ℚ := ![⊥, ⊥, ⊤]
def orderRecords : Fin 3 → ℚ := ![0, 1, 0]
def swapLast : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def orderA (n : ℕ) : Submodule ℚ ℚ := orderSpaces (Fin.ofNat 3 n)
def orderX (n : ℕ) : ℚ := orderRecords (Fin.ofNat 3 n)
def swappedA (n : ℕ) : Submodule ℚ ℚ := orderSpaces (swapLast (Fin.ofNat 3 n))
def swappedX (n : ℕ) : ℚ := orderRecords (swapLast (Fin.ofNat 3 n))

theorem order_one_success : PrefixGlues orderA orderX 1 0 := by
  intro i hi
  have : i = 0 := by omega
  subst i
  norm_num [Fin.ofNat, Fin.reduceFinMk, orderA, orderX, orderSpaces, orderRecords]

theorem order_two_failure : ¬ ∃ w, PrefixGlues orderA orderX 2 w := by
  rintro ⟨w, hw⟩
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  norm_num [Fin.ofNat, Fin.reduceFinMk, orderA, orderX, orderSpaces, orderRecords] at h0 h1
  linarith

theorem swapped_two_success : PrefixGlues swappedA swappedX 2 0 := by
  intro i hi
  interval_cases i <;>
    norm_num [Fin.ofNat, Fin.reduceFinMk, swappedA, swappedX, orderSpaces, orderRecords, swapLast, Matrix.cons_val, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem swapped_three_failure : ¬ ∃ w, PrefixGlues swappedA swappedX 3 w := by
  rintro ⟨w, hw⟩
  have h0 := hw 0 (by omega)
  have h2 := hw 2 (by omega)
  norm_num [Fin.ofNat, Fin.reduceFinMk, swappedA, swappedX, orderSpaces, orderRecords, swapLast, Matrix.cons_val, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h0 h2
  linarith

theorem order_second_denominator : prefixKernel orderA 1 ⊔ orderA 1 = ⊥ := by
  rw [prefix_kernel_one]
  norm_num [Fin.ofNat, Fin.reduceFinMk, orderA, orderSpaces]

theorem swapped_second_denominator : prefixKernel swappedA 1 ⊔ swappedA 1 = ⊤ := by
  rw [prefix_kernel_one]
  norm_num [Fin.ofNat, Fin.reduceFinMk, swappedA, orderSpaces, swapLast, Matrix.cons_val, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem second_quotients_differ :
    (Submodule.Quotient.mk (1 : ℚ) : ℚ ⧸ (prefixKernel orderA 1 ⊔ orderA 1)) ≠ 0 ∧
    (∀ q : ℚ ⧸ (prefixKernel swappedA 1 ⊔ swappedA 1), q = 0) := by
  constructor
  · rw [ne_eq, Submodule.Quotient.mk_eq_zero, order_second_denominator]
    norm_num
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
        rw [Submodule.Quotient.mk_eq_zero, swapped_second_denominator]
        trivial

theorem final_records_invariant (w : ℚ) :
    (∀ i : Fin 3, w - orderRecords (swapLast i) ∈ orderSpaces (swapLast i)) ↔
      ∀ i : Fin 3, w - orderRecords i ∈ orderSpaces i :=
  permutation_invariant swapLast orderSpaces orderRecords w

/-- A genuine reindexing permutation can also change the prefix intersection. -/
theorem prefix_intersection_changes_under_permutation :
    let A : ℕ → Submodule ℚ ℚ := fun n => if n = 0 then ⊥ else ⊤
    prefixKernel A 1 ≠ prefixKernel (fun n => A (Equiv.swap 0 1 n)) 1 := by
  dsimp only
  rw [prefix_kernel_one, prefix_kernel_one]
  simpa [Equiv.swap_apply_def] using intermediate_kernel_can_change

end MathGauge.GR101
