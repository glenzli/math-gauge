import ProgressiveLinearSystems

noncomputable section
open Set Function Module
namespace MathGauge.AffineDimensions
open MathGauge.LinearSystems MathGauge.ProgressiveLinearSystems
universe u v w
variable {k : Type u} [Field k] {I : Type v} {J : Type w}

/-- A literal subspace of the original full assignment space. It consists of
the coordinate vectors of all algebraic functionals annihilating W. -/
def direction (W : Submodule k (I →₀ k)) : Submodule k (I → k) :=
  W.dualAnnihilator.map (Finsupp.llift k k k I).symm.toLinearMap

/-- A genuine linear equivalence, not just the previous set parametrization. -/
def directionEquiv (W : Submodule k (I →₀ k)) :
    (((I →₀ k) ⧸ W) →ₗ[k] k) ≃ₗ[k] direction W :=
  W.dualQuotEquivDualAnnihilator.trans
    ((Finsupp.llift k k k I).symm.submoduleMap W.dualAnnihilator)

theorem direction_mem (W : Submodule k (I →₀ k)) (x : I → k) :
    x ∈ direction W ↔ ∀ v ∈ W, evaluate x v = 0 := by
  rw [direction,Submodule.mem_map]
  constructor
  · rintro ⟨f,hf,rfl⟩
    have h := (W.mem_dualAnnihilator f).1 hf
    change ∀ v ∈ W, ((Finsupp.llift k k k I) ((Finsupp.llift k k k I).symm f)) v = 0
    rw [LinearEquiv.apply_symm_apply]
    exact h
  · intro hx
    exact ⟨evaluate x,(W.mem_dualAnnihilator _).2 hx,
      (Finsupp.llift k k k I).symm_apply_apply x⟩

theorem direction_sup (W U : Submodule k (I →₀ k)) :
    direction (W ⊔ U) = direction W ⊓ direction U := by
  ext x
  simp only [Submodule.mem_inf,direction_mem]
  change W ⊔ U ≤ LinearMap.ker (evaluate x) ↔
    W ≤ LinearMap.ker (evaluate x) ∧ U ≤ LinearMap.ker (evaluate x)
  exact sup_le_iff

theorem direction_rows (r : J → I →₀ k) (x : I → k) :
    x ∈ direction (LinearMap.range (rowMap r)) ↔ ∀ j, evaluate x (r j) = 0 := by
  rw [direction_mem]
  constructor
  · intro h j
    apply h (r j)
    exact ⟨Finsupp.single j 1,by simp [rowMap]⟩
  · intro h v hv
    obtain ⟨a,rfl⟩ := hv
    rw [rowMap,Finsupp.apply_linearCombination]
    change a.sum (fun j c => c • evaluate x (r j)) = 0
    simp [h]

theorem direction_coordinates (A : Set I) (x : I → k) :
    x ∈ direction (LinearMap.range (observationMap A)) ↔ ∀ i : A, x i = 0 := by
  rw [direction_mem]
  constructor
  · intro h i
    have hi := h (Finsupp.single i.val 1)
      ⟨Finsupp.single i 1,by simp [observationMap]⟩
    simpa using hi
  · intro h v hv
    obtain ⟨a,rfl⟩ := hv
    rw [observationMap,Finsupp.apply_linearCombination]
    change a.sum (fun i c => c • evaluate x (Finsupp.single i.val 1)) = 0
    simp [h]

theorem evaluate_difference (x y : I → k) (v : I →₀ k) :
    evaluate (x-y) v = evaluate x v-evaluate y v := by
  simp [evaluate]

/-- Exact equality with a translate in the original assignment space. -/
theorem solution_is_translate (r : J → I →₀ k) (d : J → k)
    (x0 : coordinateSolutions r d) (x : I → k) :
    (∀ j, evaluate x (r j)=d j) ↔
      x-x0.val ∈ direction (LinearMap.range (rowMap r)) := by
  rw [direction_rows]
  simp only [evaluate_difference,x0.property,sub_eq_zero]

/-- Each original coordinate fiber is a translate of the actual homogeneous
subspace with both the row equations and the observed coordinates zero. -/
theorem fiber_is_translate (r : J → I →₀ k) (d : J → k) (A : Set I)
    (y : A → k) (x0 : coordinateFiber r d A y) (x : I → k) :
    ((∀ j, evaluate x (r j)=d j) ∧ ∀ i : A, x i=y i) ↔
      x-x0.val.val ∈ direction
        (LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A)) := by
  rw [direction_sup,Submodule.mem_inf,direction_rows,direction_coordinates]
  simp only [evaluate_difference,x0.val.property,sub_eq_zero,Pi.sub_apply,x0.property]

theorem direction_dimension [Fintype I] (W : Submodule k (I →₀ k)) :
    finrank k (direction W) = Fintype.card I - finrank k W := by
  rw [← (directionEquiv W).finrank_eq]
  rw [show finrank k (_ →ₗ[k] k) = _ from Subspace.dual_finrank_eq (K := k),
    Submodule.finrank_quotient,finrank_finsupp_self]

/-- These dimensions belong to the proven translation spaces of the actual
solution and fiber sets. No dimension is transferred by a bare bijection. -/
theorem actual_solution_and_fiber_dimensions [Fintype I]
    (r : J → I →₀ k) (A : Set I) :
    finrank k (direction (LinearMap.range (rowMap r))) =
      Fintype.card I - finrank k (LinearMap.range (rowMap r)) ∧
    finrank k (direction (LinearMap.range (rowMap r) ⊔
      LinearMap.range (observationMap A))) = Fintype.card I -
      finrank k ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A)) :=
  ⟨direction_dimension _,direction_dimension _⟩

end MathGauge.AffineDimensions
