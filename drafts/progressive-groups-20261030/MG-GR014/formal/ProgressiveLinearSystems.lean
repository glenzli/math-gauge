import CoordinateFibers
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section
open Set Function Module
namespace MathGauge.ProgressiveLinearSystems
open MathGauge.LinearSystems
universe u v w
variable {k : Type u} [Field k] {I : Type v} {J : Type w}
variable (r : J → I →₀ k) (d : J → k) (A : Set I)

/-- For finite I the finitely supported row model is exactly all coefficient
functions appearing in S1; this conversion imposes no support restriction. -/
def finiteRow [Fintype I] (a : I → k) : I →₀ k := Finsupp.equivFunOnFinite.symm a

theorem finiteRow_pairing [Fintype I] (a x : I → k) :
    evaluate x (finiteRow a) = ∑ i, a i * x i := by
  classical
  change (finiteRow a).sum (fun i c => c • x i) = _
  rw [Finsupp.sum_fintype]
  · simp [finiteRow, smul_eq_mul]
  · intro i; simp

theorem row_span : LinearMap.range (rowMap r) = Submodule.span k (range r) :=
  Finsupp.range_linearCombination k

/-- Dimension of the actual parameter space already identified with every solution. -/
theorem solution_parameter_dimension [Fintype I] :
    finrank k (((I →₀ k) ⧸ LinearMap.range (rowMap r)) →ₗ[k] k) =
      Fintype.card I - finrank k (LinearMap.range (rowMap r)) := by
  rw [show finrank k (_ →ₗ[k] k) = _ from Subspace.dual_finrank_eq (K := k), Submodule.finrank_quotient,
    finrank_finsupp_self]

theorem fiber_parameter_dimension [Fintype I] :
    finrank k (((I →₀ k) ⧸
      (LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A))) →ₗ[k] k) =
      Fintype.card I - finrank k
        ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A)) := by
  rw [show finrank k (_ →ₗ[k] k) = _ from Subspace.dual_finrank_eq (K := k), Submodule.finrank_quotient,
    finrank_finsupp_self]

/-- Exact counts of all assignments and each inhabited coordinate fibre. -/
theorem solution_count [Fintype I] [Finite k] (x0 : coordinateSolutions r d) :
    Nat.card (coordinateSolutions r d) = Nat.card k ^
      (Fintype.card I - finrank k (LinearMap.range (rowMap r))) := by
  rw [← Nat.card_congr (coordinateParameters r d x0), Module.natCard_eq_pow_finrank (K := k),
    solution_parameter_dimension]

theorem fiber_count [Fintype I] [Finite k] (y : A → k) (x0 : coordinateFiber r d A y) :
    Nat.card (coordinateFiber r d A y) = Nat.card k ^
      (Fintype.card I - finrank k
        ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A))) := by
  rw [← Nat.card_congr (coordinateFiberParameters r d A y x0),
    Module.natCard_eq_pow_finrank (K := k), fiber_parameter_dimension]

/-- The original coordinate restriction, with no replacement of its image. -/
def restrict (x : coordinateSolutions r d) : A → k := fun i => x.val i

def imageFiberPoint (y : range (restrict r d A)) : coordinateFiber r d A y.val :=
  ⟨y.property.choose, fun i => congrFun y.property.choose_spec i⟩

/-- Actual total space is a product of its image and the same quotient dual
parametrizing every nonempty fibre. Choices of base points need not be canonical. -/
def solutionImageProduct : coordinateSolutions r d ≃
    range (restrict r d A) ×
      (((I →₀ k) ⧸ (LinearMap.range (rowMap r) ⊔
        LinearMap.range (observationMap A))) →ₗ[k] k) := by
  let e := Equiv.sigmaSubtypeFiberEquiv (restrict r d A)
    (fun y => y ∈ range (restrict r d A)) (fun x => ⟨x,rfl⟩)
  refine e.symm.trans (Equiv.sigmaEquivProdOfEquiv (fun y => ?_))
  let h : {x : coordinateSolutions r d // restrict r d A x = y.val} ≃
      coordinateFiber r d A y.val :=
    Equiv.subtypeEquivRight (fun x => ⟨fun hh i => congrFun hh i, fun hh => funext hh⟩)
  exact h.trans (coordinateFiberParameters r d A y.val (imageFiberPoint r d A y)).symm

theorem observation_injective : Injective (observationMap (k := k) A) := by
  exact ((Finsupp.linearIndependent_single_one k I).comp (Subtype.val : A → I)
    Subtype.val_injective)

theorem observation_dimension [Fintype I] :
    finrank k (LinearMap.range (observationMap (k := k) A)) = Nat.card A := by
  classical
  letI := Fintype.ofFinite A
  rw [LinearMap.finrank_range_of_inj (observation_injective A), finrank_finsupp_self,
    Fintype.card_eq_nat_card]

theorem image_dimension_identity [Fintype I] :
    finrank k ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A)) -
        finrank k (LinearMap.range (rowMap r)) =
      Nat.card A - finrank k
        ↥(LinearMap.range (rowMap r) ⊓ LinearMap.range (observationMap A)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (rowMap r)) (LinearMap.range (observationMap A))
  rw [observation_dimension] at h
  omega

theorem image_count [Fintype I] [Finite k] (x0 : coordinateSolutions r d) :
    Nat.card (range (restrict r d A)) = Nat.card k ^
      (finrank k ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A)) -
        finrank k (LinearMap.range (rowMap r))) := by
  have h := Nat.card_congr (solutionImageProduct r d A)
  rw [Nat.card_prod, solution_count r d x0,
    Module.natCard_eq_pow_finrank (K := k)
      (V := (((I →₀ k) ⧸ (LinearMap.range (rowMap r) ⊔
        LinearMap.range (observationMap A))) →ₗ[k] k)),
    fiber_parameter_dimension] at h
  have hm := Submodule.finrank_mono
    (show LinearMap.range (rowMap r) ≤
      LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A) from le_sup_left)
  have hn := Submodule.finrank_le
    (LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A))
  rw [finrank_finsupp_self] at hn
  have he : Fintype.card I - finrank k (LinearMap.range (rowMap r)) =
      (finrank k ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A)) -
        finrank k (LinearMap.range (rowMap r))) +
      (Fintype.card I - finrank k
        ↥(LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap A))) := by omega
  rw [he, pow_add] at h
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos : 0 < Nat.card k) _) h.symm)

theorem image_count_intersection [Fintype I] [Finite k] (x0 : coordinateSolutions r d) :
    Nat.card (range (restrict r d A)) = Nat.card k ^
      (Nat.card A - finrank k
        ↥(LinearMap.range (rowMap r) ⊓ LinearMap.range (observationMap A))) := by
  rw [image_count r d A x0, image_dimension_identity]

theorem image_iff (y : A → k) : y ∈ range (restrict r d A) ↔
    ∀ l : J →₀ k, ∀ z : A →₀ k,
      rowMap r l = observationMap A z → constantMap d l = evaluate y z := by
  rw [← coordinate_image]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨⟨x,fun i => congrFun hx i⟩⟩
  · rintro ⟨⟨x,hx⟩⟩
    exact ⟨x,funext hx⟩

/-- Finite support is imposed on every row, so evaluating it is a finite sum
of continuous coordinate functions, even when I and the discrete field are infinite. -/
theorem continuous_evaluate [TopologicalSpace k] [DiscreteTopology k]
    (z : I →₀ k) : Continuous (fun x : I → k => evaluate x z) := by
  classical
  change Continuous (fun x : I → k => z.sum (fun i a => a • x i))
  exact continuous_finset_sum _ (fun i _ => continuous_const.smul (continuous_apply i))

theorem coordinate_image_closed [TopologicalSpace k] [DiscreteTopology k] :
    IsClosed (range (restrict r d A)) := by
  have he : range (restrict r d A) =
      ⋂ (l : J →₀ k) (z : A →₀ k) (_h : rowMap r l = observationMap A z),
        {y | constantMap d l = evaluate y z} := by
    ext y
    simp only [mem_iInter, mem_setOf_eq, image_iff]
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_iInter (fun z => isClosed_iInter (fun _ =>
    isClosed_eq continuous_const (continuous_evaluate z))))

theorem solution_set_closed [TopologicalSpace k] [DiscreteTopology k] :
    IsClosed {x : I → k | ∀ j, evaluate x (r j) = d j} := by
  have he : {x : I → k | ∀ j, evaluate x (r j) = d j} =
      ⋂ j, {x : I → k | evaluate x (r j) = d j} := by ext; simp
  rw [he]
  exact isClosed_iInter (fun j => isClosed_eq (continuous_evaluate (r j)) continuous_const)

theorem solution_set_compact [TopologicalSpace k] [DiscreteTopology k] [Finite k] :
    IsCompact {x : I → k | ∀ j, evaluate x (r j) = d j} :=
  (solution_set_closed r d).isCompact

instance solution_topology [TopologicalSpace k] : TopologicalSpace (coordinateSolutions r d) :=
  inferInstanceAs (TopologicalSpace {x : I → k // ∀ j, evaluate x (r j) = d j})

theorem solution_totally_disconnected [TopologicalSpace k] [DiscreteTopology k] :
    TotallyDisconnectedSpace (coordinateSolutions r d) := by
  exact @Subtype.totallyDisconnectedSpace (I → k) (fun x => ∀ j, evaluate x (r j) = d j) inferInstance inferInstance

/-- Arbitrary finite simultaneous row and observation requirements suffice.
This constructs the global extension by applying the proved algebraic extension
to the actual augmented row system. In particular it is valid over finite fields. -/
theorem finite_joint_iff (y : A → k) : y ∈ range (restrict r d A) ↔
    ∀ (F : Finset J) (G : Finset A), ∃ x : I → k,
      (∀ j ∈ F, evaluate x (r j) = d j) ∧ (∀ i ∈ G, x i = y i) := by
  classical
  constructor
  · rintro ⟨x,hx⟩ F G
    exact ⟨x.val, fun j _ => x.property j, fun i _ => congrFun hx i⟩
  · intro h
    let rr : J ⊕ A → I →₀ k := Sum.elim r (fun i => Finsupp.single i.val 1)
    let dd : J ⊕ A → k := Sum.elim d y
    have hs : finiteSolvable rr dd := by
      intro F
      obtain ⟨x,hx,hg⟩ := h (F.toLeft) (F.toRight)
      refine ⟨x, ?_⟩
      intro j hj
      cases j with
      | inl j => exact hx j (by simpa using hj)
      | inr i => simpa [rr,dd] using hg i (by simpa using hj)
    obtain ⟨x⟩ := global_solution rr dd hs
    refine ⟨⟨x.val,fun j => x.property (Sum.inl j)⟩, ?_⟩
    funext i
    simpa [restrict,rr,dd] using x.property (Sum.inr i)

/-- Counterexample: every finite family of equations x_i=1 has a finitely
supported assignment, but there is no such assignment satisfying all equations. -/
theorem finite_support_counterexample (k : Type u) [Field k] :
    (∀ F : Finset ℕ, ∃ x : ℕ →₀ k, ∀ i ∈ F, x i = 1) ∧
      ¬ ∃ x : ℕ →₀ k, ∀ i, x i = 1 := by
  classical
  constructor
  · intro F
    refine ⟨F.sum (fun i => Finsupp.single i 1), ?_⟩
    intro i hi
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hi]
  · rintro ⟨x,hx⟩
    obtain ⟨i,hi⟩ := Infinite.exists_notMem_finset x.support
    have hz : x i = 0 := Finsupp.notMem_support_iff.mp hi
    exact one_ne_zero ((hx i).symm.trans hz)

end MathGauge.ProgressiveLinearSystems
