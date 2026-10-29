import Candidate
import Boundary
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic

open scoped Topology
namespace MathGauge.F104
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}

theorem empty_family [IsEmpty ι] (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    assembled t f = ⊤ := by simp [assembled]

theorem induced_injective_discrete {V : Type*} (f : X → V) (hf : Function.Injective f) :
    TopologicalSpace.induced f (⊥ : TopologicalSpace V) = ⊥ := by
  apply le_antisymm
  · intro U hU
    exact ⟨f '' U, trivial, Set.preimage_image_eq U hf⟩
  · intro U hU; trivial

theorem singleton_discrete_initial {V : Type*} (f : X → V) (hf : Function.Injective f) :
    assembled (fun _ : Unit => (⊥ : TopologicalSpace V)) (fun _ : Unit => f) = ⊥ := by
  simpa [assembled] using induced_injective_discrete f hf

theorem subspace_initial (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) (E : Set X) :
    TopologicalSpace.induced (Subtype.val : E → X) (assembled t f) =
      assembled t (fun i => f i ∘ Subtype.val) := by
  simp only [assembled, induced_iInf, induced_compose]

theorem jointly_injective_t0 (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (hT : ∀ i, @T0Space (Y i) (t i))
    (hj : ∀ x y, (∀ i, f i x = f i y) → x = y) : @T0Space X (assembled t f) := by
  letI : TopologicalSpace X := assembled t f
  refine ⟨fun {x y} h => hj x y (fun i => ?_)⟩
  letI : TopologicalSpace (Y i) := t i
  letI : T0Space (Y i) := hT i
  exact (h.map (candidate_realizes t f i)).eq

theorem subspace_t0 (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (hT : ∀ i, @T0Space (Y i) (t i))
    (hj : ∀ x y, (∀ i, f i x = f i y) → x = y) (E : Set X) :
    @T0Space E (TopologicalSpace.induced (Subtype.val : E → X) (assembled t f)) := by
  rw [subspace_initial]
  exact jointly_injective_t0 t (fun i => f i ∘ Subtype.val) hT
    (fun x y h => Subtype.ext (hj x.val y.val h))

theorem empty_joint_subsingleton [IsEmpty ι] (f : ∀ i, X → Y i)
    (hj : ∀ x y, (∀ i, f i x = f i y) → x = y) : Subsingleton X :=
  ⟨fun x y => hj x y (fun i => isEmptyElim i)⟩

theorem top_bool_not_t0 : ¬ @T0Space Bool ⊤ := by
  intro ht
  letI : TopologicalSpace Bool := ⊤
  letI : T0Space Bool := ht
  have h : Inseparable false true := by
    rw [inseparable_iff_forall_isOpen]
    intro U hU
    rcases (TopologicalSpace.isOpen_top_iff _).mp hU with rfl | rfl <;> simp
  have he : false = true := h.eq
  cases he

theorem t0_targets_counterexample :
    @T0Space Unit ⊤ ∧
    assembled (fun _ : Unit => (⊤ : TopologicalSpace Unit)) (fun _ : Unit => fun _ : Bool => ()) = ⊤ ∧
    ¬ @T0Space Bool
      (assembled (fun _ : Unit => (⊤ : TopologicalSpace Unit)) (fun _ : Unit => fun _ : Bool => ())) ∧
    ¬ (∀ x y : Bool, (∀ i : Unit, (fun _ : Bool => ()) x = (fun _ : Bool => ()) y) → x = y) := by
  have he : assembled (fun _ : Unit => (⊤ : TopologicalSpace Unit))
      (fun _ : Unit => fun _ : Bool => ()) = ⊤ := by simp [assembled]
  refine ⟨?_,he,he ▸ top_bool_not_t0,?_⟩
  · letI : TopologicalSpace Unit := ⊤
    infer_instance
  · intro h
    have := h false true (fun _ => rfl)
    cases this

end MathGauge.F104
