import Candidate
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic

open scoped Topology
namespace MathGauge.F103
universe u v w z
variable {ι : Type u} {X : Type v} {Y : ι → Type w}

theorem empty_family [IsEmpty ι] (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    assembled t f = ⊤ := by simp [assembled]

theorem refined_targets (t u : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (htu : ∀ i, t i ≤ u i) : assembled t f ≤ assembled u f :=
  iInf_mono fun i => induced_mono (htu i)

theorem refined_identity (t u : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (htu : ∀ i, t i ≤ u i) : Continuous[assembled t f, assembled u f] id :=
  continuous_id_iff_le.mpr (refined_targets t u f htu)

theorem top_bool_not_le_bot : ¬ (⊤ : TopologicalSpace Bool) ≤ ⊥ := by
  intro h
  have ho : IsOpen[(⊤ : TopologicalSpace Bool)] ({true} : Set Bool) := h _ (by trivial)
  rcases (TopologicalSpace.isOpen_top_iff _).mp ho with he | hu
  · have : true ∈ (∅ : Set Bool) := he ▸ (by simp : true ∈ ({true} : Set Bool))
    exact this
  · have : false ∈ ({true} : Set Bool) := hu ▸ (by trivial : false ∈ (Set.univ : Set Bool))
    simpa using this

theorem targets_not_recoverable :
    assembled (fun _ : Unit => (⊥ : TopologicalSpace Bool)) (fun _ : Unit => fun _ : Unit => true) =
    assembled (fun _ : Unit => (⊤ : TopologicalSpace Bool)) (fun _ : Unit => fun _ : Unit => true) ∧
    (⊥ : TopologicalSpace Bool) ≠ ⊤ := by
  constructor
  · simp [assembled, induced_const]
  · intro h; exact top_bool_not_le_bot (le_of_eq h.symm)

theorem continuous_from_unit {T : Type*} (s : TopologicalSpace Unit) (t : TopologicalSpace T)
    (g : Unit → T) : Continuous[s,t] g := by
  letI := s
  letI := t
  have hg : g = fun _ => g () := by funext x; cases x; rfl
  rw [hg]
  exact continuous_const

theorem point_tests_insufficient :
    Realizes (fun _ : Unit => (⊤ : TopologicalSpace Unit)) (fun _ : Unit => fun _ : Bool => ()) ⊥ ∧
    (∀ (s : TopologicalSpace Unit) (g : Unit → Bool),
      Continuous[s,(⊥ : TopologicalSpace Bool)] g ↔
      ∀ i : Unit, Continuous[s,(⊤ : TopologicalSpace Unit)] ((fun _ : Bool => ()) ∘ g)) ∧
    (⊥ : TopologicalSpace Bool) ≠
      assembled (fun _ : Unit => (⊤ : TopologicalSpace Unit)) (fun _ : Unit => fun _ : Bool => ()) := by
  refine ⟨fun _ => continuous_bot, ?_, ?_⟩
  · intro s g
    exact ⟨fun _ _ => continuous_top, fun _ => continuous_from_unit s ⊥ g⟩
  · simp only [assembled, induced_top, iInf_const]
    intro h; exact top_bool_not_le_bot h.symm.le

theorem identity_test_sufficient (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (σ : TopologicalSpace X) (hσ : Realizes t f σ)
    (hid : Continuous[assembled t f, σ] id) : σ = assembled t f :=
  le_antisymm (candidate_coarsest t f σ hσ) (continuous_id_iff_le.mp hid)

end MathGauge.F103
