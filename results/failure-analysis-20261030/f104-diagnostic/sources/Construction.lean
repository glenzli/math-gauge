import Core

open scoped Topology

namespace MathGauge.F104

universe u v w

variable {ι : Type u} {X : Type v} {Y : ι → Type w}

/-- The construction in the submitted file always gives the discrete topology. -/
theorem submitted_sInf_eq_bot
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    sInf {s : TopologicalSpace X | Realizes t f s} = ⊥ := by
  have hb : Realizes t f (⊥ : TopologicalSpace X) :=
    fun _ => continuous_bot
  apply le_antisymm
  · exact sInf_le hb
  · exact TopologicalSpace.instCompleteLattice.bot_le _

/--
A set is open in `assembled t f` exactly when it is open in every topology
on `X` for which all the maps `f i` are continuous.
-/
@[reducible] def assembled
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    TopologicalSpace X where
  IsOpen := fun U =>
    ∀ s : TopologicalSpace X, Realizes t f s → s.IsOpen U
  isOpen_univ := by
    intro s _
    exact s.isOpen_univ
  isOpen_inter := by
    intro U V hU hV s hs
    exact s.isOpen_inter U V (hU s hs) (hV s hs)
  isOpen_sUnion := by
    intro S hS s hs
    exact s.isOpen_sUnion S (fun U hU => hS U hU s hs)

/-- Every map in the family is continuous for the constructed topology. -/
theorem candidate_realizes
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (assembled t f) := by
  intro i
  letI : TopologicalSpace X := assembled t f
  letI : TopologicalSpace (Y i) := t i
  apply continuous_def.mpr
  intro U hU
  change ∀ s : TopologicalSpace X, Realizes t f s →
    s.IsOpen (f i ⁻¹' U)
  intro s hs
  letI : TopologicalSpace X := s
  exact (continuous_def.mp (hs i)) U hU

/--
Every topology making the family continuous is finer than `assembled t f`.
Mathlib orders finer topologies below coarser ones.
-/
theorem construction_bound
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) (hs : Realizes t f s) :
    s ≤ assembled t f := by
  change ∀ U : Set X, (assembled t f).IsOpen U → s.IsOpen U
  intro U hU
  exact hU s hs

/-- Any other topology satisfying the same coarseness property is equal to it. -/
theorem construction_unique
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X)
    (hs : Realizes t f s)
    (hcoarse : ∀ r : TopologicalSpace X, Realizes t f r → r ≤ s) :
    s = assembled t f := by
  exact le_antisymm
    (construction_bound t f s hs)
    (hcoarse (assembled t f) (candidate_realizes t f))

/-- Existence and uniqueness of the coarsest topology for the family. -/
theorem existsUnique_coarsest
    (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    ∃! s : TopologicalSpace X,
      Realizes t f s ∧
        ∀ r : TopologicalSpace X, Realizes t f r → r ≤ s := by
  refine ⟨assembled t f, ?_, ?_⟩
  · refine ⟨candidate_realizes t f, ?_⟩
    intro r hr
    exact construction_bound t f r hr
  · intro s hs
    exact construction_unique t f s hs.1 hs.2

end MathGauge.F104
