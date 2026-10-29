import FiniteObservations
import Mathlib.Topology.Compactification.StoneCech

noncomputable section
open Set Filter Function Topology
namespace MathGauge.ProgressiveObservations
open MathGauge.FiniteObservations
attribute [local instance] Classical.propDecidable
universe u v

/-- The finite classification includes uniqueness and permits the bottom set to live
in an arbitrary universe: only the finite skeleton is used in `Record`. -/
theorem finite_point_unique (X : Type u) [Finite X] (r : Record X) :
    ∃! x, Record.point x = r := by
  obtain ⟨x,hx⟩ := (point_surjective_iff_finite X).2 inferInstance r
  exact ⟨x,hx,fun y hy => point_injective X (hy.trans hx.symm)⟩

theorem empty_no_record (X : Type u) [IsEmpty X] : IsEmpty (Record X) := by
  refine ⟨fun r => ?_⟩
  exact isEmptyElim (r.choose Empty isEmptyElim)

/-- A natural m-ary operation on all finite sets. Naturality is for every map,
not only bijections. The zero-ary case remains part of the same definition. -/
structure FiniteOperation (m : ℕ) where
  apply : (A : Type) → [Fintype A] → (Fin m → A) → A
  natural : ∀ (A B : Type) [Fintype A] [Fintype B] (x : Fin m → A) (g : A → B),
    g (apply A x) = apply B (g ∘ x)

def coordinateOperation {m : ℕ} (j : Fin m) : FiniteOperation m where
  apply _ _ x := x j
  natural _ _ _ _ _ _ := rfl

theorem finite_operation_classification {m : ℕ} (θ : FiniteOperation m) :
    ∃! j : Fin m, ∀ (A : Type) [Fintype A] (x : Fin m → A), θ.apply A x = x j := by
  let j := θ.apply (Fin m) id
  refine ⟨j, ?_, ?_⟩
  · intro A _ x
    exact (θ.natural (Fin m) A id x).symm
  · intro k hk
    simpa [j] using (hk (Fin m) id).symm

theorem no_nullary_operation : IsEmpty (FiniteOperation 0) :=
  ⟨fun θ => Fin.elim0 (θ.apply (Fin 0) id)⟩

/-- Literal majority of three, implemented without choosing a distinguished point
of the target. It will be natural for every target containing at most two values. -/
def majority {A : Type u} (f : Fin 3 → A) : A :=
  if f 0 = f 1 then f 0 else f 2

theorem three_values_repeat {A : Type u} [Fintype A] (hA : Fintype.card A ≤ 2)
    (f : Fin 3 → A) : f 0 = f 1 ∨ f 0 = f 2 ∨ f 1 = f 2 := by
  classical
  by_contra hn
  push Not at hn
  have hi : Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hc := Fintype.card_le_of_injective f hi
  simp only [Fintype.card_fin] at hc
  omega

theorem majority_natural {A : Type u} {B : Type v} [Fintype A]
    (hA : Fintype.card A ≤ 2) (f : Fin 3 → A) (g : A → B) :
    g (majority f) = majority (g ∘ f) := by
  classical
  obtain h | h | h := three_values_repeat hA f
  all_goals
    simp only [majority, comp_apply]
    split_ifs <;> simp_all

structure BinaryRecord (X : Type u) where
  choose : (A : Type) → [Fintype A] → Fintype.card A ≤ 2 → (X → A) → A
  natural : ∀ (A B : Type) [Fintype A] [Fintype B]
    (hA : Fintype.card A ≤ 2) (hB : Fintype.card B ≤ 2) (f : X → A) (g : A → B),
    g (choose A hA f) = choose B hB (g ∘ f)

def majorityRecord : BinaryRecord (Fin 3) where
  choose _ _ _ f := majority f
  natural _ _ _ _ hA _ f g := majority_natural hA f g

theorem majority_not_point (x : Fin 3) :
    ∃ f : Fin 3 → Bool, majorityRecord.choose Bool (by decide) f ≠ f x := by
  refine ⟨fun y => decide (y = x), ?_⟩
  fin_cases x <;> simp [majorityRecord, majority]

/-- Stone evaluation is continuous for an arbitrary finite discrete target. -/
theorem selected_eq_extend {X : Type u} (A : Type) [Fintype A]
    [TopologicalSpace A] [DiscreteTopology A] (f : X → A) (U : Ultrafilter X) :
    selected U A f = Ultrafilter.extend f U := by
  symm
  rw [ultrafilter_extend_eq_iff, selected_spec, Ultrafilter.coe_pure]
  exact pure_le_nhds _

theorem selected_continuous {X : Type u} (A : Type) [Fintype A]
    [TopologicalSpace A] [DiscreteTopology A] (f : X → A) :
    Continuous (fun U : Ultrafilter X => selected U A f) := by
  simpa only [selected_eq_extend] using continuous_ultrafilter_extend f

/-- Every continuous finite observation comes from a unique actual map on X;
the statement includes empty X and the empty target. -/
theorem continuous_observation_unique {X : Type u} (A : Type) [Fintype A]
    [TopologicalSpace A] [DiscreteTopology A] (h : Ultrafilter X → A) (hh : Continuous h) :
    ∃! f : X → A, ∀ U, h U = selected U A f := by
  refine ⟨h ∘ pure, ?_, ?_⟩
  · have he : h = Ultrafilter.extend (h ∘ pure) := by
      apply Continuous.ext_on denseRange_pure hh (continuous_ultrafilter_extend _)
      rintro _ ⟨x,rfl⟩
      simp
    intro U
    exact (congrFun he U).trans (selected_eq_extend A _ U).symm
  · intro f hf
    funext x
    have he := hf (pure x)
    simpa only [selected_eq_extend, ultrafilter_extend_pure, comp_apply] using he.symm

/-- The clopen sets are exactly individual Stone basic sets, not merely unions. -/
theorem clopen_is_basic {X : Type u} (B : Set (Ultrafilter X)) (hB : IsClopen B) :
    ∃ S : Set X, B = {U | S ∈ U} := by
  let f : Ultrafilter X → Bool := B.boolIndicator
  have hc : Continuous f := (continuous_boolIndicator_iff_isClopen B).2 hB
  obtain ⟨g,hg,_⟩ := continuous_observation_unique Bool f hc
  refine ⟨g ⁻¹' {true}, ?_⟩
  ext U
  rw [mem_setOf_eq, selected_fibre]
  rw [← hg U]
  simp [f, Set.boolIndicator]

/-- Give the record model precisely the topology transported from its already
proved ultrafilter equivalence. This is the task's Stone topology. -/
instance recordTopology (X : Type u) : TopologicalSpace (Record X) :=
  TopologicalSpace.induced toUltrafilter inferInstance

def recordHomeomorph (X : Type u) : Record X ≃ₜ Ultrafilter X :=
  { classification X with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := continuous_induced_rng.mpr (by
      change Continuous (toUltrafilter ∘ ofUltrafilter : Ultrafilter X → Ultrafilter X)
      simpa only [comp_def, to_of] using (continuous_id : Continuous (id : Ultrafilter X → Ultrafilter X))) }

theorem record_observation_continuous {X : Type u} (A : Type) [Fintype A]
    [TopologicalSpace A] [DiscreteTopology A] (f : X → A) :
    Continuous (fun r : Record X => r.choose A f) := by
  have h := (selected_continuous A f).comp (recordHomeomorph X).continuous
  convert h using 1
  funext r
  exact congrArg (fun s : Record X => s.choose A f) (of_to r).symm

theorem record_observation_unique {X : Type u} (A : Type) [Fintype A]
    [TopologicalSpace A] [DiscreteTopology A] (h : Record X → A) (hh : Continuous h) :
    ∃! f : X → A, ∀ r, h r = r.choose A f := by
  obtain ⟨f,hf,hfu⟩ := continuous_observation_unique A (h ∘ ofUltrafilter)
    (hh.comp (recordHomeomorph X).symm.continuous)
  refine ⟨f, ?_, ?_⟩
  · intro r
    have he := hf (toUltrafilter r)
    change h (ofUltrafilter (toUltrafilter r)) =
      (ofUltrafilter (toUltrafilter r)).choose A f at he
    simpa only [of_to] using he
  · intro g hg
    apply hfu
    intro U
    exact hg (ofUltrafilter U)

/-- The two unit laws supply different preimages at every non-point record. -/
theorem flatten_witness {X : Type u} (r : Record X)
    (hr : ∀ x, r ≠ Record.point x) :
    Record.point r ≠ Record.map Record.point r ∧
    Record.flatten (Record.point r) = r ∧
    Record.flatten (Record.map Record.point r) = r := by
  refine ⟨?_, Record.flatten_point r, Record.flatten_map_point r⟩
  intro he
  let S : Set (Record X) := range Record.point
  have hS : S ∈ toUltrafilter (Record.map Record.point r) := by
    rw [to_map]
    exact Filter.range_mem_map
  rw [← he, to_point] at hS
  obtain ⟨x,hx⟩ := hS
  exact hr x hx.symm

theorem flatten_not_injective_infinite (X : Type u) [Infinite X] :
    ¬ Injective (Record.flatten : Record (Record X) → Record X) := by
  obtain ⟨hne,h1,h2⟩ := flatten_witness (ofUltrafilter (hyperfilter X)) (free_record_not_point X)
  exact fun hi => hne (hi (h1.trans h2.symm))

/-- Exact boundary for multiplication, including the empty case. -/
theorem flatten_injective_iff_finite (X : Type u) :
    Injective (Record.flatten : Record (Record X) → Record X) ↔ Finite X := by
  constructor
  · intro hi
    by_contra hn
    letI : Infinite X := not_finite_iff_infinite.mp hn
    exact flatten_not_injective_infinite X hi
  · intro hfin
    letI : Finite X := hfin
    let e : X ≃ Record X := Equiv.ofBijective Record.point
      ⟨point_injective X, (point_surjective_iff_finite X).2 hfin⟩
    letI : Finite (Record X) := Finite.of_surjective e e.surjective
    intro R S he
    obtain ⟨r,rfl⟩ := (point_surjective_iff_finite (Record X)).2 inferInstance R
    obtain ⟨s,rfl⟩ := (point_surjective_iff_finite (Record X)).2 inferInstance S
    simpa using congrArg Record.point he

end MathGauge.ProgressiveObservations
