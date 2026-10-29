import TowerClassification
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Module

universe u v w
namespace MathGauge.Tower.FreeTower
variable {R : Type} [CommRing R] (T : FreeTower.{u} R)

theorem homTransition_comp (A : Type v) [AddCommGroup A] [Module R A]
    (n m r : ℕ) (hnm : n ≤ m) (hmr : m ≤ r) :
    (T.homTransition A m r hmr).comp (T.homTransition A n m hnm) =
      T.homTransition A n r (hnm.trans hmr) := by
  ext f x
  change f (T.transition n m hnm (T.transition m r hmr x)) =
    f (T.transition n r (hnm.trans hmr) x)
  exact congrArg f (LinearMap.congr_fun (T.transition_comp n m r hnm hmr) x)

/-- A finite family of actual direct-limit elements has representatives at one
common stage. The target modules may depend on the family index. -/
theorem finite_records_common_stage {ι : Type w} [Finite ι]
    (A : ι → Type v) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (x : ∀ i, T.Record (A i)) :
    ∃ n, ∃ f : ∀ i, T.stage n →ₗ[R] A i, ∀ i, T.recordOf (A i) n (f i) = x i := by
  classical
  letI := Fintype.ofFinite ι
  choose n f hf using fun i => T.record_exists (A i) (x i)
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i => T.homTransition (A i) (n i) N (hn i) (f i), ?_⟩
  intro i
  rw [T.recordOf_transition, hf]

/-- Finitely many eventual equalities can be witnessed at one common later stage. -/
theorem finite_equalities_common_stage {ι : Type w} [Finite ι]
    (A : ι → Type v) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (n m : ℕ) (f : ∀ i, T.stage n →ₗ[R] A i) (g : ∀ i, T.stage m →ₗ[R] A i)
    (h : ∀ i, T.recordOf (A i) n (f i) = T.recordOf (A i) m (g i)) :
    ∃ r, ∃ hnr : n ≤ r, ∃ hmr : m ≤ r,
      ∀ i, T.homTransition (A i) n r hnr (f i) = T.homTransition (A i) m r hmr (g i) := by
  classical
  letI := Fintype.ofFinite ι
  choose r hn hm he using fun i => (T.record_eq_iff (A i) n m (f i) (g i)).mp (h i)
  let N := max (max n m) (Finset.univ.sup r)
  have hnN : n ≤ N := (le_max_left n m).trans (le_max_left _ _)
  have hmN : m ≤ N := (le_max_right n m).trans (le_max_left _ _)
  have hrN (i : ι) : r i ≤ N := (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨N, hnN, hmN, fun i => ?_⟩
  have hh := congrArg (T.homTransition (A i) (r i) N (hrN i)) (he i)
  change ((T.homTransition (A i) (r i) N (hrN i)).comp
    (T.homTransition (A i) n (r i) (hn i))) (f i) =
    ((T.homTransition (A i) (r i) N (hrN i)).comp
      (T.homTransition (A i) m (r i) (hm i))) (g i) at hh
  simpa only [T.homTransition_comp] using hh

/-- Actual finite-free lifting; the lift is constructed on a chosen finite basis. -/
theorem finite_free_map_lifts (A : Type v) [AddCommGroup A] [Module R A]
    (W : Type w) [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
    (f : W →ₗ[R] T.Record A) :
    ∃ n, ∃ g : W →ₗ[R] (T.stage n →ₗ[R] A), (T.recordOf A n).comp g = f := by
  let b := Module.Free.chooseBasis R W
  obtain ⟨n,v,hv⟩ := T.finite_records_common_stage (fun _ : Module.Free.ChooseBasisIndex R W => A)
    (fun i => f (b i))
  refine ⟨n,b.constr R v, ?_⟩
  apply b.ext
  intro i
  simpa only [LinearMap.comp_apply, Basis.constr_basis] using hv i

theorem finite_free_maps_eventually_equal (A : Type v) [AddCommGroup A] [Module R A]
    (W : Type w) [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
    (n m : ℕ) (f : W →ₗ[R] (T.stage n →ₗ[R] A)) (g : W →ₗ[R] (T.stage m →ₗ[R] A))
    (h : (T.recordOf A n).comp f = (T.recordOf A m).comp g) :
    ∃ r, ∃ hnr : n ≤ r, ∃ hmr : m ≤ r,
      (T.homTransition A n r hnr).comp f = (T.homTransition A m r hmr).comp g := by
  let b := Module.Free.chooseBasis R W
  obtain ⟨r,hnr,hmr,he⟩ := T.finite_equalities_common_stage
    (fun _ : Module.Free.ChooseBasisIndex R W => A) n m (fun i => f (b i)) (fun i => g (b i))
    (fun i => LinearMap.congr_fun h (b i))
  exact ⟨r,hnr,hmr,b.ext he⟩

theorem finite_invariant_iff_stage_surjective (T : FreeTower.{u} ℤ) :
    Module.Finite ℤ T.Invariant ↔ ∃ n, Function.Surjective (T.recordOf ℤ n) := by
  constructor
  · intro h
    letI := h
    letI : Module.Free ℤ T.Invariant := Module.free_of_finite_type_torsion_free'
    obtain ⟨n,j,hj⟩ := T.finite_free_map_lifts ℤ T.Invariant LinearMap.id
    refine ⟨n, fun x => ⟨j x, ?_⟩⟩
    exact LinearMap.congr_fun hj x
  · rintro ⟨n,hn⟩
    exact Module.Finite.of_surjective (T.recordOf ℤ n) hn

end MathGauge.Tower.FreeTower
