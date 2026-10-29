import FiniteCones
import DeletionConeGluing

/-! Actual coordinate homotopies for inclusion of faces and dominated vertices. -/
namespace MathGauge.GP001
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set ContinuousMap MathGauge.PublicProof.Topology unitInterval

variable {V : Type*} [Fintype V] [DecidableEq V]

def realizationInclusion {L K : PreAbstractSimplicialComplex V} (h : L ≤ K) :
    C(Realization L, Realization K) :=
  ⟨fun x => ⟨x.1, x.2.1, by obtain ⟨s, hs, hx⟩ := x.2.2; exact ⟨s, h hs, hx⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- A straight homotopy in the target complex; the source need not be a cone. -/
def inclusionNullhomotopy {L K : PreAbstractSimplicialComplex V} (h : L ≤ K)
    (a : V) (ha : {a} ∈ K) (hcone : ∀ s ∈ L, insert a s ∈ K) :
    (realizationInclusion h).Homotopy (ContinuousMap.const _ (vertex K a ha)) where
  toFun p := ⟨fun u => (1 - (p.1 : ℝ)) * p.2.1 u + (p.1 : ℝ) * (vertex K a ha).1 u, by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro u
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.1.2.2) (coordinate_nonneg p.2 u))
        (mul_nonneg p.1.2.1 (coordinate_nonneg (vertex K a ha) u))
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        coordinates_sum p.2, coordinates_sum (vertex K a ha)]
      ring
    · obtain ⟨s, hs, hx⟩ := p.2.2.2
      refine ⟨insert a s, hcone s hs, ?_⟩
      intro u hu
      have hua : u ≠ a := fun e => hu (e ▸ mem_insert_self a s)
      have hus : u ∉ s := fun hh => hu (mem_insert_of_mem hh)
      simp [hx u hus, vertex, Pi.single_eq_of_ne hua]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    have ht : Continuous (fun p : I × Realization L => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : I × Realization L => p.2.1 u) :=
      (continuous_apply u).comp (continuous_subtype_val.comp continuous_snd)
    exact ((continuous_const.sub ht).mul hx).add (ht.mul continuous_const)
  map_zero_left x := by apply Subtype.ext; funext u; simp [realizationInclusion]
  map_one_left x := by apply Subtype.ext; funext u; simp

/-- Transfer the mass at v linearly to w. -/
def foldCoordinates (v w : V) (t : I) (x : V → ℝ) (u : V) : ℝ :=
  x u + (Pi.single w ((t : ℝ) * x v) : V → ℝ) u - (Pi.single v ((t : ℝ) * x v) : V → ℝ) u

variable (K : PreAbstractSimplicialComplex V) (v w : V) (hvw : v ≠ w)
variable (hdom : ∀ s ∈ K, v ∈ s → insert w s ∈ K)

include hvw hdom in
theorem foldCoordinates_mem (t : I) (x : Realization K) :
    foldCoordinates v w t x.1 ∈ carrier K := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro u
    by_cases huv : u = v
    · subst u
      simp only [foldCoordinates, Pi.single_eq_of_ne hvw, Pi.single_eq_same, add_zero]
      nlinarith [coordinate_nonneg x v, t.2.2]
    · by_cases huw : u = w
      · subst u
        simp only [foldCoordinates, Pi.single_eq_same, Pi.single_eq_of_ne hvw.symm, sub_zero]
        exact add_nonneg (coordinate_nonneg x w) (mul_nonneg t.2.1 (coordinate_nonneg x v))
      · simpa [foldCoordinates, Pi.single_eq_of_ne huv, Pi.single_eq_of_ne huw] using
          coordinate_nonneg x u
  · simp [foldCoordinates, Finset.sum_sub_distrib, Finset.sum_add_distrib, coordinates_sum x]
  · obtain ⟨s, hs, hx⟩ := x.2.2
    by_cases hv : v ∈ s
    · refine ⟨insert w s, hdom s hs hv, ?_⟩
      intro u hu
      have huw : u ≠ w := fun e => hu (e ▸ mem_insert_self w s)
      have hus : u ∉ s := fun hh => hu (mem_insert_of_mem hh)
      have huv : u ≠ v := fun e => hus (e ▸ hv)
      simp [foldCoordinates, hx u hus, Pi.single_eq_of_ne huv, Pi.single_eq_of_ne huw]
    · refine ⟨s, hs, ?_⟩
      intro u hu
      simp [foldCoordinates, hx u hu, hx v hv]

def foldHomotopyMap : C(I × Realization K, Realization K) where
  toFun p := ⟨foldCoordinates v w p.1 p.2.1, foldCoordinates_mem K v w hvw hdom p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    change Continuous (fun p : I × Realization K => foldCoordinates v w p.1 p.2.1 u)
    have hx (a : V) : Continuous (fun p : I × Realization K => p.2.1 a) :=
      (continuous_apply a).comp (continuous_subtype_val.comp continuous_snd)
    have ht : Continuous (fun p : I × Realization K => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hs (a : V) : Continuous (fun p : I × Realization K =>
        (Pi.single a ((p.1 : ℝ) * p.2.1 v) : V → ℝ) u) := by
      by_cases hua : u = a
      · apply (ht.mul (hx v)).congr
        intro p
        simp [Pi.single_apply, hua]
      · simpa only [Pi.single_apply, hua, ite_false] using
          (continuous_const : Continuous (fun _ : I × Realization K => (0 : ℝ)))
    exact ((hx u).add (hs w)).sub (hs v)

@[simp] theorem foldCoordinates_zero (x : V → ℝ) : foldCoordinates v w 0 x = x := by
  funext u
  simp [foldCoordinates]

include hvw in
@[simp] theorem foldCoordinates_one_at_removed (x : V → ℝ) :
    foldCoordinates v w 1 x v = 0 := by
  simp [foldCoordinates, Pi.single_eq_of_ne hvw]

theorem foldCoordinates_of_zero (t : I) (x : V → ℝ) (hx : x v = 0) :
    foldCoordinates v w t x = x := by
  funext u
  simp [foldCoordinates, hx]

def foldRetraction : C(Realization K, Realization (deletion K v)) where
  toFun x := ⟨foldCoordinates v w 1 x.1,
    mem_carrier_deletion_iff.mpr ⟨foldCoordinates_mem K v w hvw hdom 1 x,
      foldCoordinates_one_at_removed v w hvw x.1⟩⟩
  continuous_toFun :=
    (continuous_subtype_val.comp ((foldHomotopyMap K v w hvw hdom).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _

@[simp] theorem foldRetraction_inclusion (x : Realization (deletion K v)) :
    foldRetraction K v w hvw hdom (deletion_to_realization K v x) = x := by
  apply Subtype.ext
  exact foldCoordinates_of_zero v w 1 x.1 (mem_carrier_deletion_iff.mp x.2).2

def foldHomotopy : (ContinuousMap.id (Realization K)).Homotopy
    ((deletion_to_realization K v).comp (foldRetraction K v w hvw hdom)) where
  toContinuousMap := foldHomotopyMap K v w hvw hdom
  map_zero_left x := Subtype.ext (foldCoordinates_zero v w x.1)
  map_one_left _ := rfl

@[simp] theorem foldHomotopy_fixes (t : I) (x : Realization K) (hx : x.1 v = 0) :
    foldHomotopy K v w hvw hdom (t, x) = x :=
  Subtype.ext (foldCoordinates_of_zero v w t x.1 hx)

def foldEquiv : Realization K ≃ₕ Realization (deletion K v) where
  toFun := foldRetraction K v w hvw hdom
  invFun := deletion_to_realization K v
  left_inv := ⟨(foldHomotopy K v w hvw hdom).symm⟩
  right_inv := by
    have h : (foldRetraction K v w hvw hdom).comp (deletion_to_realization K v) =
        ContinuousMap.id _ := by
      apply DFunLike.ext
      intro x
      exact foldRetraction_inclusion K v w hvw hdom x
    rw [h]

end
end MathGauge.GP001
