import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

open scoped Pointwise
namespace MathGauge.F105
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def cosetSlice (A : Finset G) (H : AddSubgroup G) (x : G) : Finset G := by
  classical
  exact A.filter (fun a => a - x ∈ H)

def Covers (A : Finset G) (H : AddSubgroup G) (F : Finset G) : Prop :=
  ∀ a ∈ A, ∃ t ∈ F, a - t ∈ H

@[simp] theorem mem_cosetSlice (A : Finset G) (H : AddSubgroup G) (x a : G) :
    a ∈ cosetSlice A H x ↔ a ∈ A ∧ a - x ∈ H := by
  classical
  simp [cosetSlice]

theorem slice_subset (A : Finset G) (H : AddSubgroup G) (x : G) :
    cosetSlice A H x ⊆ A := by
  intro a ha
  exact (mem_cosetSlice A H x a).mp ha |>.1

end MathGauge.F105
