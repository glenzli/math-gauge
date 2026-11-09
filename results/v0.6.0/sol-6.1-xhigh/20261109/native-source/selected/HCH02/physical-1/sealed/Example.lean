import Scalar

open scoped ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

namespace HCH02.Counterexample

/- 0 is absorbing.  The two live points have input distance infinity
   and output distance one; all strictly positive scalars work. -/
def distance (i : Bool) (x y : Fin 3) : ℝ≥0∞ :=
  if x = y then 0 else if x = 0 ∨ y = 0 then ⊤ else if i then 1 else ⊤

theorem gauge (i : Bool) : ExtendedPseudoMetric (Fin 3) 0 (distance i) := by
  constructor
  · exact ⟨1, by decide⟩
  · intro x
    simp [distance]
  · intro x y
    fin_cases x <;> fin_cases y <;> cases i <;> norm_num [distance]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> cases i <;> norm_num [distance]
  · intro x hx
    simp [distance, hx]

def live : Set (Fin 3) := {x | x ≠ 0}
def op : Operator (Fin 3) 0 := HCH02.identity

theorem live_legal : live.Nonempty ∧ live ⊆ dom op := by
  exact ⟨⟨1, by change (1 : Fin 3) ≠ 0; decide⟩, fun _ hx => hx⟩

theorem every_positive {a : ℝ≥0∞} (ha : 0 < a) :
    a ∈ Scalars distance op live false true := by
  intro x hx y hy
  have hx0 : x ≠ 0 := hx
  have hy0 : y ≠ 0 := hy
  by_cases hxy : x = y
  · subst y
    simp [distance, op, HCH02.identity]
  · simp [distance, op, HCH02.identity, hxy, hx0, hy0, ENNReal.mul_top ha.ne']

theorem zero_not_feasible : (0 : ℝ≥0∞) ∉ Scalars distance op live false true := by
  intro h
  have hh := h 1 (by change (1 : Fin 3) ≠ 0; decide)
    2 (by change (2 : Fin 3) ≠ 0; decide)
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have hh' : (1 : ℝ≥0∞) ≤ 0 := by
    simpa [distance, op, HCH02.identity, h12, h10, h20] using hh
  exact (not_le_of_gt zero_lt_one) hh'

theorem inf_zero : scalarInf distance op live false true = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro b hb
  obtain ⟨a, ha, hab⟩ := exists_between hb
  exact (sInf_le (every_positive ha)).trans_lt hab

theorem zero_inf_unattained :
    (∀ i, ExtendedPseudoMetric (Fin 3) 0 (distance i)) ∧
    live.Nonempty ∧ live ⊆ dom op ∧
    scalarInf distance op live false true = 0 ∧
    (0 : ℝ≥0∞) ∉ Scalars distance op live false true :=
  ⟨gauge, live_legal.1, live_legal.2, inf_zero, zero_not_feasible⟩

end HCH02.Counterexample
