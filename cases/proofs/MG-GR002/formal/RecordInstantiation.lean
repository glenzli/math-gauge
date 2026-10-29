import RecordTransform
import CompatibleRecords

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace MathGauge.RecordInstantiation
open RecordBidual
local instance dual_group : AddCommGroup (Dual CompatibleRecords.E) := inferInstance

/-- The c₀ counterexample is an instance of the original-record structure used by the
general bidual theory; it is not merely a separate abstract interpretation. -/
def c0Record : Record CompatibleRecords.E where
  value F := CompatibleRecords.record F.val
  compatible _F _G _h _φ := rfl
  bounded := ⟨1, by norm_num, fun F φ => by
    simpa only [Real.norm_eq_abs, one_mul] using CompatibleRecords.record_bound F.val φ⟩

theorem c0Record_no_realization : ¬ ∃ x, Represents c0Record x := by
  rintro ⟨x,hx⟩
  apply CompatibleRecords.no_original_realization
  refine ⟨x,?_⟩
  intro F hF φ
  exact hx ⟨F,hF⟩ φ

theorem c0Record_bidual_norm : ‖c0Record.toBidual‖ ≤ 1 := by
  apply bidual_norm_le_given_bound c0Record (by norm_num)
  intro F φ
  simpa only [Real.norm_eq_abs, one_mul] using CompatibleRecords.record_bound F.val φ

theorem c0_bidual_outside_original :
    c0Record.toBidual ∉ Set.range (J : CompatibleRecords.E → Bidual CompatibleRecords.E) := by
  intro h
  exact c0Record_no_realization ((realization_exists_iff c0Record).mpr h)

end MathGauge.RecordInstantiation
