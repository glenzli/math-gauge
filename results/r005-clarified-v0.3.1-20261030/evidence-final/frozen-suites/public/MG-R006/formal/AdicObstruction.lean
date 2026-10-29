import ObstructionNaturality
import AdicCounterexample

noncomputable section
set_option maxHeartbeats 800000
namespace MathGauge.AdicCounterexample
open MathGauge.AbelianTower

def beta (_ : ℕ) : ℤ →+ ℤ := AddMonoidHom.id ℤ

def compatibleRecord : limit (fun n => (gamma n).toAddMonoidHom) :=
  ⟨record,(mem_limit _ _).mpr record_compatible⟩

theorem quotientDiagram : ∀ n,
    (gamma n).toAddMonoidHom.comp (pi (n+1))=(pi n).comp (beta n) := by
  intro n; simpa only [AddMonoidHom.comp_id] using (diagram_commutes n).2

theorem inverse_limit_not_surjective :
    ¬Function.Surjective (limitMap (A := fun _ => ℤ) beta (fun n => (gamma n).toAddMonoidHom) pi quotientDiagram) := by
  intro h
  obtain ⟨b,hb⟩ := h compatibleRecord
  apply no_compatible_lift
  refine ⟨b.val, (mem_limit (A := fun _ => ℤ) beta b.val).mp b.property, ?_⟩
  intro n
  exact congrArg (fun c : limit (fun n => (gamma n).toAddMonoidHom) => c.val n) hb

/-- The B-limit in this actual tower is precisely the original integer group. -/
def integerLimitEquiv : limit (A := fun _ => ℤ) beta ≃+ ℤ where
  toFun b := b.val 0
  invFun z := ⟨fun _ => z,(mem_limit (A := fun _ => ℤ) beta _).mpr (fun _ => rfl)⟩
  left_inv b := by
    apply Subtype.ext; funext n
    have hc := (mem_limit (A := fun _ => ℤ) beta b.val).mp b.property
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hc n).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem actual_obstruction_nontrivial :
    ¬∀ z : ObstructionGroup (A := fun n => A n) alpha, z=0 := by
  intro hz
  apply inverse_limit_not_surjective
  exact (obstruction_trivial_iff (A := fun n => A n) (B := fun _ => ℤ) (C := C) alpha beta (fun n => (gamma n).toAddMonoidHom)
    (fun n => (A n).subtype) pi
    (fun n => (rows_exact n).2.2) (fun n => (rows_exact n).1)
    (fun n => (diagram_commutes n).1.symm) quotientDiagram pi_surjective
    (fun _ => Function.surjective_id)).mp hz

end MathGauge.AdicCounterexample
