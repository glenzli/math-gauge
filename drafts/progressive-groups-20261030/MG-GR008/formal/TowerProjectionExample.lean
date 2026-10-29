import TowerFiniteStage
import TowerFiniteLimits
import Mathlib.Tactic.NormNum

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Module CategoryTheory MathGauge.TensorClassification

namespace MathGauge.Tower.Examples
open FreeTower

def firstProjection : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
  (LinearMap.inl ℤ ℤ ℤ).comp (LinearMap.fst ℤ ℤ ℤ)

@[simp] theorem firstProjection_apply (x : ℤ × ℤ) : firstProjection x = (x.1,0) := rfl

theorem firstProjection_idempotent : firstProjection.comp firstProjection = firstProjection := by
  ext x <;> rfl

/-- The original rank-two tower with the noninvertible idempotent projection. -/
@[reducible] def projectionTower : FreeTower ℤ where
  stage _ := ModuleCat.of ℤ (ℤ × ℤ)
  step _ := firstProjection
  free _ := inferInstance
  finite _ := inferInstance

theorem projection_transition (n m : ℕ) (h : n ≤ m) :
    projectionTower.transition n m h = if n = m then LinearMap.id else firstProjection := by
  induction m,h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    rw [projectionTower.transition_succ n m h,ih]
    have hn : n ≠ m+1 := by omega
    rw [if_neg hn]
    change (if n = m then LinearMap.id else firstProjection).comp firstProjection = firstProjection
    split
    · exact LinearMap.id_comp _
    · exact firstProjection_idempotent

theorem projection_transition_strict (n m : ℕ) (h : n < m) :
    projectionTower.transition n m h.le = firstProjection := by
  rw [projection_transition,if_neg (Nat.ne_of_lt h)]

theorem projection_transition_axis (n m : ℕ) (h : n ≤ m) (a : ℤ) :
    projectionTower.transition n m h (a,0) = (a,0) := by
  rw [projection_transition]
  split <;> rfl

theorem projection_finite_stage_criterion : projectionTower.FiniteStageCriterion := by
  refine ⟨0,firstProjection,firstProjection_idempotent,?_⟩
  intro m hm
  refine ⟨firstProjection,m+1,Nat.le_succ m,firstProjection_idempotent,?_,?_⟩
  · rw [projection_transition]
    split
    · exact LinearMap.id_comp _
    · exact firstProjection_idempotent
  · rw [projection_transition_strict 0 (m+1) (Nat.zero_lt_succ m),
      projection_transition_strict m (m+1) (Nat.lt_succ_self m)]
    exact firstProjection_idempotent

def firstAxisEval : Module.Dual ℤ (ℤ × ℤ) →ₗ[ℤ] ℤ where
  toFun ℓ := ℓ (1,0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projectionInvariantToInt : projectionTower.Invariant →ₗ[ℤ] ℤ :=
  Module.DirectLimit.lift ℤ ℕ _ (projectionTower.homTransition ℤ) (fun _ => firstAxisEval)
    (fun n m h ℓ => by
      change ℓ (projectionTower.transition n m h (1,0)) = ℓ (1,0)
      rw [projection_transition_axis])

@[simp] theorem projectionInvariantToInt_of (n : ℕ) (ℓ : Module.Dual ℤ (ℤ × ℤ)) :
    projectionInvariantToInt (projectionTower.recordOf ℤ n ℓ) = ℓ (1,0) :=
  Module.DirectLimit.lift_of _ _ _

def projectionInvariantFromInt : ℤ →ₗ[ℤ] projectionTower.Invariant :=
  (projectionTower.recordOf ℤ 0).comp
    (LinearMap.toSpanSingleton ℤ (Module.Dual ℤ (ℤ × ℤ)) (LinearMap.fst ℤ ℤ ℤ))

theorem projectionInvariant_left_inverse :
    projectionInvariantFromInt.comp projectionInvariantToInt = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨n,ℓ,rfl⟩ := projectionTower.record_exists ℤ x
  change projectionInvariantFromInt (projectionInvariantToInt (projectionTower.recordOf ℤ n ℓ)) = _
  rw [projectionInvariantToInt_of]
  change projectionTower.recordOf ℤ 0 (ℓ (1,0) • LinearMap.fst ℤ ℤ ℤ) = projectionTower.recordOf ℤ n ℓ
  apply (projectionTower.record_eq_iff ℤ 0 n _ _).mpr
  refine ⟨n+1,Nat.zero_le _,Nat.le_succ n,?_⟩
  apply LinearMap.ext
  intro x
  change (ℓ (1,0) • LinearMap.fst ℤ ℤ ℤ)
    (projectionTower.transition 0 (n+1) _ x) = ℓ (projectionTower.transition n (n+1) _ x)
  rw [projection_transition_strict 0 (n+1) (Nat.zero_lt_succ n),
    projection_transition_strict n (n+1) (Nat.lt_succ_self n)]
  have hh := ℓ.map_smul x.1 ((1,0) : ℤ × ℤ)
  change ℓ (1,0) * x.1 = ℓ (x.1,0)
  rw [mul_comm]
  simpa only [Prod.smul_mk,smul_eq_mul,mul_one,mul_zero] using hh.symm

theorem projectionInvariant_right_inverse :
    projectionInvariantToInt.comp projectionInvariantFromInt = LinearMap.id := by
  apply LinearMap.ext
  intro z
  change projectionInvariantToInt (projectionTower.recordOf ℤ 0
    (z • LinearMap.fst ℤ ℤ ℤ)) = z
  rw [projectionInvariantToInt_of]
  simp

def projectionInvariantEquiv : projectionTower.Invariant ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofLinear projectionInvariantToInt projectionInvariantFromInt
    projectionInvariant_right_inverse projectionInvariant_left_inverse

/-- This is represented by the ordinary integer group, even though every
adjacent map has a nonzero kernel. -/
def projectionRepresentation : projectionTower.recordFunctor ≅ homFunctor (R := ℤ) ℤ :=
  projectionTower.tensorRecordNatIso.symm.trans
    ((tensorIso projectionInvariantEquiv).trans
      ((finiteDualRepresentation ℤ).trans
        (homIsoOfEquiv (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))))

theorem projection_step_not_injective (n : ℕ) :
    ¬ Function.Injective (projectionTower.step n) := by
  intro h
  have he := h (show projectionTower.step n (0,1) = projectionTower.step n (0,0) from rfl)
  have := congrArg Prod.snd he
  norm_num at this

theorem projection_never_eventually_isomorphisms :
    ¬ ∃ N, ∀ n, N ≤ n → Function.Bijective (projectionTower.step n) := by
  rintro ⟨N,h⟩
  exact projection_step_not_injective N (h N le_rfl).1

end MathGauge.Tower.Examples
