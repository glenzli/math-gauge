import RankOneClassification

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Module CategoryTheory MathGauge.TensorClassification
namespace MathGauge.Tower.RankOne
open FreeTower Examples

theorem classification_with_signs (a : ℕ → ℤ) :
    (tower a).Representable ↔
      (∀ N, ∃ n, N≤n ∧ a n=0) ∨ (∃ N, ∀ n, N≤n → a n=1 ∨ a n= -1) := by
  simpa only [CofinalZeros,EventualUnits,Int.isUnit_iff] using representability_classification a

theorem record_zero_of_cofinalZeros (a : ℕ → ℤ) (ha : CofinalZeros a)
    (A : Type*) [AddCommGroup A] [Module ℤ A] (x : (tower a).Record A) : x=0 := by
  obtain ⟨n,f,rfl⟩ := (tower a).record_exists A x
  obtain ⟨j,hnj,hj⟩ := ha n
  rw [← (tower a).recordOf_transition A n (j+1) (Nat.le_succ_of_le hnj) f]
  have hz : (tower a).homTransition A n (j+1) (Nat.le_succ_of_le hnj) f=0 := by
    apply LinearMap.ext
    intro z
    change f ((tower a).transition n (j+1) _ z)=0
    rw [transition_killed a hnj hj]
    exact map_zero f
  rw [hz,map_zero]

def zeroRepresentation (a : ℕ → ℤ) (ha : CofinalZeros a) :
    (tower a).recordFunctor ≅ homFunctor (R := ℤ) PUnit.{1} :=
  NatIso.ofComponents (fun A =>
    { hom := 0
      inv := 0
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (record_zero_of_cofinalZeros a ha A x).symm
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        change PUnit.{1} →ₗ[ℤ] A at f
        apply LinearMap.ext
        intro z
        change (0:A)=f z
        rw [Subsingleton.elim z 0,map_zero] })
    (by intros; simp)

theorem unit_tail_stage_bijective (a : ℕ → ℤ) (N : ℕ) (ha : ∀ n, N≤n → IsUnit (a n)) :
    Function.Bijective ((tower a).recordOf ℤ N) := by
  constructor
  · intro f g hfg
    obtain ⟨r,hnr,hnr',he⟩ := ((tower a).record_eq_iff ℤ N N f g).mp hfg
    apply LinearMap.ext
    intro x
    obtain ⟨z,hz⟩ := (transition_bijective a ha N r le_rfl hnr).2 x
    have hh := LinearMap.congr_fun he z
    change f ((tower a).transition N r hnr z)=g ((tower a).transition N r hnr z) at hh
    rwa [hz] at hh
  · intro x
    obtain ⟨m,f,rfl⟩ := (tower a).record_exists ℤ x
    let k := max N m
    have hNk : N≤k := le_max_left _ _
    have hmk : m≤k := le_max_right _ _
    let g := (tower a).homTransition ℤ m k hmk f
    let e := LinearEquiv.ofBijective ((tower a).transition N k hNk)
      (transition_bijective a ha N k le_rfl hNk)
    let v := g.comp e.symm.toLinearMap
    have hv : (tower a).homTransition ℤ N k hNk v=g := by
      apply LinearMap.ext
      intro z
      exact congrArg g (e.symm_apply_apply z)
    refine ⟨v,?_⟩
    rw [← (tower a).recordOf_transition ℤ N k hNk v,hv]
    exact (tower a).recordOf_transition ℤ m k hmk f

def unitInvariantEquivInt (a : ℕ → ℤ) (N : ℕ) (ha : ∀ n, N≤n → IsUnit (a n)) :
    (tower a).Invariant ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective ((tower a).recordOf ℤ N) (unit_tail_stage_bijective a N ha)).symm.trans
    (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ)

def unitRepresentation (a : ℕ → ℤ) (ha : EventualUnits a) :
    (tower a).recordFunctor ≅ homFunctor (R := ℤ) ℤ :=
  (tower a).tensorRecordNatIso.symm.trans
    ((tensorIso (unitInvariantEquivInt a (Classical.choose ha) (Classical.choose_spec ha))).trans
      ((finiteDualRepresentation ℤ).trans (homIsoOfEquiv (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))))

theorem all_zero_representatives (a : ℕ → ℤ) (ha : CofinalZeros a) (P : ModuleCat ℤ) :
    Nonempty ((tower a).recordFunctor ≅ homFunctor (R := ℤ) P) ↔ Nonempty (P ≃ₗ[ℤ] PUnit.{1}) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨representingObjectEquiv (e.symm.trans (zeroRepresentation a ha))⟩
  · rintro ⟨e⟩
    exact ⟨(zeroRepresentation a ha).trans (homIsoOfEquiv e.symm)⟩

theorem all_unit_representatives (a : ℕ → ℤ) (ha : EventualUnits a) (P : ModuleCat ℤ) :
    Nonempty ((tower a).recordFunctor ≅ homFunctor (R := ℤ) P) ↔ Nonempty (P ≃ₗ[ℤ] ℤ) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨representingObjectEquiv (e.symm.trans (unitRepresentation a ha))⟩
  · rintro ⟨e⟩
    exact ⟨(unitRepresentation a ha).trans (homIsoOfEquiv e.symm)⟩

theorem nonzero_tail_cofinal_nonunits_not_representable (a : ℕ → ℤ)
    (hz : ∃ N, ∀ n, N≤n → a n≠0)
    (hu : ∀ N, ∃ n, N≤n ∧ ¬ IsUnit (a n)) : ¬ (tower a).Representable := by
  intro hr
  rcases (representability_classification a).mp hr with hzero | hunit
  · obtain ⟨N,hN⟩ := hz
    obtain ⟨n,hn,he⟩ := hzero N
    exact hN n hn he
  · obtain ⟨N,hN⟩ := hunit
    obtain ⟨n,hn,he⟩ := hu N
    exact he (hN n hn)

end MathGauge.Tower.RankOne
