import TowerStageTools

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Module

universe u
namespace MathGauge.Tower.FreeTower
variable {R : Type} [CommRing R] (T : FreeTower.{u} R)

/-- Exact original-stage criterion from the reference. No coherence among the
separately chosen maps `u` is imposed. -/
def FiniteStageCriterion : Prop :=
  ∃ n, ∃ d : T.stage n →ₗ[R] T.stage n, d.comp d = d ∧
    ∀ m (hnm : n ≤ m), ∃ u : T.stage n →ₗ[R] T.stage m,
      ∃ r, ∃ hmr : m ≤ r,
        u.comp d = u ∧ (T.transition n m hnm).comp u = d ∧
          u.comp (T.transition n r (hnm.trans hmr)) = T.transition m r hmr

def DualStageCriterion : Prop :=
  ∃ n, ∃ e : Module.Dual R (T.stage n) →ₗ[R] Module.Dual R (T.stage n), e.comp e = e ∧
    ∀ m (hnm : n ≤ m), ∃ β : Module.Dual R (T.stage m) →ₗ[R] Module.Dual R (T.stage n),
      ∃ r, ∃ hmr : m ≤ r,
        e.comp β = β ∧ β.comp (T.homTransition R n m hnm) = e ∧
          (T.homTransition R n r (hnm.trans hmr)).comp β = T.homTransition R m r hmr

def transposeDual {n m : ℕ}
    (f : Module.Dual R (T.stage n) →ₗ[R] Module.Dual R (T.stage m)) :
    T.stage m →ₗ[R] T.stage n :=
  (Module.evalEquiv R (T.stage n)).symm.toLinearMap.comp
    (f.dualMap.comp (Module.evalEquiv R (T.stage m)).toLinearMap)

@[simp] theorem transposeDual_pairing {n m : ℕ}
    (f : Module.Dual R (T.stage n) →ₗ[R] Module.Dual R (T.stage m))
    (ℓ : Module.Dual R (T.stage n)) (x : T.stage m) :
    ℓ (T.transposeDual f x) = f ℓ x := by simp [transposeDual]

theorem transposeDual_comp {n m r : ℕ}
    (f : Module.Dual R (T.stage n) →ₗ[R] Module.Dual R (T.stage m))
    (g : Module.Dual R (T.stage m) →ₗ[R] Module.Dual R (T.stage r)) :
    T.transposeDual (g.comp f) = (T.transposeDual f).comp (T.transposeDual g) := by
  ext x
  apply (Module.evalEquiv R (T.stage n)).injective
  ext ℓ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply,
    T.transposeDual_pairing]

@[simp] theorem transposeDual_dualMap {n m : ℕ} (f : T.stage m →ₗ[R] T.stage n) :
    T.transposeDual f.dualMap = f := by
  ext x
  apply (Module.evalEquiv R (T.stage n)).injective
  ext ℓ
  simp

@[simp] theorem transposeDual_homTransition (n m : ℕ) (h : n ≤ m) :
    T.transposeDual (T.homTransition R n m h) = T.transition n m h :=
  T.transposeDual_dualMap (T.transition n m h)

theorem finiteStage_iff_dualStage : T.FiniteStageCriterion ↔ T.DualStageCriterion := by
  constructor
  · rintro ⟨n,d,hd,h⟩
    refine ⟨n,d.dualMap,?_,?_⟩
    · rw [LinearMap.dualMap_comp_dualMap,hd]
    · intro m hnm
      obtain ⟨u,r,hmr,hud,hρu,huρ⟩ := h m hnm
      refine ⟨u.dualMap,r,hmr,?_,?_,?_⟩
      · rw [LinearMap.dualMap_comp_dualMap,hud]
      · change u.dualMap.comp (T.transition n m hnm).dualMap = d.dualMap
        rw [LinearMap.dualMap_comp_dualMap,hρu]
      · change (T.transition n r (hnm.trans hmr)).dualMap.comp u.dualMap =
          (T.transition m r hmr).dualMap
        rw [LinearMap.dualMap_comp_dualMap,huρ]
  · rintro ⟨n,e,he,h⟩
    refine ⟨n,T.transposeDual e,?_,?_⟩
    · rw [← T.transposeDual_comp,he]
    · intro m hnm
      obtain ⟨β,r,hmr,heβ,hβα,hαβ⟩ := h m hnm
      refine ⟨T.transposeDual β,r,hmr,?_,?_,?_⟩
      · rw [← T.transposeDual_comp,heβ]
      · rw [← T.transposeDual_homTransition n m hnm,← T.transposeDual_comp,hβα]
      · rw [← T.transposeDual_homTransition n r (hnm.trans hmr),
          ← T.transposeDual_homTransition m r hmr,← T.transposeDual_comp,hαβ]

variable (T : FreeTower.{u} ℤ)

theorem finite_invariant_implies_dualStage [Module.Finite ℤ T.Invariant] :
    T.DualStageCriterion := by
  letI : Module.Free ℤ T.Invariant := Module.free_of_finite_type_torsion_free'
  obtain ⟨n,j,hj⟩ := T.finite_free_map_lifts ℤ T.Invariant LinearMap.id
  let e := j.comp (T.recordOf ℤ n)
  have he : e.comp e = e := by
    apply LinearMap.ext
    intro ℓ
    change j (T.recordOf ℤ n (j (T.recordOf ℤ n ℓ))) = j (T.recordOf ℤ n ℓ)
    rw [show T.recordOf ℤ n (j (T.recordOf ℤ n ℓ)) = T.recordOf ℤ n ℓ from
      LinearMap.congr_fun hj (T.recordOf ℤ n ℓ)]
  refine ⟨n,e,he,?_⟩
  intro m hnm
  let β := j.comp (T.recordOf ℤ m)
  have hb : (T.recordOf ℤ n).comp β = T.recordOf ℤ m := by
    ext ℓ
    exact LinearMap.congr_fun hj (T.recordOf ℤ m ℓ)
  have hbi : (T.recordOf ℤ n).comp β = (T.recordOf ℤ m).comp LinearMap.id := by simpa using hb
  obtain ⟨r,hnr,hmr,hr⟩ := T.finite_free_maps_eventually_equal ℤ (Module.Dual ℤ (T.stage m))
    n m β LinearMap.id hbi
  refine ⟨β,r,hmr,?_,?_,?_⟩
  · change (j.comp (T.recordOf ℤ n)).comp β = β
    rw [LinearMap.comp_assoc,hb]
  · apply LinearMap.ext
    intro ℓ
    change j (T.recordOf ℤ m (T.homTransition ℤ n m hnm ℓ)) = j (T.recordOf ℤ n ℓ)
    rw [T.recordOf_transition]
  · simpa only [LinearMap.comp_id] using hr

theorem dualStage_implies_finite_invariant (h : T.DualStageCriterion) :
    Module.Finite ℤ T.Invariant := by
  obtain ⟨n,e,he,h⟩ := h
  apply T.finite_invariant_iff_stage_surjective.mpr
  refine ⟨n,?_⟩
  intro x
  obtain ⟨m,ℓ,rfl⟩ := T.record_exists ℤ x
  let k := max n m
  have hnk : n ≤ k := le_max_left _ _
  have hmk : m ≤ k := le_max_right _ _
  obtain ⟨β,r,hkr,heβ,hβα,hαβ⟩ := h k hnk
  let z := T.homTransition ℤ m k hmk ℓ
  refine ⟨β z,?_⟩
  have hz : T.recordOf ℤ n (β z) = T.recordOf ℤ k z := by
    apply (T.record_eq_iff ℤ n k (β z) z).mpr
    exact ⟨r,hnk.trans hkr,hkr,LinearMap.congr_fun hαβ z⟩
  exact hz.trans (T.recordOf_transition ℤ m k hmk ℓ)

/-- The optional finite-layer criterion is equivalent to the original invariant
criterion, with every existential witness constructed from the actual tower. -/
theorem finiteStage_iff_finite_invariant : T.FiniteStageCriterion ↔ Module.Finite ℤ T.Invariant := by
  rw [T.finiteStage_iff_dualStage]
  exact ⟨T.dualStage_implies_finite_invariant, fun h => by
    letI := h
    exact T.finite_invariant_implies_dualStage⟩

theorem finiteStage_iff_representable : T.FiniteStageCriterion ↔ T.Representable :=
  T.finiteStage_iff_finite_invariant.trans T.representable_iff_finite.symm

end MathGauge.Tower.FreeTower
