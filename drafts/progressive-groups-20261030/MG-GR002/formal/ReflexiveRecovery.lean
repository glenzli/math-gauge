import RecordTransform
import Mathlib.Analysis.LocallyConvex.WeakDual

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace MathGauge.RecordBidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reflexivity is surjectivity of the actual canonical bidual embedding. -/
def reflexiveRecover (hE : Function.Surjective (J : E → Bidual E)) (r : Record E) : E :=
  Classical.choose (hE r.toBidual)

theorem reflexiveRecover_represents (hE : Function.Surjective (J : E → Bidual E))
    (r : Record E) : Represents r (reflexiveRecover hE r) :=
  (represents_iff _ _).mpr (Classical.choose_spec (hE r.toBidual))

theorem reflexiveRecover_unique (hE : Function.Surjective (J : E → Bidual E))
    (r : Record E) (x : E) (hx : Represents r x) : reflexiveRecover hE r = x :=
  realization_unique (reflexiveRecover_represents hE r) hx

theorem reflexiveRecover_covariant (hE : Function.Surjective (J : E → Bidual E))
    (r : Record E) (T : E →L[ℝ] E) :
    reflexiveRecover hE (transform T r) = T (reflexiveRecover hE r) :=
  reflexiveRecover_unique hE _ _ (transform_realization T (reflexiveRecover_represents hE r))

theorem reflexiveRecover_given_bound (hE : Function.Surjective (J : E → Bidual E))
    (r : Record E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (F : FinitePart E) (φ : F.val), ‖r.value F φ‖ ≤ C*‖φ‖) :
    ‖reflexiveRecover hE r‖ ≤ C :=
  realization_given_bound (reflexiveRecover_represents hE r) hC hb

theorem two_operator_stability (hE : Function.Surjective (J : E → Bidual E))
    (r s : Record E) (T U : E →L[ℝ] E) :
    ‖reflexiveRecover hE (transform T r) - reflexiveRecover hE (transform U s)‖ ≤
      ‖T‖ * recordDistance r s + ‖T-U‖ * ‖reflexiveRecover hE s‖ := by
  rw [reflexiveRecover_covariant,reflexiveRecover_covariant]
  let x := reflexiveRecover hE r
  let y := reflexiveRecover hE s
  have he : T x - U y = T (x-y) + (T-U) y := by simp
  rw [he]
  have hd : ‖x-y‖ = recordDistance r s :=
    exact_stability (reflexiveRecover_represents hE r) (reflexiveRecover_represents hE s)
  exact (norm_add_le _ _).trans (by
    simpa only [hd] using (add_le_add (T.le_opNorm (x-y)) ((T-U).le_opNorm y)))

/-- The topology here is the actual sigma(E',E) topology on WeakDual E. -/
theorem weakStar_continuous_iff_realizable (r : Record E) :
    Continuous (fun φ : WeakDual ℝ E => r.toBidual (WeakDual.toStrongDual φ)) ↔
      ∃ x : E, Represents r x := by
  constructor
  · intro h
    let z : WeakDual ℝ E →L[ℝ] ℝ :=
      { toLinearMap := r.toBidual.toLinearMap.comp WeakDual.toStrongDual.toLinearMap
        cont := h }
    obtain ⟨x,hx⟩ := (topDualPairing ℝ E).dualEmbedding_surjective z
    refine ⟨x,(represents_iff r x).mpr ?_⟩
    apply ContinuousLinearMap.ext
    intro φ
    exact congrArg (fun t : WeakDual ℝ E →L[ℝ] ℝ => t (StrongDual.toWeakDual φ)) hx
  · rintro ⟨x,hx⟩
    have he := (represents_iff r x).mp hx
    rw [← he]
    exact WeakDual.eval_continuous x

end MathGauge.RecordBidual
