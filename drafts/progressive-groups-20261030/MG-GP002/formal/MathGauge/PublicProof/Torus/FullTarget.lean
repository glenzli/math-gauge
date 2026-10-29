import MathGauge.PublicProof.Torus.NativeTheorems

/-! Final theorems on actual smooth zero-mean functions on the unit two-torus.
All analytical bridges used below are proved in the imported project closure. -/

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

/-- The actual normalized inverse for the task's specified quadratic direction. -/
def nativeFixedInverse (F : C(Torus2, ℂ)) (hF : Smooth F) : C(Torus2, ℂ) :=
  ofCover (directionalInverse .temporal (coefficient (coverOf F)))
    (contDiff_directionalInverse .temporal (rapid_coefficient ((smooth_iff_coverOf F).mp hF) (coverOf_periodic F)))
    (fun x k => series_periodic _ x k.1 k.2)

lemma nativeFixedInverse_smooth (F : C(Torus2, ℂ)) (hF : Smooth F) :
    Smooth (nativeFixedInverse F hF) := ofCover_smooth _ _ _

lemma cover_nativeFixedInverse (F : C(Torus2, ℂ)) (hF : Smooth F) :
    coverOf (nativeFixedInverse F hF) = directionalInverse .temporal (coefficient (coverOf F)) :=
  coverOf_ofCover _ _ _

lemma nativeFixedInverse_meanZero (F : C(Torus2, ℂ)) (hF : Smooth F) :
    MeanZero (nativeFixedInverse F hF) := by
  rw [native_meanZero_iff_cover, cover_nativeFixedInverse]
  have ha := rapid_coefficient ((smooth_iff_coverOf F).mp hF) (coverOf_periodic F)
  change coefficient (series (inverseCoeff .temporal (coefficient (coverOf F)))) 0 = 0
  rw [coefficient_series_eq (ha.inverseCoeff .temporal)]
  simp [inverseCoeff, multiplier, symbol, Borrowed.DiophantineGraph.timeSymbol,
    Borrowed.DiophantineGraph.quadraticForm]

/-- The constructed torus inverse solves the actual directional differential equation. -/
theorem nativeFixedInverse_solves (F : C(Torus2, ℂ)) (hF : Smooth F) (hFm : MeanZero F) :
    ∀ y, transport quadraticDirection (nativeFixedInverse F hF) y = F y := by
  intro y
  obtain ⟨x, rfl⟩ := pairProject_surjective y
  rw [transport_native_cover _ (nativeFixedInverse_smooth F hF), cover_nativeFixedInverse]
  have hm : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, coverOf F (x, y)) = 0 := by
    rw [← coefficient_zero_eq_integral]
    exact (native_meanZero_iff_cover F).mp hFm
  exact inverse_solves_smooth_periodic .temporal ((smooth_iff_coverOf F).mp hF)
    (coverOf_periodic F) hm x

/-- The final `C^(m+4) → C^m` estimate with exactly the task's norms.
The constant depends only on `m`, is a finite real number, and is independent of `F`. -/
theorem native_fixed_Cm_bound (m : ℕ) (F : C(Torus2, ℂ)) (hF : Smooth F) :
    nativeCNorm m (nativeFixedInverse F hF) ≤ fourConstant m * nativeCNorm (m + 4) F := by
  rw [nativeCNorm_eq_cover _ (nativeFixedInverse_smooth F hF), nativeCNorm_eq_cover F hF,
    cover_nativeFixedInverse]
  exact cmNormCover_inverse_bound_four ((smooth_iff_coverOf F).mp hF) (coverOf_periodic F) .temporal m

/-- An explicit solution, its uniqueness, and every requested `C^m` estimate. -/
theorem native_fixed_full_solution (F : C(Torus2, ℂ)) (hF : Smooth F) (hFm : MeanZero F) :
    Smooth (nativeFixedInverse F hF) ∧ MeanZero (nativeFixedInverse F hF) ∧
    (∀ y, transport quadraticDirection (nativeFixedInverse F hF) y = F y) ∧
    (∀ u : C(Torus2, ℂ), Smooth u → MeanZero u →
      (∀ y, transport quadraticDirection u y = F y) → u = nativeFixedInverse F hF) ∧
    ∀ m : ℕ, nativeCNorm m (nativeFixedInverse F hF) ≤ fourConstant m * nativeCNorm (m + 4) F := by
  refine ⟨nativeFixedInverse_smooth F hF, nativeFixedInverse_meanZero F hF,
    nativeFixedInverse_solves F hF hFm, ?_, fun m => native_fixed_Cm_bound m F hF⟩
  intro u hu hum he
  apply native_solution_unique quadraticDirection_irrational hu (nativeFixedInverse_smooth F hF)
    hum (nativeFixedInverse_meanZero F hF)
  intro y
  rw [he, nativeFixedInverse_solves F hF hFm]

/-- All real Sobolev sums in the final native-torus statements genuinely converge. -/
theorem native_sobolev_summable (u : C(Torus2, ℂ)) (hu : Smooth u) (r : ℝ) :
    Summable (fun k : Frequency => weight k ^ (2 * r) * ‖coeff u k‖ ^ 2) := by
  have hs := summable_energyTerm r (rapid_coefficient ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u))
  have h := frequencyEquiv.summable_iff.mpr hs
  convert h using 1
  funext k
  dsimp only [Function.comp_apply]
  rw [energyTerm, pairWeight_frequencyEquiv, native_coeff_eq_cover]
  rfl

/-- The native `C^m` supremum is bounded for every smooth input. -/
theorem native_CMValues_bounded (u : C(Torus2, ℂ)) (hu : Smooth u) (m : ℕ) :
    BddAbove (nativeCMValues m u) := by
  refine ⟨cmNormCover m (coverOf u), ?_⟩
  rintro v ⟨a, b, hab, y, rfl⟩
  obtain ⟨x, rfl⟩ := pairProject_surjective y
  rw [mixedDerivative_cover u hu]
  exact orderedDerivative_le_cmNorm ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u) hab x

end MathGauge.PublicProof.Torus
