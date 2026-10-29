import MathGauge.GP002.FiniteBand

noncomputable section
namespace MathGauge.GP002
open MathGauge.PublicProof.Torus
open MathGauge.PublicProof.Torus.Borrowed.TorusInverse
open MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
open scoped Topology ContDiff

theorem rapid_sub {a b : PairFrequency → ℂ} (ha : Rapid a) (hb : Rapid b) : Rapid (a-b) := by
  intro p
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _) (norm_nonneg _))
    _ ((ha p).add (hb p))
  intro k
  dsimp only [Pi.sub_apply]
  calc
    _ ≤ Borrowed.TorusInverse.weight k ^p * (‖a k‖+‖b k‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg (Borrowed.TorusInverse.weight_pos k).le _)
    _ = _ := by ring

theorem series_sub {a b : PairFrequency → ℂ} (ha : Rapid a) (hb : Rapid b) :
    series (a-b) = series a - series b := by
  funext x
  unfold series
  simp only [Pi.sub_apply,sub_mul]
  exact (summable_terms ha x).tsum_sub (summable_terms hb x)

def nativeSeries (a : PairFrequency → ℂ) (ha : Rapid a) : C(Torus2,ℂ) :=
  ofCover (series a) (contDiff_series ha) (fun x k => series_periodic _ x k.1 k.2)

theorem nativeSeries_smooth (a : PairFrequency → ℂ) (ha : Rapid a) : Smooth (nativeSeries a ha) :=
  ofCover_smooth _ _ _

theorem nativeSeries_cover (a : PairFrequency → ℂ) (ha : Rapid a) :
    coverOf (nativeSeries a ha) = series a := coverOf_ofCover _ _ _

theorem nativeSeries_meanZero {a : PairFrequency → ℂ} (ha : Rapid a) (ha0 : a 0 = 0) :
    MeanZero (nativeSeries a ha) := by
  rw [native_meanZero_iff_cover,nativeSeries_cover,coefficient_series_eq ha,ha0]

theorem nativeSeries_norm (a : PairFrequency → ℂ) (ha : Rapid a) (r : ℝ) :
    nativeHNorm r (nativeSeries a ha) = sequenceNorm r a := by
  rw [nativeHNorm_eq_cover,nativeSeries_cover,sequenceNorm_series ha]

theorem nativeSeries_sub {a b : PairFrequency → ℂ} (ha : Rapid a) (hb : Rapid b) :
    nativeSeries (a-b) (rapid_sub ha hb) = nativeSeries a ha - nativeSeries b hb := by
  apply coverOf_injective
  rw [nativeSeries_cover,series_sub ha hb]
  rfl

theorem nativeSeries_reconstruct (u : C(Torus2,ℂ)) (hu : Smooth u) :
    nativeSeries (coefficient (coverOf u))
      (rapid_coefficient ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u)) = u := by
  apply coverOf_injective
  rw [nativeSeries_cover]
  exact funext (series_coefficient ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u))

/-- These are precisely actual finite Fourier series supported in 0<|k|≤N. -/
def NativeBand (N : ℝ) (u : C(Torus2,ℂ)) : Prop :=
  ∃ a : PairFrequency → ℂ, ∃ ha : Supported (frequencyBand N) a,
    u = nativeSeries a (rapid_of_supported ha)

theorem nativeBand_iff_fourier_support (N : ℝ) (u : C(Torus2,ℂ)) :
    NativeBand N u ↔ Smooth u ∧ Supported (frequencyBand N) (coefficient (coverOf u)) := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨nativeSeries_smooth _ _,?_⟩
    rw [nativeSeries_cover]
    simpa only [funext (coefficient_series_eq (rapid_of_supported ha))] using ha
  · rintro ⟨hu,hs⟩
    exact ⟨coefficient (coverOf u),hs,(nativeSeries_reconstruct u hu).symm⟩

def finiteNativeInverse (α N : ℝ) (F : C(Torus2,ℂ)) : C(Torus2,ℂ) :=
  nativeSeries (generalInverseCoefficients α (truncate N (coefficient (coverOf F))))
    (rapid_of_supported (inverse_supported α (truncate_supported N _)))

theorem truncate_eq_of_supported {N : ℝ} {a : PairFrequency → ℂ}
    (ha : Supported (frequencyBand N) a) : truncate N a = a := by
  funext k
  by_cases hk : k ∈ frequencyBand N
  · simp [truncate,hk]
  · simp [truncate,hk,ha k hk]

theorem finiteNativeInverse_on_series (α N : ℝ) (a : PairFrequency → ℂ)
    (ha : Supported (frequencyBand N) a) :
    finiteNativeInverse α N (nativeSeries a (rapid_of_supported ha)) =
      nativeSeries (generalInverseCoefficients α a) (rapid_of_supported (inverse_supported α ha)) := by
  unfold finiteNativeInverse
  simp only [nativeSeries_cover,funext (coefficient_series_eq (rapid_of_supported ha)),
    truncate_eq_of_supported ha]

theorem finiteNativeInverse_solves {α : ℝ} (hα : Irrational α) (N : ℝ)
    (F : C(Torus2,ℂ)) (hF : NativeBand N F) :
    NativeBand N (finiteNativeInverse α N F) ∧ Smooth (finiteNativeInverse α N F) ∧
    MeanZero (finiteNativeInverse α N F) ∧
    (∀ y, transport α (finiteNativeInverse α N F) y = F y) := by
  rcases hF with ⟨a,ha,rfl⟩
  rw [finiteNativeInverse_on_series α N a ha]
  have hi := rapid_of_supported (inverse_supported α ha)
  refine ⟨⟨_,inverse_supported α ha,rfl⟩,nativeSeries_smooth _ _,
    nativeSeries_meanZero hi (generalInverse_zero_coefficient α _),?_⟩
  intro y
  obtain ⟨x,rfl⟩ := pairProject_surjective y
  rw [transport_native_cover _ (nativeSeries_smooth _ _),nativeSeries_cover,
    (finite_inverse_solves hα N a ha).2.2.2,← coverOf_apply,nativeSeries_cover]

theorem finiteNativeInverse_norm (α N : ℝ) (hN : 1 ≤ N) (r : ℝ)
    (F : C(Torus2,ℂ)) (hF : NativeBand N F) :
    nativeHNorm r (finiteNativeInverse α N F) ≤ bandConstant α N hN * nativeHNorm r F := by
  rcases hF with ⟨a,ha,rfl⟩
  rw [finiteNativeInverse_on_series α N a ha,nativeSeries_norm,nativeSeries_norm]
  exact finite_inverse_bound α N hN r a ha

theorem finiteNativeInverse_norm_attained (α N : ℝ) (hN : 1 ≤ N) (r : ℝ) :
    ∃ F : C(Torus2,ℂ), NativeBand N F ∧ 0 < nativeHNorm r F ∧
      nativeHNorm r (finiteNativeInverse α N F) = bandConstant α N hN * nativeHNorm r F := by
  obtain ⟨a,ha,hpos,he⟩ := finite_inverse_bound_attained α N hN r
  refine ⟨nativeSeries a (rapid_of_supported ha),⟨a,ha,rfl⟩,?_,?_⟩
  · simpa only [nativeSeries_norm] using hpos
  · simpa only [finiteNativeInverse_on_series α N a ha,nativeSeries_norm] using he

theorem finiteNativeInverse_best_constant (α N : ℝ) (hN : 1 ≤ N) (r C : ℝ)
    (hC : ∀ F : C(Torus2,ℂ), NativeBand N F →
      nativeHNorm r (finiteNativeInverse α N F) ≤ C * nativeHNorm r F) :
    bandConstant α N hN ≤ C := by
  obtain ⟨F,hF,hpos,he⟩ := finiteNativeInverse_norm_attained α N hN r
  have hb := hC F hF
  rw [he] at hb
  exact (mul_le_mul_iff_left₀ hpos).mp hb

theorem nativeBand_meanZero {N : ℝ} {F : C(Torus2,ℂ)} (hF : NativeBand N F) : MeanZero F := by
  rcases hF with ⟨a,ha,rfl⟩
  exact nativeSeries_meanZero (rapid_of_supported ha) (ha 0 (by simp [mem_frequencyBand]))

theorem finiteNativeInverse_unique {α : ℝ} (hα : Irrational α) (N : ℝ)
    (F u : C(Torus2,ℂ)) (hF : NativeBand N F) (hu : NativeBand N u)
    (hsol : ∀ y, transport α u y = F y) : u = finiteNativeInverse α N F := by
  have hi := finiteNativeInverse_solves hα N F hF
  apply native_solution_unique hα ((nativeBand_iff_fourier_support N u).mp hu).1 hi.2.1
    (nativeBand_meanZero hu) hi.2.2.1
  intro y
  rw [hsol,hi.2.2.2]

theorem nativeTransport_band (α N : ℝ) (u : C(Torus2,ℂ)) (hu : NativeBand N u) :
    NativeBand N (nativeTransport α u ((nativeBand_iff_fourier_support N u).mp hu).1) := by
  rcases hu with ⟨a,ha,rfl⟩
  have hs : Supported (frequencyBand N) (transportCoefficients α a) := by
    intro k hk
    rw [transportCoefficients_formula,ha k hk,mul_zero]
  refine ⟨transportCoefficients α a,hs,?_⟩
  apply coverOf_injective
  rw [cover_nativeTransport,nativeSeries_cover,nativeSeries_cover,
    transportCover_series α (rapid_of_supported ha)]

theorem finiteNativeInverse_left_inverse {α : ℝ} (hα : Irrational α) (N : ℝ)
    (u : C(Torus2,ℂ)) (hu : NativeBand N u) :
    finiteNativeInverse α N
      (nativeTransport α u ((nativeBand_iff_fourier_support N u).mp hu).1) = u := by
  symm
  apply finiteNativeInverse_unique hα N _ u (nativeTransport_band α N u hu) hu
  intro y
  exact congrFun (nativeTransport_eq α u _).symm y

end MathGauge.GP002
