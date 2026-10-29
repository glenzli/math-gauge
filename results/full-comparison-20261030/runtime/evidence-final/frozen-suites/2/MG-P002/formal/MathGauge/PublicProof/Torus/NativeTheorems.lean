import MathGauge.PublicProof.Torus.NativeAnalysis
import MathGauge.PublicProof.Torus.Classification

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

lemma transportCover_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (α : ℝ) :
    ContDiff ℝ ∞ (transportCover α f) :=
  (ContinuousLinearMap.apply ℝ ℂ (α, 1)).contDiff.comp (hf.fderiv_right (by simp))

lemma transportCover_periodic {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (α : ℝ) : UnitPeriodic (transportCover α f) := by
  have ha := rapid_coefficient hf hp
  have he : series (coefficient f) = f := funext (series_coefficient hf hp)
  have hd := transportCover_series α ha
  rw [he] at hd
  rw [hd]
  intro x k
  exact series_periodic _ x k.1 k.2

/-- The raw intrinsic derivative is a genuine continuous smooth function on the torus. -/
def nativeTransport (α : ℝ) (u : C(Torus2, ℂ)) (hu : Smooth u) : C(Torus2, ℂ) :=
  ofCover (transportCover α (coverOf u))
    (transportCover_smooth ((smooth_iff_coverOf u).mp hu) α)
    (transportCover_periodic ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u) α)

lemma cover_nativeTransport (α : ℝ) (u : C(Torus2, ℂ)) (hu : Smooth u) :
    coverOf (nativeTransport α u hu) = transportCover α (coverOf u) := coverOf_ofCover _ _ _

lemma nativeTransport_eq (α : ℝ) (u : C(Torus2, ℂ)) (hu : Smooth u) :
    (nativeTransport α u hu : Torus2 → ℂ) = transport α u := by
  funext y
  obtain ⟨x, rfl⟩ := pairProject_surjective y
  rw [← coverOf_apply, cover_nativeTransport]
  exact (transport_native_cover u hu α x).symm

lemma nativeTransport_smooth (α : ℝ) (u : C(Torus2, ℂ)) (hu : Smooth u) :
    Smooth (nativeTransport α u hu) := ofCover_smooth _ _ _

lemma nativeTransport_meanZero (α : ℝ) (u : C(Torus2, ℂ)) (hu : Smooth u) :
    MeanZero (nativeTransport α u hu) := by
  rw [native_meanZero_iff_cover, cover_nativeTransport,
    coefficient_transportCover ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u)]
  simp [pairDivisor]

def NativeSmoothSurjective (α : ℝ) : Prop :=
  ∀ F : C(Torus2, ℂ), Smooth F → MeanZero F →
    ∃ u : C(Torus2, ℂ), Smooth u ∧ MeanZero u ∧ (∀ y, transport α u y = F y)

/-- The complete quantifiers of smooth solvability are transported in both directions. -/
lemma nativeSurjective_iff_cover (α : ℝ) : NativeSmoothSurjective α ↔ SmoothSurjective α := by
  constructor
  · intro h f hf hp hf0
    let F := ofCover f hf hp
    have hF : Smooth F := ofCover_smooth f hf hp
    have hFm : MeanZero F := by rw [native_meanZero_iff_cover, coverOf_ofCover]; exact hf0
    obtain ⟨u, hu, hum, hsol⟩ := h F hF hFm
    refine ⟨coverOf u, (smooth_iff_coverOf u).mp hu, coverOf_periodic u,
      (native_meanZero_iff_cover u).mp hum, ?_⟩
    funext x
    rw [← transport_native_cover u hu α x, hsol, ← coverOf_apply, coverOf_ofCover]
  · intro h F hF hFm
    obtain ⟨g, hg, hgp, hg0, hsol⟩ := h (coverOf F) ((smooth_iff_coverOf F).mp hF)
      (coverOf_periodic F) ((native_meanZero_iff_cover F).mp hFm)
    let u := ofCover g hg hgp
    have hu : Smooth u := ofCover_smooth g hg hgp
    refine ⟨u, hu, ?_, ?_⟩
    · rw [native_meanZero_iff_cover, coverOf_ofCover]
      exact hg0
    · intro y
      obtain ⟨x, rfl⟩ := pairProject_surjective y
      rw [transport_native_cover u hu, coverOf_ofCover, hsol, coverOf_apply]

/-- The task's general-irrational smooth-surjectivity classification, now on `T²` itself. -/
theorem native_smoothSurjective_iff {α : ℝ} (hα : Irrational α) :
    NativeSmoothSurjective α ↔ ∃ s : ℝ, 0 ≤ s ∧ HasDivisorBound α s := by
  rw [nativeSurjective_iff_cover, smoothSurjective_iff_polynomialBound hα,
    polynomial_bound_iff_exists_real]
  simp_rw [pair_bound_iff_native]

/-- Actual zero-mean torus solutions are unique for every irrational direction. -/
theorem native_solution_unique {α : ℝ} (hα : Irrational α)
    {u v : C(Torus2, ℂ)} (hu : Smooth u) (hv : Smooth v) (hum : MeanZero u) (hvm : MeanZero v)
    (he : ∀ y, transport α u y = transport α v y) : u = v := by
  apply coverOf_injective
  apply transportCover_injective_zeroMean hα ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u)
    ((smooth_iff_coverOf v).mp hv) (coverOf_periodic v)
    ((native_meanZero_iff_cover u).mp hum) ((native_meanZero_iff_cover v).mp hvm)
  funext x
  rw [← transport_native_cover u hu, ← transport_native_cover v hv]
  exact he _

def NativeSobolevEstimates (α s : ℝ) : Prop :=
  ∀ r : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : C(Torus2, ℂ), Smooth u → MeanZero u →
    nativeHNorm r u ≤ C * nativeHNorm (r + s) (transport α u)

lemma nativeSobolev_iff_cover (α s : ℝ) : NativeSobolevEstimates α s ↔ HasSobolevEstimates α s := by
  constructor
  · intro h r
    obtain ⟨C, hC, hb⟩ := h r
    refine ⟨C, hC, ?_⟩
    intro f hf hp hf0
    let u := ofCover f hf hp
    have hu : Smooth u := ofCover_smooth f hf hp
    have hum : MeanZero u := by rw [native_meanZero_iff_cover, coverOf_ofCover]; exact hf0
    have he := hb u hu hum
    rw [← nativeTransport_eq α u hu, nativeHNorm_eq_cover, nativeHNorm_eq_cover,
      cover_nativeTransport, coverOf_ofCover] at he
    exact he
  · intro h r
    obtain ⟨C, hC, hb⟩ := h r
    refine ⟨C, hC, ?_⟩
    intro u hu hum
    rw [← nativeTransport_eq α u hu, nativeHNorm_eq_cover, nativeHNorm_eq_cover, cover_nativeTransport]
    exact hb (coverOf u) ((smooth_iff_coverOf u).mp hu) (coverOf_periodic u)
      ((native_meanZero_iff_cover u).mp hum)

/-- All real-order Sobolev estimates on actual smooth zero-mean torus functions,
with their exact endpoint criterion. -/
theorem native_sobolev_iff (α s : ℝ) : NativeSobolevEstimates α s ↔ HasDivisorBound α s := by
  rw [nativeSobolev_iff_cover, sobolev_iff_divisor_bound, pair_bound_iff_native]

theorem native_quadratic_sobolev_iff {s : ℝ} (hs : 0 ≤ s) :
    NativeSobolevEstimates quadraticDirection s ↔ 1 ≤ s := by
  rw [native_sobolev_iff]
  exact quadratic_divisor_bound_iff hs

end MathGauge.PublicProof.Torus
