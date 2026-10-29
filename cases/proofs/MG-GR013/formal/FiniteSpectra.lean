import StrongPolynomials
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Topology
namespace MathGauge.FiniteSpectra
open Polynomial
universe u

/-- Small value of a monic polynomial forces some root nearby; no ordering of
roots or continuity of a preselected eigenbasis is assumed. -/
theorem root_near (p : ℂ[X]) (hp : p.Monic) (z : ℂ) (ε : ℝ) (hε : 0<ε)
    (he : ‖p.eval z‖<ε^p.natDegree) : ∃ w∈p.roots,‖w-z‖<ε := by
  by_contra hn
  push_neg at hn
  have hprod := Multiset.prod_map_le_prod_map₀ (fun _ : ℂ => ε) (fun w => ‖z-w‖)
    (s := p.roots) (fun _ _ => hε.le) (fun w hw => by simpa [norm_sub_rev] using hn w hw)
  have hnorm : ‖p.eval z‖=(p.roots.map (fun w => ‖z-w‖)).prod := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp]
    simpa only [Multiset.map_map,Function.comp_def] using
      map_multiset_prod (normHom : ℂ →*₀ ℝ) (p.roots.map (fun w => z-w))
  rw [← hnorm] at hprod
  have hcard := (IsAlgClosed.splits p).natDegree_eq_card_roots
  have heq : (p.roots.map (fun _ : ℂ => ε)).prod=ε^p.natDegree := by
    simp [Multiset.map_const,← hcard]
  rw [heq] at hprod
  exact (not_lt_of_ge hprod) he

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Evaluation of the characteristic polynomial is continuous because it is
the determinant of the actual coordinate matrix λI−A. -/
theorem continuous_charpoly_eval (z : ℂ) :
    Continuous (fun A : E →L[ℂ] E => A.toLinearMap.charpoly.eval z) := by
  let b := Module.finBasis ℂ E
  have hM : Continuous (fun A : E →L[ℂ] E => LinearMap.toMatrix b b A.toLinearMap) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa only [LinearMap.toMatrix_apply,Module.Basis.coord_apply] using
      (b.coord i).continuous_of_finiteDimensional.comp (ContinuousLinearMap.apply ℂ E (b j)).continuous
  have hc : Continuous (fun A : E →L[ℂ] E => Matrix.scalar (Fin (Module.finrank ℂ E)) z-LinearMap.toMatrix b b A.toLinearMap) := continuous_const.sub hM
  have hd := hc.matrix_det
  convert hd using 1
  funext A
  rw [← A.toLinearMap.charpoly_toMatrix b,Matrix.eval_charpoly]

/-- Full-sequence nearest-root choice. Every index has a root since the common
finite dimension is positive; the finitely many early indices are included. -/
theorem spectral_recovery [Nontrivial E] (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hT : Tendsto T atTop (𝓝 A)) (z : ℂ) (hz : z∈spectrum ℂ A) :
    ∃ w : ℕ → ℂ,(∀ n,w n∈spectrum ℂ (T n)) ∧ Tendsto w atTop (𝓝 z) := by
  have hz0 : A.toLinearMap.charpoly.eval z=0 := by
    rw [ContinuousLinearMap.spectrum_eq,Module.End.mem_spectrum_iff_isRoot_charpoly] at hz
    exact hz
  have hroot (n : ℕ) : (T n).toLinearMap.charpoly.roots≠0 := by
    have hd := (IsAlgClosed.splits (T n).toLinearMap.charpoly).natDegree_eq_card_roots
    rw [LinearMap.charpoly_natDegree] at hd
    intro hh
    rw [hh,Multiset.card_zero] at hd
    exact (ne_of_gt (Module.finrank_pos (R := ℂ) (M := E))) hd
  choose w hw hmin using fun n => Multiset.exists_min_image (fun x : ℂ => ‖x-z‖) (hroot n)
  refine ⟨w,?_,?_⟩
  · intro n
    rw [ContinuousLinearMap.spectrum_eq,Module.End.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots (T n).toLinearMap.charpoly_monic.ne_zero).1 (hw n)
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hlim : Tendsto (fun n => ‖(T n).toLinearMap.charpoly.eval z‖) atTop (𝓝 0) := by
      simpa [hz0] using ((continuous_charpoly_eval (E := E) z).tendsto A |>.comp hT).norm
    have he := hlim.eventually (eventually_lt_nhds (pow_pos hε (Module.finrank ℂ E)))
    obtain ⟨N,hN⟩ := eventually_atTop.1 he
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨v,hv,hnear⟩ := root_near (T n).toLinearMap.charpoly (T n).toLinearMap.charpoly_monic z ε hε
      (by simpa [LinearMap.charpoly_natDegree] using hN n hn)
    rw [dist_eq_norm]
    exact (hmin n v hv).trans_lt hnear

theorem strong_finite_spectral_recovery [Nontrivial E]
    (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hs : ∀ x,Tendsto (fun n => T n x) atTop (𝓝 (A x))) (z : ℂ) (hz : z∈spectrum ℂ A) :
    Tendsto T atTop (𝓝 A) ∧
    ∃ w : ℕ → ℂ,(∀ n,w n∈spectrum ℂ (T n)) ∧ Tendsto w atTop (𝓝 z) := by
  have ht := MathGauge.StrongPolynomials.finite_dimensional_norm_convergence T A hs
  exact ⟨ht,spectral_recovery T A ht z hz⟩

end MathGauge.FiniteSpectra
