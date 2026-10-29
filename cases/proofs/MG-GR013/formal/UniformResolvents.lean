import StrongPolynomials
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
open Set Filter Topology
namespace MathGauge.UniformResolvents
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def resolvent (A : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  Ring.inverse (algebraMap ℂ (E →L[ℂ] E) z-A)

theorem resolvent_two_sided (A : E →L[ℂ] E) (z : ℂ) (hz : z∉spectrum ℂ A) :
    (algebraMap ℂ (E →L[ℂ] E) z-A)*resolvent A z=1 ∧
    resolvent A z*(algebraMap ℂ (E →L[ℂ] E) z-A)=1 := by
  obtain ⟨a,ha⟩ := spectrum.notMem_iff.mp hz
  rw [resolvent,← ha,Ring.inverse_unit]
  exact ⟨a.val_inv,a.inv_val⟩

theorem joint_resolvent_continuousAt (A : E →L[ℂ] E) (z : ℂ)
    (hz : z∉spectrum ℂ A) :
    ContinuousAt (fun p : (E →L[ℂ] E) × ℂ => resolvent p.1 p.2) (A,z) := by
  obtain ⟨a,ha⟩ := spectrum.notMem_iff.mp hz
  have hc : Continuous (fun p : (E →L[ℂ] E) × ℂ => algebraMap ℂ (E →L[ℂ] E) p.2-p.1) :=
    ((continuous_algebraMap ℂ (E →L[ℂ] E)).comp continuous_snd).sub continuous_fst
  have hi : ContinuousAt Ring.inverse (algebraMap ℂ (E →L[ℂ] E) z-A) := ha ▸ NormedRing.inverse_continuousAt a
  exact hi.comp (f := fun p : (E →L[ℂ] E) × ℂ => algebraMap ℂ (E →L[ℂ] E) p.2-p.1) hc.continuousAt

theorem uniform_resolvent_convergence (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E)
    (hT : Tendsto T atTop (𝓝 A)) (K : Set ℂ) (hK : IsCompact K)
    (hdis : ∀ z∈K,z∉spectrum ℂ A) :
    (∀ᶠ n in atTop,∀ z∈K,z∉spectrum ℂ (T n)) ∧
    TendstoUniformlyOn (fun n z => resolvent (T n) z) (resolvent A) atTop K := by
  have hunits : ∀ᶠ B in 𝓝 A,∀ z∈K,z∉spectrum ℂ B := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hc : Continuous (fun p : (E →L[ℂ] E) × ℂ => algebraMap ℂ (E →L[ℂ] E) p.2-p.1) :=
      ((continuous_algebraMap ℂ (E →L[ℂ] E)).comp continuous_snd).sub continuous_fst
    exact (hc.continuousAt.eventually (Units.isOpen.mem_nhds (spectrum.notMem_iff.mp (hdis z hz)))).mono
      (fun p hp => spectrum.notMem_iff.mpr hp)
  refine ⟨hT.eventually hunits,?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hall : ∀ᶠ B in 𝓝 A,∀ z∈K,dist (resolvent A z) (resolvent B z)<ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have h₁ := joint_resolvent_continuousAt A z (hdis z hz)
    have h₂ : ContinuousAt (fun p : (E →L[ℂ] E) × ℂ => resolvent A p.2) (A,z) := by
      have hc : Continuous (fun p : (E →L[ℂ] E) × ℂ => (A,p.2)) :=
        continuous_const.prodMk continuous_snd
      exact h₁.comp (x := (A,z)) (f := fun p : (E →L[ℂ] E) × ℂ => (A,p.2)) hc.continuousAt
    have hd := h₂.dist h₁
    have hzero : dist (resolvent A z) (resolvent A z)<ε := by simpa using hε
    exact hd.eventually (eventually_lt_nhds hzero)
  exact hT.eventually hall

end MathGauge.UniformResolvents
