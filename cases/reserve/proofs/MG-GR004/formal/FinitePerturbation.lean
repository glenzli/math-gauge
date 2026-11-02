import FiniteGreen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace MathGauge.HilbertFinite
open HilbertCriteria HilbertPerturbation
universe u
variable (H : ℕ → Type u)
variable [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
variable (d d' : ∀ n, H n →L[ℂ] H (n+1)) (r : ℕ)
variable (c δ : ℕ → ℝ)

def perturbationEta (n : ℕ) : ℝ :=
  2*‖d n‖*δ n+(δ n)^2+2*‖d (n+1)‖*δ (n+1)+(δ (n+1))^2

variable (hc : ∀ n≤r, 0<c n)
variable (hL : ∀ n≤r, ∀ x, c n*‖x‖^2≤Complex.re (inner ℂ (laplacian (d n) (d (n+1)) x) x))
variable (hδ : ∀ n≤r+1, ‖d' n-d n‖≤δ n)
variable (hη : ∀ n≤r, perturbationEta H d δ n<c n)

include hη in
theorem perturbed_gap (n : ℕ) (hn : n≤r) : 0<c n-perturbationEta H d δ n :=
  sub_pos.mpr (hη n hn)

include hδ in
theorem finite_laplacian_perturbation (n : ℕ) (hn : n≤r) :
    ‖laplacian (d' n) (d' (n+1))-laplacian (d n) (d (n+1))‖≤perturbationEta H d δ n :=
  laplacian_perturbation_bound _ _ _ _ (hδ n (by omega)) (hδ (n+1) (by omega))

include hL hδ in
theorem perturbed_energy (n : ℕ) (hn : n≤r) :
    ∀ x, (c n-perturbationEta H d δ n)*‖x‖^2≤
      Complex.re (inner ℂ (laplacian (d' n) (d' (n+1)) x) x) :=
  coercive_perturbation _ _ (hL n hn) (finite_laplacian_perturbation H d d' r δ hδ n hn)

def perturbedGreen : ∀ n, H (n+1) →L[ℂ] H (n+1) :=
  finiteGreen H d' r (fun n => c n-perturbationEta H d δ n)
    (perturbed_gap H d r c δ hη) (perturbed_energy H d d' r c δ hL hδ)

theorem perturbedGreen_right (n : ℕ) (hn : n≤r) :
    (laplacian (d' n) (d' (n+1))).comp (perturbedGreen H d d' r c δ hL hδ hη n)=1 :=
  finiteGreen_right H d' r _ _ _ n hn

theorem perturbedGreen_left (n : ℕ) (hn : n≤r) :
    (perturbedGreen H d d' r c δ hL hδ hη n).comp (laplacian (d' n) (d' (n+1)))=1 :=
  finiteGreen_left H d' r _ _ _ n hn

theorem perturbedGreen_bound (n : ℕ) (hn : n≤r) :
    ‖perturbedGreen H d d' r c δ hL hδ hη n‖≤(c n-perturbationEta H d δ n)⁻¹ :=
  finiteGreen_norm H d' r _ _ _ n hn

theorem perturbedGreen_difference (n : ℕ) (hn : n≤r) :
    ‖perturbedGreen H d d' r c δ hL hδ hη n-finiteGreen H d r c hc hL n‖≤
      perturbationEta H d δ n/(c n*(c n-perturbationEta H d δ n)) := by
  simp only [perturbedGreen,finiteGreen,dif_pos hn]
  exact Green_perturbation_norm _ _ (hc n hn) (hη n hn) (hL n hn)
    (finite_laplacian_perturbation H d d' r δ hδ n hn)

theorem perturbedSolution_difference (n : ℕ) (hn : n≤r) :
    ‖adjointSolution H d' (perturbedGreen H d d' r c δ hL hδ hη) n-
      adjointSolution H d (finiteGreen H d r c hc hL) n‖≤
      δ n/(c n-perturbationEta H d δ n)+
        ‖d n‖*perturbationEta H d δ n/(c n*(c n-perturbationEta H d δ n)) := by
  have hb := contraction_perturbation_norm (d n) (d' n)
    (finiteGreen H d r c hc hL n) (perturbedGreen H d d' r c δ hL hδ hη n)
    (hδ n (by omega)) (perturbedGreen_bound H d d' r c δ hL hδ hη n hn)
    (perturbedGreen_difference H d d' r c δ hc hL hδ hη n hn)
  simpa only [adjointSolution,div_eq_mul_inv,mul_assoc] using hb

variable [Subsingleton (H 0)] [Subsingleton (H (r+2))]

theorem perturbedSolution_contraction
    (hd' : ∀ n≤r, (d' (n+1)).comp (d' n)=0) :
    ∀ n≤r, (d' n).comp (adjointSolution H d' (perturbedGreen H d d' r c δ hL hδ hη) n)+
      (adjointSolution H d' (perturbedGreen H d d' r c δ hL hδ hη) (n+1)).comp (d' (n+1))=1 :=
  finite_adjoint_formula H d' r hd' _
    (perturbedGreen_right H d d' r c δ hL hδ hη)
    (perturbedGreen_left H d d' r c δ hL hδ hη)

end MathGauge.HilbertFinite
