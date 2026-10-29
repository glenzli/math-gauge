import CyclicPotential
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Filter Topology
namespace MathGauge.QuadraticPotentials
open MathGauge.CyclicPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x "," y "⟫" => inner ℝ x y

def quad (Q : E →L[ℝ] E) (b x : E) : ℝ := ⟪Q x,x⟫/2+⟪b,x⟫
def grad (Q : E →L[ℝ] E) (b x : E) : E →L[ℝ] ℝ := innerSL ℝ (Q x+b)
def graph (Q : E →L[ℝ] E) (b : E) : Set (E × (E →L[ℝ] ℝ)) := {p | p.2=grad Q b p.1}

theorem support_identity (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b x z : E) :
    quad Q b z-quad Q b x-grad Q b x (z-x)=⟪Q (z-x),z-x⟫/2 := by
  have hs : ⟪Q z,x⟫=⟪Q x,z⟫ := (hQ.isSymmetric z x).trans (real_inner_comm _ _)
  simp only [quad,grad,innerSL_apply_apply,map_sub,inner_sub_left,inner_sub_right,inner_add_left]
  rw [hs]
  ring

theorem quad_support (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b x z : E) :
    quad Q b x+grad Q b x (z-x)≤quad Q b z := by
  have h := support_identity Q hQ b x z
  have hn := hQ.inner_nonneg_left (z-x)
  linarith

theorem graph_subgradient (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b x : E) :
    Subgradient (fun z => (quad Q b z : EReal)) x (grad Q b x) :=
  ⟨quad Q b x,rfl,fun z => EReal.coe_le_coe (quad_support Q hQ b x z)⟩

theorem graph_cyclic (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b : E) : CyclicMonotone (graph Q b) := by
  intro a ha l hl
  have hp := path_le_supporting (graph Q b) (fun z => (quad Q b z : EReal))
    (fun p hp => by rw [show p.2=grad Q b p.1 from hp];exact graph_subgradient Q hQ b p.1)
    a ha l hl (quad Q b a.1) rfl a.1
  have h := EReal.coe_le_coe_iff.mp hp
  linarith

/-- A complete affine gradient support record itself forces differentiability.
The estimate is proved from the two actual supporting inequalities. -/
theorem derivative_of_supports (Q : E →L[ℝ] E) (b : E) (g : E → ℝ)
    (hg : ∀ x z,g x+grad Q b x (z-x)≤g z) (x : E) :
    HasFDerivAt g (grad Q b x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨ε/(‖Q‖+1),by positivity,?_⟩
  intro v hv
  have hvnorm : ‖v‖<ε/(‖Q‖+1) := by simpa only [Metric.mem_ball,dist_zero_right] using hv
  have hlo : 0≤g (x+v)-g x-grad Q b x v := by
    have h := hg x (x+v)
    simp only [add_sub_cancel_left] at h
    linarith
  have hup : g (x+v)-g x-grad Q b x v≤⟪Q v,v⟫ := by
    have h := hg (x+v) x
    have he : grad Q b (x+v) (x-(x+v)) = -grad Q b x v-⟪Q v,v⟫ := by
      change ⟪Q (x+v)+b,x-(x+v)⟫ = -⟪Q x+b,v⟫-⟪Q v,v⟫
      simp only [map_add,inner_add_left,inner_sub_right,inner_add_right]
      ring
    rw [he] at h
    linarith
  have hinner : ⟪Q v,v⟫≤‖Q‖*‖v‖*‖v‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (Q.le_opNorm v) (norm_nonneg _))
  have hsmall : ‖Q‖*‖v‖≤ε := by
    have h := (lt_div_iff₀ (show 0<‖Q‖+1 by positivity)).mp hvnorm
    nlinarith [norm_nonneg Q,norm_nonneg v]
  rw [Real.norm_eq_abs,abs_of_nonneg hlo]
  exact hup.trans (hinner.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)))

theorem quad_hasFDerivAt (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b x : E) :
    HasFDerivAt (quad Q b) (grad Q b x) x :=
  derivative_of_supports Q b (quad Q b) (quad_support Q hQ b) x

theorem subgradient_iff (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b x : E) (y : E →L[ℝ] ℝ) :
    Subgradient (fun z => (quad Q b z : EReal)) x y ↔ y=grad Q b x := by
  constructor
  · rintro ⟨r,hr,hy⟩
    have hr' : quad Q b x=r := EReal.coe_injective hr
    have hmin : IsLocalMin (fun z => quad Q b z-y z) x := by
      apply Filter.Eventually.of_forall
      intro z
      have h := EReal.coe_le_coe_iff.mp (hy z)
      rw [← hr',map_sub] at h
      linarith
    have hd := hmin.hasFDerivAt_eq_zero ((quad_hasFDerivAt Q hQ b x).sub y.hasFDerivAt)
    exact (sub_eq_zero.mp hd).symm
  · rintro rfl
    exact graph_subgradient Q hQ b x

theorem normalized_potential_unique (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b : E)
    (g : E → EReal) (hg0 : g 0=0) (hg : ∀ x,Subgradient g x (grad Q b x)) :
    g=fun x => (quad Q b x : EReal) := by
  have hreal (x : E) : ((g x).toReal : EReal)=g x := by
    obtain ⟨r,hr,_⟩ := hg x
    simp [hr]
  have hs (x z : E) : (g x).toReal+grad Q b x (z-x)≤(g z).toReal := by
    obtain ⟨r,hr,hs⟩ := hg x
    have hr' : (g x).toReal=r := by simp [hr]
    rw [hr']
    apply EReal.coe_le_coe_iff.mp
    rw [hreal]
    exact hs z
  have he : (fun x => (g x).toReal)=quad Q b := by
    refine eq_of_fderiv_eq
      (fun x => (derivative_of_supports Q b _ hs x).differentiableAt)
      (fun x => (quad_hasFDerivAt Q hQ b x).differentiableAt) ?_ (0 : E) ?_
    · intro x
      rw [(derivative_of_supports Q b _ hs x).fderiv,(quad_hasFDerivAt Q hQ b x).fderiv]
    · simp [hg0,quad]
  funext x
  rw [← hreal,congrFun he x]

/-- Positivity plus zero energy identifies the true kernel, including singular Q. -/
theorem energy_zero_iff (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (x : E) :
    ⟪Q x,x⟫=0 ↔ Q x=0 := by
  constructor
  · intro hx
    have hmin : IsLocalMin (quad Q 0) x := by
      apply Filter.Eventually.of_forall
      intro z
      simp only [quad,inner_zero_left,hx,zero_div,zero_add,add_zero]
      exact div_nonneg (hQ.inner_nonneg_left z) (by norm_num)
    have h := hmin.hasFDerivAt_eq_zero (quad_hasFDerivAt Q hQ 0 x)
    have he := congrArg (fun L : E →L[ℝ] ℝ => L (Q x)) h
    simpa [grad] using he
  · rintro hx
    simp [hx]

end MathGauge.QuadraticPotentials
