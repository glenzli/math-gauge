import QuadraticPotentials
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open Filter Topology
namespace MathGauge.QuadraticConjugates
open MathGauge.QuadraticPotentials
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x "," y "⟫" => inner ℝ x y

def objective (Q : E →L[ℝ] E) (b y x : E) : ℝ := ⟪y,x⟫-quad Q b x
def conjugate (Q : E →L[ℝ] E) (b y : E) : EReal := ⨆ x : E,(objective Q b y x : EReal)

theorem complete_square (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b y v : E) (hv : Q v=y-b) (x : E) :
    objective Q b y x=⟪Q v,v⟫/2-⟪Q (x-v),x-v⟫/2 := by
  have hy : y=Q v+b := by rw [hv];abel
  have hs : ⟪Q x,v⟫=⟪Q v,x⟫ := (hQ.isSymmetric x v).trans (real_inner_comm _ _)
  rw [hy]
  simp only [objective,quad,map_sub,inner_sub_left,inner_sub_right,inner_add_left]
  rw [hs]
  ring

theorem conjugate_on_image (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b y v : E) (hv : Q v=y-b) :
    conjugate Q b y=((⟪Q v,v⟫/2 : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply EReal.coe_le_coe
    rw [complete_square Q hQ b y v hv x]
    have h := hQ.inner_nonneg_left (x-v)
    linarith
  · have h : objective Q b y v=⟪Q v,v⟫/2 := by
      rw [complete_square Q hQ b y v hv v]
      simp
    rw [← h]
    exact le_iSup (fun x : E => (objective Q b y x : EReal)) v

theorem all_optimizers (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b y v : E) (hv : Q v=y-b) (x : E) :
    (objective Q b y x : EReal)=conjugate Q b y ↔ x-v∈Q.ker := by
  rw [conjugate_on_image Q hQ b y v hv,EReal.coe_eq_coe_iff,complete_square Q hQ b y v hv x]
  change _ ↔ Q (x-v)=0
  rw [← energy_zero_iff Q hQ]
  constructor <;> intro h <;> linarith

theorem optimizer_coset (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b y v : E) (hv : Q v=y-b) :
    {x : E | (objective Q b y x : EReal)=conjugate Q b y}=
      {x | ∃ w∈Q.ker,x=v+w} := by
  ext x
  rw [Set.mem_setOf_eq,all_optimizers Q hQ b y v hv x]
  constructor
  · intro h
    exact ⟨x-v,h,by abel⟩
  · rintro ⟨w,hw,rfl⟩
    simpa using hw

theorem optimizer_unique_iff_kernel_zero (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (b y v : E) (hv : Q v=y-b) :
    (∃! x : E,(objective Q b y x : EReal)=conjugate Q b y) ↔ Q.ker=⊥ := by
  have hvopt : (objective Q b y v : EReal)=conjugate Q b y :=
    (all_optimizers Q hQ b y v hv v).mpr (by simp)
  constructor
  · rintro ⟨x,hx,hu⟩
    rw [Submodule.eq_bot_iff]
    change ∀ w∈Q.ker,w=0
    intro w hw
    have hopt : (objective Q b y (v+w) : EReal)=conjugate Q b y :=
      (all_optimizers Q hQ b y v hv (v+w)).mpr (by simpa using hw)
    have he : v+w=v := (hu (v+w) hopt).trans (hu v hvopt).symm
    simpa using (add_left_cancel (show v+w=v+0 by simpa using he))
  · intro hker
    refine ⟨v,hvopt,?_⟩
    intro x hx
    have h := (all_optimizers Q hQ b y v hv x).mp hx
    rw [hker,Submodule.mem_bot] at h
    exact sub_eq_zero.mp h

theorem value_independent (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b y v w : E)
    (hv : Q v=y-b) (hw : Q w=y-b) : ⟪Q v,v⟫/2=⟪Q w,w⟫/2 :=
  EReal.coe_injective ((conjugate_on_image Q hQ b y v hv).symm.trans
    (conjugate_on_image Q hQ b y w hw))

theorem conjugate_unbounded_direction (Q : E →L[ℝ] E) (b y w : E)
    (hw : Q w=0) (hc : ⟪y-b,w⟫≠0) : conjugate Q b y=⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  let t : ℝ := (M+1)/⟪y-b,w⟫
  have he : objective Q b y (t • w)=M+1 := by
    simp only [objective,quad,map_smul,hw,smul_zero,inner_zero_left,zero_div,zero_add,
      inner_smul_right,mul_zero,zero_div,zero_add]
    rw [← mul_sub,← inner_sub_left]
    exact div_mul_cancel₀ _ hc
  apply lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (show M<M+1 by linarith))
  rw [← he]
  exact le_iSup (fun x : E => (objective Q b y x : EReal)) (t • w)

theorem kernel_witness [FiniteDimensional ℝ E] (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (z : E) (hz : z∉Q.range) : ∃ w : E,Q w=0 ∧ ⟪z,w⟫≠0 := by
  by_contra hn
  push_neg at hn
  have he : Q.kerᗮ=Q.range := by
    rw [← hQ.isSymmetric.orthogonal_range,Submodule.orthogonal_orthogonal]
  apply hz
  rw [← he,Submodule.mem_orthogonal]
  intro w hw
  rw [real_inner_comm]
  exact hn w hw

theorem conjugate_off_image [FiniteDimensional ℝ E] (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (b y : E) (hy : y-b∉Q.range) : conjugate Q b y=⊤ := by
  obtain ⟨w,hw,hc⟩ := kernel_witness Q hQ (y-b) hy
  exact conjugate_unbounded_direction Q b y w hw hc

theorem finite_domain [FiniteDimensional ℝ E] (Q : E →L[ℝ] E) (hQ : Q.IsPositive) (b y : E) :
    conjugate Q b y≠⊤ ↔ y-b∈Q.range := by
  constructor
  · intro h
    by_contra hn
    exact h (conjugate_off_image Q hQ b y hn)
  · rintro ⟨v,hv⟩
    rw [conjugate_on_image Q hQ b y v hv]
    exact EReal.coe_ne_top _

/-- The zero quadratic is an actual singular example: its zero dual fiber
has every vector as optimizer, while every nonzero dual vector is unbounded. -/
theorem zero_example [FiniteDimensional ℝ E] (y : E) (hy : y≠0) :
    conjugate (0 : E →L[ℝ] E) 0 y=⊤ ∧
    ∀ x : E,(objective (0 : E →L[ℝ] E) 0 0 x : EReal)=
      conjugate (0 : E →L[ℝ] E) 0 0 := by
  constructor
  · apply conjugate_off_image 0 (by simp) 0 y
    simpa using hy
  · intro x
    simp [conjugate,objective,quad,inner_zero_left]

theorem singular_scalar_counterexample :
    conjugate (0 : ℝ →L[ℝ] ℝ) 0 1=⊤ ∧
    ∀ x : ℝ,(objective (0 : ℝ →L[ℝ] ℝ) 0 0 x : EReal)=
      conjugate (0 : ℝ →L[ℝ] ℝ) 0 0 := zero_example (1 : ℝ) one_ne_zero

section PositiveDefinite
variable [FiniteDimensional ℝ E]

def inverseEquiv (Q : E →L[ℝ] E) (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective Q.toLinearMap (by
    have hi : Function.Injective Q := by
      apply (LinearMap.ker_eq_bot).mp
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hn
      have h := hp x hn
      have he : Q x=0 := hx
      simp only [he,inner_zero_left] at h
      exact lt_irrefl _ h
    exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩)

def inverseOperator (Q : E →L[ℝ] E) (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) : E →L[ℝ] E :=
  (inverseEquiv Q hp).symm.toLinearMap.toContinuousLinearMap

@[simp] theorem apply_inverse (Q : E →L[ℝ] E) (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (z : E) :
    Q (inverseOperator Q hp z)=z := (inverseEquiv Q hp).apply_symm_apply z
@[simp] theorem inverse_apply (Q : E →L[ℝ] E) (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (z : E) :
    inverseOperator Q hp (Q z)=z := (inverseEquiv Q hp).symm_apply_apply z

def dualValue (Q : E →L[ℝ] E) (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b y : E) : ℝ :=
  ⟪y-b,inverseOperator Q hp (y-b)⟫/2

theorem conjugate_positive (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b y : E) :
    conjugate Q b y=(dualValue Q hp b y : EReal) := by
  rw [conjugate_on_image Q hQ b y (inverseOperator Q hp (y-b)) (apply_inverse Q hp (y-b))]
  simp [dualValue]

theorem unique_optimizer (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b y x : E) :
    (objective Q b y x : EReal)=conjugate Q b y ↔ x=inverseOperator Q hp (y-b) := by
  rw [all_optimizers Q hQ b y (inverseOperator Q hp (y-b)) (apply_inverse Q hp (y-b)) x]
  change Q (x-inverseOperator Q hp (y-b))=0 ↔ _
  have hi : Function.Injective Q := (inverseEquiv Q hp).injective
  rw [← map_zero Q,hi.eq_iff,sub_eq_zero]

theorem fenchel_gap (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b x y : E) :
    quad Q b x+dualValue Q hp b y-⟪y,x⟫=
      ⟪Q (x-inverseOperator Q hp (y-b)),x-inverseOperator Q hp (y-b)⟫/2 := by
  have h := complete_square Q hQ b y (inverseOperator Q hp (y-b)) (apply_inverse Q hp (y-b)) x
  simp only [objective,apply_inverse] at h
  unfold dualValue
  linarith

theorem fenchel_equality (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b x y : E) :
    quad Q b x+dualValue Q hp b y=⟪y,x⟫ ↔ y=Q x+b := by
  have he : quad Q b x+dualValue Q hp b y=⟪y,x⟫ ↔
      (objective Q b y x : EReal)=conjugate Q b y := by
    rw [conjugate_positive Q hQ hp b y,EReal.coe_eq_coe_iff]
    unfold objective
    constructor <;> intro h <;> linarith
  rw [he,unique_optimizer Q hQ hp b y x]
  constructor
  · intro hx
    have h := congrArg Q hx
    rw [apply_inverse] at h
    rw [h]
    abel
  · intro hy
    rw [hy,add_sub_cancel_right,inverse_apply]

theorem dualValue_hasFDerivAt (Q : E →L[ℝ] E) (hQ : Q.IsPositive)
    (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b y : E) :
    HasFDerivAt (dualValue Q hp b) (innerSL ℝ (inverseOperator Q hp (y-b))) y := by
  let R := inverseOperator Q hp
  have he : dualValue Q hp b=fun z => quad Q 0 (R (z-b)) := by
    funext z
    simp [dualValue,quad,R]
  rw [he]
  have hd : HasFDerivAt (fun z => R (z-b)) R y := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using
      R.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const b)
  convert (quad_hasFDerivAt Q hQ 0 (R (y-b))).comp y hd using 1
  ext z
  change ⟪R (y-b),z⟫=⟪Q (R (y-b))+0,R z⟫
  rw [add_zero]
  have hs : ⟪Q (R (y-b)),R z⟫=⟪R (y-b),Q (R z)⟫ := hQ.isSymmetric _ _
  rw [hs]
  change _=⟪R (y-b),Q (inverseOperator Q hp z)⟫
  rw [apply_inverse]

theorem gradient_inverse_relations (Q : E →L[ℝ] E)
    (hp : ∀ x : E,x≠0 → 0<⟪Q x,x⟫) (b x y : E) :
    inverseOperator Q hp ((Q x+b)-b)=x ∧
      Q (inverseOperator Q hp (y-b))+b=y := by
  simp

end PositiveDefinite
end MathGauge.QuadraticConjugates
