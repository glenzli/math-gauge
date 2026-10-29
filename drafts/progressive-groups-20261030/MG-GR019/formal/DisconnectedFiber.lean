import ProductAlgebras

noncomputable section
open Set Function Topology
namespace MathGauge.DisconnectedFiber
open MathGauge.ObservationTopology

abbrev X := Set.Icc (-1 : ℝ) 1
abbrev Y := Set.Icc (0 : ℝ) 1

def fold (x : X) : Y := ⟨x.val^2,by
  constructor
  · positivity
  · have h₁ : (-1 : ℝ) ≤ x.val := x.property.1
    have h₂ : x.val ≤ 1 := x.property.2
    nlinarith⟩

theorem fold_continuous : Continuous fold :=
  (continuous_subtype_val.pow 2).subtype_mk _

theorem fold_surjective : Surjective fold := by
  intro y
  refine ⟨⟨Real.sqrt y.val,?_⟩,?_⟩
  · constructor
    · have := Real.sqrt_nonneg y.val
      linarith
    · exact (Real.sqrt_le_one).2 y.property.2
  · apply Subtype.ext
    exact Real.sq_sqrt y.property.1

instance : ConnectedSpace X := isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))
instance : ConnectedSpace Y := isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))

theorem fold_component_bijective : Bijective (componentMap fold fold_continuous) := by
  constructor
  · intro a b _
    exact Subsingleton.elim a b
  · intro a
    obtain ⟨y,rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨x,rfl⟩ := fold_surjective y
    exact ⟨ConnectedComponents.mk x,rfl⟩

def quotientHomeomorph : ObservationImage X ≃ₜ ObservationImage Y :=
  (componentObservationHomeomorph X).symm.trans
    (((Equiv.ofBijective (componentMap fold fold_continuous) fold_component_bijective).toHomeomorphOfContinuousClosed
      (componentMap_continuous fold fold_continuous)
      (componentMap_continuous fold fold_continuous).isClosedMap).trans
      (componentObservationHomeomorph Y))

theorem quotient_natural (x : X) :
    quotientHomeomorph (observationMap X x)=observationMap Y (fold x) := by
  change (componentObservationHomeomorph Y)
    (componentMap fold fold_continuous
      ((componentObservationHomeomorph X).symm
        ((componentObservationHomeomorph X) (ConnectedComponents.mk x))))=_
  rw [Homeomorph.symm_apply_apply]
  rfl

def one : Y := ⟨1,by norm_num⟩
def left : X := ⟨-1,by norm_num⟩
def right : X := ⟨1,by norm_num⟩

theorem fiber_not_connected : ¬ IsConnected (fold ⁻¹' {one}) := by
  intro h
  have hp := h.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn
  have hl : (-1 : ℝ) ∈ Subtype.val '' (fold ⁻¹' {one}) := by
    refine ⟨left,?_,rfl⟩
    change fold left=one
    apply Subtype.ext
    norm_num [fold,left,one]
  have hr : (1 : ℝ) ∈ Subtype.val '' (fold ⁻¹' {one}) := by
    refine ⟨right,?_,rfl⟩
    change fold right=one
    apply Subtype.ext
    norm_num [fold,right,one]
  obtain ⟨x,hx,hzero⟩ := hp.Icc_subset hl hr (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)
  have he := congrArg Subtype.val (show fold x=one from hx)
  change x.val^2=1 at he
  rw [hzero] at he
  norm_num at he

/-- A concrete continuous surjection of compact Hausdorff spaces whose
induced finite-observation map is a homeomorphism and has a disconnected fiber. -/
theorem counterexample : Continuous fold ∧ Surjective fold ∧
    (∀ x,quotientHomeomorph (observationMap X x)=observationMap Y (fold x)) ∧
    ¬ IsConnected (fold ⁻¹' {one}) :=
  ⟨fold_continuous,fold_surjective,quotient_natural,fiber_not_connected⟩

end MathGauge.DisconnectedFiber
