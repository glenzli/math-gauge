import Ch03.Step

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-- Exercise 3.1: `x ↦ 2x-1`. -/
noncomputable def affineOp : Operator RealBase none where
  func
    | none => none
    | some x => some (2*x-1)
  preserves_bot := rfl

def binaryRealDomain : Set RealBase := {some 0, some 1}

theorem affine_fibre_and_const :
    FibSingle (fun _ : Unit => absReadDist) affineOp () (affineOp.func (some 0)) binaryRealDomain =
      binaryRealDomain ∧
    () ∈ constComponents (fun _ : Unit => absReadDist) affineOp binaryRealDomain := by
  have hc : () ∈ constComponents (fun _ : Unit => absReadDist) affineOp binaryRealDomain := by
    intro x hx y hy
    simp only [binaryRealDomain, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [affineOp, absReadDist, optionDist]
  refine ⟨?_, hc⟩
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    simp only [binaryRealDomain, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [affineOp, absReadDist, optionDist]

theorem affine_squared_fibre :
    FibSingle (fun _ : Unit => absReadDist) (operator_compose affineOp affineOp) ()
      ((operator_compose affineOp affineOp).func (some 0)) binaryRealDomain = {some 0} := by
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    simp only [binaryRealDomain, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp
    · norm_num [affineOp, operator_compose, absReadDist, optionDist] at hzero
  · intro hx
    have : x = some 0 := by simpa using hx
    subst x
    exact ⟨by simp [binaryRealDomain], by norm_num [affineOp, operator_compose, absReadDist, optionDist]⟩

theorem affine_squared_active :
    () ∈ actComponents (fun _ : Unit => absReadDist) (operator_compose affineOp affineOp) binaryRealDomain := by
  constructor
  · intro hc
    have h := hc (some 0) (by simp [binaryRealDomain]) (some 1) (by simp [binaryRealDomain])
    norm_num [affineOp, operator_compose, absReadDist, optionDist] at h
  · intro hi
    have h := hi.2 (some 0) (by simp [binaryRealDomain])
    norm_num [affineOp, operator_compose, absReadDist, optionDist] at h

/-- Exercise 3.1(ii): any operator pointwise constant on `U` has pointwise
constant self-composite there, regardless of whether the second image is the
absorbing point. -/
theorem pointwise_constant_self_compose (ψ : Operator RealBase none) (c : ℝ)
    (h : ∀ x ∈ binaryRealDomain, ψ.func x = some c) :
    ∀ x ∈ binaryRealDomain, ∀ y ∈ binaryRealDomain,
      (operator_compose ψ ψ).func x = (operator_compose ψ ψ).func y := by
  intro x hx y hy
  simp [operator_compose, h x hx, h y hy]

/-- If the second image is absorbing, the original `U` is not a legal domain
for the self-composite; otherwise the displayed constancy gives the component
and fibre conclusions whenever the domain condition is supplied. -/
theorem pointwise_constant_self_compose_domain (ψ : Operator RealBase none) (c : ℝ)
    (h : ∀ x ∈ binaryRealDomain, ψ.func x = some c) :
    (ψ.func (some c) = none → ¬ binaryRealDomain ⊆ dom (operator_compose ψ ψ)) ∧
    (binaryRealDomain ⊆ dom (operator_compose ψ ψ) →
      () ∈ constComponents (fun _ : Unit => absReadDist) (operator_compose ψ ψ) binaryRealDomain) := by
  constructor
  · intro hbot hdom
    have h0 := hdom (show some 0 ∈ binaryRealDomain by simp [binaryRealDomain])
    apply h0
    simp [operator_compose, h (some 0) (by simp [binaryRealDomain]), hbot]
  · intro hdom x hx y hy
    rw [pointwise_constant_self_compose ψ c h x hx y hy]
    exact absReadDist_extended.dist_self _

/-- Exercise 3.2(i): no input distance lies strictly between zero and a
positive pointwise annihilation radius. -/
theorem no_input_distance_in_zero_radius [Fintype I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    {U : Set X} (K : I → I → ENNReal) (hK : IsCoLipMatrix d φ U K)
    {i j : I} (hKpos : 0 < K i j) {y : X} (hy : y ∈ U) {x : X} (hx : x ∈ U) :
    d i x y ∉ Set.Ioo 0 (annihilationRadius φ (d i) (d j) y U) := by
  intro h
  have hzero := output_zero_of_dist_lt_radius d hd φ hx (by
    rw [(hd i).symm y x]
    exact h.2)
  have houtpos := (positive_colip_channels_preserve_distinguishability d φ U K hK).1
    i j hKpos x hx y hy h.1
  exact (ne_of_gt houtpos) (by
    rw [(hd j).symm (φ.func x) (φ.func y)]
    exact hzero)

/-- Exercise 3.2(ii): all input distances are zero or at least the uniform
radius. -/
theorem input_distance_zero_or_ge_uniform [Fintype I] (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (φ : Operator X bot)
    {U : Set X} (K : I → I → ENNReal) (hK : IsCoLipMatrix d φ U K)
    {i j : I} (hKpos : 0 < K i j)
    (hr : 0 < uniformAnnihilationRadiusOn φ (d i) (d j) U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformAnnihilationRadiusOn φ (d i) (d j) U ≤ d i x y := by
  by_cases hlt : d i x y < uniformAnnihilationRadiusOn φ (d i) (d j) U
  · left
    have hzero := output_zero_of_dist_lt_uniformRadius d hd φ hx hy hlt
    by_contra hne
    have hpos : 0 < d i x y := pos_iff_ne_zero.mpr hne
    have houtpos := (positive_colip_channels_preserve_distinguishability d φ U K hK).1
      i j hKpos x hx y hy hpos
    exact (ne_of_gt houtpos) hzero
  · exact Or.inr (le_of_not_gt hlt)

/-- Exercise 3.3: translation by one. -/
noncomputable def translateOp : Operator RealBase none where
  func
    | none => none
    | some x => some (x+1)
  preserves_bot := rfl

def translateDomain : Set RealBase := {some (-3), some (-2), some 0, some 2}

def realId : Operator RealBase none := operator_identity

/-- All distinct fibres of the identity and translation on the specified
finite domain; repeated targets are deliberately retained in the list. -/
theorem translate_fibre_partition :
    (FibSingle (fun _ : Unit => absReadDist) realId () (some (-3)) translateDomain = {some (-3)} ∧
     FibSingle (fun _ : Unit => absReadDist) realId () (some (-2)) translateDomain = {some (-2), some 2} ∧
     FibSingle (fun _ : Unit => absReadDist) realId () (some 0) translateDomain = {some 0} ∧
     FibSingle (fun _ : Unit => absReadDist) realId () (some 2) translateDomain = {some (-2), some 2}) ∧
    (FibSingle (fun _ : Unit => absReadDist) translateOp () (translateOp.func (some (-3))) translateDomain = {some (-3)} ∧
     FibSingle (fun _ : Unit => absReadDist) translateOp () (translateOp.func (some (-2))) translateDomain = {some (-2), some 0} ∧
     FibSingle (fun _ : Unit => absReadDist) translateOp () (translateOp.func (some 0)) translateDomain = {some (-2), some 0} ∧
     FibSingle (fun _ : Unit => absReadDist) translateOp () (translateOp.func (some 2)) translateDomain = {some 2}) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals ext x; constructor
  all_goals intro h
  all_goals have hx : x ∈ translateDomain := by first | exact h.1 | (simp_all [translateDomain] <;> tauto)
  all_goals simp only [translateDomain, mem_insert_iff, mem_singleton_iff] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl
  all_goals norm_num [FibSingle, realId, translateOp, absReadDist, optionDist, operator_identity, translateDomain] at *

end OET.Ch03
