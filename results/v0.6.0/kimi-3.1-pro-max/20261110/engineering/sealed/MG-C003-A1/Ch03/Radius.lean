import Ch03.Factorization

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X I : Type} {bot : X} [Fintype I]

section RadiusBasics

/-- A member of the defining radius set is below the pointwise supremum. -/
theorem le_annihilationRadius_of_mem {φ : Operator X bot} {din dout : X → X → ENNReal}
    {y : X} {U : Set X} {r : ENNReal} (hr : r ∈ annihilatingRadii φ din dout y U) :
    r ≤ annihilationRadius φ din dout y U := le_sSup hr

/-- If every finite positive radius below `M` is legal, then `M` is below the
pointwise supremum. -/
theorem le_annihilationRadius_of_forall_lt {φ : Operator X bot}
    {din dout : X → X → ENNReal} {y : X} {U : Set X} {M : ENNReal}
    (h : ∀ r : ENNReal, 0 < r → r < ⊤ → r < M →
      ball din y r ∩ U ⊆ {x | x ∈ U ∧ dout (φ.func x) (φ.func y) = 0}) :
    M ≤ annihilationRadius φ din dout y U := by
  by_contra hn
  have hs : annihilationRadius φ din dout y U < M := lt_of_not_ge hn
  obtain ⟨r, hr, hrM⟩ := exists_between hs
  have hr0 : 0 < r := lt_of_le_of_lt (zero_le _) hr
  have hrt : r < ⊤ := hrM.trans_le le_top
  have hmem : r ∈ annihilatingRadii φ din dout y U := ⟨hr0, hrt, h r hr0 hrt hrM⟩
  exact (not_lt_of_ge (le_sSup hmem)) hr

/-- Proposition 3.11, fibre-membership branch. -/
theorem output_zero_of_mem_fib (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {j : I} {U : Set X} {y y' : X}
    (h : y' ∈ FibSingle d φ j (φ.func y) U) :
    d j (φ.func y) (φ.func y') = 0 := by
  rw [(hd j).symm (φ.func y) (φ.func y')]
  exact h.2

/-- Proposition 3.11, strict-radius branch: a legal finite positive radius is
extracted from the strict supremum inequality. -/
theorem output_zero_of_dist_lt_radius (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {i j : I} {U : Set X} {y y' : X}
    (hy' : y' ∈ U) (h : d i y y' < annihilationRadius φ (d i) (d j) y U) :
    d j (φ.func y) (φ.func y') = 0 := by
  obtain ⟨ρ, hρ, hlt⟩ := lt_sSup_iff.mp h
  have hy'ball : y' ∈ ball (d i) y ρ ∩ U := by
    refine ⟨?_, hy'⟩
    exact (show d i y' y < ρ from (hd i).symm y' y ▸ hlt)
  have hz := hρ.2.2 hy'ball
  rw [(hd j).symm (φ.func y) (φ.func y')]
  exact hz.2

/-- Proposition 3.11, the composite-input instance with both image points
checked against the downstream evaluation domain. -/
theorem output_zero_compose_of_mem_fib (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {j : I} {U₂ : Set X} {x x' : X}
    (hy : φ₁.func x ∈ U₂) (hy' : φ₁.func x' ∈ U₂)
    (h : φ₁.func x' ∈ FibSingle d φ₂ j (φ₂.func (φ₁.func x)) U₂) :
    d j ((operator_compose φ₂ φ₁).func x) ((operator_compose φ₂ φ₁).func x') = 0 := by
  exact output_zero_of_mem_fib d hd φ₂ h

/-- Proposition 3.9(i). -/
theorem fib_idComponent_image (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {i : I} {U : Set X} (hi : i ∈ idComponents d φ U)
    (y : X) (hy : y ∈ U) :
    FibSingle d φ i (φ.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, ?_⟩
    rw [idComponent_dist_eq d hd φ U hi x hx y hy] at hzero
    exact hzero
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, ?_⟩
    rw [idComponent_dist_eq d hd φ U hi x hx y hy]
    exact hzero

/-- Proposition 3.9(ii). -/
theorem radius_ge_of_ball_subset_id (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {i : I} {U : Set X} {y : X} (hy : y ∈ U)
    (hi : i ∈ idComponents d φ U) {r₀ : ENNReal} (hr₀ : 0 < r₀) (hr₀top : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ {x | x ∈ U ∧ d i x y = 0}) :
    r₀ ≤ annihilationRadius φ (d i) (d i) y U ∧ 0 < r₀ := by
  constructor
  · apply le_sSup
    refine ⟨hr₀, hr₀top, ?_⟩
    intro x hx
    have hz := hball hx
    refine ⟨hz.1, ?_⟩
    have heq := idComponent_dist_eq d hd φ U hi x hz.1 y hy
    rw [heq]
    exact hz.2
  · exact hr₀

end RadiusBasics

section ConstantRadius

variable (d : I → X → X → ENNReal)

/-- Proposition 3.8(i-a). -/
theorem fib_const_subfamily (φ : Operator X bot) {J : Set I} {U : Set X}
    (hJ : ∀ j ∈ J, j ∈ constComponents d φ U) {y : X} (hy : y ∈ U) :
    Fib d φ J (φ.func y) U = U := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    exact ⟨hx, subfamily_zero_iff.mpr (fun j hj => hJ j hj x hx y hy)⟩

/-- Proposition 3.8(i-b): every pointwise and every uniform radius is `+∞`. -/
theorem uniformRadius_top_of_const_subfamily (φ : Operator X bot) {J : Set I}
    {U : Set X} (hU : U.Nonempty) (hJ : ∀ j ∈ J, j ∈ constComponents d φ U) (i : I) :
    (∀ y ∈ U, componentAnnihilationRadius d φ i J y U = ⊤) ∧
      componentUniformAnnihilationRadius d φ i J U = ⊤ := by
  have hp : ∀ y ∈ U, componentAnnihilationRadius d φ i J y U = ⊤ := by
    intro y hy
    rw [componentAnnihilationRadius, annihilationRadius, sSup_eq_top]
    intro b hb
    refine ⟨b + 1, ?_, ?_⟩
    · refine ⟨by positivity, ENNReal.add_lt_top.mpr ⟨hb, ENNReal.one_lt_top⟩, ?_⟩
      intro x hx
      exact ⟨hx.2, subfamily_zero_iff.mpr (fun j hj => hJ j hj x hx.2 y hy)⟩
    · exact ENNReal.lt_add_right (ne_of_lt hb) (by simp)
  refine ⟨hp, ?_⟩
  apply top_unique
  apply le_iInf
  intro y
  change ⊤ ≤ componentAnnihilationRadius d φ i J y.1 U
  rw [hp y.1 y.2]

end ConstantRadius

section RadiusMin

variable (d : I → X → X → ENNReal)

/-- Proposition 3.10, pointwise component-minimum formula, written as an
infimum over the nonempty subtype `J`. -/
theorem componentRadius_eq_iInf (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) :
    componentAnnihilationRadius d φ i J y U =
      ⨅ j : J, componentAnnihilationRadius d φ i ({j.1} : Set I) y U := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply sSup_le
    intro r hr
    apply le_sSup
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro x hx
    have hz := hr.2.2 hx
    refine ⟨hz.1, ?_⟩
    rw [subfamily_pseudometric_singleton]
    exact subfamily_zero_iff.mp hz.2 j.1 j.2
  · apply le_annihilationRadius_of_forall_lt
    intro r hr0 hrt hrM
    intro x hx
    refine ⟨hx.2, subfamily_zero_iff.mpr ?_⟩
    intro j hj
    have hrj : r < componentAnnihilationRadius d φ i ({j} : Set I) y U :=
      hrM.trans_le (iInf_le (fun k : J => componentAnnihilationRadius d φ i ({k.1} : Set I) y U) ⟨j, hj⟩)
    have hdist : d i y x < annihilationRadius φ (d i) (d j) y U := by
      rw [← componentRadius_single d φ i j y U]
      exact lt_of_lt_of_le ((hd i).symm y x ▸ hx.1) hrj.le
    rw [(hd j).symm (φ.func x) (φ.func y)]
    exact output_zero_of_dist_lt_radius d hd φ hx.2 hdist

/-- Proposition 3.10, exchanging the base-point infimum and the finite
component minimum. -/
theorem componentUniformRadius_eq_iInf (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (i : I) (J : Set I) (U : Set X) :
    componentUniformAnnihilationRadius d φ i J U =
      ⨅ j : J, componentUniformAnnihilationRadius d φ i ({j.1} : Set I) U := by
  simp only [componentUniformAnnihilationRadius, uniformAnnihilationRadiusOn,
    uniformAnnihilationRadius, componentAnnihilationRadius]
  simp_rw [show ∀ y : U, annihilationRadius φ (d i) (subfamily_pseudometric d J) y.1 U =
      ⨅ j : J, annihilationRadius φ (d i) (subfamily_pseudometric d ({j.1} : Set I)) y.1 U from
    fun y => componentRadius_eq_iInf d hd φ i J y.1 U]
  exact iInf_comm

/-- Proposition 3.10, antitonicity in the output subfamily. -/
theorem componentUniformRadius_antitone (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (i : I) {J K : Set I} (hJK : J ⊆ K) (U : Set X) :
    componentUniformAnnihilationRadius d φ i K U ≤
      componentUniformAnnihilationRadius d φ i J U := by
  rw [componentUniformRadius_eq_iInf d hd, componentUniformRadius_eq_iInf d hd]
  apply le_iInf
  intro j
  exact iInf_le (fun k : K => componentUniformAnnihilationRadius d φ i ({k.1} : Set I) U)
    ⟨j.1, hJK j.2⟩

end RadiusMin

section RadiusMonotone

/-- Proposition 3.14(ii-a). -/
theorem annihilationRadius_domain_antitone {φ : Operator X bot}
    {din dout : X → X → ENNReal} {A B : Set X} (hBA : B ⊆ A) (x : X) :
    annihilationRadius φ din dout x A ≤ annihilationRadius φ din dout x B := by
  apply sSup_le
  intro r hr
  apply le_sSup
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro y hy
  have hz := hr.2.2 ⟨hy.1, hBA hy.2⟩
  exact ⟨hy.2, hz.2⟩

/-- Proposition 3.14(ii-b). -/
theorem uniformRadius_domain_antitone {φ : Operator X bot}
    {din dout : X → X → ENNReal} {A B : Set X} (hBA : B ⊆ A) :
    uniformAnnihilationRadiusOn φ din dout A ≤
      uniformAnnihilationRadiusOn φ din dout B := by
  apply le_iInf
  intro x
  calc
    uniformAnnihilationRadiusOn φ din dout A ≤ annihilationRadius φ din dout x.1 A :=
      iInf_le (fun y : A => annihilationRadius φ din dout y.1 A) ⟨x.1, hBA x.2⟩
    _ ≤ annihilationRadius φ din dout x.1 B := annihilationRadius_domain_antitone hBA x.1

end RadiusMonotone

section UniformThreshold

variable (d : I → X → X → ENNReal)

/-- Proposition 3.15(i). -/
theorem output_zero_of_dist_lt_uniformRadius (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A)
    (h : d i x y < uniformAnnihilationRadiusOn f (d i) (d j) A) :
    d j (f.func x) (f.func y) = 0 := by
  apply output_zero_of_dist_lt_radius d hd f hy
  exact h.trans_le (iInf_le (fun z : A => annihilationRadius f (d i) (d j) z.1 A) ⟨x, hx⟩)

/-- Proposition 3.15(ii). -/
theorem dist_ge_uniformRadius_of_output_pos (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (hpos : 0 < d j (f.func x) (f.func y)) :
    uniformAnnihilationRadiusOn f (d i) (d j) A ≤ d i x y := by
  by_contra hn
  have hlt : d i x y < uniformAnnihilationRadiusOn f (d i) (d j) A := lt_of_not_ge hn
  exact (ne_of_gt hpos) (output_zero_of_dist_lt_uniformRadius d hd f hx hy hlt)

/-- Proposition 3.15(iii), including infinite output distance. -/
theorem separation_witness_of_uniformRadius_lt (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) {i j : I} {A : Set X} {α : ENNReal}
    (hα0 : 0 < α) (hαtop : α < ⊤)
    (h : uniformAnnihilationRadiusOn f (d i) (d j) A < α) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp h
  have hyα : annihilationRadius f (d i) (d j) y.1 A < α := hy
  have hnot : ¬ ball (d i) y.1 α ∩ A ⊆
      {x | x ∈ A ∧ d j (f.func x) (f.func y.1) = 0} := by
    intro hall
    have hmem : α ∈ annihilatingRadii f (d i) (d j) y.1 A := ⟨hα0, hαtop, hall⟩
    exact (not_lt_of_ge (le_sSup hmem)) hyα
  obtain ⟨x, hx, hnx⟩ := not_subset.mp hnot
  have hpos : 0 < d j (f.func x) (f.func y.1) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    exact hnx ⟨hx.2, hzero⟩
  refine ⟨x, hx.2, y.1, y.2, ?_⟩
  by_cases htop : d j (f.func x) (f.func y.1) = ⊤
  · exact ⟨1, zero_lt_one, ENNReal.one_lt_top, hx.1, by rw [htop]; exact le_top⟩
  · exact ⟨d j (f.func x) (f.func y.1), hpos, lt_top_iff_ne_top.mpr htop, hx.1, le_rfl⟩

end UniformThreshold

section CompositionRadius

variable (d : I → X → X → ENNReal)

/-- Proposition 3.12(i). -/
theorem uniformRadius_compose_ge_of_zero_preserving
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {i j l : I} {U : Set X}
    (hpres : ∀ y ∈ φ₁.func '' U, ∀ y' ∈ φ₁.func '' U,
      d l y y' = 0 → d j (φ₂.func y) (φ₂.func y') = 0) :
    uniformAnnihilationRadiusOn φ₁ (d i) (d l) U ≤
      uniformAnnihilationRadiusOn (operator_compose φ₂ φ₁) (d i) (d j) U := by
  apply le_iInf
  intro x
  apply le_annihilationRadius_of_forall_lt
  intro r hr0 hrt hrM
  intro z hz
  refine ⟨hz.2, ?_⟩
  have hpoint : uniformAnnihilationRadiusOn φ₁ (d i) (d l) U ≤
      annihilationRadius φ₁ (d i) (d l) x.1 U :=
    iInf_le (fun y : U => annihilationRadius φ₁ (d i) (d l) y.1 U) x
  have hdist : d i x.1 z < annihilationRadius φ₁ (d i) (d l) x.1 U :=
    lt_of_lt_of_le ((hd i).symm x.1 z ▸ hz.1) (hrM.le.trans hpoint)
  have hzero := output_zero_of_dist_lt_radius d hd φ₁ hz.2 hdist
  rw [(hd j).symm ((operator_compose φ₂ φ₁).func z) ((operator_compose φ₂ φ₁).func x.1)]
  exact hpres (φ₁.func x.1) ⟨x.1, x.2, rfl⟩ (φ₁.func z) ⟨z, hz.2, rfl⟩ hzero

/-- Proposition 3.12(ii), with zero and infinite right-hand sides handled by
`ENNReal` arithmetic. -/
theorem uniformRadius_compose_ge_div_of_lip
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ₁ φ₂ : Operator X bot) {i j l : I} {U : Set X}
    {L : ENNReal} (hL0 : 0 < L) (hLtop : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d l (φ₁.func x) (φ₁.func x') ≤ L * d i x x') :
    uniformAnnihilationRadiusOn φ₂ (d l) (d j) (φ₁.func '' U) / L ≤
      uniformAnnihilationRadiusOn (operator_compose φ₂ φ₁) (d i) (d j) U := by
  apply le_iInf
  intro x
  apply le_annihilationRadius_of_forall_lt
  intro r hr0 hrt hrM
  intro z hz
  refine ⟨hz.2, ?_⟩
  have hbase : φ₁.func x.1 ∈ φ₁.func '' U := ⟨x.1, x.2, rfl⟩
  have hpoint : uniformAnnihilationRadiusOn φ₂ (d l) (d j) (φ₁.func '' U) ≤
      annihilationRadius φ₂ (d l) (d j) (φ₁.func x.1) (φ₁.func '' U) :=
    iInf_le (fun y : (φ₁.func '' U) => annihilationRadius φ₂ (d l) (d j) y.1 (φ₁.func '' U))
      ⟨φ₁.func x.1, hbase⟩
  have hmul : L * d i x.1 z < uniformAnnihilationRadiusOn φ₂ (d l) (d j) (φ₁.func '' U) := by
    have hxz : d i x.1 z < r := by
      rw [(hd i).symm x.1 z]
      exact hz.1
    calc
      L * d i x.1 z < L * r := ENNReal.mul_lt_mul_right (ne_of_gt hL0) (ne_of_lt hLtop) hxz
      _ < L * (uniformAnnihilationRadiusOn φ₂ (d l) (d j) (φ₁.func '' U) / L) :=
        ENNReal.mul_lt_mul_right (ne_of_gt hL0) (ne_of_lt hLtop) hrM
      _ = uniformAnnihilationRadiusOn φ₂ (d l) (d j) (φ₁.func '' U) := by
        rw [mul_comm]
        exact ENNReal.div_mul_cancel (ne_of_gt hL0) (ne_of_lt hLtop)
  have hdist : d l (φ₁.func x.1) (φ₁.func z) <
      annihilationRadius φ₂ (d l) (d j) (φ₁.func x.1) (φ₁.func '' U) := by
    apply lt_of_le_of_lt _ (hmul.trans_le hpoint)
    rw [(hd l).symm (φ₁.func x.1) (φ₁.func z)]
    exact (hLip z hz.2 x.1 x.2).trans (by rw [(hd i).symm z x.1])
  have hz' : φ₁.func z ∈ φ₁.func '' U := ⟨z, hz.2, rfl⟩
  rw [(hd j).symm ((operator_compose φ₂ φ₁).func z) ((operator_compose φ₂ φ₁).func x.1)]
  exact output_zero_of_dist_lt_radius d hd φ₂ hz' hdist

end CompositionRadius

end OET.Ch03
