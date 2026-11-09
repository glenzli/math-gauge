import Ch03.Core

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X I : Type} {bot : X}

/-- Existence of the prescribed point-value factor map on the actual image. -/
def PointFactorable (φA φB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (φA.func '' U) → X,
    ∀ x (hx : x ∈ U), T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x

/-- Canonical representative-based construction of a point-value factor. -/
noncomputable def pointFactor (φA φB : Operator X bot) (U : Set X)
    (a : φA.func '' U) : X :=
  φB.func (Classical.choose a.2)

theorem pointFactor_spec {φA φB : Operator X bot} {U : Set X}
    (hrel : pointRel φA U ⊆ pointRel φB U) (x : X) (hx : x ∈ U) :
    pointFactor φA φB U ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x := by
  let a : φA.func '' U := ⟨φA.func x, ⟨x, hx, rfl⟩⟩
  have ha := Classical.choose_spec a.2
  have hpair : (Classical.choose a.2, x) ∈ pointRel φA U := ⟨ha.1, hx, ha.2⟩
  exact (hrel hpair).2.2

/-- Proposition 3.6(i), necessity and representative-independent construction. -/
theorem pointFactorable_iff {φA φB : Operator X bot} {U : Set X} :
    PointFactorable φA φB U ↔ pointRel φA U ⊆ pointRel φB U := by
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    calc
      φB.func x = T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ := (hT x hx).symm
      _ = T ⟨φA.func y, ⟨y, hy, rfl⟩⟩ := congrArg T (Subtype.ext hxy)
      _ = φB.func y := hT y hy
  · intro hrel
    exact ⟨pointFactor φA φB U, pointFactor_spec hrel⟩

/-- Proposition 3.6(ii). -/
theorem pointFactorable_bidirectional_iff {φA φB : Operator X bot} {U : Set X} :
    (PointFactorable φA φB U ∧ PointFactorable φB φA U) ↔
      pointRel φA U = pointRel φB U := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact Set.Subset.antisymm (pointFactorable_iff.mp hAB) (pointFactorable_iff.mp hBA)
  · intro h
    exact ⟨pointFactorable_iff.mpr (le_of_eq h),
      pointFactorable_iff.mpr (le_of_eq h.symm)⟩

/-- Proposition 3.6(iii): the finite scalar Lip bound on the actual image. -/
theorem pointFactor_scalar_lip {φA φB : Operator X bot} {U : Set X}
    (dist : X → X → ENNReal) (KA LB : ℝ) (hKA : 0 < KA) (hLB : 0 ≤ LB)
    (hco : ∀ x ∈ U, ∀ y ∈ U,
      ENNReal.ofReal KA * dist x y ≤ dist (φA.func x) (φA.func y))
    (hlip : ∀ x ∈ U, ∀ y ∈ U,
      dist (φB.func x) (φB.func y) ≤ ENNReal.ofReal LB * dist x y)
    (T : (φA.func '' U) → X)
    (hT : ∀ x (hx : x ∈ U), T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x) :
    ∀ y y' : (φA.func '' U),
      dist (T y) (T y') ≤ ENNReal.ofReal (LB / KA) * dist y.1 y'.1 := by
  intro y y'
  rcases y with ⟨_, ⟨x, hx, rfl⟩⟩
  rcases y' with ⟨_, ⟨x', hx', rfl⟩⟩
  rw [hT x hx, hT x' hx']
  have h1 := hlip x hx x' hx'
  have hK0 : ENNReal.ofReal KA ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hKA)
  have hKtop : ENNReal.ofReal KA ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : ENNReal.ofReal (LB / KA) = ENNReal.ofReal LB / ENNReal.ofReal KA := by
    rw [ENNReal.ofReal_div_of_pos hKA]
  rw [hdiv]
  calc
    dist (φB.func x) (φB.func x') ≤ ENNReal.ofReal LB * dist x x' := h1
    _ = (ENNReal.ofReal LB / ENNReal.ofReal KA) * (ENNReal.ofReal KA * dist x x') := by
      rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hKtop]
    _ ≤ (ENNReal.ofReal LB / ENNReal.ofReal KA) * dist (φA.func x) (φA.func x') :=
      mul_le_mul_left' (hco x hx x' hx') _

section QuotientFactorization

variable (d : I → X → X → ENNReal)
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))

/-- The zero-distance setoid on an actual operator image. -/
def imageSetoid (φ : Operator X bot) (U : Set X) : Setoid (φ.func '' U) where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have h := gauge_zero_related_equivalence d
      (fun i x => (hd i).dist_self x) (fun i x y => (hd i).symm x y)
      (fun i x y z => (hd i).triangle x y z)
    exact ⟨fun a => h.refl a.1, fun hAB => h.symm hAB, fun hAB hBC => h.trans hAB hBC⟩

/-- Quotient of an actual image by all-component zero distance. -/
def ImageQuot (φ : Operator X bot) (U : Set X) := Quotient (imageSetoid d hd φ U)

/-- Class of a point of the actual image. -/
def imageClass (φ : Operator X bot) (U : Set X) (a : φ.func '' U) : ImageQuot d hd φ U :=
  Quotient.mk (imageSetoid d hd φ U) a

/-- Existence of the prescribed quotient transformation. -/
def QuotientFactorable (φA φB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuot d hd φA U → ImageQuot d hd φB U,
    ∀ x (hx : x ∈ U),
      T (imageClass d hd φA U ⟨φA.func x, ⟨x, hx, rfl⟩⟩) =
        imageClass d hd φB U ⟨φB.func x, ⟨x, hx, rfl⟩⟩

/-- Representative-independent quotient transformation induced by a relation
inclusion. -/
noncomputable def quotientFactor {φA φB : Operator X bot} {U : Set X}
    (hrel : zeroRel d φA U ⊆ zeroRel d φB U) :
    ImageQuot d hd φA U → ImageQuot d hd φB U :=
  fun q => Quotient.liftOn q
    (fun a => imageClass d hd φB U
      ⟨φB.func (Classical.choose a.2),
        ⟨Classical.choose a.2, (Classical.choose_spec a.2).1, rfl⟩⟩)
    (by
      intro a b hab
      apply Quotient.sound
      change GaugeZeroRelated d (φB.func (Classical.choose a.2))
        (φB.func (Classical.choose b.2))
      have ha := Classical.choose_spec a.2
      have hb := Classical.choose_spec b.2
      have hp : (Classical.choose a.2, Classical.choose b.2) ∈ zeroRel d φA U := by
        refine ⟨ha.1, hb.1, ?_⟩
        change GaugeZeroRelated d (φA.func (Classical.choose a.2))
          (φA.func (Classical.choose b.2))
        rw [ha.2, hb.2]
        exact hab
      exact (hrel hp).2.2)

theorem quotientFactor_spec {φA φB : Operator X bot} {U : Set X}
    (hrel : zeroRel d φA U ⊆ zeroRel d φB U) (x : X) (hx : x ∈ U) :
    quotientFactor d hd hrel
      (imageClass d hd φA U ⟨φA.func x, ⟨x, hx, rfl⟩⟩) =
      imageClass d hd φB U ⟨φB.func x, ⟨x, hx, rfl⟩⟩ := by
  apply Quotient.sound
  let a : φA.func '' U := ⟨φA.func x, ⟨x, hx, rfl⟩⟩
  change GaugeZeroRelated d (φB.func (Classical.choose a.2)) (φB.func x)
  have ha := Classical.choose_spec a.2
  have hp : (Classical.choose a.2, x) ∈ zeroRel d φA U := by
    refine ⟨ha.1, hx, ?_⟩
    change GaugeZeroRelated d (φA.func (Classical.choose a.2)) (φA.func x)
    rw [ha.2]
    intro i
    exact (hd i).dist_self _
  exact (hrel hp).2.2

/-- Proposition 3.7, one-way quotient factorization criterion. -/
theorem quotientFactorable_iff {φA φB : Operator X bot} {U : Set X} :
    QuotientFactorable d hd φA φB U ↔ zeroRel d φA U ⊆ zeroRel d φB U := by
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    have hq : imageClass d hd φA U ⟨φA.func x, ⟨x, hx, rfl⟩⟩ =
        imageClass d hd φA U ⟨φA.func y, ⟨y, hy, rfl⟩⟩ := Quotient.sound hxy
    have heq := congrArg T hq
    rw [hT x hx, hT y hy] at heq
    exact Quotient.exact heq
  · intro hrel
    exact ⟨quotientFactor d hd hrel, quotientFactor_spec d hd hrel⟩

/-- Proposition 3.7, two-way criterion. -/
theorem quotientFactorable_bidirectional_iff {φA φB : Operator X bot} {U : Set X} :
    (QuotientFactorable d hd φA φB U ∧ QuotientFactorable d hd φB φA U) ↔
      zeroRel d φA U = zeroRel d φB U := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact Set.Subset.antisymm (quotientFactorable_iff d hd |>.mp hAB)
      (quotientFactorable_iff d hd |>.mp hBA)
  · intro h
    exact ⟨quotientFactorable_iff d hd |>.mpr (le_of_eq h),
      quotientFactorable_iff d hd |>.mpr (le_of_eq h.symm)⟩

/-- On a separating actual image, point equality and gauge zero distance give
the same ordered-pair relation. -/
theorem pointRel_eq_zeroRel_of_separating {φ : Operator X bot} {U : Set X}
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hsep : ∀ a ∈ φ.func '' U, ∀ b ∈ φ.func '' U,
      GaugeZeroRelated d a b → a = b) :
    pointRel φ U = zeroRel d φ U := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    intro i
    rw [hxy]
    exact (hd i).dist_self _
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, hsep (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩ hxy⟩

/-- Proposition 3.7: under separation of both actual images, the one-way point
and quotient criteria coincide. -/
theorem quotientFactorable_iff_pointFactorable_of_separating
    {φA φB : Operator X bot} {U : Set X}
    (hsepA : ∀ a ∈ φA.func '' U, ∀ b ∈ φA.func '' U, GaugeZeroRelated d a b → a = b)
    (hsepB : ∀ a ∈ φB.func '' U, ∀ b ∈ φB.func '' U, GaugeZeroRelated d a b → a = b) :
    QuotientFactorable d hd φA φB U ↔ PointFactorable φA φB U := by
  rw [quotientFactorable_iff d hd, pointFactorable_iff,
    pointRel_eq_zeroRel_of_separating d hd hsepA,
    pointRel_eq_zeroRel_of_separating d hd hsepB]

/-- The corresponding two-way point/quotient criterion. -/
theorem quotientFactorable_bidirectional_iff_pointFactorable_of_separating
    {φA φB : Operator X bot} {U : Set X}
    (hsepA : ∀ a ∈ φA.func '' U, ∀ b ∈ φA.func '' U, GaugeZeroRelated d a b → a = b)
    (hsepB : ∀ a ∈ φB.func '' U, ∀ b ∈ φB.func '' U, GaugeZeroRelated d a b → a = b) :
    (QuotientFactorable d hd φA φB U ∧ QuotientFactorable d hd φB φA U) ↔
      (PointFactorable φA φB U ∧ PointFactorable φB φA U) := by
  rw [quotientFactorable_bidirectional_iff d hd, pointFactorable_bidirectional_iff,
    pointRel_eq_zeroRel_of_separating d hd hsepA,
    pointRel_eq_zeroRel_of_separating d hd hsepB]

end QuotientFactorization

end OET.Ch03
