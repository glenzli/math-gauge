/-
Portions copyright (c) 2026 kangxyz and Motivic Cohomology contributors.
SPDX-License-Identifier: Apache-2.0

Finite-point extensions and assembly for Math Gauge GP003 S5.
Adapted from kangxyz/motivic, commit a6805c4a87cdfd7717dd7a94039246a167f15380:
https://github.com/kangxyz/motivic/tree/a6805c4a87cdfd7717dd7a94039246a167f15380
Upstream license: https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/LICENSE

These sources use the fixed upstream Lean 4.34.1 profile. The ambient and scalar
schemes, complete finite fibres, original nonreduced boundaries and actual
finite correspondences are retained throughout the construction.
-/
import Motivic.Cohomology.A1.LocalVanishing.Original.AffineLocalVanishing
/-!
A single quadratic projection works above finitely many selected closed points.
The nonzero parameter conditions are constructed from actual bad-point incidence
charts. Their finite product replaces repeated unrelated pointwise choices.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Module TensorProduct KaehlerDifferential MvPolynomial AlgebraicGeometry
universe u

namespace MathGauge.GP003.S5Simultaneous
open QuadraticIncidence
open AlgebraicGeometry.Scheme.RelativeCurve

/-- Actual off-diagonal bad charts supply one nonzero polynomial whose principal
open consists entirely of good parameters; no parameter-goodness certificate is
assumed. -/
theorem exists_goodOffDiagonal_open
    (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Module.Finite R B] [Algebra.Smooth k R]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a : σ → B) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin d × Exponent σ) k, f ≠ 0 ∧
      ∀ c, eval c f ≠ 0 → GoodOffDiagonalParameters k R B g a d c := by
  obtain ⟨f, hf, hz⟩ :=
    MovingPointChart.exists_nonzero_common_parameter_relation k R B g hg a d hd
  refine ⟨f, hf, ?_⟩
  intro c hc K _ _ _ _ _ _
  dsimp only
  intro hab hvalue
  apply MovingPointChart.linearIndependent_of_parameter_relation_ne_zero k R B K
    g a d f c hc hz (parameterTuple K σ d (algebraMap k K ∘ c)) _ hab hvalue
  intro x
  exact parameterTuple_repr K σ d (algebraMap k K ∘ c) x

/-- Smoothness along an entire selected fibre is ensured on a constructed
nonempty principal open in the original parameter space. -/
theorem exists_wholeFiber_smooth_open
    (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ h : MvPolynomial (Fin d × Exponent σ) k, h ≠ 0 ∧
      ∀ c, eval c h ≠ 0 →
        let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
        ∀ Q : PrimeSpectrum R,
          Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
            Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
          ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
            (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
              (aeval (R := k) f).toRingHom))) := by
  obtain ⟨q₀, hq₀, hselected⟩ := exists_selectedPoint_open_of_smooth
    (L := P.asIdeal.ResidueField) g hg d hd
  obtain ⟨q₁, hq₁, hoff⟩ := exists_goodOffDiagonal_open k R
    (ClosedPoint.CoefficientRing k R P) g hg
    (fun j => ClosedPoint.selectedValue k R P (g j)) d hd
  refine ⟨q₀ * q₁, mul_ne_zero hq₀ hq₁, ?_⟩
  intro c hc
  have hc₀ : eval c q₀ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hc)).1
  have hc₁ : eval c q₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hc)).2
  let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
  dsimp only
  intro Q hPQ
  apply exists_smooth_one_of_residue_independent k R Q.asIdeal d f hd
  apply independent_differentials_of_same_fiber k R P Q d f hPQ
  intro K _ _ _ _ _ _ hv
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq'
    ((IsScalarTower.algebraMap_eq k (ClosedPoint.CoefficientRing k R P) K).trans
      (by rw [IsScalarTower.algebraMap_eq k R (ClosedPoint.CoefficientRing k R P),
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R
          (ClosedPoint.CoefficientRing k R P) K]))
  let s : R →ₐ[k] K := (IsScalarTower.toAlgHom k (ClosedPoint.CoefficientRing k R P) K).comp
    ((Algebra.TensorProduct.includeRight : P.asIdeal.ResidueField →ₐ[k]
      ClosedPoint.CoefficientRing k R P).comp
        (IsScalarTower.toAlgHom k R P.asIdeal.ResidueField))
  have hv' : ∀ i, eval (fun j => algebraMap R K (g j))
      (parameterTuple K σ d (algebraMap k K ∘ c) i).val =
    eval (fun j => algebraMap (ClosedPoint.CoefficientRing k R P) K
      (ClosedPoint.selectedValue k R P (g j)))
      (parameterTuple K σ d (algebraMap k K ∘ c) i).val := by
    intro i
    rw [← parameterTuple_map, eval_map_generator_polynomial]
    change algebraMap R K (f i) = eval (fun j => s (g j))
      (MvPolynomial.map (algebraMap k K) (parameterTuple k σ d c i).val)
    rw [eval_map_original_function]
    exact hv i
  have hi : LinearIndependent K (fun i => residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l))
        (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
    by_cases he : (fun j => algebraMap R K (g j)) =
        fun j => algebraMap (ClosedPoint.CoefficientRing k R P) K
          (ClosedPoint.selectedValue k R P (g j))
    · exact ClosedPoint.independent_parameterTuple_at_diagonal k R P K g hg d c
        (hselected c hc₀) (fun j => congrFun he j)
    · exact hoff c hc₁ K he hv'
  simpa only [← parameterTuple_map,
    residueGeneratorGradient_map_polynomial] using hi

/-- One original quadratic projection is smooth around every point of every
selected fibre, simultaneously. No new tuple is chosen as the selected point
varies; arbitrary prescribed nonempty parameter opens are retained. -/
theorem exists_finitelyMany_wholeFiber_smooth_projection
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    {τ : Type u} [Fintype τ] (P : τ → PrimeSpectrum R)
    [∀ i, (P i).asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ i : τ, ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom (P i).asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  classical
  choose h hh hgood using fun i => exists_wholeFiber_smooth_open k R (P i) g hg d hd
  have hprod : q * ∏ i, h i ≠ 0 :=
    mul_ne_zero hq (Finset.prod_ne_zero_iff.mpr (fun i _ => hh i))
  have hex : ∃ c : Fin d × Exponent σ → k, eval c (q * ∏ i, h i) ≠ 0 := by
    by_contra! hz
    exact hprod (MvPolynomial.funext fun c => by simpa using hz c)
  obtain ⟨c, hc⟩ := hex
  rw [map_mul, map_prod] at hc
  have hcq := (mul_ne_zero_iff.mp hc).1
  have hch := (mul_ne_zero_iff.mp hc).2
  refine ⟨c, hcq, ?_⟩
  dsimp only
  intro i
  exact hgood i c (Finset.prod_ne_zero_iff.mp hch i (Finset.mem_univ i))

/-- A finite collection of whole closed fibres fits in one genuine principal
smooth open. The defining element is one modulo the intersection of the actual
fibre ideals, so no point of any selected fibre is discarded. -/
theorem exists_finitelyMany_closedFiber_principal_smooth
    (k A R : Type u) [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra k R] [Algebra.FiniteType k R]
    (φ : A →ₐ[k] R) {τ : Type u} [Fintype τ] (P : τ → PrimeSpectrum R)
    [∀ i, (P i).asIdeal.IsMaximal] (n : ℕ)
    (h : ∀ i, ∀ Q : PrimeSpectrum R,
      Ideal.comap φ.toRingHom (P i).asIdeal = Ideal.comap φ.toRingHom Q.asIdeal →
      ∃ a ∉ Q.asIdeal, SmoothOfRelativeDimension n
        (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away a)).comp
          φ.toRingHom)))) :
    ∃ r : R,
      (∀ i, r - 1 ∈ Ideal.map φ.toRingHom (Ideal.comap φ.toRingHom (P i).asIdeal)) ∧
      (∀ i, ∀ Q : PrimeSpectrum R,
        Ideal.comap φ.toRingHom (P i).asIdeal = Ideal.comap φ.toRingHom Q.asIdeal →
        r ∉ Q.asIdeal) ∧
      SmoothOfRelativeDimension n
        (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
          Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  classical
  let I : τ → Ideal R := fun i =>
    Ideal.map φ.toRingHom (Ideal.comap φ.toRingHom (P i).asIdeal)
  let J : Ideal R := Finset.univ.inf I
  obtain ⟨r, hr, hs⟩ := exists_principal_smooth_neighborhood A R φ.toRingHom J n (by
    intro Q hQ
    obtain ⟨i, _, hi⟩ := Q.isPrime.inf_le'.mp hQ
    have hm := comap_closedPoint_isMaximal k A R φ (P i)
    exact h i Q (hm.eq_of_le
      (Ideal.IsPrime.ne_top (inferInstance : (Ideal.comap φ.toRingHom Q.asIdeal).IsPrime))
      (Ideal.map_le_iff_le_comap.mp hi)))
  have hrI : ∀ i, r - 1 ∈ I i := fun i =>
    (show J ≤ I i from Finset.inf_le (Finset.mem_univ i)) hr
  exact ⟨r, hrI, fun i Q hQ =>
    not_mem_of_sub_one_mem_fiber φ.toRingHom (P i) Q r (hrI i) hQ, hs⟩

/-- An unchanged quadratic tuple and one principal source open retain all
selected whole fibres. The local smoothness premises of the preceding helper
are constructed here from the original smooth affine algebra. -/
theorem exists_finitelyMany_wholeFiber_principal_smooth_projection
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    {τ : Type u} [Fintype τ] (P : τ → PrimeSpectrum R)
    [∀ i, (P i).asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      let φ := (aeval (R := k) f).toRingHom
      ∃ r : R,
        (∀ i, r - 1 ∈ Ideal.map φ (Ideal.comap φ (P i).asIdeal)) ∧
        (∀ i, ∀ Q : PrimeSpectrum R,
          Ideal.comap φ (P i).asIdeal = Ideal.comap φ Q.asIdeal → r ∉ Q.asIdeal) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨c, hc, h⟩ := exists_finitelyMany_wholeFiber_smooth_projection
    k R P g hg d hd q hq
  refine ⟨c, hc, ?_⟩
  exact exists_finitelyMany_closedFiber_principal_smooth
    k (MvPolynomial (Fin d) k) R
    (aeval (R := k) (fun i => aeval g (parameterTuple k σ d c i).val)) P 1 h

/-- One tuple simultaneously supplies a genuine finite compactification, finite
prescribed boundary, and smoothness on all selected fibres. The full-tuple
étale condition at one selected point constructs the original normal model;
the entire family of curve-fibre smoothness conditions is retained. -/
theorem exists_finitelyMany_quadratic_parameters
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    {τ : Type u} [Fintype τ] [Nonempty τ] (P : τ → PrimeSpectrum R)
    [∀ i, (P i).asIdeal.IsMaximal]
    (I : Ideal R) (hI : I ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      (∃ i : τ, ∃ r ∉ (P i).asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun j => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) j).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      let φ := (aeval (R := k) f).toRingHom
      ∃ r : R,
        (∀ i, r - 1 ∈ Ideal.map φ (Ideal.comap φ (P i).asIdeal)) ∧
        (∀ i, ∀ Q : PrimeSpectrum R,
          Ideal.comap φ (P i).asIdeal = Ideal.comap φ Q.asIdeal → r ∉ Q.asIdeal) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom φ)) := by
  classical
  let i₀ : τ := Classical.choice inferInstance
  obtain ⟨F, hF, hgood⟩ := InfinityChart.exists_infinity_avoidance_polynomial k R g d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hd.le)
  obtain ⟨E, hE, hetale⟩ := exists_selectedEtale_open k R (P i₀) g hg (d + 1) hd
  obtain ⟨Q, hQ, hclosed⟩ := InfinityChart.exists_closed_infinity_avoidance_polynomial
    k R I hI g d (by simpa only [Nat.cast_add, Nat.cast_one] using hd.le)
  obtain ⟨a, ha⟩ := exists_specializeAuxiliary_ne_zero k d (F * E) (mul_ne_zero hF hE)
  obtain ⟨c, hc, hsmooth⟩ := exists_finitelyMany_wholeFiber_principal_smooth_projection
    k R P g hg d hd (specializeAuxiliary k d a (F * E) * (Q * q))
      (mul_ne_zero ha (mul_ne_zero hQ hq))
  have hc' : eval c (specializeAuxiliary k d a (F * E)) *
      (eval c Q * eval c q) ≠ 0 := by simpa only [map_mul] using hc
  have hFE : eval (prependParameters k d a c) (F * E) ≠ 0 := by
    rw [← eval_specializeAuxiliary]
    exact (mul_ne_zero_iff.mp hc').1
  rw [map_mul] at hFE
  exact ⟨a, c, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc').2).2,
    hclosed c (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc').2).1,
    hgood _ (mul_ne_zero_iff.mp hFE).1,
    ⟨i₀, hetale _ (mul_ne_zero_iff.mp hFE).2⟩, hsmooth⟩

/-- The actual original finite-point compactification: the affine smooth open
contains every selected fibre, including non-rational closed points. This is a
construction from smooth affine algebra data, not an assumed curve presentation. -/
theorem exists_finitelyMany_quadratic_compactification
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    {τ : Type u} [Fintype τ] [Nonempty τ] (P : τ → PrimeSpectrum B)
    [∀ i, (P i).asIdeal.IsMaximal]
    (I : Ideal B) (hI : I ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (InfinityChart.quadraticCoordinateHom k B g d c)))) ∧
      (∃ r : B,
        (∀ i, r - 1 ∈ Ideal.map (InfinityChart.quadraticCoordinateHom k B g d c)
          (Ideal.comap (InfinityChart.quadraticCoordinateHom k B g d c) (P i).asIdeal)) ∧
        (∀ i, ∀ Q : PrimeSpectrum B,
          Ideal.comap (InfinityChart.quadraticCoordinateHom k B g d c) (P i).asIdeal =
            Ideal.comap (InfinityChart.quadraticCoordinateHom k B g d c) Q.asIdeal →
          r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (InfinityChart.quadraticCoordinateHom k B g d c)))) ∧
      ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N)
        (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2))) (b : D ⟶ N),
        IsIntegral N ∧ IsLocallyNoetherian N ∧
        (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
        IsOpenImmersion i ∧ IsFinite π ∧ IsClosedImmersion b ∧
        IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _) ∧
        Set.range b = (Set.range i)ᶜ ∧
        i ≫ π = Spec.map (CommRingCat.ofHom
          (InfinityChart.quadraticRelativeCoordinateHom k B g d a c)) ≫
            RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
        i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
          Spec.map (CommRingCat.ofHom (InfinityChart.quadraticCoordinateHom k B g d c)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨a, c, hc, hZ, hW, ⟨i₀, r₀, hr₀, he⟩, r, hr, hwhole, hs⟩ :=
    exists_finitelyMany_quadratic_parameters k B P I hI g hg d hd q hq
  exact ⟨a, c, hc, InfinityChart.quadraticClosedTuple_isFinite k B g d I hg c hZ,
    ⟨r, hr, hwhole, IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of B) r).hom, hs⟩,
    InfinityChart.exists_quadratic_normal_compactification k B g hg d a c hW
      (P i₀) r₀ hr₀ he⟩

/-- Finiteness over the union of actual target opens follows by Zariski descent.
No source open is shrunk when passing to this common base neighborhood. -/
theorem finite_morphismRestrict_iSup {X S : Scheme.{u}} (f : X ⟶ S)
    {τ : Type u} (U : τ → S.Opens) (hU : ∀ i, IsFinite (f ∣_ U i)) :
    IsFinite (f ∣_ (⨆ i, U i)) := by
  let V : S.Opens := ⨆ i, U i
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
  refine ⟨V.ι ⁻¹ᵁ U i, hi, ?_⟩
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U i) = U i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_iSup U i)
  apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U i))).mpr
  rw [he]
  exact hU i

/-- The literal full retained boundary and original prescribed finite scheme
are controlled on a single open containing every selected base point. -/
theorem exists_finite_retainedBoundary_preserving_finitelyMany
    {C S B Z : Scheme.{u}} (q : C ⟶ S) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens)
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : Set S)
    (hwhole : ∀ y ∈ s, ∀ x : C, q x = y → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ T : S.Opens, s ⊆ T ∧ IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T) ∧
      ∀ x : Z, (z ≫ q) x ∈ T → z x ∈ V := by
  classical
  choose T hs hfinite hZ using fun y : s =>
    exists_finite_retainedBoundary_preserving_scheme q b U V hboundary y.1
      (hwhole y.1 y.2) z hzU
  refine ⟨⨆ y, T y, ?_, finite_morphismRestrict_iSup _ T hfinite, ?_⟩
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hs ⟨y, hy⟩⟩
  · intro x hx
    obtain ⟨y, hy⟩ := Opens.mem_iSup.mp hx
    exact hZ y x hy

/-- A single principal base open retains every selected point, all original
prescribed points and the full new finite boundary, including nilpotent structure. -/
theorem exists_principal_retainedBoundary_preserving_finitelyMany
    (R : Type u) [CommRing R] {C B Z : Scheme.{u}}
    (q : C ⟶ Spec (CommRingCat.of R)) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens) [IsAffine V.toScheme]
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b)
    (s : Set (Spec (CommRingCat.of R))) (hs : s.Finite)
    (hwhole : ∀ y ∈ s, ∀ x : C, q x = y → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ r : R, s ⊆ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∧
      IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ PrimeSpectrum.basicOpen r) ∧
      IsAffine (((V.ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme) ∧
      ∀ x : Z, (z ≫ q) x ∈ PrimeSpectrum.basicOpen r → z x ∈ V := by
  obtain ⟨T, hsT, hfinite, hZ⟩ := exists_finite_retainedBoundary_preserving_finitelyMany
    q b U V hboundary s hwhole z hzU
  obtain ⟨r, hsr, hrT⟩ := PrimeSpectrum.exists_basicOpen_of_finite_subset T s hs hsT
  have : IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T) := hfinite
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) :=
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) r).hom
  refine ⟨r, hsr, finite_morphismRestrict_of_le _ hrT, ?_, fun x hx => hZ x (hrT hx)⟩
  exact IsAffineOpen.preimage (by assumption) (V.ι ≫ q)

/-- A genuine compactification and an unchanged whole-fibre affine smooth open
give one principal base neighborhood controlling all the selected fibres. -/
theorem exists_compact_retained_principal_neighborhood_finitelyMany
    (R : Type u) [CommRing R] {X N D Z : Scheme.{u}}
    (i : X ⟶ N) [IsOpenImmersion i] (q : N ⟶ Spec (.of R)) [IsProper q]
    (f : X ⟶ Spec (.of R)) (hi : i ≫ q = f)
    (b : D ⟶ N) [IsFinite (b ≫ q)] (hb : Set.range b = (Set.range i)ᶜ)
    (V : X.Opens) [IsAffine V.toScheme] [SmoothOfRelativeDimension 1 (V.ι ≫ f)]
    (s : Set (Spec (.of R))) (hs : s.Finite)
    (hV : ∀ y ∈ s, ∀ x : X, f x = y → x ∈ V)
    (z : Z ⟶ X) [IsFinite (z ≫ f)] :
    ∃ t : R, s ⊆ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)) ∧
      IsAffine (i ''ᵁ V).toScheme ∧
      SmoothOfRelativeDimension 1 ((i ''ᵁ V).ι ≫ q) ∧
      IsFinite ((retainedBoundaryInclusion (i ''ᵁ V) ≫ q) ∣_ PrimeSpectrum.basicOpen t) ∧
      IsAffine ((((i ''ᵁ V).ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen t).toScheme) ∧
      ∀ x : Z, (z ≫ f) x ∈ PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ V := by
  obtain ⟨ha, hsmooth⟩ := affine_smooth_image i q f hi V 1
  have : IsAffine (i ''ᵁ V).toScheme := ha
  have hz : IsFinite ((z ≫ i) ≫ q) := by
    simpa only [Category.assoc, hi] using (inferInstance : IsFinite (z ≫ f))
  obtain ⟨t, ht, hb', ha', hz'⟩ :=
    exists_principal_retainedBoundary_preserving_finitelyMany R q b
      i.opensRange (i ''ᵁ V) (by simpa only [Scheme.Hom.coe_opensRange] using hb.ge)
      s hs (fun y hy => whole_fiber_image i q f hi V y (hV y hy)) (z ≫ i)
      (by rintro _ ⟨x, rfl⟩; exact ⟨z x, rfl⟩)
  refine ⟨t, ht, ha, hsmooth, hb', ha', ?_⟩
  intro x hx
  apply hz' x
  simpa only [Category.assoc, hi] using hx

open QuadraticIncidence.InfinityChart

/-- One original quadratic tuple gives the normal finite compactification, an affine
smooth retained curve, and a single principal base shrink on which the complete new
boundary is finite and the full original nonreduced prescribed scheme is retained. -/
theorem exists_finitelyMany_retained_presentation
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] {τ : Type u} [Fintype τ] [Nonempty τ]
    (P : τ → PrimeSpectrum B) [∀ j, (P j).asIdeal.IsMaximal]
    (I : Ideal B) (hI : I ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k), eval c q ≠ 0 ∧
    ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2)))
      (V : N.Opens) (t : MvPolynomial (Fin d) k),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) ∧
      (∀ j : τ, ∀ x : Spec (.of B),
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) x =
          Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) (P j) → i x ∈ V) ∧
      (V : Set N) ⊆ Set.range i ∧ IsAffine V.toScheme ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ∧
      (∀ j : τ, Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) (P j) ∈
        PrimeSpectrum.basicOpen t) ∧
      IsFinite ((retainedBoundaryInclusion V ≫ π ≫ ProjectiveSpace.toSpec _ _) ∣_
        PrimeSpectrum.basicOpen t) ∧
      IsAffine (((V.ι ≫ π ≫ ProjectiveSpace.toSpec _ _) ⁻¹ᵁ
        PrimeSpectrum.basicOpen t).toScheme) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      ∀ z : Spec (.of (B ⧸ I)),
        (Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) z ∈
            PrimeSpectrum.basicOpen t →
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) z ∈ V := by
  obtain ⟨a, c, hc, hZ, ⟨r, _, hr, ha, hs⟩,
    N, D, i, π, b, hN, hNoeth, hnormal, hi, hπ, hb, hbfin, hbrange, hfull, htail⟩ :=
    exists_finitelyMany_quadratic_compactification k B P I hI g hg d hd q hq
  let f := Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c))
  let v : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen r
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let p := π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _
  have : IsOpenImmersion i := hi
  have : IsFinite π := hπ
  have : IsFinite (b ≫ p) := hbfin
  have : IsAffine v.toScheme := ha
  have : SmoothOfRelativeDimension 1 (v.ι ≫ f) := hs
  have hzcomp : z ≫ f = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c))) := by
    exact (Spec.map_comp _ _).symm
  have : IsFinite (z ≫ f) := hzcomp.symm ▸ hZ
  have hwhole : ∀ j : τ, ∀ x : Spec (.of B), f x = f (P j) → x ∈ v := by
    intro j x hx
    apply hr j x
    exact (congrArg PrimeSpectrum.asIdeal hx).symm
  obtain ⟨t, ht, hva, hvs, hbf, hav, hretain⟩ :=
    exists_compact_retained_principal_neighborhood_finitelyMany (MvPolynomial (Fin d) k)
      i p f htail b hbrange v (Set.range (fun j => f (P j))) (Set.finite_range _)
      (by rintro y ⟨j, rfl⟩; exact hwhole j) z
  refine ⟨a, c, hc, N, i, π, i ''ᵁ v, t, hN, hNoeth, hnormal, hi, hπ,
    hfull, htail, ?_, ?_, hva, hvs, fun j => ht (Set.mem_range_self j), hbf, hav, hZ, ?_⟩
  · intro j x hx
    exact ⟨x, hwhole j x hx, rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · intro x hx
    apply hretain x
    simpa only [hzcomp] using hx


/-- The infinite-field closed-point presentation supplies every geometric input of the
original-section lifting theorem, preserving the literal original étale map, puncture,
full nonreduced closed scheme, field structure and every selected point. -/
theorem exists_finitelyMany_originalEtalePresentation
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] {τ : Type u} [Fintype τ]
    (P : τ → PrimeSpectrum B) [∀ j, (P j).asIdeal.IsMaximal] (i₀ : τ)
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    ∃ e : OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s (P i₀),
      ∀ j : τ, P j ∈ Set.range e.refinement := by
  let := Fintype.ofFinite σ
  let : Nonempty τ := ⟨i₀⟩
  obtain ⟨I, hI, hIJ, U, hU, hpU⟩ := exists_fixed_finite_locus_bad_ideal k B p J hJ
  obtain ⟨_, c, _, N, i, π, V, t,
    hN, hNoeth, hnormal, hi, hπ, _, htail, hwhole, hV, hVa, hVs,
    ht, hbfin, hVaT, hIfin, hIret⟩ :=
    exists_finitelyMany_retained_presentation k B P I hI g hg d hd 1 one_ne_zero
  let R := MvPolynomial (Fin d) k
  let f := Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c))
  let Q := π ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let T : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen t
  let zI := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let zJ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hQ : i ≫ Q = f := htail
  have : IsClosedImmersion zI :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion zJ :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsFinite (p ∣_ U) := hpU
  have : IsIntegral N := hN
  have : IsLocallyNoetherian N := hNoeth
  have : IsOpenImmersion i := hi
  have : IsFinite π := hπ
  have : IsAffine V.toScheme := hVa
  have : SmoothOfRelativeDimension 1 (V.ι ≫ Q) := hVs
  have : IsAffine T.toScheme :=
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) t).hom
  have hIfc : zI ≫ f = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c))) :=
    (Spec.map_comp _ _).symm
  have : IsFinite (zI ≫ f) := hIfc.symm ▸ hIfin
  have : IsFinite (zJ ≫ f) := prescribedSubquotient_finite B I J hIJ f
  have hzI : ∀ x : Spec (.of (B ⧸ I)), (zI ≫ f) x ∈ T → i (zI x) ∈ V := by
    intro x hx
    apply hIret x
    simpa only [hIfc] using hx
  have hzJ : ∀ x : Spec (.of (B ⧸ J)), (zJ ≫ f) x ∈ T → i (zJ x) ∈ V :=
    prescribedSubquotient_retained B I J hIJ i f T V hzI
  have hxT : Q (i (P i₀)) ∈ T := by
    change (i ≫ Q) (P i₀) ∈ T
    rw [htail]
    exact ht i₀
  have hnorm : N.NormalStalks := fun x => ⟨inferInstance, hnormal x⟩
  obtain ⟨hCn, hCnoeth, hCnormal, hπT, _⟩ :=
    finiteProjectiveBaseRestriction_properties R (ULift.{u} (Fin 2)) π T hnorm (i (P i₀)) hxT
  let r := retainedBaseToOriginal i Q T V hV
  let j := retainedBaseInclusion Q T V
  let πT := finiteProjectiveBaseRestriction R (ULift.{u} (Fin 2)) π T
  let tK := T.toScheme.isoSpec.inv ≫ T.ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  let zT := prescribedBaseToRetained i Q f htail T V hV zJ hzJ
  let sT := retainedEtaleClosedLift i Q f htail T V hV zJ hzJ p s hs
  let zIN := zI ≫ i
  let dT := coprod.desc (retainedBoundaryInclusion V ∣_ Q ⁻¹ᵁ T) (zIN ∣_ Q ⁻¹ᵁ T)
  have : IsFinite ((zI ≫ i) ≫ Q) := by simpa only [Category.assoc, hQ] using
    (inferInstance : IsFinite (zI ≫ f))
  have : IsClosedImmersion zIN := prescribed_closed_in_compactification i Q zI
  have : IsFinite ((retainedBoundaryInclusion V ≫ Q) ∣_ T) := hbfin
  have : IsFinite ((zIN ≫ Q) ∣_ T) := inferInstance
  have hretIN : ∀ x, (zIN ≫ Q) x ∈ T → zIN x ∈ V := by
    simpa only [zIN, Category.assoc, hQ, Scheme.Hom.comp_apply] using hzI
  obtain ⟨hdClosed, hdFinite⟩ := retained_prescribed_boundary_on_base Q V zIN T hretIN
  have : IsFinite (dT ≫ (Q ∣_ T)) := hdFinite
  have : IsFinite (zT ≫ ((V.ι ≫ Q) ∣_ T)) :=
    prescribedBaseToRetained_finite i Q f htail T V hV zJ hzJ
  have hbR : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have hrbase : r ≫ f = ((V.ι ≫ Q) ∣_ T) ≫ T.ι := by
    rw [morphismRestrict_ι, ← hQ, ← Category.assoc r, retainedBaseToOriginal_comp]
    simp only [Category.assoc]
  have hfield : f ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (MvPolynomial.aeval (fun i => aeval g (parameterTuple k σ d c i).val)).commutes x
  refine ⟨{
    base := Γ(T.toScheme, ⊤)
    base_noetherian := (restrictedBaseCoefficientMap_properties k R T).1
    toField := tK
    base_smooth := inferInstance
    target := (retainedBaseOpen Q T V).toScheme
    target_affine := hVaT
    refinement := r
    refinement_open := inferInstance
    point := ⟨⟨i (P i₀), hwhole i₀ (P i₀) rfl⟩, hxT⟩
    point_eq := retainedBaseToOriginal_point i Q T V hV (P i₀) (hwhole i₀ (P i₀) rfl) hxT
    compact := (Q ⁻¹ᵁ T).toScheme
    compact_integral := hCn
    compact_noetherian := hCnoeth
    compact_normal := fun x => (hCnormal x).2
    projectiveMap := πT
    projective_finite := hπT
    inclusion := j
    inclusion_open := inferInstance
    target_smooth := finiteProjectiveBaseRestriction_retained_smooth R _ π T V
    base_compatibility := ?_
    closed := ((zJ ≫ f) ⁻¹ᵁ T).toScheme
    closedToOriginal := ((zJ ≫ f) ⁻¹ᵁ T).ι
    closedInclusion := zT
    closed_cartesian := prescribedBaseToRetained_isPullback i Q f htail T V hV zJ hzJ
    closed_finite := ?_
    closedLift := sT
    closedLift_original := retainedEtaleClosedLift_fst i Q f htail T V hV zJ hzJ p s hs
    closedLift_eq := retainedEtaleClosedLift_snd i Q f htail T V hV zJ hzJ p s hs
    closedLift_closed := retainedEtaleClosedLift_closed i Q f htail T V hV zJ hzJ p s hs H
    closedLift_cartesian := retainedEtaleClosedLift_isPullback i Q f htail T V hV zJ hzJ p s hs H
    punctured_disjoint := retainedPunctured_disjoint i Q f htail T V hV zJ hzJ a ha
    punctured_cover := retainedPunctured_cover i Q f htail T V hV zJ hzJ a hcover
    boundary := _
    boundaryInclusion := dT
    boundary_closed := hdClosed
    boundary_finite := ?_
    goodOpen := r ⁻¹ᵁ U
    good_finite := Scheme.finite_pullback_on_original_chart p r U
    bad_cover := ?_ }, ?_⟩
  · rw [← hfield, ← Category.assoc, hrbase]
    simp only [πT, tK, Category.assoc, finiteProjectiveBaseRestriction_toSpec_assoc,
      Iso.hom_inv_id_assoc]
    exact (retainedBaseInclusion_projection_assoc Q T V _).symm
  · change IsFinite (zT ≫ j ≫ πT ≫ ProjectiveSpace.toSpec _ _)
    rw [finiteProjectiveBaseRestriction_toSpec, retainedBaseInclusion_projection_assoc,
      ← Category.assoc]
    infer_instance
  · change IsFinite (dT ≫ πT ≫ ProjectiveSpace.toSpec _ _)
    rw [finiteProjectiveBaseRestriction_toSpec, ← Category.assoc]
    infer_instance
  · simpa only [r, j, dT, zIN, zI, Scheme.Hom.coe_image,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      using retained_base_bad_chart_cover B I i Q T V hV U hU


  · intro j
    have hxTj : Q (i (P j)) ∈ T := by
      change (i ≫ Q) (P j) ∈ T
      rw [htail]
      exact ht j
    refine ⟨⟨⟨i (P j), hwhole j (P j) rfl⟩, hxTj⟩, ?_⟩
    exact retainedBaseToOriginal_point i Q T V hV (P j) (hwhole j (P j) rfl) hxTj


open ProjectiveSpace Motivic Motivic.OneSidedMovingEndpoints
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.Hom Scheme.Moving Scheme.RelativeCurvePencil

/-- The full preimage of a finite base set has a common frame; the actual finite
scheme, including nilpotents, is retained above the resulting base open. -/
theorem exists_finitelyMany_base_open_unitIso {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Y) [IsFinite f] (s : Set Y) (hs : s.Finite) (L : LineBundle X) :
    ∃ U : Y.Opens, s ⊆ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj L.val ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  have hf : (f ⁻¹' s).Finite := by
    convert hs.biUnion (fun y _ => f.finite_preimage_singleton y) using 1
    ext x
    simp
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_open_unitIso_around_finite X L (f ⁻¹' s) hf
  let U : Y.Opens := ⟨(f '' (V : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hUV : f ⁻¹ᵁ U ≤ V := by
    intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  refine ⟨U, ?_, ⟨restrictUnitIsoOfLE L.val hUV e⟩⟩
  rintro y hy ⟨x, hx, rfl⟩
  exact hx (hV hy)

/-- A finite set lying in an open of an affine scheme has one affine
neighborhood still lying in that open. -/
theorem exists_affineOpen_inside_finitelyMany {X : Scheme.{u}} [IsAffine X]
    (U : X.Opens) (s : Set X) (hs : s.Finite) (hsU : s ⊆ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ s ⊆ W ∧ W ≤ U := by
  obtain ⟨r, hr, hrU⟩ := PrimeSpectrum.exists_basicOpen_of_finite_subset
    (X.toSpecΓ ''ᵁ U) (X.toSpecΓ '' s) (hs.image _) (Set.image_mono hsU)
  refine ⟨X.basicOpen r, (isAffineOpen_top X).basicOpen r, ?_, ?_⟩
  · intro x hx
    rw [← X.toSpecΓ_preimage_basicOpen]
    exact hr (Set.mem_image_of_mem _ hx)
  · intro x hx
    rw [← X.toSpecΓ_preimage_basicOpen] at hx
    obtain ⟨y, hy, he⟩ := hrU hx
    exact (Scheme.Hom.injective X.toSpecΓ he) ▸ hy

/-- One actual affine source neighborhood retains all selected points and the
entire prescribed boundary over a common base neighborhood. -/
theorem exists_finitelyMany_affine_relativeBoundaryFrame
    {S X Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    [SmoothOfRelativeDimension 1 q] [IsAffine X]
    (z : Z ⟶ X) [IsFinite (z ≫ q)] (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ ∃ V : S.Opens, q '' s ⊆ V ∧
      (∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U) ∧
      Nonempty ((idealModule (boundaryGraphTarget q z)).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let f := z ≫ q
  let P : Set X := s ∪ z '' (f ⁻¹' (q '' s))
  have hf : (f ⁻¹' (q '' s)).Finite := by
    convert (hs.image q).biUnion (fun y _ => f.finite_preimage_singleton y) using 1
    ext x
    simp [eq_comm]
  have hP : P.Finite := hs.union (hf.image z)
  obtain ⟨U, hU, ⟨e⟩⟩ := exists_relativeBoundaryFrame_around_finite q z P hP
  obtain ⟨W, hW, hPW, hWU⟩ := exists_affineOpen_inside_finitelyMany U P hP hU
  let V : S.Opens := ⟨(f '' (z ⁻¹' (W : Set X))ᶜ)ᶜ,
    (f.isClosedMap _ ((W.isOpen.preimage z.continuous).isClosed_compl)).isOpen_compl⟩
  refine ⟨W, hW, fun x hx => hPW (Or.inl hx), V, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩ ⟨t, ht, he⟩
    exact ht (hPW (Or.inr ⟨t, ⟨x, hx, he.symm⟩, rfl⟩))
  · intro t ht
    change f t ∉ f '' (z ⁻¹' (W : Set X))ᶜ at ht
    by_contra hn
    exact ht ⟨t, hn, rfl⟩
  · exact ⟨restrictUnitIsoOfLE (relativeBoundaryGraphLine q z).val
      (fun _ hx => hWU hx) e⟩

/-- The two required frames are genuinely produced, and both already use the native
spectrum presentation and projective twists of exactly the same smaller affine base. -/
theorem exists_finitelyMany_native_boundary_frames
    (R : Type u) [CommRing R] (ι : Type u)
    {X Z C D : Scheme.{u}} [IsAffine X]
    (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (z : Z ⟶ X) [IsFinite (z ≫ q)]
    (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C)
    [IsFinite ((d ≫ f) ≫ toSpec R ι)] (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q '' s ⊆ V ∧
      ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
        IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
        Nonempty (SheafOfModules.unit
          (pullback (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom)
            (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V ≫
              V.toScheme.isoSpec.hom)).ringCatSheaf ≅
          idealModule (boundaryGraphTarget
            (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom)
            (boundaryBaseLift q z U V h))) ∧
        Nonempty ((n : ℕ) →
          (Modules.pullback (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫
            boundaryBaseProjectiveMap R ι f V)).obj
              (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
          SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  obtain ⟨U, hU, hx, V₁, hx₁, hz, ⟨a⟩⟩ :=
    exists_finitelyMany_affine_relativeBoundaryFrame q z s hs
  let b := d ≫ (f ≫ toSpec R ι)
  have : IsFinite b := by simpa only [b, Category.assoc] using
    (inferInstance : IsFinite ((d ≫ f) ≫ toSpec R ι))
  let L := pullbackLineBundle (d ≫ f) (twistingLineBundle R ι 1)
  have : IsAffine D := isAffine_of_isAffineHom b
  obtain ⟨V₂, hx₂, ⟨e₂⟩⟩ := exists_finitelyMany_base_open_unitIso b (q '' s) (hs.image q) L
  obtain ⟨V, hV, hxV, hVV⟩ := exists_affineOpen_inside_finitelyMany
    (V₁ ⊓ V₂) (q '' s) (hs.image q) (fun y hy => ⟨hx₁ hy, hx₂ hy⟩)
  let : IsAffine V.toScheme := hV
  let h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U := fun t ht => hz t (hVV ht).1
  let W := b ⁻¹ᵁ V
  let eW := restrictUnitIsoOfLE L.val
    (show W ≤ b ⁻¹ᵁ V₂ from fun _ ht => (hVV ht).2) e₂
  let e₁ : (Modules.pullback (W.ι ≫ d ≫ f)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι (d ≫ f)).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback (d ≫ f)).obj (twistingSheaf R ι 1)) ≪≫ eW
  let e := CoherentGraph.positiveTwistUnitIso R ι (W.ι ≫ d ≫ f) e₁
  have := boundaryBaseSourceProjection_smooth q U V
  have : IsSeparated (boundaryBaseSourceProjection q U V) := by
    dsimp [boundaryBaseSourceProjection]
    infer_instance
  refine ⟨U, hU, hx, V, hV, hxV, h, boundaryBaseSourceOpen_affine q U V hU hV,
    ⟨boundaryGraphFrameBaseIso _ _ V.toScheme.isoSpec
      (boundaryBaseCanonicalFrame q z U V h a)⟩,
    ⟨fun n => boundaryBaseWholeTwistFrame R ι f d V n (e n)⟩⟩


open Motivic Motivic.OneSidedMovingEndpoints
open Scheme.Moving Scheme.RelativeCurvePencil

section Moving
variable {k : Type u} [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1)) [Finite ι]
  {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine A.left]
  {C Z D : Scheme.{u}} (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (x : X.left ⟶ C) [IsOpenImmersion x]
  [SmoothOfRelativeDimension 1 (x ≫ (f ≫ toSpec R ι))]
  (a : A ⟶ X) [IsOpenImmersion a.left]
  (t : Spec (.of R) ⟶ Spec (.of k))
  (hbase : (x ≫ (f ≫ toSpec R ι)) ≫ t = X.hom)
  (z : Z ⟶ X.left) [IsClosedImmersion (z ≫ x)]
  (d : D ⟶ C) [IsClosedImmersion d]
  (hd : Disjoint (Set.range x) (Set.range d))
  (hX : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d)
  (hA : ∀ c : C, c ∈ Set.range (a.left ≫ x) ∨
    c ∈ Set.range d ∨ c ∈ Set.range (z ≫ x))
  (U : X.left.Opens) (W : (Spec (.of R)).Opens) [IsAffine W.toScheme]
  [IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme]
  (h : ∀ b : Z, (z ≫ (x ≫ f ≫ toSpec R ι)) b ∈ W → z b ∈ U)

include eι hbase hd hX hA in
private theorem finitePoint_moving_on_refinement
    (e : SheafOfModules.unit
      (pullback (boundaryBaseSpecProjection (x ≫ f ≫ toSpec R ι) U W)
        (boundaryBaseLift (x ≫ f ≫ toSpec R ι) z U W h ≫
          boundaryBaseSpecProjection (x ≫ f ≫ toSpec R ι) U W)).ringCatSheaf ≅
        idealModule (boundaryGraphTarget
          (boundaryBaseSpecProjection (x ≫ f ≫ toSpec R ι) U W)
          (boundaryBaseLift (x ≫ f ≫ toSpec R ι) z U W h)))
    (eF : ∀ m : ℕ, (Scheme.Modules.pullback
      (boundaryBaseWholeMap (f ≫ toSpec R ι) (coprod.desc d (z ≫ x)) W ≫
        boundaryBaseProjectiveMap R ι f W)).obj
      (twistingSheaf Γ(W.toScheme, ⊤) ι (m : ℤ)) ≅
        SheafOfModules.unit
          ((coprod.desc d (z ≫ x) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ W).toScheme.ringCatSheaf) :
    HasMovingEndpoints (refinedSourceToOriginal X (x ≫ f ≫ toSpec R ι) U W) a := by
  let π := f ≫ toSpec R ι
  let q := x ≫ π
  let f' := boundaryBaseProjectiveMap R ι f W
  let j' := refinedParameterInclusion q π x rfl U W
  let x' := boundaryBaseRetainedTarget π W x
  let z' := boundaryBaseLift q z U W h
  let d' := boundaryBaseWholeMap π d W
  let S' := refinedSourceSite X q U W
  let X' := refinedTargetSite X q W
  let A' := refinedGoodSite X q W a
  let φ' := refinedSourceToTarget X q U W
  let a' := refinedGoodToTarget X q W a
  have : IsAffine S'.left :=
    inferInstanceAs (IsAffine (boundaryBaseSourceOpen q U W).toScheme)
  have : IsAffine X'.left := inferInstanceAs (IsAffine (q ⁻¹ᵁ W).toScheme)
  have : IsAffine A'.left := inferInstanceAs (IsAffine ((a.left ≫ q) ⁻¹ᵁ W).toScheme)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherianRing Γ(S'.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ(W.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsLocallyNoetherian (boundaryBaseCompactification π W) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst W.ι π)
  have : IsLocallyNoetherian (pullback (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι))
      (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have hS : (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) ≫ boundaryBaseFieldMap W t = S'.hom := by
    rw [refinedParameterInclusion_projective]
    simp only [boundaryBaseSpecProjection, boundaryBaseFieldMap, Category.assoc,
      Iso.hom_inv_id_assoc, boundaryBaseSourceProjection_ι_assoc]
    rw [hbase]
    rfl
  have hXt : (x' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) ≫ boundaryBaseFieldMap W t = X'.hom := by
    rw [boundaryBaseProjectiveMap_toSpec]
    simp only [boundaryBaseFieldMap, Category.assoc, Iso.hom_inv_id_assoc,
      pullback.condition_assoc]
    change boundaryBaseWholeMap π x W ≫ pullback.snd W.ι π ≫ π ≫ t = _
    rw [boundaryBaseWholeMap_snd_assoc]
    rw [← Category.assoc x π, hbase]
    rfl
  have hφ : φ'.left ≫ x' = j' := refinedParameterToTarget_inclusion q π x rfl U W
  have ha : a'.left ≫ x' = boundaryBaseRetainedTarget π W (a.left ≫ x) := by
    apply (cancel_mono (pullback.snd W.ι π)).mp
    change (a.left ∣_ (q ⁻¹ᵁ W)) ≫ x' ≫ pullback.snd W.ι π = _
    simp only [x', boundaryBaseRetainedTarget, boundaryBaseWholeMap_snd]
    exact morphismRestrict_ι_assoc a.left (q ⁻¹ᵁ W) x
  have he : SheafOfModules.unit
      (pullback (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι))
        (z' ≫ (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)))).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι)) z') := by
    have hproj : j' ≫ (f' ≫ toSpec Γ(W.toScheme, ⊤) ι) =
        boundaryBaseSpecProjection q U W :=
      refinedParameterInclusion_projective R ι f q x rfl U W
    rw [hproj]
    exact e
  have hcA : ∀ c : boundaryBaseCompactification π W,
      c ∈ Set.range (a'.left ≫ x') ∨ c ∈ Set.range d' ∨ c ∈ Set.range (z' ≫ j') := by
    rw [ha]
    exact refinedGood_cover q π x rfl U W z h d a.left hA
  have hm := exists_moving_endpoints_of_relative_frames
    (S := S') (X := X') (V := A') Γ(W.toScheme, ⊤) ι n eι f' j' x' a' φ' hφ
    (boundaryBaseFieldMap W t) hS hXt z' d'
    (refinedParameter_disjoint q π x rfl U W d hd)
    (boundaryBaseWholeTarget_cover π d W x hX) hcA he
    (fun m => refinedFullTwistFrame R ι f x U W z h d m (eF m))
  have hm' := hm.postcompose (refinedTargetToOriginal X q W)
    (refinedGoodToOriginal X q W a) a (refinedGoodToTarget_original X q W a)
  simpa only [φ', refinedSourceToTarget_original] using hm'

include eι hbase hd hX hA in
omit [IsAffine W.toScheme]
  [IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme] in
/-- Every finite parameter set has one actual Zariski neighborhood with a constructed
moving correspondence and homotopy. Only a genuine good curve presentation is
assumed; all boundary frames, sections and zero families are produced internally. -/
theorem exists_finitelyMany_moving_of_curve_presentation
    [IsFinite (z ≫ (x ≫ f ≫ toSpec R ι))]
    [IsFinite ((coprod.desc d (z ≫ x) ≫ f) ≫ toSpec R ι)]
    (points : Set X.left) (hpoints : points.Finite) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ points ⊆ U ∧
    ∃ (W : (Spec (.of R)).Opens) (hW : IsAffineOpen W),
      let : IsAffine W.toScheme := hW
      (x ≫ f ≫ toSpec R ι) '' points ⊆ W ∧
      ∃ hO : IsAffineOpen (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W),
        let : IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme := hO
        HasMovingEndpoints (refinedSourceToOriginal X (x ≫ f ≫ toSpec R ι) U W) a := by
  obtain ⟨U, hU, hpU, W, hW, hpW, h, hO, ⟨e⟩, ⟨eF⟩⟩ :=
    exists_finitelyMany_native_boundary_frames R ι (x ≫ f ≫ toSpec R ι)
      z f (coprod.desc d (z ≫ x)) points hpoints
  let : IsAffine W.toScheme := hW
  let : IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme := hO
  refine ⟨U, hU, hpU, W, hW, hpW, hO, ?_⟩
  exact finitePoint_moving_on_refinement R ι n eι f x a t hbase z d hd hX hA U W h e eF



end Moving

section ExistingPresentation
variable {k : Type u} [Field k] {X A : SmoothSite (Spec (.of k))}
  [IsAffine X.left] [IsAffine A.left] {Y Z : Scheme.{u}}
  (p : Y ⟶ X.left) (a : A ⟶ X) [IsOpenImmersion a.left]
  (z : Z ⟶ X.left) [IsClosedImmersion z] (s : Z ⟶ Y) (x : X.left)
  (e : OriginalEtalePresentation k X.hom p a.left z s x)
local instance localVanishingBaseNoetherian : IsNoetherianRing e.base := e.base_noetherian
local instance localVanishingTargetAffine : IsAffine e.target := e.target_affine
local instance localVanishingRefinementOpen : IsOpenImmersion e.refinement := e.refinement_open
local instance localVanishingProjectiveFinite : IsFinite e.projectiveMap := e.projective_finite
local instance localVanishingInclusionOpen : IsOpenImmersion e.inclusion := e.inclusion_open
local instance localVanishingCompactLocallyNoetherian : IsLocallyNoetherian e.compact :=
  e.compact_noetherian
local instance localVanishingTargetLocallyNoetherian : IsLocallyNoetherian e.target :=
  LocallyOfFiniteType.isLocallyNoetherian e.inclusion
local instance localVanishingTargetNoetherian : IsNoetherian e.target := {}
local instance localVanishingRelativeSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth
local instance localVanishingClosedFinite : IsFinite
    (e.closedInclusion ≫ e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) :=
  e.closed_finite


/-- On a constructed original-data presentation, one actual moving
correspondence and one A1-homotopy work simultaneously at every selected point. -/
theorem exists_finitelyMany_moving_on_presentation
    (points : Set e.target) (hpoints : points.Finite) :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ X),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧
      e.refinement '' points ⊆ Set.range r.left ∧ HasMovingEndpoints r a := by
  let T : SmoothSite (Spec (.of k)) := SmoothSite.mk (e.refinement ≫ X.hom)
  let B : SmoothSite (Spec (.of k)) :=
    SmoothSite.mk (pullback.fst a.left e.refinement ≫ A.hom)
  let r : T ⟶ X := SmoothSite.homMk e.refinement rfl
  let j : B ⟶ T := SmoothSite.homMk (pullback.snd a.left e.refinement) (by
    change pullback.snd a.left e.refinement ≫ e.refinement ≫ X.hom =
      pullback.fst a.left e.refinement ≫ A.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
    exact congrArg (fun f => pullback.fst a.left e.refinement ≫ f) a.w)
  let b : B ⟶ A := SmoothSite.homMk (pullback.fst a.left e.refinement) rfl
  have : IsAffine T.left := e.target_affine
  have : IsAffine B.left := inferInstanceAs (IsAffine (pullback a.left e.refinement))
  have : IsClosedImmersion e.closedInclusion :=
    MorphismProperty.of_isPullback e.closed_cartesian inferInstance
  have : IsFinite ((e.closedInclusion ≫ e.inclusion) ≫
      e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := by
    simpa only [Category.assoc] using e.closed_finite
  have : IsClosedImmersion (e.closedInclusion ≫ e.inclusion) :=
    prescribed_closed_in_compactification e.inclusion
      (e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) e.closedInclusion
  have : IsFinite (e.missingInclusion ≫ e.projectiveMap ≫
      ProjectiveSpace.toSpec e.base _) := e.missing_finite
  have : IsFinite ((coprod.desc e.missingInclusion (e.closedInclusion ≫ e.inclusion) ≫
      e.projectiveMap) ≫ ProjectiveSpace.toSpec e.base _) := by
    rw [Category.assoc, coprod.desc_comp]
    infer_instance
  have hd : Disjoint (Set.range e.inclusion) (Set.range e.missingInclusion) := by
    rw [e.missing_range]
    exact disjoint_compl_right
  have hX : ∀ c, c ∈ Set.range e.inclusion ∨ c ∈ Set.range e.missingInclusion := by
    intro c
    rw [e.missing_range]
    exact Classical.em _
  have hA : ∀ c, c ∈ Set.range (j.left ≫ e.inclusion) ∨
      c ∈ Set.range e.missingInclusion ∨ c ∈ Set.range (e.closedInclusion ≫ e.inclusion) := by
    intro c
    rcases hX c with ⟨y, rfl⟩ | hc
    · rcases e.punctured_cover y with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact Or.inl ⟨v, rfl⟩
      · exact Or.inr (Or.inr ⟨v, rfl⟩)
    · exact Or.inr (Or.inl hc)
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left e.refinement))
  have hj : j ≫ r = b ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm

  obtain ⟨U, hU, hpU, W, hW, hpW, hO, hm⟩ :=
    exists_finitelyMany_moving_of_curve_presentation (X := T) (A := B)
      e.base (ULift.{u} (Fin 2)) 1 Equiv.ulift e.projectiveMap e.inclusion j
      e.toField e.base_compatibility.symm e.closedInclusion e.missingInclusion
      hd hX hA points hpoints
  let q := e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _
  let : IsAffine W.toScheme := hW
  let : IsAffine (boundaryBaseSourceOpen q U W).toScheme := hO
  let S := refinedSourceSite T q U W
  let r' : S ⟶ X := refinedSourceToOriginal T q U W ≫ r
  have hr' : IsOpenImmersion r'.left := by
    change IsOpenImmersion ((boundaryBaseSourceOpen q U W).ι ≫ e.refinement)
    infer_instance
  refine ⟨S, r', hO, hr', ?_, hm.postcompose r b a hj⟩
  rintro y ⟨t, ht, rfl⟩
  exact ⟨⟨t, ⟨hpU ht, hpW ⟨t, ht, rfl⟩⟩⟩, rfl⟩

end ExistingPresentation


section OriginalAffine
open Motivic.PresheafWithTransfers

/-- A genuine simultaneous moving correspondence on the original affine
scheme, constructed from the original finite set and dense affine puncture.
It is independent of any presheaf, section, local-zero or comparison hypothesis. -/
theorem exists_finitelyMany_original_moving
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] {τ : Type u} [Fintype τ]
    (points : τ → PrimeSpectrum B) [∀ j, (points j).asIdeal.IsMaximal] (i₀ : τ)
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    ∃ (S : SmoothSite (Spec (.of k))) (r : S ⟶ originalAffineObject k B),
      IsAffine S.left ∧ IsOpenImmersion r.left ∧
      (∀ j : τ, points j ∈ Set.range r.left) ∧ HasMovingEndpoints r a := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsAffine (originalAffineObject k B).left := inferInstanceAs (IsAffine (Spec (.of B)))
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have H : IsPullback z (𝟙 _) (𝟙 _) z := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he⟩ := exists_finitelyMany_originalEtalePresentation k B points i₀ J hJ g hg d hd
    (𝟙 _) a.left z (by simp only [Category.comp_id]; rfl) H ha hcover
  have : IsAffine e.target := e.target_affine
  have : IsOpenImmersion e.refinement := e.refinement_open
  let T : Set e.target := e.refinement ⁻¹' Set.range points
  have hT : T.Finite := (Set.finite_range points).preimage
    e.refinement.isOpenEmbedding.injective.injOn
  obtain ⟨S, r, hS, hr, hTr, hm⟩ := exists_finitelyMany_moving_on_presentation
    (X := originalAffineObject k B) (A := A) (𝟙 _) a z z (points i₀) e T hT
  refine ⟨S, r, hS, hr, ?_, hm⟩
  intro j
  obtain ⟨y, hy⟩ := he j
  apply hTr
  have hyT : y ∈ T := by
    change e.refinement y ∈ Set.range points
    rw [hy]
    exact Set.mem_range_self j
  exact ⟨y, hyT, hy⟩

end OriginalAffine
end MathGauge.GP003.S5Simultaneous
