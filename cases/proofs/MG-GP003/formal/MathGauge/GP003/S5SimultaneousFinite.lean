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
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarComparison
import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.ScalarCoordinates
import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineScalarClosedSquare
import MathGauge.GP003.S5SimultaneousUniversal
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.ChosenOriginalEtalePresentation
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LargePrimeCompactification
import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg

/-! Finite-point parameter choice over the same two genuine coprime extensions. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module TensorProduct
open KaehlerDifferential MvPolynomial
open scoped TensorProduct
universe u
namespace MathGauge.GP003.S5Simultaneous
open QuadraticIncidence QuadraticIncidence.InfinityChart
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Two actual coprime scalar extensions admit one unchanged tuple smooth on
all relative fibres above all lifts of every selected original closed point.
All diagonal norms and off-diagonal relations are formed over the original
field before either extension is chosen. -/
theorem exists_two_prime_finitelyMany_parameters
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {τ : Type u} [Fintype τ] (points : τ → PrimeSpectrum R)
    [∀ j, (points j).asIdeal.IsMaximal] (i₀ : τ)
    (I : Ideal R) (hI : I ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        let S := R ⊗[k] L
        let gS := algebraMap R S ∘ g
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          (∃! y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap R S) y = points i₀) ∧
          ∃ (a : Exponent σ → L) (c : Fin d × Exponent σ → L),
            eval₂ (algebraMap k L) c q ≠ 0 ∧
            NoCommonClosedInfinityZero L S (I.map (algebraMap R S)) gS d c ∧
            NoCommonInfinityZero L S gS d (prependParameters L d a c) ∧
            (∀ y : PrimeSpectrum S,
              PrimeSpectrum.comap (algebraMap R S) y = points i₀ →
              ∃ s ∉ y.asIdeal,
                ((algebraMap S (Localization.Away s)).comp
                  (aeval (R := L) (fun j => aeval gS
                    (parameterTuple L σ (d + 1)
                      (prependParameters L d a c) j).val)).toRingHom).Etale) ∧
            ∀ j : τ, ∀ y : PrimeSpectrum S,
              PrimeSpectrum.comap (algebraMap R S) y = points j →
              ∀ Q : PrimeSpectrum S,
                Ideal.comap (quadraticCoordinateHom L S gS d c) y.asIdeal =
                  Ideal.comap (quadraticCoordinateHom L S gS d c) Q.asIdeal →
                ∃ s ∉ Q.asIdeal, SmoothOfRelativeDimension 1
                  (Spec.map (CommRingCat.ofHom ((algebraMap S (Localization.Away s)).comp
                    (quadraticCoordinateHom L S gS d c)))) := by
  classical
  have hdim (j : τ) : Module.finrank (points j).asIdeal.ResidueField
      ((points j).asIdeal.ResidueField ⊗[R] KaehlerDifferential k R) = d + 1 := by
    rw [Algebra.residue_cotangent_finrank_eq_trdeg_toNat k R (points j).asIdeal,
      hd, Cardinal.toNat_natCast]
  choose _ basis _ using fun j => exists_residue_basis_fin_original_functions
    k R (points j).asIdeal.ResidueField (d + 1) (hdim j)
  let : ∀ j : τ, Module.Finite k (points j).asIdeal.ResidueField :=
    fun j => ClosedPoint.residueField_finite k R (points j)
  choose f hf hz using fun j => MovingPointChart.exists_nonzero_common_parameter_relation
    k R (ClosedPoint.CoefficientRing k R (points j)) g hg
      (fun a => ClosedPoint.selectedValue k R (points j) (g a)) d hd
  let D : τ → MvPolynomial (Fin d × Exponent σ) k := fun j =>
    residueParameterNorm k (points j).asIdeal.ResidueField
      (selectedDeterminant d (basis j)
        (selectedDerivative (k := k) (L := (points j).asIdeal.ResidueField) g))
  have hD : ∀ j, D j ≠ 0 := fun j => residueParameterNorm_ne_zero k _ _
    (selectedDeterminant_ne_zero d (basis j) _ (selectedDerivative_surjective g hg))
  have hprod : q * ∏ j, f j * D j ≠ 0 :=
    mul_ne_zero hq (Finset.prod_ne_zero_iff.mpr (fun j _ => mul_ne_zero (hf j) (hD j)))
  obtain ⟨n, m, hn, hm, hnm, h⟩ := exists_two_prime_quadratic_etale_infinity
    k R p (points i₀) I hI g hg d
      (by simpa only [Nat.cast_add, Nat.cast_one] using hd.le) (basis i₀)
      (f i₀) (q * ∏ j, f j * D j) (hf i₀) hprod N₀
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdegree, hdom, hunique, a, c, _, hextra, hW, hZ, _, hetale⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  let S := R ⊗[k] L
  let : IsDomain S := hdom
  have hextra' : (eval₂Hom (algebraMap k L) c) (q * ∏ j, f j * D j) ≠ 0 := hextra
  rw [map_mul, map_prod] at hextra'
  have hq' := (mul_ne_zero_iff.mp hextra').1
  have hprod' := (mul_ne_zero_iff.mp hextra').2
  have hfactor (j : τ) : eval₂ (algebraMap k L) c (f j) ≠ 0 ∧
      eval₂ (algebraMap k L) c (D j) ≠ 0 := by
    have hj := Finset.prod_ne_zero_iff.mp hprod' j (Finset.mem_univ j)
    change eval₂ (algebraMap k L) c (f j * D j) ≠ 0 at hj
    rw [eval₂_mul] at hj
    exact mul_ne_zero_iff.mp hj
  refine ⟨hdegree, hdom, hunique, a, c, hq', hZ, hW, hetale, ?_⟩
  intro j y hy Q hQ
  apply exists_scalar_wholeFiber_smooth_projection k R L (points j) y hy
    g hg d (basis j) (f j) c (hfactor j).1 (hz j) _ hd Q hQ
  exact isUnit_residueParameter_of_eval₂_norm_ne_zero k _ L _ c (hfactor j).2


open AlgebraicGeometry.Scheme.RelativeCurve

/-- Assemble actual geometry from chosen original parameters. No cardinality
assumption or parameter-choice theorem is used. The prescribed quotient stays
nonreduced and its original quotient map is retained. -/
theorem exists_finitelyMany_chosen_quadratic_compactification
    (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] {τ : Type u} [Fintype τ]
    (P : τ → PrimeSpectrum B) [∀ j, (P j).asIdeal.IsMaximal] (i₀ : τ)
    (I : Ideal B) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (hZ : NoCommonClosedInfinityZero k B I g d c)
    (hW : NoCommonInfinityZero k B g d (prependParameters k d a c))
    (he : ∃ r ∉ (P i₀).asIdeal, ((algebraMap B (Localization.Away r)).comp
      (aeval (R := k) (fun i => aeval g
        (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale)
    (hs : ∀ j : τ, ∀ Q : PrimeSpectrum B,
      Ideal.comap (quadraticCoordinateHom k B g d c) (P j).asIdeal =
        Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal →
      ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
        (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away r)).comp
          (quadraticCoordinateHom k B g d c))))) :
      IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      (∃ r : B,
        (∀ j, r - 1 ∈ Ideal.map (quadraticCoordinateHom k B g d c)
          (Ideal.comap (quadraticCoordinateHom k B g d c) (P j).asIdeal)) ∧
        (∀ j : τ, ∀ Q : PrimeSpectrum B,
          Ideal.comap (quadraticCoordinateHom k B g d c) (P j).asIdeal =
            Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)))) ∧
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2))) (b : D ⟶ N),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨r₀, hr₀, hf₀, hsm₀⟩ := exists_finitelyMany_closedFiber_principal_smooth k
    (MvPolynomial (Fin d) k) B
    (aeval (R := k) (fun i => aeval g (parameterTuple k σ d c i).val)) P 1 hs
  obtain ⟨r, hr, he⟩ := he
  exact ⟨quadraticClosedTuple_isFinite k B g d I hg c hZ,
    ⟨r₀, hr₀, hf₀,
      IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of B) r₀).hom, hsm₀⟩,
    exists_quadratic_normal_compactification k B g hg d a c hW (P i₀) r hr he⟩


/-- Retain the entire prescribed quotient using the given compactification and
quadratic parameters. No parameter choice or field-cardinality hypothesis is used. -/
theorem exists_finitelyMany_chosen_retained_presentation
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    {τ : Type u} [Fintype τ] (P : τ → PrimeSpectrum B)
    (I : Ideal B) {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (hcompact : IsFinite (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c)))) ∧
      (∃ r : B,
        (∀ j, r - 1 ∈ Ideal.map (quadraticCoordinateHom k B g d c)
          (Ideal.comap (quadraticCoordinateHom k B g d c) (P j).asIdeal)) ∧
        (∀ j : τ, ∀ Q : PrimeSpectrum B,
          Ideal.comap (quadraticCoordinateHom k B g d c) (P j).asIdeal =
            Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
        IsAffine (Scheme.Opens.toScheme (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ∧
        SmoothOfRelativeDimension 1
          (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
            Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c)))) ∧
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2))) (b : D ⟶ N),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a c)) ≫
        RelativeProjectiveLine.chart (MvPolynomial (Fin d) k) 0 ∧
      i ≫ π ≫ ProjectiveSpace.toSpec (MvPolynomial (Fin d) k) _ =
        Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c))) :
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
  obtain ⟨hZ, ⟨r, _, hr, ha, hs⟩,
    N, D, i, π, b, hN, hNoeth, hnormal, hi, hπ, hb, hbfin, hbrange, hfull, htail⟩ :=
    hcompact
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
  refine ⟨N, i, π, i ''ᵁ v, t, hN, hNoeth, hnormal, hi, hπ,
    hfull, htail, ?_, ?_, hva, hvs, fun j => ht (Set.mem_range_self j), hbf, hav, hZ, ?_⟩
  · intro j x hx
    exact ⟨x, hwhole j x hx, rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · intro x hx
    apply hretain x
    simpa only [hzcomp] using hx



/-- Chosen retained geometry and the original fixed finite-locus data supply
an actual original étale presentation over any field. No new ideal or tuple is chosen. -/
theorem exists_finitelyMany_originalEtalePresentation_of_chosen_retained
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    {τ : Type u} [Fintype τ] (P : τ → PrimeSpectrum B) (i₀ : τ)
    (I J : Ideal B) (hIJ : I ≤ J) {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a₀ : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (hretained : ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace (MvPolynomial (Fin d) k) (ULift.{u} (Fin 2)))
      (V : N.Opens) (t : MvPolynomial (Fin d) k),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧
      i ≫ π = Spec.map (CommRingCat.ofHom (quadraticRelativeCoordinateHom k B g d a₀ c)) ≫
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
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) z ∈ V)
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ)
    (hpU : IsFinite (p ∣_ U)) :
    ∃ e : OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s (P i₀),
      ∀ j : τ, P j ∈ Set.range e.refinement := by
  obtain ⟨N, i, π, V, t,
    hN, hNoeth, hnormal, hi, hπ, _, htail, hwhole, hV, hVa, hVs,
    ht, hbfin, hVaT, hIfin, hIret⟩ := hretained
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


open Motivic Motivic.OneSidedMovingEndpoints
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

/-- The two actual coprime extensions carry one moving correspondence each on
an open containing the full preimage of every original marked closed point.
The targets are the literal native base change and original good-open map. -/
theorem exists_two_prime_finitelyMany_native_moving
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {τ : Type u} [Fintype τ] (points : τ → PrimeSpectrum B)
    [∀ j, (points j).asIdeal.IsMaximal] (i₀ : τ)
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        let F := fieldBaseChange (algebraMap k L)
        Module.finrank k L = r ∧
          ∃ (S : SmoothSite (Spec (.of L))) (v : S ⟶ F.obj (affineSite k B)),
            IsAffine S.left ∧ IsOpenImmersion v.left ∧
            ((fieldBaseChangeForgetProjection (L := L) (affineSite k B)).left ⁻¹'
              Set.range points) ⊆ Set.range v.left ∧
            HasMovingEndpoints v (F.map a) := by
  classical
  obtain ⟨n, m, hn, hm, hnm, h⟩ := exists_two_prime_finitelyMany_parameters
    k B p points i₀ J hJ g hg d hd 1 one_ne_zero N₀
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdegree, hdom, hyunique, a₀, c, _, hZ, hW, hetale, hsm⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  let R := B ⊗[k] L
  let gR := algebraMap B R ∘ g
  let : IsDomain R := hdom
  let : Algebra.Smooth L R :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap B R))
  have : IsFinite ρ :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap B R))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  let marks : Set (PrimeSpectrum R) := ρ ⁻¹' Set.range points
  have hmarks : marks.Finite := by
    convert (Set.finite_range points).biUnion (fun y _ => ρ.finite_preimage_singleton y) using 1
    ext x
    simp [marks, eq_comm]
  let Y := marks
  let : Fintype Y := hmarks.fintype
  let P : Y → PrimeSpectrum R := Subtype.val
  let : ∀ y : Y, (P y).asIdeal.IsMaximal := fun y => by
    obtain ⟨j, hj⟩ := y.property
    have hxy : (P y).asIdeal.under B = (points j).asIdeal :=
      congrArg PrimeSpectrum.asIdeal hj.symm
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (P y).asIdeal
      (by rw [hxy]; infer_instance)
  obtain ⟨y₀, hy₀, _⟩ := hyunique
  let j₀ : Y := ⟨y₀, ⟨i₀, hy₀.symm⟩⟩
  have hgR : Algebra.adjoin L (Set.range gR) = ⊤ := by
    let e := Algebra.TensorProduct.commRight k L B
    have ht := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k) (A := L) (Set.range g) hg
    have hm := congrArg (Subalgebra.map e.toAlgHom) ht
    rw [← Algebra.adjoin_image, Algebra.map_top,
      (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective] at hm
    have hset : e '' ((fun x : B => (1 : L) ⊗ₜ[k] x) '' Set.range g) = Set.range gR := by
      rw [← Set.image_comp, ← Set.range_comp]
      rfl
    change Algebra.adjoin L (e '' ((fun x : B => (1 : L) ⊗ₜ[k] x) '' Set.range g)) = ⊤ at hm
    rw [hset] at hm
    exact hm
  have hcompact := exists_finitelyMany_chosen_quadratic_compactification
    L R P j₀ (J.map (algebraMap B R)) gR hgR d a₀ c hZ hW (hetale y₀ hy₀) (by
      intro y Q hQ
      obtain ⟨j, hj⟩ := y.property
      exact hsm j y.1 hj.symm Q hQ)
  have hretained := exists_finitelyMany_chosen_retained_presentation
    L R P (J.map (algebraMap B R)) gR d a₀ c hcompact
  let XS := affineSite L R
  let AS := mk (pullback.snd a.left ρ ≫ XS.hom)
  let aS : AS ⟶ XS := homMk (pullback.snd a.left ρ) rfl
  have : IsAffine XS.left := inferInstanceAs (IsAffine (Spec (.of R)))
  have : IsAffine (affineSite k B).left := inferInstanceAs (IsAffine (Spec (.of B)))
  have : IsAffine AS.left := inferInstanceAs (IsAffine (pullback a.left ρ))
  have : IsOpenImmersion aS.left := inferInstanceAs (IsOpenImmersion (pullback.snd a.left ρ))
  let I := J.map (algebraMap B R)
  let z : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have H : IsPullback z (𝟙 _) (𝟙 _) z := IsPullback.of_vert_isIso ⟨by simp⟩
  let U : (Spec (.of R)).Opens :=
    ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩
  obtain ⟨e, he⟩ := exists_finitelyMany_originalEtalePresentation_of_chosen_retained
    L R P j₀ I I le_rfl gR d a₀ c hretained (𝟙 _) aS.left z
    (by simp only [Category.comp_id]; rfl) H
    (Scheme.quotientBaseChange_punctured_disjoint B R J a.left ha)
    (Scheme.quotientBaseChange_punctured_cover B R J a.left hcover)
    U rfl (by infer_instance)
  have : IsAffine e.target := e.target_affine
  have : IsOpenImmersion e.refinement := e.refinement_open
  let T : Set e.target := e.refinement ⁻¹' marks
  have hT : T.Finite := hmarks.preimage e.refinement.isOpenEmbedding.injective.injOn
  obtain ⟨S, v, hS, hv, hTv, hmove⟩ := exists_finitelyMany_moving_on_presentation
    (X := XS) (A := AS) (𝟙 _) aS z z (P j₀) e T hT
  have hmarkv : marks ⊆ Set.range v.left := by
    intro y hy
    obtain ⟨t, ht⟩ := he ⟨y, hy⟩
    apply hTv
    refine ⟨t, ?_, ht⟩
    change e.refinement t ∈ marks
    rwa [ht]
  let F := fieldBaseChange (algebraMap k L)
  let i := affineScalarIso k B L
  let Hmap := affineScalarMap_isPullback k B L a
  have hc : Hmap.isoPullback.inv ≫ (F.map a).left ≫ i.hom.left = pullback.snd a.left ρ := by
    simpa only [Category.assoc] using Hmap.isoPullback_inv_snd
  let b : AS ⟶ F.obj A := homMk Hmap.isoPullback.inv (by
    change Hmap.isoPullback.inv ≫ (F.obj A).hom = pullback.snd a.left ρ ≫ XS.hom
    rw [← MorphismProperty.Over.w (F.map a), ← MorphismProperty.Over.w i.hom]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ XS.hom) hc)
  have hba : aS ≫ i.inv = b ≫ F.map a := by
    symm
    apply (cancel_mono i.hom).mp
    apply MorphismProperty.Over.Hom.ext
    change (Hmap.isoPullback.inv ≫ (F.map a).left) ≫ i.hom.left =
      (pullback.snd a.left ρ ≫ i.inv.left) ≫ i.hom.left
    have hi : i.inv.left ≫ i.hom.left = 𝟙 _ := congrArg (fun f => f.left) i.inv_hom_id
    simp only [Category.assoc]
    erw [hi, Category.comp_id]
    simpa only [Category.assoc] using hc
  have : IsOpenImmersion v.left := hv
  have hvnative : IsOpenImmersion (v ≫ i.inv).left := by
    change IsOpenImmersion (v.left ≫ i.inv.left)
    infer_instance
  refine ⟨hdegree, S, v ≫ i.inv, hS, hvnative, ?_, hmove.postcompose i.inv b (F.map a) hba⟩
  intro y hy
  have hymark : i.hom.left y ∈ marks := by
    have hproj := congrArg (fun f => f y) (affineScalarIso_hom_original k B L)
    obtain ⟨j, hj⟩ := hy
    exact ⟨j, hj.trans hproj.symm⟩
  obtain ⟨t, ht⟩ := hmarkv hymark
  refine ⟨t, ?_⟩
  change i.inv.left (v.left t) = y
  rw [ht]
  exact congrArg (fun f => f.left y) i.hom_inv_id

end MathGauge.GP003.S5Simultaneous
