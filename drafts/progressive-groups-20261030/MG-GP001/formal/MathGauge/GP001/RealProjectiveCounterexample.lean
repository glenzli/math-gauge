import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
import TwoConeOpenCover
import TwoOpenContractibility
import CoordinateReindex

/-!
MG-GP001 S3. The input is an actual finite triangulation, expressed by a
homeomorphism of its coordinate realization with the antipodal-quotient model
of RP². Its homology is computed, never supplied as an assumption.

The two-cone complex and its distinguished edge are the existing explicit
simplicial constructions. Reduced Mayer–Vietoris for their genuine open cover
transports the integer torsion and the rational vanishing to the whole space.
The borrowed cellular calculation and its exact source closure are recorded in
`vendor/tauceti-real-projective/SOURCE-CLOSURE.json`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set ContinuousMap
open MathGauge.PublicProof.Topology
open scoped Topology Topology.Homotopy

namespace MathGauge.GP001

/-- Actual singular homology of a topological space, with the indicated ring. -/
abbrev SingularHomology (R : Type) [Ring R] (X : Type) [TopologicalSpace X] (n : ℕ) :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).obj (TopCat.of X)

/-- Actual reduced singular homology, including the augmentation kernel in degree zero. -/
abbrev ReducedHomology (R : Type) [Ring R] (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of R R) n).obj (TopCat.of X)

/-- In degree one, the real projective plane has integer homology Z/2. -/
def realProjective_integralH1 :
    SingularHomology ℤ (TauCeti.RealProjectiveSpace 2) 1 ≃ₗ[ℤ] ZMod 2 :=
  TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd
    (N := 2) (k := 1) (by decide) (by decide)

/-- The odd-dimensional rational group is actually zero: twice a rational spans ℚ. -/
theorem realProjective_rationalH1_isZero :
    IsZero (SingularHomology ℚ (TauCeti.RealProjectiveSpace 2) 1) := by
  let e := TauCeti.RealProjectiveSpace.singularHomologyLinearEquivOfOdd
    (N := 2) (k := 1) ℚ (by decide) (by decide)
  have hspan : (ℚ ∙ (2 : ℚ)) = ⊤ := by
    rw [Submodule.span_singleton_eq_top_iff]
    intro x
    exact ⟨x / 2, by simp [smul_eq_mul]⟩
  letI : Subsingleton (ℚ ⧸ ℚ ∙ (2 : ℚ)) := by
    rw [hspan]
    infer_instance
  exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton

/-- All positive rational homology of RP² vanishes, including the even top degree. -/
theorem realProjective_rational_positive_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularHomology ℚ (TauCeti.RealProjectiveSpace 2) n) := by
  by_cases h1 : n = 1
  · subst n
    exact realProjective_rationalH1_isZero
  by_cases h2 : n = 2
  · subst n
    exact TauCeti.RealProjectiveSpace.isZero_singularHomology_of_even ℚ
      (isRegular_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).right
      (by decide) (by decide)
  exact TauCeti.RealProjectiveSpace.isZero_singularHomology_of_lt ℚ (by omega)

/-- Reduced degree zero vanishes by the proved path connectedness of the antipodal quotient. -/
theorem realProjective_reducedRational_isZero (n : ℕ) :
    IsZero (ReducedHomology ℚ (TauCeti.RealProjectiveSpace 2) n) := by
  cases n with
  | zero =>
    exact TauCeti.isZero_reducedSingularHomologyFunctor_zero
      (ModuleCat.of ℚ ℚ) (TopCat.of (TauCeti.RealProjectiveSpace 2))
  | succ n =>
    exact realProjective_rational_positive_isZero (n + 1) (by omega)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The genuine two-open-set cover supplies a coefficient-generic homology shift. -/
def twoConeHomologyIso (R : Type) [Ring R]
    (L : PreAbstractSimplicialComplex V) (n : ℕ) :
    SingularHomology R (Realization (realizing_complex L)) (n + 1) ≅
      ReducedHomology R (Realization L) n := by
  letI := pole_open_contractible L false
  letI := pole_open_contractible L true
  let e := @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ
    (X := TopCat.of (Realization (realizing_complex L))) (ModuleCat.of R R)
    (isOpen_pole_open L false) (isOpen_pole_open L true) (pole_open_cover L) n)
    (TopCat.isIso_reducedMayerVietorisδ_of_contractible
      (X := TopCat.of (Realization (realizing_complex L))) (ModuleCat.of R R)
      (isOpen_pole_open L false) (isOpen_pole_open L true) (pole_open_cover L) n)
  exact e ≪≫ (equatorial_equiv L).reducedSingularHomologyIso (ModuleCat.of R R) n

/-- Two contractible open cones meet along a nonempty band, so their union is path connected. -/
theorem twoCone_pathConnected (L : PreAbstractSimplicialComplex V)
    [Nonempty (Realization L)] : PathConnectedSpace (Realization (realizing_complex L)) := by
  letI := pole_open_contractible L false
  letI := pole_open_contractible L true
  have hU : IsPathConnected (pole_open L false) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hV : IsPathConnected (pole_open L true) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hi : (pole_open L false ∩ pole_open L true).Nonempty := by
    let x := equator_inclusion L (Classical.choice (inferInstance : Nonempty (Realization L)))
    exact ⟨x.1, x.2⟩
  apply pathConnectedSpace_iff_univ.mpr
  rw [← pole_open_cover L]
  exact hU.union hV hi

/-- Every actual triangulation carries the computed RP² torsion to its explicit double cone. -/
def triangulated_realProjective_H2 (L : PreAbstractSimplicialComplex V)
    (e : Realization L ≃ₜ TauCeti.RealProjectiveSpace 2) :
    SingularHomology ℤ (Realization (realizing_complex L)) 2 ≃ₗ[ℤ] ZMod 2 :=
  (twoConeHomologyIso ℤ L 1).toLinearEquiv ≪≫ₗ
    (e.toHomotopyEquiv.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) 1).toLinearEquiv ≪≫ₗ
      realProjective_integralH1

/-- All reduced rational degrees vanish on the actual double-cone realization. -/
theorem triangulated_realProjective_rational_isZero (L : PreAbstractSimplicialComplex V)
    (e : Realization L ≃ₜ TauCeti.RealProjectiveSpace 2) (n : ℕ) :
    IsZero (ReducedHomology ℚ (Realization (realizing_complex L)) n) := by
  letI : Nonempty (Realization L) :=
    ⟨e.symm (Classical.choice (inferInstance : Nonempty (TauCeti.RealProjectiveSpace 2)))⟩
  cases n with
  | zero =>
    letI := twoCone_pathConnected L
    exact TauCeti.isZero_reducedSingularHomologyFunctor_zero
      (ModuleCat.of ℚ ℚ) (TopCat.of (Realization (realizing_complex L)))
  | succ n =>
    have hL : IsZero (ReducedHomology ℚ (Realization L) n) :=
      (realProjective_reducedRational_isZero n).of_iso
        (e.toHomotopyEquiv.reducedSingularHomologyIso (ModuleCat.of ℚ ℚ) n)
    exact hL.of_iso (twoConeHomologyIso ℚ L n)

/-- Nonzero integer torsion rules out contractibility, despite rational acyclicity. -/
theorem triangulated_realProjective_not_contractible (L : PreAbstractSimplicialComplex V)
    (e : Realization L ≃ₜ TauCeti.RealProjectiveSpace 2) :
    ¬ ContractibleSpace (Realization (realizing_complex L)) := by
  intro h
  letI := h
  have hz := TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace
    (ModuleCat.of ℤ ℤ) (TopCat.of (Realization (realizing_complex L)))
    (by decide : (2 : ℕ) ≠ 0)
  letI : Subsingleton (SingularHomology ℤ (Realization (realizing_complex L)) 2) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  let f := triangulated_realProjective_H2 L e
  have h01 : (0 : ZMod 2) = 1 := by
    simpa using congrArg f (Subsingleton.elim (f.symm 0) (f.symm 1))
  exact zero_ne_one h01

omit [DecidableEq V] in
/-- A nonempty realization supplies an actual vertex, rather than an assumed vertex certificate. -/
theorem realization_has_vertex (L : PreAbstractSimplicialComplex V)
    [Nonempty (Realization L)] : ∃ a : V, ({a} : Finset V) ∈ L := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (Realization L))
  obtain ⟨s, hs, _⟩ := x.2.2
  obtain ⟨a, ha⟩ := (L.isRelLowerSet_faces hs).1
  exact ⟨a, (L.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr ha)
    (Finset.singleton_nonempty a)⟩

/-- Full S3 constructor for any finite RP² triangulation in the usual coordinate realization. -/
theorem realProjective_counterexample (L : PreAbstractSimplicialComplex V)
    (e : Realization L ≃ₜ TauCeti.RealProjectiveSpace 2) :
    ∃ (K B : PreAbstractSimplicialComplex (Sum Bool V)) (v : Sum Bool V),
      B ≤ K ∧ ({v} : Finset (Sum Bool V)) ∈ B ∧
      Nonempty (Punctured K v) ∧ ContractibleSpace (Punctured K v) ∧
      (∃ h : Punctured B v ≃ₕ Realization B, h.toFun = punctured_inclusion_map B v) ∧
      Nonempty (SingularHomology ℤ (Realization K) 2 ≃ₗ[ℤ] ZMod 2) ∧
      (∀ n : ℕ, IsZero (ReducedHomology ℚ (Realization K) n)) ∧
      ¬ ContractibleSpace (Realization K) := by
  letI : Nonempty (Realization L) :=
    ⟨e.symm (Classical.choice (inferInstance : Nonempty (TauCeti.RealProjectiveSpace 2)))⟩
  obtain ⟨a, ha⟩ := realization_has_vertex L
  obtain ⟨hBK, hv, hc, he⟩ := realizing_original_hypotheses L a ha
  letI := hc
  exact ⟨realizing_complex L, realizing_edge a, Sum.inl false,
    hBK, hv, inferInstance, hc, he, ⟨triangulated_realProjective_H2 L e⟩,
    triangulated_realProjective_rational_isZero L e,
    triangulated_realProjective_not_contractible L e⟩

/-- The same construction for a finite vertex type in any universe. The finite relabeling
comes with a proved homeomorphism, so this adds no restriction on the given triangulation. -/
theorem realProjective_counterexample_any_finite_triangulation
    {W : Type*} [Fintype W] [DecidableEq W] (L : PreAbstractSimplicialComplex W)
    (e : Realization L ≃ₜ TauCeti.RealProjectiveSpace 2) :
    ∃ (K B : PreAbstractSimplicialComplex (Sum Bool (Fin (Fintype.card W))))
        (v : Sum Bool (Fin (Fintype.card W))),
      B ≤ K ∧ ({v} : Finset (Sum Bool (Fin (Fintype.card W)))) ∈ B ∧
      Nonempty (Punctured K v) ∧ ContractibleSpace (Punctured K v) ∧
      (∃ h : Punctured B v ≃ₕ Realization B, h.toFun = punctured_inclusion_map B v) ∧
      Nonempty (SingularHomology ℤ (Realization K) 2 ≃ₗ[ℤ] ZMod 2) ∧
      (∀ n : ℕ, IsZero (ReducedHomology ℚ (Realization K) n)) ∧
      ¬ ContractibleSpace (Realization K) :=
  realProjective_counterexample (TauBridge.smallComplex L)
    ((TauBridge.smallCoordinateHomeomorph L).symm.trans e)

end MathGauge.GP001
