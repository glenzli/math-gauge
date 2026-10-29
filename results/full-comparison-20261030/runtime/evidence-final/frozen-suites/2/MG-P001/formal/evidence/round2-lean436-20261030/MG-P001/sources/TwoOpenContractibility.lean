import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic

/-!
Actual CW spaces, integral singular homology, and two contractible open sets.
These are wrappers around proved TauCeti results at commit
ab0153c648bc0f1364ea268fc806793beb01473a. They do not assume the
contractibility conclusion, a homological certificate, or a suspension theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Topology Topology.Homotopy

namespace MathGauge.PublicProof.Topology.TauBridge

/-- Reduced integral singular homology of the actual topological space. -/
abbrev ReducedIntegralHomology (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) n).obj (TopCat.of X)

/-- Hurewicz followed by Whitehead, retaining the actual CW-type and topology. -/
theorem contractible_of_simplyConnected_acyclic
    (X : Type) [TopologicalSpace X] [TauCeti.CWType X] [SimplyConnectedSpace X]
    (hH : ∀ n : ℕ,
      IsZero (((TauCeti.singularChains ℤ).obj (TopCat.of X)).homology (n + 2))) :
    ContractibleSpace X := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  letI : Subsingleton (π_ 1 X x) :=
    HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.mpr inferInstance
  exact TauCeti.contractibleSpace_of_subsingleton_homotopyGroup x fun n =>
    TauCeti.subsingleton_homotopyGroup_of_isZero_homology_singularChains x hH (n + 1)

/-- For a simply connected CW space, integral acyclicity is equivalent to contractibility. -/
theorem contractible_iff_reducedIntegralHomology_isZero
    (X : Type) [TopologicalSpace X] [TauCeti.CWType X] [SimplyConnectedSpace X] :
    ContractibleSpace X ↔ ∀ n : ℕ, IsZero (ReducedIntegralHomology X n) := by
  constructor
  · intro h n
    letI := h
    exact TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace
      (ModuleCat.of ℤ ℤ) (TopCat.of X) n
  · intro h
    exact contractible_of_simplyConnected_acyclic X fun n => h (n + 2)

/-- The actual Mayer–Vietoris isomorphism for a cover by two contractible open sets. -/
def twoOpenHomologyIso {X : Type} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    ((TauCeti.singularChains ℤ).obj (TopCat.of X)).homology (n + 1) ≅
      ReducedIntegralHomology ↥(U ∩ V) n :=
  @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ (X := TopCat.of X)
    (ModuleCat.of ℤ ℤ) hU hV hUV n)
      (TopCat.isIso_reducedMayerVietorisδ_of_contractible (X := TopCat.of X)
        (ModuleCat.of ℤ ℤ) hU hV hUV n)

/-- Two contractible open sets with nonempty intersection in a CW space give the exact
acyclicity criterion on the intersection, including reduced degree zero. -/
theorem contractible_iff_intersection_reducedIntegralHomology_isZero
    {X : Type} [TopologicalSpace X] [TauCeti.CWType X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    [ContractibleSpace U] [ContractibleSpace V] (hne : (U ∩ V).Nonempty) :
    ContractibleSpace X ↔ ∀ n : ℕ,
      IsZero (ReducedIntegralHomology ↥(U ∩ V) n) := by
  constructor
  · intro h n
    letI := h
    have hX := TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace
      (ModuleCat.of ℤ ℤ) (TopCat.of X) (Nat.succ_ne_zero n)
    exact hX.of_iso (twoOpenHomologyIso hU hV hUV n).symm
  · intro h
    letI : Nonempty ↥(U ∩ V) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    letI : PathConnectedSpace ↥(U ∩ V) :=
      TauCeti.pathConnectedSpace_of_isZero_reducedSingularHomologyFunctor_zero (h 0)
    have hi : IsPathConnected (U ∩ V) := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    letI : SimplyConnectedSpace X :=
      TauCeti.simplyConnectedSpace_of_interior_union
        (by simpa only [hU.interior_eq, hV.interior_eq] using hUV) hi
    exact contractible_of_simplyConnected_acyclic X fun n =>
      (h (n + 1)).of_iso (twoOpenHomologyIso hU hV hUV (n + 1))

/-- A homotopy equivalence with the intersection transports the criterion to the actual
model space. For the suspension application the model will be the finite link realization. -/
theorem contractible_iff_model_reducedIntegralHomology_isZero
    {X L : Type} [TopologicalSpace X] [TopologicalSpace L] [TauCeti.CWType X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    [ContractibleSpace U] [ContractibleSpace V] [Nonempty L]
    (e : ContinuousMap.HomotopyEquiv ↥(U ∩ V) L) :
    ContractibleSpace X ↔ ∀ n : ℕ, IsZero (ReducedIntegralHomology L n) := by
  have hne : (U ∩ V).Nonempty := by
    let p := e.invFun (Classical.choice (inferInstance : Nonempty L))
    exact ⟨p.1, p.2⟩
  rw [contractible_iff_intersection_reducedIntegralHomology_isZero hU hV hUV hne]
  constructor
  · intro h n
    exact (h n).of_iso (e.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) n).symm
  · intro h n
    exact (h n).of_iso (e.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) n)

end MathGauge.PublicProof.Topology.TauBridge
