import FinitePrimeLocalization
import NeighborhoodRefinement
import AffineScheme
import FilteredExactness
import ComparisonDiagram
import SheafificationStalk
import NeighborhoodValues
import MathGauge.GP003.OpenNeighborhoods
import MathGauge.GP003.DenseOpenFailure
import MathGauge.GP003.EventualExactness
import MathGauge.GP003.TwoPointComparison
import MathGauge.GP003.FiniteGermDescent
import MathGauge.GP003.FiniteNeighborhoodDescent
import MathGauge.GP003.LocalizationNeighborhoods
import MathGauge.GP003.PairLocalizationNeighborhoods
import MathGauge.GP003.ActualSemilocalGeometry
import MathGauge.GP003.SchemeNeighborhoodValues
import MathGauge.GP003.ActualSemilocalDescent
import MathGauge.GP003.SchemeNeighborhoodMaps
import MathGauge.GP003.ActualOpenComparison
import MathGauge.GP003.AffineRestriction
import MathGauge.GP003.GeneralAmbient
import MathGauge.GP003.GeneralAmbientNonOpen
import MathGauge.GP003.GeneralAmbientComparison
import MathGauge.GP003.S5FiniteInduction
import MathGauge.GP003.S5FiniteClosedPointReduction
import MathGauge.GP003.S5SimultaneousUniversal
import MathGauge.GP003.S5SimultaneousFinite
import MathGauge.GP003.S5SiteBridge
import MathGauge.GP003.S5ZariskiKernel
import MathGauge.GP003.S5ZariskiComparison
import MathGauge.GP003.S5TransferSectionLift
import MathGauge.GP003.S5GenericRepresentative
import MathGauge.GP003.S5InfiniteAffineMoving
import MathGauge.GP003.S5IntegralComparison
import MathGauge.GP003.S5FiniteScalarMovingDescent
import MathGauge.GP003.S5FiniteFieldMoving
import MathGauge.GP003.S5AllFieldMoving
import MathGauge.GP003.S5DisjointAssembly
import MathGauge.GP003.S5DisjointGeometry
import MathGauge.GP003.S5AffineComparison
import MathGauge.GP003.S5AmbientComparison
import MathGauge.GP003.S5Complete
import Main
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command

open Lean Elab Command

/- Generated engineering audit for the fixed Lean 4.34 profile. Each loaded
MathGauge root, including private user names, is checked via the public API. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["FinitePrimeLocalization", "NeighborhoodRefinement", "AffineScheme", "FilteredExactness", "ComparisonDiagram", "SheafificationStalk", "NeighborhoodValues", "MathGauge.GP003.OpenNeighborhoods", "MathGauge.GP003.DenseOpenFailure", "MathGauge.GP003.EventualExactness", "MathGauge.GP003.TwoPointComparison", "MathGauge.GP003.FiniteGermDescent", "MathGauge.GP003.FiniteNeighborhoodDescent", "MathGauge.GP003.LocalizationNeighborhoods", "MathGauge.GP003.PairLocalizationNeighborhoods", "MathGauge.GP003.ActualSemilocalGeometry", "MathGauge.GP003.SchemeNeighborhoodValues", "MathGauge.GP003.ActualSemilocalDescent", "MathGauge.GP003.SchemeNeighborhoodMaps", "MathGauge.GP003.ActualOpenComparison", "MathGauge.GP003.AffineRestriction", "MathGauge.GP003.GeneralAmbient", "MathGauge.GP003.GeneralAmbientNonOpen", "MathGauge.GP003.GeneralAmbientComparison", "MathGauge.GP003.S5FiniteInduction", "MathGauge.GP003.S5FiniteClosedPointReduction", "MathGauge.GP003.S5SimultaneousUniversal", "MathGauge.GP003.S5SimultaneousFinite", "MathGauge.GP003.S5SiteBridge", "MathGauge.GP003.S5ZariskiKernel", "MathGauge.GP003.S5ZariskiComparison", "MathGauge.GP003.S5TransferSectionLift", "MathGauge.GP003.S5GenericRepresentative", "MathGauge.GP003.S5InfiniteAffineMoving", "MathGauge.GP003.S5IntegralComparison", "MathGauge.GP003.S5FiniteScalarMovingDescent", "MathGauge.GP003.S5FiniteFieldMoving", "MathGauge.GP003.S5AllFieldMoving", "MathGauge.GP003.S5DisjointAssembly", "MathGauge.GP003.S5DisjointGeometry", "MathGauge.GP003.S5AffineComparison", "MathGauge.GP003.S5AmbientComparison", "MathGauge.GP003.S5Complete", "Main"]
  let entries := env.constants.toList.filter fun entry =>
    let origin := match env.getModuleIdxFor? entry.1 with
      | some index => env.header.moduleNames[index]!.toString
      | none => env.mainModule.toString
    expectedModules.contains origin
  let entries := entries.toArray.qsort fun a b => a.1.toString < b.1.toString
  unless !entries.isEmpty do
    throwError "MATH_GAUGE_EMPTY_AUDIT: no case-owned constants were loaded"
  let mut axioms : Array Name := #[]
  for (name, info) in entries do
    let origin := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index]!.toString
      | none => env.mainModule.toString
    unless expectedModules.contains origin do
      throwError "MATH_GAUGE_FOREIGN_MODULE: {name} came from {origin}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
    let row := Json.mkObj [("name", toJson name.toString),
      ("user_name", toJson (privateToUserName name).toString),
      ("module", toJson origin), ("kind", toJson kind)]
    logInfo m!"MATH_GAUGE_DECL {row.compress}"
    for axiomName in (← Lean.collectAxioms name) do
      if !axioms.contains axiomName then
        axioms := axioms.push axiomName
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let sortedAxioms := axioms.qsort fun a b => a.toString < b.toString
  let unexpected := sortedAxioms.filter fun name => !(allowed.contains name)
  let summary := Json.mkObj [("declaration_count", toJson entries.size),
    ("axiom_union", toJson (sortedAxioms.map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString)),
    ("passed", toJson unexpected.isEmpty)]
  logInfo m!"MATH_GAUGE_AUDIT_SUMMARY {summary.compress}"
  unless unexpected.isEmpty do
    throwError "MATH_GAUGE_FORBIDDEN_AXIOMS: {unexpected}"
