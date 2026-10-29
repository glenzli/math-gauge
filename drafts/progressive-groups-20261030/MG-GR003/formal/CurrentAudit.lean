import BinomialSmoothing
import ErgodicOperators
import ErgodicRecoveryCore
import ErgodicComparison
import ErgodicRecoveryMap
import ErgodicQuotient
import ErgodicConsequences
import ErgodicCounterexample
import ErgodicCoordinates
import OrthogonalComponents
import ProjectionDynamics
import NoisyProjection
import SharpNoise
import DiagonalSlow
import FullRecovery
import UniformPowers
import AverageRates
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command

open Lean Elab Command

/- Generated engineering audit. Its roots are every constant owned by the explicit case modules,
including private declarations after recovering their user-facing namespace.
The shared visited set traverses the complete union of their dependencies. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["BinomialSmoothing", "ErgodicOperators", "ErgodicRecoveryCore", "ErgodicComparison", "ErgodicRecoveryMap", "ErgodicQuotient", "ErgodicConsequences", "ErgodicCounterexample", "ErgodicCoordinates", "OrthogonalComponents", "ProjectionDynamics", "NoisyProjection", "SharpNoise", "DiagonalSlow", "FullRecovery", "UniformPowers", "AverageRates"]
  let entries := env.constants.toList.filter fun entry =>
    let origin := match env.getModuleIdxFor? entry.1 with
      | some index => env.header.moduleNames[index]!.toString
      | none => env.mainModule.toString
    expectedModules.contains origin
  let entries := entries.toArray.qsort fun a b => a.1.toString < b.1.toString
  unless !entries.isEmpty do
    throwError "MATH_GAUGE_EMPTY_AUDIT: no case-owned constants were loaded"
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
  let action : CollectAxioms.M Unit := entries.forM fun (name, _) =>
    CollectAxioms.collect name
  let (_, state) := (action.run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let axioms := state.axioms.qsort fun a b => a.toString < b.toString
  let unexpected := axioms.filter fun name => !(allowed.contains name)
  let summary := Json.mkObj [("declaration_count", toJson entries.size),
    ("axiom_union", toJson (axioms.map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString)),
    ("passed", toJson unexpected.isEmpty)]
  logInfo m!"MATH_GAUGE_AUDIT_SUMMARY {summary.compress}"
  unless unexpected.isEmpty do
    throwError "MATH_GAUGE_FORBIDDEN_AXIOMS: {unexpected}"
