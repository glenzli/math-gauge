import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_03_operator_local_degeneracy.component_partition
import formal_oet.vol_01.ch_03_operator_local_degeneracy.computational_fiber
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_03_operator_local_degeneracy.component_transfer
import formal_oet.vol_01.ch_03_operator_local_degeneracy.finite_counterexamples
import formal_oet.vol_01.ch_03_operator_local_degeneracy.image_factorization
import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_classification
import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy
import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples
import formal_oet.vol_01.ch_03_operator_local_degeneracy.pointwise_uniform_radius_example
import formal_oet.vol_01.ch_03_operator_local_degeneracy.pseudometric_composition
import formal_oet.vol_01.ch_03_operator_local_degeneracy.zeroing_composition
import formal_oet.vol_01.exercise_solutions.distance_gap
import formal_oet.vol_01.exercise_solutions.foundation_examples
import formal_oet.vol_01.exercise_solutions.translation_entropy
import formal_oet.vol_01.exercise_solutions.four_point_covering
import MathGauge.C003.SourceBridge
import MathGauge.C003.Completeness
import MathGauge.C003.CoveringConstructions
import MathGauge.C003.ExampleLegality
import Main
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command

open Lean Elab Command

/- Generated engineering audit. Its roots are every constant owned by the explicit case modules,
including private declarations after recovering their user-facing namespace.
The shared visited set traverses the complete union of their dependencies. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["formal_oet.vol_01.ch_01_foundations.gauge_space", "formal_oet.vol_01.ch_01_foundations.operator_space", "formal_oet.vol_01.ch_02_operator_bounds.lip_matrix", "formal_oet.vol_01.ch_02_operator_bounds.single_channel", "formal_oet.vol_01.ch_01_foundations.metric_entropy", "formal_oet.vol_01.ch_03_operator_local_degeneracy.component_partition", "formal_oet.vol_01.ch_03_operator_local_degeneracy.computational_fiber", "formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix", "formal_oet.vol_01.ch_02_operator_bounds.decoupling", "formal_oet.vol_01.ch_03_operator_local_degeneracy.component_transfer", "formal_oet.vol_01.ch_03_operator_local_degeneracy.finite_counterexamples", "formal_oet.vol_01.ch_03_operator_local_degeneracy.image_factorization", "formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_classification", "formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy", "formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples", "formal_oet.vol_01.ch_03_operator_local_degeneracy.pointwise_uniform_radius_example", "formal_oet.vol_01.ch_03_operator_local_degeneracy.pseudometric_composition", "formal_oet.vol_01.ch_03_operator_local_degeneracy.zeroing_composition", "formal_oet.vol_01.exercise_solutions.distance_gap", "formal_oet.vol_01.exercise_solutions.foundation_examples", "formal_oet.vol_01.exercise_solutions.translation_entropy", "formal_oet.vol_01.exercise_solutions.four_point_covering", "MathGauge.C003.SourceBridge", "MathGauge.C003.Completeness", "MathGauge.C003.CoveringConstructions", "MathGauge.C003.ExampleLegality", "Main"]
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
