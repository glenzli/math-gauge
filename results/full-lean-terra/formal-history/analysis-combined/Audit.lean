import RecordInstantiation
import HilbertCriteria
import ErgodicConsequences
import ErgodicCoordinates
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Dynamic audit of every constant actually loaded in the project namespace. A shared
visited set traverses the union of every transitive dependency, without rewalking the
same Mathlib declaration hundreds of times. The exact audited roots are listed. -/
run_cmd do
  let env ← getEnv
  let entries := env.constants.toList.filter fun p =>
    p.1.toString.startsWith "MathGauge."
  let entries := entries.toArray.qsort fun a b => a.1.toString < b.1.toString
  let action : CollectAxioms.M Unit := entries.forM fun (name, _) => CollectAxioms.collect name
  let (_, state) := (action.run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let unexpected := state.axioms.filter fun a => !(allowed.contains a)
  unless unexpected.isEmpty do
    throwError "Unexpected axioms in project dependency closure: {unexpected}"
  for (name, _) in entries do
    logInfo m!"AXIOM_AUDITED_ROOT {name}"
  logInfo m!"AXIOM_AUDIT_UNION {state.axioms}"
  logInfo m!"AXIOM_AUDIT_TOTAL {entries.size}; allowed = {allowed}"
