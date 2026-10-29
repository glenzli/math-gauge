import RelaxationGeometry
import TowerClassification
import Lean.Util.CollectAxioms

/- The audit enumerates the compiled environment, including private generated
declarations. It fails if any project declaration is an axiom or depends on an
axiom other than Lean's three standard classical foundations. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter fun n =>
    (n.toString.splitOn "MathGauge.").length > 1
  let names := names.toArray.qsort fun a b => a.toString < b.toString
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut theoremCount := 0
  let mut definitionCount := 0
  for n in names do
    let some info := env.find? n | throwError "Declaration disappeared: {n}"
    match info with
    | .axiomInfo _ => throwError "Project axiom is forbidden: {n}"
    | .thmInfo _ => theoremCount := theoremCount + 1
    | .defnInfo _ => definitionCount := definitionCount + 1
    | _ => pure ()
    let axioms ← collectAxioms n
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {n}: {ax}"
    logInfo m!"AXIOMS {n}: {axioms}"
  logInfo m!"AUDIT_OK declarations={names.size} theorems={theoremCount} definitions={definitionCount}"

#print MathGauge.ConvexCost.finite_observation_reconstruction
#print MathGauge.ConvexCost.reconstruct_maximal_ereal
#print MathGauge.Tower.FreeTower.classification
#print MathGauge.Tower.FreeTower.all_record_representing_objects
#print MathGauge.Tower.FreeTower.recordNatEquiv
#print MathGauge.Tower.FreeTower.recordNatEquivInLargerUniverse
