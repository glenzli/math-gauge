import TowerProjectionExample
import TowerDoublingExample
import Lean.Util.CollectAxioms

/- Audit every declaration actually loaded from the five new mathematical
modules, including compiler-generated private declarations, recursively through
all dependencies. The already-delivered core remains frozen. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[`TowerStageTools, `TowerFiniteLimits,
    `TowerFiniteStage, `TowerProjectionExample, `TowerDoublingExample]
  let names := (env.constants.toList.map Prod.fst).filter fun n =>
    match env.getModuleIdxFor? n with
    | none => false
    | some i => selected.contains env.allImportedModuleNames[i.toNat]!
  let names := names.toArray.qsort fun a b => a.toString < b.toString
  unless names.size > 0 do throwError "No extension declarations found"
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
      unless allowed.contains ax do throwError "Unexpected axiom in {n}: {ax}"
    logInfo m!"AXIOMS {n}: {axioms}"
  logInfo m!"EXTRAS_AUDIT_OK declarations={names.size} theorems={theoremCount} definitions={definitionCount}"

#check MathGauge.Tower.FreeTower.finiteStage_iff_finite_invariant
#check MathGauge.Tower.FreeTower.finiteStage_iff_representable
#check MathGauge.Tower.FreeTower.preserves_every_finite_limit
#check MathGauge.Tower.Examples.projectionRepresentation
#check MathGauge.Tower.Examples.projection_never_eventually_isomorphisms
#check MathGauge.Tower.Examples.doublingInvariantEquivDyadic
#check MathGauge.Tower.Examples.doubling_invariant_not_finite
#check MathGauge.Tower.Examples.doubling_not_representable
#check MathGauge.Tower.Examples.doubling_not_preserves_countable_limits
#check MathGauge.Tower.Examples.dyadicIntegers_not_finitely_generated
