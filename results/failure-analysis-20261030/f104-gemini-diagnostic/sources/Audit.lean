import Core
import Construction
import Candidate
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/- Candidate audit roots are selected by actual module origin, not namespace. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["Core", "Construction", "Candidate"]
  -- Read the imported module inventories directly. In particular, do not rebuild
  -- header.moduleNames for every constant in an entire Mathlib environment.
  let moduleNames := env.header.moduleNames
  let mut entries : Array (Name × String) := #[]
  for index in [:moduleNames.size] do
    let moduleName := moduleNames[index]!.toString
    if expectedModules.contains moduleName then
      let data := env.header.moduleData[index]!
      for name in data.constNames ++ data.extraConstNames do
        if (env.find? name).isSome && !(entries.any fun entry => entry.1 == name) then
          entries := entries.push (name, moduleName)
  entries := entries.qsort fun a b => a.1.toString < b.1.toString
  for (name, moduleName) in entries do
    let row := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName)]
    logInfo m!"CANDIDATE_DECL {row.compress}"
  let action : CollectAxioms.M Unit := entries.forM fun (name, _) => CollectAxioms.collect name
  let (_, state) := (action.run env).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let axioms := state.axioms.qsort fun a b => a.toString < b.toString
  let unexpected := axioms.filter fun name => !(allowed.contains name)
  let summary := Json.mkObj [("declaration_count", toJson entries.size),
    ("axiom_union", toJson (axioms.map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString)),
    ("passed", toJson unexpected.isEmpty)]
  logInfo m!"CANDIDATE_AUDIT_SUMMARY {summary.compress}"
  unless unexpected.isEmpty do
    throwError "CANDIDATE_FORBIDDEN_AXIOMS: {unexpected}"
