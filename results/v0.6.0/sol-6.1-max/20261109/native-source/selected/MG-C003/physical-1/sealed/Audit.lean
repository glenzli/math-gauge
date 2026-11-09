import Chapter3.Correspondence
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    let selected := (env.getModuleIdxFor? name).any fun idx =>
      (`Chapter3).isPrefixOf env.header.moduleNames[idx.toNat]!
    if selected then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {name}"
  logInfo m!"Audited {count} Chapter3 declarations: only propext, Classical.choice, Quot.sound."
