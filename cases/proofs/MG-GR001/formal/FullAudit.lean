import Core
import Partial
import Bounds
import Spectral
import Weighted
import Counterexample
import Obstructions
import Limits
import Extra
import Routes
import Reference
import PathBounds
import Partitions
import InputTransport
import FiniteResidual
import TerminationBoundary
import AbsorbingTransport
import FullTarget
import Lean.Util.CollectAxioms
open Lean Elab Command in
elab "#audit_local" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "MathGauge.RecursiveClosure." then
      let axioms ← Lean.collectAxioms name
      for a in axioms do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "Forbidden axiom {a} in {name}"
      logInfo m!"{name}: {axioms}"
      count := count + 1
  logInfo m!"AUDIT PASSED: {count} declarations including helpers and instances."
#audit_local
