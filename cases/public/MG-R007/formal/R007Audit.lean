import LinearTower
import RepresentationTower
import SplitRepresentation
import TowerSplit
import SectionTransport
import CoherentTransport
import SplitClassification
import TowerBoundaries
import BoundaryData
import ModularBoundary
import Lean.Util.CollectAxioms
open Lean Elab Command in
elab "#audit_local" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "MathGauge.LinearTower." || name.toString.startsWith "MathGauge.RepresentationTower." || name.toString.startsWith "MathGauge.SplitRepresentation." || name.toString.startsWith "MathGauge.SectionTransport." || name.toString.startsWith "MathGauge.TowerBoundaries." then
      let axioms ← Lean.collectAxioms name
      for a in axioms do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "Forbidden axiom {a} in {name}"
      logInfo m!"{name}: {axioms}"
      count := count + 1
  logInfo m!"AUDIT PASSED: {count} declarations including helpers and instances."
#audit_local
