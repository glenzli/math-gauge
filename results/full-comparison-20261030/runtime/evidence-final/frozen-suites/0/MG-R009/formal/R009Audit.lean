import SheafQuotientExtras
import SheafBaseQuotient
import PointInvisibleAction
import PadicBoundary
import Lean.Util.CollectAxioms

open Lean Elab Command in
elab "#audit_descent" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "MathGauge.Descent." then
      let axioms ← Lean.collectAxioms name
      for a in axioms do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "Forbidden axiom {a} in {name}"
      logInfo m!"{name}: {axioms}"
      count := count + 1
  logInfo m!"AUDIT PASSED: {count} declarations, including generated declarations and instances."

set_option pp.universes true in
#check @MathGauge.Descent.SpaceAction.classification
set_option pp.universes true in
#check @MathGauge.Descent.basechange_equivalence
set_option pp.universes true in
#check @MathGauge.Descent.basechange_realization_quotient_iso
#audit_descent
