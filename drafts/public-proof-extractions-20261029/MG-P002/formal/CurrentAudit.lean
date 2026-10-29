import MathGauge.PublicProof.Torus.Arithmetic
import MathGauge.PublicProof.Torus.ArithmeticSharp
import MathGauge.PublicProof.Torus.Borrowed.DiophantineGraph
import MathGauge.PublicProof.Torus.Borrowed.TorusInverse
import MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData
import MathGauge.PublicProof.Torus.Functions
import MathGauge.PublicProof.Torus.CubicBound
import MathGauge.PublicProof.Torus.FourierBridge
import MathGauge.PublicProof.Torus.GeneralTransport
import MathGauge.PublicProof.Torus.GeneralInverse
import MathGauge.PublicProof.Torus.Weights
import MathGauge.PublicProof.Torus.Sobolev
import MathGauge.PublicProof.Torus.Necessity
import MathGauge.PublicProof.Torus.Classification
import MathGauge.PublicProof.Torus.CNorm
import MathGauge.PublicProof.Torus.Representation
import MathGauge.PublicProof.Torus.NativeAnalysis
import MathGauge.PublicProof.Torus.NativeTheorems
import MathGauge.PublicProof.Torus.FullTarget
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command

open Lean Elab Command

/- Generated engineering audit. Its roots are every loaded MathGauge constant,
including private declarations after recovering their user-facing namespace.
The shared visited set traverses the complete union of their dependencies. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["MathGauge.PublicProof.Torus.Arithmetic", "MathGauge.PublicProof.Torus.ArithmeticSharp", "MathGauge.PublicProof.Torus.Borrowed.DiophantineGraph", "MathGauge.PublicProof.Torus.Borrowed.TorusInverse", "MathGauge.PublicProof.Torus.Borrowed.SmoothFourierData", "MathGauge.PublicProof.Torus.Functions", "MathGauge.PublicProof.Torus.CubicBound", "MathGauge.PublicProof.Torus.FourierBridge", "MathGauge.PublicProof.Torus.GeneralTransport", "MathGauge.PublicProof.Torus.GeneralInverse", "MathGauge.PublicProof.Torus.Weights", "MathGauge.PublicProof.Torus.Sobolev", "MathGauge.PublicProof.Torus.Necessity", "MathGauge.PublicProof.Torus.Classification", "MathGauge.PublicProof.Torus.CNorm", "MathGauge.PublicProof.Torus.Representation", "MathGauge.PublicProof.Torus.NativeAnalysis", "MathGauge.PublicProof.Torus.NativeTheorems", "MathGauge.PublicProof.Torus.FullTarget"]
  let entries := env.constants.toList.filter fun entry =>
    (privateToUserName entry.1).toString.startsWith "MathGauge."
  let entries := entries.toArray.qsort fun a b => a.1.toString < b.1.toString
  unless !entries.isEmpty do
    throwError "MATH_GAUGE_EMPTY_AUDIT: no MathGauge constants were loaded"
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
