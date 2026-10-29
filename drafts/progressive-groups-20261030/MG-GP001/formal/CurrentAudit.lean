import VertexDeletion
import LinkNonempty
import FiniteCones
import TwoConeRealizations
import RealizationCompactness
import VendoredSuspension
import SuspensionRealization
import DeletionConeGluing
import SuspensionRetime
import GeneralSuspensionClassification
import TwoConeOpenCover
import CoordinateCore
import CoordinateReindex
import CoordinateCWBridge
import TwoOpenContractibility
import OrderedAcyclicity
import OriginalCriterion
import FiniteLocalChains
import FiniteBoundaryMatrix
import FiniteMatrixCriterion
import FiniteLocalCriterion
import MathGauge.GP001.Borrowed.CWSubcomplex
import MathGauge.GP001.CollapseContractible
import MathGauge.GP001.IsolatedVertex
import MathGauge.GP001.ConstantConeWedge
import MathGauge.GP001.ConeHomotopy
import MathGauge.GP001.RealizationCone
import MathGauge.GP001.Borrowed.RealProjective.Mathlib.LinearAlgebra.DirectSum.Finite
import MathGauge.GP001.Borrowed.RealProjective.Mathlib.Algebra.Homology.EulerCharacteristic
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Algebra.Category.ModuleCat.Finrank
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Basic
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Singular.LocalHomology.Involution
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Geometry.Sphere.Connected
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Analysis.Normed.Module.Ball.Action
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Analysis.Normed.Module.Ball.IntUnitsAction
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Topology.CWComplex.Classical.FiniteCWType
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.Topology.CWComplex.Classical.RealProjective
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.RealProjective.Basic
import MathGauge.GP001.Borrowed.RealProjective.Mathlib.Data.Nat.Prime.Int
import MathGauge.GP001.Borrowed.RealProjective.Mathlib.RingTheory.Int.Basic
import MathGauge.GP001.Borrowed.RealProjective.Mathlib.RingTheory.ZMod
import MathGauge.GP001.Borrowed.RealProjective.Mathlib.Data.ZMod.QuotientRing
import MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
import MathGauge.GP001.RealProjectiveCounterexample
import MathGauge.GP001.SimplicialHomotopy
import MathGauge.GP001.WedgeHomotopy
import MathGauge.GP001.GraphExamples
import MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.AffineSpace.Dimension
import MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
import MathGauge.GP001.Borrowed.Graph.Mathlib.FieldTheory.Finiteness
import MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.Dimension.OrzechProperty
import MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import MathGauge.GP001.Borrowed.Graph.Mathlib.Analysis.Normed.Affine.AddTorsorBases
import MathGauge.GP001.Borrowed.Graph.TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
import MathGauge.GP001.Borrowed.Graph.TauCeti.AlgebraicTopology.Sphere.Contractible
import MathGauge.GP001.GraphNonEquivalence
import MathGauge.GP001.GraphSuspensionFaces
import MathGauge.GP001.SuspensionGraphCounterexample
import Main
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command

open Lean Elab Command

/- Generated engineering audit for the fixed Lean 4.36 profile. Each loaded
MathGauge root, including private user names, is checked via the public API. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["VertexDeletion", "LinkNonempty", "FiniteCones", "TwoConeRealizations", "RealizationCompactness", "VendoredSuspension", "SuspensionRealization", "DeletionConeGluing", "SuspensionRetime", "GeneralSuspensionClassification", "TwoConeOpenCover", "CoordinateCore", "CoordinateReindex", "CoordinateCWBridge", "TwoOpenContractibility", "OrderedAcyclicity", "OriginalCriterion", "FiniteLocalChains", "FiniteBoundaryMatrix", "FiniteMatrixCriterion", "FiniteLocalCriterion", "MathGauge.GP001.Borrowed.CWSubcomplex", "MathGauge.GP001.CollapseContractible", "MathGauge.GP001.IsolatedVertex", "MathGauge.GP001.ConstantConeWedge", "MathGauge.GP001.ConeHomotopy", "MathGauge.GP001.RealizationCone", "MathGauge.GP001.Borrowed.RealProjective.Mathlib.LinearAlgebra.DirectSum.Finite", "MathGauge.GP001.Borrowed.RealProjective.Mathlib.Algebra.Homology.EulerCharacteristic", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Algebra.Category.ModuleCat.Finrank", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Algebra.Homology.ShortComplex.ModuleCat", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Basic", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Singular.LocalHomology.Involution", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Geometry.Sphere.Connected", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Analysis.Normed.Module.Ball.Action", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Analysis.Normed.Module.Ball.IntUnitsAction", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Topology.CWComplex.Classical.FiniteCWType", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.Topology.CWComplex.Classical.RealProjective", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.RealProjective.Basic", "MathGauge.GP001.Borrowed.RealProjective.Mathlib.Data.Nat.Prime.Int", "MathGauge.GP001.Borrowed.RealProjective.Mathlib.RingTheory.Int.Basic", "MathGauge.GP001.Borrowed.RealProjective.Mathlib.RingTheory.ZMod", "MathGauge.GP001.Borrowed.RealProjective.Mathlib.Data.ZMod.QuotientRing", "MathGauge.GP001.Borrowed.RealProjective.TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology", "MathGauge.GP001.RealProjectiveCounterexample", "MathGauge.GP001.SimplicialHomotopy", "MathGauge.GP001.WedgeHomotopy", "MathGauge.GP001.GraphExamples", "MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.AffineSpace.Dimension", "MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid", "MathGauge.GP001.Borrowed.Graph.Mathlib.FieldTheory.Finiteness", "MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.Dimension.OrzechProperty", "MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.FreeModule.Finite.Matrix", "MathGauge.GP001.Borrowed.Graph.Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional", "MathGauge.GP001.Borrowed.Graph.Mathlib.Analysis.Normed.Affine.AddTorsorBases", "MathGauge.GP001.Borrowed.Graph.TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere", "MathGauge.GP001.Borrowed.Graph.TauCeti.AlgebraicTopology.Sphere.Contractible", "MathGauge.GP001.GraphNonEquivalence", "MathGauge.GP001.GraphSuspensionFaces", "MathGauge.GP001.SuspensionGraphCounterexample", "Main"]
  let entries := env.constants.toList.filter fun entry =>
    let origin := match env.getModuleIdxFor? entry.1 with
      | some index => env.header.moduleNames[index]!.toString
      | none => env.mainModule.toString
    expectedModules.contains origin
  let entries := entries.toArray.qsort fun a b => a.1.toString < b.1.toString
  unless !entries.isEmpty do
    throwError "MATH_GAUGE_EMPTY_AUDIT: no case-owned constants were loaded"
  let mut axioms : Array Name := #[]
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
    for axiomName in (← Lean.collectAxioms name) do
      if !axioms.contains axiomName then
        axioms := axioms.push axiomName
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let sortedAxioms := axioms.qsort fun a b => a.toString < b.toString
  let unexpected := sortedAxioms.filter fun name => !(allowed.contains name)
  let summary := Json.mkObj [("declaration_count", toJson entries.size),
    ("axiom_union", toJson (sortedAxioms.map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString)),
    ("passed", toJson unexpected.isEmpty)]
  logInfo m!"MATH_GAUGE_AUDIT_SUMMARY {summary.compress}"
  unless unexpected.isEmpty do
    throwError "MATH_GAUGE_FORBIDDEN_AXIOMS: {unexpected}"
