import Submission.WhiteheadTheorem.Basic
import Submission.Hurewicz.AbsoluteIsomorphism
import Submission.Homology.MayerVietorisIso
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command

open Lean Elab Command

/- Generated engineering audit. Its roots are every loaded MathGauge constant,
including private declarations after recovering their user-facing namespace.
The shared visited set traverses the complete union of their dependencies. -/
run_cmd do
  let env ← getEnv
  let expectedModules : Array String := #["Submission.Approximation.Approx", "Submission.Approximation.Estimate", "Submission.Approximation.Grid", "Submission.Approximation.RegularValue", "Submission.Approximation.Simplex", "Submission.Cohomology.Basic", "Submission.Cohomology.Cochain", "Submission.Cohomology.Cup", "Submission.Cohomology.DualBridge", "Submission.Cohomology.FrontBack", "Submission.Cohomology.Singular", "Submission.Excision.ConvexSpace.AffineChains", "Submission.Excision.ConvexSpace.AffineMap", "Submission.Excision.ConvexSpace.Diameter", "Submission.Excision.ConvexSpace.StdSimplex", "Submission.Excision.ConvexSpace.ToSSet", "Submission.Excision.ConvexSpace.Top", "Submission.Excision.Fin.Prod", "Submission.Excision.Fin.Vec", "Submission.Excision.Finsupp.Basic", "Submission.Excision.HomologicalComplex.NullHomotopy", "Submission.Excision.Limits.SigmaConst", "Submission.Excision.Mathlib.Backports", "Submission.Excision.Mathlib.HomologicalComplexKernels", "Submission.Excision.Mathlib.SSetPair", "Submission.Excision.Mathlib.SimplicialSetHomologyRelative", "Submission.Excision.Perm.EquivSucc", "Submission.Excision.Preadditive.HasZeroObject", "Submission.Excision.SimplexCategory.Basic", "Submission.Excision.SimplicialSet.Homology", "Submission.Excision.SimplicialSet.RelativeHomology", "Submission.Excision.SimplicialSet.ULift", "Submission.Excision.SingularHomology.Basic", "Submission.Excision.SingularHomology.NatTrans", "Submission.Excision.SingularHomology.Subdivision", "Submission.Excision.SingularHomology.ULift", "Submission.Excision.SmallSimplices", "Submission.Excision.Topology.LebesgueNumber", "Submission.ForMathlib.HomotopyGroup.Basic", "Submission.ForMathlib.HomotopyGroup.Contractible", "Submission.ForMathlib.HomotopyGroup.Homotopy", "Submission.ForMathlib.HomotopyGroup.Map", "Submission.Homology.Basic", "Submission.Homology.Contractible", "Submission.Homology.Excision", "Submission.Homology.HomologyZero", "Submission.Homology.Homotopy", "Submission.Homology.LesTools", "Submission.Homology.MayerVietoris", "Submission.Homology.MayerVietorisIso", "Submission.Homology.MayerVietorisLES", "Submission.Homology.Pair", "Submission.Homology.PairHomotopy", "Submission.Homology.Point", "Submission.Homology.RelMap", "Submission.Homology.RightExact", "Submission.Homology.SimplicialSplitting", "Submission.Homology.Sphere", "Submission.Homology.SphereOne", "Submission.Homology.SphereZero", "Submission.Homology.SphereZeroSplit", "Submission.Homology.UCT.Dual", "Submission.Homology.UCT.HomologyClass", "Submission.Homotopy.Connected", "Submission.Homotopy.ContractionData", "Submission.Homotopy.HomotopyLesTools", "Submission.Homotopy.RelGroup", "Submission.Homotopy.RelMap", "Submission.Hurewicz.AbsoluteIsomorphism", "Submission.Hurewicz.AbsoluteSurjectivity", "Submission.Hurewicz.Compression", "Submission.Hurewicz.CubeFundamentalClass", "Submission.Hurewicz.CubicalShell", "Submission.Hurewicz.Deformation", "Submission.Hurewicz.DeformationClass", "Submission.Hurewicz.DegreeOne.Affine", "Submission.Hurewicz.FaceHomotopy", "Submission.Hurewicz.NormalizedBoundary", "Submission.Hurewicz.NormalizedSimplex", "Submission.Hurewicz.Prism", "Submission.Hurewicz.RelativeAdditivity", "Submission.Hurewicz.RelativeMap", "Submission.Hurewicz.RelativeSimplex", "Submission.Hurewicz.RelativeSimplicialDescent", "Submission.Hurewicz.RelativeSurjectivity", "Submission.Hurewicz.SimplexBall", "Submission.Hurewicz.SimplexCubeClass", "Submission.Hurewicz.SimplexCubeOrientation", "Submission.Hurewicz.SimplexDict", "Submission.Hurewicz.SimplexGlue", "Submission.Hurewicz.SimplexHEP", "Submission.Hurewicz.SimplexHorn", "Submission.Hurewicz.SimplicialAddition", "Submission.Hurewicz.SimplicialDescent", "Submission.Hurewicz.SimplicialIndexShift", "Submission.Hurewicz.SimplicialRelation", "Submission.Hurewicz.SimplicialRelationAt", "Submission.Hurewicz.SimplicialTelescope", "Submission.Hurewicz.SingularKan", "Submission.Hurewicz.SmallRelativeChains", "Submission.Hurewicz.SphereLoopBridge", "Submission.Hurewicz.StickBoundary", "Submission.Hurewicz.StickSimplex", "Submission.Hurewicz.StickSphere", "Submission.Hurewicz.Tower", "Submission.Hurewicz.Vanishing", "Submission.Hurewicz.VanishingSorries", "Submission.Model.Sphere", "Submission.Model.SphereCompl", "Submission.Model.SphereConnected", "Submission.Model.SuspSphere", "Submission.Model.Suspension", "Submission.SphereGenerator", "Submission.SphereHomotopy", "Submission.WhiteheadTheorem", "Submission.WhiteheadTheorem.Auxiliary", "Submission.WhiteheadTheorem.Basic", "Submission.WhiteheadTheorem.CWComplex.Basic", "Submission.WhiteheadTheorem.CWComplex.IProd.Def", "Submission.WhiteheadTheorem.CWComplex.IProd.Iso", "Submission.WhiteheadTheorem.Compressible.CWComplex", "Submission.WhiteheadTheorem.Compressible.Defs", "Submission.WhiteheadTheorem.Compressible.Disk", "Submission.WhiteheadTheorem.Compressible.WeakEquiv", "Submission.WhiteheadTheorem.Defs", "Submission.WhiteheadTheorem.Exponential", "Submission.WhiteheadTheorem.HEP.Cofibration", "Submission.WhiteheadTheorem.HEP.Cube", "Submission.WhiteheadTheorem.HEP.CubeJar", "Submission.WhiteheadTheorem.HEP.Retract", "Submission.WhiteheadTheorem.HomotopyGroup.ChangeBasePt", "Submission.WhiteheadTheorem.HomotopyGroup.InducedMaps", "Submission.WhiteheadTheorem.RelHomotopyGroup.Algebra", "Submission.WhiteheadTheorem.RelHomotopyGroup.Compression", "Submission.WhiteheadTheorem.RelHomotopyGroup.Defs", "Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq", "Submission.WhiteheadTheorem.Shapes.Cube", "Submission.WhiteheadTheorem.Shapes.CubeBoundaryMap", "Submission.WhiteheadTheorem.Shapes.Disk", "Submission.WhiteheadTheorem.Shapes.DiskHomeoCube", "Submission.WhiteheadTheorem.Shapes.Jar", "Submission.WhiteheadTheorem.Shapes.MappingCylinder", "Submission.WhiteheadTheorem.Shapes.Maps", "Submission.WhiteheadTheorem.Shapes.Pushout", "Submission.WhiteheadTheorem.Shapes.UnitInterval"]
  let entries := env.constants.toList.filter fun entry =>
    (match env.getModuleIdxFor? entry.1 with
      | some index => expectedModules.contains env.header.moduleNames[index]!.toString
      | none => false)
  let entries := entries.toArray.qsort fun a b => a.1.toString < b.1.toString
  unless !entries.isEmpty do
    throwError "MATH_GAUGE_EMPTY_AUDIT: no source-module constants were loaded"
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
  let mut axiomUnion : Array Name := #[]
  for (name, _) in entries do
    let deps ← Lean.collectAxioms name
    for ax in deps do
      unless axiomUnion.contains ax do
        axiomUnion := axiomUnion.push ax
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let axioms := axiomUnion.qsort fun a b => a.toString < b.toString
  let unexpected := axioms.filter fun name => !(allowed.contains name)
  let summary := Json.mkObj [("declaration_count", toJson entries.size),
    ("axiom_union", toJson (axioms.map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString)),
    ("passed", toJson unexpected.isEmpty)]
  logInfo m!"MATH_GAUGE_AUDIT_SUMMARY {summary.compress}"
  unless unexpected.isEmpty do
    throwError "MATH_GAUGE_FORBIDDEN_AXIOMS: {unexpected}"
