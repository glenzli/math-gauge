import MappingNaturality

noncomputable section
open TopologicalSpace Topology Set CategoryTheory
universe u
namespace MathGauge.GR010.LocalCompact

variable {X X' Y Y' Z Z' : Type u}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
  [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace Z']

/-- Ordinary evaluation, with local compactness only on its input X. -/
theorem evaluation_continuous [LocallyCompactSpace X] :
    Continuous (fun p : C(X,Y) × X => p.1 p.2) := continuous_eval

/-- Z need not be locally compact: this is a bijection of continuous maps,
not an assertion about a compact-open topology on the outer mapping spaces. -/
def exponential [LocallyCompactSpace X] : C(Z,C(X,Y)) ≃ C(Z × X,Y) where
  toFun := ContinuousMap.uncurry
  invFun := ContinuousMap.curry
  left_inv f := by ext z x; rfl
  right_inv f := by ext p; rfl

theorem parameter_natural [LocallyCompactSpace X]
    (g : C(Z,C(X,Y))) (v : C(Z',Z)) :
    exponential (g.comp v) = (exponential g).comp (v.prodMap (ContinuousMap.id X)) := by
  ext p; rfl

theorem input_output_natural [LocallyCompactSpace X] [LocallyCompactSpace X']
    (g : C(Z,C(X,Y))) (a : C(X',X)) (b : C(Y,Y')) :
    exponential (⟨fun z => b.comp ((g z).comp a),
      (ContinuousMap.continuous_postcomp b).comp
        ((ContinuousMap.continuous_precomp a).comp g.continuous)⟩ : C(Z,C(X',Y'))) =
      b.comp ((exponential g).comp ((ContinuousMap.id Z).prodMap a)) := by
  ext p; rfl

end MathGauge.GR010.LocalCompact
