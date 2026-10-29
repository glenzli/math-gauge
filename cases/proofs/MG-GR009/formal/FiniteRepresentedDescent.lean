import FibreAutomorphisms
import FreeOrbitDescent

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite
universe u g w
namespace MathGauge.Descent.FiniteFibres
variable {Γ : Type g} [Group Γ] [Finite Γ]
variable (T X : Profinite.{u}) [MulAction Γ T] [MulAction Γ X]
variable [ContinuousConstSMul Γ T] [ContinuousConstSMul Γ X]
variable (π : X →ₑ[(id : Γ → Γ)] T) (hπ : Continuous π)

/-- The actual represented equivariant object; continuity is automatic for the
finite discrete sets in S2. The result also holds for profinite X. -/
def representedRecord : EquivariantOver (FiniteOrbit.action.{u,g,w} (Γ := Γ) T) where
  sheaf := prof_probe_sheaf.{u,w} X
  projection := ⟨(MathGauge.Mapping.lift_nat_equiv _ _)
    (MathGauge.Mapping.probe_post ⟨π,hπ⟩)⟩
  action := FiniteOrbit.action.{u,g,w} (Γ := Γ) X
  equivariant a := by
    ext U f x
    exact π.map_smul a (f.down x)

theorem represented_stabilizer_iff_point :
    (representedRecord.{u,g,w} T X π hπ).StabilizerTrivial ↔ PointTrivial π := by
  constructor
  · intro h a x hx
    let e : (prof_probe_sheaf.{u,w} X).obj.obj (op ProfPoint) := ⟨ContinuousMap.const _ x⟩
    have he : ((FiniteOrbit.action.{u,g,w} (Γ := Γ) T).act a).app (op ProfPoint)
        ((representedRecord.{u,g,w} T X π hπ).projection.hom.app (op ProfPoint) e) =
        (representedRecord.{u,g,w} T X π hπ).projection.hom.app (op ProfPoint) e := by
      apply ULift.ext
      ext t
      exact hx
    have hfix := h (op ProfPoint) e a he
    exact congrArg (fun f => f.down PUnit.unit) hfix
  · intro h U f a ha
    apply ULift.ext
    ext x
    exact h a (f.down x) (congrArg (fun s => s.down x) ha)

/-- Exact criterion using only the stabilizer action on representative fibres. -/
theorem represented_realizable_iff :
    (representedRecord.{u,g,w} T X π hπ).Realizable ↔ FibreTrivial π := by
  rw [EquivariantOver.realizable_iff_stabilizer_trivial,
    represented_stabilizer_iff_point,pointTrivial_iff_fibreTrivial]

/-- A realizable object's equivariant automorphism group is the full product of
symmetric groups, including the unique permutation of an empty fibre. -/
def represented_automorphismGroup
    (h : (representedRecord.{u,g,w} T X π hπ).Realizable) :
    AutOver π ≃* (∀ o : OrbitIndex (Γ := Γ) (T := T), Equiv.Perm (Fibre π (representative o))) :=
  automorphismGroupEquiv π ((represented_realizable_iff.{u,g,w} T X π hπ).mp h)

end MathGauge.Descent.FiniteFibres
