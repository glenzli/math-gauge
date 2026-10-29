import MappingUniverse

noncomputable section
open TopologicalSpace Topology Set
universe u
namespace MathGauge.GR010.JointComposition
open MathGauge.Mapping

variable {X Y Z T : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace T]

/-- The uncurried composition varies all three entries simultaneously and
uses only the proved continuous evaluation on compactly generated products. -/
def uncurriedComposition [T2Space X] [T2Space Y] :
    C(kprod (kprod (Realization Y Z) (Realization X Y)) (Kify X),Kify Z) :=
  keval.comp (kpair
    ((kfst (Realization Y Z) (Realization X Y)).comp
      (kfst (kprod (Realization Y Z) (Realization X Y)) (Kify X)))
    (keval.comp (kpair
      ((ksnd (Realization Y Z) (Realization X Y)).comp
        (kfst (kprod (Realization Y Z) (Realization X Y)) (Kify X)))
      (ksnd (kprod (Realization Y Z) (Realization X Y)) (Kify X)))))

def composition [T2Space X] [T2Space Y] :
    C(kprod (Realization Y Z) (Realization X Y),Realization X Z) :=
  kcurry uncurriedComposition

@[simp] theorem composition_apply [T2Space X] [T2Space Y]
    (g : Realization Y Z) (f : Realization X Y) (x : Kify X) :
    kdown (composition (kup (g,f))) x=kdown g (kdown f x) := rfl

def identity (X : Type u) [TopologicalSpace X] : Realization X X :=
  kup (ContinuousMap.id (Kify X))

theorem composition_assoc [T2Space X] [T2Space Y] [T2Space Z]
    (h : Realization Z T) (g : Realization Y Z) (f : Realization X Y) :
    composition (kup (h,composition (kup (g,f))))=
      composition (kup (composition (kup (h,g)),f)) := by
  apply ContinuousMap.ext
  intro x
  rfl

theorem identity_comp [T2Space X] [T2Space Y] (f : Realization X Y) :
    composition (kup (identity Y,f))=f := by
  apply ContinuousMap.ext
  intro x
  rfl

theorem comp_identity [T2Space X] (f : Realization X Y) :
    composition (kup (f,identity X))=f := by
  apply ContinuousMap.ext
  intro x
  rfl

end MathGauge.GR010.JointComposition
