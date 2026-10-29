import TowerStageTools
import Mathlib.CategoryTheory.Limits.Preserves.Finite

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open CategoryTheory CategoryTheory.Limits
open MathGauge.TensorClassification

universe u
namespace MathGauge.Tower.FreeTower
variable {R : Type} [CommRing R] (T : FreeTower.{u} R)
variable {J K : Type u} (D : ModuleDiagram R J K)

def recordsDiagram : ModuleDiagram R J K where
  obj j := ModuleCat.of R (T.Record (D.obj j))
  source := D.source
  target := D.target
  map k := T.recordMap (D.map k)

/-- The canonical record comparison on compatible families, induced by the
actual projections of the limit. -/
def recordComparison : T.Record D.compatible →ₗ[R] (T.recordsDiagram D).compatible :=
  (LinearMap.pi fun j => T.recordMap (D.projection j)).codRestrict _ (by
    intro t k
    have he : (D.map k).comp (D.projection (D.source k)) = D.projection (D.target k) := by
      ext x
      exact x.2 k
    change T.recordMap (D.map k) (T.recordMap (D.projection (D.source k)) t) =
      T.recordMap (D.projection (D.target k)) t
    rw [← LinearMap.comp_apply, ← T.recordMap_comp, he])

@[simp] theorem recordComparison_apply (x : T.Record D.compatible) (j : J) :
    (T.recordComparison D x).1 j = T.recordMap (D.projection j) x := rfl

@[simp] theorem recordComparison_of (n : ℕ) (f : T.stage n →ₗ[R] D.compatible) (j : J) :
    (T.recordComparison D (T.recordOf D.compatible n f)).1 j =
      T.recordOf (D.obj j) n ((D.projection j).comp f) := T.recordMap_of _ _ _

theorem recordComparison_injective [Finite J] : Function.Injective (T.recordComparison D) := by
  intro x y hxy
  obtain ⟨n,f,rfl⟩ := T.record_exists D.compatible x
  obtain ⟨m,g,rfl⟩ := T.record_exists D.compatible y
  have he (j : J) : T.recordOf (D.obj j) n ((D.projection j).comp f) =
      T.recordOf (D.obj j) m ((D.projection j).comp g) := by
    simpa only [T.recordComparison_of] using congrArg
      (fun z : (T.recordsDiagram D).compatible => z.1 j) hxy
  obtain ⟨r,hnr,hmr,hr⟩ := T.finite_equalities_common_stage (fun j => (D.obj j : Type u)) n m
    (fun j => (D.projection j).comp f) (fun j => (D.projection j).comp g) he
  apply (T.record_eq_iff D.compatible n m f g).mpr
  refine ⟨r,hnr,hmr,?_⟩
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  funext j
  exact LinearMap.congr_fun (hr j) z

theorem recordComparison_surjective [Finite J] [Finite K] :
    Function.Surjective (T.recordComparison D) := by
  intro y
  obtain ⟨n,f,hf⟩ := T.finite_records_common_stage (fun j => (D.obj j : Type u)) y.1
  have he (k : K) :
      T.recordOf (D.obj (D.target k)) n ((D.map k).comp (f (D.source k))) =
        T.recordOf (D.obj (D.target k)) n (f (D.target k)) := by
    rw [← T.recordMap_of, hf, hf]
    exact y.2 k
  obtain ⟨r,hnr,hnr',hr⟩ := T.finite_equalities_common_stage
    (fun k => (D.obj (D.target k) : Type u)) n n
    (fun k => (D.map k).comp (f (D.source k))) (fun k => f (D.target k)) he
  let v : T.stage r →ₗ[R] D.compatible :=
    (LinearMap.pi fun j => T.homTransition (D.obj j) n r hnr (f j)).codRestrict _ (by
      intro z k
      exact LinearMap.congr_fun (hr k) z)
  refine ⟨T.recordOf D.compatible r v, ?_⟩
  apply Subtype.ext
  funext j
  rw [T.recordComparison_of]
  change T.recordOf (D.obj j) r (T.homTransition (D.obj j) n r hnr (f j)) = y.1 j
  rw [T.recordOf_transition, hf]

theorem recordComparison_bijective [Finite J] [Finite K] :
    Function.Bijective (T.recordComparison D) :=
  ⟨T.recordComparison_injective D, T.recordComparison_surjective D⟩

variable {I : Type u} [Category.{u} I]

/-- Preservation is proved for the standard categorical limit, by inverting the
canonical comparison constructed above. Empty diagrams are included. -/
def finiteRecordConeIsLimit (D : I ⥤ ModuleCat.{u} R)
    [Finite I] [Finite (Σ i j : I, i ⟶ j)] :
    IsLimit (T.recordFunctor.mapCone (categoryCone D)) := by
  let e : T.Record (categoryDiagram D).compatible ≃ₗ[R]
      (categoryDiagram (D ⋙ T.recordFunctor)).compatible :=
    LinearEquiv.ofBijective (T.recordComparison (categoryDiagram D))
      (T.recordComparison_bijective (categoryDiagram D))
  refine
    { lift := fun s => ModuleCat.ofHom (e.symm.toLinearMap.comp (categoryLift _ s))
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun z => z.1 j) (e.apply_symm_apply (categoryLift _ s x))
  · intro s m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply e.injective
    change e (m x) = e (e.symm (categoryLift _ s x))
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext j
    exact congrArg (fun h => h x) (hm j)

theorem preserves_every_finite_limit (D : I ⥤ ModuleCat.{u} R)
    [Finite I] [Finite (Σ i j : I, i ⟶ j)] : PreservesLimit D T.recordFunctor :=
  preservesLimit_of_preserves_limit_cone (categoryConeIsLimit D) (T.finiteRecordConeIsLimit D)

end MathGauge.Tower.FreeTower
