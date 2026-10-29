import DyadicUnits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Module CategoryTheory MathGauge.TensorClassification
namespace MathGauge.Tower.Dyadic
open FreeTower Examples

def conjugateEnd :
    (doublingTower.Invariant →ₗ[ℤ] doublingTower.Invariant) ≃ₗ[ℤ] (D →ₗ[ℤ] D) :=
  LinearEquiv.arrowCongr doublingInvariantEquivDyadic doublingInvariantEquivDyadic

theorem conjugateEnd_id : conjugateEnd LinearMap.id=LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [conjugateEnd,LinearEquiv.arrowCongr_apply]

theorem conjugateEnd_comp (f g : doublingTower.Invariant →ₗ[ℤ] doublingTower.Invariant) :
    conjugateEnd (f.comp g)=(conjugateEnd f).comp (conjugateEnd g) := by
  apply LinearMap.ext
  intro x
  simp [conjugateEnd,LinearEquiv.arrowCongr_apply,LinearMap.comp_apply]

/-- This equivalence ranges over every natural transformation of the actual
record functor, rather than over a preselected family of scalar maps. -/
def naturalEndEquiv : (doublingTower.recordFunctor ⟶ doublingTower.recordFunctor) ≃ D :=
  (doublingTower.recordNatEquiv doublingTower).trans
    (conjugateEnd.toEquiv.trans endomorphismEquiv)

theorem naturalEnd_id : naturalEndEquiv (𝟙 doublingTower.recordFunctor)=one := by
  change endomorphismEquiv (conjugateEnd
    (doublingTower.recordNatEquiv doublingTower (𝟙 doublingTower.recordFunctor)))=one
  rw [FreeTower.recordNatEquiv_id,conjugateEnd_id,endomorphism_coefficient_id]

theorem naturalEnd_comp
    (η ξ : doublingTower.recordFunctor ⟶ doublingTower.recordFunctor) :
    (naturalEndEquiv (η ≫ ξ)).1=(naturalEndEquiv ξ).1*(naturalEndEquiv η).1 := by
  change (endomorphismEquiv (conjugateEnd
    (doublingTower.recordNatEquiv doublingTower (η ≫ ξ)))).1=_
  rw [FreeTower.recordNatEquiv_comp,conjugateEnd_comp,endomorphism_coefficient_comp]
  rfl

theorem naturalEnd_add
    (η ξ : doublingTower.recordFunctor ⟶ doublingTower.recordFunctor) :
    naturalEndEquiv (η+ξ)=naturalEndEquiv η+naturalEndEquiv ξ := by
  have hadd : doublingTower.recordNatEquiv doublingTower (η+ξ)=
      doublingTower.recordNatEquiv doublingTower η+
        doublingTower.recordNatEquiv doublingTower ξ := by
    change tensorNatHom (doublingTower.tensorRecordNatIso.hom ≫ (η+ξ) ≫
      doublingTower.tensorRecordNatIso.inv)=_
    rw [Preadditive.add_comp,Preadditive.comp_add]
    apply LinearMap.ext
    intro x
    simp only [tensorNatHom,NatTrans.app_add]
    change (unitEquiv doublingTower.Invariant) (_+_)=_
    rw [map_add]
    rfl
  change endomorphismEquiv (conjugateEnd
    (doublingTower.recordNatEquiv doublingTower (η+ξ)))=_
  rw [hadd,map_add,endomorphism_coefficient_add]
  rfl

theorem naturalEnd_invertible_iff
    (η : doublingTower.recordFunctor ⟶ doublingTower.recordFunctor) :
    (∃ ξ, η ≫ ξ=𝟙 _ ∧ ξ ≫ η=𝟙 _) ↔
      ∃ k : ℤ, (naturalEndEquiv η).1=(2:ℚ)^k ∨
        (naturalEndEquiv η).1=-(2:ℚ)^k := by
  rw [← reciprocal_iff_signed_power]
  constructor
  · rintro ⟨ξ,hξ,_⟩
    refine ⟨naturalEndEquiv ξ,?_⟩
    have h := congrArg (fun t => (naturalEndEquiv t).1) hξ
    dsimp only at h
    rw [naturalEnd_comp,naturalEnd_id] at h
    simpa only [mul_comm] using h
  · rintro ⟨s,hs⟩
    let ξ := naturalEndEquiv.symm s
    have hξ : naturalEndEquiv ξ=s := naturalEndEquiv.apply_symm_apply s
    refine ⟨ξ,?_,?_⟩ <;> apply naturalEndEquiv.injective <;> apply Subtype.ext
    · rw [naturalEnd_comp,hξ,naturalEnd_id]
      exact (mul_comm _ _).trans hs
    · rw [naturalEnd_comp,hξ,naturalEnd_id]
      exact hs

/-- Every signed integral power produces an actual natural automorphism. -/
def naturalAutomorphism (r : D)
    (hr : ∃ k : ℤ, r.1=(2:ℚ)^k ∨ r.1=-(2:ℚ)^k) :
    doublingTower.recordFunctor ≅ doublingTower.recordFunctor := by
  let η := naturalEndEquiv.symm r
  have hη : ∃ ξ, η ≫ ξ=𝟙 _ ∧ ξ ≫ η=𝟙 _ :=
    (naturalEnd_invertible_iff η).mpr (by
      simpa only [η,naturalEndEquiv.apply_symm_apply] using hr)
  exact ⟨η,Classical.choose hη,(Classical.choose_spec hη).1,
    (Classical.choose_spec hη).2⟩

theorem naturalAutomorphism_coefficient (r : D)
    (hr : ∃ k : ℤ, r.1=(2:ℚ)^k ∨ r.1=-(2:ℚ)^k) :
    naturalEndEquiv (naturalAutomorphism r hr).hom=r :=
  naturalEndEquiv.apply_symm_apply r

theorem every_natural_automorphism
    (e : doublingTower.recordFunctor ≅ doublingTower.recordFunctor) :
    ∃ k : ℤ, (naturalEndEquiv e.hom).1=(2:ℚ)^k ∨
      (naturalEndEquiv e.hom).1=-(2:ℚ)^k :=
  (naturalEnd_invertible_iff e.hom).mp ⟨e.inv,e.hom_inv_id,e.inv_hom_id⟩

end MathGauge.Tower.Dyadic
