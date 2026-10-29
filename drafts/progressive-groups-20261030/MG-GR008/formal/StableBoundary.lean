import StableRecords
import RankOneModels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Module CategoryTheory MathGauge.TensorClassification
namespace MathGauge.Tower.StableBoundary
open FreeTower

def coefficients (n : ℕ) : ℤ := if n=0 then 2 else 1
abbrev exampleTower := RankOne.tower coefficients

def image (n : ℕ) : Submodule ℤ ℤ := (exampleTower.step n).range

theorem step_eq_id (n : ℕ) (hn : n≠0) : exampleTower.step n=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (if n=0 then (2:ℤ) else 1)*x=x
  simp [hn]

theorem transition_formula (n m : ℕ) (hnm : n≤m) :
    exampleTower.transition n m hnm=if n=m then LinearMap.id else exampleTower.step n := by
  induction m,hnm using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    rw [exampleTower.transition_succ n m h,ih]
    have hne : n≠m+1 := by omega
    rw [if_neg hne]
    by_cases he : n=m
    · subst n
      simp
    · rw [if_neg he,step_eq_id m (by omega),LinearMap.comp_id]

theorem image_succ (n : ℕ) : image (n+1)=⊤ := by
  rw [image,step_eq_id (n+1) (by omega)]
  exact LinearMap.range_id

theorem stable_image :
    ∀ n, 0≤n → ∃ m, ∃ hnm : n≤m,
      ∀ k (hmk : m≤k), (exampleTower.transition n k (hnm.trans hmk)).range=image n := by
  intro n _
  refine ⟨n+1,Nat.le_succ n,?_⟩
  intro k hk
  rw [transition_formula,if_neg (show n≠k by omega)]
  rfl

theorem maps_stable_image :
    ∀ n, 0≤n → ∀ x, x ∈ image (n+1) → exampleTower.step n x ∈ image n := by
  intro n _ x _
  exact ⟨x,rfl⟩

theorem stable_step_bijective : ∀ n (hn : 0≤n),
    Function.Bijective (Stable.step exampleTower 0 image maps_stable_image n hn) := by
  intro n hn
  have ha : coefficients n≠0 := by unfold coefficients; split <;> norm_num
  constructor
  · intro x y hxy
    apply Subtype.ext
    have he := congrArg Subtype.val hxy
    change coefficients n*x.1=coefficients n*y.1 at he
    exact mul_left_cancel₀ ha he
  · intro z
    obtain ⟨x,hx⟩ := z.2
    refine ⟨⟨x,?_⟩,?_⟩
    · rw [image_succ]; trivial
    · exact Subtype.ext hx

theorem no_retraction_at_zero :
    ¬ ∃ r : ℤ →ₗ[ℤ] image 0, r.comp (image 0).subtype=LinearMap.id := by
  rintro ⟨r,hr⟩
  let two : image 0 := ⟨2,1,by simp [RankOne.tower,coefficients]⟩
  have he := LinearMap.congr_fun hr two
  change r 2=two at he
  have hs : r (2:ℤ)=(2:ℤ) • r 1 := by simpa using r.map_smul (2:ℤ) 1
  rw [hs] at he
  have hv : (2:ℤ)*(r 1).1=2 := congrArg Subtype.val he
  have hv1 : (r 1).1=1 := by omega
  obtain ⟨z,hz⟩ := (r 1).2
  change (2:ℤ)*z=(r 1).1 at hz
  rw [hv1] at hz
  omega

theorem no_direct_summand_at_zero :
    ¬ ∃ J : Submodule ℤ ℤ, IsCompl (image 0) J := by
  rintro ⟨J,hJ⟩
  exact no_retraction_at_zero
    ⟨(image 0).linearProjOfIsCompl J hJ,
      Submodule.linearProjOfIsCompl_comp_subtype hJ⟩

def exampleRepresentation : exampleTower.recordFunctor ≅ homFunctor (R := ℤ) (image 0) :=
  Stable.representation exampleTower 0 image maps_stable_image stable_step_bijective
    (Stable.imageRealized_of_stable exampleTower 0 image stable_image)

theorem later_retraction_exists :
    ∃ m, 0≤m ∧ ∃ r : ℤ →ₗ[ℤ] image m, r.comp (image m).subtype=LinearMap.id :=
  Stable.exists_later_retraction exampleTower 0 image maps_stable_image stable_step_bijective
    (Stable.imageRealized_of_stable exampleTower 0 image stable_image)

end MathGauge.Tower.StableBoundary
