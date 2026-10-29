import TowerDoublingExample

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Module CategoryTheory MathGauge.TensorClassification
namespace MathGauge.Tower.RankOne
open FreeTower Examples

@[reducible] def tower (a : ℕ → ℤ) : FreeTower ℤ where
  stage _ := ModuleCat.of ℤ ℤ
  step n := a n • LinearMap.id
  free _ := inferInstance
  finite _ := inferInstance

def CofinalZeros (a : ℕ → ℤ) : Prop := ∀ N, ∃ n, N≤n ∧ a n=0

def EventualUnits (a : ℕ → ℤ) : Prop := ∃ N, ∀ n, N≤n → IsUnit (a n)

theorem integer_idempotent (d : ℤ →ₗ[ℤ] ℤ) (hd : d.comp d=d) : d=0 ∨ d=LinearMap.id := by
  have he := LinearMap.congr_fun hd 1
  change d (d 1)=d 1 at he
  rw [int_linear_apply] at he
  have hz : d 1*(d 1-1)=0 := by nlinarith
  rcases mul_eq_zero.mp hz with h0 | h1
  · left
    apply LinearMap.ext
    intro z
    rw [int_linear_apply,h0,mul_zero]
    rfl
  · right
    have h1' : d 1=1 := sub_eq_zero.mp h1
    apply LinearMap.ext
    intro z
    rw [int_linear_apply,h1',mul_one]
    rfl

theorem transition_killed (a : ℕ → ℤ) {n j : ℕ} (hnj : n≤j) (hj : a j=0) :
    (tower a).transition n (j+1) (Nat.le_succ_of_le hnj)=0 := by
  rw [(tower a).transition_succ n j hnj]
  apply LinearMap.ext
  intro x
  change (tower a).transition n j hnj (a j*x)=0
  rw [hj,zero_mul,map_zero]

theorem transition_injective (a : ℕ → ℤ) {N : ℕ} (ha : ∀ j, N≤j → a j≠0)
    (n m : ℕ) (hn : N≤n) (hnm : n≤m) : Function.Injective ((tower a).transition n m hnm) := by
  induction m,hnm using Nat.le_induction with
  | base => simpa using Function.injective_id
  | succ m h ih =>
    rw [(tower a).transition_succ n m h]
    apply ih.comp
    intro x y he
    exact mul_left_cancel₀ (ha m (hn.trans h)) he

theorem transition_bijective (a : ℕ → ℤ) {N : ℕ} (ha : ∀ j, N≤j → IsUnit (a j))
    (n m : ℕ) (hn : N≤n) (hnm : n≤m) : Function.Bijective ((tower a).transition n m hnm) := by
  induction m,hnm using Nat.le_induction with
  | base => simpa using Function.bijective_id
  | succ m h ih =>
    rw [(tower a).transition_succ n m h]
    have hs : Function.Bijective ((tower a).step m) := by
      change Function.Bijective (fun x : ℤ => a m*x)
      rcases Int.isUnit_iff.mp (ha m (hn.trans h)) with h1 | hm1
      · simpa only [h1,one_mul] using Function.bijective_id
      · rw [hm1]
        exact ⟨fun x y he => by linarith,fun y => ⟨-y,by ring⟩⟩
    exact ih.comp hs

theorem cofinalZeros_finiteStage (a : ℕ → ℤ) (ha : CofinalZeros a) : (tower a).FiniteStageCriterion := by
  refine ⟨0,0,by simp,?_⟩
  intro m hm
  obtain ⟨j,hmj,hj⟩ := ha m
  refine ⟨0,j+1,Nat.le_succ_of_le hmj,by simp,by simp,?_⟩
  rw [LinearMap.zero_comp,transition_killed a hmj hj]

theorem eventualUnits_finiteStage (a : ℕ → ℤ) (ha : EventualUnits a) : (tower a).FiniteStageCriterion := by
  obtain ⟨N,hN⟩ := ha
  refine ⟨N,LinearMap.id,by simp,?_⟩
  intro m hm
  let e := LinearEquiv.ofBijective ((tower a).transition N m hm) (transition_bijective a hN N m le_rfl hm)
  refine ⟨e.symm.toLinearMap,m,le_rfl,by simp,?_,?_⟩
  · apply LinearMap.ext
    exact e.apply_symm_apply
  · rw [(tower a).transition_self]
    apply LinearMap.ext
    exact e.symm_apply_apply

theorem finiteStage_classification (a : ℕ → ℤ) :
    (tower a).FiniteStageCriterion ↔ CofinalZeros a ∨ EventualUnits a := by
  constructor
  · rintro ⟨n,d,hd,ht⟩
    rcases integer_idempotent d hd with hzero | hone
    · left
      intro N
      by_contra hno
      push_neg at hno
      let m := max n N
      obtain ⟨u,r,hmr,hud,_,huρ⟩ := ht m (le_max_left _ _)
      have hu : u=0 := by simpa only [hzero,LinearMap.comp_zero] using hud.symm
      have hz : (tower a).transition m r hmr=0 := by simpa only [hu,LinearMap.zero_comp] using huρ.symm
      have hi := transition_injective a hno m r (le_max_right _ _) hmr
      have he : (tower a).transition m r hmr 0=(tower a).transition m r hmr 1 := by rw [hz]; rfl
      have hbad : (0:ℤ)=1 := hi he
      norm_num at hbad
    · right
      refine ⟨n,?_⟩
      intro j hj
      obtain ⟨u,r,hmr,_,hρu,_⟩ := ht (j+1) (Nat.le_succ_of_le hj)
      have he := LinearMap.congr_fun hρu 1
      rw [hone] at he
      change (tower a).transition n (j+1) _ (u 1)=1 at he
      rw [(tower a).transition_succ n j hj] at he
      change (tower a).transition n j hj (a j*u 1)=1 at he
      have hs := ((tower a).transition n j hj).map_smul (a j) (u 1)
      simp only [smul_eq_mul] at hs
      rw [hs] at he
      exact isUnit_of_mul_eq_one _ he
  · rintro (hz | hu)
    · exact cofinalZeros_finiteStage a hz
    · exact eventualUnits_finiteStage a hu

theorem representability_classification (a : ℕ → ℤ) :
    (tower a).Representable ↔ CofinalZeros a ∨ EventualUnits a :=
  (tower a).finiteStage_iff_representable.symm.trans (finiteStage_classification a)

end MathGauge.Tower.RankOne
