import TowerFiniteStage

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Module CategoryTheory MathGauge.TensorClassification
universe u v
namespace MathGauge.Tower.Stable
open FreeTower
variable {R : Type} [CommRing R]
variable (T : FreeTower.{u} R) (N : ℕ) (I : ∀ n, Submodule R (T.stage n))
variable (hmap : ∀ n, N≤n → ∀ x, x ∈ I (n+1) → T.step n x ∈ I n)

def step (n : ℕ) (hn : N≤n) : I (n+1) →ₗ[R] I n :=
  ((T.step n).comp (I (n+1)).subtype).codRestrict (I n) (fun x => hmap n hn x x.2)

include hmap in
theorem transition_mem (n m : ℕ) (hn : N≤n) (hnm : n≤m) (x : T.stage m) (hx : x ∈ I m) :
    T.transition n m hnm x ∈ I n := by
  induction m,hnm using Nat.le_induction with
  | base => simpa using hx
  | succ m h ih =>
    rw [T.transition_succ n m h]
    exact ih (T.step m x) (hmap m (hn.trans h) x hx)

def transition (n m : ℕ) (hn : N≤n) (hnm : n≤m) : I m →ₗ[R] I n :=
  ((T.transition n m hnm).comp (I m).subtype).codRestrict (I n)
    (fun x => transition_mem T N I hmap n m hn hnm x x.2)

@[simp] theorem transition_self (n : ℕ) (hn : N≤n) :
    transition T N I hmap n n hn le_rfl=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (T.transition_self n) x

theorem transition_comp (n m k : ℕ) (hn : N≤n) (hnm : n≤m) (hmk : m≤k) :
    (transition T N I hmap n m hn hnm).comp (transition T N I hmap m k (hn.trans hnm) hmk)=
      transition T N I hmap n k hn (hnm.trans hmk) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (T.transition_comp n m k hnm hmk) x

theorem transition_succ (n m : ℕ) (hn : N≤n) (hnm : n≤m) :
    transition T N I hmap n (m+1) hn (Nat.le_succ_of_le hnm)=
      (transition T N I hmap n m hn hnm).comp (step T N I hmap m (hn.trans hnm)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (T.transition_succ n m hnm) x

variable (hb : ∀ n (hn : N≤n), Function.Bijective (step T N I hmap n hn))

include hb in
theorem transition_bijective (n m : ℕ) (hn : N≤n) (hnm : n≤m) :
    Function.Bijective (transition T N I hmap n m hn hnm) := by
  induction m,hnm using Nat.le_induction with
  | base => simpa using Function.bijective_id
  | succ m h ih =>
    rw [transition_succ T N I hmap n m hn h]
    exact ih.comp (hb m (hn.trans h))

def equiv (n m : ℕ) (hn : N≤n) (hnm : n≤m) : I m ≃ₗ[R] I n :=
  LinearEquiv.ofBijective (transition T N I hmap n m hn hnm)
    (transition_bijective T N I hmap hb n m hn hnm)

theorem inverse_transition (n m : ℕ) (hn : N≤n) (hnm : n≤m) (x : I N) :
    transition T N I hmap n m hn hnm ((equiv T N I hmap hb N m le_rfl (hn.trans hnm)).symm x)=
      (equiv T N I hmap hb N n le_rfl hn).symm x := by
  apply (equiv T N I hmap hb N n le_rfl hn).injective
  calc
    _ = equiv T N I hmap hb N m le_rfl (hn.trans hnm)
        ((equiv T N I hmap hb N m le_rfl (hn.trans hnm)).symm x) :=
      LinearMap.congr_fun (transition_comp T N I hmap N n m le_rfl hn hnm) _
    _ = x := LinearEquiv.apply_symm_apply _ _
    _ = _ := (LinearEquiv.apply_symm_apply _ _).symm

/-- A compatible actual element of every original stage, constructed from I_N. -/
def thread (n : ℕ) : I N →ₗ[R] T.stage n :=
  if hn : N≤n then (I n).subtype.comp (equiv T N I hmap hb N n le_rfl hn).symm.toLinearMap
  else (T.transition n N (le_of_not_ge hn)).comp (I N).subtype

theorem thread_above (n : ℕ) (hn : N≤n) :
    thread T N I hmap hb n=(I n).subtype.comp (equiv T N I hmap hb N n le_rfl hn).symm.toLinearMap :=
  dif_pos hn

theorem thread_hits (n : ℕ) (hn : N≤n) (z : I n) :
    thread T N I hmap hb n (equiv T N I hmap hb N n le_rfl hn z)=z := by
  rw [thread_above T N I hmap hb n hn]
  exact congrArg Subtype.val ((equiv T N I hmap hb N n le_rfl hn).symm_apply_apply z)

theorem thread_base_projection (n : ℕ) (hn : N≤n) (x : I N) :
    T.transition N n hn (thread T N I hmap hb n x)=x := by
  rw [thread_above T N I hmap hb n hn]
  exact congrArg Subtype.val ((equiv T N I hmap hb N n le_rfl hn).apply_symm_apply x)

theorem thread_compatible (n m : ℕ) (hnm : n≤m) :
    (T.transition n m hnm).comp (thread T N I hmap hb m)=thread T N I hmap hb n := by
  apply LinearMap.ext
  intro x
  by_cases hn : N≤n
  · rw [thread_above T N I hmap hb m (hn.trans hnm),thread_above T N I hmap hb n hn]
    exact congrArg Subtype.val (inverse_transition T N I hmap hb n m hn hnm x)
  · by_cases hm : N≤m
    · change T.transition n m hnm (thread T N I hmap hb m x)=_
      rw [show thread T N I hmap hb n=(T.transition n N (le_of_not_ge hn)).comp (I N).subtype from dif_neg hn]
      rw [← T.transition_comp n N m (le_of_not_ge hn) hm]
      change T.transition n N _ (T.transition N m hm (thread T N I hmap hb m x))=_
      rw [thread_base_projection T N I hmap hb m hm]
      rfl
    · simp only [thread,dif_neg hn,dif_neg hm,LinearMap.comp_apply]
      exact LinearMap.congr_fun (T.transition_comp n m N hnm (le_of_not_ge hm)) x

end MathGauge.Tower.Stable
