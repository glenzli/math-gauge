import StableImages

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
variable (hb : ∀ n (hn : N≤n), Function.Bijective (step T N I hmap n hn))

/-- The actual eventual-image premise implies this weaker existential image premise. -/
def ImageRealized : Prop := ∀ n, N≤n → ∃ m, ∃ hnm : n≤m, (T.transition n m hnm).range=I n

theorem imageRealized_of_stable
    (hs : ∀ n, N≤n → ∃ m, ∃ hnm : n≤m,
      ∀ k (hmk : m≤k), (T.transition n k (hnm.trans hmk)).range=I n) : ImageRealized T N I := by
  intro n hn
  obtain ⟨m,hnm,hm⟩ := hs n hn
  exact ⟨m,hnm,hm m le_rfl⟩

variable (A : Type v) [AddCommGroup A] [Module R A]

def evaluateStage (n : ℕ) : (T.stage n →ₗ[R] A) →ₗ[R] (I N →ₗ[R] A) where
  toFun f := f.comp (thread T N I hmap hb n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def recordMap : T.Record A →ₗ[R] (I N →ₗ[R] A) :=
  Module.DirectLimit.lift R ℕ _ (T.homTransition A) (evaluateStage T N I hmap hb A)
    (fun n m h f => by
      apply LinearMap.ext
      intro x
      exact congrArg f (LinearMap.congr_fun (thread_compatible T N I hmap hb n m h) x))

@[simp] theorem recordMap_of (n : ℕ) (f : T.stage n →ₗ[R] A) :
    recordMap T N I hmap hb A (T.recordOf A n f)=f.comp (thread T N I hmap hb n) :=
  Module.DirectLimit.lift_of _ _ _

variable (hI : ImageRealized T N I)

include hI in
theorem recordMap_zero (x : T.Record A) (hx : recordMap T N I hmap hb A x=0) : x=0 := by
  obtain ⟨n,f,rfl⟩ := T.record_exists A x
  let k := max N n
  have hNk : N≤k := le_max_left _ _
  have hnk : n≤k := le_max_right _ _
  let g := T.homTransition A n k hnk f
  have hg : g.comp (thread T N I hmap hb k)=0 := by
    rw [← recordMap_of T N I hmap hb A k g]
    change recordMap T N I hmap hb A (T.recordOf A k (T.homTransition A n k hnk f))=0
    rw [T.recordOf_transition]
    exact hx
  have hvan (z : I k) : g z=0 := by
    have hz := LinearMap.congr_fun hg (equiv T N I hmap hb N k le_rfl hNk z)
    change g (thread T N I hmap hb k (equiv T N I hmap hb N k le_rfl hNk z))=0 at hz
    rwa [thread_hits T N I hmap hb k hNk] at hz
  obtain ⟨m,hkm,hm⟩ := hI k hNk
  have hzero : T.homTransition A k m hkm g=0 := by
    apply LinearMap.ext
    intro z
    have hz : T.transition k m hkm z ∈ I k := by
      rw [← hm]
      exact ⟨z,rfl⟩
    exact hvan ⟨T.transition k m hkm z,hz⟩
  rw [← T.recordOf_transition A n k hnk f]
  change T.recordOf A k g=0
  rw [← T.recordOf_transition A k m hkm g,hzero,map_zero]

include hI in
theorem recordMap_injective : Function.Injective (recordMap T N I hmap hb A) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply recordMap_zero T N I hmap hb A hI
  rw [map_sub,hxy,sub_self]

include hI in
theorem recordMap_surjective : Function.Surjective (recordMap T N I hmap hb A) := by
  intro f
  obtain ⟨m,hNm,hm⟩ := hI N le_rfl
  let q : T.stage m →ₗ[R] I N := (T.transition N m hNm).codRestrict (I N) (by
    intro z
    rw [← hm]
    exact ⟨z,rfl⟩)
  refine ⟨T.recordOf A m (f.comp q),?_⟩
  rw [recordMap_of]
  apply LinearMap.ext
  intro x
  change f (q (thread T N I hmap hb m x))=f x
  congr 1
  apply Subtype.ext
  exact thread_base_projection T N I hmap hb m hNm x

def recordEquiv : T.Record A ≃ₗ[R] (I N →ₗ[R] A) :=
  LinearEquiv.ofBijective (recordMap T N I hmap hb A)
    ⟨recordMap_injective T N I hmap hb A hI,recordMap_surjective T N I hmap hb A hI⟩

include hmap hb hI

/-- A retraction is constructed at the stage where the actual image has arrived;
no retraction at the original N is assumed. -/
theorem exists_later_retraction :
    ∃ m, N≤m ∧ ∃ r : T.stage m →ₗ[R] I m, r.comp (I m).subtype=LinearMap.id := by
  obtain ⟨m,hNm,hm⟩ := hI N le_rfl
  let q : T.stage m →ₗ[R] I N := (T.transition N m hNm).codRestrict (I N) (by
    intro z
    rw [← hm]
    exact ⟨z,rfl⟩)
  let J := equiv T N I hmap hb N m le_rfl hNm
  refine ⟨m,hNm,J.symm.toLinearMap.comp q,?_⟩
  apply LinearMap.ext
  intro x
  exact J.symm_apply_apply x

/-- The equivalence acts on actual direct-limit records, is linear, and is natural
in every target module; the representing object is the actual I_N. -/
def representation : T.recordFunctor ≅ homFunctor (R := R) (I N) :=
  NatIso.ofComponents (fun A => (recordEquiv T N I hmap hb A hI).toModuleIso)
    (fun {A B} f => by
      apply ModuleCat.hom_ext
      apply Module.DirectLimit.hom_ext
      intro n
      apply LinearMap.ext
      intro g
      change recordMap T N I hmap hb B (T.recordMap f.hom (T.recordOf A n g))=
        f.hom.comp (recordMap T N I hmap hb A (T.recordOf A n g))
      rw [T.recordMap_of,recordMap_of,recordMap_of]
      rfl)

end MathGauge.Tower.Stable
