import CompletionStructure

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace MathGauge.AdicBridge
open MathGauge.CompletionFailure MathGauge.CompletionStructure
universe u v
variable {R : Type u} [CommRing R] (t : R)
variable (M : Type v) [AddCommGroup M] [Module R M]

abbrev principal := Ideal.span {t}

def levelEquiv (n : ℕ) : Level t M n ≃ₗ[R] M ⧸ ((principal t)^n • (⊤ : Submodule R M)) :=
  Submodule.quotEquivOfEq _ _ (principal_power t n).symm

@[simp] theorem levelEquiv_mk (n : ℕ) (x : M) :
    levelEquiv t M n ((powerSub t M n).mkQ x)=((principal t)^n • (⊤ : Submodule R M)).mkQ x := rfl

@[simp] theorem levelEquiv_symm_mk (n : ℕ) (x : M) :
    (levelEquiv t M n).symm (((principal t)^n • (⊤ : Submodule R M)).mkQ x)=
      (powerSub t M n).mkQ x := rfl

theorem levelEquiv_reduce {n m : ℕ} (h : n≤m) (x : Level t M m) :
    AdicCompletion.transitionMap (principal t) M h (levelEquiv t M m x)=
      levelEquiv t M n (reduce t M h x) := by
  induction x using Submodule.Quotient.induction_on (powerSub t M m) with
  | H a => rfl

def toAdic (x : completion t M) : AdicCompletion (principal t) M :=
  ⟨fun n => levelEquiv t M n (x.val n),by
    intro n m h
    rw [levelEquiv_reduce,x.property n m h]⟩

def fromAdic (x : AdicCompletion (principal t) M) : completion t M :=
  ⟨fun n => (levelEquiv t M n).symm (x.val n),by
    intro n m h
    apply (levelEquiv t M n).injective
    rw [← levelEquiv_reduce,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    exact x.property h⟩

def adicEquiv : completion t M ≃ₗ[R] AdicCompletion (principal t) M where
  toFun := toAdic t M
  invFun := fromAdic t M
  left_inv x := by apply Subtype.ext;funext n;exact (levelEquiv t M n).symm_apply_apply (x.val n)
  right_inv x := by apply AdicCompletion.ext;intro n;exact (levelEquiv t M n).apply_symm_apply (x.val n)
  map_add' x y := by apply AdicCompletion.ext;intro n;exact map_add _ _ _
  map_smul' r x := by apply AdicCompletion.ext;intro n;exact (levelEquiv t M n).map_smul r (x.val n)

@[simp] theorem adicEquiv_canonical (x : M) :
    adicEquiv t M (canonical t x)=AdicCompletion.of (principal t) M x := by
  apply AdicCompletion.ext
  intro n
  rfl

@[simp] theorem adicEquiv_eval (x : completion t M) (n : ℕ) :
    AdicCompletion.eval (principal t) M n (adicEquiv t M x)=levelEquiv t M n (eval t n x) := rfl

/-- The actual nth projection kernel on the completion is t^n times the
completion itself, transported through the exact principal-ideal identity. -/
theorem evaluation_kernel (n : ℕ) :
    (eval t n : completion t M →ₗ[R] Level t M n).ker=powerSub t (completion t M) n := by
  ext x
  constructor
  · intro hx
    have hzero : AdicCompletion.eval (principal t) M n (adicEquiv t M x)=0 := by
      rw [adicEquiv_eval,show eval t n x=0 from hx,map_zero]
    have hmem : adicEquiv t M x∈powerSub t (AdicCompletion (principal t) M) n := by
      rw [← principal_power t n,AdicCompletion.pow_smul_top_eq_ker_eval (I := principal t) (M := M) (n := n) (show (principal t).FG from Submodule.fg_span_singleton t)]
      exact hzero
    obtain ⟨y,hy⟩ := hmem
    refine ⟨(adicEquiv t M).symm y,?_⟩
    change (t^n) • (adicEquiv t M).symm y=x
    apply (adicEquiv t M).injective
    rw [map_smul,LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y,rfl⟩
    change eval t n ((t^n) • y)=0
    apply (levelEquiv t M n).injective
    rw [map_zero,← adicEquiv_eval,map_smul]
    have hmem : (t^n) • adicEquiv t M y∈((principal t)^n •
        (⊤ : Submodule R (AdicCompletion (principal t) M))) := by
      rw [principal_power t n]
      exact ⟨adicEquiv t M y,rfl⟩
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := principal t) (M := M) (n := n) (show (principal t).FG from Submodule.fg_span_singleton t)] at hmem
    exact hmem

theorem canonical_bijective_on_completion :
    Function.Bijective (canonical t : completion t M →ₗ[R] completion t (completion t M)) := by
  let I := principal t
  letI : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete (Submodule.fg_span_singleton t)
  let e := adicEquiv t M
  let e₂ := (completedEquiv t e).trans (adicEquiv t (AdicCompletion I M))
  have he (x : completion t M) : e₂ (canonical t x)=AdicCompletion.of I (AdicCompletion I M) (e x) := by
    change adicEquiv t (AdicCompletion I M) (completionMap t (completion t M) e.toLinearMap
      (canonical t x))=_
    rw [completed_map_canonical,adicEquiv_canonical]
    rfl
  constructor
  · intro x y hxy
    apply e.injective
    apply AdicCompletion.of_injective I (AdicCompletion I M)
    rw [← he,← he,hxy]
  · intro z
    obtain ⟨y,hy⟩ := AdicCompletion.of_surjective I (AdicCompletion I M) (e₂ z)
    refine ⟨e.symm y,?_⟩
    apply e₂.injective
    rw [he,LinearEquiv.apply_symm_apply,hy]

def canonicalDoubleEquiv : completion t M ≃ₗ[R] completion t (completion t M) :=
  LinearEquiv.ofBijective (canonical t) (canonical_bijective_on_completion t M)

@[simp] theorem canonicalDoubleEquiv_apply (x : completion t M) :
    canonicalDoubleEquiv t M x=canonical t x := rfl

section Functor
variable {N : Type*} [AddCommGroup N] [Module R N]

theorem adicEquiv_map (f : M →ₗ[R] N) (x : completion t M) :
    adicEquiv t N (completionMap t M f x)=
      AdicCompletion.map (principal t) f (adicEquiv t M x) := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨a,ha⟩ := (powerSub t M n).mkQ_surjective (x.val n)
  change levelEquiv t N n (levelMap t M f n (x.val n))=
    f.reduceModIdeal ((principal t)^n) (levelEquiv t M n (x.val n))
  rw [← ha,levelMap_mk,levelEquiv_mk,levelEquiv_mk]
  rfl

theorem completed_map_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (completionMap t M f) := by
  intro y
  obtain ⟨x,hx⟩ := AdicCompletion.map_surjective (principal t) hf (adicEquiv t N y)
  refine ⟨(adicEquiv t M).symm x,?_⟩
  apply (adicEquiv t N).injective
  rw [adicEquiv_map,LinearEquiv.apply_symm_apply,hx]

end Functor
end MathGauge.AdicBridge

