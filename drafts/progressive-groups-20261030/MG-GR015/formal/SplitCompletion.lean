import CompletionStructure

noncomputable section
namespace MathGauge.SplitCompletion
open MathGauge.CompletionFailure MathGauge.CompletionStructure
universe u v w z
variable {R : Type u} [CommRing R] (t : R)
variable {A : Type v} {B : Type w} {C : Type z}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

def kernelEquiv (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) : A ≃ₗ[R] q.ker :=
  LinearEquiv.ofBijective (i.codRestrict q.ker (fun a => (he (i a)).2 ⟨a,rfl⟩))
    ⟨fun _ _ h => hi (congrArg Subtype.val h),fun b => by
      obtain ⟨a,ha⟩ := (he b.val).1 b.property
      exact ⟨a,Subtype.ext ha⟩⟩

def retraction (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) : B →ₗ[R] A :=
  (kernelEquiv i q hi he).symm.toLinearMap.comp
    ((LinearMap.id-s.comp q).codRestrict q.ker (fun b => by
      change q (b-s (q b))=0
      rw [map_sub,show q (s (q b))=q b from LinearMap.congr_fun hs (q b),sub_self]))

theorem retraction_equation (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) (b : B) :
    i (retraction i q hi he s hs b)=b-s (q b) := by
  exact congrArg Subtype.val ((kernelEquiv i q hi he).apply_symm_apply
    (⟨b-s (q b),by
      rw [LinearMap.mem_ker,map_sub,show q (s (q b))=q b from LinearMap.congr_fun hs (q b),sub_self]⟩ : q.ker))

theorem split_identities (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) :
    (retraction i q hi he s hs).comp i=LinearMap.id ∧
    (retraction i q hi he s hs).comp s=0 ∧
    i.comp (retraction i q hi he s hs)+s.comp q=LinearMap.id ∧ q.comp i=0 := by
  have hz (a : A) : q (i a)=0 := (he (i a)).2 ⟨a,rfl⟩
  refine ⟨?_,?_,?_,?_⟩
  · ext a
    apply hi
    rw [LinearMap.comp_apply,retraction_equation,hz,map_zero,sub_zero]
    rfl
  · ext c
    apply hi
    rw [LinearMap.comp_apply,retraction_equation,show q (s c)=c from LinearMap.congr_fun hs c]
    simp
  · ext b
    change i (retraction i q hi he s hs b)+s (q b)=b
    rw [retraction_equation,sub_add_cancel]
  · ext a
    exact hz a

theorem completed_split_identities (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) :
    (completionMap t B (retraction i q hi he s hs)).comp (completionMap t A i)=LinearMap.id ∧
    (completionMap t B (retraction i q hi he s hs)).comp (completionMap t C s)=0 ∧
    (completionMap t A i).comp (completionMap t B (retraction i q hi he s hs))+
      (completionMap t C s).comp (completionMap t B q)=LinearMap.id ∧
    (completionMap t B q).comp (completionMap t A i)=0 ∧
    (completionMap t B q).comp (completionMap t C s)=LinearMap.id := by
  obtain ⟨hpi,hps,hb,hqi⟩ := split_identities i q hi he s hs
  simp only [← completionMap_comp,← completionMap_add,hpi,hps,hb,hqi,hs,completionMap_id,completionMap_zero,
    and_self]

def completedSplit (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) :
    (completion t A × completion t C) ≃ₗ[R] completion t B := by
  let I := completionMap t A i
  let Q := completionMap t B q
  let S := completionMap t C s
  let P := completionMap t B (retraction i q hi he s hs)
  obtain ⟨hpi,hps,hb,hqi,hqs⟩ := completed_split_identities t i q hi he s hs
  change P.comp I=LinearMap.id at hpi
  change P.comp S=0 at hps
  change I.comp P+S.comp Q=LinearMap.id at hb
  change Q.comp I=0 at hqi
  change Q.comp S=LinearMap.id at hqs
  exact
    { toFun := fun x => I x.1+S x.2
      invFun := fun b => (P b,Q b)
      left_inv := fun x => by
        apply Prod.ext
        · change P (I x.1+S x.2)=x.1
          rw [map_add,show P (I x.1)=x.1 from LinearMap.congr_fun hpi x.1,
            show P (S x.2)=0 from LinearMap.congr_fun hps x.2,add_zero]
        · change Q (I x.1+S x.2)=x.2
          rw [map_add,show Q (I x.1)=0 from LinearMap.congr_fun hqi x.1,
            show Q (S x.2)=x.2 from LinearMap.congr_fun hqs x.2,zero_add]
      right_inv := fun b => LinearMap.congr_fun hb b
      map_add' := fun x y => by simp only [Prod.fst_add,Prod.snd_add,map_add];abel
      map_smul' := fun r x => by simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_add,RingHom.id_apply] }

theorem completed_short_exact (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) :
    Function.Injective (completionMap t A i) ∧ Function.Surjective (completionMap t B q) ∧
      Function.Exact (completionMap t A i) (completionMap t B q) := by
  obtain ⟨hpi,hps,hb,hqi,hqs⟩ := completed_split_identities t i q hi he s hs
  refine ⟨?_,?_,?_⟩
  · intro a b hab
    have h := congrArg (completionMap t B (retraction i q hi he s hs)) hab
    simpa only [← LinearMap.comp_apply,hpi,LinearMap.id_apply] using h
  · intro c
    exact ⟨completionMap t C s c,LinearMap.congr_fun hqs c⟩
  · intro b
    constructor
    · intro hq
      refine ⟨completionMap t B (retraction i q hi he s hs) b,?_⟩
      have h := LinearMap.congr_fun hb b
      simpa only [LinearMap.add_apply,LinearMap.comp_apply,hq,map_zero,add_zero,LinearMap.id_apply] using h
    · rintro ⟨a,rfl⟩
      exact LinearMap.congr_fun hqi a

theorem all_completed_lifts (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) (c : completion t C) (b : completion t B) :
    completionMap t B q b=c ↔ ∃! a : completion t A,
      b=completionMap t C s c+completionMap t A i a := by
  obtain ⟨hI,hQ,hE⟩ := completed_short_exact t i q hi he s hs
  have hqs : (completionMap t B q).comp (completionMap t C s)=LinearMap.id := by
    rw [← completionMap_comp,hs,completionMap_id]
  constructor
  · intro hb
    have hz : completionMap t B q (b-completionMap t C s c)=0 := by
      rw [map_sub,hb,show completionMap t B q (completionMap t C s c)=c from LinearMap.congr_fun hqs c,sub_self]
    obtain ⟨a,ha⟩ := (hE _).mp hz
    refine ⟨a,by dsimp only;rw [ha];abel,?_⟩
    intro a' ha'
    apply hI
    rw [ha]
    rw [ha']
    abel
  · rintro ⟨a,ha,_⟩
    rw [ha,map_add,show completionMap t B q (completionMap t C s c)=c from LinearMap.congr_fun hqs c,
      (hE _).mpr ⟨a,rfl⟩,add_zero]

theorem changed_section (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q)
    (s s' : C →ₗ[R] B) (hs : q.comp s=LinearMap.id) (hs' : q.comp s'=LinearMap.id) :
    ∃ h : C →ₗ[R] A,s'=s+i.comp h ∧
      ∀ c : completion t C,completionMap t C s' c=completionMap t C s c+
        completionMap t A i (completionMap t C h c) := by
  let h := (retraction i q hi he s hs).comp (s'-s)
  have heq : s'=s+i.comp h := by
    ext c
    change s' c=s c+i (retraction i q hi he s hs (s' c-s c))
    rw [retraction_equation,map_sub,show q (s' c)=c from LinearMap.congr_fun hs' c,
      show q (s c)=c from LinearMap.congr_fun hs c,sub_self,map_zero,sub_zero]
    abel
  refine ⟨h,heq,?_⟩
  intro c
  rw [heq,completionMap_add,completionMap_comp]
  rfl

end MathGauge.SplitCompletion
