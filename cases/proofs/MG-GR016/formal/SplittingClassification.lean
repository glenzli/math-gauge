import LocalSplitting
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Ideal.IdempotentFG

noncomputable section
namespace MathGauge.SplittingClassification
universe u v w t
variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {C : Type t}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

abbrev Sections (q : B →ₗ[R] C) := {s : C →ₗ[R] B // q.comp s=LinearMap.id}

def kernelEquiv (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) : A ≃ₗ[R] q.ker :=
  LinearEquiv.ofBijective (i.codRestrict q.ker (fun a => (he (i a)).2 ⟨a,rfl⟩))
    ⟨fun _ _ h => hi (congrArg Subtype.val h),fun b => by
      obtain ⟨a,ha⟩ := (he b.val).1 b.property
      exact ⟨a,Subtype.ext ha⟩⟩

def kernelSplit (q : B →ₗ[R] C) (s : Sections q) : (q.ker × C) ≃ₗ[R] B where
  toFun x := x.1.val+s.val x.2
  invFun b := (⟨b-s.val (q b),by
    change q (b-s.val (q b))=0
    rw [map_sub,show q (s.val (q b))=q b from LinearMap.congr_fun s.property (q b),sub_self]⟩,q b)
  left_inv x := by
    have hx : q x.1.val=0 := x.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add,hx,zero_add]
      rw [show q (s.val x.2)=x.2 from LinearMap.congr_fun s.property x.2]
      abel
    · simp only [map_add,hx,zero_add]
      exact LinearMap.congr_fun s.property x.2
  right_inv b := sub_add_cancel _ _
  map_add' x y := by simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add,map_add]; abel
  map_smul' r x := by simp only [Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul,map_smul,smul_add,RingHom.id_apply]

def split (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s : Sections q) : (A × C) ≃ₗ[R] B :=
  ((kernelEquiv i q hi he).prodCongr (LinearEquiv.refl R C)).trans (kernelSplit q s)

@[simp] theorem split_apply (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s : Sections q) (a : A) (c : C) :
    split i q hi he s (a,c)=i a+s.val c := rfl

def sectionWith (i : A →ₗ[R] B) (q : B →ₗ[R] C) (he : Function.Exact i q)
    (s₀ : Sections q) (h : C →ₗ[R] A) : Sections q :=
  ⟨s₀.val+i.comp h,by
    ext c
    change q (s₀.val c+i (h c))=c
    rw [map_add,show q (s₀.val c)=c from LinearMap.congr_fun s₀.property c,
      (he (i (h c))).2 ⟨h c,rfl⟩,add_zero]⟩

def sectionParameter (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s₀ s : Sections q) : C →ₗ[R] A :=
  (kernelEquiv i q hi he).symm.toLinearMap.comp
    ((s.val-s₀.val).codRestrict q.ker (fun c => by
      change q (s.val c-s₀.val c)=0
      rw [map_sub,show q (s.val c)=c from LinearMap.congr_fun s.property c,
        show q (s₀.val c)=c from LinearMap.congr_fun s₀.property c,sub_self]))

theorem parameter_equation (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s₀ s : Sections q) (c : C) :
    i (sectionParameter i q hi he s₀ s c)=s.val c-s₀.val c := by
  exact congrArg Subtype.val ((kernelEquiv i q hi he).apply_symm_apply
    (⟨s.val c-s₀.val c,by
      rw [LinearMap.mem_ker,map_sub,show q (s.val c)=c from LinearMap.congr_fun s.property c,
        show q (s₀.val c)=c from LinearMap.congr_fun s₀.property c,sub_self]⟩ : q.ker))

def sectionEquiv (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s₀ : Sections q) :
    (C →ₗ[R] A) ≃ Sections q where
  toFun := sectionWith i q he s₀
  invFun := sectionParameter i q hi he s₀
  left_inv h := by
    ext c
    apply hi
    rw [parameter_equation]
    change s₀.val c+i (h c)-s₀.val c=i (h c)
    abel
  right_inv s := by
    apply Subtype.ext
    ext c
    change s₀.val c+i (sectionParameter i q hi he s₀ s c)=s.val c
    rw [parameter_equation]
    abel

abbrev CompatibleEquivs (i : A →ₗ[R] B) (q : B →ₗ[R] C) :=
  {e : (A × C) ≃ₗ[R] B // (∀ a,e (a,0)=i a) ∧ ∀ a c,q (e (a,c))=c}

def sectionToCompatible (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s : Sections q) : CompatibleEquivs i q :=
  ⟨split i q hi he s,⟨by intro a; simp,by
    intro a c
    rw [split_apply,map_add,(he (i a)).2 ⟨a,rfl⟩,zero_add]
    exact LinearMap.congr_fun s.property c⟩⟩

def compatibleToSection (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (e : CompatibleEquivs i q) : Sections q :=
  ⟨e.val.toLinearMap.comp (LinearMap.inr R A C),by ext c;exact e.property.2 0 c⟩

def compatibleEquiv (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) : Sections q ≃ CompatibleEquivs i q where
  toFun := sectionToCompatible i q hi he
  invFun := compatibleToSection i q
  left_inv s := by
    apply Subtype.ext
    ext c
    change i 0+s.val c=s.val c
    simp
  right_inv e := by
    apply Subtype.ext
    apply LinearEquiv.ext
    rintro ⟨a,c⟩
    change i a+e.val (0,c)=e.val (a,c)
    rw [← e.property.1 a,← map_add]
    simp

theorem change_origin (i : A →ₗ[R] B) (q : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i q) (s₀ s₁ s : Sections q) :
    sectionParameter i q hi he s₁ s=
      sectionParameter i q hi he s₀ s-sectionParameter i q hi he s₀ s₁ := by
  ext c
  apply hi
  simp only [LinearMap.sub_apply,map_sub,parameter_equation]
  abel

end MathGauge.SplittingClassification
