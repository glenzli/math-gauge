import FiniteFibers
import Mathlib.Data.ZMod.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace MathGauge.GR006
open MathGauge.AbelianTower

namespace Shear
def inclusion : ℤ →+ ℤ×ℤ := AddMonoidHom.inl ℤ ℤ
def projection : ℤ×ℤ →+ ℤ := AddMonoidHom.snd ℤ ℤ
def splitting : ℤ →+ ℤ×ℤ := AddMonoidHom.inr ℤ ℤ
def shear (v : ℤ) : (ℤ×ℤ) ≃+ (ℤ×ℤ) where
  toFun x := (x.1+v*x.2,x.2)
  invFun x := (x.1-v*x.2,x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem split_row : Function.Injective inclusion ∧ Function.Surjective projection ∧
    inclusion.range=projection.ker ∧ projection.comp splitting=AddMonoidHom.id ℤ := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b h; exact congrArg Prod.fst h
  · intro c; exact ⟨(0,c),rfl⟩
  · ext x
    constructor
    · rintro ⟨a,rfl⟩; rfl
    · intro h
      change x.2=0 at h
      exact ⟨x.1,Prod.ext rfl h.symm⟩
  · rfl

theorem shear_preserves_ends (v : ℤ) :
    (shear v).toAddMonoidHom.comp inclusion=inclusion ∧
    projection.comp (shear v).toAddMonoidHom=projection := by
  constructor <;> ext x <;> simp [shear,inclusion,projection]

theorem shear_commutes_constant_transition (v : ℤ) :
    (AddMonoidHom.id (ℤ×ℤ)).comp (shear v).toAddMonoidHom=
      (shear v).toAddMonoidHom.comp (AddMonoidHom.id (ℤ×ℤ)) := rfl

/-- Every possible lift of record 1 is moved by a legitimate tower
automorphism which is identity on the kernel and the record. -/
theorem no_invariant_lift (x : ℤ×ℤ) (hx : projection x=1) : shear 1 x ≠ x := by
  intro h
  have hh := congrArg Prod.fst h
  change x.1+1*x.2=x.1 at hh
  change x.2=1 at hx
  omega

theorem no_natural_constant_lift :
    ¬ ∃ x : limit (A := fun _ => ℤ×ℤ) (fun _ => AddMonoidHom.id _),
      (∀ n, projection (x.val n)=1) ∧ (∀ v n, shear v (x.val n)=x.val n) := by
  rintro ⟨x,hx,hn⟩
  exact no_invariant_lift (x.val 0) (hx 0) (hn 1 0)
end Shear

namespace Nonnecessary
abbrev C : ℕ → Type
  | 0 => ZMod 2
  | _+1 => ZMod 4
instance : (n : ℕ) → AddCommGroup (C n)
  | 0 => inferInstanceAs (AddCommGroup (ZMod 2))
  | _+1 => inferInstanceAs (AddCommGroup (ZMod 4))
instance : (n : ℕ) → Finite (C n)
  | 0 => inferInstanceAs (Finite (ZMod 2))
  | _+1 => inferInstanceAs (Finite (ZMod 4))
def p : (n : ℕ) → ℤ →+ C n
  | 0 => Int.castAddHom (ZMod 2)
  | _+1 => Int.castAddHom (ZMod 4)
def gamma : ∀ n, C (n+1) →+ C n
  | 0 => (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom
  | _+1 => AddMonoidHom.id _
def beta (_ : ℕ) : ℤ →+ ℤ := AddMonoidHom.id _

theorem quotient_commutes (n : ℕ) :
    (gamma n).comp (p (n+1))=(p n).comp (beta n) := by
  cases n
  · ext z; simp [p,gamma,beta]
  · rfl

def A (n : ℕ) : AddSubgroup ℤ := (p n).ker
def alpha (n : ℕ) : A (n+1) →+ A n where
  toFun x := ⟨x.val,by
    have hh := congrArg (fun f : ℤ →+ C n => f x.val) (quotient_commutes n)
    change gamma n (p (n+1) x.val)=p n x.val at hh
    rw [x.property,map_zero] at hh
    exact hh.symm⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem rows_exact (n : ℕ) :
    Function.Injective (A n).subtype ∧ Function.Surjective (p n) ∧
      (A n).subtype.range=(p n).ker := by
  refine ⟨Subtype.val_injective,?_,?_⟩
  · cases n <;> exact ZMod.intCast_surjective
  · exact AddSubgroup.range_subtype _

theorem kernel_diagram (n : ℕ) :
    (beta n).comp (A (n+1)).subtype=(A n).subtype.comp (alpha n) := rfl

theorem transitions_surjective (n : ℕ) :
    Function.Surjective (beta n) ∧ Function.Surjective (gamma n) := by
  refine ⟨Function.surjective_id,?_⟩
  cases n
  · intro z
    obtain ⟨a,ha⟩ := ZMod.intCast_surjective z
    refine ⟨(a : ZMod 4),?_⟩
    simpa [gamma] using ha
  · exact Function.surjective_id

theorem alpha_zero_not_surjective : ¬ Function.Surjective (alpha 0) := by
  intro h
  have ht : (2 : ℤ) ∈ A 0 := by
    change (2 : ZMod 2)=0
    decide
  obtain ⟨a,ha⟩ := h ⟨2,ht⟩
  have hav : a.val=2 := congrArg Subtype.val ha
  have hz := a.property
  change (a.val : ZMod 4)=0 at hz
  rw [hav] at hz
  change (2 : ZMod 4)=0 at hz
  exact (by decide : (2 : ZMod 4) ≠ 0) hz

theorem record_tail (r : limit gamma) (n : ℕ) : r.val (n+1)=r.val 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := (mem_limit gamma r.val).mp r.property (n+1)
    exact h.trans ih

/-- A genuine S4 tower has non-surjective first kernel map but surjective
inverse-limit augmentation. Thus S2 is sufficient, not necessary. -/
theorem augmentation_surjective : Function.Surjective (limitMap beta gamma p quotient_commutes) := by
  intro r
  obtain ⟨z,hz⟩ := (rows_exact 1).2.1 (r.val 1)
  let b : limit (A := fun _ => ℤ) beta :=
    ⟨fun _ => z,(mem_limit (A := fun _ => ℤ) beta _).mpr (fun _ => rfl)⟩
  refine ⟨b,Subtype.ext ?_⟩
  funext n
  cases n with
  | zero =>
    have hh := congrArg (gamma 0) hz
    have ht := (mem_limit gamma r.val).mp r.property 0
    exact (congrArg (fun f : ℤ →+ C 0 => f z) (quotient_commutes 0)).symm.trans (hh.trans ht)
  | succ n =>
    change p (n+1) z=r.val (n+1)
    exact hz.trans (record_tail r n).symm

theorem infinite_kernel (n : ℕ) : Infinite (A n) := by
  have hm : ∀ z : ℤ, (4*z : ℤ) ∈ A n := by
    intro z
    cases n
    · change (((4*z : ℤ) : ZMod 2))=0
      rw [Int.cast_mul]
      change (4 : ZMod 2)*(z : ZMod 2)=0
      rw [show (4 : ZMod 2)=0 by decide,zero_mul]
    · change (((4*z : ℤ) : ZMod 4))=0
      rw [Int.cast_mul]
      change (4 : ZMod 4)*(z : ZMod 4)=0
      rw [show (4 : ZMod 4)=0 by decide,zero_mul]
  let f : ℤ → A n := fun z => ⟨4*z,hm z⟩
  apply Infinite.of_injective f
  intro x y h
  have hh := congrArg Subtype.val h
  change 4*x=4*y at hh
  omega

end Nonnecessary
end MathGauge.GR006
