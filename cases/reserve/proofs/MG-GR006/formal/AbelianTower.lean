import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic

noncomputable section
namespace MathGauge.AbelianTower
universe u
variable {A B C : ℕ → Type u}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)]

/-- The actual product-difference homomorphism; its kernel is the inverse limit. -/
def delta (a : ∀ n, A (n+1) →+ A n) : (∀ n, A n) →+ (∀ n, A n) where
  toFun x n := x n - a n (x (n+1))
  map_zero' := by ext n; simp
  map_add' := by intro x y; ext n; simp; abel

def limit (a : ∀ n, A (n+1) →+ A n) := (delta a).ker

@[simp] theorem mem_limit (a : ∀ n, A (n+1) →+ A n) (x : ∀ n, A n) :
    x ∈ limit a ↔ ∀ n, a n (x (n+1)) = x n := by
  change (fun n => x n-a n (x (n+1))) = 0 ↔ _
  constructor
  · intro h n; exact (sub_eq_zero.mp (congrFun h n)).symm
  · intro h; funext n; exact sub_eq_zero.mpr (h n).symm

variable (a : ∀ n, A (n+1) →+ A n) (b : ∀ n, B (n+1) →+ B n)
variable (i : ∀ n, A n →+ B n)

/-- Products of the supplied row maps. -/
def productMap : (∀ n, A n) →+ (∀ n, B n) where
  toFun x n := i n (x n)
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

theorem delta_natural (h : ∀ n, (b n).comp (i (n+1)) = (i n).comp (a n))
    (x : ∀ n, A n) : delta b (productMap i x) = productMap i (delta a x) := by
  funext n
  change i n (x n) - b n (i (n+1) (x (n+1))) = i n (x n-a n (x (n+1)))
  rw [map_sub]
  rw [show b n (i (n+1) (x (n+1))) = i n (a n (x (n+1))) from
    congrArg (fun f : A (n+1) →+ B n => f (x (n+1))) (h n)]

def limitMap (h : ∀ n, (b n).comp (i (n+1)) = (i n).comp (a n)) : limit a →+ limit b where
  toFun x := ⟨productMap i x.val, by
    change delta b (productMap i x.val)=0
    rw [delta_natural a b i h, x.property, map_zero]⟩
  map_zero' := by ext n; exact (i n).map_zero
  map_add' := by intros; ext n; exact (i n).map_add _ _

theorem limitMap_injective (h : ∀ n, (b n).comp (i (n+1)) = (i n).comp (a n))
    (hi : ∀ n, Function.Injective (i n)) : Function.Injective (limitMap a b i h) := by
  intro x y he
  apply Subtype.ext
  funext n
  apply hi n
  exact congrArg (fun z : limit b => z.val n) he

/-- Surjective adjacent maps imply that the actual product-difference map is surjective. -/
theorem delta_surjective (hb : ∀ n, Function.Surjective (b n)) : Function.Surjective (delta b) := by
  intro u
  let nxt : ∀ n, B n → B (n+1) := fun n x => (hb n (x-u n)).choose
  let x : ∀ n, B n := fun n => Nat.rec 0 (fun n x => nxt n x) n
  refine ⟨x, ?_⟩
  funext n
  change x n-b n (nxt n (x n))=u n
  rw [(hb n (x n-u n)).choose_spec]
  abel

variable (c : ∀ n, C (n+1) →+ C n) (p : ∀ n, B n →+ C n)
variable (hip : ∀ n, (i n).range = (p n).ker)
variable (hpi : ∀ n, Function.Injective (i n))
variable (hb : ∀ n, (b n).comp (i (n+1)) = (i n).comp (a n))
variable (hp : ∀ n, (c n).comp (p (n+1)) = (p n).comp (b n))
include hip

theorem pi_i (n : ℕ) (x : A n) : p n (i n x) = 0 := by
  have h : i n x ∈ (p n).ker := by rw [← hip n]; exact ⟨x,rfl⟩
  exact h

theorem row_kernel (n : ℕ) {x : B n} (hx : p n x = 0) : ∃ y, i n y=x := by
  have h : x ∈ (i n).range := by rw [hip n]; exact hx
  exact h

include hb hp hpi
/-- Exactness at the middle of the actual inverse-limit sequence. -/
theorem limit_kernel (x : limit b)
    (hx : limitMap b c p hp x = 0) : ∃ y : limit a, limitMap a b i hb y=x := by
  have hrow : ∀ n, p n (x.val n)=0 := fun n =>
    congrArg (fun z : limit c => z.val n) hx
  choose y hy using fun n => row_kernel i p hip n (hrow n)
  have he : ∀ n, a n (y (n+1))=y n := by
    intro n
    apply hpi n
    calc
      i n (a n (y (n+1))) = b n (i (n+1) (y (n+1))) :=
        (congrArg (fun f : A (n+1) →+ B n => f (y (n+1))) (hb n)).symm
      _ = b n (x.val (n+1)) := congrArg (b n) (hy (n+1))
      _ = x.val n := (mem_limit b x.val).1 x.property n
      _ = i n (y n) := (hy n).symm
  refine ⟨⟨y,(mem_limit a y).2 he⟩, ?_⟩
  apply Subtype.ext
  exact funext hy

/-- The unique coordinate defect in the kernel for an actual row lift. -/
theorem defect_exists (r : limit c) (x : ∀ n, B n) (hx : ∀ n, p n (x n)=r.val n) :
    ∃ d : ∀ n, A n, ∀ n, i n (d n)=delta b x n := by
  have hd : ∀ n, ∃ y : A n, i n y=delta b x n := by
    intro n
    apply row_kernel i p hip n
    change p n (x n-b n (x (n+1)))=0
    rw [map_sub, hx n]
    have he := congrArg (fun f : B (n+1) →+ C n => f (x (n+1))) (hp n)
    change c n (p (n+1) (x (n+1)))=p n (b n (x (n+1))) at he
    rw [← he, hx (n+1), (mem_limit c r.val).1 r.property n, sub_self]
  choose d hd using hd
  exact ⟨d,hd⟩

/-- A chosen defect is a coboundary exactly when the record has a coherent lift. -/
theorem lift_iff_coboundary (r : limit c) (x : ∀ n, B n) (hx : ∀ n, p n (x n)=r.val n)
    (d : ∀ n, A n) (hd : ∀ n, i n (d n)=delta b x n) :
    (∃ y : limit b, limitMap b c p hp y=r) ↔ ∃ z, delta a z=d := by
  constructor
  · rintro ⟨y,hy⟩
    have he : ∀ n, p n (x n-y.val n)=0 := by
      intro n
      rw [map_sub,hx n]
      have hh := congrArg (fun t : limit c => t.val n) hy
      change p n (y.val n)=r.val n at hh
      rw [hh,sub_self]
    choose z hz using fun n => row_kernel i p hip n (he n)
    refine ⟨z,funext fun n => hpi n ?_⟩
    have hmap : productMap i z=x-y.val := funext hz
    have hn := congrArg (fun t => t n) (delta_natural a b i hb z)
    change delta b (productMap i z) n=i n (delta a z n) at hn
    rw [hmap,map_sub,y.property,sub_zero] at hn
    exact hn.symm.trans (hd n).symm
  · rintro ⟨z,hz⟩
    let y := x-productMap i z
    have hy : y ∈ limit b := by
      change delta b (x-productMap i z)=0
      rw [map_sub,delta_natural a b i hb,hz]
      exact sub_eq_zero.mpr (funext hd).symm
    refine ⟨⟨y,hy⟩, ?_⟩
    apply Subtype.ext
    funext n
    change p n (x n-i n (z n))=r.val n
    rw [map_sub,pi_i i p hip,hx n,sub_zero]

/-- Changing row lifts changes their defect by the actual product coboundary. -/
theorem defect_change (x : ∀ n, B n) (d : ∀ n, A n)
    (hd : productMap i d=delta b x) (z : ∀ n, A n) (d' : ∀ n, A n)
    (hd' : productMap i d'=delta b (x+productMap i z)) : d'=d+delta a z := by
  funext n
  apply hpi n
  have he : productMap i d'=productMap i (d+delta a z) := by
    rw [hd',map_add,delta_natural a b i hb,map_add,hd]
  exact congrArg (fun t => t n) he

end MathGauge.AbelianTower
