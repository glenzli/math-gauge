import ObstructionNaturality
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathGauge.GR006
open MathGauge.AbelianTower
universe u
variable {A B C : ℕ → Type u}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)]

def down (b : ∀ n, B (n+1) →+ B n) (n m : ℕ) (h : n ≤ m) : B m →+ B n :=
  Nat.leRecOn h (fun {j} p => p.comp (b j)) (AddMonoidHom.id _)

@[simp] theorem down_self (b : ∀ n, B (n+1) →+ B n) (n : ℕ) :
    down b n n le_rfl=AddMonoidHom.id _ := Nat.leRecOn_self _

@[simp] theorem down_succ (b : ∀ n, B (n+1) →+ B n) (n m : ℕ) (h : n ≤ m) :
    down b n (m+1) (Nat.le_succ_of_le h)=(down b n m h).comp (b m) := by
  simp [down,Nat.leRecOn_succ h]

theorem down_comp (b : ∀ n, B (n+1) →+ B n) (n m l : ℕ) (h : n ≤ m) (h' : m ≤ l) :
    down b n l (h.trans h')=(down b n m h).comp (down b m l h') := by
  induction l,h' using Nat.le_induction with
  | base => simp
  | succ l hl ih => rw [down_succ b n l (h.trans hl),down_succ b m l hl,ih]; rfl

theorem down_adjacent (b : ∀ n, B (n+1) →+ B n) (n : ℕ) :
    down b n (n+1) (Nat.le_succ n)=b n := by simp

variable (b : ∀ n, B (n+1) →+ B n) (c : ∀ n, C (n+1) →+ C n)
variable (p : ∀ n, B n →+ C n)
variable (hp : ∀ n, (c n).comp (p (n+1))=(p n).comp (b n))

include hp in
theorem down_natural (n m : ℕ) (h : n ≤ m) :
    (p n).comp (down b n m h)=(down c n m h).comp (p m) := by
  induction m,h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [down_succ b n m hm,down_succ c n m hm]
    rw [← AddMonoidHom.comp_assoc,ih,AddMonoidHom.comp_assoc,← hp m]
    rfl

/-- Finite prefixes have no condition beyond the last adjacent arrow.
The represented indices 0..N correspond to the question's 1..N+1. -/
def Prefix (N : ℕ) (a : ∀ n, A (n+1) →+ A n) : AddSubgroup (∀ n : Fin (N+1), A n) where
  carrier := {x | ∀ n : Fin N, a n (x n.succ)=x n.castSucc}
  zero_mem' := by intro n; exact map_zero _
  add_mem' := by
    intro x y hx hy n
    change a n (x n.succ+y n.succ)=x n.castSucc+y n.castSucc
    rw [map_add,hx n,hy n]
  neg_mem' := by
    intro x hx n
    change a n (-x n.succ)= -x n.castSucc
    rw [map_neg,hx n]

theorem prefix_down (N : ℕ) (x : Prefix N c) (n m : Fin (N+1)) (h : n ≤ m) :
    down c n m h (x.val m)=x.val n := by
  have hh (m : ℕ) (hnm : (n : ℕ) ≤ m) (hm : m ≤ N) :
      down c n m hnm (x.val ⟨m,by omega⟩)=x.val n := by
    induction m,hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      rw [down_succ c n m hnm,AddMonoidHom.comp_apply]
      have he := x.property (⟨m,by omega⟩ : Fin N)
      change c m (x.val ⟨m+1,by omega⟩)=x.val ⟨m,by omega⟩ at he
      rw [he]
      exact ih (by omega)
  exact hh m h (by omega)

include hp in
theorem prefix_lift (N : ℕ) (hs : Function.Surjective (p N)) (x : Prefix N c) :
    ∃ y : Prefix N b, ∀ n : Fin (N+1), p n (y.val n)=x.val n := by
  obtain ⟨top,htop⟩ := hs (x.val ⟨N,Nat.lt_succ_self N⟩)
  let y : ∀ n : Fin (N+1), B n := fun n => down b n N (by omega) top
  have hy : y ∈ Prefix N b := by
    intro n
    change b n (down b (n+1) N (by omega) top)=down b n N (by omega) top
    rw [down_comp b n (n+1) N (Nat.le_succ _) (by omega),down_adjacent]
    rfl
  refine ⟨⟨y,hy⟩,?_⟩
  intro n
  change ((p n).comp (down b n N (by omega))) top=x.val n
  rw [down_natural b c p hp,AddMonoidHom.comp_apply,htop]
  exact prefix_down c N x n ⟨N,by omega⟩ (show n.val ≤ N from Nat.le_of_lt_succ n.isLt)

variable (a : ∀ n, A (n+1) →+ A n) (i : ∀ n, A n →+ B n)
variable (hb : ∀ n, (b n).comp (i (n+1))=(i n).comp (a n))

def prefixMap (N : ℕ) : Prefix N a →+ Prefix N b where
  toFun z := ⟨fun n => i n (z.val n),by
    intro n
    have hh := congrArg (fun f : A (n+1) →+ B n => f (z.val n.succ)) (hb n)
    change b n (i (n+1) (z.val n.succ))=i n (z.val n.castSucc)
    rw [show b n (i (n+1) (z.val n.succ))=i n (a n (z.val n.succ)) from hh,z.property n]⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ _ _

theorem prefixMap_injective (N : ℕ) (hi : ∀ n, Function.Injective (i n)) :
    Function.Injective (prefixMap b a i hb N) := by
  intro x y h
  apply Subtype.ext
  funext n
  exact hi n (congrArg (fun z : Prefix N b => z.val n) h)

/-- S1 freedom: exactly one compatible kernel prefix translates one lift
to another; no compatibility beyond N or global lifting is assumed. -/
theorem prefix_freedom (N : ℕ) (hex : ∀ n, (i n).range=(p n).ker)
    (hi : ∀ n, Function.Injective (i n)) (x y : Prefix N b)
    (hxy : ∀ n : Fin (N+1), p n (y.val n)=p n (x.val n)) :
    ∃! z : Prefix N a, y=x+prefixMap b a i hb N z := by
  have hz (n : Fin (N+1)) : ∃ z : A n, i n z=y.val n-x.val n := by
    apply row_kernel i p hex n
    rw [map_sub,hxy n,sub_self]
  choose z hz using hz
  have hcoh : z ∈ Prefix N a := by
    intro n
    apply hi n
    have hh := congrArg (fun f : A (n+1) →+ B n => f (z n.succ)) (hb n)
    change i n (a n (z n.succ))=i n (z n.castSucc)
    have hzs : i (n+1) (z n.succ)=y.val n.succ-x.val n.succ := hz n.succ
    have hzc : i n (z n.castSucc)=y.val n.castSucc-x.val n.castSucc := hz n.castSucc
    rw [← show b n (i (n+1) (z n.succ))=i n (a n (z n.succ)) from hh,
      hzs,map_sub,y.property n,x.property n,hzc]
  refine ⟨⟨z,hcoh⟩,?_,?_⟩
  · apply Subtype.ext
    funext n
    change y.val n=x.val n+i n (z n)
    rw [hz n]
    abel
  · intro z' hz'
    apply prefixMap_injective b a i hb N hi
    apply add_left_cancel (a := x)
    rw [← hz']
    apply Subtype.ext
    funext n
    change y.val n=x.val n+i n (z n)
    rw [hz n]
    abel

theorem prefix_kernel_translation_preserves_record (N : ℕ)
    (hex : ∀ n, (i n).range=(p n).ker) (x : Prefix N b) (z : Prefix N a)
    (n : Fin (N+1)) :
    p n ((x+prefixMap b a i hb N z).val n)=p n (x.val n) := by
  change p n (x.val n+i n (z.val n))=p n (x.val n)
  rw [map_add,pi_i i p hex,add_zero]

end MathGauge.GR006
