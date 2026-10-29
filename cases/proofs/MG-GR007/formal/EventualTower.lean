import Mathlib.Tactic

noncomputable section
namespace MathGauge.GR007.EventualTower
universe u
variable {X : ℕ → Type u} (f : ∀ n, X (n+1) → X n)

def down (n m : ℕ) (h : n ≤ m) : X m → X n :=
  Nat.leRecOn h (fun {j} p => p ∘ f j) id

@[simp] theorem down_self (n : ℕ) : down f n n le_rfl=id := Nat.leRecOn_self _
@[simp] theorem down_succ (n m : ℕ) (h : n ≤ m) :
    down f n (m+1) (Nat.le_succ_of_le h)=down f n m h ∘ f m := by
  simp [down,Nat.leRecOn_succ h]
@[simp] theorem down_adjacent (n : ℕ) : down f n (n+1) (Nat.le_succ n)=f n := by simp

theorem down_comp (n m l : ℕ) (h : n ≤ m) (h' : m ≤ l) :
    down f n l (h.trans h')=down f n m h ∘ down f m l h' := by
  induction l,h' using Nat.le_induction with
  | base => simp
  | succ l hl ih => rw [down_succ f n l (h.trans hl),down_succ f m l hl,ih]; rfl

def Coherent := {x : ∀ n, X n // ∀ n, f n (x (n+1))=x n}

theorem coherent_down (x : Coherent f) (n m : ℕ) (h : n ≤ m) :
    down f n m h (x.val m)=x.val n := by
  induction m,h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [down_succ f n m hm,Function.comp_apply,x.property]
    exact ih

/-- Every finite prefix is obtained by descending a choice at its last stage.
No transition is assumed surjective. -/
theorem finite_prefix (N : ℕ) (z : X N) :
    ∃ x : (n : Fin (N+1)) → X n,
      (∀ n : Fin N, f n (x ⟨n+1,by omega⟩)=x ⟨n,by omega⟩) ∧
      x ⟨N,by omega⟩=z := by
  refine ⟨fun n => down f n N (by omega) z,?_,by simp⟩
  intro n
  have hh := congrFun (down_comp f n (n+1) N (Nat.le_succ _) (by omega)) z
  simpa only [down_adjacent,Function.comp_apply] using hh.symm

variable (N : ℕ) (hb : ∀ n, N ≤ n → Function.Bijective (f n))

def extend (z : X N) : ∀ n, X n :=
  fun n => Nat.rec (down f 0 N (Nat.zero_le _) z)
    (fun j x => if h : j+1 ≤ N then down f (j+1) N h z
      else ((hb j (by omega)).surjective x).choose) n

theorem extend_le (z : X N) (n : ℕ) (hn : n ≤ N) :
    extend f N hb z n=down f n N hn z := by
  cases n with
  | zero => rfl
  | succ n =>
    change (if h : n+1 ≤ N then down f (n+1) N h z else _) = _
    rw [dif_pos hn]

theorem extend_coherent (z : X N) (n : ℕ) :
    f n (extend f N hb z (n+1))=extend f N hb z n := by
  by_cases hn : n+1 ≤ N
  · rw [extend_le f N hb z (n+1) hn,extend_le f N hb z n (by omega)]
    have hh := congrFun (down_comp f n (n+1) N (Nat.le_succ _) hn) z
    simpa only [down_adjacent,Function.comp_apply] using hh.symm
  · change f n (if h : n+1 ≤ N then down f (n+1) N h z
      else ((hb n (by omega)).surjective (extend f N hb z n)).choose)=extend f N hb z n
    rw [dif_neg hn]
    exact ((hb n (by omega)).surjective (extend f N hb z n)).choose_spec

@[simp] theorem extend_at (z : X N) : extend f N hb z N=z := by
  rw [extend_le f N hb z N le_rfl]; simp

include hb in
theorem eval_injective : Function.Injective (fun x : Coherent f => x.val N) := by
  intro x y h
  change x.val N=y.val N at h
  apply Subtype.ext; funext n
  by_cases hn : n ≤ N
  · rw [← coherent_down f x n N hn,← coherent_down f y n N hn,h]
  · have hn' : N ≤ n := by omega
    clear hn
    induction n,hn' using Nat.le_induction with
    | base => exact h
    | succ n hN ih =>
      apply (hb n hN).injective
      rw [x.property,y.property]
      exact ih

/-- Actual evaluation of compatible sequences, not an assumed stable-tail equivalence. -/
def evaluationEquiv : Coherent f ≃ X N where
  toFun x := x.val N
  invFun z := ⟨extend f N hb z,extend_coherent f N hb z⟩
  left_inv x := eval_injective f N hb (extend_at f N hb (x.val N))
  right_inv := extend_at f N hb

end MathGauge.GR007.EventualTower
