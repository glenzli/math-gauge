import Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal Classical
noncomputable section

variable {X I : Type} {b : X} {n : ℕ}

def run : {n : ℕ} → (Fin n → Operator X b) → Operator X b
  | 0, _ => ident b
  | n+1, f => comp (f (Fin.last n)) (run (Fin.init f))

theorem run_eq_chain (f : Fin n → Operator X b) :
    run f = OperatorChain (List.ofFn f).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last, List.reverse_append]
    change comp _ (run (Fin.init f)) = comp _ (OperatorChain _)
    rw [ih]
    rfl

def stage (f : Fin n → Operator X b) (U : Set X) (t : Fin (n+1)) : Set X :=
  (run (fun r : Fin t.val => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.le_of_lt_succ t.isLt)⟩)).func '' U

@[simp] theorem stage_zero (f : Fin n → Operator X b) (U : Set X) : stage f U 0 = U := by
  change id '' U = U
  simp

theorem stage_succ (f : Fin n → Operator X b) (U : Set X) (t : Fin n) :
    stage f U t.succ = (f t).func '' stage f U t.castSucc := by
  unfold stage
  rw [Set.image_image]
  rfl

theorem stage_last (f : Fin n → Operator X b) (U : Set X) :
    stage f U (Fin.last n) = (run f).func '' U := rfl

theorem stages_unique {f : Fin n → Operator X b} {U : Set X} {V : Fin (n+1) → Set X}
    (h0 : V 0 = U) (hs : ∀ m, V m.succ = (f m).func '' V m.castSucc) :
    ∀ t, V t = stage f U t := by
  intro t
  induction t using Fin.induction with
  | zero => simpa using h0
  | succ m ih => rw [hs, ih, stage_succ]

theorem final_image {f : Fin n → Operator X b} {U : Set X} {V : Fin (n+1) → Set X}
    (h0 : V 0 = U) (hs : ∀ m, V m.succ = (f m).func '' V m.castSucc) :
    V (Fin.last n) = (run f).func '' U :=
  (stages_unique h0 hs _).trans (stage_last f U)

theorem stage_domain (f : Fin n → Operator X b) {U : Set X} (h : U ⊆ dom (run f))
    (m : Fin n) : stage f U m.castSucc ⊆ dom (f m) := by
  induction n with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) m
    · exact (comp_domain.mp h).2
    · exact ih (Fin.init f) (comp_domain.mp h).1 k

variable [Fintype I]

def product : {n : ℕ} → (Fin n → Coeff I) → Coeff I
  | 0, _ => unitM I
  | n+1, A => mul (A (Fin.last n)) (product (Fin.init A))

theorem product_empty (A : Fin 0 → Coeff I) : product A = unitM I := rfl
theorem product_step (A : Fin (n+1) → Coeff I) :
    product A = mul (A (Fin.last n)) (product (Fin.init A)) := rfl
@[simp] theorem product_one (A : Fin 1 → Coeff I) : product A = A 0 := mul_unit _

theorem display_product (A : Fin n → Coeff I) :
    display (product A) = (List.ofFn (fun t => display (A t))).reverse.prod := by
  induction n with
  | zero => exact display_unit
  | succ n ih =>
    rw [List.ofFn_succ_last, List.reverse_append, product_step, display_mul, ih]
    rfl

def OnStages (C : Operator X b → Set X → Set (Coeff I)) (f : Fin n → Operator X b)
    (U : Set X) (A : Fin n → Coeff I) := ∀ m, A m ∈ C (f m) (stage f U m.castSucc)

omit [Fintype I] in
theorem onStages_iff {C : Operator X b → Set X → Set (Coeff I)} {f : Fin n → Operator X b}
    {U : Set X} {V : Fin (n+1) → Set X} {A : Fin n → Coeff I}
    (h0 : V 0 = U) (hs : ∀ m, V m.succ = (f m).func '' V m.castSucc) :
    OnStages C f U A ↔ ∀ m, A m ∈ C (f m) (V m.castSucc) := by
  simp only [OnStages, stages_unique h0 hs]

variable [Nonempty I] {G : Gauge X I b} {U : Set X}

theorem id_lip (h : U ⊆ dom (ident b)) : unitM I ∈ lip G (ident b) U := by
  exact ⟨h, fun {x y} _ _ => by simp [ident]⟩

theorem id_coLip (hne : U.Nonempty) (h : U ⊆ dom (ident b)) : unitM I ∈ coLip G (ident b) U := by
  exact ⟨hne, h, fun {x y} _ _ => by simp [ident]⟩

theorem chain_lip (f : Fin n → Operator X b) (A : Fin n → Coeff I) (h : U ⊆ dom (run f))
    (hs : OnStages (lip G) f U A) : product A ∈ lip G (run f) U := by
  induction n with
  | zero => exact id_lip h
  | succ n ih =>
    exact lip_comp h (ih (Fin.init f) (Fin.init A) (comp_domain.mp h).1
      (fun m => hs m.castSucc)) (hs (Fin.last n))

private theorem chain_lower_aux (hne : U.Nonempty) (f : Fin n → Operator X b)
    (A : Fin n → Coeff I) (h : U ⊆ dom (run f)) (hs : OnStages (coLip G) f U A) :
    product A ∈ coLip G (run f) U := by
  induction n with
  | zero => exact id_coLip hne h
  | succ n ih =>
    exact co_comp h (ih (Fin.init f) (Fin.init A) (comp_domain.mp h).1
      (fun m => hs m.castSucc)) (hs (Fin.last n))

theorem chain_coLip (f : Fin (n+1) → Operator X b) (A : Fin (n+1) → Coeff I)
    (h : U ⊆ dom (run f)) (hs : OnStages (coLip G) f U A) :
    product A ∈ coLip G (run f) U := by
  apply chain_lower_aux _ f A h hs
  simpa using (hs 0).1

abbrev Path (I : Type) (n : ℕ) := Fin n → I

def edge (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) (t : Fin (n+1)) :=
  A t (Fin.cons (α := fun _ => I) i p t) (Fin.snoc (α := fun _ => I) p j t)

def weight (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) :=
  ∏ t, edge A i j p t

def HasZero (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) :=
  ∃ t, edge A i j p t = 0

def AllPositive (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) :=
  ∀ t, 0 < edge A i j p t

omit [Fintype I] [Nonempty I] in
theorem one_path (A : Fin 1 → Coeff I) (i j : I) :
    (∃! _ : Path I 0, True) ∧ ∀ p : Path I 0,
      weight A i j p = A 0 i j ∧ (HasZero A i j p ↔ A 0 i j = 0) ∧
      (AllPositive A i j p ↔ 0 < A 0 i j) := by
  refine ⟨⟨Fin.elim0, trivial, fun _ _ => Subsingleton.elim _ _⟩, fun p => ?_⟩
  have hj : Fin.snoc (α := fun _ => I) p j (0 : Fin 1) = j := Fin.snoc_last _ _
  simp [weight, edge, HasZero, AllPositive, hj]

omit [Fintype I] [Nonempty I] in
private theorem weight_snoc (A : Fin (n+2) → Coeff I) (i j k : I) (p : Path I n) :
    weight A i j (Fin.snoc p k) = A (Fin.last (n+1)) k j * weight (Fin.init A) i k p := by
  unfold weight
  rw [Fin.prod_univ_castSucc, mul_comm]
  simp only [edge, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last, Fin.init]

omit [Nonempty I] in
theorem sum_paths (A : Fin (n+1) → Coeff I) (i j : I) :
    product A i j = ∑ p : Path I n, weight A i j p := by
  induction n generalizing i j with
  | zero =>
    simp [fun p => ((one_path A i j).2 p).1]
  | succ n ih =>
    let e := Fin.snocEquiv (fun _ : Fin (n+1) => I)
    rw [← e.sum_comp (weight A i j), Fintype.sum_prod_type]
    change (∑ k, A (Fin.last _) k j * product (Fin.init A) i k) =
      ∑ k, ∑ p, weight A i j (Fin.snoc p k)
    simp_rw [weight_snoc, ← Finset.mul_sum, ← ih]

theorem path_criteria (f : Fin (n+1) → Operator X b) (L K : Fin (n+1) → Coeff I)
    (_h : U ⊆ dom (run f)) (_hL : OnStages (lip G) f U L) (_hK : OnStages (coLip G) f U K)
    (i j : I) :
    (product L i j = 0 ↔ ∀ p, HasZero L i j p) ∧
    (0 < product K i j ↔ ∃ p, AllPositive K i j p) := by
  classical
  simp [sum_paths, HasZero, AllPositive, weight, pos_iff_ne_zero,
    Finset.sum_eq_zero_iff, Finset.prod_eq_zero_iff, not_forall]

end
end HCH02
