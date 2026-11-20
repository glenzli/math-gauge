import Bounds
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fin.Tuple.Basic

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical
noncomputable section
namespace HCH02

variable {X I : Type} {b : X} [Fintype I]
abbrev Op (X : Type) (b : X) := Operator X b

def eye : Mat I := fun i j => if i = j then 1 else 0

def product : {n : ℕ} → (Fin n → Mat I) → Mat I
  | 0, _ => eye
  | _+1, M => mul (product (Fin.tail M)) (M 0)

theorem product_one (M : Fin 1 → Mat I) : product M = M 0 := by
  funext i j
  simp [product, mul, eye, ite_mul]

theorem product_order {n} (M : Fin n → Mat I) :
    display (product M) = (List.ofFn (display ∘ M)).reverse.prod := by
  induction n with
  | zero =>
    change display eye = 1
    ext j i
    simp [display, eye, Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton,
      product, display_mul, ih]
    rfl

def chain : {n : ℕ} → (Fin n → Op X b) → Op X b
  | 0, _ => OperatorChain []
  | _+1, f => comp (chain (Fin.tail f)) (f 0)

private theorem append_one (fs : List (Op X b)) (p : Op X b) :
    OperatorChain (fs ++ [p]) = comp (OperatorChain fs) p := by
  induction fs with
  | nil => rfl
  | cons q fs ih =>
    ext x
    change q.func ((OperatorChain (fs ++ [p])).func x) = _
    rw [ih]
    rfl

theorem chain_order {n} (f : Fin n → Op X b) :
    chain f = OperatorChain (List.ofFn f).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.reverse_cons, append_one, chain, ih]
    rfl

def stage : {n : ℕ} → (Fin n → Op X b) → Set X → Fin (n+1) → Set X
  | 0, _, U, _ => U
  | _+1, f, U, t => Fin.cases U (stage (Fin.tail f) (operator_image (f 0) U)) t

theorem stage_zero {n} (f : Fin n → Op X b) (U) : stage f U 0 = U := by cases n <;> rfl

theorem stage_next {n} (f : Fin n → Op X b) (U) (m : Fin n) :
    stage f U m.succ = operator_image (f m) (stage f U m.castSucc) := by
  induction n generalizing U with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ih (Fin.tail f) (operator_image (f 0) U) k) m
    exact stage_zero (Fin.tail f) _

theorem final_image {n} (f : Fin n → Op X b) (U) :
    stage f U (Fin.last n) = operator_image (chain f) U := by
  induction n generalizing U with
  | zero => simp [stage, operator_image, chain, OperatorChain]
  | succ n ih =>
    exact (ih (Fin.tail f) (operator_image (f 0) U)).trans (Set.image_image _ _ _)

theorem step_domains {n} (f : Fin n → Op X b) (U) (h : U ⊆ dom (chain f)) :
    ∀ m, stage f U m.castSucc ⊆ dom (f m) := by
  induction n generalizing U with
  | zero => exact fun m => m.elim0
  | succ n ih =>
    obtain ⟨h₀, ht⟩ := comp_domain.mp h
    exact Fin.cases h₀ (ih (Fin.tail f) _ ht)

def Steps {n} (C : Op X b → Set X → Set (Mat I)) (f : Fin n → Op X b)
    (U : Set X) (M : Fin n → Mat I) := ∀ m, M m ∈ C (f m) (stage f U m.castSucc)

omit [Fintype I] in
theorem steps_from {n} {f : Fin n → Op X b} {U : Set X} {V : Fin (n+1) → Set X}
    {C : Op X b → Set X → Set (Mat I)} {M : Fin n → Mat I}
    (h₀ : V 0 = U) (hv : ∀ m, V m.succ = operator_image (f m) (V m.castSucc))
    (hm : ∀ m, M m ∈ C (f m) (V m.castSucc)) : Steps C f U M := by
  have he (t) : V t = stage f U t := by
    induction t using Fin.induction with
    | zero => exact h₀.trans (stage_zero f U).symm
    | succ m ih => rw [hv, stage_next, ih]
  exact fun m => he m.castSucc ▸ hm m

theorem eye_act (v : I → ENNReal) (j : I) : act eye v j = v j := by
  simp [act, eye, ite_mul]

variable [Nonempty I] {g : Gauge X I b} {U : Set X}

theorem empty_lip (h : U ⊆ dom (OperatorChain ([] : List (Op X b)))) :
    eye ∈ lip g (OperatorChain []) U :=
  ⟨h, fun _ _ _ _ j => (eye_act _ j).ge⟩

theorem empty_co (h : U ⊆ dom (OperatorChain ([] : List (Op X b)))) (hu : U.Nonempty) :
    eye ∈ coLip g (OperatorChain []) U :=
  ⟨hu, h, fun _ _ _ _ j => (eye_act _ j).le⟩

theorem chain_lip {n} {f : Fin n → Op X b} {M : Fin n → Mat I}
    (h : U ⊆ dom (chain f)) (hs : Steps (lip g) f U M) :
    product M ∈ lip g (chain f) U := by
  induction n generalizing U with
  | zero => exact empty_lip h
  | succ n ih =>
    exact lip_comp h (hs 0) (ih (comp_domain.mp h).2 (fun m => hs m.succ))

private theorem chain_co_aux {n} {f : Fin n → Op X b} {M : Fin n → Mat I}
    (hu : U.Nonempty) (h : U ⊆ dom (chain f)) (hs : Steps (coLip g) f U M) :
    product M ∈ coLip g (chain f) U := by
  induction n generalizing U with
  | zero => exact empty_co h hu
  | succ n ih =>
    exact co_comp h (hs 0) (ih (hu.image _) (comp_domain.mp h).2 (fun m => hs m.succ))

theorem chain_co {n} {f : Fin (n+1) → Op X b} {M : Fin (n+1) → Mat I}
    (h : U ⊆ dom (chain f)) (hs : Steps (coLip g) f U M) :
    product M ∈ coLip g (chain f) U := chain_co_aux (hs 0).1 h hs

abbrev Path (I : Type) (n : ℕ) := Fin n → I

def edges : {n : ℕ} → (Fin (n+1) → Mat I) → I → I → Path I n → List ENNReal
  | 0, M, i, j, _ => [M 0 i j]
  | _+1, M, i, j, p => M 0 i (p 0) :: edges (Fin.tail M) (p 0) j (Fin.tail p)

omit [Fintype I] [Nonempty I] in
theorem edges_indexed {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) :
    edges M i j p = List.ofFn (fun m => M m (Fin.cons (α := fun _ => I) i p m)
      (Fin.snoc (α := fun _ => I) p j m)) := by
  induction n generalizing i with
  | zero => simp [edges, List.ofFn_succ, Fin.snoc_zero]
  | succ n ih =>
    have hs : Fin.snoc (α := fun _ => I) p j =
        Fin.cons (p 0) (Fin.snoc (α := fun _ => I) (Fin.tail p) j) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    rw [List.ofFn_succ, edges, ih, hs]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.cons_self_tail, Fin.tail]

def weight {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) := (edges M i j p).prod
def hasZero {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) := 0 ∈ edges M i j p
def allPos {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) := ∀ a ∈ edges M i j p, 0 < a

abbrev one_path : Unique (Path I 0) := inferInstance

omit [Nonempty I] in
theorem expansion {n} (M : Fin (n+1) → Mat I) (i j : I) :
    product M i j = ∑ p : Path I n, weight M i j p := by
  induction n generalizing i with
  | zero => simp [product_one, weight, edges]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => I)
    rw [← e.sum_comp (weight M i j), Fintype.sum_prod_type]
    change (∑ k, product (Fin.tail M) k j * M 0 i k) = _
    apply Finset.sum_congr rfl
    intro k _
    rw [ih (Fin.tail M) k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    simp [e, Fin.consEquiv, weight, edges, mul_comm]

omit [Nonempty I] in
theorem product_zero {n} (M : Fin (n+1) → Mat I) (i j) :
    product M i j = 0 ↔ ∀ p, hasZero M i j p := by
  rw [expansion]
  simp [weight, hasZero, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le _)]

omit [Nonempty I] in
theorem product_pos {n} (M : Fin (n+1) → Mat I) (i j) :
    0 < product M i j ↔ ∃ p, allPos M i j p := by
  rw [pos_iff_ne_zero, ne_eq, product_zero, not_forall]
  apply exists_congr
  intro p
  exact ⟨fun h a ha => pos_iff_ne_zero.mpr (by rintro rfl; exact h ha),
    fun h hz => (lt_irrefl 0) (h 0 hz)⟩

section Certified
variable {n : ℕ} {f : Fin (n+1) → Op X b} {L K : Fin (n+1) → Mat I}
theorem certified_zero (_h : U ⊆ dom (chain f)) (_hl : Steps (lip g) f U L)
    (_hk : Steps (coLip g) f U K) (i j : I) : product L i j = 0 ↔ ∀ p, hasZero L i j p :=
  product_zero L i j

theorem certified_pos (_h : U ⊆ dom (chain f)) (_hl : Steps (lip g) f U L)
    (_hk : Steps (coLip g) f U K) (i j : I) : 0 < product K i j ↔ ∃ p, allPos K i j p :=
  product_pos K i j

end Certified

end HCH02
