/-
Formalization of selected material from The Operator Evolution Theory by Zhe Li
(Glen Li / glenzli), https://glenzli.com/books/oet/, CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/). Adapted to Lean.
-/
import formal_oet.vol_01.ch_01_foundations.operator_space

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

namespace LCH02

noncomputable section
set_option linter.unusedSectionVars false
variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]

-- The first matrix index is the output, the second the input.
abbrev Mat (I : Type) := I → I → ENNReal

def matMul (A B : Mat I) : Mat I := fun j i => ∑ k, A j k * B k i
def matOne : Mat I := fun j i => if j = i then 1 else 0

def lip (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j, d j (f.func x) (f.func y) ≤ ∑ i, L j i * d i x y

def coLip (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j, ∑ i, K j i * d i x y ≤ d j (f.func x) (f.func y)

def lipFamily (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Mat I) :=
  {L | lip d f U L}
def coLipFamily (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Mat I) :=
  {K | coLip d f U K}
def globalLip (d : I → X → X → ENNReal) (f : Operator X bot) : Set (Mat I) :=
  lipFamily d f (dom f)

theorem lip_mono {d : I → X → X → ENNReal} {f : Operator X bot} {U V : Set X}
    {L : Mat I} (hUV : U ⊆ V) (h : lip d f V L) : lip d f U L :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict {d : I → X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {L : Mat I} (hU : U ⊆ dom f) (h : L ∈ globalLip d f) :
    L ∈ lipFamily d f U := lip_mono hU h

theorem colip_mono {d : I → X → X → ENNReal} {f : Operator X bot} {U V : Set X}
    {K : Mat I} (hU : U.Nonempty) (hUV : U ⊆ V) (h : coLip d f V K) : coLip d f U K :=
  ⟨hU, hUV.trans h.2.1, fun x hx y hy j => h.2.2 x (hUV hx) y (hUV hy) j⟩

theorem global_colip_restrict {d : I → X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {K : Mat I} (hU : U.Nonempty) (hsub : U ⊆ dom f)
    (h : K ∈ coLipFamily d f (dom f)) : K ∈ coLipFamily d f U := colip_mono hU hsub h

theorem singleton_lip {d : Unit → X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {L : Mat Unit} (h : lip d f U L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d () (f.func x) (f.func y) ≤ L () () * d () x y := by
  simpa using h.2 x hx y hy ()

theorem colip_entry_zero {d : I → X → X → ENNReal} {f : Operator X bot}
    {K : Mat I} {x y : X} {i j : I} (h : coLip d f (dom f) K)
    (hx : x ∈ dom f) (hy : y ∈ dom f) (hz : d j (f.func x) (f.func y) = 0)
    (hp : 0 < d i x y) : K j i = 0 := by
  have hs := h.2.2 x hx y hy j
  rw [hz] at hs
  have ht : K j i * d i x y = 0 := le_antisymm ((Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans hs) (zero_le _)
  exact (mul_eq_zero.mp ht).resolve_right (ne_of_gt hp)

theorem one_sum (v : I → ENNReal) (j : I) : (∑ i, matOne j i * v i) = v j := by
  classical
  simp [matOne]

theorem identity_lip (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    lip d (operator_identity : Operator X bot) U matOne := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i, matOne j i * d i x y
  rw [one_sum]

theorem identity_colip (d : I → X → X → ENNReal) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    coLip d (operator_identity : Operator X bot) U matOne := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, matOne j i * d i x y) ≤ d j x y
  rw [one_sum]

theorem matrix_sum (A B : Mat I) (v : I → ENNReal) (j : I) :
    (∑ i, matMul A B j i * v i) = ∑ k, A j k * (∑ i, B k i * v i) := by
  simp only [matMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem compose_domains {f g : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (g * f)) : U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx hf
    have h := hU hx
    apply h
    change g.func (f.func x) = bot
    rw [hf, g.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_compose {d : I → X → X → ENNReal} {f g : Operator X bot}
    {U : Set X} {A B : Mat I} (hU : U ⊆ dom (g * f))
    (hf : lip d f U B) (hg : lip d g (f.func '' U) A) :
    lip d (g * f) U (matMul A B) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (g.func (f.func x)) (g.func (f.func y)) ≤ _
  rw [matrix_sum]
  apply le_trans (hg.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_left' (hf.2 x hx y hy k) _

theorem colip_compose {d : I → X → X → ENNReal} {f g : Operator X bot}
    {U : Set X} {A B : Mat I} (hU : U ⊆ dom (g * f))
    (hf : coLip d f U B) (hg : coLip d g (f.func '' U) A) :
    coLip d (g * f) U (matMul A B) := by
  refine ⟨hf.1, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, matMul A B j i * d i x y) ≤ d j (g.func (f.func x)) (g.func (f.func y))
  rw [matrix_sum]
  apply le_trans _ (hg.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_left' (hf.2.2 x hx y hy k) _

-- Lists are chronological: the head acts first.
def chain : List (Operator X bot × Mat I) → Operator X bot
  | [] => 1
  | (f, _) :: tail => chain tail * f

def matProduct : List (Mat I) → Mat I
  | [] => matOne
  | M :: tail => matMul (matProduct tail) M

theorem matProduct_singleton (M : Mat I) (i j : I) : matProduct [M] j i = M j i := by
  simp [matProduct, matMul, matOne]

def matrixProduct (s : List (Operator X bot × Mat I)) : Mat I :=
  matProduct (s.map Prod.snd)

def inputDomain (U : Set X) : List (Operator X bot × Mat I) → ℕ → Set X
  | _, 0 => U
  | [], _ + 1 => U
  | (f, _) :: tail, n + 1 => inputDomain (f.func '' U) tail n

theorem chain_eq_operatorChain (s : List (Operator X bot × Mat I)) :
    chain s = OperatorChain (s.map Prod.fst).reverse := by
  rw [operator_chain_eq_prod]
  induction s with
  | nil => rfl
  | cons a tail ih =>
    rcases a with ⟨f, M⟩
    simp only [chain, List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one] at *
    rw [ih]

def lipSteps (d : I → X → X → ENNReal) (U : Set X) :
    List (Operator X bot × Mat I) → Prop
  | [] => True
  | (f, M) :: tail => lip d f U M ∧ lipSteps d (f.func '' U) tail

def colipSteps (d : I → X → X → ENNReal) (U : Set X) :
    List (Operator X bot × Mat I) → Prop
  | [] => True
  | (f, M) :: tail => coLip d f U M ∧ colipSteps d (f.func '' U) tail

theorem chain_lip (d : I → X → X → ENNReal) (s : List (Operator X bot × Mat I))
    (U : Set X) (hU : U ⊆ dom (chain s)) (hs : lipSteps d U s) :
    lip d (chain s) U (matrixProduct s) := by
  induction s generalizing U with
  | nil => exact identity_lip d U hU
  | cons a tail ih =>
    rcases a with ⟨f, M⟩
    have ht : f.func '' U ⊆ dom (chain tail) := (compose_domains hU).2
    exact lip_compose hU hs.1 (ih _ ht hs.2)

theorem chain_colip (d : I → X → X → ENNReal) (s : List (Operator X bot × Mat I))
    (U : Set X) (hne : U.Nonempty) (hU : U ⊆ dom (chain s)) (hs : colipSteps d U s) :
    coLip d (chain s) U (matrixProduct s) := by
  induction s generalizing U with
  | nil => exact identity_colip d U hne hU
  | cons a tail ih =>
    rcases a with ⟨f, M⟩
    have ht : f.func '' U ⊆ dom (chain tail) := (compose_domains hU).2
    have hn : (f.func '' U).Nonempty := hne.image f.func
    exact colip_compose hU hs.1 (ih _ hn ht hs.2)

inductive Path : List (Mat I) → I → I → Type
  | nil (i : I) : Path [] i i
  | cons {M : Mat I} {ms : List (Mat I)} {i j : I} (k : I)
      (tail : Path ms k j) : Path (M :: ms) i j

def Path.allPositive : {ms : List (Mat I)} → {i j : I} → Path ms i j → Prop
  | _, _, _, .nil _ => True
  | M :: _, i, _, .cons k tail => 0 < M k i ∧ tail.allPositive

def Path.hasZero : {ms : List (Mat I)} → {i j : I} → Path ms i j → Prop
  | _, _, _, .nil _ => False
  | M :: _, i, _, .cons k tail => M k i = 0 ∨ tail.hasZero

theorem Path.positive_iff_not_zero {ms : List (Mat I)} {i j : I} (p : Path ms i j) :
    p.allPositive ↔ ¬ p.hasZero := by
  induction p with
  | nil => simp [Path.allPositive, Path.hasZero]
  | cons k tail ih =>
    simp only [Path.allPositive, Path.hasZero, not_or, ← ih, pos_iff_ne_zero]

theorem enn_mul_positive (a b : ENNReal) : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    have hn : a * b ≠ 0 := pos_iff_ne_zero.mp h
    exact ⟨pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).1,
      pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2⟩
  · rintro ⟨ha, hb⟩
    exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb))

theorem matProduct_pos_iff (ms : List (Mat I)) (i j : I) :
    0 < matProduct ms j i ↔ ∃ p : Path ms i j, p.allPositive := by
  induction ms generalizing i j with
  | nil =>
    by_cases h : j = i
    · subst j
      constructor
      · intro _; exact ⟨Path.nil i, trivial⟩
      · intro _; simp [matProduct, matOne]
    · constructor
      · intro hp; simp [matProduct, matOne, h] at hp
      · rintro ⟨p, hp⟩
        cases p
        exact (h rfl).elim
  | cons M ms ih =>
    simp only [matProduct, matMul, Finset.sum_pos_iff, Finset.mem_univ, true_and]
    simp only [enn_mul_positive, ih]
    constructor
    · rintro ⟨k, ⟨⟨p, hp⟩, hm⟩⟩
      exact ⟨Path.cons k p, hm, hp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | cons k tail => exact ⟨k, ⟨⟨tail, hp.2⟩, hp.1⟩⟩

theorem matProduct_zero_iff (ms : List (Mat I)) (i j : I) :
    matProduct ms j i = 0 ↔ ∀ p : Path ms i j, p.hasZero := by
  rw [← nonpos_iff_eq_zero, ← not_lt, matProduct_pos_iff]
  simp only [not_exists, Path.positive_iff_not_zero, not_not]

theorem singleton_paths (M : Mat I) (i j : I) :
    ((∃ p : Path [M] i j, p.allPositive) ↔ 0 < M j i) ∧
    ((∀ p : Path [M] i j, p.hasZero) ↔ M j i = 0) := by
  constructor
  · rw [← matProduct_pos_iff, matProduct_singleton]
  · rw [← matProduct_zero_iff, matProduct_singleton]

end
end LCH02
