已在指定环境中检查 `Bounds.lean` 和 `Main.lean`；所用逻辑公理为 `propext`、`Classical.choice` 和 `Quot.sound`。

```lean filename=Bounds.lean
import Mathlib
import formal_oet.vol_01.ch_01_foundations.operator_space

/-
  Formalization of selected parts of Chapter 2 of Zhe Li (also known as
  Glen Li / glenzli), ORCID https://orcid.org/0009-0006-6536-3453,
  The Operator Evolution Theory, https://glenzli.com/books/oet/,
  https://gitlab.com/glenzli/oet-public, licensed under CC BY 4.0:
  https://creativecommons.org/licenses/by/4.0/ . This Lean formalization
  is a derivative work.
-/

namespace LCH02

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]

abbrev Gauge (I X : Type) := I → X → X → ENNReal
abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

/-- Row j, column i is the coefficient for the channel i → j. -/
def LipOn (d : Gauge I X) (φ : Operator X bot) (U : Set X)
    (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def Lip (d : Gauge I X) (φ : Operator X bot) (L : BoundMatrix I) : Prop :=
  LipOn d φ (dom φ) L

def lipFamilyOn (d : Gauge I X) (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {L | LipOn d φ U L}

def lipFamily (d : Gauge I X) (φ : Operator X bot) : Set (BoundMatrix I) :=
  {L | Lip d φ L}

/-- The nonemptiness and domain requirements belong to the restricted co-Lip predicate. -/
def CoLipOn (d : Gauge I X) (φ : Operator X bot) (U : Set X)
    (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def coLipFamilyOn (d : Gauge I X) (φ : Operator X bot) (U : Set X) :
    Set (BoundMatrix I) := {K | CoLipOn d φ U K}

def coLipFamily (d : Gauge I X) (φ : Operator X bot) : Set (BoundMatrix I) :=
  coLipFamilyOn d φ (dom φ)

theorem matrix_product_entry (A B : BoundMatrix I) (i j : I) :
    (A * B) j i = ∑ k, A j k * B k i := Matrix.mul_apply

theorem singleton_lip [Unique I] (d : Gauge I X) (φ : Operator X bot)
    (L : BoundMatrix I) :
    Lip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d default (φ.func x) (φ.func y) ≤ L default default * d default x y := by
  simp only [Lip, LipOn, Set.Subset.rfl, true_and, Fintype.sum_unique]
  constructor
  · intro h x hx y hy
    exact h x hx y hy default
  · intro h x hx y hy j
    simpa only [Subsingleton.elim j default] using h x hx y hy

theorem lip_antitone (d : Gauge I X) (φ : Operator X bot) (U V : Set X)
    (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipFamilyOn d φ V ⊆ lipFamilyOn d φ U := by
  intro L hL
  exact ⟨hUV.trans hV, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

theorem lip_global_restrict (d : Gauge I X) (φ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom φ) : lipFamily d φ ⊆ lipFamilyOn d φ U := by
  exact lip_antitone d φ U (dom φ) hU (Set.Subset.rfl)

theorem colip_antitone (d : Gauge I X) (φ : Operator X bot) (U V : Set X)
    (hU : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U := by
  intro K hK
  exact ⟨hU, hUV.trans hV, fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

theorem colip_global_restrict (d : Gauge I X) (φ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hsub : U ⊆ dom φ) :
    coLipFamily d φ ⊆ coLipFamilyOn d φ U := by
  exact colip_antitone d φ U (dom φ) hU hsub (Set.Subset.rfl)

theorem colip_forced_zero (d : Gauge I X) (φ : Operator X bot)
    (K : BoundMatrix I) (hK : K ∈ coLipFamily d φ)
    (i j : I) (x y : X) (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    K j i = 0 := by
  have hle : K j i * d i x y ≤ d j (φ.func x) (φ.func y) :=
    (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans
      (hK.2.2 x hx y hy j)
  have hz : K j i * d i x y = 0 := le_antisymm (hout ▸ hle) (zero_le _)
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact False.elim ((ne_of_gt hin) h)

/-- Distributing finite matrix multiplication through an input-distance vector. -/
theorem matrix_apply_assoc (A B : BoundMatrix I) (v : I → ENNReal) (j : I) :
    (∑ k, A j k * (∑ i, B k i * v i)) = ∑ i, (A * B) j i * v i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  exact (mul_assoc (A j k) (B k i) (v i)).symm

/-- Legality of both actual input sets follows from the composite domain. -/
theorem compose_domains (φ₁ φ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (φ₂ * φ₁)) :
    U ⊆ dom φ₁ ∧ φ₁.func '' U ⊆ dom φ₂ := by
  constructor
  · intro x hx hz
    apply hU hx
    change φ₂.func (φ₁.func x) = bot
    rw [hz, φ₂.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_compose (d : Gauge I X) (φ₁ φ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (φ₂ * φ₁)) (L₁ L₂ : BoundMatrix I)
    (h₁ : LipOn d φ₁ U L₁) (h₂ : LipOn d φ₂ (φ₁.func '' U) L₂) :
    LipOn d (φ₂ * φ₁) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y) ≤
        ∑ k, L₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, L₂ j k * (∑ i, L₁ k i * d i x y) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_left' (h₁.2 x hx y hy k) _
    _ = ∑ i, (L₂ * L₁) j i * d i x y := matrix_apply_assoc L₂ L₁ _ j

theorem colip_compose (d : Gauge I X) (φ₁ φ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (φ₂ * φ₁)) (K₁ K₂ : BoundMatrix I)
    (h₁ : CoLipOn d φ₁ U K₁) (h₂ : CoLipOn d φ₂ (φ₁.func '' U) K₂) :
    CoLipOn d (φ₂ * φ₁) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, (K₂ * K₁) j i * d i x y) =
        ∑ k, K₂ j k * (∑ i, K₁ k i * d i x y) := (matrix_apply_assoc K₂ K₁ _ j).symm
    _ ≤ ∑ k, K₂ j k * d k (φ₁.func x) (φ₁.func y) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_left' (h₁.2.2 x hx y hy k) _
    _ ≤ d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y) :=
      h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem identity_matrix_apply (d : Gauge I X) (x y : X) (j : I) :
    (∑ i, (1 : BoundMatrix I) j i * d i x y) = d j x y := by
  simp [Matrix.one_apply]

theorem identity_lip (d : Gauge I X) (U : Set X)
    (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    LipOn d (operator_identity : Operator X bot) U 1 := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simpa [operator_identity, identity_matrix_apply]

theorem identity_colip (d : Gauge I X) (U : Set X)
    (hn : U.Nonempty) (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    CoLipOn d (operator_identity : Operator X bot) U 1 := by
  refine ⟨hn, hU, ?_⟩
  intro x hx y hy j
  simpa [operator_identity, identity_matrix_apply]

/-- The lists in this section are chronological: the first item acts first. -/
def chainOperator : List (Operator X bot) → Operator X bot
  | [] => operator_identity
  | φ :: tail => chainOperator tail * φ

noncomputable def chainMatrix : List (BoundMatrix I) → BoundMatrix I
  | [] => 1
  | M :: tail => chainMatrix tail * M

theorem chainOperator_frozen (ops : List (Operator X bot)) :
    chainOperator ops = OperatorChain ops.reverse := by
  rw [operator_chain_eq_prod]
  induction ops with
  | nil => rfl
  | cons φ tail ih =>
      simp only [chainOperator, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [ih]

theorem chainMatrix_reverse_prod (ms : List (BoundMatrix I)) :
    chainMatrix ms = ms.reverse.prod := by
  induction ms with
  | nil => rfl
  | cons M tail ih =>
      simp only [chainMatrix, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [ih]

theorem zero_step_lip (d : Gauge I X) (U : Set X)
    (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    LipOn d (chainOperator ([] : List (Operator X bot))) U
      (chainMatrix ([] : List (BoundMatrix I))) :=
  identity_lip d U hU

theorem zero_step_colip (d : Gauge I X) (U : Set X)
    (hn : U.Nonempty) (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    CoLipOn d (chainOperator ([] : List (Operator X bot))) U
      (chainMatrix ([] : List (BoundMatrix I))) :=
  identity_colip d U hn hU

/-- Zero-based actual input set: index 0 is U₁; each successor is the exact image. -/
def actualDomain : List (Operator X bot) → Set X → Nat → Set X
  | _, U, 0 => U
  | [], U, _ + 1 => U
  | φ :: tail, U, n + 1 => actualDomain tail (φ.func '' U) n

def StepLip (d : Gauge I X) : Set X → List (Operator X bot × BoundMatrix I) → Prop
  | _, [] => True
  | U, (φ, M) :: tail => LipOn d φ U M ∧ StepLip d (φ.func '' U) tail

def StepCoLip (d : Gauge I X) : Set X → List (Operator X bot × BoundMatrix I) → Prop
  | _, [] => True
  | U, (φ, M) :: tail => CoLipOn d φ U M ∧ StepCoLip d (φ.func '' U) tail

theorem stepLip_iff_indexed (d : Gauge I X) (U : Set X)
    (steps : List (Operator X bot × BoundMatrix I)) :
    StepLip d U steps ↔ ∀ n p, steps[n]? = some p →
      LipOn d p.1 (actualDomain (steps.map Prod.fst) U n) p.2 := by
  induction steps generalizing U with
  | nil => simp [StepLip]
  | cons p tail ih =>
      rcases p with ⟨φ, M⟩
      constructor
      · intro hs n p hp
        cases n with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst p
            exact hs.1
        | succ n =>
            simp only [List.getElem?_cons_succ] at hp
            exact (ih _).mp hs.2 n p hp
      · intro hs
        constructor
        · exact hs 0 (φ, M) rfl
        · apply (ih _).mpr
          intro n p hp
          exact hs (n + 1) p hp

theorem stepCoLip_iff_indexed (d : Gauge I X) (U : Set X)
    (steps : List (Operator X bot × BoundMatrix I)) :
    StepCoLip d U steps ↔ ∀ n p, steps[n]? = some p →
      CoLipOn d p.1 (actualDomain (steps.map Prod.fst) U n) p.2 := by
  induction steps generalizing U with
  | nil => simp [StepCoLip]
  | cons p tail ih =>
      rcases p with ⟨φ, M⟩
      constructor
      · intro hs n p hp
        cases n with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst p
            exact hs.1
        | succ n =>
            simp only [List.getElem?_cons_succ] at hp
            exact (ih _).mp hs.2 n p hp
      · intro hs
        constructor
        · exact hs 0 (φ, M) rfl
        · apply (ih _).mpr
          intro n p hp
          exact hs (n + 1) p hp

theorem image_subset_dom_tail (φ : Operator X bot) (tail : List (Operator X bot))
    (U : Set X) (hU : U ⊆ dom (chainOperator (φ :: tail))) :
    φ.func '' U ⊆ dom (chainOperator tail) := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU hx

theorem initial_subset_dom (φ : Operator X bot) (tail : List (Operator X bot))
    (U : Set X) (hU : U ⊆ dom (chainOperator (φ :: tail))) :
    U ⊆ dom φ := by
  intro x hx hz
  apply hU hx
  change (chainOperator tail).func (φ.func x) = bot
  rw [hz, (chainOperator tail).preserves_bot]

theorem actualDomain_subset_step_dom (ops : List (Operator X bot)) (U : Set X)
    (hU : U ⊆ dom (chainOperator ops)) :
    ∀ n φ, ops[n]? = some φ → actualDomain ops U n ⊆ dom φ := by
  induction ops generalizing U with
  | nil => simp
  | cons op tail ih =>
      intro n φ h
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst φ
          exact initial_subset_dom op tail U hU
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          exact ih (op.func '' U) (image_subset_dom_tail op tail U hU) n φ h

/-- The theorem includes the empty list; in particular it covers every k ≥ 1. -/
theorem finite_lip (d : Gauge I X)
    (steps : List (Operator X bot × BoundMatrix I)) (U : Set X)
    (hU : U ⊆ dom (chainOperator (steps.map Prod.fst)))
    (hs : StepLip d U steps) :
    LipOn d (chainOperator (steps.map Prod.fst)) U
      (chainMatrix (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil =>
      exact identity_lip d U hU
  | cons p tail ih =>
      rcases p with ⟨φ, M⟩
      change LipOn d (chainOperator (tail.map Prod.fst) * φ) U
        (chainMatrix (tail.map Prod.snd) * M)
      apply lip_compose d φ (chainOperator (tail.map Prod.fst)) U hU M
        (chainMatrix (tail.map Prod.snd)) hs.1
      exact ih (φ.func '' U) (image_subset_dom_tail φ (tail.map Prod.fst) U hU) hs.2

theorem finite_colip_aux (d : Gauge I X)
    (steps : List (Operator X bot × BoundMatrix I)) (U : Set X)
    (hn : U.Nonempty) (hU : U ⊆ dom (chainOperator (steps.map Prod.fst)))
    (hs : StepCoLip d U steps) :
    CoLipOn d (chainOperator (steps.map Prod.fst)) U
      (chainMatrix (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil =>
      exact identity_colip d U hn hU
  | cons p tail ih =>
      rcases p with ⟨φ, M⟩
      change CoLipOn d (chainOperator (tail.map Prod.fst) * φ) U
        (chainMatrix (tail.map Prod.snd) * M)
      apply colip_compose d φ (chainOperator (tail.map Prod.fst)) U hU M
        (chainMatrix (tail.map Prod.snd)) hs.1
      exact ih (φ.func '' U) (hn.image φ.func)
        (image_subset_dom_tail φ (tail.map Prod.fst) U hU) hs.2

/-- For a positive-length chain, nonemptiness follows from the first co-Lip certificate. -/
theorem finite_colip (d : Gauge I X)
    (steps : List (Operator X bot × BoundMatrix I)) (U : Set X)
    (hpos : steps ≠ []) (hU : U ⊆ dom (chainOperator (steps.map Prod.fst)))
    (hs : StepCoLip d U steps) :
    CoLipOn d (chainOperator (steps.map Prod.fst)) U
      (chainMatrix (steps.map Prod.snd)) := by
  apply finite_colip_aux d steps U _ hU hs
  cases steps with
  | nil => exact False.elim (hpos rfl)
  | cons p tail =>
      rcases p with ⟨φ, M⟩
      exact hs.1.1

/-- A path records successive vertices after the starting vertex, including the final one. -/
def PathEndsAt : I → I → List I → Prop
  | i, j, [] => i = j
  | _, j, k :: tail => PathEndsAt k j tail

def PathAllPositive : List (BoundMatrix I) → I → List I → Prop
  | [], _, [] => True
  | M :: tail, i, k :: nodes => 0 < M k i ∧ PathAllPositive tail k nodes
  | _, _, _ => False

def PathHasZero : List (BoundMatrix I) → I → List I → Prop
  | M :: tail, i, k :: nodes => M k i = 0 ∨ PathHasZero tail k nodes
  | _, _, _ => False

def IsIndexPath (ms : List (BoundMatrix I)) (i j : I) (nodes : List I) : Prop :=
  nodes.length = ms.length ∧ PathEndsAt i j nodes

theorem path_one (M : BoundMatrix I) (i j : I) (nodes : List I) :
    IsIndexPath [M] i j nodes ↔ nodes = [j] := by
  cases nodes with
  | nil => simp [IsIndexPath]
  | cons k tail =>
      cases tail with
      | nil => simp [IsIndexPath, PathEndsAt]
      | cons l tail => simp [IsIndexPath]

theorem mul_positive_iff (a b : ENNReal) : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

theorem path_zero_iff_not_positive (ms : List (BoundMatrix I)) (i : I) (nodes : List I)
    (hlen : nodes.length = ms.length) :
    PathHasZero ms i nodes ↔ ¬ PathAllPositive ms i nodes := by
  induction ms generalizing i nodes with
  | nil =>
      cases nodes with
      | nil => simp [PathHasZero, PathAllPositive]
      | cons k nodes => simp at hlen
  | cons M tail ih =>
      cases nodes with
      | nil => simp at hlen
      | cons k nodes =>
          have hlen' : nodes.length = tail.length := by simpa using hlen
          change (M k i = 0 ∨ PathHasZero tail k nodes) ↔
            ¬ (0 < M k i ∧ PathAllPositive tail k nodes)
          rw [not_and_or, ← ih k nodes hlen']
          simp only [pos_iff_ne_zero, not_not]

theorem matrix_product_positive_iff (ms : List (BoundMatrix I)) (i j : I) :
    0 < chainMatrix ms j i ↔
      ∃ nodes, IsIndexPath ms i j nodes ∧ PathAllPositive ms i nodes := by
  induction ms generalizing i j with
  | nil =>
      by_cases h : i = j <;>
        simp [chainMatrix, Matrix.one_apply, IsIndexPath, PathEndsAt, PathAllPositive,
          h, eq_comm]
  | cons M tail ih =>
      change 0 < (chainMatrix tail * M) j i ↔ _
      rw [Matrix.mul_apply, Finset.sum_pos_iff]
      constructor
      · rintro ⟨k, _, hk⟩
        obtain ⟨htail, hfirst⟩ := mul_positive_iff _ _ |>.mp hk
        obtain ⟨nodes, ⟨hlen, hend⟩, hpos⟩ := (ih k j).mp htail
        refine ⟨k :: nodes, ?_, ?_⟩
        · exact ⟨by simpa using hlen, hend⟩
        · exact ⟨hfirst, hpos⟩
      · rintro ⟨nodes, ⟨hlen, hend⟩, hpos⟩
        cases nodes with
        | nil => simp at hlen
        | cons k nodes =>
            have hlen' : nodes.length = tail.length := by simpa using hlen
            refine ⟨k, Finset.mem_univ k, ?_⟩
            apply (mul_positive_iff _ _).mpr
            exact ⟨(ih k j).mpr ⟨nodes, ⟨hlen', hend⟩, hpos.2⟩, hpos.1⟩

theorem matrix_product_zero_iff (ms : List (BoundMatrix I)) (i j : I) :
    chainMatrix ms j i = 0 ↔
      ∀ nodes, IsIndexPath ms i j nodes → PathHasZero ms i nodes := by
  constructor
  · intro hz nodes ⟨hlen, hend⟩
    apply (path_zero_iff_not_positive ms i nodes hlen).mpr
    intro hp
    have hpos := (matrix_product_positive_iff ms i j).mpr ⟨nodes, ⟨hlen, hend⟩, hp⟩
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  · intro h
    apply le_antisymm _ (zero_le _)
    by_contra hn
    have hpos : 0 < chainMatrix ms j i := lt_of_not_ge hn
    obtain ⟨nodes, ⟨hlen, hend⟩, hp⟩ := (matrix_product_positive_iff ms i j).mp hpos
    exact ((path_zero_iff_not_positive ms i nodes hlen).mp (h nodes ⟨hlen, hend⟩)) hp

theorem matrix_product_one_step (M : BoundMatrix I) (i j : I) :
    chainMatrix [M] j i = M j i := by simp [chainMatrix]

theorem path_one_positive (M : BoundMatrix I) (i j : I) :
    PathAllPositive [M] i [j] ↔ 0 < M j i := by simp [PathAllPositive]

theorem path_one_zero (M : BoundMatrix I) (i j : I) :
    PathHasZero [M] i [j] ↔ M j i = 0 := by simp [PathHasZero]

end LCH02
```

```lean filename=Main.lean
import Bounds
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.Gauge"},
        {"file": "Bounds.lean", "name": "LCH02.LipOn"},
        {"file": "Bounds.lean", "name": "LCH02.Lip"},
        {"file": "Bounds.lean", "name": "LCH02.lipFamilyOn"},
        {"file": "Bounds.lean", "name": "LCH02.lipFamily"}
      ],
      "representation": {
        "objects": "Gauge I X 是分量函数族；算子与定义域使用冻结模块的 Operator 和 dom。",
        "parameters": "I 为有限指标类型，L 为以输出为行、输入为列的 ENNReal 矩阵；允许无穷大。",
        "quantifiers": "LipOn 明确包含 U⊆dom φ，并对 U 内任意 x、y 和任意输出分量 j 要求全部有限和不等式。",
        "conclusion": "Lip 是 U=dom φ 的特例，lipFamilyOn 和 lipFamily 分别是满足相应谓词的矩阵集合。形式化甚至允许 I 为空，故覆盖原文的非空情形。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.CoLipOn"},
        {"file": "Bounds.lean", "name": "LCH02.coLipFamilyOn"},
        {"file": "Bounds.lean", "name": "LCH02.coLipFamily"}
      ],
      "representation": {
        "objects": "CoLipOn 和 coLipFamilyOn 分别是受限 co-Lip 谓词和矩阵族；coLipFamily 是在整个定义域上的该族。",
        "parameters": "矩阵条目为 ENNReal，K j i 对应 K_{i→j}。",
        "quantifiers": "显式要求 U 非空、U⊆dom φ，且对所有 x、y∈U 和 j∈I 有求和下界。",
        "conclusion": "集合成员恰为满足这些条件的矩阵；定义域为空时全域 co-Lip 族为空。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.BoundMatrix"},
        {"file": "Bounds.lean", "name": "LCH02.matrix_product_entry"}
      ],
      "representation": {
        "objects": "BoundMatrix I 为 Matrix I I ENNReal。",
        "parameters": "数学条目 M_{i→j} 表示为 M j i。",
        "quantifiers": "对任意有限 I、任意矩阵 A、B 及 i、j。",
        "conclusion": "(A*B) j i = ∑ k, A j k * B k i，即后一步矩阵在左；采用 ENNReal 的零和无穷乘法。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.chainMatrix"},
        {"file": "Bounds.lean", "name": "LCH02.chainMatrix_reverse_prod"},
        {"file": "Bounds.lean", "name": "LCH02.matrix_product_one_step"}
      ],
      "representation": {
        "objects": "chainMatrix 是按时间先后列出的矩阵列表的有序乘积。",
        "parameters": "输入 [M¹,…,Mⁿ]，单位矩阵使用 Matrix 的 1。",
        "quantifiers": "对任意有限列表，包括空列表和单元素列表。",
        "conclusion": "空列表为 1；递归式 chainMatrix (M::tail)=chainMatrix tail*M，reverse_prod 证明等于反转列表的标准乘积；单步恰为 M。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.chainOperator"},
        {"file": "Bounds.lean", "name": "LCH02.chainOperator_frozen"},
        {"file": "Bounds.lean", "name": "LCH02.actualDomain"},
        {"file": "Bounds.lean", "name": "LCH02.actualDomain_subset_step_dom"}
      ],
      "representation": {
        "objects": "chainOperator 使用按先后顺序列出的算子；actualDomain 是对应的实际中间输入集。",
        "parameters": "actualDomain ops U 0=U₁，后继逐步取当前算子的整个集合像，原文 U_m 对应索引 m-1。",
        "quantifiers": "对每个存在的第 n 步 ops[n]?=some φ，起始集在全复合定义域内。",
        "conclusion": "actualDomain 在该步包含于 dom φ；chainOperator_frozen 证明它与冻结 OperatorChain 对反转列表的复合完全相同。超出列表长度的索引不参与链陈述。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.PathEndsAt"},
        {"file": "Bounds.lean", "name": "LCH02.IsIndexPath"},
        {"file": "Bounds.lean", "name": "LCH02.PathAllPositive"},
        {"file": "Bounds.lean", "name": "LCH02.PathHasZero"},
        {"file": "Bounds.lean", "name": "LCH02.path_one"},
        {"file": "Bounds.lean", "name": "LCH02.path_one_positive"},
        {"file": "Bounds.lean", "name": "LCH02.path_one_zero"}
      ],
      "representation": {
        "objects": "路径存成经过每一步后的节点列表，包含最后的 j，不包含起点 i。",
        "parameters": "n 个矩阵对应 n 个节点 [k₁,…,kₙ₋₁,j]，前接起点 i=k₀；节点长度等于矩阵列表长度。",
        "quantifiers": "IsIndexPath 检查长度和终点；PathAllPositive 与 PathHasZero 逐层检查对应 Mᵐ(kₘ,kₘ₋₁)。",
        "conclusion": "这与原文 n−1 个中间指标双向对应；path_one 证明 n=1 时唯一节点列表为 [j]，没有中间指标，两个单步谓词分别化为条目正与条目零。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [{"file": "Bounds.lean", "name": "LCH02.singleton_lip"}],
      "representation": {
        "objects": "单分量指标集表示为 Unique I。",
        "parameters": "default 是唯一的分量 i。",
        "quantifiers": "所有定义域内点对，且原谓词的所有输出指标都归为 default。",
        "conclusion": "全域 Lip 矩阵合法当且仅当唯一标量 Lip 不等式成立。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [{"file": "Bounds.lean", "name": "LCH02.lip_antitone"}],
      "representation": {
        "objects": "两个受限 Lip 证书族以集合包含比较。",
        "parameters": "U⊆V⊆dom φ。",
        "quantifiers": "任意矩阵及 U 中任意两个点和输出分量。",
        "conclusion": "lipFamilyOn d φ V ⊆ lipFamilyOn d φ U。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.matrix_apply_assoc"},
        {"file": "Bounds.lean", "name": "LCH02.compose_domains"},
        {"file": "Bounds.lean", "name": "LCH02.lip_compose"}
      ],
      "representation": {
        "objects": "两步算子、其各自的受限 Lip 矩阵及标准矩阵乘法。",
        "parameters": "U⊆dom(φ₂*φ₁)，第二步输入域恰为 φ₁.func '' U，而非任意超集。",
        "quantifiers": "对 U 内任意 x、y 及输出分量 j 使用每一步证书。",
        "conclusion": "L₂*L₁ 是 φ₂∘φ₁ 在 U 的合法 Lip 矩阵；compose_domains 证明两个局部定义域合法，有限分配及求和换序在 ENNReal 中证明。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [{"file": "Bounds.lean", "name": "LCH02.colip_antitone"}],
      "representation": {
        "objects": "两个受限 co-Lip 矩阵族。",
        "parameters": "U 非空且 U⊆V⊆dom φ；V 的非空性由此蕴含。",
        "quantifiers": "任意矩阵及 U 中全部点对和输出分量。",
        "conclusion": "coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U，结果仍显式带 U 非空。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [{"file": "Bounds.lean", "name": "LCH02.colip_forced_zero"}],
      "representation": {
        "objects": "全定义域 co-Lip 矩阵 K 与通道 i→j。",
        "parameters": "x、y 属于 dom φ；输出 j 距离为零而输入 i 距离严格为正。",
        "quantifiers": "对任意符合前提的矩阵、点对与指标。",
        "conclusion": "K j i=0；由单项不大于非负总和及 ENNReal 无零因子证明。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.compose_domains"},
        {"file": "Bounds.lean", "name": "LCH02.colip_compose"}
      ],
      "representation": {
        "objects": "两步受限 co-Lip 证书与其矩阵乘积。",
        "parameters": "U⊆dom(φ₂*φ₁)，第二步域精确为 φ₁.func '' U；第一步证书包含 U 非空。",
        "quantifiers": "对 U 中所有 x、y 和每个输出分量，逐步使用下界。",
        "conclusion": "K₂*K₁ 是全复合在 U 的合法 co-Lip 矩阵，结论保留非空和定义域条件。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P04"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.identity_matrix_apply"},
        {"file": "Bounds.lean", "name": "LCH02.identity_lip"},
        {"file": "Bounds.lean", "name": "LCH02.zero_step_lip"}
      ],
      "representation": {
        "objects": "冻结的恒等算子、单位矩阵及空算子链和空矩阵链。",
        "parameters": "U⊆dom id；不要求 U 非空，因而覆盖原文所述非空 U。",
        "quantifiers": "任意 U 中点对和任意分量。",
        "conclusion": "单位矩阵满足恒等算子的 Lip 界；zero_step_lip 直接给出空链和空乘积形式。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.identity_colip"},
        {"file": "Bounds.lean", "name": "LCH02.zero_step_colip"}
      ],
      "representation": {
        "objects": "恒等算子及单位矩阵，亦为零步链和空矩阵乘积。",
        "parameters": "U 非空且 U⊆dom id。",
        "quantifiers": "对 U 中每个点对和每个分量。",
        "conclusion": "单位矩阵满足 co-Lip 界，包含原文要求的非空与定义域条件。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P11"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.mul_positive_iff"},
        {"file": "Bounds.lean", "name": "LCH02.matrix_product_positive_iff"},
        {"file": "Bounds.lean", "name": "LCH02.matrix_product_one_step"},
        {"file": "Bounds.lean", "name": "LCH02.path_one_positive"}
      ],
      "representation": {
        "objects": "任意 ENNReal 矩阵有序列表的乘积条目与有限指标路径。",
        "parameters": "i 为起点，j 为终点；节点列表末尾含 j。",
        "quantifiers": "对任意有限列表、任意 i、j；尤其对长度 n≥1 的每个乘积。",
        "conclusion": "乘积 (j,i) 严格正当且仅当存在全路径条目严格正的路径；定理还涵盖空乘积，单步引理明确覆盖 n=1。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [{"file": "Bounds.lean", "name": "LCH02.lip_global_restrict"}],
      "representation": {
        "objects": "全域和受限 Lip 证书族。",
        "parameters": "任意 U⊆dom φ。",
        "quantifiers": "任意全域合法 Lip 矩阵。",
        "conclusion": "全域族包含于 U 上的受限族，由反单调性取 V=dom φ。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [{"file": "Bounds.lean", "name": "LCH02.colip_global_restrict"}],
      "representation": {
        "objects": "全定义域和受限 co-Lip 证书族。",
        "parameters": "U 非空且 U⊆dom φ。",
        "quantifiers": "任意全域合法 co-Lip 矩阵。",
        "conclusion": "全域族包含于 U 上的受限族，由反单调性取 V=dom φ。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.StepLip"},
        {"file": "Bounds.lean", "name": "LCH02.stepLip_iff_indexed"},
        {"file": "Bounds.lean", "name": "LCH02.finite_lip"}
      ],
      "representation": {
        "objects": "steps 为按作用先后排列的 (单步算子, 单步矩阵) 列表；两个投影分别形成算子链与矩阵链。",
        "parameters": "U⊆dom 全复合；每步使用当前集合的精确像作为下一步输入域。",
        "quantifiers": "StepLip 仅逐项给出该步证书；stepLip_iff_indexed 证明它等价于对每个存在的索引在 actualDomain 上具有对应单步证书。",
        "conclusion": "finite_lip 从所有单步证书推出整个链在 U 上具有逆时间次序的乘积证书；对所有长度成立，特别是原文 n≥1。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P04", "CH02-P11"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.StepCoLip"},
        {"file": "Bounds.lean", "name": "LCH02.stepCoLip_iff_indexed"},
        {"file": "Bounds.lean", "name": "LCH02.finite_colip_aux"},
        {"file": "Bounds.lean", "name": "LCH02.finite_colip"}
      ],
      "representation": {
        "objects": "按作用先后排列的算子和 co-Lip 矩阵配对列表。",
        "parameters": "非空步骤列表、U⊆dom 全复合，以及每步在精确实际输入域上的 co-Lip 证书。",
        "quantifiers": "stepCoLip_iff_indexed 证明所有列表位置的逐步证书与递归前提等价，不把全链结论作为假设。",
        "conclusion": "finite_colip 给出全复合在 U 上的逆时间次序乘积 co-Lip 证书；U 非空由第一步证书推出，不额外假设。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P08", "CH02-P12"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "LCH02.path_zero_iff_not_positive"},
        {"file": "Bounds.lean", "name": "LCH02.matrix_product_zero_iff"},
        {"file": "Bounds.lean", "name": "LCH02.matrix_product_one_step"},
        {"file": "Bounds.lean", "name": "LCH02.path_one_zero"}
      ],
      "representation": {
        "objects": "任意 ENNReal 矩阵列表的乘积条目，以及逐步节点路径中的零因子。",
        "parameters": "路径从 i 到 j，列表按时间顺序排列，最后的节点为 j。",
        "quantifiers": "对所有有限矩阵列表、所有 i、j，且对每一条长度匹配、终点正确的路径。",
        "conclusion": "乘积条目等于零当且仅当每条路径至少有一个零条目；定理比 n≥1 更一般，单步引理显式给出 n=1 的退化。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```