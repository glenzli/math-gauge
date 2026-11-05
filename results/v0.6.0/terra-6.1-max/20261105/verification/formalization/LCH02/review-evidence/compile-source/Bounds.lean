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
