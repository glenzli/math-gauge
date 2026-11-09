20 项均已完成，全部模块通过指定 Lean 4.29.1 与 mathlib 提交的编译检查。对应表中的 60 个声明均已核验，公理依赖仅含允许的三项；冻结模块与附件逐字节一致。以下为全部新增交付文件，保留附件中的 `formal_oet/`、`ATTRIBUTION.md` 和 `LICENSE`。

数学来源：Zhe Li（Glen Li / glenzli，[ORCID](https://orcid.org/0009-0006-6536-3453)），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[原作仓库](https://gitlab.com/glenzli/oet-public)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下是根据所选原文新写的形式化。

```toml filename=lakefile.toml
name = "lch02"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "formal_oet"

[[lean_lib]]
name = "LCH02"

[[lean_lib]]
name = "Main"
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=LCH02/Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §2.1, CC BY 4.0. https://glenzli.com/books/oet/
This file is a new formalization of the selected statements.
-/

noncomputable section

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

/-- Output index first, input index second. -/
abbrev Mat (I : Type) := Matrix I I ENNReal

def entry {I : Type} (A : Mat I) (i j : I) : ENNReal := A j i

variable {X I : Type} {bot : X} [Fintype I]

theorem entry_mul (B A : Mat I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k := rfl

def applyMatrix (A : Mat I) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ i, A j i * v i

theorem applyMatrix_mul (B A : Mat I) (v : I → ENNReal) (j : I) :
    applyMatrix (B * A) v j = applyMatrix B (applyMatrix A v) j := by
  simp only [applyMatrix, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

@[simp] theorem applyMatrix_one [DecidableEq I] (v : I → ENNReal) (j : I) :
    applyMatrix (1 : Mat I) v j = v j := by
  simp [applyMatrix, Matrix.one_apply, ite_mul]

theorem applyMatrix_mono (A : Mat I) {v w : I → ENNReal}
    (h : ∀ i, v i ≤ w i) (j : I) : applyMatrix A v j ≤ applyMatrix A w j := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) (A j i)

/-- The restricted domain condition is part of the predicate. -/
def LipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ applyMatrix L (fun i => d i x y) j

def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Mat I) : Prop :=
  LipOn d φ (dom φ) L

def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {L | LipOn d φ U L}

def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {L | Lip d φ L}

/-- Nonemptiness is required whenever a co-Lip certificate is asserted. -/
def CoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    applyMatrix K (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)

def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {K | CoLipOn d φ U K}

variable {d : I → X → X → ENNReal}
    {φ φ₁ φ₂ : Operator X bot} {U V : Set X} {A B : Mat I}

theorem lip_singleton [Unique I] (L : Mat I) :
    Lip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d (default : I) (φ.func x) (φ.func y) ≤
        L default default * d default x y := by
  constructor
  · intro h x hx y hy
    simpa [applyMatrix] using h.2 x hx y hy default
  · intro h
    refine ⟨fun _ hx => hx, ?_⟩
    intro x hx y hy j
    have hj : j = default := Subsingleton.elim _ _
    subst j
    simpa [applyMatrix] using h x hx y hy

theorem lipOn_mono (hUV : U ⊆ V) (h : LipOn d φ V A) : LipOn d φ U A :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem lipFamilyOn_antitone (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    lipFamilyOn d φ V ⊆ lipFamilyOn d φ U :=
  fun _ h => lipOn_mono hUV h

theorem lip_restrict (hU : U ⊆ dom φ) : lipFamily d φ ⊆ lipFamilyOn d φ U :=
  fun _ h => lipOn_mono hU h

theorem coLipOn_mono (hne : U.Nonempty) (hUV : U ⊆ V)
    (h : CoLipOn d φ V A) : CoLipOn d φ U A :=
  ⟨hne, hUV.trans h.2.1, fun x hx y hy j => h.2.2 x (hUV hx) y (hUV hy) j⟩

theorem coLipFamilyOn_antitone (hne : U.Nonempty) (hUV : U ⊆ V)
    (_hV : V ⊆ dom φ) : coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U :=
  fun _ h => coLipOn_mono hne hUV h

theorem coLip_restrict (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipFamilyOn d φ (dom φ) ⊆ coLipFamilyOn d φ U :=
  fun _ h => coLipOn_mono hne hU h

theorem composition_domains (hU : U ⊆ dom (φ₂ * φ₁)) :
    U ⊆ dom φ₁ ∧ φ₁.func '' U ⊆ dom φ₂ := by
  constructor
  · intro x hx hbot
    apply hU hx
    change φ₂.func (φ₁.func x) = bot
    rw [hbot, φ₂.preserves_bot]
  · rintro z ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_comp (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : LipOn d φ₁ U A) (h₂ : LipOn d φ₂ (φ₁.func '' U) B) :
    LipOn d (φ₂ * φ₁) U (B * A) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) ≤ _
  rw [applyMatrix_mul]
  exact (h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j).trans
    (applyMatrix_mono B (fun k => h₁.2 x hx y hy k) j)

theorem coLip_comp (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : CoLipOn d φ₁ U A) (h₂ : CoLipOn d φ₂ (φ₁.func '' U) B) :
    CoLipOn d (φ₂ * φ₁) U (B * A) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y))
  rw [applyMatrix_mul]
  exact (applyMatrix_mono B (fun k => h₁.2.2 x hx y hy k) j).trans
    (h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)

theorem coLip_entry_zero (h : CoLipOn d φ (dom φ) A)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    entry A i j = 0 := by
  have hle : A j i * d i x y ≤ 0 := calc
    A j i * d i x y ≤ applyMatrix A (fun k => d k x y) j :=
      Finset.single_le_sum (f := fun k => A j k * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := h.2.2 x hx y hy j
    _ = 0 := hout
  exact (mul_eq_zero.mp (le_antisymm hle (zero_le _))).resolve_right (ne_of_gt hin)

theorem identity_lip [DecidableEq I] (hU : U ⊆ dom (1 : Operator X bot)) :
    LipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ applyMatrix (1 : Mat I) (fun i => d i x y) j
  rw [applyMatrix_one]

theorem identity_coLip [DecidableEq I] (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    CoLipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change applyMatrix (1 : Mat I) (fun i => d i x y) j ≤ d j x y
  rw [applyMatrix_one]

end LCH02
```

```lean filename=LCH02/Products.lean
import LCH02.Bounds

noncomputable section

namespace LCH02

open scoped BigOperators

/-- Temporal order: step 0 acts first; the newest factor is on the left. -/
def orderedProduct {α : Type} [Monoid α] (f : ℕ → α) : ℕ → α
  | 0 => 1
  | n + 1 => f n * orderedProduct f n

theorem orderedProduct_eq_reverse_prod {α : Type} [Monoid α] (f : ℕ → α) (n : ℕ) :
    orderedProduct f n = ((List.range n).reverse.map f).prod := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orderedProduct, List.range_succ, List.reverse_append, ih]

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem entry_one (i j : I) :
    entry (1 : Mat I) i j = if i = j then 1 else 0 := by
  simp [entry, Matrix.one_apply, eq_comm]

def matrixProduct (M : ℕ → Mat I) (n : ℕ) : Mat I := orderedProduct M n

@[simp] theorem matrixProduct_zero (M : ℕ → Mat I) : matrixProduct M 0 = 1 := rfl

@[simp] theorem matrixProduct_succ (M : ℕ → Mat I) (n : ℕ) :
    matrixProduct M (n + 1) = M n * matrixProduct M n := rfl

@[simp] theorem matrixProduct_one (M : ℕ → Mat I) : matrixProduct M 1 = M 0 := by
  simp [matrixProduct, orderedProduct]

/-- A length-indexed path with fixed initial and final vertices. -/
inductive IndexPath (I : Type) : ℕ → I → I → Type
  | nil (i : I) : IndexPath I 0 i i
  | snoc {n : ℕ} {i k : I} (p : IndexPath I n i k) (j : I) :
      IndexPath I (n + 1) i j

namespace IndexPath

omit [Fintype I] [DecidableEq I]

def AllPositive (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .snoc (n := n) (k := k) p j =>
      AllPositive M p ∧ 0 < entry (M n) k j

def HasZero (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Prop
  | _, _, _, .nil _ => False
  | _, _, _, .snoc (n := n) (k := k) p j =>
      HasZero M p ∨ entry (M n) k j = 0

/-- Vertices in temporal order, including both endpoints. -/
def vertices : {n : ℕ} → {i j : I} → IndexPath I n i j → List I
  | _, _, _, .nil i => [i]
  | _, _, _, .snoc p j => vertices p ++ [j]

theorem vertices_length {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    p.vertices.length = n + 1 := by
  induction p with
  | nil => rfl
  | snoc p j ih => simp [vertices, ih]

/-- The endpoints of edge m, where 0 ≤ m < n. -/
def edge : {n : ℕ} → {i j : I} → IndexPath I n i j → Fin n → I × I
  | _, _, _, .nil _, m => Fin.elim0 m
  | _, _, _, .snoc (k := k) p j, m => Fin.lastCases (k, j) p.edge m

theorem allPositive_iff_edges {n : ℕ} {i j : I} (M : ℕ → Mat I)
    (p : IndexPath I n i j) :
    p.AllPositive M ↔ ∀ m : Fin n, 0 < entry (M m) (p.edge m).1 (p.edge m).2 := by
  induction p with
  | nil => simp [AllPositive]
  | snoc p j ih => simp [AllPositive, edge, Fin.forall_fin_succ', ih]

theorem not_allPositive_iff {n : ℕ} {i j : I} (M : ℕ → Mat I)
    (p : IndexPath I n i j) : ¬ p.AllPositive M ↔ p.HasZero M := by
  induction p with
  | nil => simp [AllPositive, HasZero]
  | snoc p j ih =>
      change (¬ (p.AllPositive M ∧ 0 < _)) ↔ p.HasZero M ∨ _ = 0
      rw [not_and_or, ih]
      simp

theorem hasZero_iff_edges {n : ℕ} {i j : I} (M : ℕ → Mat I)
    (p : IndexPath I n i j) :
    p.HasZero M ↔ ∃ m : Fin n, entry (M m) (p.edge m).1 (p.edge m).2 = 0 := by
  rw [← not_allPositive_iff, allPositive_iff_edges]
  simp

theorem one_step_unique {i j : I} (p : IndexPath I 1 i j) :
    p = IndexPath.snoc (IndexPath.nil i) j := by
  cases p with
  | snoc p j => cases p; rfl

@[simp] theorem single_positive (M : ℕ → Mat I) (i j : I) :
    (IndexPath.snoc (IndexPath.nil i) j).AllPositive M ↔ 0 < entry (M 0) i j := by
  simp [AllPositive]

@[simp] theorem single_zero (M : ℕ → Mat I) (i j : I) :
    (IndexPath.snoc (IndexPath.nil i) j).HasZero M ↔ entry (M 0) i j = 0 := by
  simp [HasZero]

end IndexPath

omit [DecidableEq I] in
theorem mul_entry_pos (B A : Mat I) (i j : I) :
    0 < entry (B * A) i j ↔ ∃ k, 0 < entry A i k ∧ 0 < entry B k j := by
  simp only [entry_mul, Finset.sum_pos_iff, Finset.mem_univ, true_and,
    ENNReal.mul_pos_iff]
  exact exists_congr fun _ => and_comm

theorem matrixProduct_pos_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    0 < entry (matrixProduct M n) i j ↔
      ∃ p : IndexPath I n i j, p.AllPositive M := by
  induction n generalizing i j with
  | zero =>
      constructor
      · intro h
        have hij : i = j := by
          by_contra hne
          simp [entry, Ne.symm hne] at h
        subst j
        exact ⟨.nil i, trivial⟩
      · rintro ⟨p, _⟩
        cases p
        simp [entry]
  | succ n ih =>
      rw [matrixProduct_succ, mul_entry_pos]
      constructor
      · rintro ⟨k, hk, hkj⟩
        obtain ⟨p, hp⟩ := (ih i k).mp hk
        exact ⟨.snoc p j, hp, hkj⟩
      · rintro ⟨p, hp⟩
        cases p with
        | @snoc n i k p j => exact ⟨k, (ih i k).mpr ⟨p, hp.1⟩, hp.2⟩

theorem matrixProduct_zero_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    entry (matrixProduct M n) i j = 0 ↔
      ∀ p : IndexPath I n i j, p.HasZero M := by
  have hzero : entry (matrixProduct M n) i j = 0 ↔
      ¬ 0 < entry (matrixProduct M n) i j := by simp
  rw [hzero, matrixProduct_pos_iff, not_exists]
  exact forall_congr' fun p => p.not_allPositive_iff M

/-- The n = 1 boundary, with no intermediate vertex to choose. -/
theorem one_step_criteria (M : ℕ → Mat I) (i j : I) :
    (0 < entry (M 0) i j ↔ ∃ p : IndexPath I 1 i j, p.AllPositive M) ∧
    (entry (M 0) i j = 0 ↔ ∀ p : IndexPath I 1 i j, p.HasZero M) := by
  constructor
  · simpa using matrixProduct_pos_iff M 1 i j
  · simpa using matrixProduct_zero_iff M 1 i j

end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.Products

noncomputable section

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

variable {X : Type} {bot : X}

/-- Only the first n operators are used; φ 0 is the book's φ₁. -/
def chain (φ : ℕ → Operator X bot) (n : ℕ) : Operator X bot := orderedProduct φ n

@[simp] theorem chain_zero (φ : ℕ → Operator X bot) : chain φ 0 = 1 := rfl

@[simp] theorem chain_succ (φ : ℕ → Operator X bot) (n : ℕ) :
    chain φ (n + 1) = φ n * chain φ n := rfl

theorem chain_eq_frozen (φ : ℕ → Operator X bot) (n : ℕ) :
    chain φ n = OperatorChain ((List.range n).reverse.map φ) := by
  rw [operator_chain_eq_prod]
  exact orderedProduct_eq_reverse_prod φ n

/-- This is U_{m+1} in the book, including m = 0. -/
def inputDomain (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ) : Set X :=
  (chain φ m).func '' U

@[simp] theorem inputDomain_zero (φ : ℕ → Operator X bot) (U : Set X) :
    inputDomain φ U 0 = U := by
  change id '' U = U
  exact Set.image_id U

theorem inputDomain_succ (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ) :
    inputDomain φ U (m + 1) = (φ m).func '' inputDomain φ U m := by
  change ((φ m).func ∘ (chain φ m).func) '' U =
    (φ m).func '' ((chain φ m).func '' U)
  rw [Set.image_image]
  rfl

theorem chain_dom_mono (φ : ℕ → Operator X bot) {m n : ℕ} (hmn : m ≤ n) :
    dom (chain φ n) ⊆ dom (chain φ m) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact fun _ hx => hx
  | succ n ih =>
      by_cases hm : m ≤ n
      · have hstep : dom (chain φ (n + 1)) ⊆ dom (chain φ n) :=
          (composition_domains (φ₁ := chain φ n) (φ₂ := φ n)
            (fun _ hx => hx)).1
        exact hstep.trans (ih hm)
      · have hm' : m = n + 1 := by omega
        subst m
        exact fun _ hx => hx

theorem inputDomain_subset_dom (φ : ℕ → Operator X bot) {U : Set X} {n m : ℕ}
    (hU : U ⊆ dom (chain φ n)) (hm : m < n) :
    inputDomain φ U m ⊆ dom (φ m) := by
  rintro z ⟨x, hx, rfl⟩
  change (chain φ (m + 1)).func x ≠ bot
  exact chain_dom_mono φ (Nat.succ_le_of_lt hm) (hU hx)

theorem inputDomain_nonempty (φ : ℕ → Operator X bot) {U : Set X}
    (hne : U.Nonempty) (m : ℕ) : (inputDomain φ U m).Nonempty :=
  hne.image _

variable {I : Type} [Fintype I] [DecidableEq I]
    {d : I → X → X → ENNReal}

theorem chain_lip (φ : ℕ → Operator X bot) (L : ℕ → Mat I) (U : Set X) (n : ℕ) :
    U ⊆ dom (chain φ n) →
    (∀ m < n, LipOn d (φ m) (inputDomain φ U m) (L m)) →
    LipOn d (chain φ n) U (matrixProduct L n) := by
  induction n with
  | zero =>
      intro hU _
      exact identity_lip hU
  | succ n ih =>
      intro hU hs
      have hp := ih (hU.trans (chain_dom_mono φ (Nat.le_succ n)))
        (fun m hm => hs m (Nat.lt_succ_of_lt hm))
      exact lip_comp hU hp (hs n (Nat.lt_succ_self n))

theorem finite_lip (φ : ℕ → Operator X bot) (L : ℕ → Mat I)
    (U : Set X) (n : ℕ) (_hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, LipOn d (φ m) (inputDomain φ U m) (L m)) :
    LipOn d (chain φ n) U (matrixProduct L n) :=
  chain_lip φ L U n hU hs

theorem chain_coLip (φ : ℕ → Operator X bot) (K : ℕ → Mat I) (U : Set X)
    (hne : U.Nonempty) (n : ℕ) :
    U ⊆ dom (chain φ n) →
    (∀ m < n, CoLipOn d (φ m) (inputDomain φ U m) (K m)) →
    CoLipOn d (chain φ n) U (matrixProduct K n) := by
  induction n with
  | zero =>
      intro hU _
      exact identity_coLip hne hU
  | succ n ih =>
      intro hU hs
      have hp := ih (hU.trans (chain_dom_mono φ (Nat.le_succ n)))
        (fun m hm => hs m (Nat.lt_succ_of_lt hm))
      exact coLip_comp hU hp (hs n (Nat.lt_succ_self n))

theorem finite_coLip (φ : ℕ → Operator X bot) (K : ℕ → Mat I)
    (U : Set X) (n : ℕ) (hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, CoLipOn d (φ m) (inputDomain φ U m) (K m)) :
    CoLipOn d (chain φ n) U (matrixProduct K n) := by
  have hne : U.Nonempty := by simpa using (hs 0 hn).1
  exact chain_coLip φ K U hne n hU hs

end LCH02
```

```lean filename=LCH02/Textbook.lean
import LCH02.Chains

/- The target statements with the textbook's full gauge-space context. -/
noncomputable section

-- These hypotheses deliberately retain the full textbook context.
set_option linter.unusedSectionVars false

namespace LCH02.Textbook

open formal_oet.vol_01.ch_01_foundations

section Gauge

variable {X I : Type} {bot : X}
    [fi : Fintype I] [ni : Nonempty I] [di : DecidableEq I]
    (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))

include hd ni di

theorem scalar_lip [Unique I] (φ : Operator X bot) (L : Mat I) :
    Lip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d (default : I) (φ.func x) (φ.func y) ≤
        L default default * d default x y :=
  lip_singleton L

theorem lip_antitone (φ : Operator X bot) (U V : Set X)
    (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipFamilyOn d φ V ⊆ lipFamilyOn d φ U :=
  lipFamilyOn_antitone hUV hV

theorem global_lip_restrict (φ : Operator X bot) (U : Set X) (hU : U ⊆ dom φ) :
    lipFamily d φ ⊆ lipFamilyOn d φ U := lip_restrict hU

theorem two_step_lip (φ₁ φ₂ : Operator X bot) (U : Set X) (A B : Mat I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : LipOn d φ₁ U A) (h₂ : LipOn d φ₂ (φ₁.func '' U) B) :
    LipOn d (φ₂ * φ₁) U (B * A) := lip_comp hU h₁ h₂

theorem coLip_antitone (φ : Operator X bot) (U V : Set X)
    (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U :=
  coLipFamilyOn_antitone hne hUV hV

theorem global_coLip_restrict (φ : Operator X bot) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipFamilyOn d φ (dom φ) ⊆ coLipFamilyOn d φ U := coLip_restrict hne hU

theorem forced_zero_entry (φ : Operator X bot) (K : Mat I)
    (hK : CoLipOn d φ (dom φ) K) (x y : X) (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (i j : I) (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    entry K i j = 0 := coLip_entry_zero hK hx hy hout hin

theorem two_step_coLip (φ₁ φ₂ : Operator X bot) (U : Set X) (A B : Mat I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : CoLipOn d φ₁ U A) (h₂ : CoLipOn d φ₂ (φ₁.func '' U) B) :
    CoLipOn d (φ₂ * φ₁) U (B * A) := coLip_comp hU h₁ h₂

theorem finite_lip_bound (φ : ℕ → Operator X bot) (L : ℕ → Mat I)
    (U : Set X) (n : ℕ) (hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, LipOn d (φ m) (inputDomain φ U m) (L m)) :
    LipOn d (chain φ n) U (matrixProduct L n) := finite_lip φ L U n hn hU hs

theorem finite_coLip_bound (φ : ℕ → Operator X bot) (K : ℕ → Mat I)
    (U : Set X) (n : ℕ) (hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, CoLipOn d (φ m) (inputDomain φ U m) (K m)) :
    CoLipOn d (chain φ n) U (matrixProduct K n) := finite_coLip φ K U n hn hU hs

theorem unit_lip (U : Set X) (_hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    LipOn d (1 : Operator X bot) U (1 : Mat I) := identity_lip hU

theorem unit_coLip (U : Set X) (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    CoLipOn d (1 : Operator X bot) U (1 : Mat I) := identity_coLip hne hU

end Gauge

section Matrices

variable {I : Type} [Fintype I] [ni : Nonempty I] [DecidableEq I]
include ni

theorem product_positive (M : ℕ → Mat I) (n : ℕ) (_hn : 0 < n) (i j : I) :
    0 < entry (matrixProduct M n) i j ↔
      ∃ p : IndexPath I n i j,
        ∀ m : Fin n, 0 < entry (M m) (p.edge m).1 (p.edge m).2 := by
  rw [matrixProduct_pos_iff]
  exact exists_congr fun p => p.allPositive_iff_edges M

theorem product_zero (M : ℕ → Mat I) (n : ℕ) (_hn : 0 < n) (i j : I) :
    entry (matrixProduct M n) i j = 0 ↔
      ∀ p : IndexPath I n i j,
        ∃ m : Fin n, entry (M m) (p.edge m).1 (p.edge m).2 = 0 := by
  rw [matrixProduct_zero_iff]
  exact forall_congr' fun p => p.hasZero_iff_edges M

end Matrices

end LCH02.Textbook
```

```lean filename=Main.lean
import LCH02.Bounds
import LCH02.Products
import LCH02.Chains
import LCH02.Textbook
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
        {"file": "LCH02/Bounds.lean", "name": "LCH02.LipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.Lip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipFamilyOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipFamily"}
      ],
      "representation": {
        "objects": "使用冻结 Operator、dom；ENNReal 表示扩展非负实数。",
        "parameters": "d、φ、U、L；LipOn 同时要求 U ⊆ dom φ。",
        "quantifiers": "∀ x∈U，∀ y∈U，∀ j∈I。",
        "conclusion": "输出距离 ≤ ∑ i, L j i * d i x y；全域取 U=dom φ，证书族为满足谓词的矩阵集合。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.CoLipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipFamilyOn"}
      ],
      "representation": {
        "objects": "受限 co-Lip 谓词及其矩阵集合。",
        "parameters": "d、φ、U、K；U.Nonempty 与 U ⊆ dom φ 均内置于合法性定义。",
        "quantifiers": "∀ x∈U，∀ y∈U，∀ j∈I。",
        "conclusion": "∑ i, K j i * d i x y ≤ 输出距离；没有任何全复合结论藏入定义。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.Mat"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.entry"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.entry_mul"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.applyMatrix"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.applyMatrix_mul"}
      ],
      "representation": {
        "objects": "Mat I = Matrix I I ENNReal。",
        "parameters": "entry A i j = A j i，输出为行、输入为列。",
        "quantifiers": "任意有限 I、A、B、输入 i 与输出 j。",
        "conclusion": "entry (B*A) i j = ∑ k, entry B k j * entry A i k；有限求和和乘法采用 ENNReal 的标准算术。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Products.lean", "name": "LCH02.orderedProduct"},
        {"file": "LCH02/Products.lean", "name": "LCH02.orderedProduct_eq_reverse_prod"},
        {"file": "LCH02/Products.lean", "name": "LCH02.entry_one"},
        {"file": "LCH02/Products.lean", "name": "LCH02.matrixProduct"},
        {"file": "LCH02/Products.lean", "name": "LCH02.matrixProduct_zero"},
        {"file": "LCH02/Products.lean", "name": "LCH02.matrixProduct_succ"},
        {"file": "LCH02/Products.lean", "name": "LCH02.matrixProduct_one"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.applyMatrix_one"}
      ],
      "representation": {
        "objects": "单位矩阵使用 mathlib 的 1，条目为 Kronecker δ。",
        "parameters": "M : ℕ → Mat I，M m 对应正文 M^(m+1)。",
        "quantifiers": "任意 n∈ℕ；只读取前 n 项，任意有限序列均可在其后补单位矩阵。DecidableEq 可由经典逻辑提供。",
        "conclusion": "零步乘积为 1；后继为 M n * matrixProduct M n；等于反序列表的普通乘积。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_eq_frozen"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.inputDomain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.inputDomain_zero"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.inputDomain_succ"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.inputDomain_subset_dom"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.inputDomain_nonempty"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.composition_domains"}
      ],
      "representation": {
        "objects": "chain φ n 是正文 c_n；φ m 是正文 φ_(m+1)。",
        "parameters": "inputDomain φ U m = c_m(U)，对应正文 U_(m+1)；有限算子序列可补恒等算子。",
        "quantifiers": "任意 n 与 m<n，假设 U ⊆ dom c_n。",
        "conclusion": "初域为 U，后继域是精确像集，且包含于本步定义域；与冻结 OperatorChain 的反序列表表示相等。"
      },
      "dependencies": ["CH02-D04"]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.AllPositive"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.HasZero"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.edge"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.allPositive_iff_edges"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.hasZero_iff_edges"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.not_allPositive_iff"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.one_step_unique"}
      ],
      "representation": {
        "objects": "IndexPath I n i j 是含 n 条边、首尾固定为 i,j 的有限顶点序列。nil 固定初点，snoc 追加任意终点，因此中间顶点没有额外限制。",
        "parameters": "edge p m 返回第 m+1 层的输入和输出指标。",
        "quantifiers": "全正为 ∀ m:Fin n；含零为 ∃ m:Fin n。",
        "conclusion": "递归谓词与逐层量词形式等价；n=1 的路径唯一且没有中间指标。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.scalar_lip"}
      ],
      "representation": {
        "objects": "单分量 Lip 条件。",
        "parameters": "Unique I 表示 I 恰有一个元素 default；保留规范空间假设 hd。",
        "quantifiers": "∀ x,y∈dom φ。",
        "conclusion": "全域矩阵条件当且仅当唯一分量上的标量 Lip 不等式。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.lip_antitone"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipOn_mono"}
      ],
      "representation": {
        "objects": "受限 Lip 证书族。",
        "parameters": "固定 φ；U ⊆ V ⊆ dom φ；有限非空规范族及 hd。",
        "quantifiers": "任意 V 上的合法矩阵。",
        "conclusion": "lipFamilyOn d φ V ⊆ lipFamilyOn d φ U。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.two_step_lip"}
      ],
      "representation": {
        "objects": "φ₂ * φ₁ 是先 φ₁ 后 φ₂ 的冻结算子乘法。",
        "parameters": "U ⊆ dom(φ₂*φ₁)，A 在 U 合法，B 在精确像集 φ₁.func '' U 合法；保留 hd。",
        "quantifiers": "任意两算子、两矩阵和起始子集。",
        "conclusion": "B*A 在 U 上是复合算子的 Lip 矩阵。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.coLip_antitone"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipOn_mono"}
      ],
      "representation": {
        "objects": "含非空性要求的 co-Lip 证书族。",
        "parameters": "U.Nonempty，U ⊆ V ⊆ dom φ；保留 hd。",
        "quantifiers": "任意 V 上合法矩阵。",
        "conclusion": "coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.forced_zero_entry"}
      ],
      "representation": {
        "objects": "全域 co-Lip 矩阵 K 的通道 i→j。",
        "parameters": "x,y∈dom φ，输出 j 距离为零，输入 i 距离严格为正；保留 hd。",
        "quantifiers": "任意这样的点对、通道和合法 K。",
        "conclusion": "entry K i j = 0；允许输入距离或系数为无穷。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.two_step_coLip"}
      ],
      "representation": {
        "objects": "两步 co-Lip 复合。",
        "parameters": "U ⊆ dom(φ₂*φ₁)，A 在 U 合法，B 在精确像集 φ₁.func '' U 合法；各合法性包含非空条件，保留 hd。",
        "quantifiers": "任意两算子、两矩阵和起始子集。",
        "conclusion": "B*A 在 U 上为合法 co-Lip 矩阵，结论保留 U.Nonempty。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.unit_lip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_lip"}
      ],
      "representation": {
        "objects": "恒等算子 1 与单位矩阵 1。",
        "parameters": "非空 U ⊆ dom id；保留 hd。",
        "quantifiers": "任意该类 U。",
        "conclusion": "单位矩阵为受限 Lip 证书；chain_zero 与 matrixProduct_zero 将其对应到零步复合。"
      },
      "dependencies": ["CH02-D01", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.unit_coLip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_coLip"}
      ],
      "representation": {
        "objects": "恒等算子与单位 co-Lip 矩阵。",
        "parameters": "非空 U ⊆ dom id；保留 hd。",
        "quantifiers": "任意该类 U。",
        "conclusion": "单位矩阵为合法 co-Lip 证书，含所需非空性；空乘积等于此单位矩阵。"
      },
      "dependencies": ["CH02-D02", "CH02-D04"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.product_positive"},
        {"file": "LCH02/Products.lean", "name": "LCH02.matrixProduct_pos_iff"},
        {"file": "LCH02/Products.lean", "name": "LCH02.IndexPath.single_positive"}
      ],
      "representation": {
        "objects": "任意 ENNReal 矩阵序列的有序乘积。",
        "parameters": "有限非空 I，n>0，固定输入 i 和输出 j。",
        "quantifiers": "存在 p:IndexPath I n i j，使所有 m:Fin n 的边条目严格为正。",
        "conclusion": "乘积条目 >0 当且仅当存在上述全正路径；n=1 由唯一单边路径及 matrixProduct_one 退化为原条目 >0。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.global_lip_restrict"}
      ],
      "representation": {
        "objects": "全域和受限 Lip 证书族。",
        "parameters": "U ⊆ dom φ；保留 hd。",
        "quantifiers": "任意全域合法矩阵。",
        "conclusion": "lipFamily d φ ⊆ lipFamilyOn d φ U。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.global_coLip_restrict"}
      ],
      "representation": {
        "objects": "全域和受限 co-Lip 证书族。",
        "parameters": "U.Nonempty，U ⊆ dom φ；保留 hd。",
        "quantifiers": "任意在 dom φ 上合法的 co-Lip 矩阵。",
        "conclusion": "coLipFamilyOn d φ (dom φ) ⊆ coLipFamilyOn d φ U。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.finite_lip_bound"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_lip"}
      ],
      "representation": {
        "objects": "c_n=chain φ n；所选逐步 Lip 矩阵的有序乘积。",
        "parameters": "n>0，U ⊆ dom c_n；保留 hd。",
        "quantifiers": "只假设每个 m<n 的 L m 在实际输入域 inputDomain φ U m 合法。",
        "conclusion": "从逐步证书归纳构造全复合的 Lip 证书；不假设全链估计或任何最优性。"
      },
      "dependencies": ["CH02-D01", "CH02-D04", "CH02-D05", "CH02-P04", "CH02-P11"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.finite_coLip_bound"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_coLip"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.finite_coLip"}
      ],
      "representation": {
        "objects": "c_n 及所选逐步 co-Lip 矩阵的有序乘积。",
        "parameters": "n>0，U ⊆ dom c_n；保留 hd。",
        "quantifiers": "每个 m<n 的 K m 只在实际输入域满足单步 CoLipOn。",
        "conclusion": "由第一步证书获得 U 非空，再归纳证明全链 CoLipOn；全链下界不是前提。"
      },
      "dependencies": ["CH02-D02", "CH02-D04", "CH02-D05", "CH02-P08", "CH02-P12"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Textbook.lean", "name": "LCH02.Textbook.product_zero"},
        {"file": "LCH02/Products.lean", "name": "LCH02.matrixProduct_zero_iff"},
        {"file": "LCH02/Products.lean", "name": "LCH02.one_step_criteria"}
      ],
      "representation": {
        "objects": "任意 ENNReal 矩阵序列的有序乘积。",
        "parameters": "有限非空 I，n>0，固定输入 i 和输出 j。",
        "quantifiers": "对每条 p:IndexPath I n i j，存在 m:Fin n 使该边条目为零。",
        "conclusion": "乘积条目为零当且仅当每条路径含零因子；覆盖 n=1，且使用标准 0*∞=0 算术。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```