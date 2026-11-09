20项义务均已完成，全部目标模块通过 Lean 4.29.1 检查；核心定理的公理依赖仅为允许的三项。以下交付全部新增文件，冻结前置模块沿用附件原件。

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=lakefile.lean
import Lake
open Lake DSL

package lch02

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

lean_lib Frozen where
  roots := #[`formal_oet]
  globs := #[.submodules `formal_oet]

lean_lib LCH02 where
  globs := #[.submodules `LCH02]

@[default_target]
lean_lib Main
```

```lean filename=LCH02/Matrix.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §2.1, https://glenzli.com/books/oet/, CC BY 4.0.
This file is a new formalization of the selected obligations.
-/

open scoped BigOperators Classical Matrix

namespace LCH02

abbrev Mat (I : Type) := Matrix I I ENNReal

/-- The textbook entry i → j is row j, column i. -/
def entry {I : Type} (M : Mat I) (i j : I) : ENNReal := M j i

section Matrices
variable {I : Type} [Fintype I]

theorem entry_mul (A B : Mat I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k := rfl

omit [Fintype I] in
theorem entry_one (i j : I) :
    entry (1 : Mat I) i j = if j = i then 1 else 0 := by
  simp [entry, Matrix.one_apply]

/-- Matrices are listed in execution order: [M₁,...,Mₙ]. -/
noncomputable def matrixProduct : List (Mat I) → Mat I
  | [] => 1
  | M :: Ms => matrixProduct Ms * M

@[simp] theorem matrixProduct_nil : matrixProduct ([] : List (Mat I)) = 1 := rfl

@[simp] theorem matrixProduct_cons (M : Mat I) (Ms : List (Mat I)) :
    matrixProduct (M :: Ms) = matrixProduct Ms * M := rfl

@[simp] theorem matrixProduct_singleton (M : Mat I) :
    matrixProduct [M] = M := by simp [matrixProduct]

theorem matrixProduct_eq_reverse_prod (Ms : List (Mat I)) :
    matrixProduct Ms = Ms.reverse.prod := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih => simp [matrixProduct, ih, List.reverse_cons, List.prod_append]

/-- Multiplication by a matrix preserves pointwise inequalities, including ∞. -/
theorem mulVec_mono (M : Mat I) {v w : I → ENNReal} (h : ∀ i, v i ≤ w i) :
    ∀ j, (M *ᵥ v) j ≤ (M *ᵥ w) j := by
  intro j
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_right (h i) (M j i))

end Matrices

end LCH02
```

```lean filename=LCH02/Bounds.lean
import LCH02.Matrix

open scoped BigOperators Classical Matrix
open formal_oet.vol_01.ch_01_foundations

namespace LCH02

variable {X I : Type} {bot : X} [Fintype I]

/-- Domain legality is part of the restricted predicate. -/
def IsLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def IsLip (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Mat I) : Prop :=
  IsLipOn d φ (dom φ) L

def LipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {L | IsLipOn d φ U L}

def LipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {L | IsLip d φ L}

/-- In particular, no co-Lip certificate exists on the empty set. -/
def IsCoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def CoLipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {K | IsCoLipOn d φ U K}

theorem composite_domain (φ ψ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (ψ * φ)) :
    U ⊆ dom φ ∧ φ.func '' U ⊆ dom ψ := by
  constructor
  · intro x hx hbot
    have h := hU hx
    change ψ.func (φ.func x) ≠ bot at h
    exact h (by rw [hbot, ψ.preserves_bot])
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

section Gauge
variable [Nonempty I] {d : I → X → X → ENNReal}
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
include hd
set_option linter.unusedSectionVars false

theorem singleton_lip [Subsingleton I] (i : I) {φ : Operator X bot} {L : Mat I}
    (hL : IsLip d φ L) (x y : X) (hx : x ∈ dom φ) (hy : y ∈ dom φ) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hs : (∑ k, L i k * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact (hki (Subsingleton.elim _ _)).elim
    · simp
  simpa only [hs] using hL.2 x hx y hy i

theorem lip_antitone {φ : Operator X bot} {U V : Set X}
    (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    LipMatricesOn d φ V ⊆ LipMatricesOn d φ U := by
  intro L hL
  exact ⟨hUV.trans hL.1, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

theorem lip_restrict {φ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ) :
    LipMatrices d φ ⊆ LipMatricesOn d φ U :=
  lip_antitone hd hU (Set.Subset.refl _)

theorem colip_antitone {φ : Operator X bot} {U V : Set X}
    (hne : U.Nonempty) (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    CoLipMatricesOn d φ V ⊆ CoLipMatricesOn d φ U := by
  intro K hK
  exact ⟨hne, hUV.trans hK.2.1,
    fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

theorem colip_restrict {φ : Operator X bot} {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    CoLipMatricesOn d φ (dom φ) ⊆ CoLipMatricesOn d φ U :=
  colip_antitone hd hne hU (Set.Subset.refl _)

theorem lip_comp {φ ψ : Operator X bot} {U : Set X} {L₁ L₂ : Mat I}
    (hU : U ⊆ dom (ψ * φ)) (h₁ : IsLipOn d φ U L₁)
    (h₂ : IsLipOn d ψ (φ.func '' U) L₂) :
    IsLipOn d (ψ * φ) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤ _
  calc
    _ ≤ (L₂ *ᵥ (fun k => d k (φ.func x) (φ.func y))) j :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ (L₂ *ᵥ (L₁ *ᵥ (fun i => d i x y))) j :=
      mulVec_mono L₂ (h₁.2 x hx y hy) j
    _ = _ := congrFun (Matrix.mulVec_mulVec (fun i => d i x y) L₂ L₁) j

theorem colip_comp {φ ψ : Operator X bot} {U : Set X} {K₁ K₂ : Mat I}
    (hU : U ⊆ dom (ψ * φ)) (h₁ : IsCoLipOn d φ U K₁)
    (h₂ : IsCoLipOn d ψ (φ.func '' U) K₂) :
    IsCoLipOn d (ψ * φ) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
  calc
    _ = (K₂ *ᵥ (K₁ *ᵥ (fun i => d i x y))) j :=
      (congrFun (Matrix.mulVec_mulVec (fun i => d i x y) K₂ K₁) j).symm
    _ ≤ (K₂ *ᵥ (fun k => d k (φ.func x) (φ.func y))) j :=
      mulVec_mono K₂ (h₁.2.2 x hx y hy) j
    _ ≤ _ := h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_entry_zero {φ : Operator X bot} {K : Mat I}
    (hK : IsCoLipOn d φ (dom φ) K) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    K j i = 0 := by
  have hterm : K j i * d i x y ≤ 0 := by
    calc
      _ ≤ ∑ k, K j k * d k x y :=
        Finset.single_le_sum (fun k _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hout
  exact (mul_eq_zero.mp (le_antisymm hterm (zero_le _))).resolve_right (ne_of_gt hin)

theorem identity_lip {U : Set X} (hU : U ⊆ dom (1 : Operator X bot)) :
    IsLipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ((1 : Mat I) *ᵥ (fun i => d i x y)) j
  simp

theorem identity_colip {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsCoLipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change ((1 : Mat I) *ᵥ (fun i => d i x y)) j ≤ d j x y
  simp

end Gauge
end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.Bounds

open scoped BigOperators Classical Matrix
open formal_oet.vol_01.ch_01_foundations

namespace LCH02

variable {X : Type} {bot : X}

/-- [φ₁,...,φₖ] is executed left to right, yielding φₖ ∘ ... ∘ φ₁. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: ps => chain ps * φ

@[simp] theorem chain_nil : chain ([] : List (Operator X bot)) = 1 := rfl

@[simp] theorem chain_cons (φ : Operator X bot) (ps : List (Operator X bot)) :
    chain (φ :: ps) = chain ps * φ := rfl

@[simp] theorem chain_singleton (φ : Operator X bot) : chain [φ] = φ := by
  simp [chain]

theorem chain_eq_frozen (ps : List (Operator X bot)) :
    chain ps = OperatorChain ps.reverse := by
  rw [operator_chain_eq_prod]
  induction ps with
  | nil => rfl
  | cons φ ps ih => simp [chain, ih, List.reverse_cons, List.prod_append]

theorem chain_append (ps qs : List (Operator X bot)) :
    chain (ps ++ qs) = chain qs * chain ps := by
  induction ps with
  | nil => simp
  | cons φ ps ih => simp [ih, mul_assoc]

/-- The textbook Uₘ is intermediate ps U₁ (m-1). -/
def intermediate (ps : List (Operator X bot)) (U : Set X) (n : ℕ) : Set X :=
  (chain (ps.take n)).func '' U

@[simp] theorem intermediate_zero (ps : List (Operator X bot)) (U : Set X) :
    intermediate ps U 0 = U := by
  change (id : X → X) '' U = U
  exact Set.image_id U

@[simp] theorem intermediate_cons_succ (φ : Operator X bot)
    (ps : List (Operator X bot)) (U : Set X) (n : ℕ) :
    intermediate (φ :: ps) U (n + 1) = intermediate ps (φ.func '' U) n := by
  simp only [intermediate, List.take_succ_cons, chain_cons, Set.image_image]
  rfl

theorem intermediate_step (ps : List (Operator X bot)) (U : Set X)
    (n : ℕ) (hn : n < ps.length) :
    intermediate ps U (n + 1) = ps[n].func '' intermediate ps U n := by
  simp only [intermediate, List.take_succ_eq_append_getElem hn,
    chain_append, chain_singleton, Set.image_image]
  rfl

@[simp] theorem intermediate_final (ps : List (Operator X bot)) (U : Set X) :
    intermediate ps U ps.length = (chain ps).func '' U := by
  simp [intermediate]

/-- Full-composite legality forces legality at every actual input domain. -/
theorem intermediate_legal (ps : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain ps)) :
    ∀ n (hn : n < ps.length), intermediate ps U n ⊆ dom ps[n] := by
  induction ps generalizing U with
  | nil => intro n hn; simp at hn
  | cons φ ps ih =>
      intro n hn
      have hdom := composite_domain φ (chain ps) hU
      cases n with
      | zero => simpa using hdom.1
      | succ n =>
          simpa using ih hdom.2 n (by simpa using hn)

/-- A step stores only an operator and its chosen matrix, never a chain bound. -/
abbrev Step (X : Type) (bot : X) (I : Type) := Operator X bot × Mat I

section Gauge
variable {I : Type} [Fintype I] [Nonempty I] {d : I → X → X → ENNReal}
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
include hd

theorem chain_lip (ss : List (Step X bot I)) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => simpa using identity_lip hd hU
  | cons s ss ih =>
      have h₀ : IsLipOn d s.1 U s.2 := by
        simpa using hsteps 0 (by simp)
      have ht : ∀ n (hn : n < ss.length),
          IsLipOn d ss[n].1
            (intermediate (ss.map Prod.fst) (s.1.func '' U) n) ss[n].2 := by
        intro n hn
        simpa using hsteps (n + 1) (by simpa using hn)
      have hdom := (composite_domain s.1 (chain (ss.map Prod.fst)) hU).2
      exact lip_comp hd hU h₀ (ih hdom ht)

theorem finite_lip (ss : List (Step X bot I)) (_hne : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) :=
  chain_lip hd ss hU hsteps

theorem chain_colip (ss : List (Step X bot I)) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsCoLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsCoLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => simpa using identity_colip hd hne hU
  | cons s ss ih =>
      have h₀ : IsCoLipOn d s.1 U s.2 := by
        simpa using hsteps 0 (by simp)
      have ht : ∀ n (hn : n < ss.length),
          IsCoLipOn d ss[n].1
            (intermediate (ss.map Prod.fst) (s.1.func '' U) n) ss[n].2 := by
        intro n hn
        simpa using hsteps (n + 1) (by simpa using hn)
      have hdom := (composite_domain s.1 (chain (ss.map Prod.fst)) hU).2
      exact colip_comp hd hU h₀ (ih (hne.image s.1.func) hdom ht)

/-- Nonemptiness of U is obtained from the first local co-Lip certificate. -/
theorem finite_colip (ss : List (Step X bot I)) (hne : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsCoLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsCoLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) := by
  apply chain_colip hd ss _ hU hsteps
  cases ss with
  | nil => exact (hne rfl).elim
  | cons s ss => simpa using (hsteps 0 (by simp)).1

end Gauge
end LCH02
```

```lean filename=LCH02/Paths.lean
import LCH02.Matrix

open scoped BigOperators Classical Matrix

namespace LCH02

/-- The n internal vertices of a path of n+1 steps; endpoints are separate. -/
abbrev IndexPath (I : Type) (n : ℕ) := Fin n → I

variable {I : Type} [Fintype I]

/-- In execution order, the first edge goes from i to p(0). -/
def AllPositive : (M : Mat I) → (Ms : List (Mat I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => 0 < M j i
  | M, N :: Ns, i, j, p =>
      0 < M (p 0) i ∧ AllPositive N Ns (p 0) j (Fin.tail p)

/-- At least one of the edges of this particular path has zero weight. -/
def HasZero : (M : Mat I) → (Ms : List (Mat I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => M j i = 0
  | M, N :: Ns, i, j, p =>
      M (p 0) i = 0 ∨ HasZero N Ns (p 0) j (Fin.tail p)

omit [Fintype I] in
theorem hasZero_iff_not_allPositive (M : Mat I) (Ms : List (Mat I))
    (i j : I) (p : IndexPath I Ms.length) :
    HasZero M Ms i j p ↔ ¬ AllPositive M Ms i j p := by
  induction Ms generalizing M i with
  | nil => simp [HasZero, AllPositive]
  | cons N Ns ih =>
      simp only [HasZero, AllPositive, ih, not_and_or, not_lt, nonpos_iff_eq_zero]

/-- Every positive-length product, with no finiteness restriction on entries. -/
theorem matrixProduct_pos_iff (M : Mat I) (Ms : List (Mat I)) (i j : I) :
    0 < matrixProduct (M :: Ms) j i ↔
      ∃ p : IndexPath I Ms.length, AllPositive M Ms i j p := by
  induction Ms generalizing M i with
  | nil => simp [AllPositive, IndexPath]
  | cons N Ns ih =>
      rw [matrixProduct_cons, Matrix.mul_apply, Finset.sum_pos_iff]
      simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff]
      constructor
      · rintro ⟨k, hk, hM⟩
        obtain ⟨p, hp⟩ := (ih N k).mp hk
        exact ⟨Fin.cons k p, by simpa [AllPositive] using And.intro hM hp⟩
      · rintro ⟨p, hp⟩
        exact ⟨p 0, (ih N (p 0)).mpr ⟨Fin.tail p, hp.2⟩, hp.1⟩

/-- Zero is equivalent to a zero factor on every internal-index sequence. -/
theorem matrixProduct_zero_iff (M : Mat I) (Ms : List (Mat I)) (i j : I) :
    matrixProduct (M :: Ms) j i = 0 ↔
      ∀ p : IndexPath I Ms.length, HasZero M Ms i j p := by
  simp only [hasZero_iff_not_allPositive, ← not_exists,
    ← matrixProduct_pos_iff, not_lt, nonpos_iff_eq_zero]

omit [Fintype I] in
/-- For one step there is exactly one empty internal-index sequence. -/
theorem one_step_path (M : Mat I) (i j : I) :
    (∃! _p : IndexPath I 0, True) ∧
    (∀ p : IndexPath I 0, AllPositive M [] i j p ↔ 0 < M j i) ∧
    (∀ p : IndexPath I 0, HasZero M [] i j p ↔ M j i = 0) := by
  refine ⟨⟨Fin.elim0, trivial, fun p _ => Subsingleton.elim _ _⟩, ?_, ?_⟩
  · intro p; rfl
  · intro p; rfl

end LCH02
```

```lean filename=Main.lean
import LCH02.Matrix
import LCH02.Bounds
import LCH02.Chains
import LCH02.Paths
```

```lean filename=Audit.lean
import Main

#print axioms LCH02.singleton_lip
#print axioms LCH02.lip_antitone
#print axioms LCH02.lip_restrict
#print axioms LCH02.colip_antitone
#print axioms LCH02.colip_restrict
#print axioms LCH02.lip_comp
#print axioms LCH02.colip_comp
#print axioms LCH02.colip_entry_zero
#print axioms LCH02.identity_lip
#print axioms LCH02.identity_colip
#print axioms LCH02.chain_eq_frozen
#print axioms LCH02.intermediate_step
#print axioms LCH02.intermediate_legal
#print axioms LCH02.finite_lip
#print axioms LCH02.finite_colip
#print axioms LCH02.matrixProduct_pos_iff
#print axioms LCH02.matrixProduct_zero_iff
#print axioms LCH02.one_step_path
```

```text filename=NOTICE.md
Original mathematical source: Zhe Li (Glen Li / glenzli), ORCID
https://orcid.org/0009-0006-6536-3453, The Operator Evolution Theory,
Volume I, v1.0.0, https://glenzli.com/books/oet/,
DOI https://doi.org/10.5281/zenodo.21457931.
Source snapshot: https://github.com/glenzli/oet-public at commit
539b40cec73184d98e06d54fbd10e4b4698bd6e7.
Current public repository: https://gitlab.com/glenzli/oet-public.
License: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.

The LCH02 Lean modules are a new, AI-assisted formalization of the selected
source obligations. The underlying mathematics is attributed to Zhe Li.
The supplied formal_oet prerequisite sources are used unchanged.
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
        {"file": "LCH02/Bounds.lean", "name": "LCH02.IsLipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.IsLip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.LipMatricesOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.LipMatrices"}
      ],
      "representation": {
        "objects": "使用冻结 Operator、dom；d : I → X → X → ENNReal，L : Matrix I I ENNReal。",
        "parameters": "U 是指定受限域；IsLipOn 显式包含 U ⊆ dom φ。",
        "quantifiers": "对所有 x∈U、y∈U、j∈I 作有限指标求和；全域取 U=dom φ。",
        "conclusion": "L j i 表示 L_{i→j}；两个证书族是相应谓词的集合。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.IsCoLipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.CoLipMatricesOn"}
      ],
      "representation": {
        "objects": "受限 co-Lip 谓词及其矩阵集合，条目在 ENNReal 中。",
        "parameters": "谓词同时包含 U.Nonempty 和 U ⊆ dom φ；全域情况通过 U=dom φ 表示。",
        "quantifiers": "∀ x∈U，∀ y∈U，∀ j∈I。",
        "conclusion": "Σ_i K j i * d i x y ≤ d j (φ x) (φ y)，没有省略非空性。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.Mat"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.entry"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.entry_mul"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.mulVec_mono"}
      ],
      "representation": {
        "objects": "Mat I 是标准 Matrix I I ENNReal。",
        "parameters": "entry M i j=M j i，即输入为列、输出为行。",
        "quantifiers": "乘法公式对任意有限 I、矩阵 A B、端点 i j 成立。",
        "conclusion": "entry (B*A) i j=Σ_k entry B k j * entry A i k；使用标准 ENNReal 的 0*∞=0 算术。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.entry_one"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_nil"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_cons"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_singleton"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_eq_reverse_prod"}
      ],
      "representation": {
        "objects": "单位矩阵使用 mathlib 的 1，并给出 Kronecker 条目公式。",
        "parameters": "列表 [M¹,...,Mⁿ] 按步骤执行顺序排列。",
        "quantifiers": "任意有限列表，包括空列表和单元素列表。",
        "conclusion": "matrixProduct []=1；matrixProduct [M¹,...,Mⁿ]=Mⁿ*...*M¹，证明等于 reverse.prod。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.composite_domain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_eq_frozen"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.intermediate"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.intermediate_zero"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.intermediate_cons_succ"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.intermediate_step"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.intermediate_final"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.intermediate_legal"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.Step"}
      ],
      "representation": {
        "objects": "ps=[φ₁,...,φₖ]；chain ps 是执行该列表所得算子。Step 仅存一个算子与一个矩阵。",
        "parameters": "intermediate ps U n 是前 n 步复合对 U 的精确像，正文 U_m 对应 n=m-1。",
        "quantifiers": "递推公式对 n<ps.length 成立；由 U⊆dom(chain ps) 推出每个实际输入域的合法性。",
        "conclusion": "初域等于 U，后一域等于该步作用于前一域的像；最终域是全复合像。chain ps=冻结 OperatorChain ps.reverse。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.AllPositive"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.HasZero"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.one_step_path"}
      ],
      "representation": {
        "objects": "正长度矩阵列表表示为 M::Ms，长度 n=Ms.length+1；IndexPath I Ms.length=Fin Ms.length→I。",
        "parameters": "外部参数 i,j 是 k₀,kₙ；p(r) 是 k_{r+1}。",
        "quantifiers": "AllPositive 逐边递归取合取；HasZero 逐边递归取析取，分别等价于所有层严格正和存在零层。",
        "conclusion": "首边为 M (p 0) i，递归转到剩余路径；单步时直接检验 M j i，且唯一中间路径是空函数。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.singleton_lip"}
      ],
      "representation": {
        "objects": "单分量规范上的全域 Lip 证书。",
        "parameters": "保留有限非空 I 和每个 d_i 的 ExtendedPseudoMetric；Subsingleton I 加指定 i 表达 I={i}。",
        "quantifiers": "任意 x,y∈dom φ。",
        "conclusion": "有限和等于唯一项，得到 d_i(φx,φy)≤L_{i→i} d_i(x,y)。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_antitone"}
      ],
      "representation": {
        "objects": "受限 Lip 矩阵族的集合包含。",
        "parameters": "规范空间参数 hd、有限非空 I、U⊆V⊆dom φ。",
        "quantifiers": "所有在 V 上合法的矩阵，以及 U 内所有点对和输出分量。",
        "conclusion": "LipMatricesOn d φ V ⊆ LipMatricesOn d φ U。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_comp"}
      ],
      "representation": {
        "objects": "φ=φ₁、ψ=φ₂；ψ*φ 是冻结算子乘法，即 ψ∘φ。",
        "parameters": "规范空间 hd、有限非空 I、U⊆dom(ψ*φ)，第一步证书在 U 上，第二步在精确像 φ.func '' U 上。",
        "quantifiers": "U 内任意点对、所有输出分量。",
        "conclusion": "L₂*L₁ 是全两步复合在 U 上的合法 Lip 矩阵。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.colip_antitone"}
      ],
      "representation": {
        "objects": "受限 co-Lip 矩阵族的集合包含。",
        "parameters": "规范空间 hd、有限非空 I、U.Nonempty 和 U⊆V⊆dom φ。",
        "quantifiers": "所有在 V 上合法的 co-Lip 矩阵。",
        "conclusion": "CoLipMatricesOn d φ V ⊆ CoLipMatricesOn d φ U，目标证书保留 U 非空性。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.colip_entry_zero"}
      ],
      "representation": {
        "objects": "全域 co-Lip 矩阵 K 的指定输入/输出条目。",
        "parameters": "规范空间 hd、有限非空 I、K 在 dom φ 上合法，x,y∈dom φ，输出 d_j 为零且输入 d_i>0。",
        "quantifiers": "任意 K、见证点对 x,y 和分量 i,j。",
        "conclusion": "K j i=0；先从非负有限和抽取该项，再用 ENNReal 无零因子性。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.colip_comp"}
      ],
      "representation": {
        "objects": "两步算子 ψ*φ 和下界矩阵 K₂*K₁。",
        "parameters": "规范空间 hd、有限非空 I、U⊆dom(ψ*φ)，两个证书分别在 U 和精确像 φ.func '' U 上。",
        "quantifiers": "U 内所有点对和所有输出分量；两个证书均含非空性。",
        "conclusion": "乘积是复合在 U 上的 co-Lip 矩阵，非空性由第一步证书取得。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_lip"}
      ],
      "representation": {
        "objects": "算子 1 是冻结恒等算子，矩阵 1 是单位矩阵。",
        "parameters": "规范空间 hd、有限非空 I、U⊆dom(id)。",
        "quantifiers": "对任意 U 成立，因而包含正文指定的所有非空 U。",
        "conclusion": "单位矩阵是恒等算子的受限 Lip 证书；结合空链和空矩阵乘积定义即为零步结论。"
      },
      "dependencies": ["CH02-D01", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_colip"}
      ],
      "representation": {
        "objects": "恒等算子和单位矩阵。",
        "parameters": "规范空间 hd、有限非空 I、U.Nonempty、U⊆dom(id)。",
        "quantifiers": "任意这样的 U、U 内所有点对和分量。",
        "conclusion": "单位矩阵是恒等算子在 U 上的 co-Lip 证书，含非空性。"
      },
      "dependencies": ["CH02-D02", "CH02-D04"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.matrixProduct_pos_iff"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.one_step_path"}
      ],
      "representation": {
        "objects": "任意非空矩阵序列 M::Ms；有限 I，条目允许 ∞。",
        "parameters": "端点 i,j 任意；列表长度 n=Ms.length+1，对应正文 n≥1。",
        "quantifiers": "存在 p : Fin (n-1)→I，其 AllPositive 逐边要求所有 n 个条目严格正。",
        "conclusion": "matrixProduct (M::Ms) j i>0 当且仅当存在全正路径；Ms=[] 时已证明唯一空路径和单条目条件。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_restrict"}
      ],
      "representation": {
        "objects": "全域 Lip 矩阵族和受限族。",
        "parameters": "规范空间 hd、有限非空 I、U⊆dom φ。",
        "quantifiers": "任意全域合法矩阵。",
        "conclusion": "LipMatrices d φ ⊆ LipMatricesOn d φ U，由反单调定理取 V=dom φ。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.colip_restrict"}
      ],
      "representation": {
        "objects": "全域和受限 co-Lip 矩阵族。",
        "parameters": "规范空间 hd、有限非空 I、U.Nonempty、U⊆dom φ。",
        "quantifiers": "任意在 dom φ 上合法的 co-Lip 矩阵。",
        "conclusion": "CoLipMatricesOn d φ (dom φ) ⊆ CoLipMatricesOn d φ U。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_lip"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.finite_lip"}
      ],
      "representation": {
        "objects": "ss=[(φ₁,L¹),...,(φₖ,Lᵏ)]，两投影分别给出算子列表和矩阵列表。",
        "parameters": "规范空间 hd、有限非空 I、ss≠[]、U⊆dom(chain (ss.map fst))。",
        "quantifiers": "唯一证书前提为 ∀n<k，第 n 步在 intermediate (ss.map fst) U n 上具有所选 Lip 证书。",
        "conclusion": "归纳构造全链证书，矩阵为 Lᵏ*...*L¹；chain_lip 还包含空链归纳基。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D04",
        "CH02-D05",
        "CH02-P04",
        "CH02-P11"
      ]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_colip"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.finite_colip"}
      ],
      "representation": {
        "objects": "ss=[(φ₁,K¹),...,(φₖ,Kᵏ)]，每步数据仅含算子与所选矩阵。",
        "parameters": "规范空间 hd、有限非空 I、ss≠[]、U⊆dom(全链)。",
        "quantifiers": "对所有 n<k，给出第 n 步在精确实际输入域上的 co-Lip 证书；初域非空由首步证书推出。",
        "conclusion": "从逐步证书归纳得到 Kᵏ*...*K¹ 的全链 co-Lip 证书，无额外全链界前提。"
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D04",
        "CH02-D05",
        "CH02-P08",
        "CH02-P12"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.hasZero_iff_not_allPositive"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.matrixProduct_zero_iff"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.one_step_path"}
      ],
      "representation": {
        "objects": "任意有限非空矩阵序列 M::Ms，乘积为执行顺序的逆序相乘。",
        "parameters": "有限 I、任意端点 i,j，允许零和 ∞ 条目。",
        "quantifiers": "对每个 p : Fin Ms.length→I，HasZero 表示沿其 n=Ms.length+1 个单步条目存在零因子。",
        "conclusion": "乘积的 j,i 条目为零当且仅当每条路径含零因子；由已证正值判据和逐边逻辑等价推出，明确覆盖 n=1。"
      },
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06",
        "CH02-P14"
      ]
    }
  ]
}
```