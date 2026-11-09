全部 20 项已完成，并通过 Lean 4.29.1 离线构建及公理审计；仅依赖允许的三项逻辑公理。

数学来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下为新增形式化源码，直接导入附件冻结模块。

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "lch02"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "Frozen"
roots = ["formal_oet.vol_01.ch_01_foundations.gauge_space", "formal_oet.vol_01.ch_01_foundations.operator_space"]

[[lean_lib]]
name = "LCH02"
roots = ["LCH02.MatrixBounds", "LCH02.Finite", "LCH02.Paths"]

[[lean_lib]]
name = "Main"
```

```lean filename=LCH02/MatrixBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-
Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, §2.1, https://glenzli.com/books/oet/, CC BY 4.0.
ORCID: https://orcid.org/0009-0006-6536-3453.
This file is a new Lean formalization of the selected obligations.
-/

namespace LCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

variable {X I : Type} {bot : X} [Fintype I]

/-- The arrow i → j is stored in row j, column i. -/
def channel (M : BoundMatrix I) (i j : I) : ENNReal := M j i

theorem channel_mul (B A : BoundMatrix I) (i j : I) :
    channel (B * A) i j = ∑ k, channel B k j * channel A i k := rfl

/-- Chronological input order: [M₁,...,Mₙ] has product Mₙ ⋯ M₁. -/
def matrixProduct [DecidableEq I] (Ms : List (BoundMatrix I)) : BoundMatrix I :=
  Ms.reverse.prod

@[simp] theorem matrixProduct_nil [DecidableEq I] :
    matrixProduct ([] : List (BoundMatrix I)) = 1 := rfl

@[simp] theorem matrixProduct_cons [DecidableEq I] (M : BoundMatrix I)
    (Ms : List (BoundMatrix I)) :
    matrixProduct (M :: Ms) = matrixProduct Ms * M := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

@[simp] theorem matrixProduct_singleton [DecidableEq I] (M : BoundMatrix I) :
    matrixProduct [M] = M := by simp

def LipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def lipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) := {L | LipOn d φ U L}

def lipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot) :
    Set (BoundMatrix I) := lipMatricesOn d φ (dom φ)

def CoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def coLipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (BoundMatrix I) := {K | CoLipOn d φ U K}

theorem lip_single_component [Unique I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (L : BoundMatrix I) (i : I) :
    LipOn d φ U L ↔ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hs (f : I → ENNReal) : ∑ k, f k = f i := by
    simpa only [Subsingleton.elim (default : I) i] using Fintype.sum_unique f
  constructor
  · rintro ⟨hU, hL⟩
    exact ⟨hU, fun x hx y hy => by simpa only [hs] using hL x hx y hy i⟩
  · rintro ⟨hU, hL⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    simpa only [hs, Subsingleton.elim j i] using hL x hx y hy

theorem global_lip_single_component [Unique I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : BoundMatrix I) (i : I) :
    L ∈ lipMatrices d φ ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  change LipOn d φ (dom φ) L ↔ _
  simpa using lip_single_component d φ (dom φ) L i

theorem lip_antitone (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) :
    lipMatricesOn d φ V ⊆ lipMatricesOn d φ U := by
  rintro L ⟨hV, hL⟩
  exact ⟨hUV.trans hV, fun x hx y hy j => hL x (hUV hx) y (hUV hy) j⟩

theorem lip_restrict (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom φ) :
    lipMatrices d φ ⊆ lipMatricesOn d φ U := lip_antitone d φ hU

theorem coLip_antitone (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U V : Set X} (hU : U.Nonempty) (hUV : U ⊆ V) :
    coLipMatricesOn d φ V ⊆ coLipMatricesOn d φ U := by
  rintro K ⟨_, hV, hK⟩
  exact ⟨hU, hUV.trans hV, fun x hx y hy j => hK x (hUV hx) y (hUV hy) j⟩

theorem coLip_restrict (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U : Set X} (hU : U.Nonempty) (hdom : U ⊆ dom φ) :
    coLipMatricesOn d φ (dom φ) ⊆ coLipMatricesOn d φ U :=
  coLip_antitone d φ hU hdom

theorem composition_domains (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) :
    U ⊆ dom φ₁ ∧ operator_image φ₁ U ⊆ dom φ₂ := by
  constructor
  · intro x hx heq
    apply hU hx
    change φ₂.func (φ₁.func x) = bot
    rw [heq, φ₂.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem matrix_action_mul (B A : BoundMatrix I) (v : I → ENNReal) (j : I) :
    (∑ i, (B * A) j i * v i) = ∑ k, B j k * (∑ i, A k i * v i) := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lip_comp (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    {U : Set X} {L₁ L₂ : BoundMatrix I} (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : LipOn d φ₁ U L₁) (h₂ : LipOn d φ₂ (operator_image φ₁ U) L₂) :
    LipOn d (φ₂ * φ₁) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) ≤ _
  calc
    _ ≤ ∑ k, L₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, L₂ j k * (∑ i, L₁ k i * d i x y) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2 x hx y hy k) _
    _ = _ := (matrix_action_mul L₂ L₁ (fun i => d i x y) j).symm

theorem coLip_comp (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    {U : Set X} {K₁ K₂ : BoundMatrix I} (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : CoLipOn d φ₁ U K₁) (h₂ : CoLipOn d φ₂ (operator_image φ₁ U) K₂) :
    CoLipOn d (φ₂ * φ₁) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y))
  calc
    _ = ∑ k, K₂ j k * (∑ i, K₁ k i * d i x y) :=
      matrix_action_mul K₂ K₁ (fun i => d i x y) j
    _ ≤ ∑ k, K₂ j k * d k (φ₁.func x) (φ₁.func y) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2.2 x hx y hy k) _
    _ ≤ _ := h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem coLip_entry_zero (d : I → X → X → ENNReal) (φ : Operator X bot)
    {K : BoundMatrix I} (hK : CoLipOn d φ (dom φ) K)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K j i = 0 := by
  have hterm : K j i * d i x y ≤ 0 := calc
    _ ≤ ∑ k, K j k * d k x y :=
      Finset.single_le_sum (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
    _ = 0 := hout
  exact (mul_eq_zero.mp (le_antisymm hterm (zero_le _))).resolve_right (ne_of_gt hin)

theorem identity_lip [DecidableEq I] (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (1 : Operator X bot)) : LipOn d (1 : Operator X bot) U 1 := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i, (1 : BoundMatrix I) j i * d i x y
  simp [Matrix.one_apply]

theorem identity_coLip [DecidableEq I] (d : I → X → X → ENNReal) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X bot)) :
    CoLipOn d (1 : Operator X bot) U 1 := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, (1 : BoundMatrix I) j i * d i x y) ≤ d j x y
  simp [Matrix.one_apply]

end
end LCH02
```

```lean filename=LCH02/Finite.lean
import LCH02.MatrixBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]

/-- Operators are listed in order of application. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: tail => chain tail * φ

theorem chain_eq_frozen (φs : List (Operator X bot)) :
    chain φs = OperatorChain φs.reverse := by
  rw [operator_chain_eq_prod]
  induction φs with
  | nil => rfl
  | cons φ tail ih => simp [chain, List.reverse_cons, List.prod_append, ih]

/-- m = 0 represents the textbook's U₁; m steps have already acted. -/
def actualDomain (φs : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  operator_image (chain (φs.take m)) U

@[simp] theorem actualDomain_zero (φs : List (Operator X bot)) (U : Set X) :
    actualDomain φs U 0 = U := by
  change id '' U = U
  exact Set.image_id U

@[simp] theorem actualDomain_succ (φ : Operator X bot) (tail : List (Operator X bot))
    (U : Set X) (m : ℕ) :
    actualDomain (φ :: tail) U (m + 1) = actualDomain tail (operator_image φ U) m := by
  change ((chain (tail.take m)).func ∘ φ.func) '' U =
    (chain (tail.take m)).func '' (φ.func '' U)
  exact (Set.image_image (chain (tail.take m)).func φ.func U).symm

theorem actualDomain_legal (φs : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain φs)) (m : ℕ) (hm : m < φs.length) :
    actualDomain φs U m ⊆ dom φs[m] := by
  induction φs generalizing U m with
  | nil => simp at hm
  | cons φ tail ih =>
      have hparts := composition_domains φ (chain tail) hU
      cases m with
      | zero => simpa using hparts.1
      | succ m =>
          simpa using ih hparts.2 m (Nat.lt_of_succ_lt_succ hm)

/-- Only single-step assertions appear here, on the exact recursive image domains. -/
def Stepwise (P : Operator X bot → Set X → BoundMatrix I → Prop) :
    List (Operator X bot × BoundMatrix I) → Set X → Prop
  | [], _ => True
  | s :: tail, U => P s.1 U s.2 ∧ Stepwise P tail (operator_image s.1 U)

omit [Fintype I] [DecidableEq I] in
theorem stepwise_iff_actualDomains
    (P : Operator X bot → Set X → BoundMatrix I → Prop)
    (steps : List (Operator X bot × BoundMatrix I)) (U : Set X) :
    Stepwise P steps U ↔ ∀ m (hm : m < steps.length),
      P steps[m].1 (actualDomain (steps.map Prod.fst) U m) steps[m].2 := by
  induction steps generalizing U with
  | nil => simp [Stepwise]
  | cons s tail ih =>
      constructor
      · intro hs m hm
        cases m with
        | zero => simpa using hs.1
        | succ m =>
            simpa using (ih (operator_image s.1 U)).mp hs.2 m (Nat.lt_of_succ_lt_succ hm)
      · intro h
        refine ⟨?_, (ih (operator_image s.1 U)).mpr ?_⟩
        · simpa using h 0 (by simp)
        · intro m hm
          simpa using h (m + 1) (Nat.succ_lt_succ hm)

theorem finite_lip (d : I → X → X → ENNReal)
    (steps : List (Operator X bot × BoundMatrix I)) {U : Set X}
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hsteps : Stepwise (LipOn d) steps U) :
    LipOn d (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact identity_lip d hU
  | cons s tail ih =>
      rcases s with ⟨φ, L⟩
      have htail := (composition_domains φ (chain (tail.map Prod.fst)) hU).2
      have h := lip_comp d φ (chain (tail.map Prod.fst)) hU hsteps.1
        (ih htail hsteps.2)
      simpa [chain] using h

theorem finite_coLip (d : I → X → X → ENNReal)
    (steps : List (Operator X bot × BoundMatrix I)) {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hsteps : Stepwise (CoLipOn d) steps U) :
    CoLipOn d (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact identity_coLip d hne hU
  | cons s tail ih =>
      rcases s with ⟨φ, K⟩
      have htail := (composition_domains φ (chain (tail.map Prod.fst)) hU).2
      have h := coLip_comp d φ (chain (tail.map Prod.fst)) hU hsteps.1
        (ih (hne.image φ.func) htail hsteps.2)
      simpa [chain] using h

theorem finite_coLip_positive (d : I → X → X → ENNReal)
    (steps : List (Operator X bot × BoundMatrix I)) (hpos : steps ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hsteps : Stepwise (CoLipOn d) steps U) :
    CoLipOn d (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  cases steps with
  | nil => exact False.elim (hpos rfl)
  | cons s tail => exact finite_coLip d (s :: tail) hsteps.1.1 hU hsteps

end
end LCH02
```

```lean filename=LCH02/Paths.lean
import LCH02.MatrixBounds

namespace LCH02

open scoped BigOperators

noncomputable section

variable {I : Type}

/-- A path has fixed endpoints and one arrow per matrix, in chronological order.
For a singleton matrix list it has no free intermediate vertex. -/
inductive IndexPath : List (BoundMatrix I) → I → I → Type
  | nil (i : I) : IndexPath [] i i
  | cons {M : BoundMatrix I} {Ms : List (BoundMatrix I)} {i k j : I}
      (tail : IndexPath Ms k j) : IndexPath (M :: Ms) i j

def singletonPathEquiv (M : BoundMatrix I) (i j : I) : IndexPath [M] i j ≃ Unit where
  toFun _ := ()
  invFun _ := IndexPath.cons (IndexPath.nil j)
  left_inv p := by
    cases p with
    | cons tail => cases tail; rfl
  right_inv u := by cases u; rfl

def AllPositive : {Ms : List (BoundMatrix I)} → {i j : I} → IndexPath Ms i j → Prop
  | _, _, _, .nil _ => True
  | _, _, _, @IndexPath.cons _ M _ i k _ tail => 0 < M k i ∧ AllPositive tail

def ZeroFactor : {Ms : List (BoundMatrix I)} → {i j : I} → IndexPath Ms i j → Prop
  | _, _, _, .nil _ => False
  | _, _, _, @IndexPath.cons _ M _ i k _ tail => M k i = 0 ∨ ZeroFactor tail

theorem not_allPositive_iff_zeroFactor {Ms : List (BoundMatrix I)} {i j : I}
    (p : IndexPath Ms i j) : ¬ AllPositive p ↔ ZeroFactor p := by
  classical
  induction p with
  | nil => simp [AllPositive, ZeroFactor]
  | cons tail ih =>
      simp only [AllPositive, ZeroFactor, not_and_or, pos_iff_ne_zero, not_not, ih]

theorem matrixProduct_pos_iff [Fintype I] [DecidableEq I]
    (Ms : List (BoundMatrix I)) (i j : I) :
    0 < matrixProduct Ms j i ↔ ∃ p : IndexPath Ms i j, AllPositive p := by
  induction Ms generalizing i j with
  | nil =>
      constructor
      · intro h
        simp only [matrixProduct_nil, Matrix.one_apply] at h
        split_ifs at h with heq
        · subst j
          exact ⟨IndexPath.nil i, trivial⟩
        · exact (lt_irrefl 0 h).elim
      · rintro ⟨p, _⟩
        cases p
        simp
  | cons M Ms ih =>
      rw [matrixProduct_cons, Matrix.mul_apply]
      constructor
      · intro h
        obtain ⟨k, _, hk⟩ := Finset.sum_pos_iff.mp h
        obtain ⟨htail, hentry⟩ := ENNReal.mul_pos_iff.mp hk
        obtain ⟨p, hp⟩ := (ih k j).mp htail
        exact ⟨IndexPath.cons p, hentry, hp⟩
      · rintro ⟨p, hp⟩
        cases p with
        | @cons _ _ _ k _ tail =>
            apply Finset.sum_pos_iff.mpr
            exact ⟨k, Finset.mem_univ k,
              ENNReal.mul_pos_iff.mpr ⟨(ih k j).mpr ⟨tail, hp.2⟩, hp.1⟩⟩

theorem matrixProduct_zero_iff [Fintype I] [DecidableEq I]
    (Ms : List (BoundMatrix I)) (i j : I) :
    matrixProduct Ms j i = 0 ↔ ∀ p : IndexPath Ms i j, ZeroFactor p := by
  constructor
  · intro hz p
    apply (not_allPositive_iff_zeroFactor p).mp
    intro hp
    have hpos := (matrixProduct_pos_iff Ms i j).mpr ⟨p, hp⟩
    simp only [hz, lt_self_iff_false] at hpos
  · intro hz
    by_contra hne
    obtain ⟨p, hp⟩ := (matrixProduct_pos_iff Ms i j).mp (pos_iff_ne_zero.mpr hne)
    exact ((not_allPositive_iff_zeroFactor p).mpr (hz p)) hp

/-- Explicit length-one boundary cases. -/
theorem singleton_path_pos [Fintype I] [DecidableEq I] (M : BoundMatrix I) (i j : I) :
    (∃ p : IndexPath [M] i j, AllPositive p) ↔ 0 < M j i := by
  simpa using (matrixProduct_pos_iff [M] i j).symm

theorem singleton_path_zero [Fintype I] [DecidableEq I] (M : BoundMatrix I) (i j : I) :
    (∀ p : IndexPath [M] i j, ZeroFactor p) ↔ M j i = 0 := by
  simpa using (matrixProduct_zero_iff [M] i j).symm

end
end LCH02
```

```lean filename=Main.lean
import LCH02.MatrixBounds
import LCH02.Finite
import LCH02.Paths
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
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.LipOn"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lipMatricesOn"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lipMatrices"}
      ],
      "representation": {
        "objects": "Operator、dom、operator_image 直接使用冻结模块；d 为正文的分量规范族，距离取 ENNReal。",
        "parameters": "X、bot、有限指标类型 I、d、φ、U、L；这些代数定义及结论对任意 d 有效，因而适用于正文有限非空扩展规范空间。",
        "quantifiers": "LipOn 包含 U⊆dom φ，并对所有 x∈U、y∈U 和输出 j 要求上界。",
        "conclusion": "lipMatricesOn 是合法受限矩阵集合；lipMatrices 取 U=dom φ，恰为全域证书族。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.CoLipOn"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.coLipMatricesOn"}
      ],
      "representation": {
        "objects": "CoLipOn 为受限 co-Lip 谓词，coLipMatricesOn 为其矩阵集合。",
        "parameters": "d、φ、U、K 与正文相同。",
        "quantifiers": "显式要求 U.Nonempty、U⊆dom φ，且对所有 x,y∈U 和所有输出分量 j 成立。",
        "conclusion": "矩阵加权输入距离之和不大于输出距离；非空性没有省略。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.BoundMatrix"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.channel"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.channel_mul"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrix_action_mul"}
      ],
      "representation": {
        "objects": "BoundMatrix I = Matrix I I ENNReal，使用 mathlib 的标准矩阵乘法。",
        "parameters": "channel M i j = M j i；输入为列，输出为行。",
        "quantifiers": "对任意 A、B 和 i、j，乘积通道等于对全部中间分量 k 的有限和。",
        "conclusion": "channel (B*A) i j = Σk channel B k j * channel A i k；matrix_action_mul 给出交换求和后的作用公式。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct_nil"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct_cons"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct_singleton"}
      ],
      "representation": {
        "objects": "单位矩阵为标准 Matrix 的 1。",
        "parameters": "列表按作用先后存放 [M¹,...,Mⁿ]；DecidableEq I 仅用于单位矩阵，可经典获得。",
        "quantifiers": "matrixProduct 定义于任意有限列表，包含空列表和单元素列表。",
        "conclusion": "逆序列表乘积为 Mⁿ⋯M¹；空乘积为 1，cons 公式为 product(tail)*head。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Finite.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.chain_eq_frozen"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.actualDomain"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.actualDomain_zero"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.actualDomain_succ"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.actualDomain_legal"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.Stepwise"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.stepwise_iff_actualDomains"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.composition_domains"}
      ],
      "representation": {
        "objects": "chain [φ₁,...,φₖ]=φₖ⋯φ₁，等于冻结 OperatorChain 在逆序列表上的值。",
        "parameters": "actualDomain φs U m 是前 m 步复合作用于 U 的精确像，即正文 U_(m+1)。",
        "quantifiers": "U⊆dom(chain φs) 时，每个 m<length 的实际输入域均包含于第 m 个算子的定义域。",
        "conclusion": "零步域为 U，后续域逐步取像；stepwise_iff_actualDomains 证明递归单步条件等价于在每个实际输入域上的逐项条件。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.singletonPathEquiv"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.AllPositive"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.ZeroFactor"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.not_allPositive_iff_zeroFactor"}
      ],
      "representation": {
        "objects": "IndexPath Ms i j 是固定起点 i、终点 j、每个矩阵对应一条边的有限归纳路径。",
        "parameters": "cons 选取下一分量 k，nil 固定末点；长度 n≥1 时自由选择恰为 n−1 个中间指标。",
        "quantifiers": "AllPositive 递归要求所有边 M^(m)_(k_m,k_(m−1))>0；ZeroFactor 表示至少一条边为零。",
        "conclusion": "singletonPathEquiv 证明长度 1 的路径类型等价于 Unit，即唯一空中间序列；含零因子等价于不全正。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_single_component"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.global_lip_single_component"}
      ],
      "representation": {
        "objects": "单指标集用 Unique I 表示；i 是其唯一元素。",
        "parameters": "任意 φ、L、d；另提供任意受限 U 的同形版本。",
        "quantifiers": "全域版本对所有 x,y∈dom φ，受限版本对所有 x,y∈U。",
        "conclusion": "合法 Lip 条件当且仅当标量距离界 d_i(φx,φy)≤L_ii*d_i(x,y)。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_antitone"}
      ],
      "representation": {
        "objects": "lipMatricesOn 的集合包含关系。",
        "parameters": "固定 d、φ，给定 U⊆V；V⊆dom φ 已包含在 V 上的合法证书中。",
        "quantifiers": "任意 V 上的合法 L 均可限制到 U，所有 U 内点对仍满足原不等式。",
        "conclusion": "lipMatricesOn d φ V ⊆ lipMatricesOn d φ U。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_comp"}
      ],
      "representation": {
        "objects": "复合为 φ₂*φ₁，精确中间域为 operator_image φ₁ U。",
        "parameters": "U⊆dom(φ₂*φ₁)，L₁ 在 U 上合法，L₂ 在 φ₁(U) 上合法。",
        "quantifiers": "对任意有限指标族、任意输入点对及所有输出分量。",
        "conclusion": "L₂*L₁ 是复合在 U 上的合法 Lip 矩阵，包含 U 的定义域条件。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.coLip_antitone"}
      ],
      "representation": {
        "objects": "coLipMatricesOn 的集合包含关系。",
        "parameters": "固定 d、φ，假设 U.Nonempty 和 U⊆V；V 的定义域条件来自其证书。",
        "quantifiers": "任意 V 上合法 K 及任意 U 内点对。",
        "conclusion": "V 上证书属于 U 上证书族，且保留 U 非空。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.coLip_entry_zero"}
      ],
      "representation": {
        "objects": "全域 co-Lip 矩阵 K 的通道 i→j，即 K j i。",
        "parameters": "K 在 dom φ 上合法，x,y∈dom φ，输出 j 距离为零且输入 i 距离严格正。",
        "quantifiers": "对任意满足上述点对条件的 i、j 和任意全域 K。",
        "conclusion": "K j i=0；证明使用单项≤有限和与 ENNReal 无零因子性质。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.coLip_comp"}
      ],
      "representation": {
        "objects": "复合 φ₂*φ₁，中间域严格为 φ₁(U)。",
        "parameters": "U⊆dom(φ₂*φ₁)，K₁ 在 U 上合法，K₂ 在 operator_image φ₁ U 上合法。",
        "quantifiers": "对所有 U 内点对及全部输出分量。",
        "conclusion": "K₂*K₁ 给出复合的 co-Lip 下界；返回的 CoLipOn 同时包含 U 非空和定义域条件。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.identity_lip"}
      ],
      "representation": {
        "objects": "算子 1 为冻结幺半群的恒等算子；矩阵 1 为单位矩阵。",
        "parameters": "任意 U⊆dom id；结论还允许 U 为空，覆盖正文非空情形。",
        "quantifiers": "对任意 x,y∈U 和 j，单位矩阵加权和恰为 d_j(x,y)。",
        "conclusion": "LipOn d id U 1，即零步单位 Lip 证书。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.identity_coLip"}
      ],
      "representation": {
        "objects": "恒等算子及单位矩阵均采用标准幺半群的 1。",
        "parameters": "显式假设 U.Nonempty 和 U⊆dom id。",
        "quantifiers": "对全部 U 内点对及所有分量，单位矩阵作用等于原距离。",
        "conclusion": "CoLipOn d id U 1，完整包含非空性。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.matrixProduct_pos_iff"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.singleton_path_pos"}
      ],
      "representation": {
        "objects": "有序矩阵列表 Ms 及固定输入 i、输出 j 的 IndexPath。",
        "parameters": "任意有限指标类型和任意 ENNReal 矩阵列表，包含所有正长度 n；定理也处理空乘积。",
        "quantifiers": "乘积条目严格正，当且仅当存在一条所有边严格正的路径。",
        "conclusion": "matrixProduct Ms j i>0 ↔ ∃p, AllPositive p；singleton_path_pos 明确给出 n=1 时的单条目条件。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_restrict"}
      ],
      "representation": {
        "objects": "全域 lipMatrices 与受限 lipMatricesOn。",
        "parameters": "任意 U⊆dom φ。",
        "quantifiers": "每个全域合法 L 都属于 U 上的合法矩阵族。",
        "conclusion": "lipMatrices d φ ⊆ lipMatricesOn d φ U。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.coLip_restrict"}
      ],
      "representation": {
        "objects": "dom φ 上的 co-Lip 证书族与 U 上的证书族。",
        "parameters": "显式要求 U.Nonempty 与 U⊆dom φ。",
        "quantifiers": "每个全域合法 K 均可限制到 U。",
        "conclusion": "coLipMatricesOn d φ (dom φ) ⊆ coLipMatricesOn d φ U。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Finite.lean", "name": "LCH02.finite_lip"}
      ],
      "representation": {
        "objects": "steps 按作用先后存放算子与单步 Lip 矩阵的配对列表。",
        "parameters": "U⊆dom(chain(map fst steps))；Stepwise(LipOn d) 只要求各步在递归实际输入域的局部证书。",
        "quantifiers": "任意有限列表，特别包含正文所有 k≥1；stepwise_iff_actualDomains 给出与逐项量化的等价。",
        "conclusion": "由单步证书归纳建立全链 LipOn，矩阵恰为 Lᵏ⋯L¹；没有把全链界放入前提。"
      },
      "dependencies": [
        "CH02-D01", "CH02-D03", "CH02-D04",
        "CH02-D05", "CH02-P04", "CH02-P11"
      ]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Finite.lean", "name": "LCH02.finite_coLip"},
        {"file": "LCH02/Finite.lean", "name": "LCH02.finite_coLip_positive"}
      ],
      "representation": {
        "objects": "steps 按作用先后存放算子与单步 co-Lip 矩阵。",
        "parameters": "positive 版本要求 steps≠[]、U⊆全链定义域及逐步实际域上的 CoLipOn。",
        "quantifiers": "对任意正长度链；U 非空从第一步证书推出，各中间域为精确像。",
        "conclusion": "从单步下界推出全链 CoLipOn，矩阵为 Kᵏ⋯K¹；辅助 finite_coLip 同时处理显式非空 U 的零步情形。"
      },
      "dependencies": [
        "CH02-D02", "CH02-D03", "CH02-D04",
        "CH02-D05", "CH02-P08", "CH02-P12"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.matrixProduct_zero_iff"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.singleton_path_zero"}
      ],
      "representation": {
        "objects": "有序 ENNReal 矩阵乘积及固定起终点的全部有限路径。",
        "parameters": "任意有限矩阵列表，特别包括所有 n≥1。",
        "quantifiers": "乘积条目为零，当且仅当每条路径都至少含一个零因子。",
        "conclusion": "matrixProduct Ms j i=0 ↔ ∀p, ZeroFactor p；n=1 明确退化为 M j i=0。证明由正值判据和非全正等价含零得到。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```