全部 20 项完成；指定版本下 Lake 构建通过，42 个声明的公理依赖仅含允许的三项。冻结模块沿用附件原件。

数学内容来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，CC BY 4.0。以下为新增形式化源码。

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

@[default_target] lean_lib Main
```

```lean filename=LCH02/Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-!
Formalization of the selected statements of OET, Volume I, Chapter 2.
Source: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
https://glenzli.com/books/oet/, DOI 10.5281/zenodo.21457931, CC BY 4.0.
The mathematical content is from that source; this Lean formalization is new.
-/

namespace LCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

section Matrices

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Input `i`, output `j` is the entry in row `j`, column `i`. -/
def channel (M : BoundMatrix I) (i j : I) : ENNReal := M j i

omit [DecidableEq I] in
theorem channel_mul (M₂ M₁ : BoundMatrix I) (i j : I) :
    channel (M₂ * M₁) i j = ∑ k, channel M₂ k j * channel M₁ i k := rfl

/-- The list is in chronological order: the first matrix acts first. -/
def orderedProduct : List (BoundMatrix I) → BoundMatrix I
  | [] => 1
  | M :: Ms => orderedProduct Ms * M

theorem orderedProduct_eq_reverse_prod (Ms : List (BoundMatrix I)) :
    orderedProduct Ms = Ms.reverse.prod := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih => simp [orderedProduct, List.reverse_cons, ih]

@[simp] theorem orderedProduct_nil :
    orderedProduct ([] : List (BoundMatrix I)) = 1 := rfl

@[simp] theorem orderedProduct_singleton (M : BoundMatrix I) :
    orderedProduct [M] = M := by simp [orderedProduct]

omit [DecidableEq I] in
theorem matrix_action_mul (B A : BoundMatrix I) (v : I → ENNReal) (j : I) :
    (∑ k, B j k * ∑ i, A k i * v i) = ∑ i, (B * A) j i * v i := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Matrices

section Bounds

variable {X I : Type} {bot : X} [Fintype I]
variable (d : I → X → X → ENNReal)

/-- Membership includes the stipulated restriction to the operator domain. -/
def IsRestrictedLip (φ : Operator X bot) (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def IsLip (φ : Operator X bot) (L : BoundMatrix I) : Prop :=
  IsRestrictedLip d φ (dom φ) L

def lipFamily (φ : Operator X bot) : Set (BoundMatrix I) := {L | IsLip d φ L}

def restrictedLipFamily (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {L | IsRestrictedLip d φ U L}

/-- Nonemptiness is part of the predicate, not an implicit convention. -/
def IsRestrictedCoLip (φ : Operator X bot) (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def restrictedCoLipFamily (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {K | IsRestrictedCoLip d φ U K}

theorem singleton_lip_iff [Unique I] (φ : Operator X bot) (L : BoundMatrix I) (j : I) :
    IsLip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  constructor
  · intro h x hx y hy
    simpa [Finset.univ_unique, ← Unique.eq_default j] using h.2 x hx y hy j
  · intro h
    refine ⟨fun _ hx => hx, ?_⟩
    intro x hx y hy k
    have hk : k = j := Subsingleton.elim _ _
    subst k
    simpa [Finset.univ_unique, ← Unique.eq_default j] using h x hx y hy

theorem restrictedLipFamily_antitone (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) : restrictedLipFamily d φ V ⊆ restrictedLipFamily d φ U := by
  intro L hL
  exact ⟨fun _ hx => hL.1 (hUV hx),
    fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

theorem lipFamily_restrict (φ : Operator X bot) {U : Set X} (hU : U ⊆ dom φ) :
    lipFamily d φ ⊆ restrictedLipFamily d φ U :=
  restrictedLipFamily_antitone d φ hU

theorem restrictedCoLipFamily_antitone (φ : Operator X bot) {U V : Set X}
    (hne : U.Nonempty) (hUV : U ⊆ V) :
    restrictedCoLipFamily d φ V ⊆ restrictedCoLipFamily d φ U := by
  intro K hK
  exact ⟨hne, fun _ hx => hK.2.1 (hUV hx),
    fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

theorem coLipFamily_restrict (φ : Operator X bot) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    restrictedCoLipFamily d φ (dom φ) ⊆ restrictedCoLipFamily d φ U :=
  restrictedCoLipFamily_antitone d φ hne hU

theorem coLip_entry_eq_zero (φ : Operator X bot) (K : BoundMatrix I)
    (hK : IsRestrictedCoLip d φ (dom φ) K)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K j i = 0 := by
  have hterm : K j i * d i x y ≤ 0 := calc
    K j i * d i x y ≤ ∑ k, K j k * d k x y :=
      Finset.single_le_sum (f := fun k => K j k * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
    _ = 0 := hout
  have hz : K j i * d i x y = 0 := le_antisymm hterm (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

/-- The exact intermediate image lies in the second operator's domain. -/
theorem image_subset_dom_of_comp (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) : φ₁.func '' U ⊆ dom φ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU hx

theorem subset_dom_first_of_comp (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) : U ⊆ dom φ₁ := by
  intro x hx heq
  apply hU hx
  change φ₂.func (φ₁.func x) = bot
  rw [heq, φ₂.preserves_bot]

variable [DecidableEq I]

omit [DecidableEq I] in
theorem lip_comp (φ₁ φ₂ : Operator X bot) (U : Set X) (L₁ L₂ : BoundMatrix I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : IsRestrictedLip d φ₁ U L₁)
    (h₂ : IsRestrictedLip d φ₂ (φ₁.func '' U) L₂) :
    IsRestrictedLip d (φ₂ * φ₁) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y)
        ≤ ∑ k, L₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, L₂ j k * ∑ i, L₁ k i * d i x y :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2 x hx y hy k) _
    _ = ∑ i, (L₂ * L₁) j i * d i x y :=
      matrix_action_mul L₂ L₁ (fun i => d i x y) j

omit [DecidableEq I] in
theorem coLip_comp (φ₁ φ₂ : Operator X bot) (U : Set X) (K₁ K₂ : BoundMatrix I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : IsRestrictedCoLip d φ₁ U K₁)
    (h₂ : IsRestrictedCoLip d φ₂ (φ₁.func '' U) K₂) :
    IsRestrictedCoLip d (φ₂ * φ₁) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, (K₂ * K₁) j i * d i x y)
        = ∑ k, K₂ j k * ∑ i, K₁ k i * d i x y :=
      (matrix_action_mul K₂ K₁ (fun i => d i x y) j).symm
    _ ≤ ∑ k, K₂ j k * d k (φ₁.func x) (φ₁.func y) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (h₁.2.2 x hx y hy k) _
    _ ≤ d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y) :=
      h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem identity_lip (U : Set X) (hU : U ⊆ dom (1 : Operator X bot)) :
    IsRestrictedLip d (1 : Operator X bot) U (1 : BoundMatrix I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i, (1 : BoundMatrix I) j i * d i x y
  simp [Matrix.one_apply]

theorem identity_coLip (U : Set X) (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsRestrictedCoLip d (1 : Operator X bot) U (1 : BoundMatrix I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, (1 : BoundMatrix I) j i * d i x y) ≤ d j x y
  simp [Matrix.one_apply]

end Bounds
end
end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.Bounds

namespace LCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- Operators are listed in execution order, so the head acts first. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: fs => chain fs * φ

theorem chain_eq_frozen (fs : List (Operator X bot)) :
    chain fs = OperatorChain fs.reverse := by
  rw [operator_chain_eq_prod]
  induction fs with
  | nil => rfl
  | cons φ fs ih => simp [chain, List.reverse_cons, ih]

/-- Zero-based step `m` has input domain `U_(m+1)` in the text. -/
def actualDomain (fs : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  (chain (fs.take m)).func '' U

@[simp] theorem actualDomain_zero (fs : List (Operator X bot)) (U : Set X) :
    actualDomain fs U 0 = U := by
  change id '' U = U
  simp

theorem actualDomain_cons_succ (φ : Operator X bot) (fs : List (Operator X bot))
    (U : Set X) (m : ℕ) :
    actualDomain (φ :: fs) U (m + 1) = actualDomain fs (φ.func '' U) m := by
  unfold actualDomain
  rw [List.take_succ_cons, chain, Set.image_image]
  rfl

theorem actualDomain_last (fs : List (Operator X bot)) (U : Set X) :
    actualDomain fs U fs.length = (chain fs).func '' U := by
  simp [actualDomain]

theorem actualDomain_subset_dom (fs : List (Operator X bot)) (U : Set X)
    (hU : U ⊆ dom (chain fs)) :
    ∀ m (hm : m < fs.length), actualDomain fs U m ⊆ dom (fs[m]) := by
  induction fs generalizing U with
  | nil => intro m hm; simp at hm
  | cons φ fs ih =>
      intro m hm
      cases m with
      | zero =>
          simpa using subset_dom_first_of_comp φ (chain fs) hU
      | succ m =>
          have ht := image_subset_dom_of_comp φ (chain fs) hU
          simpa only [actualDomain_cons_succ, List.getElem_cons_succ] using
            ih (φ.func '' U) ht m (by simpa using hm)

variable [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)

/-- A list of pairs contains only operators and matrices, without proof fields.
Every hypothesis is a single-step inequality on its exact actual input image. -/
theorem chain_lip (ss : List (Operator X bot × BoundMatrix I)) (U : Set X)
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hstep : ∀ m (hm : m < ss.length),
      IsRestrictedLip d (ss[m]).1 (actualDomain (ss.map Prod.fst) U m) (ss[m]).2) :
    IsRestrictedLip d (chain (ss.map Prod.fst)) U (orderedProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => exact identity_lip d U hU
  | cons s ss ih =>
      have hhead : IsRestrictedLip d s.1 U s.2 := by
        simpa using hstep 0 (by simp)
      have htail : IsRestrictedLip d (chain (ss.map Prod.fst)) (s.1.func '' U)
          (orderedProduct (ss.map Prod.snd)) := by
        apply ih (s.1.func '' U)
          (image_subset_dom_of_comp s.1 (chain (ss.map Prod.fst)) hU)
        intro m hm
        simpa only [List.getElem_cons_succ, List.map_cons, actualDomain_cons_succ] using
          hstep (m + 1) (by simpa using hm)
      exact lip_comp d s.1 (chain (ss.map Prod.fst)) U s.2
        (orderedProduct (ss.map Prod.snd)) hU hhead htail

theorem chain_coLip_of_nonempty (ss : List (Operator X bot × BoundMatrix I))
    (U : Set X) (hne : U.Nonempty) (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hstep : ∀ m (hm : m < ss.length),
      IsRestrictedCoLip d (ss[m]).1 (actualDomain (ss.map Prod.fst) U m) (ss[m]).2) :
    IsRestrictedCoLip d (chain (ss.map Prod.fst)) U (orderedProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => exact identity_coLip d U hne hU
  | cons s ss ih =>
      have hhead : IsRestrictedCoLip d s.1 U s.2 := by
        simpa using hstep 0 (by simp)
      have htail : IsRestrictedCoLip d (chain (ss.map Prod.fst)) (s.1.func '' U)
          (orderedProduct (ss.map Prod.snd)) := by
        apply ih (s.1.func '' U) (hne.image s.1.func)
          (image_subset_dom_of_comp s.1 (chain (ss.map Prod.fst)) hU)
        intro m hm
        simpa only [List.getElem_cons_succ, List.map_cons, actualDomain_cons_succ] using
          hstep (m + 1) (by simpa using hm)
      exact coLip_comp d s.1 (chain (ss.map Prod.fst)) U s.2
        (orderedProduct (ss.map Prod.snd)) hU hhead htail

/-- For a positive length chain, nonemptiness follows from the first co-Lip premise. -/
theorem chain_coLip (ss : List (Operator X bot × BoundMatrix I))
    (hlen : 0 < ss.length) (U : Set X) (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hstep : ∀ m (hm : m < ss.length),
      IsRestrictedCoLip d (ss[m]).1 (actualDomain (ss.map Prod.fst) U m) (ss[m]).2) :
    IsRestrictedCoLip d (chain (ss.map Prod.fst)) U (orderedProduct (ss.map Prod.snd)) := by
  have hne : U.Nonempty := by simpa using (hstep 0 hlen).1
  exact chain_coLip_of_nonempty d ss U hne hU hstep

end
end LCH02
```

```lean filename=LCH02/Paths.lean
import LCH02.Bounds

namespace LCH02

noncomputable section

open scoped BigOperators

/-- A path with `r` intermediate indices. `r = 0` has exactly one empty path. -/
def IndexPath (I : Type) : ℕ → Type
  | 0 => PUnit
  | r + 1 => I × IndexPath I r

variable {I : Type}

/-- The nonempty chronological matrix list is `M :: Ms`.
Each component of the path chooses the next intermediate index. -/
def AllPositivePath : (M : BoundMatrix I) → (Ms : List (BoundMatrix I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => 0 < M j i
  | M, N :: Ns, i, j, p => 0 < M p.1 i ∧ AllPositivePath N Ns p.1 j p.2

def HasZeroFactor : (M : BoundMatrix I) → (Ms : List (BoundMatrix I)) →
    I → I → IndexPath I Ms.length → Prop
  | M, [], i, j, _ => M j i = 0
  | M, N :: Ns, i, j, p => M p.1 i = 0 ∨ HasZeroFactor N Ns p.1 j p.2

theorem positivePath_iff_no_zero (M : BoundMatrix I) (Ms : List (BoundMatrix I))
    (i j : I) (p : IndexPath I Ms.length) :
    AllPositivePath M Ms i j p ↔ ¬ HasZeroFactor M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => simp [AllPositivePath, HasZeroFactor, pos_iff_ne_zero]
  | cons N Ns ih =>
      rcases p with ⟨k, p⟩
      simp only [AllPositivePath, HasZeroFactor, not_or, pos_iff_ne_zero, ih]

variable [Fintype I] [DecidableEq I]

theorem product_pos_iff_path (M : BoundMatrix I) (Ms : List (BoundMatrix I)) (i j : I) :
    0 < orderedProduct (M :: Ms) j i ↔
      ∃ p : IndexPath I Ms.length, AllPositivePath M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => simp [orderedProduct, IndexPath, AllPositivePath]
  | cons N Ns ih =>
      change (0 < ∑ k, orderedProduct (N :: Ns) j k * M k i) ↔ _
      rw [Finset.sum_pos_iff]
      constructor
      · rintro ⟨k, _, hk⟩
        obtain ⟨htail, hfirst⟩ := ENNReal.mul_pos_iff.mp hk
        obtain ⟨p, hp⟩ := (ih N k j).mp htail
        exact ⟨⟨k, p⟩, hfirst, hp⟩
      · rintro ⟨⟨k, p⟩, hfirst, hp⟩
        exact ⟨k, Finset.mem_univ _,
          ENNReal.mul_pos_iff.mpr ⟨(ih N k j).mpr ⟨p, hp⟩, hfirst⟩⟩

theorem product_zero_iff_paths (M : BoundMatrix I) (Ms : List (BoundMatrix I)) (i j : I) :
    orderedProduct (M :: Ms) j i = 0 ↔
      ∀ p : IndexPath I Ms.length, HasZeroFactor M Ms i j p := by
  classical
  have hz : orderedProduct (M :: Ms) j i = 0 ↔
      ¬ 0 < orderedProduct (M :: Ms) j i := by
    simp [pos_iff_ne_zero]
  rw [hz, product_pos_iff_path]
  simp only [not_exists, positivePath_iff_no_zero, not_not]

end
end LCH02
```

```lean filename=Main.lean
import LCH02.Bounds
import LCH02.Chains
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
        {"file": "LCH02/Bounds.lean", "name": "LCH02.IsRestrictedLip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.IsLip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipFamily"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.restrictedLipFamily"}
      ],
      "representation": {
        "objects": "使用冻结 Operator X bot、dom 及 d : I → X → X → ENNReal；I 为 Fintype。代数结论对任意 d 成立，因而直接适用于原文有限非空扩展伪度量族。",
        "parameters": "φ 为算子，U 为子集，L j i 为 L_{i→j}。",
        "quantifiers": "受限谓词包含 U ⊆ dom φ，并对全部 x∈U、y∈U、j∈I 量化。",
        "conclusion": "输出距离 ≤ 有限加权输入距离和；全域取 U=dom φ；证书族为满足相应谓词的矩阵集合。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.IsRestrictedCoLip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.restrictedCoLipFamily"}
      ],
      "representation": {
        "objects": "沿用冻结算子和 ENNReal 分量距离。",
        "parameters": "φ、U、K；K j i 表示 K_{i→j}。",
        "quantifiers": "显式包含 U.Nonempty、U ⊆ dom φ，及所有 x∈U、y∈U、j∈I。",
        "conclusion": "加权输入距离和 ≤ 输出距离；证书族是该谓词对应的集合。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.BoundMatrix"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.channel"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.channel_mul"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.matrix_action_mul"}
      ],
      "representation": {
        "objects": "BoundMatrix I = Matrix I I ENNReal；使用标准矩阵乘法。",
        "parameters": "channel M i j = M j i，输出为行，输入为列。",
        "quantifiers": "对所有矩阵、输入 i、输出 j 以及距离向量 v。",
        "conclusion": "(M₂*M₁) j i = ∑k M₂ j k * M₁ k i；matrix_action_mul 给出有限和的分配及换序。ENNReal 包含 0*∞=0。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.orderedProduct"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.orderedProduct_nil"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.orderedProduct_singleton"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.orderedProduct_eq_reverse_prod"}
      ],
      "representation": {
        "objects": "单位矩阵使用 Matrix 的 1，其 j,i 项为 Kronecker delta。",
        "parameters": "列表 [M¹,…,Mⁿ] 按执行顺序给出矩阵。DecidableEq 只用于单位矩阵的表示。",
        "quantifiers": "任意有限列表，包含空列表及单元素列表。",
        "conclusion": "空列表乘积为 1；非空递归为 orderedProduct Ms * M，故为 Mⁿ⋯M¹；等于列表逆序的标准 prod。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_eq_frozen"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.actualDomain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.actualDomain_zero"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.actualDomain_cons_succ"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.actualDomain_last"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.actualDomain_subset_dom"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.image_subset_dom_of_comp"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.subset_dom_first_of_comp"}
      ],
      "representation": {
        "objects": "fs=[φ₁,…,φₖ] 为执行顺序；chain fs=φₖ∘⋯∘φ₁，并证明等于冻结 OperatorChain fs.reverse。",
        "parameters": "actualDomain fs U m=(chain (fs.take m)).func '' U；零基 m 对应正文 U_{m+1}。",
        "quantifiers": "任意列表、U、前缀长度；定义域定理要求 U ⊆ dom(chain fs) 且 m<fs.length。",
        "conclusion": "初始域为 U，逐步域为前一步的精确像；最终域为全链像，并证明每步实际输入域包含于该步定义域。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.AllPositivePath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.HasZeroFactor"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.positivePath_iff_no_zero"}
      ],
      "representation": {
        "objects": "IndexPath I r 为 r 个中间指标的递归元组；0 对应 PUnit，r+1 对应 I × IndexPath I r。",
        "parameters": "任意非空矩阵列唯一写为 M::Ms；路径类型为 IndexPath I Ms.length，端点另给 i,j。",
        "quantifiers": "元组依次选择 k₁,…,k_{n−1}，没有限制允许路径的额外条件。",
        "conclusion": "AllPositivePath 递归合取所有边严格正；HasZeroFactor 递归析取某边为零；二者互为否定。n=1 时唯一空元组只检验 M j i。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.singleton_lip_iff"}
      ],
      "representation": {
        "objects": "Unique I 等价于原文指标集恰有一个元素。",
        "parameters": "φ、L 和唯一指标 j。",
        "quantifiers": "所有 x,y∈dom φ。",
        "conclusion": "全域 Lip 矩阵条件等价于 d_j(φx,φy) ≤ L j j*d_j(x,y)，同时给出两个方向。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.restrictedLipFamily_antitone"}
      ],
      "representation": {
        "objects": "受限 Lip 证书族。",
        "parameters": "固定 φ 及 U⊆V。",
        "quantifiers": "任意属于 V 上证书族的 L；V⊆dom φ 已包含在该成员条件中。",
        "conclusion": "V 上的合法矩阵属于 U 上的证书族，即所需反单调包含。"
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
        "objects": "φ₂*φ₁ 是冻结算子乘法，即 φ₂∘φ₁。",
        "parameters": "U⊆dom(φ₂*φ₁)，L₁ 在 U 上合法，L₂ 在精确像 φ₁.func '' U 上合法。",
        "quantifiers": "任意 x,y∈U 及所有输出分量 j。",
        "conclusion": "L₂*L₁ 是复合在 U 上的合法 Lip 矩阵；没有用任意更大集合替代实际中间像。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.restrictedCoLipFamily_antitone"}
      ],
      "representation": {
        "objects": "含非空性条件的受限 co-Lip 证书族。",
        "parameters": "固定 φ，U.Nonempty 及 U⊆V。",
        "quantifiers": "任意 V 上合法 K；V⊆dom φ 从成员条件取得。",
        "conclusion": "K 在 U 上仍合法，保留 U 的非空性。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_entry_eq_zero"}
      ],
      "representation": {
        "objects": "全域 co-Lip 矩阵为 dom φ 上的受限 co-Lip 矩阵。",
        "parameters": "K 合法；x,y∈dom φ；输出 j 距离为 0，输入 i 距离严格正。",
        "quantifiers": "任意满足这些条件的点对、通道及全域合法矩阵。",
        "conclusion": "K j i=0；不要求距离或矩阵条目有限。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_comp"}
      ],
      "representation": {
        "objects": "复合算子及 co-Lip 矩阵的通常乘积。",
        "parameters": "U⊆dom(φ₂*φ₁)，K₁ 在 U 上合法，K₂ 在精确像 φ₁.func '' U 上合法。",
        "quantifiers": "任意 x,y∈U 和输出 j；每个输入证书均显式包含所用集合非空性。",
        "conclusion": "K₂*K₁ 在 U 上合法，输出谓词包含 U.Nonempty 和定义域条件。"
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
        "objects": "算子 1 是恒等算子，矩阵 1 是标准单位矩阵。",
        "parameters": "任意 U⊆dom(1)。",
        "quantifiers": "所有 x,y∈U 和 j；定理也涵盖空 U，因而包含正文非空情形。",
        "conclusion": "单位矩阵是恒等算子的合法受限 Lip 矩阵。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_coLip"}
      ],
      "representation": {
        "objects": "恒等算子和单位矩阵与空链、空矩阵乘积的表示一致。",
        "parameters": "U.Nonempty 且 U⊆dom(1)。",
        "quantifiers": "全部 x,y∈U 及输出 j。",
        "conclusion": "单位矩阵是恒等算子的合法受限 co-Lip 矩阵。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.product_pos_iff_path"}
      ],
      "representation": {
        "objects": "任意非空有限矩阵列写为 M::Ms，长度 n=Ms.length+1。",
        "parameters": "任意输入 i 和输出 j，条目为 orderedProduct (M::Ms) j i。",
        "quantifiers": "存在 p : IndexPath I Ms.length，精确量化所有 n−1 个中间指标。",
        "conclusion": "乘积条目严格正当且仅当存在所有边严格正的路径；归纳基 Ms=[] 处理 n=1。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipFamily_restrict"}
      ],
      "representation": {
        "objects": "全域及受限 Lip 证书族。",
        "parameters": "固定 φ，任意 U⊆dom φ。",
        "quantifiers": "任意全域合法 L。",
        "conclusion": "全域证书族包含于 U 上的受限证书族。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipFamily_restrict"}
      ],
      "representation": {
        "objects": "dom φ 上及 U 上的 co-Lip 证书族。",
        "parameters": "U.Nonempty 且 U⊆dom φ。",
        "quantifiers": "任意在 dom φ 上合法的 K。",
        "conclusion": "K 在 U 上仍合法，包括非空性要求。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_lip"}
      ],
      "representation": {
        "objects": "ss 是 (算子,矩阵) 的有限列表，只含原始数据，没有保存目标结论的字段。",
        "parameters": "U⊆dom(chain (ss.map fst))；算子及矩阵列表按执行顺序对应。",
        "quantifiers": "每个 m<ss.length 单独假设第 m 步矩阵在 actualDomain (ss.map fst) U m 上满足受限 Lip 条件。",
        "conclusion": "从逐步条件归纳建立整个复合在 U 上的 Lip 界，矩阵为逆执行顺序乘积；证明对所有有限长度成立，特别涵盖任意正长度。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
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
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_coLip_of_nonempty"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_coLip"}
      ],
      "representation": {
        "objects": "同样用算子与矩阵的数据对列表，逐步实际域为精确前缀像。",
        "parameters": "主定理要求 0<ss.length 及 U⊆全链定义域；没有额外假定全链 co-Lip 结论。",
        "quantifiers": "对每个合法步索引，单独假设其矩阵在实际输入域上的 co-Lip 条件；U 非空由首步条件推出。",
        "conclusion": "归纳得到有序连乘矩阵是全链在 U 上的 co-Lip 矩阵；辅助定理还在显式 U.Nonempty 下覆盖零步边界。"
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
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
        {"file": "LCH02/Paths.lean", "name": "LCH02.product_zero_iff_paths"}
      ],
      "representation": {
        "objects": "任意非空有限矩阵列 M::Ms，输入 i，输出 j。",
        "parameters": "乘积与所有路径均沿用 D04、D06 的精确表示。",
        "quantifiers": "对所有 p : IndexPath I Ms.length，递归析取表示存在某层零因子。",
        "conclusion": "乘积条目为零当且仅当每条路径含零因子；由正值判据和路径上的正/零互补推出，包含唯一空中间序列的 n=1 情形。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```