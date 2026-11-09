已完成全部 40 项义务，并使用指定 Lean 4.29.1 和固定 mathlib 本地编译通过。104 个新增声明的传递公理依赖仅包含 `propext`、`Classical.choice`、`Quot.sound`。两份冻结前置模块原样使用，以下提交全部新增项目文件。

原文归属：Zhe Li（Glen Li / glenzli），[ORCID](https://orcid.org/0009-0006-6536-3453)，*The Operator Evolution Theory*，[官方页面](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下为 AI 辅助编写的历史章节 Lean 改编。

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "hch02"
version = "0.1.0"
defaultTargets = ["HCH02"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "HCH02"
roots = ["Main", "Bounds", "Chains", "Scalar", "Example",
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space"]
```

```lean filename=Main.lean
import Bounds
import Chains
import Scalar
import Example
```

```lean filename=Bounds.lean
/-
Formalization of the frozen historical Chapter 2 of The Operator Evolution Theory.
Source: Zhe Li / Glen Li / glenzli, https://glenzli.com/books/oet/.
License: CC-BY-4.0, https://creativecommons.org/licenses/by/4.0/.
This Lean adaptation was generated with AI assistance; it is not the author's code.
-/
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ENNReal.Inv

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

noncomputable section
namespace HCH02
set_option linter.unusedSectionVars false

abbrev Mat (I : Type) := I → I → ℝ≥0∞
abbrev Channel (I : Type) := I × I

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def compose (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

def identity : Operator X bot := ⟨id, rfl⟩

theorem dom_comp (ψ φ : Operator X bot) (x : X) :
    x ∈ dom (compose ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro e
    exact h (by rw [e, ψ.preserves_bot])
  · exact And.right

def mmul (A B : Mat I) : Mat I := fun i j => ∑ k, A k j * B i k

noncomputable def unit : Mat I := fun i j => if i = j then 1 else 0

def display (A : Mat I) : Matrix I I ℝ≥0∞ := fun j i => A i j

theorem display_mmul (A B : Mat I) : display (mmul A B) = display A * display B := rfl

theorem display_unit : display (unit : Mat I) = (1 : Matrix I I ℝ≥0∞) := by
  classical
  ext j i
  simp [display, unit, Matrix.one_apply, eq_comm]

theorem unit_mmul (A : Mat I) : mmul unit A = A := by
  classical
  ext i j
  simp [mmul, unit]

theorem mmul_unit (A : Mat I) : mmul A unit = A := by
  classical
  ext i j
  simp [mmul, unit]

def action (M : Mat I) (v : I → ℝ≥0∞) (j : I) : ℝ≥0∞ := ∑ i, M i j * v i

theorem action_mmul (A B : Mat I) (v : I → ℝ≥0∞) (j : I) :
    action (mmul A B) v j = action A (action B v) j := by
  simp only [action, mmul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem action_unit (v : I → ℝ≥0∞) (j : I) : action unit v j = v j := by
  classical
  simp [action, unit]

def LipOn (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ action M (fun i => d i x y) j}

def Lip (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) : Set (Mat I) :=
  LipOn d φ (dom φ)

def CoLipOn (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    action M (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)}

variable {d : I → X → X → ℝ≥0∞} {φ ψ : Operator X bot}
  {U V : Set X} {L K : Mat I}

theorem lip_restrict (h : L ∈ LipOn d φ V) (hUV : U ⊆ V) : L ∈ LipOn d φ U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem lip_global_restrict (hU : U ⊆ dom φ) : Lip d φ ⊆ LipOn d φ U :=
  fun _ h => lip_restrict h hU

noncomputable def entryInf (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf ((fun M : Mat I => M i j) '' LipOn d φ U)

theorem entryInf_mono (hUV : U ⊆ V) (i j : I) :
    entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  rintro _ ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict hM hUV, rfl⟩

theorem lip_singleton [Subsingleton I] (i : I) (h : L ∈ LipOn d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have he : action L (fun k => d k x y) i = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      exact (hk (Subsingleton.elim k i)).elim
    · simp
  simpa only [he] using h.2 x hx y hy i

theorem lip_comp (hU : U ⊆ dom (compose ψ φ))
    {A B : Mat I} (hB : B ∈ LipOn d φ U)
    (hA : A ∈ LipOn d ψ (φ.func '' U)) :
    mmul A B ∈ LipOn d (compose ψ φ) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
        ≤ action A (fun k => d k (φ.func x) (φ.func y)) j :=
      hA.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ action A (fun k => action B (fun i => d i x y) k) j := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (hB.2 x hx y hy k) _
    _ = action (mmul A B) (fun i => d i x y) j := (action_mmul A B _ j).symm

theorem colip_comp (hU : U ⊆ dom (compose ψ φ))
    {A B : Mat I} (hB : B ∈ CoLipOn d φ U)
    (hA : A ∈ CoLipOn d ψ (φ.func '' U)) :
    mmul A B ∈ CoLipOn d (compose ψ φ) U := by
  refine ⟨hB.1, hU, ?_⟩
  intro x hx y hy j
  rw [action_mmul]
  exact (Finset.sum_le_sum (fun k _ => mul_le_mul_left' (hB.2.2 x hx y hy k) _)).trans
    (hA.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)

theorem colip_term (hK : K ∈ CoLipOn d φ U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (hK.2.2 x hx y hy j)

theorem colip_zero_output (hK : K ∈ CoLipOn d φ (dom φ)) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hz : d j (φ.func x) (φ.func y) = 0) (hp : 0 < d i x y) : K i j = 0 := by
  have h := colip_term hK hx hy i j
  rw [hz] at h
  exact (mul_eq_zero.mp (le_antisymm h (zero_le _))).resolve_right (ne_of_gt hp)

theorem perturb_forward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  have hleft : d j (ψ.func x) (φ.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  calc
    d j (ψ.func x) (ψ.func y)
        ≤ d j (ψ.func x) (φ.func x) +
          (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) :=
      ((hd j).triangle _ _ _).trans (add_le_add le_rfl ((hd j).triangle _ _ _))
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) :=
      add_le_add hleft (add_le_add le_rfl (hδ y hy j))
    _ = _ := by simp only [add_assoc, add_left_comm (δ j)]

theorem perturb_reverse (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward hd (fun _ hz => ⟨(hU hz).2, (hU hz).1⟩) _ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k

theorem perturb_lip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : L ∈ LipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ action L (fun i => d i x y) j + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (perturb_forward hd hU hδ hx hy j).trans
    (add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_colip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : K ∈ CoLipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    action K (fun i => d i x y) j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  simpa [two_mul, add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hU hδ hx hy j)

def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0

def RowDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ LipOn d φ U, ∃ i, Row L i j

def ColDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ LipOn d φ U, ∃ j, Col L i j

theorem zero_term {i j : I} (h : L i j = 0) (v : I → ℝ≥0∞) : L i j * v i = 0 := by
  rw [h, zero_mul]

theorem erase_zero_term {i j : I} (h : L i j = 0) (v : I → ℝ≥0∞) :
    action L v j = ∑ k ∈ Finset.univ.erase i, L k j * v k := by
  classical
  have he := Finset.sum_erase_add Finset.univ (fun k => L k j * v k) (Finset.mem_univ i)
  simpa [h, action] using he.symm

theorem row_action {i j : I} (h : Row L i j) (v : I → ℝ≥0∞) :
    action L v j = L i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h k hk, zero_mul]
  · simp

theorem row_bound (hL : L ∈ LipOn d φ U) {i j : I} (h : Row L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  simpa [row_action h] using hL.2 x hx y hy j

theorem col_contribution {i j : I} (h : Col L i j) (v : I → ℝ≥0∞)
    (k : I) (hk : k ≠ j) : L i k * v i = 0 := zero_term (h k hk) v

theorem diagonal_bound (hL : L ∈ LipOn d φ U) (h : Diagonal L)
    (j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_bound hL (fun k hk => h k j hk) hx hy

theorem two_sided (hL : L ∈ LipOn d φ U) (hK : K ∈ CoLipOn d φ U)
    (j : I) (h : Row L j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy j j, row_bound hL h hx hy⟩

theorem all_two_sided (hL : L ∈ LipOn d φ U) (hK : K ∈ CoLipOn d φ U)
    (h : ∀ j, Row L j j) : ∀ j, ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ hx _ hy => two_sided hL hK j (h j) hx hy

theorem finite_two_sided (hL : L ∈ LipOn d φ U) (hK : K ∈ CoLipOn d φ U)
    (h : ∀ j, Row L j j) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hfin j).1, (hfin j).2, all_two_sided hL hK h j⟩

theorem positive_channel (hK : K ∈ CoLipOn d φ U) {i j : I} (h : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hp : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  (ENNReal.mul_pos h.ne' hp.ne').trans_le (colip_term hK hx hy i j)

theorem reflect_zero (hK : K ∈ CoLipOn d φ U) (h : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hz : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel hK (h j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hz j] at hp
  exact (lt_irrefl 0) hp

end HCH02
```

```lean filename=Chains.lean
import Bounds

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

noncomputable section
namespace HCH02

set_option linter.unusedSectionVars false

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def product : List (Mat I) → Mat I
  | [] => unit
  | [M] => M
  | M :: N :: ms => mmul (product (N :: ms)) M

theorem product_cons (M : Mat I) (ms : List (Mat I)) :
    product (M :: ms) = mmul (product ms) M := by
  cases ms with
  | nil => exact (unit_mmul M).symm
  | cons N ns => rfl

theorem product_empty : product ([] : List (Mat I)) = unit := rfl
theorem product_single (M : Mat I) : product [M] = M := rfl

abbrev Step (X I : Type) (bot : X) := Operator X bot × Mat I

def chain : List (Step X I bot) → Operator X bot
  | [] => identity
  | s :: ss => compose (chain ss) s.1

def finalImage : List (Step X I bot) → Set X → Set X
  | [], U => U
  | s :: ss, U => finalImage ss (s.1.func '' U)

def inputDomain : List (Step X I bot) → Set X → ℕ → Set X
  | [], U, _ => U
  | _ :: _, U, 0 => U
  | s :: ss, U, n + 1 => inputDomain ss (s.1.func '' U) n

def Steps (R : Operator X bot → Set X → Mat I → Prop) :
    List (Step X I bot) → Set X → Prop
  | [], _ => True
  | s :: ss, U => R s.1 U s.2 ∧ Steps R ss (s.1.func '' U)

theorem chain_fold (ss : List (Step X I bot)) (x : X) :
    (chain ss).func x = ss.foldl (fun y s => s.1.func y) x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih (s.1.func x)

theorem steps_iff (R : Operator X bot → Set X → Mat I → Prop)
    (ss : List (Step X I bot)) (U : Set X) :
    Steps R ss U ↔ ∀ n (hn : n < ss.length),
      R ss[n].1 (inputDomain ss U n) ss[n].2 := by
  induction ss generalizing U with
  | nil => simp [Steps]
  | cons s ss ih =>
    constructor
    · rintro ⟨h, hs⟩ n hn
      cases n with
      | zero => exact h
      | succ n => exact (ih _).mp hs n (by simpa using hn)
    · intro h
      exact ⟨h 0 (by simp), (ih _).mpr (fun n hn => h (n + 1) (by simpa using hn))⟩

theorem image_chain (ss : List (Step X I bot)) (U : Set X) :
    (chain ss).func '' U = finalImage ss U := by
  induction ss generalizing U with
  | nil => simp [chain, identity, finalImage]
  | cons s ss ih =>
    simpa only [chain, compose, Set.image_image, finalImage] using ih (s.1.func '' U)

theorem inputDomain_prefix (ss : List (Step X I bot)) (U : Set X) (n : ℕ) :
    inputDomain ss U n = (chain (ss.take n)).func '' U := by
  induction ss generalizing U n with
  | nil => simp [inputDomain, chain, identity]
  | cons s ss ih =>
    cases n with
    | zero => simp [inputDomain, chain, identity]
    | succ n =>
      simpa only [inputDomain, List.take_succ_cons, chain, compose, Set.image_image]
        using ih (s.1.func '' U) n

theorem chain_domains (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) :
    Steps (fun φ V _ => V ⊆ dom φ) ss U := by
  induction ss generalizing U with
  | nil => trivial
  | cons s ss ih =>
    refine ⟨fun x hx => ((dom_comp _ _ x).mp (hU hx)).1, ih _ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ((dom_comp _ _ x).mp (hU hx)).2

theorem actual_domains (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) (n : ℕ) (hn : n < ss.length) :
    inputDomain ss U n ⊆ dom ss[n].1 :=
  (steps_iff _ ss U).mp (chain_domains ss U hU) n hn

theorem lip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hU : U ⊆ dom (identity : Operator X bot)) :
    unit ∈ LipOn d (identity : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [action_unit, identity]

theorem colip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (identity : Operator X bot)) :
    unit ∈ CoLipOn d (identity : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [action_unit, identity]

theorem chain_lip (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) (hs : Steps (LipOn d) ss U) :
    product (ss.map Prod.snd) ∈ LipOn d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact lip_unit d U hU
  | cons s ss ih =>
    have ht : s.1.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ((dom_comp _ _ x).mp (hU hx)).2
    simpa only [List.map_cons, product_cons, chain] using
      lip_comp hU hs.1 (ih _ ht hs.2)

theorem chain_colip (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X I bot)) (U : Set X) (hne : U.Nonempty)
    (hU : U ⊆ dom (chain ss)) (hs : Steps (CoLipOn d) ss U) :
    product (ss.map Prod.snd) ∈ CoLipOn d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact colip_unit d U hne hU
  | cons s ss ih =>
    have ht : s.1.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ((dom_comp _ _ x).mp (hU hx)).2
    simpa only [List.map_cons, product_cons, chain] using
      colip_comp hU hs.1 (ih _ (hne.image _) ht hs.2)

theorem nonempty_chain_colip (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain (s :: ss))) (hs : Steps (CoLipOn d) (s :: ss) U) :
    product ((s :: ss).map Prod.snd) ∈ CoLipOn d (chain (s :: ss)) U :=
  chain_colip d _ U hs.1.1 hU hs

theorem finite_lip (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss))
    (hs : ∀ n (hn : n < ss.length),
      ss[n].2 ∈ LipOn d ss[n].1 (inputDomain ss U n)) :
    product (ss.map Prod.snd) ∈ LipOn d (chain ss) U :=
  chain_lip d ss U hU ((steps_iff _ ss U).mpr hs)

theorem finite_colip (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain (s :: ss)))
    (hs : ∀ n (hn : n < (s :: ss).length),
      (s :: ss)[n].2 ∈ CoLipOn d (s :: ss)[n].1 (inputDomain (s :: ss) U n)) :
    product ((s :: ss).map Prod.snd) ∈ CoLipOn d (chain (s :: ss)) U :=
  nonempty_chain_colip d s ss U hU ((steps_iff _ (s :: ss) U).mpr hs)

/- Paths include every intermediate index, without filtering by edge weights. -/
def Paths : List (Mat I) → Type
  | [] => PUnit
  | [_] => PUnit
  | _ :: N :: ms => I × Paths (N :: ms)

def weight : (ms : List (Mat I)) → Paths ms → I → I → ℝ≥0∞
  | [], _, i, j => unit i j
  | [M], _, i, j => M i j
  | M :: N :: ms, p, i, j => weight (N :: ms) p.2 p.1 j * M i p.1

def AllPositive : (ms : List (Mat I)) → Paths ms → I → I → Prop
  | [], _, i, j => i = j
  | [M], _, i, j => 0 < M i j
  | M :: N :: ms, p, i, j => 0 < M i p.1 ∧ AllPositive (N :: ms) p.2 p.1 j

def HasZero : (ms : List (Mat I)) → Paths ms → I → I → Prop
  | [], _, i, j => i ≠ j
  | [M], _, i, j => M i j = 0
  | M :: N :: ms, p, i, j => M i p.1 = 0 ∨ HasZero (N :: ms) p.2 p.1 j

theorem paths_single (M : Mat I) : ∃ p : Paths [M], ∀ q, q = p := by
  exact ⟨PUnit.unit, fun q => by cases q; rfl⟩

theorem weight_zero (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    weight (M :: ms) p i j = 0 ↔ HasZero (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => rfl
  | cons N ns ih =>
    simp only [weight, HasZero, mul_eq_zero, ih N p.2 p.1, or_comm]

theorem weight_positive (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    0 < weight (M :: ms) p i j ↔ AllPositive (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => rfl
  | cons N ns ih =>
    simp only [weight, AllPositive, ENNReal.mul_pos_iff, ih N p.2 p.1, and_comm]

def edgeValues : (ms : List (Mat I)) → Paths ms → I → I → List ℝ≥0∞
  | [], _, _, _ => []
  | [M], _, i, j => [M i j]
  | M :: N :: ms, p, i, j => M i p.1 :: edgeValues (N :: ms) p.2 p.1 j

theorem edges_length (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    (edgeValues (M :: ms) p i j).length = ms.length + 1 := by
  induction ms generalizing M i with
  | nil => rfl
  | cons N ns ih => simp [edgeValues, ih N p.2 p.1]

theorem weight_edges (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    weight (M :: ms) p i j = (edgeValues (M :: ms) p i j).prod := by
  induction ms generalizing M i with
  | nil => simp [weight, edgeValues]
  | cons N ns ih => simp [weight, edgeValues, ih N p.2 p.1, mul_comm]

theorem positive_edges (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    AllPositive (M :: ms) p i j ↔ ∀ a ∈ edgeValues (M :: ms) p i j, 0 < a := by
  induction ms generalizing M i with
  | nil => simp [AllPositive, edgeValues]
  | cons N ns ih => simp [AllPositive, edgeValues, ih N p.2 p.1]

theorem zero_edges (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    HasZero (M :: ms) p i j ↔ (0 : ℝ≥0∞) ∈ edgeValues (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => simp [HasZero, edgeValues, eq_comm]
  | cons N ns ih => simp [HasZero, edgeValues, ih N p.2 p.1, eq_comm]

/- Removing the head index identifies these paths with I^(length-1). -/
def finConsEquiv (n : ℕ) : I × (Fin n → I) ≃ (Fin (n + 1) → I) where
  toFun p := Fin.cases p.1 p.2
  invFun f := (f 0, fun k => f k.succ)
  left_inv p := by cases p; rfl
  right_inv f := by
    funext k
    exact Fin.cases rfl (fun _ => rfl) k

def intermediates : (M : Mat I) → (ms : List (Mat I)) → Paths (M :: ms) ≃ (Fin ms.length → I)
  | _, [] =>
    ⟨fun _ k => Fin.elim0 k, fun _ => PUnit.unit,
      (fun p => by cases p; rfl), (fun f => by funext k; exact Fin.elim0 k)⟩
  | M, N :: ns =>
    (Equiv.prodCongr (Equiv.refl I) (intermediates N ns)).trans
      (finConsEquiv ns.length)

theorem product_zero_paths (M : Mat I) (ms : List (Mat I)) (i j : I) :
    product (M :: ms) i j = 0 ↔ ∀ p, HasZero (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => simp [product, HasZero, Paths]
  | cons N ns ih =>
    simp only [product, mmul, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const,
      mul_eq_zero, ih N]
    constructor
    · intro h p
      rcases h p.1 with ht | hz
      · exact Or.inr (ht p.2)
      · exact Or.inl hz
    · intro h k
      by_cases hz : M i k = 0
      · exact Or.inr hz
      · exact Or.inl (fun p => (h (k, p)).resolve_left hz)

theorem product_positive_paths (M : Mat I) (ms : List (Mat I)) (i j : I) :
    0 < product (M :: ms) i j ↔ ∃ p, AllPositive (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => simp [product, AllPositive, Paths]
  | cons N ns ih =>
    simp only [product, mmul, Finset.sum_pos_iff, Finset.mem_univ, true_and,
      ENNReal.mul_pos_iff, ih N]
    constructor
    · rintro ⟨k, ⟨p, hp⟩, hk⟩
      exact ⟨(k, p), hk, hp⟩
    · rintro ⟨⟨k, p⟩, hk, hp⟩
      exact ⟨k, ⟨p, hp⟩, hk⟩

/- Textbook chain specialization: local certificates are the only analytic data. -/
theorem lip_chain_zero_paths (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (_hU : U ⊆ dom (chain (s :: ss)))
    (_hs : Steps (LipOn d) (s :: ss) U) (i j : I) :
    product (s.2 :: ss.map Prod.snd) i j = 0 ↔
      ∀ p, HasZero (s.2 :: ss.map Prod.snd) p i j :=
  product_zero_paths _ _ i j

theorem colip_chain_positive_paths (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (_hU : U ⊆ dom (chain (s :: ss)))
    (_hs : Steps (CoLipOn d) (s :: ss) U) (i j : I) :
    0 < product (s.2 :: ss.map Prod.snd) i j ↔
      ∃ p, AllPositive (s.2 :: ss.map Prod.snd) p i j :=
  product_positive_paths _ _ i j

end HCH02
```

```lean filename=Scalar.lean
import Bounds

open scoped ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

namespace HCH02

variable {X I : Type} {bot : X}

def Scalars (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : Set ℝ≥0∞ :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}

noncomputable def scalarInf (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf (Scalars d φ U i j)

variable {d : I → X → X → ℝ≥0∞} {φ : Operator X bot} {U : Set X} {i j : I}

theorem scalars_upward {a b : ℝ≥0∞} (ha : a ∈ Scalars d φ U i j) (hab : a ≤ b) :
    b ∈ Scalars d φ U i j :=
  fun x hx y hy => (ha x hx y hy).trans (mul_le_mul_right' hab _)

theorem above_inf {b : ℝ≥0∞} (hb : scalarInf d φ U i j < b) :
    b ∈ Scalars d φ U i j := by
  obtain ⟨a, ha, hab⟩ := sInf_lt_iff.mp hb
  exact scalars_upward ha hab.le

theorem zero_inf_positive (ha : scalarInf d φ U i j = 0) {b : ℝ≥0∞}
    (hb : 0 < b) (hfin : b < ⊤) : b ∈ Scalars d φ U i j :=
  above_inf (ha ▸ hb)

theorem finite_inf_iff : scalarInf d φ U i j < ⊤ ↔
    ∃ a < ⊤, a ∈ Scalars d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, ht⟩ := sInf_lt_iff.mp h
    exact ⟨a, ht, ha⟩
  · rintro ⟨a, ht, ha⟩
    exact (sInf_le ha).trans_lt ht

theorem positive_finite_attained (hp : 0 < scalarInf d φ U i j)
    (ht : scalarInf d φ U i j < ⊤) :
    scalarInf d φ U i j ∈ Scalars d φ U i j := by
  let S := Scalars d φ U i j
  obtain ⟨a, _, ha⟩ := finite_inf_iff.mp ht
  letI : Nonempty S := ⟨⟨a, ha⟩⟩
  have hi : scalarInf d φ U i j = ⨅ a : S, (a : ℝ≥0∞) := sInf_eq_iInf' S
  intro x hx y hy
  calc
    d j (φ.func x) (φ.func y) ≤ ⨅ a : S, (a : ℝ≥0∞) * d i x y :=
      le_iInf (fun a => a.property x hx y hy)
    _ = scalarInf d φ U i j * d i x y := by
      rw [hi]
      exact (ENNReal.iInf_mul (fun _ hz => (ne_of_gt hp (hi.trans hz)).elim)).symm

theorem zero_input_positive_output {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hz : d i x y = 0) (hp : 0 < d j (φ.func x) (φ.func y)) :
    Scalars d φ U i j = ∅ ∧ scalarInf d φ U i j = ⊤ := by
  have hempty : Scalars d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hz, mul_zero] at h
    exact (not_le_of_gt hp) h
  exact ⟨hempty, by simp [scalarInf, hempty]⟩

end HCH02
```

```lean filename=Example.lean
import Scalar

open scoped ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

namespace HCH02.Counterexample

/- 0 is absorbing.  The two live points have input distance infinity
   and output distance one; all strictly positive scalars work. -/
def distance (i : Bool) (x y : Fin 3) : ℝ≥0∞ :=
  if x = y then 0 else if x = 0 ∨ y = 0 then ⊤ else if i then 1 else ⊤

theorem gauge (i : Bool) : ExtendedPseudoMetric (Fin 3) 0 (distance i) := by
  constructor
  · exact ⟨1, by decide⟩
  · intro x
    simp [distance]
  · intro x y
    fin_cases x <;> fin_cases y <;> cases i <;> norm_num [distance]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> cases i <;> norm_num [distance]
  · intro x hx
    simp [distance, hx]

def live : Set (Fin 3) := {x | x ≠ 0}
def op : Operator (Fin 3) 0 := HCH02.identity

theorem live_legal : live.Nonempty ∧ live ⊆ dom op := by
  exact ⟨⟨1, by change (1 : Fin 3) ≠ 0; decide⟩, fun _ hx => hx⟩

theorem every_positive {a : ℝ≥0∞} (ha : 0 < a) :
    a ∈ Scalars distance op live false true := by
  intro x hx y hy
  have hx0 : x ≠ 0 := hx
  have hy0 : y ≠ 0 := hy
  by_cases hxy : x = y
  · subst y
    simp [distance, op, HCH02.identity]
  · simp [distance, op, HCH02.identity, hxy, hx0, hy0, ENNReal.mul_top ha.ne']

theorem zero_not_feasible : (0 : ℝ≥0∞) ∉ Scalars distance op live false true := by
  intro h
  have hh := h 1 (by change (1 : Fin 3) ≠ 0; decide)
    2 (by change (2 : Fin 3) ≠ 0; decide)
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have hh' : (1 : ℝ≥0∞) ≤ 0 := by
    simpa [distance, op, HCH02.identity, h12, h10, h20] using hh
  exact (not_le_of_gt zero_lt_one) hh'

theorem inf_zero : scalarInf distance op live false true = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro b hb
  obtain ⟨a, ha, hab⟩ := exists_between hb
  exact (sInf_le (every_positive ha)).trans_lt hab

theorem zero_inf_unattained :
    (∀ i, ExtendedPseudoMetric (Fin 3) 0 (distance i)) ∧
    live.Nonempty ∧ live ⊆ dom op ∧
    scalarInf distance op live false true = 0 ∧
    (0 : ℝ≥0∞) ∉ Scalars distance op live false true :=
  ⟨gauge, live_legal.1, live_legal.2, inf_zero, zero_not_feasible⟩

end HCH02.Counterexample
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "HC02-D01",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.LipOn"},
        {"file": "Bounds.lean", "name": "HCH02.Lip"}
      ],
      "representation": "LipOn同时要求U⊆dom φ与所有x,y∈U、输出j的ENNReal求和上界；Lip取U=dom φ。指标I有限非空。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.CoLipOn"}
      ],
      "representation": "同时要求U.Nonempty、U⊆dom φ及所有点对、输出分量的求和下界；0和∞均为合法系数。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.Mat"},
        {"file": "Bounds.lean", "name": "HCH02.mmul"},
        {"file": "Bounds.lean", "name": "HCH02.action"},
        {"file": "Bounds.lean", "name": "HCH02.display"},
        {"file": "Bounds.lean", "name": "HCH02.display_mmul"}
      ],
      "representation": "Mat按输入i、输出j存储；display M的第j行第i列为M i j。display_mmul证明Σk A k j*B i k对应通常矩阵乘法。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.product"},
        {"file": "Chains.lean", "name": "HCH02.product_empty"},
        {"file": "Chains.lean", "name": "HCH02.product_single"},
        {"file": "Chains.lean", "name": "HCH02.product_cons"},
        {"file": "Bounds.lean", "name": "HCH02.unit"},
        {"file": "Bounds.lean", "name": "HCH02.unit_mmul"},
        {"file": "Bounds.lean", "name": "HCH02.mmul_unit"},
        {"file": "Bounds.lean", "name": "HCH02.action_unit"},
        {"file": "Bounds.lean", "name": "HCH02.display_unit"}
      ],
      "representation": "product的列表按施行顺序排列；空乘积为δij，单元素乘积等于该矩阵，递推为尾部乘积乘首矩阵。单位作用与通常显示矩阵的对应也已证明。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.Step"},
        {"file": "Chains.lean", "name": "HCH02.chain"},
        {"file": "Chains.lean", "name": "HCH02.Steps"},
        {"file": "Chains.lean", "name": "HCH02.inputDomain"},
        {"file": "Chains.lean", "name": "HCH02.steps_iff"},
        {"file": "Chains.lean", "name": "HCH02.chain_fold"},
        {"file": "Chains.lean", "name": "HCH02.image_chain"},
        {"file": "Chains.lean", "name": "HCH02.inputDomain_prefix"},
        {"file": "Chains.lean", "name": "HCH02.chain_domains"},
        {"file": "Chains.lean", "name": "HCH02.actual_domains"}
      ],
      "representation": "列表按φ1,…,φk排列。chain_fold证明逐次施行；inputDomain从U1递归取实际像。steps_iff对应逐步序号量化；最终域条件推出全部中间域合法，image_chain对应全复合像。Steps只记录单步条件。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.Paths"},
        {"file": "Chains.lean", "name": "HCH02.intermediates"},
        {"file": "Chains.lean", "name": "HCH02.paths_single"},
        {"file": "Chains.lean", "name": "HCH02.weight"},
        {"file": "Chains.lean", "name": "HCH02.edgeValues"},
        {"file": "Chains.lean", "name": "HCH02.edges_length"},
        {"file": "Chains.lean", "name": "HCH02.weight_edges"},
        {"file": "Chains.lean", "name": "HCH02.AllPositive"},
        {"file": "Chains.lean", "name": "HCH02.HasZero"},
        {"file": "Chains.lean", "name": "HCH02.positive_edges"},
        {"file": "Chains.lean", "name": "HCH02.zero_edges"},
        {"file": "Chains.lean", "name": "HCH02.weight_zero"},
        {"file": "Chains.lean", "name": "HCH02.weight_positive"}
      ],
      "representation": "正长度n的Paths与Fin(n-1)→I等价，遍历所有中间序列，以i,j固定端点；边列表有n项，权重等于边乘积，全正与含零谓词分别对应全部边正、存在零边；n=1路径唯一。",
      "dependencies": ["HC02-D03", "HC02-D04"]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.Channel"},
        {"file": "Bounds.lean", "name": "HCH02.Row"},
        {"file": "Bounds.lean", "name": "HCH02.Col"},
        {"file": "Bounds.lean", "name": "HCH02.Diagonal"},
        {"file": "Bounds.lean", "name": "HCH02.RowDecoupled"},
        {"file": "Bounds.lean", "name": "HCH02.ColDecoupled"}
      ],
      "representation": "通道为I×I。Row L i j仅允许输出j的输入i位置非零，Col L i j仅允许输入i的输出j位置非零；解耦定义存在合法证书及任意唯一位置，Diagonal要求全部非对角项为零。",
      "dependencies": ["HC02-D01", "HC02-D03"]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.Scalars"},
        {"file": "Scalar.lean", "name": "HCH02.scalarInf"}
      ],
      "representation": "Scalars为全部点对的单输入分量可行标量族；scalarInf取ENNReal下确界，空族下确界为∞。用于合法U⊆dom φ，未与矩阵条目等同。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_singleton"}
      ],
      "representation": "有限非空I另有Subsingleton时，任取唯一指标i，Lip求和化为Lii*di，保留全部U内点对。",
      "dependencies": ["HC02-D01", "HC02-D03"]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_global_restrict"}
      ],
      "representation": "U⊆dom φ时，全域Lip证书均属于U上的受限族。",
      "dependencies": ["HC02-D01", "HC02-P03"]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_restrict"}
      ],
      "representation": "U⊆V时，V上的合法证书限制到U；定义域合法性随包含传递。",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.entryInf"},
        {"file": "Bounds.lean", "name": "HCH02.entryInf_mono"}
      ],
      "representation": "entryInf为合法受限证书条目像集的下确界；用族包含证明U⊆V时下确界不增，包含空族。",
      "dependencies": ["HC02-D01", "HC02-P03"]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_comp"}
      ],
      "representation": "U⊆dom(ψ∘φ)，第二步实际域φ(U)；两局部Lip证书给出mmul A B的复合证书，有限和换序由action_mmul证明。",
      "dependencies": ["HC02-D01", "HC02-D03", "HC02-D05"]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.colip_zero_output"},
        {"file": "Bounds.lean", "name": "HCH02.colip_term"}
      ],
      "representation": "dom内点对输出j距0、输入i距正时，从全域co-Lip求和取单项并用乘积零判据，推出Kij=0。",
      "dependencies": ["HC02-D02", "HC02-D03"]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.colip_comp"}
      ],
      "representation": "与两步Lip相同的实际像域，求和下界按mmul传播；结论域的非空性取自首步合法co-Lip证书。",
      "dependencies": ["HC02-D02", "HC02-D03", "HC02-D05"]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_forward"}
      ],
      "representation": "共同定义域U上逐点跨算子误差≤δ，伪度量对称性与两次三角不等式给出正向像距≤原像距+δj+δj。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_reverse"}
      ],
      "representation": "交换算子，并由对称性重建误差前提，得到反向点对扰动。",
      "dependencies": ["HC02-P08"]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_lip"}
      ],
      "representation": "把第一个算子的受限Lip界代入正向扰动，得到求和上界+2*δj。",
      "dependencies": ["HC02-D01", "HC02-D03", "HC02-P08"]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_colip"}
      ],
      "representation": "把第一个算子的co-Lip下界接到反向扰动，得到求和≤第二个算子像距+2*δj。",
      "dependencies": ["HC02-D02", "HC02-D03", "HC02-P09"]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.finite_lip"},
        {"file": "Chains.lean", "name": "HCH02.chain_lip"}
      ],
      "representation": "按序号给定各实际输入域的Lip证书，经steps_iff构造单步条件并归纳，得到指定有序乘积的全复合上界；也覆盖零步。",
      "dependencies": ["HC02-D04", "HC02-D05", "HC02-P05", "HC02-P14"]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.finite_colip"},
        {"file": "Chains.lean", "name": "HCH02.nonempty_chain_colip"},
        {"file": "Chains.lean", "name": "HCH02.chain_colip"}
      ],
      "representation": "非空列表表示任意正长度链；各步co-Lip证书自带非空性，无额外初始非空假设，归纳得到指定乘积证书。",
      "dependencies": ["HC02-D04", "HC02-D05", "HC02-P07", "HC02-P15"]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.lip_unit"}
      ],
      "representation": "恒等算子上单位矩阵给任意合法U的Lip证书，尤其覆盖正文非空U。",
      "dependencies": ["HC02-D01", "HC02-D04", "HC02-D05"]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.colip_unit"}
      ],
      "representation": "非空合法U上恒等算子的单位矩阵co-Lip证书，由单位作用恒等证明。",
      "dependencies": ["HC02-D02", "HC02-D04", "HC02-D05"]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.product_zero_paths"},
        {"file": "Chains.lean", "name": "HCH02.lip_chain_zero_paths"}
      ],
      "representation": "非空实际算子链及逐步Lip证书下，指定乘积条目0等价于每条完整路径含零边；先证明任意非负矩阵列表的更强代数结果，包含单步分支。",
      "dependencies": ["HC02-D01", "HC02-D03", "HC02-D04", "HC02-D05", "HC02-D06"]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.product_positive_paths"},
        {"file": "Chains.lean", "name": "HCH02.colip_chain_positive_paths"}
      ],
      "representation": "非空实际算子链及逐步co-Lip证书下，指定乘积条目正等价于存在完整全正路径；有限和及乘积的正值判据逐层展开，包含单步。",
      "dependencies": ["HC02-D02", "HC02-D03", "HC02-D04", "HC02-D05", "HC02-D06"]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.zero_input_positive_output"}
      ],
      "representation": "输入零距、输出正距的U内点对使Scalars为空且scalarInf=∞；包括候选标量∞，因∞*0=0也失败。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.positive_finite_attained"}
      ],
      "representation": "0<a<∞时，把a写成可行标量子类型上的下确界，应用ENNReal下确界乘法定理证明全部点对的a界，包括输入距0及∞。",
      "dependencies": ["HC02-D08", "HC02-P24"]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.scalars_upward"}
      ],
      "representation": "可行a及a≤b由ENNReal乘法单调性推出b对全部点对仍可行。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.above_inf"}
      ],
      "representation": "sInf S<b给出可行a<b，再向上封闭；实际对任何严格高于下确界的b成立，包含正文0<a<∞及b=∞。",
      "dependencies": ["HC02-D08", "HC02-P20"]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.zero_inf_positive"}
      ],
      "representation": "下确界0且0<b<∞时，由严格高于下确界的可行性取得b证书，未声称0可行。",
      "dependencies": ["HC02-D08", "HC02-P21"]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {"file": "Example.lean", "name": "HCH02.Counterexample.distance"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.gauge"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.op"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.live_legal"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.every_positive"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.inf_zero"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.zero_not_feasible"},
        {"file": "Example.lean", "name": "HCH02.Counterexample.zero_inf_unattained"}
      ],
      "representation": "X=Fin 3，bot=0，I=Bool，φ=id，U为两非吸收点。false分量异点距∞；true分量非吸收异点距1，bot隔离。已证明全部伪度量公理、非空合法域、每个正常数可行、下确界0且0不可行。",
      "dependencies": ["HC02-D05", "HC02-D08"]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.finite_inf_iff"}
      ],
      "representation": "下确界<∞等价于存在有限可行标量，直接用完全格的下确界严格不等式判据，不依赖下确界取到。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.zero_term"},
        {"file": "Bounds.lean", "name": "HCH02.erase_zero_term"}
      ],
      "representation": "系数0令对应乘积0，对任意ENNReal输入均成立；完整输出求和等于删去该输入项后的有限和。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.row_action"},
        {"file": "Bounds.lean", "name": "HCH02.row_bound"}
      ],
      "representation": "Row L i j的唯一输入i可任意；先化简完整求和，再得到输出j的单输入标量上界。",
      "dependencies": ["HC02-D01", "HC02-D03", "HC02-D07"]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.col_contribution"}
      ],
      "representation": "Col L i j保证任意k≠j时L i k*v i=0；v取全部输入距离即正文证书贡献范围。",
      "dependencies": ["HC02-D07", "HC02-P25"]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.diagonal_bound"}
      ],
      "representation": "对角Lip矩阵逐行满足Row L j j，应用任意行化简得到所有分量的对角标量上界。",
      "dependencies": ["HC02-D01", "HC02-D07", "HC02-P26"]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.two_sided"}
      ],
      "representation": "仅要求Lip输出j行只留对角输入；co-Lip不加稀疏条件，取Kjj单项作下界，与行化简上界合并。",
      "dependencies": ["HC02-D02", "HC02-D07", "HC02-P26"]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.all_two_sided"},
        {"file": "Bounds.lean", "name": "HCH02.finite_two_sided"}
      ],
      "representation": "对全部j量化双侧界；有限分支同时断言Ljj、Kjj<∞和所有U内点对的双侧界，不声称距离有限。",
      "dependencies": ["HC02-P29"]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.positive_channel"}
      ],
      "representation": "Kij正且输入i距正时，ENNReal乘积正并由co-Lip单项界支配，故输出j距正。",
      "dependencies": ["HC02-D02", "HC02-D03"]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.reflect_zero"}
      ],
      "representation": "全部Kjj正时，由正通道可分辨保持逐分量反证，反射GaugeZeroRelated；不推出点值相等。",
      "dependencies": ["HC02-D02", "HC02-P31"]
    }
  ]
}
```

已完整完成并严格对齐冻结第 2 章及全部 40 项义务。未完成或未确认范围：无。