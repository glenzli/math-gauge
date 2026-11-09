已完成全部 40 项义务。所有交付 Lean 文件均已用 Lean 4.29.1 和指定 mathlib 提交离线编译通过；108 个声明的公理审计仅出现 `propext`、`Classical.choice`、`Quot.sound`。两份冻结前置源码与附件逐字一致，未作修改。

数学来源：Zhe Li（Glen Li / glenzli），[ORCID](https://orcid.org/0009-0006-6536-3453)，[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以下是对指定历史快照的形式化改编；原附前置模块、署名和许可证文件继续保留。

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
roots = ["Main"]
globs = ["Main", "Bounds", "Chains", "Paths", "Channels", "Counterexample",
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space"]
```

```lean filename=Main.lean
import Bounds
import Chains
import Paths
import Channels
import Counterexample
```

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Matrix.Basic

/-
Formalization of the supplied historical Chapter 2 of The Operator Evolution Theory.
Mathematical source: Zhe Li / Glen Li / glenzli, https://glenzli.com/books/oet/.
License: CC BY 4.0. This Lean adaptation is AI-generated for the frozen HCH02 task.
-/
namespace HCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators
open scoped Classical

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

abbrev Mat (I : Type) := I → I → ENNReal

def display (M : Mat I) : Matrix I I ENNReal := fun j i => M i j

def mmul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k

def action (M : Mat I) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ i, M i j * v i

theorem display_mul (B A : Mat I) : display (mmul B A) = display B * display A := rfl

noncomputable def eye : Mat I := fun i j => if i = j then 1 else 0

@[simp] theorem action_eye (v : I → ENNReal) (j : I) : action eye v j = v j := by
  classical
  simp [action, eye]

@[simp] theorem mmul_eye (A : Mat I) : mmul A eye = A := by
  classical
  funext i j
  simp [mmul, eye]

@[simp] theorem eye_mmul (A : Mat I) : mmul eye A = A := by
  classical
  funext i j
  simp [mmul, eye]

theorem action_mul (B A : Mat I) (v : I → ENNReal) (j : I) :
    action (mmul B A) v j = action B (fun k => action A v k) j := by
  classical
  simp only [action, mmul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

noncomputable def mprod : List (Mat I) → Mat I
  | [] => eye
  | A :: As => mmul (mprod As) A

@[simp] theorem mprod_nil : mprod ([] : List (Mat I)) = eye := rfl
@[simp] theorem mprod_cons (A : Mat I) (As : List (Mat I)) :
    mprod (A :: As) = mmul (mprod As) A := rfl
@[simp] theorem mprod_singleton (A : Mat I) : mprod [A] = A := by simp

def comp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

def ident : Operator X bot := ⟨id, rfl⟩

theorem comp_dom (ψ φ : Operator X bot) (x : X) :
    x ∈ dom (comp ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  constructor
  · intro h
    exact ⟨fun e => h (by rw [e, ψ.preserves_bot]), h⟩
  · exact And.right

def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ action M (fun i => d i x y) j}

def GlobalLip (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  Lip d φ (dom φ)

def CoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    action M (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)}

variable {d : I → X → X → ENNReal} {φ ψ : Operator X bot}
  {U V : Set X} {L K : Mat I}

theorem lip_restrict (h : L ∈ Lip d φ V) (hUV : U ⊆ V) : L ∈ Lip d φ U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict (hU : U ⊆ dom φ) : GlobalLip d φ ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hU

theorem lip_family_antitone (hUV : U ⊆ V) : Lip d φ V ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hUV

noncomputable def entryInf (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := sInf {a | ∃ M ∈ Lip d φ U, M i j = a}

theorem entryInf_mono (hUV : U ⊆ V) (i j : I) :
    entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  rintro a ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict hM hUV, rfl⟩

theorem singleton_lip [Subsingleton I] (h : L ∈ Lip d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i : I) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  haveI : Unique I := ⟨⟨i⟩, fun a => Subsingleton.elim a i⟩
  have hi : (default : I) = i := Subsingleton.elim _ _
  simpa [action, Finset.univ_unique, hi] using h.2 x hx y hy i

theorem singleton_lip_iff [Subsingleton I] (i : I) :
    L ∈ Lip d φ U ↔ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  constructor
  · intro h
    exact ⟨h.1, fun _ hx _ hy => singleton_lip h hx hy i⟩
  · rintro ⟨hU, h⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    haveI : Unique I := ⟨⟨i⟩, fun a => Subsingleton.elim a i⟩
    have hi : (default : I) = i := Subsingleton.elim _ _
    simpa [action, Finset.univ_unique, hi] using h x hx y hy

theorem lip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ Lip d φ U) (hB : B ∈ Lip d ψ (φ.func '' U)) :
    mmul B A ∈ Lip d (comp ψ φ) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
        ≤ action B (fun k => d k (φ.func x) (φ.func y)) j :=
      hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ action B (fun k => action A (fun i => d i x y) k) j :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 x hx y hy k) _
    _ = action (mmul B A) (fun i => d i x y) j := (action_mul _ _ _ _).symm

theorem colip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ CoLip d φ U) (hB : B ∈ CoLip d ψ (φ.func '' U)) :
    mmul B A ∈ CoLip d (comp ψ φ) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  calc
    action (mmul B A) (fun i => d i x y) j
        = action B (fun k => action A (fun i => d i x y) k) j := action_mul _ _ _ _
    _ ≤ action B (fun k => d k (φ.func x) (φ.func y)) j :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 x hx y hy k) _
    _ ≤ d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) :=
      hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_term (h : K ∈ CoLip d φ U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
    (Finset.mem_univ i)).trans (h.2.2 x hx y hy j)

theorem colip_degenerate (h : K ∈ CoLip d φ (dom φ)) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hz : K i j * d i x y = 0 := le_antisymm (hout ▸ colip_term h hx hy i j) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem perturb_forward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  calc
    d j (ψ.func x) (ψ.func y)
        ≤ d j (ψ.func x) (φ.func x) + d j (φ.func x) (ψ.func y) :=
      (hd j).triangle _ _ _
    _ ≤ d j (ψ.func x) (φ.func x) +
        (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) :=
      add_le_add le_rfl ((hd j).triangle _ _ _)
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) := by
      apply add_le_add
      · rw [(hd j).symm]
        exact hδ x hx j
      · exact add_le_add le_rfl (hδ y hy j)
    _ = _ := by rw [add_left_comm, ← add_assoc]

theorem perturb_reverse (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward hd (fun z hz => ⟨(hU hz).2, (hU hz).1⟩) δ _ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k

theorem perturb_lip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : L ∈ Lip d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ action L (fun i => d i x y) j + 2 * δ j := by
  calc
    _ ≤ d j (φ.func x) (φ.func y) + δ j + δ j := perturb_forward hd hU δ hδ hx hy j
    _ ≤ action L (fun i => d i x y) j + δ j + δ j :=
      add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl
    _ = _ := by rw [two_mul, add_assoc]

theorem perturb_colip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : K ∈ CoLip d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    action K (fun i => d i x y) j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  simpa [two_mul, add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hU δ hδ hx hy j)

theorem identity_lip (hU : U ⊆ dom (ident : Operator X bot)) :
    eye ∈ Lip d (ident : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [ident]

theorem identity_colip (hU : U ⊆ dom (ident : Operator X bot)) (hne : U.Nonempty) :
    eye ∈ CoLip d (ident : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [ident]

end
end HCH02
```

```lean filename=Chains.lean
import Bounds

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def chain : List (Operator X bot) → Operator X bot
  | [] => ident
  | φ :: fs => comp (chain fs) φ

def iterImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | φ :: fs, U => iterImage fs (φ.func '' U)

def actual : List (Operator X bot) → Set X → ℕ → Set X
  | [], U, _ => U
  | _ :: _, U, 0 => U
  | φ :: fs, U, n + 1 => actual fs (φ.func '' U) n

theorem chain_image (fs : List (Operator X bot)) (U : Set X) :
    (chain fs).func '' U = iterImage fs U := by
  induction fs generalizing U with
  | nil => simp [chain, ident, iterImage]
  | cons φ fs ih =>
    simpa only [chain, comp, Set.image_image] using ih (φ.func '' U)

theorem actual_prefix (fs : List (Operator X bot)) (U : Set X) (n : ℕ) :
    actual fs U n = (chain (fs.take n)).func '' U := by
  induction fs generalizing U n with
  | nil => simp [actual, chain, ident]
  | cons φ fs ih =>
    cases n with
    | zero => simp [actual, chain, ident]
    | succ n => simpa [actual, chain, comp, Set.image_image] using ih (φ.func '' U) n

theorem initial_subset {φ ψ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (comp ψ φ)) : U ⊆ dom φ :=
  fun x hx => ((comp_dom ψ φ x).mp (hU hx)).1

theorem image_subset {φ ψ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (comp ψ φ)) : φ.func '' U ⊆ dom ψ := by
  rintro y ⟨x, hx, rfl⟩
  exact ((comp_dom ψ φ x).mp (hU hx)).2

theorem actual_domain (fs : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain fs)) (n : ℕ) (hn : n < fs.length) :
    actual fs U n ⊆ dom fs[n] := by
  induction fs generalizing U n with
  | nil => simp at hn
  | cons φ fs ih =>
    cases n with
    | zero => exact initial_subset hU
    | succ n => exact ih (image_subset hU) n (Nat.lt_of_succ_lt_succ hn)

theorem chain_append (fs gs : List (Operator X bot)) :
    chain (fs ++ gs) = comp (chain gs) (chain fs) := by
  induction fs with
  | nil => ext x; rfl
  | cons φ fs ih =>
    simp only [List.cons_append, chain, ih]
    rfl

theorem chain_frozen (fs : List (Operator X bot)) : chain fs = OperatorChain fs.reverse := by
  induction fs using List.reverseRecOn with
  | nil => rfl
  | append_singleton fs φ ih =>
    rw [chain_append, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, OperatorChain, ← ih]
    ext x
    rfl

theorem display_eye : display (eye : Mat I) = (1 : Matrix I I ENNReal) := by
  ext j i
  simp [display, eye, Matrix.one_apply, eq_comm]

theorem display_product (As : List (Mat I)) :
    display (mprod As) = ((As.map display).reverse).prod := by
  induction As with
  | nil => exact display_eye
  | cons A As ih =>
    simp only [mprod_cons, display_mul, ih, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton]

def OnSteps (P : Operator X bot → Set X → Mat I → Prop) :
    Set X → List (Operator X bot × Mat I) → Prop
  | _, [] => True
  | U, s :: ss => P s.1 U s.2 ∧ OnSteps P (s.1.func '' U) ss

theorem onSteps_iff (P : Operator X bot → Set X → Mat I → Prop)
    (ss : List (Operator X bot × Mat I)) (U : Set X) :
    OnSteps P U ss ↔ ∀ n (hn : n < ss.length),
      P ss[n].1 (actual (ss.map Prod.fst) U n) ss[n].2 := by
  induction ss generalizing U with
  | nil => simp [OnSteps]
  | cons s ss ih =>
    constructor
    · rintro ⟨h, hs⟩ n hn
      cases n with
      | zero => exact h
      | succ n => exact (ih _).mp hs n (Nat.lt_of_succ_lt_succ hn)
    · intro h
      refine ⟨h 0 (by simp), (ih _).mpr ?_⟩
      intro n hn
      exact h (n + 1) (Nat.succ_lt_succ hn)

theorem lip_chain {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : OnSteps (fun φ V M => M ∈ Lip d φ V) U ss) :
    mprod (ss.map Prod.snd) ∈ Lip d (chain (ss.map Prod.fst)) U := by
  induction ss generalizing U with
  | nil => exact identity_lip hU
  | cons s ss ih =>
    exact lip_comp hU hs.1 (ih (image_subset hU) hs.2)

theorem colip_chain {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst))) (hne : U.Nonempty)
    (hs : OnSteps (fun φ V M => M ∈ CoLip d φ V) U ss) :
    mprod (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U := by
  induction ss generalizing U with
  | nil => exact identity_colip hU hne
  | cons s ss ih =>
    exact colip_comp hU hs.1 (ih (image_subset hU) (hne.image _) hs.2)

theorem colip_chain_positive {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) (hlen : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : OnSteps (fun φ V M => M ∈ CoLip d φ V) U ss) :
    mprod (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U := by
  cases ss with
  | nil => exact (hlen rfl).elim
  | cons s ss => exact colip_chain _ hU hs.1.1 hs

theorem lip_chain_indexed {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) (_hlen : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : ∀ n (hn : n < ss.length),
      ss[n].2 ∈ Lip d ss[n].1 (actual (ss.map Prod.fst) U n)) :
    mprod (ss.map Prod.snd) ∈ Lip d (chain (ss.map Prod.fst)) U :=
  lip_chain ss hU ((onSteps_iff _ ss U).mpr hs)

theorem colip_chain_indexed {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) (hlen : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : ∀ n (hn : n < ss.length),
      ss[n].2 ∈ CoLip d ss[n].1 (actual (ss.map Prod.fst) U n)) :
    mprod (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U :=
  colip_chain_positive ss hlen hU ((onSteps_iff _ ss U).mpr hs)

end
end HCH02
```

```lean filename=Paths.lean
import Chains

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

variable {I X : Type} {bot : X} [Fintype I] [Nonempty I]

/-- All intermediate index sequences, without any support or positivity restriction. -/
def Interior (I : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => I × Interior I n

instance interiorFintype : (n : ℕ) → Fintype (Interior I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := interiorFintype n
    exact inferInstanceAs (Fintype (I × Interior I n))

def interiorEquiv : (n : ℕ) → Interior I n ≃ (Fin n → I)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := by intro p; cases p; rfl
      right_inv := by intro f; funext k; exact Fin.elim0 k }
  | n + 1 =>
    { toFun := fun p => Fin.cases p.1 (interiorEquiv n p.2)
      invFun := fun f => (f 0, (interiorEquiv n).symm (fun k => f k.succ))
      left_inv := by intro p; rcases p with ⟨i, p⟩; simp
      right_inv := by
        intro f
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · rfl
        · simp }

def edges : (A : Mat I) → (As : List (Mat I)) → I → I → Interior I As.length → List ENNReal
  | A, [], i, j, _ => [A i j]
  | A, B :: Bs, i, j, p => A i p.1 :: edges B Bs p.1 j p.2

def weight (A : Mat I) (As : List (Mat I)) (i j : I) (p : Interior I As.length) : ENNReal :=
  (edges A As i j p).prod

def AllPositive (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : Prop := ∀ a ∈ edges A As i j p, 0 < a

def HasZero (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : Prop := 0 ∈ edges A As i j p

theorem edges_length (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : (edges A As i j p).length = As.length + 1 := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simpa [edges] using congrArg Nat.succ (ih B p.1 p.2)

theorem weight_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : weight A As i j p = 0 ↔ HasZero A As i j p := by
  simp [weight, HasZero, List.prod_eq_zero_iff]

theorem weight_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I)
    (p : Interior I As.length) : 0 < weight A As i j p ↔ AllPositive A As i j p := by
  simp [weight, AllPositive, pos_iff_ne_zero, List.prod_eq_zero_iff]
  constructor
  · intro h a ha haz
    exact h (haz ▸ ha)
  · intro h hz
    exact h 0 hz rfl

theorem product_expansion (A : Mat I) (As : List (Mat I)) (i j : I) :
    mprod (A :: As) i j = ∑ p : Interior I As.length, weight A As i j p := by
  induction As generalizing A i with
  | nil => simp [weight, edges, Interior]
  | cons B Bs ih =>
    change (∑ k, mprod (B :: Bs) k j * A i k) =
      ∑ p : I × Interior I Bs.length, A i p.1 * weight B Bs p.1 j p.2
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih B k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    exact mul_comm _ _

theorem product_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    mprod (A :: As) i j = 0 ↔ ∀ p : Interior I As.length, HasZero A As i j p := by
  rw [product_expansion, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, weight_zero_iff]

theorem product_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    0 < mprod (A :: As) i j ↔ ∃ p : Interior I As.length, AllPositive A As i j p := by
  rw [product_expansion, Finset.sum_pos_iff]
  simp only [Finset.mem_univ, true_and, weight_positive_iff]

theorem one_step_paths (A : Mat I) (i j : I) :
    (∀ p : Interior I 0, HasZero A [] i j p) ↔ A i j = 0 := by
  simp [Interior, HasZero, edges, eq_comm]

theorem one_step_positive (A : Mat I) (i j : I) :
    (∃ p : Interior I 0, AllPositive A [] i j p) ↔ 0 < A i j := by
  simp [Interior, AllPositive, edges]

theorem local_path_criteria (d : I → X → X → ENNReal)
    (fs : List (Operator X bot)) (A B : Mat I) (As Bs : List (Mat I)) (U : Set X)
    (_hlenL : fs.length = (A :: As).length) (_hlenK : fs.length = (B :: Bs).length)
    (_hU : U ⊆ dom (chain fs))
    (_hL : OnSteps (fun φ V M => M ∈ Lip d φ V) U (fs.zip (A :: As)))
    (_hK : OnSteps (fun φ V M => M ∈ CoLip d φ V) U (fs.zip (B :: Bs))) (i j : I) :
    (mprod (A :: As) i j = 0 ↔ ∀ p : Interior I As.length, HasZero A As i j p) ∧
    (0 < mprod (B :: Bs) i j ↔ ∃ p : Interior I Bs.length, AllPositive B Bs i j p) :=
  ⟨product_zero_iff A As i j, product_positive_iff B Bs i j⟩

end
end HCH02
```

```lean filename=Channels.lean
import Bounds

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
  {d : I → X → X → ENNReal} {φ : Operator X bot}
  {U : Set X} {L K : Mat I}

abbrev Channel (I : Type) := I × I

def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0
def RowDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (j : I) : Prop := ∃ L ∈ Lip d φ U, ∃ i, Row L i j
def ColDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i : I) : Prop := ∃ L ∈ Lip d φ U, ∃ j, Col L i j

theorem diagonal_iff_rows : Diagonal L ↔ ∀ j, Row L j j :=
  ⟨fun h j k hk => h k j hk, fun h i j hij => h j i hij⟩

theorem zero_term (i j : I) (h : L i j = 0) (v : I → ENNReal) : L i j * v i = 0 := by
  rw [h, zero_mul]

theorem erase_zero_term (i j : I) (h : L i j = 0) (v : I → ENNReal) :
    action L v j = ∑ k ∈ Finset.univ.erase i, L k j * v k := by
  simpa [action, h] using
    (Finset.sum_erase_add Finset.univ (fun k => L k j * v k) (Finset.mem_univ i)).symm

theorem row_action {i j : I} (h : Row L i j) (v : I → ENNReal) :
    action L v j = L i j * v i := by
  apply Finset.sum_eq_single i
  · intro k hk hki
    rw [h k hki, zero_mul]
  · simp

theorem row_lip (hL : L ∈ Lip d φ U) {i j : I} (hr : Row L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  simpa only [row_action hr] using hL.2 x hx y hy j

theorem col_contribution {i j : I} (hc : Col L i j) (v : I → ENNReal)
    (k : I) (hk : k ≠ j) : L i k * v i = 0 := zero_term i k (hc k hk) v

theorem diagonal_lip (hL : L ∈ Lip d φ U) (hD : Diagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_lip hL (fun k hk => hD k j hk) hx hy

theorem scalar_two_sided (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    {j : I} (hr : Row L j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy j j, row_lip hL hr hx hy⟩

theorem diagonal_two_sided (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (hD : Diagonal L) : ∀ j x, x ∈ U → ∀ y, y ∈ U →
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j x hx y hy => scalar_two_sided hL hK (fun k hk => hD k j hk) hx hy

theorem finite_diagonal_two_sided (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (hD : Diagonal L) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hfin j).1, (hfin j).2, diagonal_two_sided hL hK hD j⟩

theorem positive_channel (hK : K ∈ CoLip d φ U) {i j : I} (hpos : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  (ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hin)).trans_le (colip_term hK hx hy i j)

theorem reflects_zero (hK : K ∈ CoLip d φ U) (hpos : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hp := positive_channel hK (hpos j) hx hy (pos_iff_ne_zero.mpr hne)
  simpa [hout j] using hp

def Scalars (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}

def singleInf (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : ENNReal := sInf (Scalars d φ U i j)

theorem scalars_upward {i j : I} {a b : ENNReal}
    (ha : a ∈ Scalars d φ U i j) (hab : a ≤ b) : b ∈ Scalars d φ U i j :=
  fun x hx y hy => (ha x hx y hy).trans (mul_le_mul_left hab _)

theorem above_inf_feasible {i j : I} {a : ENNReal}
    (ha : singleInf d φ U i j < a) : a ∈ Scalars d φ U i j := by
  obtain ⟨b, hb, hba⟩ := sInf_lt_iff.mp ha
  exact scalars_upward hb hba.le

theorem zero_input_obstruction {i j : I} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hin : d i x y = 0)
    (hout : 0 < d j (φ.func x) (φ.func y)) :
    Scalars d φ U i j = ∅ ∧ singleInf d φ U i j = ⊤ := by
  have hempty : Scalars d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hin, mul_zero] at h
    exact (not_le_of_gt hout) h
  exact ⟨hempty, by simp [singleInf, hempty]⟩

theorem positive_finite_attained {i j : I}
    (hpos : 0 < singleInf d φ U i j) (hfin : singleInf d φ U i j < ⊤) :
    singleInf d φ U i j ∈ Scalars d φ U i j := by
  obtain ⟨b, hb, _⟩ := sInf_lt_iff.mp hfin
  letI : Nonempty (Scalars d φ U i j) := ⟨⟨b, hb⟩⟩
  intro x hx y hy
  change d j (φ.func x) (φ.func y) ≤ sInf (Scalars d φ U i j) * d i x y
  rw [sInf_eq_iInf']
  rw [ENNReal.iInf_mul (fun _ hz => ?_)]
  · exact le_iInf fun a => a.property x hx y hy
  · exact False.elim ((ne_of_gt hpos) (by simpa only [singleInf, sInf_eq_iInf'] using hz))

theorem zero_inf_positive_feasible {i j : I}
    (hzero : singleInf d φ U i j = 0) {a : ENNReal} (ha : 0 < a) (_hfin : a < ⊤) :
    a ∈ Scalars d φ U i j := above_inf_feasible (hzero ▸ ha)

theorem finite_inf_iff {i j : I} :
    singleInf d φ U i j < ⊤ ↔ ∃ a, a < ⊤ ∧ a ∈ Scalars d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, hfin⟩ := sInf_lt_iff.mp h
    exact ⟨a, hfin, ha⟩
  · rintro ⟨a, hfin, ha⟩
    exact (sInf_le ha).trans_lt hfin

end
end HCH02
```

```lean filename=Counterexample.lean
import Channels

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped Classical

/-- `none` is absorbing; the two ordinary points have infinite input distance
and unit output distance. The two components are indexed by `Bool`. -/
def exampleDist (i : Bool) (x y : Option Bool) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if i then 1 else ⊤

theorem none_ne_some_bool (b : Bool) : (none : Option Bool) ≠ some b := by
  intro h
  cases h

@[reducible] def exampleMetric (i : Bool) : ExtendedPseudoMetric (Option Bool) none (exampleDist i) where
  nonabsorbing := ⟨some false, by simp⟩
  dist_self := by intro x; simp [exampleDist]
  symm := by
    intro x y
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      norm_num [exampleDist, Option.some_ne_none, none_ne_some_bool]
  triangle := by
    intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [exampleDist, Option.some_ne_none, none_ne_some_bool]
  isolate_bot := by intro x hx; simp [exampleDist, hx]

def exampleOp : Operator (Option Bool) none := ident
def exampleU : Set (Option Bool) := {x | x ≠ none}

theorem example_domain : exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp :=
  ⟨⟨some false, by simp [exampleU]⟩, fun _ hx => hx⟩

theorem example_positive_feasible {a : ENNReal} (ha : 0 < a) :
    a ∈ Scalars exampleDist exampleOp exampleU false true := by
  intro x hx y hy
  change x ≠ none at hx
  change y ≠ none at hy
  by_cases hxy : x = y
  · subst y
    simp [exampleOp, ident, exampleDist]
  · simp [exampleOp, ident, exampleDist, hxy, hx, hy, ENNReal.mul_top (ne_of_gt ha)]

theorem example_zero_infeasible :
    0 ∉ Scalars exampleDist exampleOp exampleU false true := by
  intro h
  have hh := h (some false) (by simp [exampleU]) (some true) (by simp [exampleU])
  norm_num [exampleDist, exampleOp, ident, Option.some_ne_none] at hh

theorem example_inf_zero : singleInf exampleDist exampleOp exampleU false true = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  obtain ⟨a, ha, hlt⟩ := exists_between (lt_of_not_ge hn)
  exact (not_lt_of_ge (sInf_le (example_positive_feasible ha))) hlt

theorem zero_not_attained :
    exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp ∧
    singleInf exampleDist exampleOp exampleU false true = 0 ∧
    0 ∉ Scalars exampleDist exampleOp exampleU false true :=
  ⟨example_domain.1, example_domain.2, example_inf_zero, example_zero_infeasible⟩

end
end HCH02
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
        {"file":"Bounds.lean","name":"HCH02.Lip"},
        {"file":"Bounds.lean","name":"HCH02.GlobalLip"}
      ],
      "representation": "Lip是ENNReal系数矩阵的Set，包含U⊆dom φ和全部x,y∈U、输出j的求和上界；GlobalLip取U=dom φ。有限非空指标语境保留。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.CoLip"},
        {"file":"Bounds.lean","name":"HCH02.colip_term"}
      ],
      "representation": "CoLip的成员条件依次为U.Nonempty、U⊆dom φ和所有点对及输出分量的求和下界。系数允许0和∞；colip_term从和中抽取单项下界。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.Mat"},
        {"file":"Bounds.lean","name":"HCH02.display"},
        {"file":"Bounds.lean","name":"HCH02.mmul"},
        {"file":"Bounds.lean","name":"HCH02.action"},
        {"file":"Bounds.lean","name":"HCH02.display_mul"},
        {"file":"Bounds.lean","name":"HCH02.action_mul"}
      ],
      "representation": "Mat I=I→I→ENNReal，M i j输入在前；display M j i=M i j。mmul B A i j=Σk B k j*A i k，display_mul证明与通常矩阵乘法一致，action_mul证明其作用公式。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.eye"},
        {"file":"Bounds.lean","name":"HCH02.mprod"},
        {"file":"Bounds.lean","name":"HCH02.mprod_nil"},
        {"file":"Bounds.lean","name":"HCH02.mprod_singleton"},
        {"file":"Chains.lean","name":"HCH02.display_eye"},
        {"file":"Chains.lean","name":"HCH02.display_product"}
      ],
      "representation": "eye为Kronecker单位矩阵。列表按施行顺序存储，mprod(A::As)=mprod(As)*A；空积为eye，单项积为该项。display_product证明显示矩阵的乘积等于反向列表的通常乘积。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {"file":"Chains.lean","name":"HCH02.chain"},
        {"file":"Chains.lean","name":"HCH02.actual"},
        {"file":"Chains.lean","name":"HCH02.iterImage"},
        {"file":"Chains.lean","name":"HCH02.actual_prefix"},
        {"file":"Chains.lean","name":"HCH02.actual_domain"},
        {"file":"Chains.lean","name":"HCH02.chain_image"},
        {"file":"Chains.lean","name":"HCH02.chain_frozen"},
        {"file":"Chains.lean","name":"HCH02.OnSteps"},
        {"file":"Chains.lean","name":"HCH02.onSteps_iff"}
      ],
      "representation": "列表按φ1,…,φk存储；actual fs U n对应U_(n+1)。证明实际域为前n步像、各步输入在定义域内、全复合像为逐次像，并证明chain fs=冻结OperatorChain fs.reverse。OnSteps仅保存逐步前提，onSteps_iff从全部实际输入域上的逐项条件构造它。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {"file":"Paths.lean","name":"HCH02.Interior"},
        {"file":"Paths.lean","name":"HCH02.interiorEquiv"},
        {"file":"Paths.lean","name":"HCH02.edges"},
        {"file":"Paths.lean","name":"HCH02.edges_length"},
        {"file":"Paths.lean","name":"HCH02.weight"},
        {"file":"Paths.lean","name":"HCH02.AllPositive"},
        {"file":"Paths.lean","name":"HCH02.HasZero"},
        {"file":"Paths.lean","name":"HCH02.product_expansion"}
      ],
      "representation": "非空矩阵列A::As对应n=As.length+1。Interior I As.length与Fin As.length→I等价，包含全部中间序列。edges从固定i到固定j逐层记录恰好n条边；weight为其乘积，AllPositive逐边正，HasZero表示某边为零。n=1的Interior I 0为PUnit。乘积展开为全部路径权重之和。",
      "dependencies": ["HC02-D03","HC02-D04"]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.Channel"},
        {"file":"Channels.lean","name":"HCH02.Row"},
        {"file":"Channels.lean","name":"HCH02.Col"},
        {"file":"Channels.lean","name":"HCH02.Diagonal"},
        {"file":"Channels.lean","name":"HCH02.RowDecoupled"},
        {"file":"Channels.lean","name":"HCH02.ColDecoupled"},
        {"file":"Channels.lean","name":"HCH02.diagonal_iff_rows"}
      ],
      "representation": "Channel=I×I。Row L i j固定输出j且仅输入i可能非零；Col L i j固定输入i且仅输出j可能非零。解耦定义量化合法L和对应唯一可能支撑位置；Diagonal要求所有非对角项为零。",
      "dependencies": ["HC02-D01","HC02-D03"]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.Scalars"},
        {"file":"Channels.lean","name":"HCH02.singleInf"}
      ],
      "representation": "Scalars逐字给出∀x,y∈U的单输入分量标量上界族；singleInf是该Set的sInf，空族自动为∞。纯公式也可用于任意U；在原文U⊆dom φ的范围内就是原定义，与矩阵条目下确界entryInf分开。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.singleton_lip"},
        {"file":"Bounds.lean","name":"HCH02.singleton_lip_iff"}
      ],
      "representation": "以Subsingleton I及给定i表示I={i}，证明合法矩阵条件等价于定义域条件和L i i的标量界；全域情形直接取U=dom φ。",
      "dependencies": ["HC02-D01","HC02-D03"]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.global_lip_restrict"}
      ],
      "representation": "对任意U⊆dom φ，证明GlobalLip d φ⊆Lip d φ U。",
      "dependencies": ["HC02-D01","HC02-P03"]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.lip_restrict"},
        {"file":"Bounds.lean","name":"HCH02.lip_family_antitone"}
      ],
      "representation": "U⊆V时V上每个合法Lip证书仍在U合法，V⊆dom φ由原证书成员条件得到。",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.entryInf"},
        {"file":"Bounds.lean","name":"HCH02.entryInf_mono"}
      ],
      "representation": "entryInf取合法矩阵的第i→j项值集的sInf；证书族扩大给出U⊆V时entryInf(U)≤entryInf(V)，包括空族。",
      "dependencies": ["HC02-D01","HC02-P03"]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.lip_comp"}
      ],
      "representation": "U⊆dom(ψ∘φ)，A在U、B在φ(U)合法时，mmul B A在同一U上界复合。证明使用有限和单调性及action_mul。",
      "dependencies": ["HC02-D01","HC02-D03"]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.colip_degenerate"}
      ],
      "representation": "任意全域co-Lip证书，若所给定义域点对输出j零距且输入i正距，则K i j=0；允许输入距离或系数为∞。",
      "dependencies": ["HC02-D02","HC02-D03"]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.colip_comp"}
      ],
      "representation": "与Lip复合同一实际像域，所选A、B的乘积为复合co-Lip证书；结果非空性由第一步证书取得。",
      "dependencies": ["HC02-D02","HC02-D03"]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.perturb_forward"}
      ],
      "representation": "保留完整扩展伪度量族、公共定义域和逐点δ上界前提；推出ψ点对像距≤φ点对像距+δj+δj。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.perturb_reverse"}
      ],
      "representation": "由伪度量对称性交换算子，得到同一U、δ和点对上的反向扰动界。",
      "dependencies": ["HC02-P08"]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.perturb_lip"}
      ],
      "representation": "在扰动前提下代入φ的所选合法Lip矩阵，得到ψ输出距≤原求和上界+2*δj；所有量均为ENNReal。",
      "dependencies": ["HC02-D01","HC02-D03","HC02-P08"]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.perturb_colip"}
      ],
      "representation": "在同一扰动前提下，将φ的所选合法co-Lip求和下界桥接到ψ输出距+2*δj。",
      "dependencies": ["HC02-D02","HC02-D03","HC02-P09"]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {"file":"Chains.lean","name":"HCH02.lip_chain"},
        {"file":"Chains.lean","name":"HCH02.lip_chain_indexed"}
      ],
      "representation": "非空列表ss逐项存储(φm,Lm)，indexed版本只要求全部实际Um上的逐步合法性和U1⊆dom ck；归纳证明指定mprod合法。通用辅助版本也处理零步。",
      "dependencies": ["HC02-D01","HC02-D04","HC02-D05","HC02-P05","HC02-P14"]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {"file":"Chains.lean","name":"HCH02.colip_chain"},
        {"file":"Chains.lean","name":"HCH02.colip_chain_positive"},
        {"file":"Chains.lean","name":"HCH02.colip_chain_indexed"}
      ],
      "representation": "同样的实际域和指定有序矩阵序列；正长度版本从第一步co-Lip义务推出U1非空，再归纳得到全复合下界，不假设最终下界。",
      "dependencies": ["HC02-D02","HC02-D04","HC02-D05","HC02-P07","HC02-P15"]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.identity_lip"}
      ],
      "representation": "eye在id的任意合法U上是Lip证书，因此包括原文非空U；action_eye证明求和恰等于原分量距离。",
      "dependencies": ["HC02-D01","HC02-D04"]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {"file":"Bounds.lean","name":"HCH02.identity_colip"}
      ],
      "representation": "U.Nonempty和U⊆dom id下，同一eye满足co-Lip定义的全部条件。",
      "dependencies": ["HC02-D02","HC02-D04"]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {"file":"Paths.lean","name":"HCH02.product_zero_iff"},
        {"file":"Paths.lean","name":"HCH02.one_step_paths"},
        {"file":"Paths.lean","name":"HCH02.local_path_criteria"}
      ],
      "representation": "任意非空矩阵列的(i,j)乘积条目为零当且仅当每条完整路径含零边；local_path_criteria保留同一算子链、长度相等、实际域及两族合法证书的正文语境。证明为更一般的代数展开，不依赖复合界；单步明确退化为A i j=0。",
      "dependencies": ["HC02-D03","HC02-D04","HC02-D06"]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {"file":"Paths.lean","name":"HCH02.product_positive_iff"},
        {"file":"Paths.lean","name":"HCH02.one_step_positive"},
        {"file":"Paths.lean","name":"HCH02.local_path_criteria"}
      ],
      "representation": "同一正文链条件下，co-Lip乘积条目正当且仅当存在完整全正路径；证明适用于任意ENNReal矩阵。单步唯一空中间序列对应B i j>0。",
      "dependencies": ["HC02-D03","HC02-D04","HC02-D06"]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.zero_input_obstruction"}
      ],
      "representation": "给定U中输入零距而输出正距的点对，证明Scalars=∅并同时推出singleInf=∞，排除的标量包括∞。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.positive_finite_attained"}
      ],
      "representation": "0<a<∞时证明a∈Scalars，即全部点对上界。替代证明用ENNReal非空下确界乘法交换定理；a>0排除乘数为∞时的零下确界异常。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.scalars_upward"}
      ],
      "representation": "任意可行a及a≤b，由ENNReal乘法单调性证明b可行。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.above_inf_feasible"}
      ],
      "representation": "证明任意λ>singleInf均可行，允许λ=∞；这包含原文正有限下确界语境。证明从sInf严格上界取得较小可行常数，再向上封闭。",
      "dependencies": ["HC02-D08","HC02-P20"]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.zero_inf_positive_feasible"}
      ],
      "representation": "singleInf=0且0<λ<∞时，λ满足全部点对单通道界。",
      "dependencies": ["HC02-D08","HC02-P21"]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {"file":"Counterexample.lean","name":"HCH02.exampleDist"},
        {"file":"Counterexample.lean","name":"HCH02.exampleMetric"},
        {"file":"Counterexample.lean","name":"HCH02.exampleOp"},
        {"file":"Counterexample.lean","name":"HCH02.exampleU"},
        {"file":"Counterexample.lean","name":"HCH02.example_positive_feasible"},
        {"file":"Counterexample.lean","name":"HCH02.zero_not_attained"}
      ],
      "representation": "X=Option Bool，bot=none，I=Bool；两普通点的false分量距离∞、true分量距离1，bot在两分量均∞隔离。证明全部扩展伪度量公理；φ=id，U为两个普通点。false→true通道每个正标量可行，inf=0而0不可行，U非空且合法。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.finite_inf_iff"}
      ],
      "representation": "singleInf<∞当且仅当存在λ<∞属于完整Scalars族；直接用sInf_lt_iff和sInf_le，无须假定下确界取到。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.zero_term"},
        {"file":"Channels.lean","name":"HCH02.erase_zero_term"}
      ],
      "representation": "L i j=0使任意ENNReal输入v i的贡献为0，并证明总和等于删除i后的有限和；取v i=d i x y即可，允许距离∞。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.row_action"},
        {"file":"Channels.lean","name":"HCH02.row_lip"}
      ],
      "representation": "Row L i j将输出j的完整求和化为L i j*d i x y，代入合法Lip界得到全部U中点对的单输入界；i与j独立。",
      "dependencies": ["HC02-D01","HC02-D03","HC02-D07"]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.col_contribution"}
      ],
      "representation": "Col L i j蕴含每个k≠j的L i k*v i=0。该代数结论适用于所选合法证书的所有输入点对，不声称其他输入没有贡献。",
      "dependencies": ["HC02-D03","HC02-D07","HC02-P25"]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.diagonal_lip"}
      ],
      "representation": "Diagonal L及合法Lip证书给出任意j和U中点对的L j j标量上界。",
      "dependencies": ["HC02-D01","HC02-D07","HC02-P26"]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.scalar_two_sided"}
      ],
      "representation": "仅要求Lip矩阵的输出j行Row L j j；co-Lip矩阵无稀疏假设。从其和中抽取K j j项，与Lip行化简合并为双侧界。",
      "dependencies": ["HC02-D01","HC02-D02","HC02-D07","HC02-P26"]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.diagonal_two_sided"},
        {"file":"Channels.lean","name":"HCH02.finite_diagonal_two_sided"}
      ],
      "representation": "Lip的全部对角行条件给出所有j上的双侧界；第二声明额外保留每个L j j、K j j有限，并同时给出这些系数的全部双侧界。",
      "dependencies": ["HC02-D01","HC02-D02","HC02-D07","HC02-P29"]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.positive_channel"}
      ],
      "representation": "合法co-Lip证书中K i j>0与d i x y>0推出输出j距离>0，适用于全部U中点对和∞边界。",
      "dependencies": ["HC02-D02","HC02-D03"]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {"file":"Channels.lean","name":"HCH02.reflects_zero"}
      ],
      "representation": "所有K j j>0时，U中任意x,y的输出GaugeZeroRelated蕴含输入GaugeZeroRelated；不加入分离性，不推出点相等。",
      "dependencies": ["HC02-D02","HC02-P31"]
    }
  ]
}
```

已完整完成并对齐冻结第 2 章与全部 40 项义务；未完成或未确认的数学范围：无。