原文出自 Zhe Li（Glen Li / glenzli）的《The Operator Evolution Theory》。以下源码是对附件所给第 2 章历史快照的 Lean 形式化改编，采用 CC BY 4.0。 [ORCID](https://orcid.org/0009-0006-6536-3453) · [作品主页](https://glenzli.com/books/oet/) · [源码仓库](https://gitlab.com/glenzli/oet-public) · [许可证](https://creativecommons.org/licenses/by/4.0/)

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "hch02"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "formal_oet"
globs = [
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space",
]

[[lean_lib]]
name = "OperatorBounds"
globs = ["OperatorBounds.+"]

[[lean_lib]]
name = "Main"
```

```lean filename=Main.lean
import OperatorBounds.Basic
import OperatorBounds.Chains
import OperatorBounds.Paths
import OperatorBounds.Channels
```

```lean filename=OperatorBounds/Basic.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/- The Operator Evolution Theory, historical Chapter 2, Zhe Li (Glen Li / glenzli).
   Independent Lean formalization of the frozen text, licensed under CC BY 4.0. -/

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal

variable {X I : Type} {bot : X}

abbrev BoundMatrix (I : Type) := I → I → ℝ≥0∞

/-- Display a coefficient at row j and column i when its channel is i → j. -/
def display : BoundMatrix I ≃ Matrix I I ℝ≥0∞ where
  toFun M j i := M i j
  invFun M i j := M j i
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def matrixMul [Fintype I] (B A : BoundMatrix I) : BoundMatrix I :=
  fun i j => ∑ k, B k j * A i k

theorem display_mul [Fintype I] (B A : BoundMatrix I) :
    display (matrixMul B A) = display B * display A := rfl

def identityOp : Operator X bot := OperatorChain []

def composeOp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨fun x => ψ.func (φ.func x), by simp only [φ.preserves_bot, ψ.preserves_bot]⟩

theorem mem_dom_compose {ψ φ : Operator X bot} {x : X} :
    x ∈ dom (composeOp ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  intro e
  exact h (by rw [e, ψ.preserves_bot])

theorem compose_domains {ψ φ : Operator X bot} {U : Set X}
    (h : U ⊆ dom (composeOp ψ φ)) :
    U ⊆ dom φ ∧ operator_image φ U ⊆ dom ψ := by
  refine ⟨fun x hx => (mem_dom_compose.mp (h hx)).1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_dom_compose.mp (h hx)).2

variable [Fintype I] (d : I → X → X → ℝ≥0∞)

noncomputable def weightedDistance (M : BoundMatrix I) (x y : X) (j : I) : ℝ≥0∞ :=
  ∑ i, M i j * d i x y

def lipOn (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {L | U ⊆ dom φ ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
    d j (φ.func x) (φ.func y) ≤ weightedDistance d L x y j}

def lip (φ : Operator X bot) : Set (BoundMatrix I) :=
  lipOn d φ (dom φ)

def coLipOn (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {K | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
    weightedDistance d K x y j ≤ d j (φ.func x) (φ.func y)}

variable {d} {φ ψ : Operator X bot} {U V : Set X}

theorem mem_coLipOn_iff {K : BoundMatrix I} :
    K ∈ coLipOn d φ U ↔ U ≠ ∅ ∧ U ⊆ dom φ ∧
      ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
        weightedDistance d K x y j ≤ d j (φ.func x) (φ.func y) := by
  simp only [coLipOn, Set.mem_setOf_eq, Set.nonempty_iff_ne_empty]

theorem top_coefficient (r : ℝ≥0∞) :
    (⊤ : ℝ≥0∞) * r = if r = 0 then 0 else ⊤ :=
  ENNReal.top_mul'

theorem term_le_weightedDistance (M : BoundMatrix I) (x y : X) (i j : I) :
    M i j * d i x y ≤ weightedDistance d M x y j :=
  Finset.single_le_sum (f := fun k => M k j * d k x y)
    (fun _ _ => zero_le _) (Finset.mem_univ i)

theorem top_channel_bound {M : BoundMatrix I} {x y : X} {i j : I}
    (hM : M i j = ⊤) (hxy : 0 < d i x y) : weightedDistance d M x y j = ⊤ := by
  have h := term_le_weightedDistance (d := d) M x y i j
  rw [hM, ENNReal.top_mul hxy.ne'] at h
  exact top_unique h

theorem singleton_lip (i : I) (hi : ∀ k : I, k = i) (L : BoundMatrix I) :
    L ∈ lip d φ ↔ ∀ ⦃x y⦄, x ∈ dom φ → y ∈ dom φ →
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  letI : Unique I := ⟨⟨i⟩, hi⟩
  have hsum (x y : X) : weightedDistance d L x y i = L i i * d i x y :=
    Fintype.sum_unique _
  constructor
  · intro h x y hx hy
    simpa only [← hsum] using h.2 hx hy i
  · intro h
    refine ⟨Set.Subset.rfl, fun x y hx hy j => ?_⟩
    rw [hi j, hsum]
    exact h hx hy

theorem lipOn_mono (hUV : U ⊆ V) : lipOn d φ V ⊆ lipOn d φ U :=
  fun _ h => ⟨hUV.trans h.1, fun _ _ hx hy j => h.2 (hUV hx) (hUV hy) j⟩

theorem lip_restrict (hU : U ⊆ dom φ) : lip d φ ⊆ lipOn d φ U :=
  lipOn_mono hU

noncomputable def lipEntryInf (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ :=
  sInf ((fun L => L i j) '' lipOn d φ U)

theorem lipEntryInf_mono (hUV : U ⊆ V) (i j : I) :
    lipEntryInf d φ U i j ≤ lipEntryInf d φ V i j :=
  sInf_le_sInf (Set.image_mono (lipOn_mono hUV))

theorem coLip_channel_bound {K : BoundMatrix I} (hK : K ∈ coLipOn d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (term_le_weightedDistance K x y i j).trans (hK.2.2 hx hy j)

theorem coLip_zero_of_collapsed {K : BoundMatrix I} (hK : K ∈ coLipOn d φ (dom φ))
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have h := coLip_channel_bound hK hx hy i j
  rw [hout, nonpos_iff_eq_zero, mul_eq_zero] at h
  exact h.resolve_right hin.ne'

theorem weightedDistance_mul (B A : BoundMatrix I) (x y : X) (j : I) :
    weightedDistance d (matrixMul B A) x y j =
      ∑ k, B k j * weightedDistance d A x y k := by
  simp only [weightedDistance, matrixMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lip_compose {A B : BoundMatrix I} (hU : U ⊆ dom (composeOp ψ φ))
    (hA : A ∈ lipOn d φ U) (hB : B ∈ lipOn d ψ (operator_image φ U)) :
    matrixMul B A ∈ lipOn d (composeOp ψ φ) U := by
  refine ⟨hU, fun x y hx hy j => ?_⟩
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤
    weightedDistance d (matrixMul B A) x y j
  rw [weightedDistance_mul]
  exact (hB.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ j).trans
    (Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 hx hy k) (B k j))

theorem coLip_compose {A B : BoundMatrix I} (hU : U ⊆ dom (composeOp ψ φ))
    (hA : A ∈ coLipOn d φ U) (hB : B ∈ coLipOn d ψ (operator_image φ U)) :
    matrixMul B A ∈ coLipOn d (composeOp ψ φ) U := by
  refine ⟨hA.1, hU, fun x y hx hy j => ?_⟩
  change weightedDistance d (matrixMul B A) x y j ≤
    d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
  rw [weightedDistance_mul]
  exact (Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 hx hy k) (B k j)).trans
    (hB.2.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ j)

def PointwiseClose (d : I → X → X → ℝ≥0∞) (φ ψ : Operator X bot)
    (U : Set X) (δ : I → ℝ≥0∞) : Prop :=
  U ⊆ dom φ ∩ dom ψ ∧ ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j

variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {δ : I → ℝ≥0∞}

include hd

omit [Fintype I] in
theorem pointwiseClose_symm (h : PointwiseClose d φ ψ U δ) :
    PointwiseClose d ψ φ U δ := by
  refine ⟨fun x hx => ⟨(h.1 hx).2, (h.1 hx).1⟩, fun z hz j => ?_⟩
  rw [(hd j).symm (ψ.func z)]
  exact h.2 z hz j

omit [Fintype I] in
theorem perturb_forward (h : PointwiseClose d φ ψ U δ)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  have h₁ := (pointwiseClose_symm hd h).2 x hx j
  have h₂ := h.2 y hy j
  calc
    _ ≤ d j (ψ.func x) (φ.func x) + d j (φ.func x) (ψ.func y) :=
      (hd j).triangle _ _ _
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) :=
      add_le_add h₁ (((hd j).triangle _ (φ.func y) _).trans (add_le_add le_rfl h₂))
    _ = _ := by rw [← add_assoc, add_comm (δ j) (d j (φ.func x) (φ.func y))]

omit [Fintype I] in
theorem perturb_backward (h : PointwiseClose d φ ψ U δ)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j :=
  perturb_forward hd (pointwiseClose_symm hd h) hx hy j

theorem perturb_lip (h : PointwiseClose d φ ψ U δ) {L : BoundMatrix I}
    (hL : L ∈ lipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ weightedDistance d L x y j + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (perturb_forward hd h hx hy j).trans
    (add_le_add (add_le_add (hL.2 hx hy j) le_rfl) le_rfl)

theorem perturb_lip_reverse (h : PointwiseClose d φ ψ U δ) {L : BoundMatrix I}
    (hL : L ∈ lipOn d ψ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ weightedDistance d L x y j + 2 * δ j :=
  perturb_lip hd (pointwiseClose_symm hd h) hL hx hy j

theorem perturb_coLip (h : PointwiseClose d φ ψ U δ) {K : BoundMatrix I}
    (hK : K ∈ coLipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    weightedDistance d K x y j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (hK.2.2 hx hy j).trans (perturb_backward hd h hx hy j)

theorem perturb_coLip_reverse (h : PointwiseClose d φ ψ U δ) {K : BoundMatrix I}
    (hK : K ∈ coLipOn d ψ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    weightedDistance d K x y j ≤ d j (φ.func x) (φ.func y) + 2 * δ j :=
  perturb_coLip hd (pointwiseClose_symm hd h) hK hx hy j

end HCH02
```

```lean filename=OperatorBounds/Chains.lean
import OperatorBounds.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal

variable {X I : Type} {bot : X} {n : ℕ}

noncomputable def matrixOne : BoundMatrix I := by
  classical
  exact fun i j => if i = j then 1 else 0

theorem display_one [DecidableEq I] :
    display (matrixOne : BoundMatrix I) = 1 := by
  ext j i
  simp [display, matrixOne, Matrix.one_apply, eq_comm]

noncomputable def matrixProduct [Fintype I] : List (BoundMatrix I) → BoundMatrix I
  | [] => matrixOne
  | M :: rest => matrixMul (matrixProduct rest) M

@[simp] theorem matrixProduct_nil [Fintype I] :
    matrixProduct ([] : List (BoundMatrix I)) = matrixOne := rfl

@[simp] theorem matrixProduct_singleton [Fintype I] (M : BoundMatrix I) :
    matrixProduct [M] = M := by
  classical
  apply display.injective
  simp [matrixProduct, display_mul, display_one]

/-- The list is in execution order, with the first operator applied first. -/
def orderedComposition (ops : List (Operator X bot)) : Operator X bot :=
  OperatorChain ops.reverse

@[simp] theorem orderedComposition_nil :
    orderedComposition ([] : List (Operator X bot)) = identityOp := rfl

private theorem operatorChain_append_singleton (ops : List (Operator X bot))
    (φ : Operator X bot) :
    OperatorChain (ops ++ [φ]) = composeOp (OperatorChain ops) φ := by
  induction ops with
  | nil => rfl
  | cons ψ ops ih =>
    ext x
    exact congrArg (fun F : Operator X bot => ψ.func (F.func x)) ih

@[simp] theorem orderedComposition_cons (φ : Operator X bot) (ops : List (Operator X bot)) :
    orderedComposition (φ :: ops) = composeOp (orderedComposition ops) φ := by
  rw [orderedComposition, List.reverse_cons, operatorChain_append_singleton]
  rfl

def imageAlong (U : Set X) (ops : List (Operator X bot)) : Set X :=
  ops.foldl (fun V φ => operator_image φ V) U

theorem imageAlong_eq (U : Set X) (ops : List (Operator X bot)) :
    imageAlong U ops = operator_image (orderedComposition ops) U := by
  induction ops generalizing U with
  | nil => simp [imageAlong, orderedComposition, OperatorChain, operator_image]
  | cons φ ops ih =>
    change imageAlong (operator_image φ U) ops = _
    rw [ih, orderedComposition_cons]
    exact Set.image_image (orderedComposition ops).func φ.func U

/-- actualInput U ops m is the image after m applications. Step m uses zero-based indexing. -/
def actualInput (U : Set X) (ops : Fin n → Operator X bot) (m : ℕ) : Set X :=
  imageAlong U ((List.ofFn ops).take m)

@[simp] theorem actualInput_zero (U : Set X) (ops : Fin n → Operator X bot) :
    actualInput U ops 0 = U := rfl

theorem actualInput_succ (U : Set X) (ops : Fin n → Operator X bot) (m : Fin n) :
    actualInput U ops (m.val + 1) = operator_image (ops m) (actualInput U ops m) := by
  unfold actualInput
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp [imageAlong, List.foldl_append, List.getElem_ofFn]

theorem actualInput_full (U : Set X) (ops : Fin n → Operator X bot) :
    actualInput U ops n = operator_image (orderedComposition (List.ofFn ops)) U := by
  have h : (List.ofFn ops).length ≤ n := by simp
  rw [actualInput, List.take_of_length_le h, imageAlong_eq]

private theorem actualInput_shift (U : Set X) (ops : Fin (n + 1) → Operator X bot)
    (m : ℕ) :
    actualInput U ops (m + 1) =
      actualInput (operator_image (ops 0) U) (fun k : Fin n => ops k.succ) m := by
  rw [actualInput, List.ofFn_succ]
  rfl

theorem actualInput_subset_dom (U : Set X) (ops : Fin n → Operator X bot)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops))) (m : Fin n) :
    actualInput U ops m ⊆ dom (ops m) := by
  induction n generalizing U with
  | zero => exact Fin.elim0 m
  | succ n ih =>
    rw [List.ofFn_succ, orderedComposition_cons] at hU
    obtain ⟨hfirst, hrest⟩ := compose_domains hU
    refine Fin.cases hfirst (fun k => ?_) m
    rw [Fin.val_succ, actualInput_shift]
    exact ih _ _ hrest k

def Stepwise (valid : Operator X bot → Set X → BoundMatrix I → Prop)
    (U : Set X) (ops : Fin n → Operator X bot) (M : Fin n → BoundMatrix I) : Prop :=
  ∀ m, valid (ops m) (actualInput U ops m) (M m)

theorem stepwise_succ (valid : Operator X bot → Set X → BoundMatrix I → Prop)
    (U : Set X) (ops : Fin (n + 1) → Operator X bot) (M : Fin (n + 1) → BoundMatrix I) :
    Stepwise valid U ops M ↔ valid (ops 0) U (M 0) ∧
      Stepwise valid (operator_image (ops 0) U)
        (fun k : Fin n => ops k.succ) (fun k => M k.succ) := by
  simp only [Stepwise, Fin.forall_fin_succ, Fin.val_zero, actualInput_zero,
    Fin.val_succ, actualInput_shift]

variable [Fintype I] {d : I → X → X → ℝ≥0∞} {U : Set X}

theorem weightedDistance_one (d : I → X → X → ℝ≥0∞) (x y : X) (j : I) :
    weightedDistance d matrixOne x y j = d j x y := by
  classical
  simp [weightedDistance, matrixOne, ite_mul]

theorem identity_lip (hU : U ⊆ dom (identityOp : Operator X bot)) :
    matrixOne ∈ lipOn d (identityOp (bot := bot)) U := by
  refine ⟨hU, fun x y _ _ j => ?_⟩
  exact (weightedDistance_one d x y j).ge

theorem identity_coLip (hU : U ⊆ dom (identityOp : Operator X bot)) (hNE : U.Nonempty) :
    matrixOne ∈ coLipOn d (identityOp (bot := bot)) U := by
  refine ⟨hNE, hU, fun x y _ _ j => ?_⟩
  exact (weightedDistance_one d x y j).le

theorem empty_chain_bounds (hU : U ⊆ dom (identityOp : Operator X bot)) (hNE : U.Nonempty) :
    matrixProduct [] ∈ lipOn d (orderedComposition (bot := bot) []) U ∧
      matrixProduct [] ∈ coLipOn d (orderedComposition (bot := bot) []) U :=
  ⟨identity_lip hU, identity_coLip hU hNE⟩

private theorem lip_chain_all (ops : Fin n → Operator X bot) (L : Fin n → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L) :
    matrixProduct (List.ofFn L) ∈ lipOn d (orderedComposition (List.ofFn ops)) U := by
  induction n generalizing U with
  | zero =>
    simp only [List.ofFn_zero] at hU ⊢
    exact identity_lip hU
  | succ n ih =>
    simp only [List.ofFn_succ, orderedComposition_cons] at hU ⊢
    obtain ⟨hfirst, hrest⟩ := (stepwise_succ _ _ _ _).mp hL
    exact lip_compose hU hfirst (ih _ _ (compose_domains hU).2 hrest)

theorem lip_chain (ops : Fin (n + 1) → Operator X bot) (L : Fin (n + 1) → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L) :
    matrixProduct (List.ofFn L) ∈ lipOn d (orderedComposition (List.ofFn ops)) U :=
  lip_chain_all ops L hU hL

private theorem coLip_chain_of_nonempty (ops : Fin n → Operator X bot) (K : Fin n → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops))) (hNE : U.Nonempty)
    (hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K) :
    matrixProduct (List.ofFn K) ∈ coLipOn d (orderedComposition (List.ofFn ops)) U := by
  induction n generalizing U with
  | zero =>
    simp only [List.ofFn_zero] at hU ⊢
    exact identity_coLip hU hNE
  | succ n ih =>
    simp only [List.ofFn_succ, orderedComposition_cons] at hU ⊢
    obtain ⟨hfirst, hrest⟩ := (stepwise_succ _ _ _ _).mp hK
    exact coLip_compose hU hfirst
      (ih _ _ (compose_domains hU).2 (hNE.image (ops 0).func) hrest)

theorem coLip_chain (ops : Fin (n + 1) → Operator X bot) (K : Fin (n + 1) → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K) :
    matrixProduct (List.ofFn K) ∈ coLipOn d (orderedComposition (List.ofFn ops)) U :=
  coLip_chain_of_nonempty ops K hU ((stepwise_succ _ _ _ _).mp hK).1.1 hK

end HCH02
```

```lean filename=OperatorBounds/Paths.lean
import OperatorBounds.Chains
import Mathlib.Data.Fintype.BigOperators

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal

variable {X I : Type} {bot : X} {n : ℕ}

/-- A path with n + 1 edges has n unrestricted intermediate indices. -/
def pathVertex (i j : I) (p : Fin n → I) : Fin (n + 2) → I :=
  Fin.cons i (Fin.snoc p j)

@[simp] theorem pathVertex_start (i j : I) (p : Fin n → I) :
    pathVertex i j p 0 = i := by simp [pathVertex]

@[simp] theorem pathVertex_middle (i j : I) (p : Fin n → I) (m : Fin n) :
    pathVertex i j p m.castSucc.succ = p m := by simp [pathVertex]

@[simp] theorem pathVertex_end (i j : I) (p : Fin n → I) :
    pathVertex i j p (Fin.last (n + 1)) = j := by
  rw [← Fin.succ_last]
  simp [pathVertex]

def pathTupleEquiv (i j : I) :
    (Fin n → I) ≃ {q : Fin (n + 2) → I // q 0 = i ∧ q (Fin.last (n + 1)) = j} where
  toFun p := ⟨pathVertex i j p, pathVertex_start i j p, pathVertex_end i j p⟩
  invFun q m := q.val m.castSucc.succ
  left_inv p := funext (pathVertex_middle i j p)
  right_inv q := by
    apply Subtype.ext
    funext m
    change pathVertex i j (fun k : Fin n => q.val k.castSucc.succ) m = q.val m
    cases m using Fin.cases with
    | zero => exact (pathVertex_start _ _ _).trans q.property.1.symm
    | succ m =>
      cases m using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, pathVertex_end]
        exact q.property.2.symm
      | cast k => exact pathVertex_middle _ _ _ k

def pathEdge (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I)
    (m : Fin (n + 1)) : ℝ≥0∞ :=
  M m (pathVertex i j p m.castSucc) (pathVertex i j p m.succ)

noncomputable def pathWeight (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) :
    ℝ≥0∞ :=
  ∏ m, pathEdge M i j p m

def PathHasZero (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) : Prop :=
  ∃ m, pathEdge M i j p m = 0

def PathPositive (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) : Prop :=
  ∀ m, 0 < pathEdge M i j p m

theorem empty_path_unique (p : Fin 0 → I) : p = (fun m => Fin.elim0 m) :=
  funext fun m => Fin.elim0 m

@[simp] theorem pathWeight_singleton (M : Fin 1 → BoundMatrix I) (i j : I)
    (p : Fin 0 → I) : pathWeight M i j p = M 0 i j := by
  rw [pathWeight, Fin.prod_univ_one]
  change M 0 (pathVertex i j p 0) (pathVertex i j p (Fin.last 1)) = _
  rw [pathVertex_start, pathVertex_end]

private theorem pathVertex_succ_cons (i j k : I) (p : Fin n → I) (m : Fin (n + 2)) :
    pathVertex i j (Fin.cons k p) m.succ = pathVertex k j p m := by
  simp [pathVertex, ← Fin.cons_snoc_eq_snoc_cons]

private theorem pathEdge_cons_first (M : Fin (n + 2) → BoundMatrix I)
    (i j k : I) (p : Fin n → I) : pathEdge M i j (Fin.cons k p) 0 = M 0 i k := by
  change M 0 (pathVertex i j (Fin.cons k p) 0)
    (pathVertex i j (Fin.cons k p) (0 : Fin (n + 1)).castSucc.succ) = _
  rw [pathVertex_start, pathVertex_middle, Fin.cons_zero]

private theorem pathWeight_cons (M : Fin (n + 2) → BoundMatrix I) (i j k : I)
    (p : Fin n → I) :
    pathWeight M i j (Fin.cons k p) =
      M 0 i k * pathWeight (fun m : Fin (n + 1) => M m.succ) k j p := by
  unfold pathWeight
  rw [Fin.prod_univ_succ, pathEdge_cons_first]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  unfold pathEdge
  rw [Fin.castSucc_succ, pathVertex_succ_cons, pathVertex_succ_cons]

theorem pathWeight_eq_zero_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) :
    pathWeight M i j p = 0 ↔ PathHasZero M i j p := by
  simp [pathWeight, PathHasZero, Finset.prod_eq_zero_iff]

theorem pathWeight_pos_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) (p : Fin n → I) :
    0 < pathWeight M i j p ↔ PathPositive M i j p := by
  rw [pos_iff_ne_zero, Ne, pathWeight_eq_zero_iff]
  simp only [PathHasZero, PathPositive, not_exists, pos_iff_ne_zero]

theorem singleton_path_criteria (M : Fin 1 → BoundMatrix I) (i j : I) (p : Fin 0 → I) :
    (PathHasZero M i j p ↔ M 0 i j = 0) ∧ (PathPositive M i j p ↔ 0 < M 0 i j) := by
  rw [← pathWeight_eq_zero_iff, ← pathWeight_pos_iff, pathWeight_singleton]
  exact ⟨Iff.rfl, Iff.rfl⟩

variable [Fintype I]

theorem matrixProduct_eq_path_sum (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    matrixProduct (List.ofFn M) i j = ∑ p : Fin n → I, pathWeight M i j p := by
  classical
  induction n generalizing i j with
  | zero =>
    letI : Unique (Fin 0 → I) := ⟨⟨fun m => Fin.elim0 m⟩, empty_path_unique⟩
    simp [List.ofFn_succ]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => I)
    calc
      _ = ∑ k : I, matrixProduct (List.ofFn fun m : Fin (n + 1) => M m.succ) k j * M 0 i k := by
        rw [List.ofFn_succ]
        rfl
      _ = ∑ k : I, ∑ p : Fin n → I, pathWeight M i j (Fin.cons k p) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [ih, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        rw [pathWeight_cons, mul_comm]
      _ = _ := by
        rw [← Fintype.sum_prod_type']
        exact e.sum_comp (fun p => pathWeight M i j p)

theorem matrixProduct_zero_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    matrixProduct (List.ofFn M) i j = 0 ↔ ∀ p, PathHasZero M i j p := by
  rw [matrixProduct_eq_path_sum, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le _)]
  simp [pathWeight_eq_zero_iff]

theorem matrixProduct_pos_iff (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    0 < matrixProduct (List.ofFn M) i j ↔ ∃ p, PathPositive M i j p := by
  rw [matrixProduct_eq_path_sum, Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
  simp [pathWeight_pos_iff]

theorem chain_lip_zero_iff {d : I → X → X → ℝ≥0∞} {U : Set X}
    (ops : Fin (n + 1) → Operator X bot) (L K : Fin (n + 1) → BoundMatrix I)
    (_hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (_hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L)
    (_hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K)
    (i j : I) :
    matrixProduct (List.ofFn L) i j = 0 ↔ ∀ p, PathHasZero L i j p :=
  matrixProduct_zero_iff L i j

theorem chain_coLip_pos_iff {d : I → X → X → ℝ≥0∞} {U : Set X}
    (ops : Fin (n + 1) → Operator X bot) (L K : Fin (n + 1) → BoundMatrix I)
    (_hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (_hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L)
    (_hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K)
    (i j : I) :
    0 < matrixProduct (List.ofFn K) i j ↔ ∃ p, PathPositive K i j p :=
  matrixProduct_pos_iff K i j

end HCH02
```

```lean filename=OperatorBounds/Channels.lean
import OperatorBounds.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Option

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal NNReal

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {φ : Operator X bot} {U : Set X} {i j : I}

abbrev Channel (I : Type) := I × I

def RowSparse (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k ≠ i, L k j = 0

def ColumnSparse (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k ≠ j, L i k = 0

def Diagonal (L : BoundMatrix I) : Prop :=
  ∀ i j, i ≠ j → L i j = 0

def scalarFeasible (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : Set ℝ≥0∞ :=
  {a | U ⊆ dom φ ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    d j (φ.func x) (φ.func y) ≤ a * d i x y}

noncomputable def channelConstant (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ :=
  sInf (scalarFeasible d φ U i j)

theorem channelConstant_of_empty (h : scalarFeasible d φ U i j = ∅) :
    channelConstant d φ U i j = ⊤ := by simp [channelConstant, h]

theorem scalar_infeasible_of_zero {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (φ.func x) (φ.func y)) :
    scalarFeasible d φ U i j = ∅ ∧ channelConstant d φ U i j = ⊤ := by
  have hempty : scalarFeasible d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a h
    have hxy := h.2 hx hy
    rw [hin, mul_zero] at hxy
    exact hout.not_ge hxy
  exact ⟨hempty, channelConstant_of_empty hempty⟩

theorem scalar_upward {a b : ℝ≥0∞} (ha : a ∈ scalarFeasible d φ U i j) (h : a ≤ b) :
    b ∈ scalarFeasible d φ U i j :=
  ⟨ha.1, fun x y hx hy => (ha.2 hx hy).trans (mul_le_mul_left h (d i x y))⟩

theorem scalar_above_inf {a : ℝ≥0∞} (h : channelConstant d φ U i j < a) :
    a ∈ scalarFeasible d φ U i j := by
  obtain ⟨b, hb, hba⟩ := sInf_lt_iff.mp h
  exact scalar_upward hb hba.le

theorem scalar_above_positive_finite_inf {a : ℝ≥0∞}
    (_hpos : 0 < channelConstant d φ U i j)
    (_hfin : channelConstant d φ U i j < ⊤)
    (h : channelConstant d φ U i j < a) : a ∈ scalarFeasible d φ U i j :=
  scalar_above_inf h

theorem scalar_of_zero_inf {a : ℝ≥0∞} (hzero : channelConstant d φ U i j = 0)
    (ha : 0 < a) (_haFin : a < ⊤) : a ∈ scalarFeasible d φ U i j :=
  scalar_above_inf (hzero.symm ▸ ha)

theorem scalar_attains_inf (hpos : 0 < channelConstant d φ U i j)
    (hfin : channelConstant d φ U i j < ⊤) :
    channelConstant d φ U i j ∈ scalarFeasible d φ U i j := by
  have htop := scalar_above_inf hfin
  refine ⟨htop.1, fun x y hx hy => ?_⟩
  rcases eq_or_ne (d i x y) 0 with hzero | hzero
  · simpa only [hzero, mul_zero] using htop.2 hx hy
  rcases eq_or_ne (d i x y) ⊤ with hinf | hinf
  · rw [hinf, ENNReal.mul_top hpos.ne']
    exact le_top
  have hdiv (a : ℝ≥0∞) :
      d j (φ.func x) (φ.func y) / d i x y ≤ a ↔
        d j (φ.func x) (φ.func y) ≤ a * d i x y :=
    ENNReal.div_le_iff_le_mul (Or.inl hzero) (Or.inl hinf)
  exact (hdiv _).mp (le_sInf fun a ha => (hdiv a).mpr (ha.2 hx hy))

theorem channelConstant_finite_iff :
    channelConstant d φ U i j < ⊤ ↔
      ∃ a < ⊤, a ∈ scalarFeasible d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, haFin⟩ := sInf_lt_iff.mp h
    exact ⟨a, haFin, ha⟩
  · rintro ⟨a, ha, hfeas⟩
    exact (sInf_le hfeas).trans_lt ha

private def exampleDist (i : Bool) (x y : Option Bool) : ℝ≥0∞ :=
  if x = y then 0 else if i = false ∨ x = none ∨ y = none then ⊤ else 1

private theorem exampleDist_metric (i : Bool) :
    ExtendedPseudoMetric (Option Bool) none (exampleDist i) := by
  constructor
  · exact ⟨some false, by simp⟩
  · intro x
    simp [exampleDist]
  · intro x y
    simp [exampleDist, eq_comm, or_comm]
  · intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [exampleDist]
  · intro x hx
    simp [exampleDist, hx]

theorem zero_inf_not_attained :
    ∃ (e : Bool → Option Bool → Option Bool → ℝ≥0∞)
      (ψ : Operator (Option Bool) none) (V : Set (Option Bool)),
      (∀ k, ExtendedPseudoMetric (Option Bool) none (e k)) ∧
      V.Nonempty ∧ V ⊆ dom ψ ∧ channelConstant e ψ V false true = 0 ∧
      (0 : ℝ≥0∞) ∉ scalarFeasible e ψ V false true := by
  let ψ : Operator (Option Bool) none := identityOp
  have hx : some false ∈ dom ψ := by
    change some false ≠ none
    simp
  have hy : some true ∈ dom ψ := by
    change some true ≠ none
    simp
  have hpositive (a : ℝ≥0∞) (ha : 0 < a) :
      a ∈ scalarFeasible exampleDist ψ (dom ψ) false true := by
    refine ⟨Set.Subset.rfl, fun x y _ _ => ?_⟩
    change exampleDist true x y ≤ a * exampleDist false x y
    by_cases h : x = y
    · simp [exampleDist, h]
    · simp [exampleDist, h, ENNReal.mul_top ha.ne']
  refine ⟨exampleDist, ψ, dom ψ, exampleDist_metric, ⟨_, hx⟩, Set.Subset.rfl, ?_, ?_⟩
  · apply le_antisymm _ (zero_le _)
    by_contra! h
    obtain ⟨a, ha, hainf⟩ := exists_between h
    exact hainf.not_ge (sInf_le (hpositive a ha))
  · intro h
    have hxy := h.2 hx hy
    change exampleDist true (some false) (some true) ≤
      0 * exampleDist false (some false) (some true) at hxy
    simp [exampleDist] at hxy

variable [Fintype I]

def RowDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ lipOn d φ U, ∃ i, RowSparse L i j

def ColumnDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ lipOn d φ U, ∃ j, ColumnSparse L i j

def FullyDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  L ∈ lipOn d φ U ∧ Diagonal L

variable {L K : BoundMatrix I} {x y : X}

omit [Fintype I] in
theorem zero_channel_term (d : I → X → X → ℝ≥0∞) (hz : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by simp [hz]

open scoped Classical in
theorem erase_zero_channel (hz : L i j = 0) :
    weightedDistance d L x y j = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  unfold weightedDistance
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), zero_channel_term d hz, add_zero]

theorem lip_of_sparse_row (hL : L ∈ lipOn d φ U) (hrow : RowSparse L i j)
    (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  have heq : weightedDistance d L x y j = L i j * d i x y :=
    Finset.sum_eq_single i (fun k _ hk => zero_channel_term d (hrow k hk) x y)
      (fun h => (h (Finset.mem_univ i)).elim)
  exact (hL.2 hx hy j).trans_eq heq

omit [Fintype I] in
theorem column_contributions (d : I → X → X → ℝ≥0∞) (hcol : ColumnSparse L i j)
    (x y : X) (k : I) (hk : k ≠ j) :
    L i k * d i x y = 0 :=
  zero_channel_term d (hcol k hk) x y

theorem lip_of_diagonal (hL : L ∈ lipOn d φ U) (hdiag : Diagonal L)
    (j : I) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_of_sparse_row hL (fun k hk => hdiag k j hk) hx hy

theorem diagonal_row_two_sided (hL : L ∈ lipOn d φ U) (hK : K ∈ coLipOn d φ U)
    (hrow : RowSparse L j j) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨coLip_channel_bound hK hx hy j j, lip_of_sparse_row hL hrow hx hy⟩

theorem all_diagonal_two_sided (hL : L ∈ lipOn d φ U) (hK : K ∈ coLipOn d φ U)
    (hdiag : Diagonal L) :
    ∀ j x y, x ∈ U → y ∈ U →
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ _ hx hy => diagonal_row_two_sided hL hK (fun k hk => hdiag k j hk) hx hy

theorem finite_diagonal_two_sided (hL : L ∈ lipOn d φ U) (hK : K ∈ coLipOn d φ U)
    (hdiag : Diagonal L) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∃ l k : I → ℝ≥0,
      (∀ j, (l j : ℝ≥0∞) = L j j ∧ (k j : ℝ≥0∞) = K j j) ∧
      ∀ j x y, x ∈ U → y ∈ U →
        (k j : ℝ≥0∞) * d j x y ≤ d j (φ.func x) (φ.func y) ∧
          d j (φ.func x) (φ.func y) ≤ (l j : ℝ≥0∞) * d j x y := by
  have hl (j : I) := ENNReal.coe_toNNReal (hfin j).1.ne
  have hk (j : I) := ENNReal.coe_toNNReal (hfin j).2.ne
  refine ⟨fun j => (L j j).toNNReal, fun j => (K j j).toNNReal,
    fun j => ⟨hl j, hk j⟩, fun j x y hx hy => ?_⟩
  rw [hl, hk]
  exact all_diagonal_two_sided hL hK hdiag j x y hx hy

theorem coLip_preserves_positive (hK : K ∈ coLipOn d φ U)
    (hpos : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  (pos_iff_ne_zero.mpr (mul_ne_zero hpos.ne' hin.ne')).trans_le
    (coLip_channel_bound hK hx hy i j)

theorem coLip_reflects_gauge_zero (hK : K ∈ coLipOn d φ U)
    (hpos : ∀ j, 0 < K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra h
  exact (coLip_preserves_positive hK (hpos j) hx hy (pos_iff_ne_zero.mpr h)).ne' (hout j)

end HCH02
```

```json filename=alignment.json
{
  "case_id":"HCH02",
  "version":"0.1.0",
  "items":[
    {"id":"HC02-D01","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.lip"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.lipOn"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.top_coefficient"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.top_channel_bound"}],"representation":"在有限非空 I 上取分量 d_i 满足 ExtendedPseudoMetric。lipOn 对保持 bot 的 φ 要求 U⊆dom φ，且对 U 内每个点对和每个输出行满足 ENNReal 加权和上界。lip 取 U=dom φ。∞ 乘零为零，∞ 乘正输入距使该行和为 ∞。","dependencies":["HC02-D03"]},
    {"id":"HC02-D02","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.coLipOn"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.mem_coLipOn_iff"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.coLip_channel_bound"}],"representation":"对同一 ENNReal 系数空间，加入 U≠∅、U⊆dom φ，并要求各点对、各行的加权和不超过输出距。成员等价定理按原文写出非空条件，且单项小于等于该行和。","dependencies":["HC02-D03"]},
    {"id":"HC02-D03","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.BoundMatrix"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.display"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.matrixMul"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.display_mul"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.weightedDistance"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.term_le_weightedDistance"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.weightedDistance_mul"}],"representation":"M i j 的输入为 i、输出为 j。display 是双向等价，普通矩阵取第 j 行第 i 列。matrixMul B A 在 (i,j) 取 Σk B k j·A i k，与普通矩阵乘法一致。","dependencies":[]},
    {"id":"HC02-D04","status":"complete","declarations":[{"file":"OperatorBounds/Chains.lean","name":"HCH02.matrixOne"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.display_one"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.matrixProduct"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.matrixProduct_nil"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.matrixProduct_singleton"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.weightedDistance_one"}],"representation":"matrixOne 是 δij。列表按施行顺序给出，空列表乘积为单位，头矩阵右乘于尾列表的乘积，故得到 Mk⋯M1。单步乘积等于唯一矩阵。","dependencies":["HC02-D03"]},
    {"id":"HC02-D05","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.identityOp"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.orderedComposition"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.orderedComposition_nil"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.orderedComposition_cons"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.actualInput"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.actualInput_zero"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.actualInput_succ"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.actualInput_full"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.actualInput_subset_dom"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.Stepwise"},{"file":"OperatorBounds/Chains.lean","name":"HCH02.stepwise_succ"}],"representation":"Fin k 按施行顺序列举算子和矩阵。actualInput U ops m 是原文 U_{m+1}，零步为 U，递推取实际像。起始 U⊆dom ck 推出每步输入域合法，末域等于 ck(U)。Stepwise 由各步实际域上的界组成。","dependencies":["HC02-D03","HC02-P05"]},
    {"id":"HC02-D06","status":"complete","declarations":[{"file":"OperatorBounds/Paths.lean","name":"HCH02.pathTupleEquiv"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.pathEdge"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.pathWeight"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.PathHasZero"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.PathPositive"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.empty_path_unique"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.singleton_path_criteria"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.matrixProduct_eq_path_sum"}],"representation":"n+1 步用 Fin n→I 作全部中间序列，与固定两端的完整顶点列双射。边取相邻顶点处的各步系数，权重为边积，谓词分别为存在零边与所有边正。一步时中间序列唯一，且矩阵条目是所有路径权重之和。","dependencies":["HC02-D03","HC02-D04"]},
    {"id":"HC02-D07","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.Channel"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.RowSparse"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.ColumnSparse"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.Diagonal"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.RowDecoupled"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.ColumnDecoupled"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.FullyDecoupled"}],"representation":"通道为 I×I。固定输出行只允许输入 i 非零，固定输入列只允许输出 j 非零。两种解耦分别存在合法 L 和相应位置。完全解耦要求所选 L 合法且所有非对角项为零。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D08","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalarFeasible"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.channelConstant"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.channelConstant_of_empty"}],"representation":"在 U⊆dom φ 上，Sij 由对 U 内所有点对成立的单输入分量标量不等式定义，系数取 ENNReal。常数是 sInf Sij，空族给 ∞。","dependencies":[]},
    {"id":"HC02-P01","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.singleton_lip"}],"representation":"给定 i 且每个指标等于 i，全域 Lip 成员资格等价于 dom φ 内各点对的单一 d_i 上界。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P02","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.lip_restrict"}],"representation":"若 U⊆dom φ，全域 Lip 集包含于在 U 上的 Lip 集。","dependencies":["HC02-D01","HC02-D03","HC02-P03"]},
    {"id":"HC02-P03","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.lipOn_mono"}],"representation":"U⊆V 时，V 上证书的合法性同时给出 V⊆dom φ，故任一该证书在 U 上合法。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P04","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.lipEntryInf"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.lipEntryInf_mono"}],"representation":"对证书集取 (i,j) 条目的像再取下确界。U⊆V 令 U 上的下确界小于等于 V 上的。","dependencies":["HC02-D01","HC02-D03","HC02-P03"]},
    {"id":"HC02-P05","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.composeOp"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.mem_dom_compose"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.compose_domains"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.lip_compose"}],"representation":"以 U⊆dom(ψ∘φ) 为起始条件，次域为 φ(U)。两步合法 A、B 给出复合在 U 上的合法 BA。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P06","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.coLip_zero_of_collapsed"}],"representation":"对 dom φ 内所有满足输入 i 距正、输出 j 距零的点对，任一在全定义域合法的 K 均有 K i j=0。","dependencies":["HC02-D02","HC02-D03"]},
    {"id":"HC02-P07","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.coLip_compose"}],"representation":"次域为起始 U 的 φ-像。两步各满足含非空条件的下界，从而 BA 是 ψ∘φ 在 U 上合法的 co-Lip 矩阵。","dependencies":["HC02-D02","HC02-D03","HC02-P05"]},
    {"id":"HC02-P08","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.PointwiseClose"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.pointwiseClose_symm"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.perturb_forward"}],"representation":"U 在两算子的公共定义域内。固定 δ，对所有 z∈U 和 j 以 δ_j 控制同点输出差。则 ψ 的点对像距不超过 φ 的点对像距加两次 δ_j。","dependencies":[]},
    {"id":"HC02-P09","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.perturb_backward"}],"representation":"相同前提下，用同一 δ 交换两算子，取得 φ 的点对像距的对应上界。","dependencies":["HC02-P08"]},
    {"id":"HC02-P10","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.perturb_lip"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.perturb_lip_reverse"}],"representation":"在同一 U 内，用 φ 的 Lip 行和替换扰动上界中的 φ 像距，加 2δ_j 后控制 ψ。也证明交换方向。","dependencies":["HC02-D01","HC02-D03","HC02-P08"]},
    {"id":"HC02-P11","status":"complete","declarations":[{"file":"OperatorBounds/Basic.lean","name":"HCH02.perturb_coLip"},{"file":"OperatorBounds/Basic.lean","name":"HCH02.perturb_coLip_reverse"}],"representation":"在同一非空 U 内，φ 的 co-Lip 行和不超过 ψ 的像距加 2δ_j。也证明交换方向。","dependencies":["HC02-D02","HC02-D03","HC02-P08","HC02-P09"]},
    {"id":"HC02-P12","status":"complete","declarations":[{"file":"OperatorBounds/Chains.lean","name":"HCH02.lip_chain"}],"representation":"正长度 Fin(n+1) 链从 U⊆dom ck 出发。每步实际输入域上的 Lip 成员资格推出施行顺序对应的矩阵乘积在 U 上合法。","dependencies":["HC02-D01","HC02-D03","HC02-D04","HC02-D05","HC02-P05","HC02-P14"]},
    {"id":"HC02-P13","status":"complete","declarations":[{"file":"OperatorBounds/Chains.lean","name":"HCH02.coLip_chain"}],"representation":"相同正长度与实际域条件下，各步下界成员资格给出非空性，指定矩阵乘积是复合在起始 U 上的合法下界。","dependencies":["HC02-D02","HC02-D03","HC02-D04","HC02-D05","HC02-P05","HC02-P07","HC02-P15"]},
    {"id":"HC02-P14","status":"complete","declarations":[{"file":"OperatorBounds/Chains.lean","name":"HCH02.identity_lip"}],"representation":"空复合为恒等算子，空积为 δij。任取 U⊆dom id 即有 Lip 上界，故覆盖原文的非空 U。","dependencies":["HC02-D01","HC02-D03","HC02-D04","HC02-D05"]},
    {"id":"HC02-P15","status":"complete","declarations":[{"file":"OperatorBounds/Chains.lean","name":"HCH02.identity_coLip"}],"representation":"对非空 U⊆dom id，同一 δij 给出合法下界。","dependencies":["HC02-D02","HC02-D03","HC02-D04","HC02-D05"]},
    {"id":"HC02-P16","status":"complete","declarations":[{"file":"OperatorBounds/Paths.lean","name":"HCH02.matrixProduct_zero_iff"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.chain_lip_zero_iff"}],"representation":"正长度实际证书链中，Lip 乘积的 (i,j) 条目等于零当且仅当每个中间序列含零边。一步由唯一空序列退化为单条目等于零。","dependencies":["HC02-D01","HC02-D02","HC02-D03","HC02-D04","HC02-D05","HC02-D06"]},
    {"id":"HC02-P17","status":"complete","declarations":[{"file":"OperatorBounds/Paths.lean","name":"HCH02.matrixProduct_pos_iff"},{"file":"OperatorBounds/Paths.lean","name":"HCH02.chain_coLip_pos_iff"}],"representation":"同一链的 co-Lip 乘积条目为正当且仅当存在一个中间序列使所有边正。一步时唯一空序列只检验单条目。","dependencies":["HC02-D01","HC02-D02","HC02-D03","HC02-D04","HC02-D05","HC02-D06"]},
    {"id":"HC02-P18","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalar_infeasible_of_zero"}],"representation":"U 内若输入 i 距为零且输出 j 距为正，则所有 ENNReal 系数均不可行，所以 Sij=∅ 且 aij=∞。","dependencies":["HC02-D08"]},
    {"id":"HC02-P19","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalar_attains_inf"}],"representation":"在 0<aij<∞ 时 aij∈Sij。按输入距为零、有限正、无穷三种情况证明对所有点对成立。","dependencies":["HC02-D08","HC02-P21"]},
    {"id":"HC02-P20","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalar_upward"}],"representation":"Sij 中任一系数的任一 ENNReal 上界仍满足相同作用域内的全部点对不等式。","dependencies":["HC02-D08"]},
    {"id":"HC02-P21","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalar_above_inf"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalar_above_positive_finite_inf"}],"representation":"在 0<aij<∞ 时任意 c>aij 可行，含 c=∞。先由下确界取得一个小于 c 的可行常数，再使用向上封闭性。","dependencies":["HC02-D08","HC02-P20"]},
    {"id":"HC02-P22","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.scalar_of_zero_inf"}],"representation":"aij=0 且 0<c<∞ 时，c 是同一作用域的标量证书。","dependencies":["HC02-D08","HC02-P21"]},
    {"id":"HC02-P23","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.zero_inf_not_attained"}],"representation":"I=Bool，X=Option Bool，none 为吸收元。恒等算子的非空定义域含两个普通点，false 分量给它们 ∞ 距，true 分量给 1 距。证明各分量全部伪度量条件、aij=0 以及 0∉Sij。","dependencies":["HC02-D05","HC02-D08"]},
    {"id":"HC02-P24","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.channelConstant_finite_iff"}],"representation":"aij<∞ 当且仅当存在一个 c<∞ 属于 Sij，因而满足作用域上全部点对的同一标量界。","dependencies":["HC02-D08"]},
    {"id":"HC02-P25","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.zero_channel_term"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.erase_zero_channel"}],"representation":"L i j=0 使该项为零，输入距可为 ∞。加权和等于从 univ 擦除 i 后在同一输出 j 上的加权和。","dependencies":["HC02-D03"]},
    {"id":"HC02-P26","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.lip_of_sparse_row"}],"representation":"任意输入 i 和输出 j，合法 L 的 j 行其余输入条目全零时，得到对 U 内所有点对的单项标量界。","dependencies":["HC02-D01","HC02-D03","HC02-D07","HC02-P25"]},
    {"id":"HC02-P27","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.column_contributions"}],"representation":"若输入 i 的列仅输出 j 处可能非零，则任何 k≠j 和任意点对的第 k 行中输入 i 的贡献等于零。","dependencies":["HC02-D03","HC02-D07","HC02-P25"]},
    {"id":"HC02-P28","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.lip_of_diagonal"}],"representation":"合法 L 为对角矩阵时，每一分量都有 U 上的标量上界 L j j·d_j。","dependencies":["HC02-D01","HC02-D03","HC02-D07","HC02-P26"]},
    {"id":"HC02-P29","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.diagonal_row_two_sided"}],"representation":"L、K 在 U 上合法。只要求 L 在 j 行的非对角项为零，逐点对得 K j j·d_j≤输出距≤L j j·d_j。","dependencies":["HC02-D01","HC02-D02","HC02-D03","HC02-D07","HC02-P26"]},
    {"id":"HC02-P30","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.all_diagonal_two_sided"},{"file":"OperatorBounds/Channels.lean","name":"HCH02.finite_diagonal_two_sided"}],"representation":"将 j 行条件施于所有 j，得到同时成立的双侧界。若两套对角系数都有限，构造恰好等于这些系数的 ℝ≥0 系数族并保留全部不等式。","dependencies":["HC02-D01","HC02-D02","HC02-D03","HC02-D07","HC02-P29"]},
    {"id":"HC02-P31","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.coLip_preserves_positive"}],"representation":"对合法 K 且 K i j>0，U 内任意输入 i 距为正的点对在输出 j 的像距仍为正。","dependencies":["HC02-D02","HC02-D03"]},
    {"id":"HC02-P32","status":"complete","declarations":[{"file":"OperatorBounds/Channels.lean","name":"HCH02.coLip_reflects_gauge_zero"}],"representation":"若合法 K 的全部对角项正，则 U 内像点的 GaugeZeroRelated 蕴含原点的 GaugeZeroRelated。","dependencies":["HC02-D02","HC02-D03","HC02-P31"]}
  ]
}
```

已完整形式化并严格对齐冻结原文第 2 章的 **40 项义务**。有限复合采用从零开始的 `Fin` 索引，逐步像域由递推定理对应原文，索引路径由双射对应固定两端的完整顶点序列。纯代数引理可直接特化到原文的有限非空规范族。

使用 Lean 4.29.1、指定 mathlib 提交和本地依赖清单，`lake --no-cache build Main` 已通过。对齐表中的 94 个命名声明均已核实存在于所列模块。目标模块的传递公理依赖仅为 `propext`、`Classical.choice` 和 `Quot.sound`。没有未完成或未确认的义务。