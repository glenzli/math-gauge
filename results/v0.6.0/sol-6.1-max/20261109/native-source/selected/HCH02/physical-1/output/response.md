已完成 40/40 项。以下文件与题给两份冻结模块共同组成项目；冻结模块保持原样。全部目标模块及 Main 已在指定版本离线编译，103 个声明的公理审计仅出现允许的三项。

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "hch02"
version = "0.1.0"
defaultTargets = ["HCH02"]

[[lean_lib]]
name = "HCH02"
roots = ["Main", "Bounds", "Chains", "Scalar", "Example", "formal_oet.vol_01.ch_01_foundations.gauge_space", "formal_oet.vol_01.ch_01_foundations.operator_space"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"
```

```lean filename=Main.lean
import Bounds
import Chains
import Scalar
import Example
```

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ENNReal.Inv

/-
Historical OET chapter 02, frozen snapshot 2d2f76c8392daf62.
Source: Zhe Li / Glen Li / glenzli, The Operator Evolution Theory,
https://glenzli.com/books/oet/, https://orcid.org/0009-0006-6536-3453.
Source repository: https://gitlab.com/glenzli/oet-public.
CC BY 4.0: https://creativecommons.org/licenses/by/4.0/.
Changes: Lean formalization of the supplied historical text.
The algebraic lemmas work for arbitrary ENNReal-valued families; metric
axioms are required explicitly where they are used.
-/

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

abbrev Mat (I : Type) := I → I → ℝ≥0∞
abbrev Channel (I : Type) := I × I

variable {X I : Type} {bot : X} [Fintype I]

def display (M : Mat I) : Matrix I I ℝ≥0∞ := fun j i => M i j
def undisplay (M : Matrix I I ℝ≥0∞) : Mat I := fun i j => M j i

theorem undisplay_display (M : Mat I) : undisplay (display M) = M := rfl
theorem display_undisplay (M : Matrix I I ℝ≥0∞) : display (undisplay M) = M := rfl

def mmul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k
def unit : Mat I := fun i j => if i = j then 1 else 0

theorem display_mmul (B A : Mat I) :
    display (mmul B A) = display B * display A := by
  rfl

theorem display_unit : display (unit : Mat I) = 1 := by
  ext j i
  simp [display, unit, Matrix.one_apply, eq_comm]

theorem mmul_unit_left (A : Mat I) : mmul unit A = A := by
  ext i j
  simp [mmul, unit]

theorem mmul_unit_right (A : Mat I) : mmul A unit = A := by
  ext i j
  simp [mmul, unit]

theorem mmul_assoc (C B A : Mat I) : mmul C (mmul B A) = mmul (mmul C B) A := by
  have h : display (mmul C (mmul B A)) = display (mmul (mmul C B) A) := by
    simp only [display_mmul, Matrix.mul_assoc]
  exact funext fun i => funext fun j => congrFun (congrFun h j) i

def ident : Operator X bot := ⟨id, rfl⟩
def comp (q p : Operator X bot) : Operator X bot :=
  ⟨q.func ∘ p.func, by simp [p.preserves_bot, q.preserves_bot]⟩

theorem dom_comp (q p : Operator X bot) :
    dom (comp q p) = dom p ∩ p.func ⁻¹' dom q := by
  ext x
  change q.func (p.func x) ≠ bot ↔ p.func x ≠ bot ∧ q.func (p.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro hx
    exact h (by rw [hx, q.preserves_bot])
  · exact And.right

def Lip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (p.func x) (p.func y) ≤ ∑ i, M i j * d i x y}

def GlobalLip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) : Set (Mat I) :=
  Lip d p (dom p)

def CoLip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U.Nonempty ∧ U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, M i j * d i x y) ≤ d j (p.func x) (p.func y)}

variable {d : I → X → X → ℝ≥0∞} {p q : Operator X bot}
variable {U V : Set X} {L K : Mat I} {i j : I} {x y : X}

theorem lip_singleton (hI : ∀ k : I, k = i) (hL : L ∈ Lip d p U)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i (p.func x) (p.func y) ≤ L i i * d i x y := by
  have hs : (∑ k, L k i * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      exact (hk (hI k)).elim
    · simp
  simpa only [hs] using hL.2 x hx y hy i

theorem lip_restrict (hUV : U ⊆ V) : Lip d p V ⊆ Lip d p U := by
  intro M hM
  exact ⟨hUV.trans hM.1, fun x hx y hy j => hM.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict (hU : U ⊆ dom p) : GlobalLip d p ⊆ Lip d p U :=
  lip_restrict hU

def entryInf (d : I → X → X → ℝ≥0∞) (p : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf ((fun M : Mat I => M i j) '' Lip d p U)

theorem entryInf_mono (hUV : U ⊆ V) : entryInf d p U i j ≤ entryInf d p V i j := by
  apply sInf_le_sInf
  rintro _ ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict hUV hM, rfl⟩

theorem weighted_mmul (B A : Mat I) (v : I → ℝ≥0∞) (j : I) :
    (∑ k, B k j * ∑ i, A i k * v i) = ∑ i, mmul B A i j * v i := by
  simp only [mmul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem lip_comp (hU : U ⊆ dom (comp q p))
    (hA : L ∈ Lip d p U) (hB : K ∈ Lip d q (p.func '' U)) :
    mmul K L ∈ Lip d (comp q p) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j (q.func (p.func x)) (q.func (p.func y))
        ≤ ∑ k, K k j * d k (p.func x) (p.func y) :=
      hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, K k j * ∑ i, L i k * d i x y := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 x hx y hy k) _
    _ = ∑ i, mmul K L i j * d i x y := weighted_mmul K L _ j

theorem colip_comp (hU : U ⊆ dom (comp q p))
    (hA : L ∈ CoLip d p U) (hB : K ∈ CoLip d q (p.func '' U)) :
    mmul K L ∈ CoLip d (comp q p) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, mmul K L i j * d i x y) = ∑ k, K k j * ∑ i, L i k * d i x y :=
      (weighted_mmul K L _ j).symm
    _ ≤ ∑ k, K k j * d k (p.func x) (p.func y) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 x hx y hy k) _
    _ ≤ d j (q.func (p.func x)) (q.func (p.func y)) :=
      hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_term (hK : K ∈ CoLip d p U) (hx : x ∈ U) (hy : y ∈ U) :
    K i j * d i x y ≤ d j (p.func x) (p.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
    (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)

theorem colip_zero_entry (hK : K ∈ CoLip d p (dom p))
    (hx : x ∈ dom p) (hy : y ∈ dom p)
    (hout : d j (p.func x) (p.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hz : K i j * d i x y = 0 := le_antisymm (hout ▸ colip_term hK hx hy) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem perturb_forward (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (q.func x) (q.func y) ≤ d j (p.func x) (p.func y) + δ j + δ j := by
  have ha : d j (q.func x) (p.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  calc
    d j (q.func x) (q.func y)
        ≤ d j (q.func x) (p.func x) + d j (p.func x) (q.func y) := (hd j).triangle _ _ _
    _ ≤ δ j + (d j (p.func x) (p.func y) + δ j) :=
      add_le_add ha (((hd j).triangle (p.func x) (p.func y) (q.func y)).trans
        (add_le_add le_rfl (hδ y hy j)))
    _ = d j (p.func x) (p.func y) + δ j + δ j := by
      simp only [add_assoc, add_left_comm]

theorem perturb_reverse (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (p.func x) (p.func y) ≤ d j (q.func x) (q.func y) + δ j + δ j := by
  apply perturb_forward hd (fun z hz => ⟨(hU hz).2, (hU hz).1⟩) δ ?_ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k

theorem perturb_lip (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hL : L ∈ Lip d p U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (q.func x) (q.func y) ≤ (∑ i, L i j * d i x y) + 2 * δ j := by
  simpa only [two_mul, add_assoc] using
    (perturb_forward hd hU δ hδ hx hy j).trans
      (add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_colip (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hK : K ∈ CoLip d p U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i, K i j * d i x y) ≤ d j (q.func x) (q.func y) + 2 * δ j := by
  simpa only [two_mul, add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hU δ hδ hx hy j)

def Row (M : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → M k j = 0
def Col (M : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → M i k = 0
def Diagonal (M : Mat I) : Prop := ∀ i j, i ≠ j → M i j = 0
def RowDecoupled (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ M ∈ Lip d p U, ∃ i, Row M i j
def ColDecoupled (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ M ∈ Lip d p U, ∃ j, Col M i j

theorem zero_term (h : L i j = 0) : L i j * d i x y = 0 := by rw [h, zero_mul]

theorem erase_zero_term (h : L i j = 0) :
    (∑ k, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  have hs := Finset.sum_erase_add Finset.univ (fun k => L k j * d k x y)
    (Finset.mem_univ i)
  simpa only [zero_term h, add_zero] using hs.symm

theorem row_sum (h : Row L i j) : (∑ k, L k j * d k x y) = L i j * d i x y := by
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h k hk, zero_mul]
  · simp

theorem row_lip (hL : L ∈ Lip d p U) (h : Row L i j) (hx : x ∈ U) (hy : y ∈ U) :
    d j (p.func x) (p.func y) ≤ L i j * d i x y := by
  simpa only [row_sum h] using hL.2 x hx y hy j

theorem col_contribution (h : Col L i j) (k : I) (hk : k ≠ j) :
    L i k * d i x y = 0 := by rw [h k hk, zero_mul]

theorem diagonal_lip (hL : L ∈ Lip d p U) (h : Diagonal L)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  row_lip hL (fun k hk => h k j hk) hx hy

theorem scalar_two_sided (hL : L ∈ Lip d p U) (hK : K ∈ CoLip d p U)
    (h : Row L j j) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
      d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy, row_lip hL h hx hy⟩

theorem component_two_sided (hL : L ∈ Lip d p U) (hK : K ∈ CoLip d p U)
    (h : ∀ j, Row L j j) : ∀ j, ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
      d j (p.func x) (p.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact scalar_two_sided hL hK (h j) hx hy

theorem finite_component_two_sided (hL : L ∈ Lip d p U) (hK : K ∈ CoLip d p U)
    (h : ∀ j, Row L j j) (hf : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
        d j (p.func x) (p.func y) ≤ L j j * d j x y := by
  intro j
  exact ⟨(hf j).1, (hf j).2, component_two_sided hL hK h j⟩

theorem positive_channel (hK : K ∈ CoLip d p U) (h : 0 < K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (p.func x) (p.func y) :=
  (ENNReal.mul_pos_iff.mpr ⟨h, hin⟩).trans_le (colip_term hK hx hy)

theorem reflect_zero (hK : K ∈ CoLip d p U) (h : ∀ j, 0 < K j j)
    (hx : x ∈ U) (hy : y ∈ U) (hout : GaugeZeroRelated d (p.func x) (p.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel hK (h j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hout j] at hp
  exact (lt_irrefl _ hp)

end HCH02
```

```lean filename=Chains.lean
import Bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

variable {X I : Type} {bot : X} [Fintype I]

/-- Lists are in application order: the head acts first. -/
def prodMat : List (Mat I) → Mat I
  | [] => unit
  | A :: As => mmul (prodMat As) A

@[simp] theorem prodMat_nil : prodMat ([] : List (Mat I)) = unit := rfl
@[simp] theorem prodMat_single (A : Mat I) : prodMat [A] = A := mmul_unit_left A

theorem prodMat_append (As Bs : List (Mat I)) :
    prodMat (As ++ Bs) = mmul (prodMat Bs) (prodMat As) := by
  induction As with
  | nil => simp [mmul_unit_right]
  | cons A As ih =>
    simp only [List.cons_append, prodMat, ih, mmul_assoc]

/-- Only single-step data; no composite estimate is stored. -/
structure Step (X : Type) (bot : X) (I : Type) where
  op : Operator X bot
  upper : Mat I
  lower : Mat I

def chain : List (Step X bot I) → Operator X bot
  | [] => ident
  | s :: ss => comp (chain ss) s.op

theorem chain_single (s : Step X bot I) : chain [s] = s.op := by
  ext x
  rfl

theorem chain_append (ss ts : List (Step X bot I)) :
    chain (ss ++ ts) = comp (chain ts) (chain ss) := by
  induction ss with
  | nil => ext x; rfl
  | cons s ss ih =>
    simp only [List.cons_append, chain, ih]
    ext x
    rfl

def actualImage : List (Step X bot I) → Set X → Set X
  | [], U => U
  | s :: ss, U => actualImage ss (s.op.func '' U)

def Safe : List (Step X bot I) → Set X → Prop
  | [], U => U ⊆ dom (ident : Operator X bot)
  | s :: ss, U => U ⊆ dom s.op ∧ Safe ss (s.op.func '' U)

def StepLip (d : I → X → X → ℝ≥0∞) : List (Step X bot I) → Set X → Prop
  | [], _ => True
  | s :: ss, U => s.upper ∈ Lip d s.op U ∧ StepLip d ss (s.op.func '' U)

def StepCoLip (d : I → X → X → ℝ≥0∞) : List (Step X bot I) → Set X → Prop
  | [], _ => True
  | s :: ss, U => s.lower ∈ CoLip d s.op U ∧ StepCoLip d ss (s.op.func '' U)

theorem safe_iff (ss : List (Step X bot I)) (U : Set X) :
    Safe ss U ↔ U ⊆ dom (chain ss) := by
  induction ss generalizing U with
  | nil => rfl
  | cons s ss ih =>
    rw [Safe, chain, dom_comp]
    constructor
    · rintro ⟨hhead, htail⟩ x hx
      exact ⟨hhead hx, (ih _).mp htail ⟨x, hx, rfl⟩⟩
    · intro h
      refine ⟨fun x hx => (h hx).1, (ih _).mpr ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (h hx).2

theorem chain_image (ss : List (Step X bot I)) (U : Set X) :
    (chain ss).func '' U = actualImage ss U := by
  induction ss generalizing U with
  | nil => simp [chain, actualImage, ident]
  | cons s ss ih =>
    simpa only [chain, comp, Function.comp_def, Set.image_image, actualImage] using
      ih (s.op.func '' U)

/-- The input at every textbook step, expressed by its preceding prefix. -/
theorem actual_step_domain (pre : List (Step X bot I)) (s : Step X bot I)
    (tail : List (Step X bot I)) (U : Set X)
    (hU : U ⊆ dom (chain (pre ++ s :: tail))) :
    actualImage pre U ⊆ dom s.op := by
  rw [← chain_image]
  rintro _ ⟨x, hx, rfl⟩
  have ht := hU hx
  rw [chain_append, dom_comp] at ht
  have hs := ht.2
  change (chain pre).func x ∈ dom (comp (chain tail) s.op) at hs
  rw [dom_comp] at hs
  exact hs.1

/-- Converts primitive bounds at every actual input into recursive chain data. -/
theorem stepLip_iff (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) :
    StepLip d ss U ↔ ∀ pre s tail, ss = pre ++ s :: tail →
      s.upper ∈ Lip d s.op (actualImage pre U) := by
  induction ss generalizing U with
  | nil =>
    constructor
    · intro _ pre s tail heq
      cases pre <;> simp at heq
    · intro _
      trivial
  | cons a ss ih =>
    constructor
    · intro h pre s tail heq
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact h.1
      | cons b pre =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, heq⟩
        exact (ih _).mp h.2 pre s tail heq
    · intro h
      refine ⟨h [] a ss rfl, (ih _).mpr ?_⟩
      intro pre s tail heq
      exact h (a :: pre) s tail (by simp only [List.cons_append, heq])

theorem stepCoLip_iff (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) :
    StepCoLip d ss U ↔ ∀ pre s tail, ss = pre ++ s :: tail →
      s.lower ∈ CoLip d s.op (actualImage pre U) := by
  induction ss generalizing U with
  | nil =>
    constructor
    · intro _ pre s tail heq
      cases pre <;> simp at heq
    · intro _
      trivial
  | cons a ss ih =>
    constructor
    · intro h pre s tail heq
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact h.1
      | cons b pre =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, heq⟩
        exact (ih _).mp h.2 pre s tail heq
    · intro h
      refine ⟨h [] a ss rfl, (ih _).mpr ?_⟩
      intro pre s tail heq
      exact h (a :: pre) s tail (by simp only [List.cons_append, heq])

theorem lip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hU : U ⊆ dom (ident : Operator X bot)) :
    unit ∈ Lip d (ident : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [unit, ident]

theorem colip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (ident : Operator X bot)) :
    unit ∈ CoLip d (ident : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [unit, ident]

theorem lip_chain (d : I → X → X → ℝ≥0∞) (ss : List (Step X bot I)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) (hs : StepLip d ss U) :
    prodMat (ss.map Step.upper) ∈ Lip d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact lip_unit d U hU
  | cons s ss ih =>
    have htail : s.op.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      have ht : x ∈ dom s.op ∩ s.op.func ⁻¹' dom (chain ss) := by
        simpa only [chain, dom_comp] using hU hx
      exact ht.2
    exact lip_comp hU hs.1 (ih _ htail hs.2)

theorem colip_chain (d : I → X → X → ℝ≥0∞) (ss : List (Step X bot I)) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (chain ss)) (hs : StepCoLip d ss U) :
    prodMat (ss.map Step.lower) ∈ CoLip d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact colip_unit d U hne hU
  | cons s ss ih =>
    have htail : s.op.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      have ht : x ∈ dom s.op ∩ s.op.func ⁻¹' dom (chain ss) := by
        simpa only [chain, dom_comp] using hU hx
      exact ht.2
    exact colip_comp hU hs.1 (ih _ (hne.image _) htail hs.2)

theorem positive_length_colip_chain (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) (hn : ss ≠ [])
    (hU : U ⊆ dom (chain ss)) (hs : StepCoLip d ss U) :
    prodMat (ss.map Step.lower) ∈ CoLip d (chain ss) U := by
  apply colip_chain d ss U ?_ hU hs
  cases ss with
  | nil => exact (hn rfl).elim
  | cons s ss => exact hs.1.1

/-- Recursive tuples of all intermediate indices, with no edge restriction. -/
def Route (I : Type) : Nat → Type
  | 0 => PUnit
  | n + 1 => I × Route I n

theorem route_zero_unique (r : Route I 0) : r = PUnit.unit := by cases r; rfl

instance routeFintype (n : Nat) : Fintype (Route I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (I × Route I n))

/-- Explicit correspondence with the textbook's n intermediate indices. -/
def routeEquiv : (n : Nat) → Route I n ≃ (Fin n → I)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := by intro r; cases r; rfl
      right_inv := fun _ => funext fun k => Fin.elim0 k }
  | n + 1 =>
    { toFun := fun r => Fin.cons r.1 (routeEquiv n r.2)
      invFun := fun f => (f 0, (routeEquiv n).symm (Fin.tail f))
      left_inv := by
        intro r
        rcases r with ⟨k, r⟩
        simp
      right_inv := by
        intro f
        simp }

def weight : (As : List (Mat I)) → I → I → Route I (As.length - 1) → ℝ≥0∞
  | [], i, j, _ => unit i j
  | [A], i, j, _ => A i j
  | A :: B :: As, i, j, r => weight (B :: As) r.1 j r.2 * A i r.1

def AllPositive : (As : List (Mat I)) → I → I → Route I (As.length - 1) → Prop
  | [], _, _, _ => True
  | [A], i, j, _ => 0 < A i j
  | A :: B :: As, i, j, r => 0 < A i r.1 ∧ AllPositive (B :: As) r.1 j r.2

def HasZero : (As : List (Mat I)) → I → I → Route I (As.length - 1) → Prop
  | [], _, _, _ => False
  | [A], i, j, _ => A i j = 0
  | A :: B :: As, i, j, r => A i r.1 = 0 ∨ HasZero (B :: As) r.1 j r.2

theorem weight_zero (As : List (Mat I)) (hn : As ≠ []) (i j : I)
    (r : Route I (As.length - 1)) : weight As i j r = 0 ↔ HasZero As i j r := by
  induction As generalizing i j with
  | nil => exact (hn rfl).elim
  | cons A As ih =>
    cases As with
    | nil => rfl
    | cons B Bs =>
      rcases r with ⟨k, r⟩
      simp only [weight, HasZero, mul_eq_zero, ih (by simp)]
      exact or_comm

theorem weight_positive (As : List (Mat I)) (hn : As ≠ []) (i j : I)
    (r : Route I (As.length - 1)) : 0 < weight As i j r ↔ AllPositive As i j r := by
  induction As generalizing i j with
  | nil => exact (hn rfl).elim
  | cons A As ih =>
    cases As with
    | nil => rfl
    | cons B Bs =>
      rcases r with ⟨k, r⟩
      simp only [weight, AllPositive, ENNReal.mul_pos_iff, ih (by simp)]
      exact and_comm

theorem path_expansion (As : List (Mat I)) (hn : As ≠ []) (i j : I) :
    prodMat As i j = ∑ r : Route I (As.length - 1), weight As i j r := by
  induction As generalizing i j with
  | nil => exact (hn rfl).elim
  | cons A As ih =>
    cases As with
    | nil => simp [weight, prodMat_single, Route]
    | cons B Bs =>
      change (∑ k, prodMat (B :: Bs) k j * A i k) =
        ∑ r : I × Route I Bs.length, weight (B :: Bs) r.1 j r.2 * A i r.1
      simp_rw [ih (by simp), Finset.sum_mul]
      exact (Fintype.sum_prod_type
        (fun r : I × Route I Bs.length => weight (B :: Bs) r.1 j r.2 * A i r.1)).symm

theorem product_zero_iff (As : List (Mat I)) (hn : As ≠ []) (i j : I) :
    prodMat As i j = 0 ↔ ∀ r, HasZero As i j r := by
  rw [path_expansion As hn i j]
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, weight_zero As hn]

theorem product_positive_iff (As : List (Mat I)) (hn : As ≠ []) (i j : I) :
    0 < prodMat As i j ↔ ∃ r, AllPositive As i j r := by
  rw [path_expansion As hn i j]
  simp only [Finset.sum_pos_iff, Finset.mem_univ, true_and, weight_positive As hn]

theorem certified_lip_zero (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) (hn : ss ≠ [])
    (hU : U ⊆ dom (chain ss)) (hL : StepLip d ss U) (hK : StepCoLip d ss U)
    (i j : I) :
    prodMat (ss.map Step.upper) i j = 0 ↔ ∀ r, HasZero (ss.map Step.upper) i j r := by
  exact product_zero_iff _ (by simpa using hn) i j

theorem certified_colip_positive (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) (hn : ss ≠ [])
    (hU : U ⊆ dom (chain ss)) (hL : StepLip d ss U) (hK : StepCoLip d ss U)
    (i j : I) :
    0 < prodMat (ss.map Step.lower) i j ↔ ∃ r, AllPositive (ss.map Step.lower) i j r := by
  exact product_positive_iff _ (by simpa using hn) i j

end HCH02
```

```lean filename=Scalar.lean
import Bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

variable {X I : Type} {bot : X}

def ScalarSet (d : I → X → X → ℝ≥0∞) (p : Operator X bot)
    (U : Set X) (i j : I) : Set ℝ≥0∞ :=
  {c | ∀ x ∈ U, ∀ y ∈ U, d j (p.func x) (p.func y) ≤ c * d i x y}

def scalarInf (d : I → X → X → ℝ≥0∞) (p : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf (ScalarSet d p U i j)

variable {d : I → X → X → ℝ≥0∞} {p : Operator X bot}
variable {U : Set X} {i j : I} {c b : ℝ≥0∞}

theorem scalarInf_empty (h : ScalarSet d p U i j = ∅) : scalarInf d p U i j = ⊤ := by
  simp [scalarInf, h]

theorem scalar_upward (hc : c ∈ ScalarSet d p U i j) (h : c ≤ b) :
    b ∈ ScalarSet d p U i j := by
  intro x hx y hy
  exact (hc x hx y hy).trans (mul_le_mul_left h _)

theorem scalar_above (h : scalarInf d p U i j < c) : c ∈ ScalarSet d p U i j := by
  obtain ⟨b, hb, hbc⟩ := sInf_lt_iff.mp h
  exact scalar_upward hb hbc.le

theorem scalar_zero_above (ha : scalarInf d p U i j = 0)
    (hc : 0 < c) (hf : c < ⊤) : c ∈ ScalarSet d p U i j :=
  scalar_above (ha ▸ hc)

theorem scalar_empty_of_zero_input {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (p.func x) (p.func y)) :
    ScalarSet d p U i j = ∅ ∧ scalarInf d p U i j = ⊤ := by
  have hs : ScalarSet d p U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hz := hc x hx y hy
    rw [hin, mul_zero] at hz
    exact (not_le_of_gt hout) hz
  exact ⟨hs, by simp [scalarInf, hs]⟩

theorem scalar_finite_iff : scalarInf d p U i j < ⊤ ↔
    ∃ c, c < ⊤ ∧ c ∈ ScalarSet d p U i j := by
  constructor
  · intro h
    obtain ⟨c, hc, hf⟩ := sInf_lt_iff.mp h
    exact ⟨c, hf, hc⟩
  · rintro ⟨c, hf, hc⟩
    exact (sInf_le hc).trans_lt hf

theorem scalar_attained (ha : 0 < scalarInf d p U i j)
    (hf : scalarInf d p U i j < ⊤) :
    scalarInf d p U i j ∈ ScalarSet d p U i j := by
  obtain ⟨c, _, hc⟩ := scalar_finite_iff.mp hf
  letI : Nonempty (ScalarSet d p U i j) := ⟨⟨c, hc⟩⟩
  have heq : scalarInf d p U i j = ⨅ c : ScalarSet d p U i j, c.val := by
    apply le_antisymm
    · exact le_iInf fun c => sInf_le c.property
    · apply le_sInf
      intro c hc
      exact iInf_le_of_le ⟨c, hc⟩ le_rfl
  intro x hx y hy
  rw [heq, ENNReal.iInf_mul (fun _ hz => ?_)]
  · exact le_iInf fun c => c.property x hx y hy
  · exact ((ne_of_gt ha) (heq.trans hz)).elim

end HCH02
```

```lean filename=Example.lean
import Scalar

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

/-- Two nonabsorbing points; input distance infinity, output distance one. -/
def exampleDist (i : Bool) (x y : Option Bool) : ℝ≥0∞ :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if i then 1 else ⊤

theorem example_gauge (i : Bool) :
    ExtendedPseudoMetric (Option Bool) none (exampleDist i) := by
  refine
    { nonabsorbing := ⟨some false, by simp⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    simp [exampleDist]
  · intro x y
    simp [exampleDist, eq_comm, or_comm]
  · intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [exampleDist]
  · intro x hx
    simp [exampleDist, hx]

def exampleU : Set (Option Bool) := Set.range some
def exampleOp : Operator (Option Bool) none := ident

theorem example_domain : exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp := by
  refine ⟨⟨some false, ⟨false, rfl⟩⟩, ?_⟩
  rintro _ ⟨b, rfl⟩
  simp [dom, exampleOp, ident]

theorem example_positive_feasible {c : ℝ≥0∞} (hc : 0 < c) :
    c ∈ ScalarSet exampleDist exampleOp exampleU false true := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  by_cases hab : a = b
  · subst b
    simp [exampleDist, exampleOp, ident]
  · simp [exampleDist, exampleOp, ident, hab, ENNReal.mul_top (ne_of_gt hc)]

theorem example_zero_not_feasible :
    (0 : ℝ≥0∞) ∉ ScalarSet exampleDist exampleOp exampleU false true := by
  intro h
  have hz := h (some false) ⟨false, rfl⟩ (some true) ⟨true, rfl⟩
  simp [exampleDist, exampleOp, ident] at hz

theorem example_inf_zero : scalarInf exampleDist exampleOp exampleU false true = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  have ha : 0 < scalarInf exampleDist exampleOp exampleU false true := lt_of_not_ge hn
  obtain ⟨c, hc, hca⟩ := exists_between ha
  have hle : scalarInf exampleDist exampleOp exampleU false true ≤ c :=
    sInf_le (example_positive_feasible hc)
  exact (not_le_of_gt hca) hle

/-- Full counterexample, including all gauge and domain obligations. -/
theorem zero_inf_not_attained :
    (∀ i, ExtendedPseudoMetric (Option Bool) none (exampleDist i)) ∧
    exampleU.Nonempty ∧ exampleU ⊆ dom exampleOp ∧
    scalarInf exampleDist exampleOp exampleU false true = 0 ∧
    (0 : ℝ≥0∞) ∉ ScalarSet exampleDist exampleOp exampleU false true :=
  ⟨example_gauge, example_domain.1, example_domain.2, example_inf_zero,
    example_zero_not_feasible⟩

end HCH02
```

```text filename=validation.txt
Lean 4.29.1
mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6
All target modules and Main compiled offline.
103 target declarations audited.
40/40 alignment items verified.
Axioms: Classical.choice, Quot.sound, propext
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {"id":"HC02-D01","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.Lip"},{"file":"Bounds.lean","name":"HCH02.GlobalLip"}],"representation":"Lip d φ U 是矩阵集合，成员同时要求 U⊆dom φ 以及全部 x,y∈U、输出 j 的 ENNReal 求和上界；GlobalLip 取 U=dom φ，允许零和无限系数。","dependencies":["HC02-D03"]},
    {"id":"HC02-D02","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.CoLip"}],"representation":"成员包含 U.Nonempty（即 U≠∅）、U⊆dom φ 和全部 x,y∈U、j 的求和下界；系数均为 ENNReal。","dependencies":["HC02-D03"]},
    {"id":"HC02-D03","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.Mat"},{"file":"Bounds.lean","name":"HCH02.display"},{"file":"Bounds.lean","name":"HCH02.undisplay"},{"file":"Bounds.lean","name":"HCH02.undisplay_display"},{"file":"Bounds.lean","name":"HCH02.display_undisplay"},{"file":"Bounds.lean","name":"HCH02.mmul"},{"file":"Bounds.lean","name":"HCH02.display_mmul"},{"file":"Bounds.lean","name":"HCH02.mmul_assoc"},{"file":"Bounds.lean","name":"HCH02.weighted_mmul"}],"representation":"Mat I 的 M i j 按输入、输出存储；display 的第 j 行第 i 列为 M i j，转换互逆。mmul B A i j=Σk B k j*A i k，已证明对应通常矩阵乘法及有限和展开。","dependencies":[]},
    {"id":"HC02-D04","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.prodMat"},{"file":"Chains.lean","name":"HCH02.prodMat_nil"},{"file":"Chains.lean","name":"HCH02.prodMat_single"},{"file":"Chains.lean","name":"HCH02.prodMat_append"},{"file":"Bounds.lean","name":"HCH02.unit"},{"file":"Bounds.lean","name":"HCH02.display_unit"},{"file":"Bounds.lean","name":"HCH02.mmul_unit_left"},{"file":"Bounds.lean","name":"HCH02.mmul_unit_right"}],"representation":"列表按施行顺序排列，prodMat []=δij，A::As 的乘积为后续乘积左乘 A；单步等于唯一矩阵，append 证明串接乘积的方向。","dependencies":["HC02-D03"]},
    {"id":"HC02-D05","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.Step"},{"file":"Chains.lean","name":"HCH02.chain"},{"file":"Chains.lean","name":"HCH02.chain_single"},{"file":"Chains.lean","name":"HCH02.chain_append"},{"file":"Chains.lean","name":"HCH02.actualImage"},{"file":"Chains.lean","name":"HCH02.Safe"},{"file":"Chains.lean","name":"HCH02.StepLip"},{"file":"Chains.lean","name":"HCH02.StepCoLip"},{"file":"Chains.lean","name":"HCH02.safe_iff"},{"file":"Chains.lean","name":"HCH02.chain_image"},{"file":"Bounds.lean","name":"HCH02.comp"},{"file":"Bounds.lean","name":"HCH02.dom_comp"},{"file":"Chains.lean","name":"HCH02.actual_step_domain"},{"file":"Chains.lean","name":"HCH02.stepLip_iff"},{"file":"Chains.lean","name":"HCH02.stepCoLip_iff"}],"representation":"Step 只存单步算子与上下界矩阵。头部首先施行，域递归为 φ.func '' U；safe_iff 和 actual_step_domain 从 U⊆dom 全复合推出每步域合法，chain_image 证明全复合像等于逐次像。stepLip_iff、stepCoLip_iff 双向证明递归单步条件等价于每个前缀实际像域上的正文条件，反向可构造链的证书数据；没有最终复合界字段。","dependencies":["HC02-D01","HC02-D02","HC02-D03"]},
    {"id":"HC02-D06","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.Route"},{"file":"Chains.lean","name":"HCH02.route_zero_unique"},{"file":"Chains.lean","name":"HCH02.routeFintype"},{"file":"Chains.lean","name":"HCH02.routeEquiv"},{"file":"Chains.lean","name":"HCH02.weight"},{"file":"Chains.lean","name":"HCH02.AllPositive"},{"file":"Chains.lean","name":"HCH02.HasZero"},{"file":"Chains.lean","name":"HCH02.weight_zero"},{"file":"Chains.lean","name":"HCH02.weight_positive"},{"file":"Chains.lean","name":"HCH02.path_expansion"}],"representation":"非空 n 步列表的路径为 Route I (n-1)，无边约束，routeEquiv 证明等价于 Fin(n-1)→I。i,j 固定两端；weight 为边乘积，两个谓词分别为全正及含零边。n=1 的空中间序列唯一；path_expansion 证明与矩阵乘积的对应。","dependencies":["HC02-D03","HC02-D04"]},
    {"id":"HC02-D07","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.Channel"},{"file":"Bounds.lean","name":"HCH02.Row"},{"file":"Bounds.lean","name":"HCH02.Col"},{"file":"Bounds.lean","name":"HCH02.Diagonal"},{"file":"Bounds.lean","name":"HCH02.RowDecoupled"},{"file":"Bounds.lean","name":"HCH02.ColDecoupled"}],"representation":"Channel=I×I；Row M i j 固定输出 j、除输入 i 外全零；Col 固定输入 i、除输出 j 外全零。行、列解耦分别存在合法 Lip 证书和保留位置；Diagonal 要求非对角条目全零。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D08","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.ScalarSet"},{"file":"Scalar.lean","name":"HCH02.scalarInf"},{"file":"Scalar.lean","name":"HCH02.scalarInf_empty"}],"representation":"给定合法作用域 U⊆dom φ，ScalarSet 精确量化全部 U 内点对的单输入分量标量上界；scalarInf=sInf ScalarSet，空族下确界为 ∞。它独立于矩阵条目下确界 entryInf。定义也可用于任意 U。","dependencies":[]},
    {"id":"HC02-P01","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.lip_singleton"}],"representation":"hI:∀k,k=i 表示指标集仅含 i；任一合法 Lip 矩阵对全部 U 内点对给出 Lii 的标量上界。","dependencies":["HC02-D01"]},
    {"id":"HC02-P02","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.global_lip_restrict"}],"representation":"给定 U⊆dom φ，GlobalLip d φ⊆Lip d φ U。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P03","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.lip_restrict"}],"representation":"U⊆V 时，V 上全部合法 Lip 证书在 U 上仍合法；V⊆dom φ 来自原成员条件。","dependencies":["HC02-D01"]},
    {"id":"HC02-P04","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.entryInf"},{"file":"Bounds.lean","name":"HCH02.entryInf_mono"}],"representation":"entryInf 为合法矩阵集合经 M↦Mij 映像的 sInf；缩小域扩大可行集合，逐条目下确界不增。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P05","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.lip_comp"}],"representation":"comp q p=φ2∘φ1；U⊆dom(comp q p)，第二证书域恰为 p.func '' U，所得证书为 mmul K L。这里 K 只是第二个上界矩阵参数名。","dependencies":["HC02-D01","HC02-D03","HC02-D05"]},
    {"id":"HC02-P06","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.colip_zero_entry"}],"representation":"在 dom φ 上的任意合法 co-Lip 矩阵，若有指定点对输出零距而输入距正，则其 Kij=0；允许输入距为 ∞。","dependencies":["HC02-D02"]},
    {"id":"HC02-P07","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.colip_comp"}],"representation":"与 P05 同样的起始域及真实像域，两个合法 co-Lip 证书的 mmul 是全复合合法证书，包含起始域非空性。","dependencies":["HC02-D02","HC02-D03","HC02-D05"]},
    {"id":"HC02-P08","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_forward"}],"representation":"在分量 ExtendedPseudoMetric、公共定义域 U 及逐点扰动≤δj 下，对全部 U 内点对给出正向像距≤原像距+δj+δj。","dependencies":[]},
    {"id":"HC02-P09","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_reverse"}],"representation":"相同前提下利用距离对称性交换两个算子，得到反向的全部点对像距界。","dependencies":["HC02-P08"]},
    {"id":"HC02-P10","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_lip"}],"representation":"φ1 在 U 上合法 Lip 证书经正向扰动界桥接到 φ2，附加项为 2*δj；由 two_mul 对应 δj+δj。","dependencies":["HC02-D01","HC02-P08"]},
    {"id":"HC02-P11","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_colip"}],"representation":"φ1 在 U 上合法 co-Lip 求和下界，经反向扰动界控制于 φ2 像距加 2*δj。","dependencies":["HC02-D02","HC02-P09"]},
    {"id":"HC02-P12","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.lip_chain"}],"representation":"任意列表链，U⊆dom 全复合，指定 upper 矩阵逐步在实际像域合法，则 prodMat 是全复合的 Lip 证书；还证明了空链情形，故包含所有正长度。","dependencies":["HC02-D01","HC02-D04","HC02-D05","HC02-P05","HC02-P14"]},
    {"id":"HC02-P13","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.colip_chain"},{"file":"Chains.lean","name":"HCH02.positive_length_colip_chain"}],"representation":"正长度链的初始非空性由首步 co-Lip 证书导出，各递归像域非空；指定 lower 乘积是完整 co-Lip 证书。辅助定理也覆盖显式非空域上的空链。","dependencies":["HC02-D02","HC02-D04","HC02-D05","HC02-P07","HC02-P15"]},
    {"id":"HC02-P14","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.lip_unit"}],"representation":"chain []=ident、prodMat []=unit；对 U⊆dom ident 验证单位矩阵合法，特别覆盖原文的非空 U。","dependencies":["HC02-D01","HC02-D04"]},
    {"id":"HC02-P15","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.colip_unit"}],"representation":"同一个非空 U⊆dom ident 上，单位矩阵满足全部 co-Lip 成员条件。","dependencies":["HC02-D02","HC02-D04"]},
    {"id":"HC02-P16","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.product_zero_iff"},{"file":"Chains.lean","name":"HCH02.certified_lip_zero"}],"representation":"非空乘积 ij=0 当且仅当每条完整路径有零边；certified_lip_zero 保留同一个非空算子链、合法起始域和两族实际单步证书。单步由唯一路径退化到唯一条目。","dependencies":["HC02-D01","HC02-D02","HC02-D04","HC02-D05","HC02-D06"]},
    {"id":"HC02-P17","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.product_positive_iff"},{"file":"Chains.lean","name":"HCH02.certified_colip_positive"}],"representation":"同一个正文链条件下，lower 乘积 ij>0 当且仅当存在一条所有边严格正的完整路径；包括单步及无限条目。","dependencies":["HC02-D01","HC02-D02","HC02-D04","HC02-D05","HC02-D06"]},
    {"id":"HC02-P18","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.scalar_empty_of_zero_input"}],"representation":"U 内有输入零距且输出正距的点对，则全部 ENNReal 标量可行族为空、下确界为 ∞；无限系数也不例外。","dependencies":["HC02-D08"]},
    {"id":"HC02-P19","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.scalar_attained"}],"representation":"0<a<∞ 时，先由有限性取得非空可行族，再用 ENNReal 的下确界乘法公式证明 a 本身满足全部点对界；a>0 排除零乘无限的边界障碍。","dependencies":["HC02-D08","HC02-P24"]},
    {"id":"HC02-P20","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.scalar_upward"}],"representation":"任意可行 c 及 c≤b，通过 ENNReal 乘法单调性证明 b 可行。","dependencies":["HC02-D08"]},
    {"id":"HC02-P21","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.scalar_above"}],"representation":"证明更一般的 a<c 即 c 可行，故包括 0<a<∞ 上下文中全部 c>a（允许 c=∞）。","dependencies":["HC02-D08","HC02-P20"]},
    {"id":"HC02-P22","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.scalar_zero_above"}],"representation":"a=0 且 0<c<∞ 时 c 可行；不声称 0 可行。","dependencies":["HC02-D08","HC02-P21"]},
    {"id":"HC02-P23","status":"complete","declarations":[{"file":"Example.lean","name":"HCH02.exampleDist"},{"file":"Example.lean","name":"HCH02.example_gauge"},{"file":"Example.lean","name":"HCH02.exampleU"},{"file":"Example.lean","name":"HCH02.exampleOp"},{"file":"Example.lean","name":"HCH02.example_domain"},{"file":"Example.lean","name":"HCH02.example_positive_feasible"},{"file":"Example.lean","name":"HCH02.example_zero_not_feasible"},{"file":"Example.lean","name":"HCH02.example_inf_zero"},{"file":"Example.lean","name":"HCH02.zero_inf_not_attained"}],"representation":"X=Option Bool、bot=none、I=Bool。两个非吸收点的 false 分量距为 ∞、true 分量距为 1，验证全部扩展伪度量公理；φ 恒等，U 为两个 some 点，合法且非空。false→true 通道下确界为 0，而 0 不可行。","dependencies":["HC02-D08"]},
    {"id":"HC02-P24","status":"complete","declarations":[{"file":"Scalar.lean","name":"HCH02.scalar_finite_iff"}],"representation":"a<∞ 当且仅当存在 c<∞ 满足全部 U 内点对标量界；直接使用完整线性格的下确界性质，无需预设取到。","dependencies":["HC02-D08"]},
    {"id":"HC02-P25","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.zero_term"},{"file":"Bounds.lean","name":"HCH02.erase_zero_term"}],"representation":"Lij=0 时对任意 ENNReal 输入距，该项均为零，输出 j 的总和等于删除输入 i 后的和，包括输入距 ∞。","dependencies":["HC02-D03"]},
    {"id":"HC02-P26","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.row_sum"},{"file":"Bounds.lean","name":"HCH02.row_lip"}],"representation":"Row L i j 中保留输入 i 可为任意位置；求和精确化简后给出 Lij*di 的标量上界，不要求 i=j。","dependencies":["HC02-D01","HC02-D07"]},
    {"id":"HC02-P27","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.col_contribution"}],"representation":"固定输入 i 列仅输出 j 可能非零，则对每个 k≠j、任意点对，Lik*di=0。定理对任意矩阵成立，特别适用于合法 Lip 证书。","dependencies":["HC02-D07"]},
    {"id":"HC02-P28","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.diagonal_lip"}],"representation":"合法 Lip 矩阵的全部非对角项为零时，每个 j 在全部 U 内点对上独立满足 Ljj 的标量上界。","dependencies":["HC02-D01","HC02-D07","HC02-P26"]},
    {"id":"HC02-P29","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.scalar_two_sided"}],"representation":"只要求 Lip 第 j 行保留对角项，对 co-Lip 矩阵不要求稀疏；从非负和抽取 Kjj 项，合并得到完整双侧界。","dependencies":["HC02-D01","HC02-D02","HC02-D07","HC02-P26"]},
    {"id":"HC02-P30","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.component_two_sided"},{"file":"Bounds.lean","name":"HCH02.finite_component_two_sided"}],"representation":"所有输出的 Lip 行均仅保留对角项，则同时给出全部分量及点对的双侧界；有限分支同时明确给出每个 Ljj、Kjj<∞。","dependencies":["HC02-D01","HC02-D02","HC02-D07","HC02-P29"]},
    {"id":"HC02-P31","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.positive_channel"}],"representation":"合法 co-Lip 矩阵的正 Kij 将全部 U 内正 di 输入距传递为正 dj 输出距，允许无限正系数或距离。","dependencies":["HC02-D02"]},
    {"id":"HC02-P32","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.reflect_zero"}],"representation":"所有 Kjj>0 时反射冻结模块的 GaugeZeroRelated；逐分量排除正输入距，不假设族分离性，也不推出点值相等。","dependencies":["HC02-D02","HC02-P31"]}
  ]
}
```

已完整完成并对齐冻结第 2 章及全部 40 项义务。等价表示均提供对应证明；未完成或未确认范围：无。