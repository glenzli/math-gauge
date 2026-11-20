已完成冻结第 2 章的 **40/40 项义务**。提交包在干净目录中使用 Lean 4.29.1 和指定的 mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6` 离线构建通过。目标模块通过 `leanchecker` 内核重放，94 个公开命名声明的公理依赖并集为 `propext`、`Classical.choice`、`Quot.sound`。两份冻结前置源码已核对哈希。[完整项目压缩包](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/HCH02/physical-1/output/artifacts/HCH02.zip)

复现时，在项目目录运行 `python3 prepare.py /本地/Lake包缓存目录`，再用 Lean 4.29.1 的 `lake --no-cache --wfail build` 构建。缓存目录应包含 `mathlib` 及其锁定的依赖。题给工作区中也可直接运行 `python3 prepare.py`，由脚本读取 `environment.json`。

数学原文为 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*，本提交将快照 `2d2f76c8392daf62` 转写为 Lean。压缩包包含原署名、许可证和两份冻结前置模块。以下是全部新增文件。[作者 ORCID](https://orcid.org/0009-0006-6536-3453) · [作品主页](https://glenzli.com/books/oet/) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

### Lean 源码

```lean filename=Main.lean
import Bounds
import Chains
import Channels
```

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/- Formalization of chapter 2 of The Operator Evolution Theory, Zhe Li
(Glen Li / glenzli), https://glenzli.com/books/oet/, CC BY 4.0.
Historical text 2d2f76c8392daf62. -/
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators
noncomputable section
namespace HCH02

abbrev Mat (I : Type) := I → I → ENNReal
variable {I X : Type} {b : X}

def display (A : Mat I) : Matrix I I ENNReal := fun j i => A i j

def mul [Fintype I] (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k

theorem display_mul [Fintype I] (B A : Mat I) :
    display (mul B A) = display B * display A := rfl

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X b (d i)

def act [Fintype I] (A : Mat I) (v : I → ENNReal) (j : I) := ∑ i, A i j * v i

theorem act_mul [Fintype I] (B A : Mat I) (v : I → ENNReal) (j : I) :
    act (mul B A) v j = act B (act A v) j := by
  simp only [act, mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem act_mono [Fintype I] (A : Mat I) {v w : I → ENNReal} (h : ∀ i, v i ≤ w i)
    (j : I) : act A v j ≤ act A w j :=
  Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) _

def comp (q p : Operator X b) : Operator X b :=
  ⟨q.func ∘ p.func, by simp [p.preserves_bot, q.preserves_bot]⟩

theorem comp_domain {p q : Operator X b} {U : Set X} :
    U ⊆ dom (comp q p) ↔ U ⊆ dom p ∧ operator_image p U ⊆ dom q := by
  constructor
  · intro h
    constructor
    · intro x hx he
      exact h hx (by change q.func (p.func x) = b; rw [he, q.preserves_bot])
    · rintro _ ⟨x, hx, rfl⟩
      exact h hx
  · exact fun h x hx => h.2 ⟨x, hx, rfl⟩

variable [Fintype I] [Nonempty I]
variable (g : Gauge X I b)

def vec (x y : X) : I → ENNReal := fun i => g.d i x y

def lip (p : Operator X b) (U : Set X) : Set (Mat I) :=
  {A | U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    g.d j (p.func x) (p.func y) ≤ act A (vec g x y) j}

def globalLip (p : Operator X b) := lip g p (dom p)

open scoped Classical in
theorem infinite_term (v : ENNReal) : ⊤ * v = if v = 0 then 0 else ⊤ := ENNReal.top_mul'

def coLip (p : Operator X b) (U : Set X) : Set (Mat I) :=
  {A | U.Nonempty ∧ U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    act A (vec g x y) j ≤ g.d j (p.func x) (p.func y)}

variable {g} {p q : Operator X b} {U V : Set X} {A B : Mat I} {x y : X} {i j : I}

theorem singleton_lip [Subsingleton I] :
    A ∈ globalLip g p ↔ ∀ x ∈ dom p, ∀ y ∈ dom p,
      g.d i (p.func x) (p.func y) ≤ A i i * g.d i x y := by
  have hs (v : I → ENNReal) : act A v i = A i i * v i := by
    exact Fintype.sum_subsingleton _ i
  constructor
  · intro h x hx y hy
    simpa only [hs, vec] using h.2 x hx y hy i
  · refine fun h => ⟨fun _ hx => hx, fun x hx y hy k => ?_⟩
    cases Subsingleton.elim k i
    simpa only [hs, vec] using h x hx y hy

theorem restrict_lip (h : U ⊆ V) : lip g p V ⊆ lip g p U :=
  fun _ hA => ⟨h.trans hA.1, fun x hx y hy => hA.2 x (h hx) y (h hy)⟩

theorem restrict_global (h : U ⊆ dom p) : globalLip g p ⊆ lip g p U := restrict_lip h

def entryInf (g : Gauge X I b) (p : Operator X b) (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun A : Mat I => A i j) '' lip g p U)

theorem entryInf_le (h : U ⊆ V) : entryInf g p U i j ≤ entryInf g p V i j :=
  sInf_le_sInf (Set.image_mono (restrict_lip h))

theorem lip_comp (h : U ⊆ dom (comp q p)) (hA : A ∈ lip g p U)
    (hB : B ∈ lip g q (operator_image p U)) : mul B A ∈ lip g (comp q p) U := by
  refine ⟨h, fun x hx y hy j => ?_⟩
  rw [act_mul]
  exact (hB.2 _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ j).trans (act_mono B (hA.2 x hx y hy) j)

theorem co_comp (h : U ⊆ dom (comp q p)) (hA : A ∈ coLip g p U)
    (hB : B ∈ coLip g q (operator_image p U)) : mul B A ∈ coLip g (comp q p) U := by
  refine ⟨hA.1, h, fun x hx y hy j => ?_⟩
  rw [act_mul]
  exact (act_mono B (hA.2.2 x hx y hy) j).trans (hB.2.2 _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ j)

theorem co_term (h : A ∈ coLip g p U) (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    A i j * g.d i x y ≤ g.d j (p.func x) (p.func y) :=
  (Finset.single_le_sum (f := fun k => A k j * g.d k x y)
    (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (h.2.2 x hx y hy j)

theorem co_degenerate (h : A ∈ coLip g p (dom p)) (hx : x ∈ dom p) (hy : y ∈ dom p)
    (hz : g.d j (p.func x) (p.func y) = 0) (hp : 0 < g.d i x y) : A i j = 0 := by
  have ht := co_term h hx hy i j
  rw [hz] at ht
  have he : A i j * g.d i x y = 0 := le_antisymm ht (zero_le _)
  exact (mul_eq_zero.mp he).resolve_right hp.ne'

def CloseOn (g : Gauge X I b) (p q : Operator X b) (U : Set X) (δ : I → ENNReal) :=
  U ⊆ dom p ∩ dom q ∧ ∀ z ∈ U, ∀ j, g.d j (p.func z) (q.func z) ≤ δ j

variable {δ : I → ENNReal}

theorem close_swap (h : CloseOn g p q U δ) : CloseOn g q p U δ :=
  ⟨fun _ hz => (h.1 hz).symm, fun z hz j => (g.metric j).symm _ _ ▸ h.2 z hz j⟩

theorem perturb (h : CloseOn g p q U δ) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    g.d j (q.func x) (q.func y) ≤ g.d j (p.func x) (p.func y) + δ j + δ j := by
  calc
    _ ≤ g.d j (q.func x) (p.func x) + g.d j (p.func x) (q.func y) :=
      (g.metric j).triangle _ _ _
    _ ≤ δ j + (g.d j (p.func x) (p.func y) + δ j) :=
      add_le_add ((close_swap h).2 x hx j)
        (((g.metric j).triangle _ (p.func y) _).trans (add_le_add le_rfl (h.2 y hy j)))
    _ = _ := by rw [← add_assoc, add_comm (δ j) (g.d j _ _)]

theorem perturb_rev (h : CloseOn g p q U δ) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    g.d j (p.func x) (p.func y) ≤ g.d j (q.func x) (q.func y) + δ j + δ j :=
  perturb (close_swap h) hx hy j

theorem perturb_lip (h : CloseOn g p q U δ) (hA : A ∈ lip g p U)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    g.d j (q.func x) (q.func y) ≤ act A (vec g x y) j + δ j + δ j :=
  (perturb h hx hy j).trans (add_le_add (add_le_add (hA.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_co (h : CloseOn g p q U δ) (hA : A ∈ coLip g p U)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (vec g x y) j ≤ g.d j (q.func x) (q.func y) + δ j + δ j :=
  (hA.2.2 x hx y hy j).trans (perturb_rev h hx hy j)

end HCH02
```

```lean filename=Chains.lean
import Bounds
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fin.Tuple.Basic

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical
noncomputable section
namespace HCH02

variable {X I : Type} {b : X} [Fintype I]
abbrev Op (X : Type) (b : X) := Operator X b

def eye : Mat I := fun i j => if i = j then 1 else 0

def product : {n : ℕ} → (Fin n → Mat I) → Mat I
  | 0, _ => eye
  | _+1, M => mul (product (Fin.tail M)) (M 0)

theorem product_one (M : Fin 1 → Mat I) : product M = M 0 := by
  funext i j
  simp [product, mul, eye, ite_mul]

theorem product_order {n} (M : Fin n → Mat I) :
    display (product M) = (List.ofFn (display ∘ M)).reverse.prod := by
  induction n with
  | zero =>
    change display eye = 1
    ext j i
    simp [display, eye, Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton,
      product, display_mul, ih]
    rfl

def chain : {n : ℕ} → (Fin n → Op X b) → Op X b
  | 0, _ => OperatorChain []
  | _+1, f => comp (chain (Fin.tail f)) (f 0)

private theorem append_one (fs : List (Op X b)) (p : Op X b) :
    OperatorChain (fs ++ [p]) = comp (OperatorChain fs) p := by
  induction fs with
  | nil => rfl
  | cons q fs ih =>
    ext x
    change q.func ((OperatorChain (fs ++ [p])).func x) = _
    rw [ih]
    rfl

theorem chain_order {n} (f : Fin n → Op X b) :
    chain f = OperatorChain (List.ofFn f).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.reverse_cons, append_one, chain, ih]
    rfl

def stage : {n : ℕ} → (Fin n → Op X b) → Set X → Fin (n+1) → Set X
  | 0, _, U, _ => U
  | _+1, f, U, t => Fin.cases U (stage (Fin.tail f) (operator_image (f 0) U)) t

theorem stage_zero {n} (f : Fin n → Op X b) (U) : stage f U 0 = U := by cases n <;> rfl

theorem stage_next {n} (f : Fin n → Op X b) (U) (m : Fin n) :
    stage f U m.succ = operator_image (f m) (stage f U m.castSucc) := by
  induction n generalizing U with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ih (Fin.tail f) (operator_image (f 0) U) k) m
    exact stage_zero (Fin.tail f) _

theorem final_image {n} (f : Fin n → Op X b) (U) :
    stage f U (Fin.last n) = operator_image (chain f) U := by
  induction n generalizing U with
  | zero => simp [stage, operator_image, chain, OperatorChain]
  | succ n ih =>
    exact (ih (Fin.tail f) (operator_image (f 0) U)).trans (Set.image_image _ _ _)

theorem step_domains {n} (f : Fin n → Op X b) (U) (h : U ⊆ dom (chain f)) :
    ∀ m, stage f U m.castSucc ⊆ dom (f m) := by
  induction n generalizing U with
  | zero => exact fun m => m.elim0
  | succ n ih =>
    obtain ⟨h₀, ht⟩ := comp_domain.mp h
    exact Fin.cases h₀ (ih (Fin.tail f) _ ht)

def Steps {n} (C : Op X b → Set X → Set (Mat I)) (f : Fin n → Op X b)
    (U : Set X) (M : Fin n → Mat I) := ∀ m, M m ∈ C (f m) (stage f U m.castSucc)

omit [Fintype I] in
theorem steps_from {n} {f : Fin n → Op X b} {U : Set X} {V : Fin (n+1) → Set X}
    {C : Op X b → Set X → Set (Mat I)} {M : Fin n → Mat I}
    (h₀ : V 0 = U) (hv : ∀ m, V m.succ = operator_image (f m) (V m.castSucc))
    (hm : ∀ m, M m ∈ C (f m) (V m.castSucc)) : Steps C f U M := by
  have he (t) : V t = stage f U t := by
    induction t using Fin.induction with
    | zero => exact h₀.trans (stage_zero f U).symm
    | succ m ih => rw [hv, stage_next, ih]
  exact fun m => he m.castSucc ▸ hm m

theorem eye_act (v : I → ENNReal) (j : I) : act eye v j = v j := by
  simp [act, eye, ite_mul]

variable [Nonempty I] {g : Gauge X I b} {U : Set X}

theorem empty_lip (h : U ⊆ dom (OperatorChain ([] : List (Op X b)))) :
    eye ∈ lip g (OperatorChain []) U :=
  ⟨h, fun _ _ _ _ j => (eye_act _ j).ge⟩

theorem empty_co (h : U ⊆ dom (OperatorChain ([] : List (Op X b)))) (hu : U.Nonempty) :
    eye ∈ coLip g (OperatorChain []) U :=
  ⟨hu, h, fun _ _ _ _ j => (eye_act _ j).le⟩

theorem chain_lip {n} {f : Fin n → Op X b} {M : Fin n → Mat I}
    (h : U ⊆ dom (chain f)) (hs : Steps (lip g) f U M) :
    product M ∈ lip g (chain f) U := by
  induction n generalizing U with
  | zero => exact empty_lip h
  | succ n ih =>
    exact lip_comp h (hs 0) (ih (comp_domain.mp h).2 (fun m => hs m.succ))

private theorem chain_co_aux {n} {f : Fin n → Op X b} {M : Fin n → Mat I}
    (hu : U.Nonempty) (h : U ⊆ dom (chain f)) (hs : Steps (coLip g) f U M) :
    product M ∈ coLip g (chain f) U := by
  induction n generalizing U with
  | zero => exact empty_co h hu
  | succ n ih =>
    exact co_comp h (hs 0) (ih (hu.image _) (comp_domain.mp h).2 (fun m => hs m.succ))

theorem chain_co {n} {f : Fin (n+1) → Op X b} {M : Fin (n+1) → Mat I}
    (h : U ⊆ dom (chain f)) (hs : Steps (coLip g) f U M) :
    product M ∈ coLip g (chain f) U := chain_co_aux (hs 0).1 h hs

abbrev Path (I : Type) (n : ℕ) := Fin n → I

def edges : {n : ℕ} → (Fin (n+1) → Mat I) → I → I → Path I n → List ENNReal
  | 0, M, i, j, _ => [M 0 i j]
  | _+1, M, i, j, p => M 0 i (p 0) :: edges (Fin.tail M) (p 0) j (Fin.tail p)

omit [Fintype I] [Nonempty I] in
theorem edges_indexed {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) :
    edges M i j p = List.ofFn (fun m => M m (Fin.cons (α := fun _ => I) i p m)
      (Fin.snoc (α := fun _ => I) p j m)) := by
  induction n generalizing i with
  | zero => simp [edges, List.ofFn_succ, Fin.snoc_zero]
  | succ n ih =>
    have hs : Fin.snoc (α := fun _ => I) p j =
        Fin.cons (p 0) (Fin.snoc (α := fun _ => I) (Fin.tail p) j) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    rw [List.ofFn_succ, edges, ih, hs]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.cons_self_tail, Fin.tail]

def weight {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) := (edges M i j p).prod
def hasZero {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) := 0 ∈ edges M i j p
def allPos {n} (M : Fin (n+1) → Mat I) (i j) (p : Path I n) := ∀ a ∈ edges M i j p, 0 < a

abbrev one_path : Unique (Path I 0) := inferInstance

omit [Nonempty I] in
theorem expansion {n} (M : Fin (n+1) → Mat I) (i j : I) :
    product M i j = ∑ p : Path I n, weight M i j p := by
  induction n generalizing i with
  | zero => simp [product_one, weight, edges]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => I)
    rw [← e.sum_comp (weight M i j), Fintype.sum_prod_type]
    change (∑ k, product (Fin.tail M) k j * M 0 i k) = _
    apply Finset.sum_congr rfl
    intro k _
    rw [ih (Fin.tail M) k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    simp [e, Fin.consEquiv, weight, edges, mul_comm]

omit [Nonempty I] in
theorem product_zero {n} (M : Fin (n+1) → Mat I) (i j) :
    product M i j = 0 ↔ ∀ p, hasZero M i j p := by
  rw [expansion]
  simp [weight, hasZero, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le _)]

omit [Nonempty I] in
theorem product_pos {n} (M : Fin (n+1) → Mat I) (i j) :
    0 < product M i j ↔ ∃ p, allPos M i j p := by
  rw [pos_iff_ne_zero, ne_eq, product_zero, not_forall]
  apply exists_congr
  intro p
  exact ⟨fun h a ha => pos_iff_ne_zero.mpr (by rintro rfl; exact h ha),
    fun h hz => (lt_irrefl 0) (h 0 hz)⟩

section Certified
variable {n : ℕ} {f : Fin (n+1) → Op X b} {L K : Fin (n+1) → Mat I}
theorem certified_zero (_h : U ⊆ dom (chain f)) (_hl : Steps (lip g) f U L)
    (_hk : Steps (coLip g) f U K) (i j : I) : product L i j = 0 ↔ ∀ p, hasZero L i j p :=
  product_zero L i j

theorem certified_pos (_h : U ⊆ dom (chain f)) (_hl : Steps (lip g) f U L)
    (_hk : Steps (coLip g) f U K) (i j : I) : 0 < product K i j ↔ ∃ p, allPos K i j p :=
  product_pos K i j

end Certified

end HCH02
```

```lean filename=Channels.lean
import Bounds
import Mathlib.Data.ENNReal.Inv

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical
noncomputable section
namespace HCH02

variable {I X : Type} {b : X}
abbrev Channel (I : Type) := I × I
def Row (A : Mat I) (i j : I) := ∀ k, k ≠ i → A k j = 0
def Col (A : Mat I) (i j : I) := ∀ k, k ≠ j → A i k = 0
def Diagonal (A : Mat I) := ∀ i j, i ≠ j → A i j = 0

variable [Fintype I] [Nonempty I]
def RowDec (g : Gauge X I b) (p : Operator X b) (U : Set X) (j : I) :=
  ∃ A ∈ lip g p U, ∃ i, Row A i j
def ColDec (g : Gauge X I b) (p : Operator X b) (U : Set X) (i : I) :=
  ∃ A ∈ lip g p U, ∃ j, Col A i j

abbrev Region (p : Operator X b) := {U : Set X // U ⊆ dom p}

def scalars (g : Gauge X I b) (p : Operator X b) (U : Region p) (i j : I) : Set ENNReal :=
  {r | ∀ x ∈ U.val, ∀ y ∈ U.val, g.d j (p.func x) (p.func y) ≤ r * g.d i x y}

def best (g : Gauge X I b) (p : Operator X b) (U : Region p) (i j : I) :=
  sInf (scalars g p U i j)

section Scalar
variable {g : Gauge X I b} {p : Operator X b} {U : Region p} {i j : I}
local notation "S" => scalars g p U i j
local notation "a" => best g p U i j

theorem best_empty (h : S = ∅) : a = ⊤ := by simp [best, h]

theorem obstructed {x y} (hx : x ∈ U.val) (hy : y ∈ U.val)
    (hz : g.d i x y = 0) (hp : 0 < g.d j (p.func x) (p.func y)) : S = ∅ ∧ a = ⊤ := by
  have he : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun r hr => by
    have h := hr x hx y hy
    rw [hz, mul_zero] at h
    exact hp.not_ge h
  exact ⟨he, best_empty he⟩

theorem scalar_up {r t : ENNReal} (hr : r ∈ S) (ht : r ≤ t) : t ∈ S :=
  fun x hx y hy => (hr x hx y hy).trans (mul_le_mul_left ht _)

theorem above_best {r : ENNReal} (h : a < r) : r ∈ S := by
  obtain ⟨t, ht, htr⟩ := sInf_lt_iff.mp h
  exact scalar_up ht htr.le

theorem zero_best {r : ENNReal} (h : a = 0) (hr : 0 < r) : r ∈ S :=
  above_best (h ▸ hr)

theorem finite_iff : a < ⊤ ↔ ∃ r ∈ S, r < ⊤ := sInf_lt_iff

theorem attained (hp : 0 < a) (hf : a < ⊤) : a ∈ S := by
  obtain ⟨r, hr, _⟩ := finite_iff.mp hf
  have hn : (⨅ t : S, (t : ENNReal)) ≠ 0 := by
    simpa only [best, sInf_eq_iInf'] using hp.ne'
  intro x hx y hy
  rw [best, sInf_eq_iInf', ENNReal.iInf_mul' (fun _ h => (hn h).elim) (fun _ => ⟨⟨r,hr⟩⟩)]
  exact le_iInf fun t => t.property x hx y hy

end Scalar

def discreteD (x y : Fin 3) : ENNReal := if x = y then 0 else ⊤

def exampleGauge : Gauge (Fin 3) Unit 0 where
  d _ := discreteD
  metric _ := {
    nonabsorbing := ⟨1, by decide⟩
    dist_self := by simp [discreteD]
    symm := by intro x y; simp [discreteD, eq_comm]
    triangle := by intro x y z; by_cases h : x = y <;> simp_all [discreteD]
    isolate_bot := by intro x hx; simp [discreteD, hx] }

def exampleId : Operator (Fin 3) 0 := ⟨id, rfl⟩
def exampleU : Region exampleId := ⟨dom exampleId, fun _ h => h⟩

theorem unattained_zero : exampleU.val.Nonempty ∧ best exampleGauge exampleId exampleU () () = 0 ∧
    0 ∉ scalars exampleGauge exampleId exampleU () () := by
  have h₁ : (1 : Fin 3) ∈ exampleU.val := by change (1 : Fin 3) ≠ 0; decide
  have h₂ : (2 : Fin 3) ∈ exampleU.val := by change (2 : Fin 3) ≠ 0; decide
  have pos_mem {r : ENNReal} (hr : 0 < r) : r ∈ scalars exampleGauge exampleId exampleU () () := by
    intro x _ y _
    by_cases h : x = y <;> simp [exampleGauge, exampleId, discreteD, h, ENNReal.mul_top, hr.ne']
  refine ⟨⟨1,h₁⟩, ?_, ?_⟩
  · by_contra hn
    obtain ⟨r, hr, hlt⟩ := exists_between (pos_iff_ne_zero.mpr hn)
    exact hlt.not_ge (sInf_le (pos_mem hr))
  · intro hz
    have h := hz 1 h₁ 2 h₂
    have hne : (1 : Fin 3) ≠ 2 := by decide
    simp [exampleGauge, exampleId, discreteD, hne] at h

variable {g : Gauge X I b} {p : Operator X b} {U : Set X} {A K : Mat I} {i j : I} {x y : X}

omit [Nonempty I] in
theorem erase_term (h : A i j = 0) (v : I → ENNReal) :
    A i j * v i = 0 ∧ act A v j = ∑ k ∈ Finset.univ.erase i, A k j * v k := by
  refine ⟨by simp [h], ?_⟩
  have he := Finset.add_sum_erase Finset.univ (fun k => A k j * v k) (Finset.mem_univ i)
  simpa [act, h] using he.symm

theorem lip_erase (ha : A ∈ lip g p U) (h : A i j = 0) (hx : x ∈ U) (hy : y ∈ U) :
    A i j * g.d i x y = 0 ∧
    g.d j (p.func x) (p.func y) ≤ ∑ k ∈ Finset.univ.erase i, A k j * g.d k x y := by
  obtain ⟨hz, he⟩ := erase_term h (vec g x y)
  exact ⟨hz, (ha.2 x hx y hy j).trans_eq he⟩

theorem row_bound (ha : A ∈ lip g p U) (h : Row A i j) (hx : x ∈ U) (hy : y ∈ U) :
    g.d j (p.func x) (p.func y) ≤ A i j * g.d i x y := by
  apply (ha.2 x hx y hy j).trans_eq
  exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun k _ hk => by simp [h k hk])

omit [Fintype I] [Nonempty I] in
theorem col_term (hc : Col A i j) {k : I} (hk : k ≠ j) (v : I → ENNReal) :
    A i k * v i = 0 := by rw [hc k hk, zero_mul]

theorem column_contribution (_ha : A ∈ lip g p U) (hc : Col A i j)
    (_hx : x ∈ U) (_hy : y ∈ U) {k : I} (hk : k ≠ j) : A i k * g.d i x y = 0 :=
  col_term hc hk (vec g x y)

theorem diagonal_upper (ha : A ∈ lip g p U) (hd : Diagonal A) (j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    g.d j (p.func x) (p.func y) ≤ A j j * g.d j x y :=
  row_bound ha (fun k hk => hd k j hk) hx hy

def ScalarBounds (g : Gauge X I b) (p : Operator X b) (U : Set X)
    (j : I) (lo hi : ENNReal) := ∀ x ∈ U, ∀ y ∈ U,
  lo * g.d j x y ≤ g.d j (p.func x) (p.func y) ∧ g.d j (p.func x) (p.func y) ≤ hi * g.d j x y

theorem bilateral (ha : A ∈ lip g p U) (hk : K ∈ coLip g p U) (h : Row A j j) :
    ScalarBounds g p U j (K j j) (A j j) :=
  fun _ hx _ hy => ⟨co_term hk hx hy j j, row_bound ha h hx hy⟩

theorem all_bilateral (ha : A ∈ lip g p U) (hk : K ∈ coLip g p U) (h : ∀ j, Row A j j) :
    ∀ j, ScalarBounds g p U j (K j j) (A j j) := fun j => bilateral ha hk (h j)

theorem finite_bilateral (ha : A ∈ lip g p U) (hk : K ∈ coLip g p U) (h : ∀ j, Row A j j)
    (hf : ∀ j, K j j < ⊤ ∧ A j j < ⊤) (j : I) : ∃ lo hi : NNReal,
    (lo : ENNReal) = K j j ∧ (hi : ENNReal) = A j j ∧ ScalarBounds g p U j lo hi := by
  refine ⟨(K j j).toNNReal, (A j j).toNNReal, ?_⟩
  simp only [ENNReal.coe_toNNReal (hf j).1.ne, ENNReal.coe_toNNReal (hf j).2.ne, true_and]
  exact all_bilateral ha hk h j

theorem distinguish (hk : K ∈ coLip g p U) (h : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U)
    (hd : 0 < g.d i x y) : 0 < g.d j (p.func x) (p.func y) :=
  (pos_iff_ne_zero.mpr (mul_ne_zero h.ne' hd.ne')).trans_le (co_term hk hx hy i j)

theorem reflect_zero (hk : K ∈ coLip g p U) (h : ∀ j, 0 < K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hz : GaugeZeroRelated g.d (p.func x) (p.func y)) : GaugeZeroRelated g.d x y := by
  intro j
  by_contra hn
  exact (distinguish hk (h j) hx hy (pos_iff_ne_zero.mpr hn)).ne' (hz j)

end HCH02
```

### 离线项目配置

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "HCH02"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
path = ".lake/packages/mathlib-5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "Main"
roots = ["formal_oet.vol_01.ch_01_foundations.gauge_space",
         "formal_oet.vol_01.ch_01_foundations.operator_space",
         "Bounds", "Chains", "Channels", "Main"]
```

```json filename=lake-manifest.json
{
  "version": "1.1.0",
  "name": "HCH02",
  "packagesDir": ".lake/packages",
  "lakeDir": ".lake",
  "packages": [
    {"name":"Cli","type":"path","inherited":true,"dir":".lake/packages/Cli","configFile":"lakefile.toml"},
    {"name":"LeanSearchClient","type":"path","inherited":true,"dir":".lake/packages/LeanSearchClient","configFile":"lakefile.toml"},
    {"name":"Qq","type":"path","inherited":true,"dir":".lake/packages/Qq","configFile":"lakefile.toml"},
    {"name":"aesop","type":"path","inherited":true,"dir":".lake/packages/aesop","configFile":"lakefile.toml"},
    {"name":"batteries","type":"path","inherited":true,"dir":".lake/packages/batteries","configFile":"lakefile.toml"},
    {"name":"importGraph","type":"path","inherited":true,"dir":".lake/packages/importGraph","configFile":"lakefile.toml"},
    {"name":"mathlib","type":"path","inherited":false,"dir":".lake/packages/mathlib-5e932f97dd25535344f80f9dd8da3aab83df0fe6","configFile":"lakefile.lean"},
    {"name":"plausible","type":"path","inherited":true,"dir":".lake/packages/plausible","configFile":"lakefile.toml"},
    {"name":"proofwidgets","type":"path","inherited":true,"dir":".lake/packages/proofwidgets","configFile":"lakefile.lean"}
  ]
}
```

```python filename=prepare.py
"""Connect the project to the pinned local Lake package cache."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
entries = json.loads((root / "lake-manifest.json").read_text())["packages"]
if len(sys.argv) > 1:
    cache = Path(sys.argv[1]).resolve()
    paths = {e["name"]: cache / e["name"] for e in entries}
else:
    packages = json.loads((root / "environment.json").read_text())["public_packages"]
    paths = {p["name"]: Path(p["path"]).resolve() for p in packages}

def revision(path):
    head = path / ".git" / "HEAD"
    if head.is_file():
        value = head.read_text().strip()
        if not value.startswith("ref:"):
            return value
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()

pin = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"
if revision(paths["mathlib"]) != pin:
    raise SystemExit("mathlib revision differs from " + pin)
lock = json.loads((paths["mathlib"] / "lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in lock["packages"]}
pins["mathlib"] = pin
for entry in entries:
    name = entry["name"]
    src = paths[name].resolve()
    if revision(src) != pins[name]:
        raise SystemExit("revision mismatch for " + name)
    dst = root / entry["dir"]
    if dst.resolve() != src:
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.symlink_to(src, target_is_directory=True)
```

### 对齐清单

```json filename=alignment.json
{
  "case_id":"HCH02",
  "version":"0.1.0",
  "items":[
    {"id":"HC02-D01","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.Gauge"},{"file":"Bounds.lean","name":"HCH02.lip"},{"file":"Bounds.lean","name":"HCH02.globalLip"},{"file":"Bounds.lean","name":"HCH02.infinite_term"}],"representation":"有限非空 I 上的 Gauge 逐分量采用冻结的扩展伪度量。lip 要求 U 包含于定义域且每对点、每个输出满足 ENNReal 加权和上界。globalLip 取整个定义域。","dependencies":["HC02-D03"]},
    {"id":"HC02-D02","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.coLip"},{"file":"Bounds.lean","name":"HCH02.co_term"}],"representation":"coLip 的成员条件同时要求 U 非空、U 包含于定义域及所有点对与输出的和式下界。co_term 提取任意一个输入项。","dependencies":["HC02-D03"]},
    {"id":"HC02-D03","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.Mat"},{"file":"Bounds.lean","name":"HCH02.display"},{"file":"Bounds.lean","name":"HCH02.mul"},{"file":"Bounds.lean","name":"HCH02.display_mul"},{"file":"Bounds.lean","name":"HCH02.act"},{"file":"Bounds.lean","name":"HCH02.act_mul"}],"representation":"A i j 从输入 i 指向输出 j。display A j i 等于 A i j，display_mul 证明该乘积对应普通矩阵乘法，act_mul 证明它对距离向量的作用。","dependencies":[]},
    {"id":"HC02-D04","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.eye"},{"file":"Chains.lean","name":"HCH02.product"},{"file":"Chains.lean","name":"HCH02.product_one"},{"file":"Chains.lean","name":"HCH02.product_order"}],"representation":"eye 为 Kronecker 单位矩阵。product 对空元组返回 eye，对一步返回 M 0。product_order 将施行顺序的反序表映为普通矩阵乘积。","dependencies":["HC02-D03"]},
    {"id":"HC02-D05","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.comp"},{"file":"Bounds.lean","name":"HCH02.comp_domain"},{"file":"Chains.lean","name":"HCH02.chain"},{"file":"Chains.lean","name":"HCH02.chain_order"},{"file":"Chains.lean","name":"HCH02.stage"},{"file":"Chains.lean","name":"HCH02.stage_zero"},{"file":"Chains.lean","name":"HCH02.stage_next"},{"file":"Chains.lean","name":"HCH02.final_image"},{"file":"Chains.lean","name":"HCH02.step_domains"},{"file":"Chains.lean","name":"HCH02.Steps"},{"file":"Chains.lean","name":"HCH02.steps_from"}],"representation":"Fin n 按施行顺序编号。chain_order 对应冻结的 OperatorChain。stage 从 U 逐步取像，末项等于全复合像。全复合的定义域条件推出逐步合法域，steps_from 将正文递推域上的逐步数据转为 Steps。","dependencies":["HC02-D03"]},
    {"id":"HC02-D06","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.Path"},{"file":"Chains.lean","name":"HCH02.edges"},{"file":"Chains.lean","name":"HCH02.edges_indexed"},{"file":"Chains.lean","name":"HCH02.weight"},{"file":"Chains.lean","name":"HCH02.hasZero"},{"file":"Chains.lean","name":"HCH02.allPos"},{"file":"Chains.lean","name":"HCH02.one_path"},{"file":"Chains.lean","name":"HCH02.expansion"}],"representation":"n+1 步的中间序列为全部 Fin n → I。edges_indexed 逐层给出固定端点间的边。weight 是边乘积，hasZero 和 allPos 分别量化零边与全正边。Fin 0 的元组唯一，expansion 对所有路径求和。","dependencies":["HC02-D03","HC02-D04"]},
    {"id":"HC02-D07","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.Channel"},{"file":"Channels.lean","name":"HCH02.Row"},{"file":"Channels.lean","name":"HCH02.Col"},{"file":"Channels.lean","name":"HCH02.Diagonal"},{"file":"Channels.lean","name":"HCH02.RowDec"},{"file":"Channels.lean","name":"HCH02.ColDec"}],"representation":"通道为 I × I。Row 和 Col 分别固定输出与输入并允许任意保留位置。行、列解耦在合法 Lip 族中存在量化矩阵及位置，Diagonal 要求所有非对角元为零。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D08","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.Region"},{"file":"Channels.lean","name":"HCH02.scalars"},{"file":"Channels.lean","name":"HCH02.best"},{"file":"Channels.lean","name":"HCH02.best_empty"}],"representation":"Region 携带 U ⊆ dom p。scalars 对 U 内全部点对只使用指定输入和输出，best 在 ENNReal 中取 sInf，空族时为顶。","dependencies":[]},
    {"id":"HC02-P01","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.singleton_lip"}],"representation":"非空且 Subsingleton 的 I 正是单元素情形。固定其指标 i，证明全域成员资格与唯一标量不等式等价。","dependencies":["HC02-D01"]},
    {"id":"HC02-P02","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.restrict_global"}],"representation":"取 V 为 dom p，由受限族包含关系得到全域证书在 U 上合法。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P03","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.restrict_lip"}],"representation":"由 U ⊆ V 将任一 V 上证书的定义域条件和全称点对界限制到 U。","dependencies":["HC02-D01"]},
    {"id":"HC02-P04","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.entryInf"},{"file":"Bounds.lean","name":"HCH02.entryInf_le"}],"representation":"对证书族在条目评价 A ↦ A i j 下的像取 sInf。缩域扩大像集，因此其下确界不增。","dependencies":["HC02-P03"]},
    {"id":"HC02-P05","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.lip_comp"}],"representation":"两步的输入依次为 U 和第一步的实际像。用 act 的单调性和乘积恒等式，把两个上界合成为 mul B A 的上界。","dependencies":["HC02-D01","HC02-D03","HC02-D05"]},
    {"id":"HC02-P06","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.co_degenerate"}],"representation":"在 dom p 取题设点对，单项下界迫使系数与正输入距离的乘积为零，从而该条目为零。","dependencies":["HC02-D02"]},
    {"id":"HC02-P07","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.co_comp"}],"representation":"在相同实际像域合成两个下界，首步的非空性给出复合 co-Lip 成员资格中的非空性。","dependencies":["HC02-D02","HC02-D03","HC02-D05"]},
    {"id":"HC02-P08","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.CloseOn"},{"file":"Bounds.lean","name":"HCH02.close_swap"},{"file":"Bounds.lean","name":"HCH02.perturb"}],"representation":"CloseOn 含公共定义域与逐点逐分量扰动。两次三角不等式给出第二个算子的像距至多为第一个的像距加两份 δ j。","dependencies":[]},
    {"id":"HC02-P09","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_rev"}],"representation":"用伪度量的对称性交换 CloseOn 中的两个算子，应用正向扰动界。","dependencies":["HC02-P08"]},
    {"id":"HC02-P10","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_lip"}],"representation":"将第一个算子的合法矩阵上界代入正向扰动界。两个算子任意，可用 close_swap 交换。","dependencies":["HC02-D01","HC02-P08"]},
    {"id":"HC02-P11","status":"complete","declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_co"}],"representation":"将第一个算子的合法矩阵下界与反向扰动界串联，保留加性误差的方向。","dependencies":["HC02-D02","HC02-P09"]},
    {"id":"HC02-P12","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.chain_lip"}],"representation":"对所有有限长度，逐步实际域上的指定上界矩阵给出全复合在 U 上的 product M，归纳首步和尾链。","dependencies":["HC02-D04","HC02-D05","HC02-P05","HC02-P14"]},
    {"id":"HC02-P13","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.chain_co"}],"representation":"长度为 n+1 时从首步证书得 U 非空。尾链使用实际像及其非空性，归纳合成指定下界矩阵。","dependencies":["HC02-D04","HC02-D05","HC02-P07","HC02-P15"]},
    {"id":"HC02-P14","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.eye_act"},{"file":"Chains.lean","name":"HCH02.empty_lip"}],"representation":"零步算子为冻结的空链恒等算子。单位作用保留距离向量，故对每个合法 U 都给出上界，包括非空 U。","dependencies":["HC02-D01","HC02-D04"]},
    {"id":"HC02-P15","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.empty_co"}],"representation":"对非空且包含于恒等算子定义域的 U，用同一单位作用等式得到下界证书。","dependencies":["HC02-D02","HC02-D04","HC02-P14"]},
    {"id":"HC02-P16","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.product_zero"},{"file":"Chains.lean","name":"HCH02.certified_zero"}],"representation":"在长度 n+1 的同一链、合法起始域和两类逐步证书下，上界乘积条目为零等价于每条完整路径有零边。一步时只有唯一边。","dependencies":["HC02-D01","HC02-D02","HC02-D04","HC02-D05","HC02-D06"]},
    {"id":"HC02-P17","status":"complete","declarations":[{"file":"Chains.lean","name":"HCH02.product_pos"},{"file":"Chains.lean","name":"HCH02.certified_pos"}],"representation":"在相同链和证书条件下，对乘积零值判据取否定得到下界乘积严格正当且仅当存在每边均正的路径，含一步情形。","dependencies":["HC02-D01","HC02-D02","HC02-D04","HC02-D05","HC02-D06","HC02-P16"]},
    {"id":"HC02-P18","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.obstructed"}],"representation":"同一合法域中，输入零距而输出正距的见证点对排除所有 ENNReal 常数，从而族为空且 best 为顶。","dependencies":["HC02-D08"]},
    {"id":"HC02-P19","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.attained"}],"representation":"正且有限的 best 本身满足全部点对界。有限性给出非空可行族，正性排除与无限输入距离相乘时的零下确界例外。","dependencies":["HC02-D08","HC02-P24"]},
    {"id":"HC02-P20","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.scalar_up"}],"representation":"任一可行 r 及任意 t ≥ r 逐点用乘法单调性得到 t 可行。","dependencies":["HC02-D08"]},
    {"id":"HC02-P21","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.above_best"}],"representation":"对任意 r > best 取小于 r 的可行元并上推。这涵盖正有限下确界及 r 为顶的情况。","dependencies":["HC02-D08","HC02-P20"]},
    {"id":"HC02-P22","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.zero_best"}],"representation":"把 best = 0 代入严格超过下确界的判据，得到每个正常数可行，特别包括所有有限正常数。","dependencies":["HC02-P21"]},
    {"id":"HC02-P23","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.discreteD"},{"file":"Channels.lean","name":"HCH02.exampleGauge"},{"file":"Channels.lean","name":"HCH02.exampleId"},{"file":"Channels.lean","name":"HCH02.exampleU"},{"file":"Channels.lean","name":"HCH02.unattained_zero"}],"representation":"Fin 3 以 0 为吸收元，Unit 指标的不同点相距顶。恒等算子的定义域含 1 和 2。所有正数可行，故下确界为零，点对 (1,2) 排除零常数。","dependencies":["HC02-D08"]},
    {"id":"HC02-P24","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.finite_iff"}],"representation":"用完整线性序的 sInf 严格小于顶判据，得到存在小于顶的可行元的充要性。","dependencies":["HC02-D08"]},
    {"id":"HC02-P25","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.erase_term"},{"file":"Channels.lean","name":"HCH02.lip_erase"}],"representation":"零系数对任意 ENNReal 向量的贡献为零。将删项等式用于合法 Lip 证书和域内点对，得到删去 i 后的输出上界。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P26","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.row_bound"}],"representation":"对合法 A 的第 j 行，除任意指定 i 外的系数为零便可把和化为 A i j 乘以第 i 输入距。","dependencies":["HC02-D01","HC02-D07"]},
    {"id":"HC02-P27","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.col_term"},{"file":"Channels.lean","name":"HCH02.column_contribution"}],"representation":"在给定合法证书和域内点对上，固定输入列 i 的贡献对每个 k ≠ j 为零。","dependencies":["HC02-D01","HC02-D07"]},
    {"id":"HC02-P28","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.diagonal_upper"}],"representation":"对角条件给每个输出 j 的 Row A j j，对任意域内点对得到对角标量上界。","dependencies":["HC02-D07","HC02-P26"]},
    {"id":"HC02-P29","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.ScalarBounds"},{"file":"Channels.lean","name":"HCH02.bilateral"}],"representation":"ScalarBounds 同时量化同一对域内点的下界与上界。上界仅需 A 的指定行稀疏，下界从 K 的对角项提取。","dependencies":["HC02-D02","HC02-P26"]},
    {"id":"HC02-P30","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.all_bilateral"},{"file":"Channels.lean","name":"HCH02.finite_bilateral"}],"representation":"将同一双侧界量化到全部 j。若两类对角系数逐分量有限，给出对应 NNReal 系数、强制转换后的等式及同一双侧界。","dependencies":["HC02-P29"]},
    {"id":"HC02-P31","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.distinguish"}],"representation":"正的 co-Lip 条目乘以正的输入距仍为正，由单项下界传到指定输出距。","dependencies":["HC02-D02"]},
    {"id":"HC02-P32","status":"complete","declarations":[{"file":"Channels.lean","name":"HCH02.reflect_zero"}],"representation":"若全部对角下界条目正，对每个分量应用可分辨保持，得到输出族零距蕴含输入族零距，直接使用冻结的 GaugeZeroRelated。","dependencies":["HC02-P31"]}
  ]
}
```

**完成范围**：已按冻结原文和 `obligations.json` 完整完成并逐项对齐整章。8 项定义与表示、32 项事实与反例均为 `complete`。未完成或未确认的范围为空。