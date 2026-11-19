已完成清单中的全部 **20 项义务**。项目使用 Lean 4.29.1 和指定的 mathlib 提交，通过了基于本地缓存的离线 `lake build`。`leanchecker` 已重放全部目标模块及 `Main`，`alignment.json` 登记的 48 个声明所用公理的并集为 `propext`、`Classical.choice` 和 `Quot.sound`。

算子和矩阵均按作用时间编号，`chain_eq_operatorChain` 证明了该顺序与冻结模块的逆序列表表示相符。长度为 `n + 1` 的路径用 `Fin n → I` 保存中间指标，两端单独给出，因此单矩阵情形恰有一个空的中间指标序列。

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
name = "Main"
globs = ["Main", "LCH02.+", "formal_oet.vol_01.ch_01_foundations.+"]
```

```lean filename=Main.lean
import LCH02.Matrices
import LCH02.Bounds
import LCH02.Chains
import LCH02.Paths

/-!
本项目依据 Zhe Li（Glen Li / glenzli，ORCID 0009-0006-6536-3453）
《The Operator Evolution Theory》卷一 v1.0.0 第 2 章所选条目编写。
数学原著采用 CC BY 4.0，本项目新增 Lean 声明与证明。
https://glenzli.com/books/oet/
https://doi.org/10.5281/zenodo.21457931
https://gitlab.com/glenzli/oet-public
https://creativecommons.org/licenses/by/4.0/
-/
```

```lean filename=LCH02/Matrices.lean
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic

namespace LCH02

open scoped BigOperators Classical Matrix

abbrev Bound (I : Type*) := Matrix I I ENNReal

/-- The channel i → j occupies row j, column i. -/
abbrev entry {I : Type*} (A : Bound I) (i j : I) : ENNReal := A j i

variable {I : Type*}

theorem row_sum [Fintype I] (A : Bound I) (v : I → ENNReal) (j : I) :
    (A *ᵥ v) j = ∑ i, entry A i j * v i := rfl

theorem entry_mul [Fintype I] (B A : Bound I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

noncomputable abbrev unitMatrix (I : Type*) : Bound I := 1

theorem entry_one (i j : I) :
    entry (unitMatrix I) i j = if j = i then 1 else 0 :=
  Matrix.one_apply

/-- The family is indexed in time order, with the earliest factor on the right. -/
def orderedProd {M : Type*} [Monoid M] : {n : ℕ} → (Fin n → M) → M
  | 0, _ => 1
  | _ + 1, f => orderedProd (Fin.tail f) * f 0

variable {M : Type*} [Monoid M]

@[simp] theorem orderedProd_empty (f : Fin 0 → M) : orderedProd f = 1 := rfl

theorem orderedProd_succ {n : ℕ} (f : Fin (n + 1) → M) :
    orderedProd f = orderedProd (Fin.tail f) * f 0 := rfl

@[simp] theorem orderedProd_one (f : Fin 1 → M) : orderedProd f = f 0 := one_mul _

theorem orderedProd_eq_reverse_prod {n : ℕ} (f : Fin n → M) :
    orderedProd f = (List.ofFn f).reverse.prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orderedProd_succ, List.ofFn_succ, List.reverse_cons, List.prod_append,
      List.prod_singleton, ih]
    rfl

theorem mulVec_mono [Fintype I] (A : Bound I) {v w : I → ENNReal} (h : v ≤ w) :
    A *ᵥ v ≤ A *ᵥ w :=
  fun _ => Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) _

end LCH02
```

```lean filename=LCH02/Bounds.lean
import LCH02.Matrices
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical Matrix

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X b (dist i)

variable {X I : Type} {b : X} [Fintype I] [Nonempty I] (G : Gauge X I b)

def Gauge.vec (x y : X) : I → ENNReal := fun i => G.dist i x y

def LipOn (f : Operator X b) (U : Set X) (A : Bound I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, G.vec (f.func x) (f.func y) ≤ A *ᵥ G.vec x y

abbrev Lip (f : Operator X b) (A : Bound I) : Prop := LipOn G f (dom f) A

def lipFamily (f : Operator X b) (U : Set X) : Set (Bound I) := {A | LipOn G f U A}

def globalLipFamily (f : Operator X b) : Set (Bound I) := {A | Lip G f A}

def CoLipOn (f : Operator X b) (U : Set X) (A : Bound I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧
    ∀ x ∈ U, ∀ y ∈ U, A *ᵥ G.vec x y ≤ G.vec (f.func x) (f.func y)

def coLipFamily (f : Operator X b) (U : Set X) : Set (Bound I) := {A | CoLipOn G f U A}

variable {f g : Operator X b} {U V : Set X} {A B : Bound I}

theorem lip_singleton [Subsingleton I] (i : I) :
    Lip G f A ↔ ∀ x ∈ dom f, ∀ y ∈ dom f,
      G.dist i (f.func x) (f.func y) ≤ entry A i i * G.dist i x y := by
  have row (x y : X) : (A *ᵥ G.vec x y) i = entry A i i * G.dist i x y := by
    rw [row_sum]
    exact Finset.sum_eq_single i (fun k _ hk => (hk (Subsingleton.elim k i)).elim)
      (fun h => (h (Finset.mem_univ i)).elim)
  constructor
  · intro h x hx y hy
    exact (h.2 x hx y hy i).trans_eq (row x y)
  · intro h
    refine ⟨Set.Subset.refl _, fun x hx y hy j => ?_⟩
    obtain rfl := Subsingleton.elim j i
    exact (h x hx y hy).trans_eq (row x y).symm

theorem lip_restrict (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    lipFamily G f V ⊆ lipFamily G f U :=
  fun _ h => ⟨hUV.trans hV, fun x hx y hy => h.2 x (hUV hx) y (hUV hy)⟩

theorem global_lip_restrict (hU : U ⊆ dom f) :
    globalLipFamily G f ⊆ lipFamily G f U :=
  lip_restrict G hU (Set.Subset.refl _)

theorem coLip_restrict (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    coLipFamily G f V ⊆ coLipFamily G f U :=
  fun _ h => ⟨hne, hUV.trans hV, fun x hx y hy => h.2.2 x (hUV hx) y (hUV hy)⟩

theorem global_coLip_restrict (hne : U.Nonempty) (hU : U ⊆ dom f) :
    coLipFamily G f (dom f) ⊆ coLipFamily G f U :=
  coLip_restrict G hne hU (Set.Subset.refl _)

theorem coLip_entry_zero (i j : I) {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hout : G.dist j (f.func x) (f.func y) = 0) (hin : 0 < G.dist i x y)
    (hA : A ∈ coLipFamily G f (dom f)) : entry A i j = 0 := by
  have hterm : entry A i j * G.dist i x y ≤ (A *ᵥ G.vec x y) j :=
    Finset.single_le_sum (fun k _ => zero_le (A j k * G.dist k x y)) (Finset.mem_univ i)
  have h := hterm.trans (hA.2.2 x hx y hy j)
  change entry A i j * G.dist i x y ≤ G.dist j (f.func x) (f.func y) at h
  rw [hout] at h
  exact (mul_eq_zero.mp (le_antisymm h (zero_le _))).resolve_right hin.ne'

theorem lip_compose (hU : U ⊆ dom (g * f)) (hf : A ∈ lipFamily G f U)
    (hg : B ∈ lipFamily G g (f.func '' U)) : B * A ∈ lipFamily G (g * f) U := by
  refine ⟨hU, fun x hx y hy => ?_⟩
  calc
    G.vec (g.func (f.func x)) (g.func (f.func y))
        ≤ B *ᵥ G.vec (f.func x) (f.func y) :=
      hg.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    _ ≤ B *ᵥ A *ᵥ G.vec x y := mulVec_mono B (hf.2 x hx y hy)
    _ = _ := Matrix.mulVec_mulVec _ _ _

theorem coLip_compose (hU : U ⊆ dom (g * f)) (hf : A ∈ coLipFamily G f U)
    (hg : B ∈ coLipFamily G g (f.func '' U)) : B * A ∈ coLipFamily G (g * f) U := by
  refine ⟨hf.1, hU, fun x hx y hy => ?_⟩
  calc
    (B * A) *ᵥ G.vec x y = B *ᵥ A *ᵥ G.vec x y := (Matrix.mulVec_mulVec _ _ _).symm
    _ ≤ B *ᵥ G.vec (f.func x) (f.func y) := mulVec_mono B (hf.2.2 x hx y hy)
    _ ≤ G.vec (g.func (f.func x)) (g.func (f.func y)) :=
      hg.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem identity_lip (_hne : U.Nonempty) (hU : U ⊆ dom (operator_identity (bot := b))) :
    unitMatrix I ∈ lipFamily G operator_identity U := by
  refine ⟨hU, fun x _ y _ => ?_⟩
  exact (Matrix.one_mulVec (G.vec x y)).symm.le

theorem identity_coLip (hne : U.Nonempty) (hU : U ⊆ dom (operator_identity (bot := b))) :
    unitMatrix I ∈ coLipFamily G operator_identity U := by
  refine ⟨hne, hU, fun x _ y _ => ?_⟩
  exact (Matrix.one_mulVec (G.vec x y)).le

end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.Bounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped Classical

variable {X : Type} {b : X}

/-- Time index zero is the first operator to act. -/
abbrev chain {n : ℕ} (f : Fin n → Operator X b) : Operator X b := orderedProd f

@[simp] theorem chain_empty (f : Fin 0 → Operator X b) : chain f = operator_identity := rfl

theorem chain_eq_operatorChain {n : ℕ} (f : Fin n → Operator X b) :
    chain f = OperatorChain (List.ofFn f).reverse := by
  rw [operator_chain_eq_prod]
  exact orderedProd_eq_reverse_prod f

/-- Stage zero is the initial set. Each recursive call starts on the exact image. -/
def stage : {n : ℕ} → (Fin n → Operator X b) → Set X → Fin (n + 1) → Set X
  | 0, _, U, _ => U
  | _ + 1, f, U, m => Fin.cases U (stage (Fin.tail f) ((f 0).func '' U)) m

@[simp] theorem stage_zero {n : ℕ} (f : Fin n → Operator X b) (U : Set X) :
    stage f U 0 = U := by cases n <;> rfl

theorem stage_succ {n : ℕ} (f : Fin n → Operator X b) (U : Set X) (m : Fin n) :
    stage f U m.succ = (f m).func '' stage f U m.castSucc := by
  induction n generalizing U with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) m
    · exact stage_zero (Fin.tail f) _
    · exact ih (Fin.tail f) _ k

theorem stage_last {n : ℕ} (f : Fin n → Operator X b) (U : Set X) :
    stage f U (Fin.last n) = (chain f).func '' U := by
  induction n generalizing U with
  | zero => exact (Set.image_id U).symm
  | succ n ih =>
    change stage (Fin.tail f) ((f 0).func '' U) (Fin.last n) = _
    rw [ih, Set.image_image]
    rfl

theorem stage_nonempty {n : ℕ} (f : Fin n → Operator X b) {U : Set X}
    (hU : U.Nonempty) (m : Fin (n + 1)) : (stage f U m).Nonempty := by
  induction n generalizing U with
  | zero => exact hU
  | succ n ih =>
    refine Fin.cases hU (fun k => ?_) m
    exact ih (Fin.tail f) (hU.image _) k

private theorem image_subset_dom {f g : Operator X b} {U : Set X}
    (hU : U ⊆ dom (g * f)) : f.func '' U ⊆ dom g := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU hx

theorem stage_subset_dom {n : ℕ} (f : Fin n → Operator X b) {U : Set X}
    (hU : U ⊆ dom (chain f)) (m : Fin n) : stage f U m.castSucc ⊆ dom (f m) := by
  induction n generalizing U with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) m
    · intro x hx hbot
      apply hU hx
      change (chain (Fin.tail f)).func ((f 0).func x) = b
      rw [hbot, (chain (Fin.tail f)).preserves_bot]
    · exact ih (Fin.tail f) (image_subset_dom hU) k

variable {I : Type} [Fintype I] [Nonempty I] (G : Gauge X I b)

theorem chain_lip {n : ℕ} (f : Fin (n + 1) → Operator X b)
    (A : Fin (n + 1) → Bound I) {U : Set X} (hU : U ⊆ dom (chain f))
    (h : ∀ m, A m ∈ lipFamily G (f m) (stage f U m.castSucc)) :
    orderedProd A ∈ lipFamily G (chain f) U := by
  induction n generalizing U with
  | zero => simpa only [chain, orderedProd_one, Fin.castSucc_zero, stage_zero] using h 0
  | succ n ih =>
    apply lip_compose G hU (by simpa only [Fin.castSucc_zero, stage_zero] using h 0)
    exact ih (Fin.tail f) (Fin.tail A) (image_subset_dom hU) (fun m => h m.succ)

theorem chain_coLip {n : ℕ} (f : Fin (n + 1) → Operator X b)
    (A : Fin (n + 1) → Bound I) {U : Set X} (hU : U ⊆ dom (chain f))
    (h : ∀ m, A m ∈ coLipFamily G (f m) (stage f U m.castSucc)) :
    orderedProd A ∈ coLipFamily G (chain f) U := by
  induction n generalizing U with
  | zero => simpa only [chain, orderedProd_one, Fin.castSucc_zero, stage_zero] using h 0
  | succ n ih =>
    apply coLip_compose G hU (by simpa only [Fin.castSucc_zero, stage_zero] using h 0)
    exact ih (Fin.tail f) (Fin.tail A) (image_subset_dom hU) (fun m => h m.succ)

end LCH02
```

```lean filename=LCH02/Paths.lean
import LCH02.Matrices

namespace LCH02

open scoped Classical

variable {I : Type*}

/-- For n+1 edges, the n intermediate vertices are free. The endpoints are separate. -/
abbrev IndexPath (I : Type*) (n : ℕ) := Fin n → I

theorem empty_path_unique (p : IndexPath I 0) : p = Fin.elim0 := Subsingleton.elim _ _

def pathEntry {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) (p : IndexPath I n)
    (m : Fin (n + 1)) : ENNReal :=
  entry (A m) (Fin.cons (α := fun _ => I) i p m) (Fin.snoc (α := fun _ => I) p j m)

def PositivePath {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) (p : IndexPath I n) : Prop :=
  ∀ m, 0 < pathEntry A i j p m

@[simp] theorem pathEntry_one (A : Fin 1 → Bound I) (i j : I) (p : IndexPath I 0)
    (m : Fin 1) : pathEntry A i j p m = entry (A 0) i j := by
  obtain rfl := Subsingleton.elim m 0
  rfl

private theorem positive_cons {n : ℕ} (A : Fin (n + 2) → Bound I) (i j k : I)
    (p : IndexPath I n) :
    PositivePath A i j (Fin.cons k p) ↔
      0 < entry (A 0) i k ∧ PositivePath (Fin.tail A) k j p := by
  unfold PositivePath
  rw [Fin.forall_fin_succ]
  simp only [pathEntry, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ, Fin.tail]

variable [Fintype I]

theorem product_pos_iff {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) :
    0 < entry (orderedProd A) i j ↔ ∃ p : IndexPath I n, PositivePath A i j p := by
  induction n generalizing i with
  | zero => simp [PositivePath, IndexPath]
  | succ n ih =>
    rw [orderedProd_succ, entry_mul, Finset.sum_pos_iff, Fin.exists_fin_succ_pi]
    simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff, ih, positive_cons]
    constructor
    · rintro ⟨k, ⟨p, hp⟩, hk⟩
      exact ⟨k, p, hk, hp⟩
    · rintro ⟨k, p, hk, hp⟩
      exact ⟨k, ⟨p, hp⟩, hk⟩

theorem product_zero_iff {n : ℕ} (A : Fin (n + 1) → Bound I) (i j : I) :
    entry (orderedProd A) i j = 0 ↔
      ∀ p : IndexPath I n, ∃ m, pathEntry A i j p m = 0 := by
  simpa only [PositivePath, not_exists, not_forall, not_lt, nonpos_iff_eq_zero] using
    not_congr (product_pos_iff A i j)

end LCH02
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
        {"file": "LCH02/Bounds.lean", "name": "LCH02.Gauge"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.Gauge.vec"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.LipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.Lip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipFamily"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.globalLipFamily"}
      ],
      "representation": "G 在有限非空指标 I 上给出冻结的扩展伪度量族。LipOn G f U A 要求 U ⊆ dom f，且对 U 中每对 x、y 及每个输出 j 成立行和上界。Lip 取 U = dom f，两个 Family 收集相应的全部 A。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.CoLipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipFamily"}
      ],
      "representation": "对任意 f、U、A，CoLipOn 同时要求 U 非空、U ⊆ dom f，以及每对 x、y ∈ U 的每个输出距离大于等于相应行和。coLipFamily 是满足这三个条件的矩阵集。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrices.lean", "name": "LCH02.Bound"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.entry"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.row_sum"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.entry_mul"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.mulVec_mono"}
      ],
      "representation": "Bound I 是 ENNReal 方阵。entry A i j = A j i。row_sum 展开第 j 个输出，entry_mul 对任意 i、j 给出先 A 后 B 的乘积条目，mulVec_mono 给出逐分量保序性。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrices.lean", "name": "LCH02.unitMatrix"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.entry_one"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.orderedProd"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.orderedProd_empty"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.orderedProd_succ"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.orderedProd_one"},
        {"file": "LCH02/Matrices.lean", "name": "LCH02.orderedProd_eq_reverse_prod"}
      ],
      "representation": "unitMatrix 的对角元为 1，其余为 0。对各长度 n 及时间顺序的 Fin n 矩阵族，orderedProd 的空积为 1，非空积为尾部乘积右乘首项，等于逆序列表乘积。单项积等于该项。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_empty"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_eq_operatorChain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stage"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stage_zero"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stage_succ"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stage_last"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stage_nonempty"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stage_subset_dom"}
      ],
      "representation": "f : Fin n → Operator X b 按作用顺序编号，chain 等于冻结 OperatorChain 读取逆序列表。stage f U r 是前 r 步的精确像，始于 U，末于全链的像。初集非空传至每层，初集包含于全链定义域推出每一步输入包含于该步定义域。",
      "dependencies": ["CH02-D04"]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.empty_path_unique"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathEntry"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.PositivePath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathEntry_one"}
      ],
      "representation": "对 n+1 个因子及任意端点 i、j，p : Fin n → I 自由选取全部中间指标。把 i 前置、j 后置所得的两个元组给出每条边的输入和输出。PositivePath 要求每条边严格正。单因子时中间元组唯一，唯一的边是 i → j。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_singleton"}
      ],
      "representation": "有限非空 I 再满足 Subsingleton I 即为单分量。对任意 i、f、A，合法全域 Lip 谓词等价于对所有定义域点对成立的标量不等式，系数为 entry A i i。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_restrict"}
      ],
      "representation": "固定 G、f，对任意 U ⊆ V ⊆ dom f，在 V 上合法的每个 Lip 矩阵均在 U 上合法。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_compose"}
      ],
      "representation": "f 先于 g 作用。给定 U ⊆ dom (g * f)、U 上的 A 和精确像 f.func '' U 上的 B，得到 B * A 在 U 上对 g * f 的 Lip 上界。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_restrict"}
      ],
      "representation": "对每个非空 U 及 U ⊆ V ⊆ dom f，coLipFamily G f V 包含于 coLipFamily G f U，结论保有 U 的非空性。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_entry_zero"}
      ],
      "representation": "对任意 i、j 和定义域中的见证 x、y，若第 j 个输出距离为零且第 i 个输入距离严格正，则任意在 dom f 上合法的 co-Lip 矩阵 A 满足 entry A i j = 0。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_compose"}
      ],
      "representation": "U ⊆ dom (g * f)，两步 co-Lip 矩阵分别取在 U 与 f.func '' U 上。结论给出原非空 U 上全复合的下界矩阵 B * A。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_lip"}
      ],
      "representation": "零步算子为冻结的 operator_identity。对任意非空 U ⊆ dom operator_identity，空积对应的 unitMatrix I 属于其受限 Lip 族。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.identity_coLip"}
      ],
      "representation": "对任意非空 U ⊆ dom operator_identity，单位矩阵给出逐分量相等式的下界方向，因而属于零步算子在 U 上的 co-Lip 族。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D04"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.product_pos_iff"}
      ],
      "representation": "对任意 n+1 个扩展非负矩阵及 i、j，乘积的 i → j 条目严格正当且仅当存在一组 n 个中间指标使每条边严格正。n = 0 是单矩阵情形。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.global_lip_restrict"}
      ],
      "representation": "对任意 U ⊆ dom f，取 V = dom f 得到全域 Lip 族至 U 上受限族的包含。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.global_coLip_restrict"}
      ],
      "representation": "对任意非空 U ⊆ dom f，将定义域上的全部合法 co-Lip 矩阵限制到 U。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_lip"}
      ],
      "representation": "以 n+1 表示任意正长度。给定 U ⊆ dom (chain f)，对每个步骤 m 仅要求 A m 在 stage f U m.castSucc 上是该步的 Lip 证书，归纳得到 orderedProd A 在初集 U 上界定全链。U 可为空。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P04"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_coLip"}
      ],
      "representation": "任取正长度 n+1 的 f 和 A，从全链定义域内的初集出发。逐步 co-Lip 成员关系在实际输入像域上量化并包含非空条件，连乘给出全链在同一初集上的合法 co-Lip 矩阵。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P08"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.product_zero_iff"}
      ],
      "representation": "对任意 n+1 个矩阵及端点 i、j，条目等于零当且仅当每一组 n 个中间指标都有至少一层 m 的边条目为零。对正值判据取否定即得此式。单矩阵时两侧均化为所选 i → j 条目等于零。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```