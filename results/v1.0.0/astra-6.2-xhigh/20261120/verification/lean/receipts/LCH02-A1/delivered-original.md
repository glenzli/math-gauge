20 项义务已全部完成。项目使用 Lean 4.29.1 和指定提交的 mathlib 离线构建通过。`leanchecker` 已重放三个目标模块及 `Main`，公理检查仅检出 `propext`、`Classical.choice` 和 `Quot.sound`。

链表按 `[末步, …, 首步]` 排列，与冻结模块的 `OperatorChain` 一致。`along_iff` 明确给出每一步的实际输入域。路径只存储内部指标，长度为一时内部路径类型为 `Unit`，因子列表恰含一个矩阵条目。

数学内容取自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory* 第一卷 v1.0.0，本次交付为所选条目的 Lean 形式化。[原著](https://doi.org/10.5281/zenodo.21457931) · [作品页](https://glenzli.com/books/oet/) · [作者 ORCID](https://orcid.org/0009-0006-6536-3453) · [源仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

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
roots = [
  "Main", "LCH02.Bounds", "LCH02.Chains", "LCH02.Paths",
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space"
]
```

```lean filename=Main.lean
import LCH02.Bounds
import LCH02.Chains
import LCH02.Paths
```

```lean filename=LCH02/Bounds.lean
/-
Formalization of selected results from Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, vol. I, v1.0.0, https://glenzli.com/books/oet/
Source DOI 10.5281/zenodo.21457931. License https://creativecommons.org/licenses/by/4.0/
-/
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped Classical
noncomputable section

abbrev Mat (I : Type) := Matrix I I ENNReal

variable {I X : Type} {b : X}

def entry (M : Mat I) (i j : I) : ENNReal := M j i

theorem entry_mul [Fintype I] (B A : Mat I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

theorem unit_entry (i j : I) :
    entry (1 : Mat I) i j = if j = i then 1 else 0 := Matrix.one_apply

/-- The last operation is at the head, as in the frozen OperatorChain. -/
def orderedProduct [Fintype I] (ms : List (Mat I)) : Mat I := ms.prod

@[simp] theorem product_nil [Fintype I] : orderedProduct ([] : List (Mat I)) = 1 := rfl

@[simp] theorem product_cons [Fintype I] (A : Mat I) (ms : List (Mat I)) :
    orderedProduct (A :: ms) = A * orderedProduct ms := rfl

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X b (d i)

variable [Fintype I] [Nonempty I] (G : Gauge X I b)

def Gauge.vec (x y : X) : I → ENNReal := fun i => G.d i x y

def LipOn (f : Operator X b) (U : Set X) (M : Mat I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U,
    G.vec (f.func x) (f.func y) ≤ M.mulVec (G.vec x y)

def IsLip (f : Operator X b) (M : Mat I) : Prop := LipOn G f (dom f) M

def lipFamilyOn (f : Operator X b) (U : Set X) : Set (Mat I) := {M | LipOn G f U M}

def lipFamily (f : Operator X b) : Set (Mat I) := {M | IsLip G f M}

def CoLipOn (f : Operator X b) (U : Set X) (M : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U,
    M.mulVec (G.vec x y) ≤ G.vec (f.func x) (f.func y)

def coLipFamilyOn (f : Operator X b) (U : Set X) : Set (Mat I) := {M | CoLipOn G f U M}

variable {f g : Operator X b} {U V : Set X} {A B : Mat I}

theorem singleton_lip [Subsingleton I] (i : I) :
    IsLip G f A ↔ ∀ x ∈ dom f, ∀ y ∈ dom f,
      G.d i (f.func x) (f.func y) ≤ entry A i i * G.d i x y := by
  have row (x y : X) : A.mulVec (G.vec x y) i = entry A i i * G.d i x y :=
    Fintype.sum_subsingleton (fun k => A i k * G.d k x y) i
  constructor
  · intro h x hx y hy
    exact (h.2 x hx y hy i).trans_eq (row x y)
  · intro h
    refine ⟨Set.Subset.rfl, fun x hx y hy j => ?_⟩
    obtain rfl : j = i := Subsingleton.elim _ _
    exact (h x hx y hy).trans_eq (row x y).symm

theorem lip_restrict (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    lipFamilyOn G f V ⊆ lipFamilyOn G f U :=
  fun _ h => ⟨hUV.trans hV, fun x hx y hy => h.2 x (hUV hx) y (hUV hy)⟩

theorem lip_from_dom (hU : U ⊆ dom f) : lipFamily G f ⊆ lipFamilyOn G f U :=
  lip_restrict G hU Set.Subset.rfl

theorem coLip_restrict (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    coLipFamilyOn G f V ⊆ coLipFamilyOn G f U :=
  fun _ h => ⟨hne, hUV.trans hV, fun x hx y hy => h.2.2 x (hUV hx) y (hUV hy)⟩

theorem coLip_from_dom (hne : U.Nonempty) (hU : U ⊆ dom f) :
    coLipFamilyOn G f (dom f) ⊆ coLipFamilyOn G f U :=
  coLip_restrict G hne hU Set.Subset.rfl

omit [Nonempty I] in
private theorem mulVec_mono (M : Mat I) {v w : I → ENNReal} (h : v ≤ w) :
    M.mulVec v ≤ M.mulVec w := fun j =>
  Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) (M j i)

theorem lip_comp (hU : U ⊆ dom (g * f)) (ha : A ∈ lipFamilyOn G f U)
    (hb : B ∈ lipFamilyOn G g (f.func '' U)) :
    B * A ∈ lipFamilyOn G (g * f) U := by
  refine ⟨hU, fun x hx y hy => ?_⟩
  have h := hb.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (h.trans (mulVec_mono B (ha.2 x hx y hy))).trans_eq (Matrix.mulVec_mulVec _ _ _)

theorem coLip_comp (hU : U ⊆ dom (g * f)) (ha : A ∈ coLipFamilyOn G f U)
    (hb : B ∈ coLipFamilyOn G g (f.func '' U)) :
    B * A ∈ coLipFamilyOn G (g * f) U := by
  refine ⟨ha.1, hU, fun x hx y hy => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  exact (mulVec_mono B (ha.2.2 x hx y hy)).trans (hb.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)

theorem coLip_zero_entry {i j : I} {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hout : G.d j (f.func x) (f.func y) = 0) (hin : 0 < G.d i x y)
    (ha : A ∈ coLipFamilyOn G f (dom f)) : entry A i j = 0 := by
  have term : entry A i j * G.d i x y ≤ A.mulVec (G.vec x y) j :=
    Finset.single_le_sum (f := fun k => A j k * G.d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have bound : entry A i j * G.d i x y ≤ 0 := (term.trans (ha.2.2 x hx y hy j)).trans_eq hout
  exact (mul_eq_zero.mp (le_antisymm bound (zero_le _))).resolve_right hin.ne'

theorem unit_lip (_hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X b)) :
    orderedProduct ([] : List (Mat I)) ∈ lipFamilyOn G 1 U :=
  ⟨hU, fun x _ y _ => (Matrix.one_mulVec (G.vec x y)).symm.le⟩

theorem unit_coLip (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X b)) :
    orderedProduct ([] : List (Mat I)) ∈ coLipFamilyOn G 1 U :=
  ⟨hne, hU, fun x _ y _ => (Matrix.one_mulVec (G.vec x y)).le⟩

end
end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.Bounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped Classical
noncomputable section

abbrev Step (X I : Type) (b : X) := Operator X b × Mat I

variable {X I : Type} {b : X}

def chain (s : List (Step X I b)) : Operator X b := OperatorChain (s.map Prod.fst)

def chainMatrix [Fintype I] (s : List (Step X I b)) : Mat I := orderedProduct (s.map Prod.snd)

def reached (s : List (Step X I b)) (U : Set X) : Set X := (chain s).func '' U

theorem chain_nil : chain ([] : List (Step X I b)) = 1 := rfl

theorem chain_cons (a : Step X I b) (s : List (Step X I b)) :
    chain (a :: s) = a.1 * chain s := rfl

theorem reached_nil (U : Set X) : reached ([] : List (Step X I b)) U = U := Set.image_id U

theorem reached_cons (a : Step X I b) (s : List (Step X I b)) (U : Set X) :
    reached (a :: s) U = a.1.func '' reached s U :=
  (Set.image_image a.1.func (chain s).func U).symm

/-- Each suffix is the part of the chain already executed. -/
def Along (P : Operator X b → Set X → Mat I → Prop) (U : Set X) : List (Step X I b) → Prop
  | [] => True
  | a :: s => Along P U s ∧ P a.1 (reached s U) a.2

theorem along_iff (P : Operator X b → Set X → Mat I → Prop) (U : Set X) (s : List (Step X I b)) :
    Along P U s ↔ ∀ n (hn : n < s.length), P s[n].1 (reached (s.drop (n + 1)) U) s[n].2 := by
  induction s with
  | nil => simp [Along]
  | cons a s ih =>
    constructor
    · intro h n hn
      cases n with
      | zero => exact h.2
      | succ n => exact ih.mp h.1 n (Nat.lt_of_succ_lt_succ hn)
    · intro h
      exact ⟨ih.mpr (fun n hn => h (n + 1) (Nat.succ_lt_succ hn)), h 0 (Nat.zero_lt_succ _)⟩

private theorem split_domain {f g : Operator X b} {U : Set X} (h : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx heq
    apply h hx
    change g.func (f.func x) = b
    rw [heq, g.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact h hx

theorem step_domains (s : List (Step X I b)) {U : Set X} (hd : U ⊆ dom (chain s)) :
    Along (fun f V _ => V ⊆ dom f) U s := by
  induction s with
  | nil => trivial
  | cons a s ih =>
    obtain ⟨hpre, him⟩ := split_domain (f := chain s) (g := a.1) hd
    exact ⟨ih hpre, him⟩

variable [Fintype I] [Nonempty I] (G : Gauge X I b) {U : Set X}

theorem finite_lip (a : Step X I b) (s : List (Step X I b)) (hd : U ⊆ dom (chain (a :: s)))
    (hs : Along (LipOn G) U (a :: s)) : chainMatrix (a :: s) ∈ lipFamilyOn G (chain (a :: s)) U := by
  induction s generalizing a with
  | nil => simpa [chainMatrix, orderedProduct, chain_cons, chain_nil, reached_nil] using hs.2
  | cons t s ih =>
    have hpre := (split_domain (f := chain (t :: s)) (g := a.1) hd).1
    exact lip_comp G hd (ih t hpre hs.1) hs.2

theorem finite_coLip (a : Step X I b) (s : List (Step X I b)) (hd : U ⊆ dom (chain (a :: s)))
    (hs : Along (CoLipOn G) U (a :: s)) : chainMatrix (a :: s) ∈ coLipFamilyOn G (chain (a :: s)) U := by
  induction s generalizing a with
  | nil => simpa [chainMatrix, orderedProduct, chain_cons, chain_nil, reached_nil] using hs.2
  | cons t s ih =>
    have hpre := (split_domain (f := chain (t :: s)) (g := a.1) hd).1
    exact coLip_comp G hd (ih t hpre hs.1) hs.2

end
end LCH02
```

```lean filename=LCH02/Paths.lean
import LCH02.Bounds

namespace LCH02

open scoped Classical
noncomputable section

/-- The intermediate indices, starting with the one nearest the output. -/
def Interior (I : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => I × Interior I n

variable {I : Type}

def factors (first : Mat I) (i : I) :
    (later : List (Mat I)) → (j : I) → Interior I later.length → List ENNReal
  | [], j, _ => [entry first i j]
  | A :: t, j, (k, p) => entry A k j :: factors first i t k p

def PositivePath (first : Mat I) (i : I) (later : List (Mat I)) (j : I)
    (p : Interior I later.length) : Prop := ∀ a ∈ factors first i later j p, 0 < a

theorem factors_length (first : Mat I) (i : I) (later : List (Mat I)) (j : I)
    (p : Interior I later.length) : (factors first i later j p).length = later.length + 1 := by
  induction later generalizing j with
  | nil => rfl
  | cons A t ih =>
    obtain ⟨k, p⟩ := p
    exact congrArg Nat.succ (ih k p)

variable [Fintype I]

theorem product_positive_iff (first : Mat I) (later : List (Mat I)) (i j : I) :
    0 < entry (orderedProduct (later ++ [first])) i j ↔
      ∃ p : Interior I later.length, PositivePath first i later j p := by
  induction later generalizing j with
  | nil => simp [orderedProduct, PositivePath, factors, Interior]
  | cons A t ih =>
    rw [List.cons_append, product_cons, entry_mul, Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
    simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff]
    constructor
    · rintro ⟨k, hk, hpre⟩
      obtain ⟨p, hp⟩ := (ih k).mp hpre
      exact ⟨(k, p), List.forall_mem_cons.mpr ⟨hk, hp⟩⟩
    · rintro ⟨⟨k, p⟩, h⟩
      have hparts := List.forall_mem_cons.mp h
      exact ⟨k, hparts.1, (ih k).mpr ⟨p, hparts.2⟩⟩

theorem product_zero_iff (first : Mat I) (later : List (Mat I)) (i j : I) :
    entry (orderedProduct (later ++ [first])) i j = 0 ↔
      ∀ p : Interior I later.length, 0 ∈ factors first i later j p := by
  have nozero (p : Interior I later.length) :
      PositivePath first i later j p ↔ 0 ∉ factors first i later j p := by
    constructor
    · intro h h0
      exact (lt_irrefl 0) (h 0 h0)
    · intro h a ha
      exact pos_iff_ne_zero.mpr (fun e => h (e ▸ ha))
  simpa only [pos_iff_ne_zero, nozero, not_exists, not_not] using
    (not_congr (product_positive_iff first later i j))

end
end LCH02
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01", "status": "complete",
      "declarations": [
        {"file":"LCH02/Bounds.lean","name":"LCH02.LipOn"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.IsLip"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.lipFamilyOn"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.lipFamily"}
      ],
      "representation": "G.d 是有限非空指标族的分量伪度量。LipOn 要求 U ⊆ dom f，且任意 x,y ∈ U 的输出距离向量逐分量小于等于 M 乘输入距离向量。IsLip 取 U = dom f，两个集合分别收集全部合法矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02", "status": "complete",
      "declarations": [
        {"file":"LCH02/Bounds.lean","name":"LCH02.CoLipOn"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.coLipFamilyOn"}
      ],
      "representation": "CoLipOn 要求 U 非空且包含于 dom f。对每对 x,y ∈ U，每个输出行的矩阵加权和均小于等于该输出距离。coLipFamilyOn 收集所有满足条件的矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03", "status": "complete",
      "declarations": [
        {"file":"LCH02/Bounds.lean","name":"LCH02.Mat"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.entry"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.entry_mul"}
      ],
      "representation": "Mat I 的元素属于 ENNReal。entry M i j = M j i，表示输入 i 到输出 j。对任意 i,j，后步 B 左乘前步 A 的条目等于对中间指标 k 求和。",
      "dependencies": []
    },
    {
      "id": "CH02-D04", "status": "complete",
      "declarations": [
        {"file":"LCH02/Bounds.lean","name":"LCH02.unit_entry"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.orderedProduct"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.product_nil"},
        {"file":"LCH02/Bounds.lean","name":"LCH02.product_cons"}
      ],
      "representation": "单位矩阵对角为 1，其余为 0。列表按末步至首步排列，空列表积为 1，在表头加入 A 将原积左乘 A。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05", "status": "complete",
      "declarations": [
        {"file":"LCH02/Chains.lean","name":"LCH02.Step"},
        {"file":"LCH02/Chains.lean","name":"LCH02.chain"},
        {"file":"LCH02/Chains.lean","name":"LCH02.chainMatrix"},
        {"file":"LCH02/Chains.lean","name":"LCH02.reached"},
        {"file":"LCH02/Chains.lean","name":"LCH02.chain_nil"},
        {"file":"LCH02/Chains.lean","name":"LCH02.chain_cons"},
        {"file":"LCH02/Chains.lean","name":"LCH02.reached_nil"},
        {"file":"LCH02/Chains.lean","name":"LCH02.reached_cons"},
        {"file":"LCH02/Chains.lean","name":"LCH02.Along"},
        {"file":"LCH02/Chains.lean","name":"LCH02.along_iff"},
        {"file":"LCH02/Chains.lean","name":"LCH02.step_domains"}
      ],
      "representation": "每步配对算子和矩阵，两次投影保留相同次序。chain 直接使用冻结的 OperatorChain。reached 从 U 出发逐步取精确像集。along_iff 将逐步前提展开到每个位置 n，其输入域是已执行后缀 drop (n+1) 的像。step_domains 从全复合的定义域条件推出每一步的定义域条件。",
      "dependencies": ["CH02-D03","CH02-D04"]
    },
    {
      "id": "CH02-D06", "status": "complete",
      "declarations": [
        {"file":"LCH02/Paths.lean","name":"LCH02.Interior"},
        {"file":"LCH02/Paths.lean","name":"LCH02.factors"},
        {"file":"LCH02/Paths.lean","name":"LCH02.PositivePath"},
        {"file":"LCH02/Paths.lean","name":"LCH02.factors_length"}
      ],
      "representation": "对 n 步，Interior I (n−1) 依次存储 k_{n−1},…,k₁，i,j 为外部固定的两端。factors 给出对应的 n 个条目，PositivePath 要求其中每一项严格为正。Interior I 0 为 Unit，单步只有唯一空内部路径。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.singleton_lip"}],
      "representation": "在非空 Subsingleton I 上任取唯一指标 i。全域 Lip 合法性等价于所有 x,y ∈ dom f 均满足以 entry A i i 为系数的标量上界。",
      "dependencies": ["CH02-D01","CH02-D03"]
    },
    {
      "id": "CH02-P02", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.lip_restrict"}],
      "representation": "固定 f，对任意 U ⊆ V ⊆ dom f，V 上的整个 Lip 证书族包含于 U 上的证书族。",
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.lip_comp"}],
      "representation": "f 为首步，g 为次步。对 U ⊆ dom (g*f)，A 在 U 上合法、B 在精确像 f.func '' U 上合法，推出 B*A 为复合在 U 上的 Lip 证书。",
      "dependencies": ["CH02-D01","CH02-D03"]
    },
    {
      "id": "CH02-P05", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.coLip_restrict"}],
      "representation": "对非空 U ⊆ V ⊆ dom f，把 V 上任意 co-Lip 证书限制到 U，得到证书族的反向包含。",
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.coLip_zero_entry"}],
      "representation": "对任意域内 x,y 和指标 i,j，若 j 输出距离为零且 i 输入距离为正，则每个全域 co-Lip 证书 A 的 entry A i j 为零。",
      "dependencies": ["CH02-D02","CH02-D03"]
    },
    {
      "id": "CH02-P08", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.coLip_comp"}],
      "representation": "对 U ⊆ dom (g*f)，分别取 U 和 f.func '' U 上的 co-Lip 证书 A,B，推出 B*A 属于复合在 U 上的证书族。非空性随成员资格给出。",
      "dependencies": ["CH02-D02","CH02-D03"]
    },
    {
      "id": "CH02-P11", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.unit_lip"}],
      "representation": "对任意非空 U ⊆ dom 1，矩阵空乘积属于恒等算子在 U 上的 Lip 证书族。product_nil 将该矩阵识别为单位矩阵。",
      "dependencies": ["CH02-D01","CH02-D04"]
    },
    {
      "id": "CH02-P12", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.unit_coLip"}],
      "representation": "对任意非空 U ⊆ dom 1，同一空乘积属于恒等算子在 U 上的 co-Lip 证书族。",
      "dependencies": ["CH02-D02","CH02-D04"]
    },
    {
      "id": "CH02-P14", "status": "complete",
      "declarations": [{"file":"LCH02/Paths.lean","name":"LCH02.product_positive_iff"}],
      "representation": "first 是首步，later 是按复合次序书写的全部后续步。对任意 i,j，乘积条目严格为正当且仅当存在全正内部路径。later = [] 时只检查 first 的对应条目。",
      "dependencies": ["CH02-D03","CH02-D04","CH02-D06"]
    },
    {
      "id": "CH02-P03", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.lip_from_dom"}],
      "representation": "取 V = dom f。对任意 U ⊆ dom f，全域 Lip 证书族包含于 U 上的 Lip 证书族。",
      "dependencies": ["CH02-D01","CH02-P02"]
    },
    {
      "id": "CH02-P06", "status": "complete",
      "declarations": [{"file":"LCH02/Bounds.lean","name":"LCH02.coLip_from_dom"}],
      "representation": "取 V = dom f。对任意非空 U ⊆ dom f，定义域上的全部 co-Lip 证书均可限制到 U。",
      "dependencies": ["CH02-D02","CH02-P05"]
    },
    {
      "id": "CH02-P09", "status": "complete",
      "declarations": [{"file":"LCH02/Chains.lean","name":"LCH02.finite_lip"}],
      "representation": "a :: s 遍历全部正长度链。给定 U 包含于复合定义域，并对每一步在其实际输入域给出 Lip 证书，推出同序矩阵连乘为全复合在 U 上的 Lip 证书。",
      "dependencies": ["CH02-D01","CH02-D04","CH02-D05","CH02-P04"]
    },
    {
      "id": "CH02-P10", "status": "complete",
      "declarations": [{"file":"LCH02/Chains.lean","name":"LCH02.finite_coLip"}],
      "representation": "对任意正长度链 a :: s 和复合定义域内的 U，从实际输入域上的逐步 co-Lip 证书推出矩阵连乘属于复合的 co-Lip 证书族，结论包含 U 非空。",
      "dependencies": ["CH02-D02","CH02-D04","CH02-D05","CH02-P08"]
    },
    {
      "id": "CH02-P13", "status": "complete",
      "declarations": [{"file":"LCH02/Paths.lean","name":"LCH02.product_zero_iff"}],
      "representation": "对任意首步、后续步和两端 i,j，乘积条目为零当且仅当每条内部路径的因子列表含 0，即至少一层条目为零。单步时该列表只有 first j i。",
      "dependencies": ["CH02-D03","CH02-D04","CH02-D06","CH02-P14"]
    }
  ]
}
```