20 项义务均已形式化并通过 Lean 4.29.1 编译。对链复合、路径判据及边界情形的公理依赖检查只检出 `propext`、`Classical.choice` 和 `Quot.sound`。

源码改编自 Zhe Li（Glen Li / glenzli）的 [The Operator Evolution Theory](https://glenzli.com/books/oet/)，遵循 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。

```lean filename=Main.lean
import LCH02
```

```lean filename=LCH02.lean
/-
Formalization of selected material from The Operator Evolution Theory by Zhe Li
(Glen Li / glenzli), https://glenzli.com/books/oet/, CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/). Adapted to Lean.
-/
import formal_oet.vol_01.ch_01_foundations.operator_space

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

namespace LCH02

noncomputable section
set_option linter.unusedSectionVars false
variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]

-- The first matrix index is the output, the second the input.
abbrev Mat (I : Type) := I → I → ENNReal

def matMul (A B : Mat I) : Mat I := fun j i => ∑ k, A j k * B k i
def matOne : Mat I := fun j i => if j = i then 1 else 0

def lip (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j, d j (f.func x) (f.func y) ≤ ∑ i, L j i * d i x y

def coLip (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j, ∑ i, K j i * d i x y ≤ d j (f.func x) (f.func y)

def lipFamily (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Mat I) :=
  {L | lip d f U L}

def coLipFamily (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Mat I) :=
  {K | coLip d f U K}

def globalLip (d : I → X → X → ENNReal) (f : Operator X bot) : Set (Mat I) :=
  lipFamily d f (dom f)

theorem lip_mono {d : I → X → X → ENNReal} {f : Operator X bot} {U V : Set X}
    {L : Mat I} (hUV : U ⊆ V) (h : lip d f V L) : lip d f U L :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict {d : I → X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {L : Mat I} (hU : U ⊆ dom f) (h : L ∈ globalLip d f) :
    L ∈ lipFamily d f U := lip_mono hU h

theorem colip_mono {d : I → X → X → ENNReal} {f : Operator X bot} {U V : Set X}
    {K : Mat I} (hU : U.Nonempty) (hUV : U ⊆ V) (h : coLip d f V K) : coLip d f U K :=
  ⟨hU, hUV.trans h.2.1, fun x hx y hy j => h.2.2 x (hUV hx) y (hUV hy) j⟩

theorem global_colip_restrict {d : I → X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {K : Mat I} (hU : U.Nonempty) (hsub : U ⊆ dom f)
    (h : K ∈ coLipFamily d f (dom f)) : K ∈ coLipFamily d f U := colip_mono hU hsub h

theorem singleton_lip {d : Unit → X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {L : Mat Unit} (h : lip d f U L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d () (f.func x) (f.func y) ≤ L () () * d () x y := by
  simpa using h.2 x hx y hy ()

theorem colip_entry_zero {d : I → X → X → ENNReal} {f : Operator X bot}
    {K : Mat I} {x y : X} {i j : I} (h : coLip d f (dom f) K)
    (hx : x ∈ dom f) (hy : y ∈ dom f) (hz : d j (f.func x) (f.func y) = 0)
    (hp : 0 < d i x y) : K j i = 0 := by
  have hs := h.2.2 x hx y hy j
  rw [hz] at hs
  have ht : K j i * d i x y = 0 := le_antisymm ((Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans hs) (zero_le _)
  exact (mul_eq_zero.mp ht).resolve_right (ne_of_gt hp)

theorem one_sum (v : I → ENNReal) (j : I) : (∑ i, matOne j i * v i) = v j := by
  classical
  simp [matOne]

theorem identity_lip (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    lip d (operator_identity : Operator X bot) U matOne := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i, matOne j i * d i x y
  rw [one_sum]

theorem identity_colip (d : I → X → X → ENNReal) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (operator_identity : Operator X bot)) :
    coLip d (operator_identity : Operator X bot) U matOne := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, matOne j i * d i x y) ≤ d j x y
  rw [one_sum]

theorem matrix_sum (A B : Mat I) (v : I → ENNReal) (j : I) :
    (∑ i, matMul A B j i * v i) = ∑ k, A j k * (∑ i, B k i * v i) := by
  simp only [matMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem compose_domains {f g : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (g * f)) : U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx hf
    have h := hU hx
    apply h
    change g.func (f.func x) = bot
    rw [hf, g.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_compose {d : I → X → X → ENNReal} {f g : Operator X bot}
    {U : Set X} {A B : Mat I} (hU : U ⊆ dom (g * f))
    (hf : lip d f U B) (hg : lip d g (f.func '' U) A) :
    lip d (g * f) U (matMul A B) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (g.func (f.func x)) (g.func (f.func y)) ≤ _
  rw [matrix_sum]
  apply le_trans (hg.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_left' (hf.2 x hx y hy k) _

theorem colip_compose {d : I → X → X → ENNReal} {f g : Operator X bot}
    {U : Set X} {A B : Mat I} (hU : U ⊆ dom (g * f))
    (hf : coLip d f U B) (hg : coLip d g (f.func '' U) A) :
    coLip d (g * f) U (matMul A B) := by
  refine ⟨hf.1, hU, ?_⟩
  intro x hx y hy j
  change (∑ i, matMul A B j i * d i x y) ≤ d j (g.func (f.func x)) (g.func (f.func y))
  rw [matrix_sum]
  apply le_trans _ (hg.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_left' (hf.2.2 x hx y hy k) _

-- Lists are chronological: the head acts first.
def chain : List (Operator X bot × Mat I) → Operator X bot
  | [] => 1
  | (f, _) :: tail => chain tail * f

def matProduct : List (Mat I) → Mat I
  | [] => matOne
  | M :: tail => matMul (matProduct tail) M

theorem matProduct_singleton (M : Mat I) (i j : I) : matProduct [M] j i = M j i := by
  simp [matProduct, matMul, matOne]

def matrixProduct (s : List (Operator X bot × Mat I)) : Mat I :=
  matProduct (s.map Prod.snd)

def inputDomain (U : Set X) : List (Operator X bot × Mat I) → ℕ → Set X
  | _, 0 => U
  | [], _ + 1 => U
  | (f, _) :: tail, n + 1 => inputDomain (f.func '' U) tail n

theorem chain_eq_operatorChain (s : List (Operator X bot × Mat I)) :
    chain s = OperatorChain (s.map Prod.fst).reverse := by
  rw [operator_chain_eq_prod]
  induction s with
  | nil => rfl
  | cons a tail ih =>
    rcases a with ⟨f, M⟩
    simp only [chain, List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one] at *
    rw [ih]

def lipSteps (d : I → X → X → ENNReal) (U : Set X) :
    List (Operator X bot × Mat I) → Prop
  | [] => True
  | (f, M) :: tail => lip d f U M ∧ lipSteps d (f.func '' U) tail

def colipSteps (d : I → X → X → ENNReal) (U : Set X) :
    List (Operator X bot × Mat I) → Prop
  | [] => True
  | (f, M) :: tail => coLip d f U M ∧ colipSteps d (f.func '' U) tail

theorem chain_lip (d : I → X → X → ENNReal) (s : List (Operator X bot × Mat I))
    (U : Set X) (hU : U ⊆ dom (chain s)) (hs : lipSteps d U s) :
    lip d (chain s) U (matrixProduct s) := by
  induction s generalizing U with
  | nil => exact identity_lip d U hU
  | cons a tail ih =>
    rcases a with ⟨f, M⟩
    have ht : f.func '' U ⊆ dom (chain tail) := (compose_domains hU).2
    exact lip_compose hU hs.1 (ih _ ht hs.2)

theorem chain_colip (d : I → X → X → ENNReal) (s : List (Operator X bot × Mat I))
    (U : Set X) (hne : U.Nonempty) (hU : U ⊆ dom (chain s)) (hs : colipSteps d U s) :
    coLip d (chain s) U (matrixProduct s) := by
  induction s generalizing U with
  | nil => exact identity_colip d U hne hU
  | cons a tail ih =>
    rcases a with ⟨f, M⟩
    have ht : f.func '' U ⊆ dom (chain tail) := (compose_domains hU).2
    have hn : (f.func '' U).Nonempty := hne.image f.func
    exact colip_compose hU hs.1 (ih _ hn ht hs.2)

inductive Path : List (Mat I) → I → I → Type
  | nil (i : I) : Path [] i i
  | cons {M : Mat I} {ms : List (Mat I)} {i j : I} (k : I)
      (tail : Path ms k j) : Path (M :: ms) i j

def Path.allPositive : {ms : List (Mat I)} → {i j : I} → Path ms i j → Prop
  | _, _, _, .nil _ => True
  | M :: _, i, _, .cons k tail => 0 < M k i ∧ tail.allPositive

def Path.hasZero : {ms : List (Mat I)} → {i j : I} → Path ms i j → Prop
  | _, _, _, .nil _ => False
  | M :: _, i, _, .cons k tail => M k i = 0 ∨ tail.hasZero

theorem Path.positive_iff_not_zero {ms : List (Mat I)} {i j : I} (p : Path ms i j) :
    p.allPositive ↔ ¬ p.hasZero := by
  induction p with
  | nil => simp [Path.allPositive, Path.hasZero]
  | cons k tail ih =>
    simp only [Path.allPositive, Path.hasZero, not_or, ← ih, pos_iff_ne_zero]

theorem enn_mul_positive (a b : ENNReal) : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    have hn : a * b ≠ 0 := pos_iff_ne_zero.mp h
    exact ⟨pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).1,
      pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2⟩
  · rintro ⟨ha, hb⟩
    exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb))

theorem matProduct_pos_iff (ms : List (Mat I)) (i j : I) :
    0 < matProduct ms j i ↔ ∃ p : Path ms i j, p.allPositive := by
  induction ms generalizing i j with
  | nil =>
    by_cases h : j = i
    · subst j
      constructor
      · intro _; exact ⟨Path.nil i, trivial⟩
      · intro _; simp [matProduct, matOne]
    · constructor
      · intro hp; simp [matProduct, matOne, h] at hp
      · rintro ⟨p, hp⟩
        cases p
        exact (h rfl).elim
  | cons M ms ih =>
    simp only [matProduct, matMul, Finset.sum_pos_iff, Finset.mem_univ, true_and]
    simp only [enn_mul_positive, ih]
    constructor
    · rintro ⟨k, ⟨⟨p, hp⟩, hm⟩⟩
      exact ⟨Path.cons k p, hm, hp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | cons k tail => exact ⟨k, ⟨⟨tail, hp.2⟩, hp.1⟩⟩

theorem matProduct_zero_iff (ms : List (Mat I)) (i j : I) :
    matProduct ms j i = 0 ↔ ∀ p : Path ms i j, p.hasZero := by
  rw [← nonpos_iff_eq_zero, ← not_lt, matProduct_pos_iff]
  simp only [not_exists, Path.positive_iff_not_zero, not_not]

theorem singleton_paths (M : Mat I) (i j : I) :
    ((∃ p : Path [M] i j, p.allPositive) ↔ 0 < M j i) ∧
    ((∀ p : Path [M] i j, p.hasZero) ↔ M j i = 0) := by
  constructor
  · rw [← matProduct_pos_iff, matProduct_singleton]
  · rw [← matProduct_zero_iff, matProduct_singleton]

end
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
        {"file": "LCH02.lean", "name": "LCH02.lip"},
        {"file": "LCH02.lean", "name": "LCH02.lipFamily"},
        {"file": "LCH02.lean", "name": "LCH02.globalLip"}
      ],
      "representation": {
        "对象": "lip d f U L 表示 L 是 f 在 U 上的受限 Lip 矩阵；lipFamily 是对应集合，globalLip 使用 U = dom f。",
        "参数": "d 是分量距离族，f 是冻结模块中的保吸收元算子，L 的条目取值 ENNReal。",
        "量词": "定义包含 U ⊆ dom f，并对所有 x,y ∈ U 和输出指标 j 量化。",
        "结论": "输出距离不超过对所有输入指标的系数乘输入距离之和。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.coLip"},
        {"file": "LCH02.lean", "name": "LCH02.coLipFamily"}
      ],
      "representation": {
        "对象": "coLip d f U K 表示受限 co-Lip 矩阵；coLipFamily 是相应集合。",
        "参数": "U 是算子的实际受限输入域，K 以 ENNReal 为条目。",
        "量词": "定义包含 U.Nonempty 和 U ⊆ dom f，并对所有 x,y ∈ U 及输出指标 j 量化。",
        "结论": "各输入距离的加权和不超过输出距离。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.Mat"},
        {"file": "LCH02.lean", "name": "LCH02.matMul"},
        {"file": "LCH02.lean", "name": "LCH02.matrix_sum"}
      ],
      "representation": {
        "对象": "Mat I 是 I → I → ENNReal；M j i 对应原文 M_{i→j}。",
        "参数": "第一指标 j 为输出行，第二指标 i 为输入列。",
        "量词": "矩阵乘法对有限指标类型 I 的全部中间指标求和。",
        "结论": "matMul A B j i = ∑ k, A j k * B k i，故后作用的矩阵位于左侧。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.matOne"},
        {"file": "LCH02.lean", "name": "LCH02.matProduct"},
        {"file": "LCH02.lean", "name": "LCH02.matrixProduct"},
        {"file": "LCH02.lean", "name": "LCH02.matProduct_singleton"}
      ],
      "representation": {
        "对象": "matOne 是对角单位矩阵；matProduct 接受按作用时间排列的矩阵列表。",
        "参数": "列表头是第一步，matrixProduct 从算子与矩阵的配对列表提取矩阵。",
        "量词": "定义覆盖空列表和任意有限非空列表。",
        "结论": "空积为 matOne；M₁,...,Mₙ 的积递归地为 Mₙ⋯M₁；单项积等于该项。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.chain"},
        {"file": "LCH02.lean", "name": "LCH02.inputDomain"},
        {"file": "LCH02.lean", "name": "LCH02.chain_eq_operatorChain"},
        {"file": "LCH02.lean", "name": "LCH02.compose_domains"},
        {"file": "LCH02.lean", "name": "LCH02.lipSteps"},
        {"file": "LCH02.lean", "name": "LCH02.colipSteps"}
      ],
      "representation": {
        "对象": "链是按作用时间排列的算子与矩阵配对列表；inputDomain 从 U 开始逐步取实际像。",
        "参数": "第一个列表元素最先作用；逐步证书递归地在 f.func '' U 上继续。",
        "量词": "定义适用于任意有限列表，inputDomain 在有效步数内给出各中间输入域。",
        "结论": "chain 等于冻结模块 OperatorChain 对算子列表反转后的复合；compose_domains 给出两步复合的域包含。"
      },
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D04"]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.Path"},
        {"file": "LCH02.lean", "name": "LCH02.Path.allPositive"},
        {"file": "LCH02.lean", "name": "LCH02.Path.hasZero"},
        {"file": "LCH02.lean", "name": "LCH02.Path.positive_iff_not_zero"}
      ],
      "representation": {
        "对象": "Path ms i j 是与矩阵列表 ms 长度匹配、从输入 i 到输出 j 的有限指标路径。",
        "参数": "cons 的 k 是第一步的输出及余下路径的输入；nil 只连接同一指标。",
        "量词": "路径类型覆盖所有中间指标选择；allPositive 和 hasZero 沿全部层级递归。",
        "结论": "allPositive 表示每个单步条目正，hasZero 表示至少一个单步条目为零。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.singleton_lip"}
      ],
      "representation": {
        "对象": "以 Unit 表示任意单元素指标集，其唯一元素为 ()。",
        "参数": "f、U、L 和 x,y 分别对应算子、受限域、矩阵和域中点。",
        "量词": "对任意域内 x,y；全域情形取 U = dom f。",
        "结论": "唯一输出距离不超过唯一矩阵条目乘唯一输入距离。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.lip_mono"}
      ],
      "representation": {
        "对象": "lip 谓词的逐矩阵蕴含等价于证书族的集合包含。",
        "参数": "U ⊆ V，且 V 的合法性包含 V ⊆ dom f。",
        "量词": "对任意矩阵 L。",
        "结论": "V 上的 Lip 证书也是 U 上的证书。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.compose_domains"},
        {"file": "LCH02.lean", "name": "LCH02.lip_compose"}
      ],
      "representation": {
        "对象": "f、g 对应先后两步，U 对应 U₁，f.func '' U 是精确的 U₂。",
        "参数": "B 是 f 在 U 上的矩阵，A 是 g 在实际像域上的矩阵。",
        "量词": "对任意 U ⊆ dom (g * f) 和任意满足逐步条件的 A、B。",
        "结论": "matMul A B 是 g * f 在 U 上的 Lip 矩阵。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.colip_mono"}
      ],
      "representation": {
        "对象": "coLip 谓词的逐矩阵蕴含等价于证书族的集合包含。",
        "参数": "U 非空且 U ⊆ V；V 的合法性包含 V ⊆ dom f。",
        "量词": "对任意矩阵 K。",
        "结论": "V 上的 co-Lip 证书也是 U 上的证书。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.colip_entry_zero"}
      ],
      "representation": {
        "对象": "K 是定义域上的 co-Lip 矩阵；K j i 对应 K_{i→j}。",
        "参数": "x,y ∈ dom f，输出 j 的距离为零，输入 i 的距离严格为正。",
        "量词": "对任意满足条件的点对、指标和矩阵。",
        "结论": "K j i = 0，允许其他条目及距离取无穷大。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.compose_domains"},
        {"file": "LCH02.lean", "name": "LCH02.colip_compose"}
      ],
      "representation": {
        "对象": "f、g 对应先后两步，U 对应 U₁，f.func '' U 是精确的 U₂。",
        "参数": "B 和 A 分别为两步在其实际输入域上的 co-Lip 矩阵。",
        "量词": "对任意复合定义域子集及满足逐步条件的矩阵；coLip 前提包含非空性。",
        "结论": "matMul A B 是 g * f 在 U 上的 co-Lip 矩阵，结论保留 U 非空。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.identity_lip"},
        {"file": "LCH02.lean", "name": "LCH02.one_sum"}
      ],
      "representation": {
        "对象": "operator_identity 是零步算子，matOne 是空矩阵乘积。",
        "参数": "U ⊆ dom operator_identity；定理还允许 U 为空。",
        "量词": "对任意有限指标族和任意距离函数。",
        "结论": "单位矩阵是恒等算子在 U 上的 Lip 证书。"
      },
      "dependencies": ["CH02-D01", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.identity_colip"},
        {"file": "LCH02.lean", "name": "LCH02.one_sum"}
      ],
      "representation": {
        "对象": "operator_identity 是零步算子，matOne 是空矩阵乘积。",
        "参数": "U 非空且 U ⊆ dom operator_identity。",
        "量词": "对任意有限指标族和任意距离函数。",
        "结论": "单位矩阵是恒等算子在 U 上的 co-Lip 证书。"
      },
      "dependencies": ["CH02-D02", "CH02-D04"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.matProduct_pos_iff"},
        {"file": "LCH02.lean", "name": "LCH02.matProduct_singleton"}
      ],
      "representation": {
        "对象": "ms 是按时间排列的矩阵列表，Path ms i j 是从 i 到 j 的指标路径。",
        "参数": "所有条目取 ENNReal；allPositive 要求路径上的每个因子严格为正。",
        "量词": "定理对任意有限列表成立，因而覆盖所有正长度及 n = 1。",
        "结论": "乘积的 j 行 i 列正，当且仅当存在全正路径；单项乘积等于原条目。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.global_lip_restrict"}
      ],
      "representation": {
        "对象": "globalLip 是在整个 dom f 上的证书族。",
        "参数": "U ⊆ dom f。",
        "量词": "对任意全域 Lip 矩阵。",
        "结论": "该矩阵属于 U 上的受限 Lip 证书族。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.global_colip_restrict"}
      ],
      "representation": {
        "对象": "coLipFamily d f (dom f) 是全域 co-Lip 证书族。",
        "参数": "U 非空且 U ⊆ dom f。",
        "量词": "对任意全域 co-Lip 矩阵。",
        "结论": "该矩阵属于 U 上的受限 co-Lip 证书族。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.chain_lip"},
        {"file": "LCH02.lean", "name": "LCH02.lipSteps"}
      ],
      "representation": {
        "对象": "s 按时间列出每步算子及其矩阵；lipSteps 递归要求每步在实际输入像域上成立。",
        "参数": "U ⊆ dom (chain s)，矩阵乘积按后作用者在左的次序。",
        "量词": "对任意有限列表成立，包括要求中的任意正长度链。",
        "结论": "直接从逐步证书推出 matrixProduct s 是整个 chain s 在 U 上的 Lip 证书。"
      },
      "dependencies": ["CH02-D01", "CH02-D04", "CH02-D05", "CH02-P04", "CH02-P11"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.chain_colip"},
        {"file": "LCH02.lean", "name": "LCH02.colipSteps"}
      ],
      "representation": {
        "对象": "s 按时间列出每步算子及其矩阵；colipSteps 递归使用每步实际输入像域。",
        "参数": "U 非空且 U ⊆ dom (chain s)；递归证明中像域非空由 U 非空推出。",
        "量词": "对任意有限列表成立，包括要求中的任意正长度链。",
        "结论": "直接从逐步证书推出 matrixProduct s 是整个 chain s 在 U 上的 co-Lip 证书。"
      },
      "dependencies": ["CH02-D02", "CH02-D04", "CH02-D05", "CH02-P08", "CH02-P12"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "LCH02.lean", "name": "LCH02.matProduct_zero_iff"},
        {"file": "LCH02.lean", "name": "LCH02.singleton_paths"}
      ],
      "representation": {
        "对象": "Path ms i j 枚举从 i 到 j 的全部有限指标路径，hasZero 表示路径有零因子。",
        "参数": "ms 的矩阵条目取 ENNReal；单项列表对应 n = 1。",
        "量词": "定理对任意有限列表及任意端点成立，特别覆盖所有非空列表。",
        "结论": "乘积的 j 行 i 列为零，当且仅当每条路径含零因子；singleton_paths 显示单步退化。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```