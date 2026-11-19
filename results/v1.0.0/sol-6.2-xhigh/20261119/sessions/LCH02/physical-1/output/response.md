20 项义务均已完成。`Main.lean` 及其导入的目标模块已在 Lean 4.29.1 和指定的 mathlib 提交上通过检查。清单中的声明依赖已与 Lean 实际引用核对，公理依赖仅涉及 `propext`、`Classical.choice` 和 `Quot.sound`。

算子与矩阵列表按应用顺序排列，复合时末步在左。中间域取实际前缀像集，路径用有限中间指标序列表示。逐项对应见 `alignment.json`。

数学内容源自 Zhe Li（Glen Li / glenzli，ORCID 0009-0006-6536-3453）的 *The Operator Evolution Theory* 第一卷第 2 章。以下是该选段的 Lean 形式化改编。[作品主页](https://glenzli.com/books/oet/) · [原作源码](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

```lean filename=Main.lean
import LCH02.Matrix
import LCH02.Bounds
import LCH02.Chains
```

```lean filename=LCH02/Matrix.lean
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic

namespace LCH02

open scoped BigOperators Classical

abbrev Coefficients (I : Type) := Matrix I I ENNReal

/-- The input index is the column and the output index is the row. -/
def entry {I : Type} (A : Coefficients I) (i j : I) : ENNReal :=
  A j i

theorem entry_mul {I : Type} [Fintype I] (B A : Coefficients I) (i j : I) :
    entry (B * A) i j = ∑ k : I, entry B k j * entry A i k :=
  Matrix.mul_apply

noncomputable def matrixUnit {I : Type} : Coefficients I := 1

theorem entry_unit {I : Type} (i j : I) :
    entry matrixUnit i j = if i = j then 1 else 0 := by
  simp [entry, matrixUnit, Matrix.one_apply, eq_comm]

/-- The list runs from the first applied matrix to the last. -/
noncomputable def matrixProduct {I : Type} [Fintype I]
    (matrices : List (Coefficients I)) : Coefficients I :=
  matrices.reverse.prod

@[simp] theorem matrixProduct_nil {I : Type} [Fintype I] :
    matrixProduct ([] : List (Coefficients I)) = matrixUnit := rfl

theorem matrixProduct_cons {I : Type} [Fintype I]
    (A : Coefficients I) (rest : List (Coefficients I)) :
    matrixProduct (A :: rest) = matrixProduct rest * A := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

@[simp] theorem matrixProduct_single {I : Type} [Fintype I] (A : Coefficients I) :
    matrixProduct [A] = A := by
  simp [matrixProduct]

/-- A path with `n` intermediate layers chooses one index at each layer. -/
abbrev IndexPath (I : Type) (n : ℕ) := Fin n → I

/-- The endpoints `i` and `j` are external to the intermediate sequence. -/
def pathFactors {I : Type} (A : Coefficients I) :
    (rest : List (Coefficients I)) → I → I → IndexPath I rest.length → List ENNReal
  | [], i, j, _ => [entry A i j]
  | B :: rest, i, j, p =>
      entry A i (p 0) :: pathFactors B rest (p 0) j (Fin.tail p)

theorem pathFactors_length {I : Type} (A : Coefficients I)
    (rest : List (Coefficients I)) (i j : I) (p : IndexPath I rest.length) :
    (pathFactors A rest i j p).length = rest.length + 1 := by
  induction rest generalizing A i with
  | nil => rfl
  | cons B rest ih => simp [pathFactors, ih]

def PositivePath {I : Type} (A : Coefficients I) (rest : List (Coefficients I))
    (i j : I) (p : IndexPath I rest.length) : Prop :=
  ∀ a ∈ pathFactors A rest i j p, 0 < a

def HasZeroFactor {I : Type} (A : Coefficients I) (rest : List (Coefficients I))
    (i j : I) (p : IndexPath I rest.length) : Prop :=
  0 ∈ pathFactors A rest i j p

abbrev singleStepPath_unique {I : Type} : Unique (IndexPath I 0) :=
  ⟨⟨Fin.elim0⟩, fun _ => funext (fun k => Fin.elim0 k)⟩

theorem matrixProduct_pos_iff {I : Type} [Fintype I]
    (A : Coefficients I) (rest : List (Coefficients I)) (i j : I) :
    0 < entry (matrixProduct (A :: rest)) i j ↔
      ∃ p : IndexPath I rest.length, PositivePath A rest i j p := by
  induction rest generalizing A i with
  | nil =>
      simp only [matrixProduct_single, PositivePath, pathFactors, List.mem_singleton]
      constructor
      · intro h
        exact ⟨singleStepPath_unique.default, fun a ha => ha ▸ h⟩
      · rintro ⟨_, h⟩
        exact h _ rfl
  | cons B rest ih =>
      rw [matrixProduct_cons, entry_mul, Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
      simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff, ih B]
      constructor
      · rintro ⟨k, ⟨p, hp⟩, hfirst⟩
        refine ⟨Fin.cons k p, ?_⟩
        simpa [PositivePath, pathFactors, List.forall_mem_cons] using And.intro hfirst hp
      · rintro ⟨p, hp⟩
        have h : 0 < entry A i (p 0) ∧
            PositivePath B rest (p 0) j (Fin.tail p) := by
          simpa [PositivePath, pathFactors, List.forall_mem_cons] using hp
        exact ⟨p 0, ⟨Fin.tail p, h.2⟩, h.1⟩

theorem matrixProduct_zero_iff {I : Type} [Fintype I]
    (A : Coefficients I) (rest : List (Coefficients I)) (i j : I) :
    entry (matrixProduct (A :: rest)) i j = 0 ↔
      ∀ p : IndexPath I rest.length, HasZeroFactor A rest i j p := by
  have hfactor (p : IndexPath I rest.length) :
      ¬ PositivePath A rest i j p ↔ HasZeroFactor A rest i j p := by
    simp [PositivePath, HasZeroFactor, pos_iff_ne_zero]
  rw [← not_ne_iff, ← pos_iff_ne_zero, matrixProduct_pos_iff, not_exists]
  exact forall_congr' hfactor

end LCH02
```

```lean filename=LCH02/Bounds.lean
import LCH02.Matrix
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

structure Gauge (X I : Type) (bot : X) where
  index_nonempty : Nonempty I
  dist : I → X → X → ENNReal
  component : ∀ i : I, ExtendedPseudoMetric X bot (dist i)

variable {X I : Type} {bot : X} [Fintype I]

noncomputable def matrixBound (A : Coefficients I) (v : I → ENNReal) (j : I) : ENNReal :=
  Matrix.mulVec A v j

theorem matrixBound_apply (A : Coefficients I) (v : I → ENNReal) (j : I) :
    matrixBound A v j = ∑ i : I, entry A i j * v i := rfl

def LipOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (A : Coefficients I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      g.dist j (φ.func x) (φ.func y) ≤ matrixBound A (fun i => g.dist i x y) j

def Lip (g : Gauge X I bot) (φ : Operator X bot) (A : Coefficients I) : Prop :=
  LipOn g φ (dom φ) A

def lipMatricesOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (Coefficients I) :=
  {A | LipOn g φ U A}

def lipMatrices (g : Gauge X I bot) (φ : Operator X bot) : Set (Coefficients I) :=
  {A | Lip g φ A}

def CoLipOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (A : Coefficients I) : Prop :=
  U ⊆ dom φ ∧ U.Nonempty ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      matrixBound A (fun i => g.dist i x y) j ≤ g.dist j (φ.func x) (φ.func y)

def coLipMatricesOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (Coefficients I) :=
  {A | CoLipOn g φ U A}

variable {g : Gauge X I bot} {φ ψ : Operator X bot} {U V : Set X}

theorem lip_scalar_iff [Subsingleton I] (i : I) (A : Coefficients I) :
    Lip g φ A ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      g.dist i (φ.func x) (φ.func y) ≤ entry A i i * g.dist i x y := by
  have hsum (v : I → ENNReal) : matrixBound A v i = entry A i i * v i := by
    rw [matrixBound_apply]
    exact Fintype.sum_eq_single i (fun k hk => (hk (Subsingleton.elim k i)).elim)
  constructor
  · intro h x hx y hy
    simpa only [hsum] using h.2 x hx y hy i
  · intro h
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x hx y hy j
    rw [Subsingleton.elim j i, hsum]
    exact h x hx y hy

theorem lipMatricesOn_antitone (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipMatricesOn g φ V ⊆ lipMatricesOn g φ U := by
  intro A h
  exact ⟨hUV.trans hV, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem lipMatrices_restrict (hU : U ⊆ dom φ) :
    lipMatrices g φ ⊆ lipMatricesOn g φ U :=
  lipMatricesOn_antitone hU Set.Subset.rfl

theorem coLipMatricesOn_antitone (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    coLipMatricesOn g φ V ⊆ coLipMatricesOn g φ U := by
  intro A h
  exact ⟨hUV.trans hV, hne, fun x hx y hy j => h.2.2 x (hUV hx) y (hUV hy) j⟩

theorem coLipMatrices_restrict (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipMatricesOn g φ (dom φ) ⊆ coLipMatricesOn g φ U :=
  coLipMatricesOn_antitone hne hU Set.Subset.rfl

theorem coLip_entry_zero {A : Coefficients I} (h : CoLipOn g φ (dom φ) A)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : g.dist j (φ.func x) (φ.func y) = 0) (hin : 0 < g.dist i x y) :
    entry A i j = 0 := by
  have hlower := h.2.2 x hx y hy j
  rw [hout, matrixBound_apply] at hlower
  have hterm : entry A i j * g.dist i x y ≤
      ∑ k : I, entry A k j * g.dist k x y :=
    Finset.single_le_sum (f := fun k => entry A k j * g.dist k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have heq := le_antisymm (hterm.trans hlower) (zero_le _)
  exact (mul_eq_zero.mp heq).resolve_right hin.ne'

theorem mem_dom_mul {x : X} :
    x ∈ dom (ψ * φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  intro hx
  apply h
  rw [hx, ψ.preserves_bot]

theorem image_subset_dom_of_mul (hU : U ⊆ dom (ψ * φ)) :
    operator_image φ U ⊆ dom ψ := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_dom_mul.mp (hU hx)).2

theorem image_mul (φ ψ : Operator X bot) (U : Set X) :
    operator_image (ψ * φ) U = operator_image ψ (operator_image φ U) :=
  (Set.image_image ψ.func φ.func U).symm

private theorem matrixBound_mono (A : Coefficients I) {v w : I → ENNReal}
    (h : ∀ i, v i ≤ w i) (j : I) : matrixBound A v j ≤ matrixBound A w j := by
  rw [matrixBound_apply, matrixBound_apply]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_right (h i) _)

private theorem matrixBound_mul (A B : Coefficients I) (v : I → ENNReal) (j : I) :
    matrixBound (B * A) v j = matrixBound B (matrixBound A v) j :=
  (congrFun (Matrix.mulVec_mulVec v B A) j).symm

theorem lip_comp {A B : Coefficients I} (hU : U ⊆ dom (ψ * φ))
    (hA : LipOn g φ U A) (hB : LipOn g ψ (operator_image φ U) B) :
    LipOn g (ψ * φ) U (B * A) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  have hx' : φ.func x ∈ operator_image φ U := ⟨x, hx, rfl⟩
  have hy' : φ.func y ∈ operator_image φ U := ⟨y, hy, rfl⟩
  rw [matrixBound_mul]
  exact (hB.2 _ hx' _ hy' j).trans (matrixBound_mono B (hA.2 x hx y hy) j)

theorem coLip_comp {A B : Coefficients I} (hU : U ⊆ dom (ψ * φ))
    (hA : CoLipOn g φ U A) (hB : CoLipOn g ψ (operator_image φ U) B) :
    CoLipOn g (ψ * φ) U (B * A) := by
  refine ⟨hU, hA.2.1, ?_⟩
  intro x hx y hy j
  have hx' : φ.func x ∈ operator_image φ U := ⟨x, hx, rfl⟩
  have hy' : φ.func y ∈ operator_image φ U := ⟨y, hy, rfl⟩
  rw [matrixBound_mul]
  exact (matrixBound_mono B (hA.2.2 x hx y hy) j).trans (hB.2.2 _ hx' _ hy' j)

private theorem matrixBound_unit (v : I → ENNReal) (j : I) :
    matrixBound matrixUnit v j = v j :=
  congrFun (Matrix.one_mulVec v) j

theorem unit_lip (hU : U ⊆ dom (1 : Operator X bot)) (_hne : U.Nonempty) :
    LipOn g 1 U matrixUnit := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  rw [matrixBound_unit]
  exact le_rfl

theorem unit_coLip (hU : U ⊆ dom (1 : Operator X bot)) (hne : U.Nonempty) :
    CoLipOn g 1 U matrixUnit := by
  refine ⟨hU, hne, ?_⟩
  intro x _ y _ j
  rw [matrixBound_unit]
  exact le_rfl

end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.Bounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- The list of operators is in application order. -/
def chain (steps : List (Operator X bot)) : Operator X bot :=
  OperatorChain steps.reverse

@[simp] theorem chain_nil : chain ([] : List (Operator X bot)) = 1 := rfl

@[simp] theorem chain_single (φ : Operator X bot) : chain [φ] = φ := by
  simp [chain, operator_chain_eq_prod]

theorem chain_append (steps rest : List (Operator X bot)) :
    chain (steps ++ rest) = chain rest * chain steps := by
  simp [chain, operator_chain_eq_prod, List.reverse_append, List.prod_append]

theorem chain_cons (φ : Operator X bot) (rest : List (Operator X bot)) :
    chain (φ :: rest) = chain rest * φ := by
  simpa only [List.singleton_append, chain_single] using chain_append [φ] rest

/-- After `m` steps, the next step receives the image of the initial set
under the first `m` operators. -/
def stageDomain (steps : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  operator_image (chain (steps.take m)) U

@[simp] theorem stageDomain_zero (steps : List (Operator X bot)) (U : Set X) :
    stageDomain steps U 0 = U := by
  change id '' U = U
  exact Set.image_id U

theorem stageDomain_length (steps : List (Operator X bot)) (U : Set X) :
    stageDomain steps U steps.length = operator_image (chain steps) U := by
  simp [stageDomain]

theorem stageDomain_cons (φ : Operator X bot) (rest : List (Operator X bot))
    (U : Set X) (m : ℕ) :
    stageDomain (φ :: rest) U (m + 1) = stageDomain rest (operator_image φ U) m := by
  simp only [stageDomain, List.take_succ_cons, chain_cons, image_mul]

theorem stageDomain_next (steps : List (Operator X bot)) (U : Set X)
    (m : Fin steps.length) :
    stageDomain steps U (m.val + 1) =
      operator_image steps[m.val] (stageDomain steps U m.val) := by
  simp only [stageDomain, List.take_succ_eq_append_getElem m.isLt,
    chain_append, chain_single, image_mul]

theorem stageDomain_subset_step_dom {steps : List (Operator X bot)} {U : Set X}
    (hU : U ⊆ dom (chain steps)) (m : Fin steps.length) :
    stageDomain steps U m.val ⊆ dom steps[m.val] := by
  induction steps generalizing U with
  | nil => exact Fin.elim0 m
  | cons φ rest ih =>
      rw [chain_cons] at hU
      refine Fin.cases ?_ (fun k => ?_) m
      · simpa using fun x hx => (mem_dom_mul.mp (hU (a := x) hx)).1
      · simpa [stageDomain_cons] using ih (image_subset_dom_of_mul hU) k

variable [Fintype I] {g : Gauge X I bot} {U : Set X}

private theorem chain_bound
    (Bound : Operator X bot → Set X → Coefficients I → Prop)
    (comp : ∀ {φ ψ U A B}, U ⊆ dom (ψ * φ) →
      Bound φ U A → Bound ψ (operator_image φ U) B → Bound (ψ * φ) U (B * A))
    {first : Operator X bot × Coefficients I} {rest : List (Operator X bot × Coefficients I)}
    (hU : U ⊆ dom (chain ((first :: rest).map Prod.fst)))
    (hstep : ∀ m : Fin (first :: rest).length,
      Bound (first :: rest)[m.val].1
        (stageDomain ((first :: rest).map Prod.fst) U m.val) (first :: rest)[m.val].2) :
    Bound (chain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) := by
  induction rest generalizing first U with
  | nil =>
      simpa using hstep (0 : Fin 1)
  | cons next rest ih =>
      have hfirst : Bound first.1 U first.2 := by
        simpa using hstep ⟨0, by simp⟩
      have hcomp : U ⊆ dom (chain ((next :: rest).map Prod.fst) * first.1) := by
        simpa only [List.map_cons, chain_cons] using hU
      have htail (m : Fin (next :: rest).length) :
          Bound (next :: rest)[m.val].1
            (stageDomain ((next :: rest).map Prod.fst) (operator_image first.1 U) m.val)
            (next :: rest)[m.val].2 := by
        simpa only [Fin.val_succ, List.getElem_cons_succ, List.map_cons, stageDomain_cons]
          using hstep m.succ
      have hrest := ih (image_subset_dom_of_mul hcomp) htail
      simpa only [List.map_cons, chain_cons, matrixProduct_cons] using comp hcomp hfirst hrest

theorem chain_lip
    {first : Operator X bot × Coefficients I} {rest : List (Operator X bot × Coefficients I)}
    (hU : U ⊆ dom (chain ((first :: rest).map Prod.fst)))
    (hstep : ∀ m : Fin (first :: rest).length,
      LipOn g (first :: rest)[m.val].1
        (stageDomain ((first :: rest).map Prod.fst) U m.val) (first :: rest)[m.val].2) :
    LipOn g (chain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) :=
  chain_bound (LipOn g) lip_comp hU hstep

theorem chain_coLip
    {first : Operator X bot × Coefficients I} {rest : List (Operator X bot × Coefficients I)}
    (hU : U ⊆ dom (chain ((first :: rest).map Prod.fst)))
    (hstep : ∀ m : Fin (first :: rest).length,
      CoLipOn g (first :: rest)[m.val].1
        (stageDomain ((first :: rest).map Prod.fst) U m.val) (first :: rest)[m.val].2) :
    CoLipOn g (chain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) :=
  chain_bound (CoLipOn g) coLip_comp hU hstep

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
        {"file": "LCH02/Bounds.lean", "name": "LCH02.matrixBound"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.matrixBound_apply"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.LipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.Lip"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipMatricesOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipMatrices"}
      ],
      "representation": "I 由 Fintype 穷举。Gauge 打包指标非空性及冻结的分量扩展伪度量公理。LipOn 要求 U ⊆ dom φ，并对 U 中任意点对及每个输出指标 j 要求原上界。matrixBound_apply 给出全部输入分量之和。Lip 取 U = dom φ，两种矩阵族分别由对应谓词作集合分离。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.CoLipOn"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipMatricesOn"}
      ],
      "representation": "CoLipOn 同时要求 U ⊆ dom φ、U.Nonempty，以及对 U 中任意点对与每个输出指标 j，原矩阵和小于等于像点距离。coLipMatricesOn 取满足该谓词的矩阵集合。全域用法取 U = dom φ，仍要求非空。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.Coefficients"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.entry"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.entry_mul"}
      ],
      "representation": "扩展非负系数用 ENNReal。entry A i j 等于 A j i，输入 i 为列，输出 j 为行。entry_mul 展开任意 B * A 的 i→j 条目，对每个中间指标 k 累加 B 的 k→j 条目和 A 的 i→k 条目的乘积。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixUnit"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.entry_unit"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_nil"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_cons"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_single"}
      ],
      "representation": "matrixUnit 为对角 1、非对角 0。列表按应用顺序给定，倒序后取幺半群乘积，即末步矩阵在最左侧、首步矩阵在最右侧。空列表的乘积为单位矩阵，单元素列表的乘积为其唯一矩阵。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.mem_dom_mul"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.image_subset_dom_of_mul"},
        {"file": "LCH02/Bounds.lean", "name": "LCH02.image_mul"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_nil"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_single"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_append"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_cons"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stageDomain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stageDomain_zero"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stageDomain_length"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stageDomain_cons"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stageDomain_next"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.stageDomain_subset_step_dom"}
      ],
      "representation": "steps = [φ₁,…,φₖ]，chain 用冻结的 OperatorChain 复合逆序列表。stageDomain steps U m 是前 m 步作用在 U 上的精确像集，对应 Uₘ₊₁。初始域是 U，递推等式对每个有效步骤成立，末域是全复合的像。从 U ⊆ dom cₖ 推出每一步的实际输入域包含于该步算子的定义域。",
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.pathFactors"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.pathFactors_length"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.PositivePath"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.HasZeroFactor"},
        {"file": "LCH02/Matrix.lean", "name": "LCH02.singleStepPath_unique"}
      ],
      "representation": "对 n = rest.length + 1 步，IndexPath I rest.length 是 Fin (n−1) → I，按从零起算的顺序取 k₁ 至 kₙ₋₁。端点单独给为 i、j。pathFactors 按步列出 n 个相邻条目。PositivePath 量化其每个因子，HasZeroFactor 表示其中至少有一个零。n = 1 时有唯一空中间序列。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_scalar_iff"}
      ],
      "representation": "Subsingleton I 和给定的 i : I 表示 I = {i}。全域 Lip 条件等价于 dom φ 中每个点对在 i 分量上满足系数 entry A i i 的标量上界。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipMatricesOn_antitone"}
      ],
      "representation": "任意 U ⊆ V ⊆ dom φ，证明 V 上合法 Lip 矩阵集合包含于 U 上的集合。U 可以为空。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lipMatrices_restrict"}
      ],
      "representation": "对任意 U ⊆ dom φ，将反单调性的较大域取为 dom φ，得到全域 Lip 证书族包含于 U 上的证书族。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-P02"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.lip_comp"}
      ],
      "representation": "φ、ψ 分别是首步和次步，ψ * φ 是 ψ ∘ φ。U ⊆ dom (ψ * φ)，首步证书 A 在 U 上，次步证书 B 在精确像集 operator_image φ U 上。结论为 B * A 在复合算子的同一个 U 上合法。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipMatricesOn_antitone"}
      ],
      "representation": "在 U.Nonempty 且 U ⊆ V ⊆ dom φ 的前提下，V 上的 co-Lip 证书族包含于 U 上的证书族。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLipMatrices_restrict"}
      ],
      "representation": "对任意非空 U ⊆ dom φ，将较大域取为 dom φ，得到全域 co-Lip 证书族包含于受限证书族。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-P05"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_entry_zero"}
      ],
      "representation": "任取全域 co-Lip 矩阵 A 及定义域内的点对 x、y。若像点的输出分量 j 距离为零且输入分量 i 距离为正，则该求和项为零，进而得到 entry A i j = 0。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.coLip_comp"}
      ],
      "representation": "对 U ⊆ dom (ψ * φ)，给定 A 在 U 上及 B 在精确像集 operator_image φ U 上的 co-Lip 证书。每个证书谓词保留相应域的非空性，结论为 B * A 在复合算子的 U 上合法。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_lip"}
      ],
      "representation": "first :: rest 是任意正长度的算子与矩阵对序列。Fin 下标 m 对应原文第 m+1 步，证书在 stageDomain 给出的实际 Uₘ₊₁ 上。由 U ⊆ dom cₖ 及每一步的 Lip 证书，归纳得到有序矩阵连乘在 cₖ 的 U 上合法。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P04"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_coLip"}
      ],
      "representation": "算子与矩阵对序列及 Fin 下标与 P09 相同。假设每个实际输入域上有对应 co-Lip 证书，非空性随该谓词给出。对任意正长度链，由起始域合法性和逐步证书得到全复合在同一起始域上的有序连乘证书。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P08"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.unit_lip"}
      ],
      "representation": "冻结算子幺半群的 1 是恒等算子，也是空链的值。对任意非空 U ⊆ dom 1，空矩阵乘积 matrixUnit 在 U 上满足 Lip 上界。",
      "dependencies": ["CH02-D01", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Bounds.lean", "name": "LCH02.unit_coLip"}
      ],
      "representation": "对任意非空 U ⊆ dom 1，空矩阵乘积 matrixUnit 在恒等算子的 U 上满足 co-Lip 下界。",
      "dependencies": ["CH02-D01", "CH02-D02", "CH02-D04"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_zero_iff"}
      ],
      "representation": "任意非空矩阵序列 A :: rest 与任意端点 i、j，乘积的 i→j 条目为零当且仅当每个中间指标序列都至少含一个零因子。rest 为空时，唯一空中间序列的路径只有 entry A i j 这一个因子。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Matrix.lean", "name": "LCH02.matrixProduct_pos_iff"}
      ],
      "representation": "任意非空矩阵序列 A :: rest 与任意端点 i、j，乘积的 i→j 条目严格正当且仅当存在一个中间指标序列，其每一步条目均严格正。单步分支使用唯一空中间序列，检验单一条目 entry A i j。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    }
  ]
}
```