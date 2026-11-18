20 项义务均已完成。全部源码通过 Lean 4.29.1 与指定 mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6` 的检查。`alignment.json` 中的 47 个声明已核对，公理依赖仅涉及 `propext`、`Classical.choice` 和 `Quot.sound`。

数学原文出自 Zhe Li（Glen Li / glenzli，ORCID 0009-0006-6536-3453）的 *The Operator Evolution Theory*。以下源码为指定选段的 Lean 形式化改编。 [著作主页](https://glenzli.com/books/oet/) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

```lean filename=Main.lean
import LCH02.MatrixBounds
import LCH02.Chains
import LCH02.Paths
```

```lean filename=LCH02/MatrixBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal Matrix

variable {X I : Type} {bot : X}

/-- The ambient finite, nonempty family of extended pseudometrics. -/
structure GaugeFamily (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ℝ≥0∞
  valid : ∀ i, ExtendedPseudoMetric X bot (dist i)

/-- The coefficient from input `i` to output `j` is stored at row `j`, column `i`. -/
abbrev BoundMatrix (I : Type) := Matrix I I ℝ≥0∞

theorem matrix_mul_entry [Fintype I] (B A : BoundMatrix I) (i j : I) :
    (B * A) j i = ∑ k, B j k * A k i :=
  Matrix.mul_apply

theorem matrix_mulVec_entry [Fintype I] (A : BoundMatrix I) (v : I → ℝ≥0∞) (j : I) :
    (A *ᵥ v) j = ∑ i, A j i * v i :=
  rfl

noncomputable def identityMatrix : BoundMatrix I := by
  classical
  exact 1

open scoped Classical in
theorem identityMatrix_entry (i j : I) :
    (identityMatrix : BoundMatrix I) j i = if j = i then 1 else 0 :=
  Matrix.one_apply

/-- The input list is in application order, from the first step to the last. -/
noncomputable def matrixProduct [Fintype I] (matrices : List (BoundMatrix I)) :
    BoundMatrix I := by
  classical
  exact matrices.reverse.prod

@[simp] theorem matrixProduct_nil [Fintype I] :
    matrixProduct ([] : List (BoundMatrix I)) = identityMatrix :=
  rfl

theorem matrixProduct_cons [Fintype I] (A : BoundMatrix I) (As : List (BoundMatrix I)) :
    matrixProduct (A :: As) = matrixProduct As * A := by
  classical
  simp [matrixProduct, List.prod_append]

@[simp] theorem matrixProduct_singleton [Fintype I] (A : BoundMatrix I) :
    matrixProduct [A] = A := by
  classical
  simp [matrixProduct]

private theorem mulVec_mono [Fintype I] (A : BoundMatrix I) {v w : I → ℝ≥0∞}
    (h : v ≤ w) : A *ᵥ v ≤ A *ᵥ w := by
  intro j
  rw [matrix_mulVec_entry, matrix_mulVec_entry]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_right (h i) (A j i))

private theorem identityMatrix_mulVec [Fintype I] (v : I → ℝ≥0∞) :
    identityMatrix *ᵥ v = v := by
  classical
  exact Matrix.one_mulVec v

variable [Fintype I] [Nonempty I] (G : GaugeFamily X I bot)

def distanceVector (x y : X) : I → ℝ≥0∞ := fun i => G.dist i x y

def IsLipOn (f : Operator X bot) (U : Set X) (A : BoundMatrix I) : Prop :=
  U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    distanceVector G (f.func x) (f.func y) ≤ A *ᵥ distanceVector G x y

def IsLip (f : Operator X bot) (A : BoundMatrix I) : Prop :=
  IsLipOn G f (dom f) A

def lipMatricesOn (f : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {A | IsLipOn G f U A}

def lipMatrices (f : Operator X bot) : Set (BoundMatrix I) :=
  {A | IsLip G f A}

def IsCoLipOn (f : Operator X bot) (U : Set X) (A : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    A *ᵥ distanceVector G x y ≤ distanceVector G (f.func x) (f.func y)

def coLipMatricesOn (f : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {A | IsCoLipOn G f U A}

theorem lip_single_component [Subsingleton I] (i : I)
    (f : Operator X bot) (A : BoundMatrix I) :
    A ∈ lipMatrices G f ↔ ∀ x ∈ dom f, ∀ y ∈ dom f,
      G.dist i (f.func x) (f.func y) ≤ A i i * G.dist i x y := by
  classical
  have hrow (x y : X) : (A *ᵥ distanceVector G x y) i = A i i * G.dist i x y := by
    rw [matrix_mulVec_entry, Finset.sum_eq_single i]
    · rfl
    · intro k _ hki
      exact (hki (Subsingleton.elim k i)).elim
    · simp
  constructor
  · intro h x hx y hy
    have hi := h.2 hx hy i
    rw [hrow] at hi
    exact hi
  · intro h
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x y hx hy j
    have hij : j = i := Subsingleton.elim _ _
    subst j
    change G.dist i (f.func x) (f.func y) ≤ (A *ᵥ distanceVector G x y) i
    rw [hrow]
    exact h x hx y hy

theorem lip_restrict {f : Operator X bot} {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    lipMatricesOn G f V ⊆ lipMatricesOn G f U := by
  intro A hA
  refine ⟨hUV.trans hV, ?_⟩
  intro x y hx hy
  exact hA.2 (hUV hx) (hUV hy)

theorem global_lip_restrict {f : Operator X bot} {U : Set X} (hU : U ⊆ dom f) :
    lipMatrices G f ⊆ lipMatricesOn G f U :=
  lip_restrict G hU Set.Subset.rfl

theorem colip_restrict {f : Operator X bot} {U V : Set X}
    (hUn : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    coLipMatricesOn G f V ⊆ coLipMatricesOn G f U := by
  intro A hA
  refine ⟨hUn, hUV.trans hV, ?_⟩
  intro x y hx hy
  exact hA.2.2 (hUV hx) (hUV hy)

theorem global_colip_restrict {f : Operator X bot} {U : Set X}
    (hUn : U.Nonempty) (hU : U ⊆ dom f) :
    coLipMatricesOn G f (dom f) ⊆ coLipMatricesOn G f U :=
  colip_restrict G hUn hU Set.Subset.rfl

theorem composed_domains {f g : Operator X bot} {U : Set X} (hU : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ operator_image f U ⊆ dom g := by
  constructor
  · intro x hx hbot
    have h := hU hx
    change g.func (f.func x) ≠ bot at h
    apply h
    change f.func x = bot at hbot
    rw [hbot, g.preserves_bot]
  · rintro z ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_comp {f g : Operator X bot} {U : Set X} {A B : BoundMatrix I}
    (hU : U ⊆ dom (g * f))
    (hA : A ∈ lipMatricesOn G f U)
    (hB : B ∈ lipMatricesOn G g (operator_image f U)) :
    B * A ∈ lipMatricesOn G (g * f) U := by
  refine ⟨hU, ?_⟩
  intro x y hx hy
  calc
    distanceVector G (g.func (f.func x)) (g.func (f.func y))
        ≤ B *ᵥ distanceVector G (f.func x) (f.func y) :=
      hB.2 (Set.mem_image_of_mem f.func hx) (Set.mem_image_of_mem f.func hy)
    _ ≤ B *ᵥ (A *ᵥ distanceVector G x y) := mulVec_mono B (hA.2 hx hy)
    _ = (B * A) *ᵥ distanceVector G x y := Matrix.mulVec_mulVec _ _ _

theorem colip_comp {f g : Operator X bot} {U : Set X} {A B : BoundMatrix I}
    (hU : U ⊆ dom (g * f))
    (hA : A ∈ coLipMatricesOn G f U)
    (hB : B ∈ coLipMatricesOn G g (operator_image f U)) :
    B * A ∈ coLipMatricesOn G (g * f) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x y hx hy
  calc
    (B * A) *ᵥ distanceVector G x y = B *ᵥ (A *ᵥ distanceVector G x y) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ ≤ B *ᵥ distanceVector G (f.func x) (f.func y) := mulVec_mono B (hA.2.2 hx hy)
    _ ≤ distanceVector G (g.func (f.func x)) (g.func (f.func y)) :=
      hB.2.2 (Set.mem_image_of_mem f.func hx) (Set.mem_image_of_mem f.func hy)

theorem colip_entry_eq_zero {f : Operator X bot} {A : BoundMatrix I} (i j : I)
    (hA : A ∈ coLipMatricesOn G f (dom f))
    (hpair : ∃ x ∈ dom f, ∃ y ∈ dom f,
      G.dist j (f.func x) (f.func y) = 0 ∧ 0 < G.dist i x y) :
    A j i = 0 := by
  classical
  obtain ⟨x, hx, y, hy, hout, hin⟩ := hpair
  have hsum := hA.2.2 hx hy j
  change (A *ᵥ distanceVector G x y) j ≤ G.dist j (f.func x) (f.func y) at hsum
  rw [matrix_mulVec_entry, hout] at hsum
  have hterm : A j i * G.dist i x y ≤ ∑ k, A j k * distanceVector G x y k :=
    Finset.single_le_sum (fun k _ => zero_le (A j k * distanceVector G x y k))
      (Finset.mem_univ i)
  exact (mul_eq_zero.mp (nonpos_iff_eq_zero.mp (hterm.trans hsum))).resolve_right hin.ne'

theorem zero_step_lip {U : Set X} (_hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matrixProduct ([] : List (BoundMatrix I)) ∈ lipMatricesOn G 1 U := by
  refine ⟨hU, ?_⟩
  intro x y _ _
  change distanceVector G x y ≤ identityMatrix *ᵥ distanceVector G x y
  rw [identityMatrix_mulVec]

theorem zero_step_colip {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matrixProduct ([] : List (BoundMatrix I)) ∈ coLipMatricesOn G 1 U := by
  refine ⟨hne, hU, ?_⟩
  intro x y _ _
  change identityMatrix *ᵥ distanceVector G x y ≤ distanceVector G x y
  rw [identityMatrix_mulVec]

end LCH02
```

```lean filename=LCH02/Chains.lean
import LCH02.MatrixBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- Operators are listed in the order in which they act. -/
def chain (ops : List (Operator X bot)) : Operator X bot :=
  OperatorChain ops.reverse

@[simp] theorem chain_nil : chain ([] : List (Operator X bot)) = 1 := rfl

theorem chain_cons (f : Operator X bot) (ops : List (Operator X bot)) :
    chain (f :: ops) = chain ops * f := by
  simp [chain, operator_chain_eq_prod, List.prod_append]

@[simp] theorem chain_singleton (f : Operator X bot) : chain [f] = f := by
  rw [chain_cons, chain_nil, one_mul]

/-- After `m` steps this is the input domain for step `m + 1` in the text. -/
def prefixDomain (ops : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  operator_image (chain (ops.take m)) U

@[simp] theorem prefixDomain_zero (ops : List (Operator X bot)) (U : Set X) :
    prefixDomain ops U 0 = U :=
  Set.image_id U

private theorem prefixDomain_cons_succ
    (f : Operator X bot) (ops : List (Operator X bot)) (U : Set X) (m : ℕ) :
    prefixDomain (f :: ops) U (m + 1) = prefixDomain ops (operator_image f U) m := by
  unfold prefixDomain
  rw [List.take_succ_cons, chain_cons]
  exact (Set.image_image (chain (ops.take m)).func f.func U).symm

theorem prefixDomain_step (ops : List (Operator X bot)) (U : Set X) (m : Fin ops.length) :
    prefixDomain ops U (m.val + 1) = operator_image (ops.get m) (prefixDomain ops U m.val) := by
  induction ops generalizing U with
  | nil => exact m.elim0
  | cons f ops ih =>
    cases m using Fin.cases with
    | zero => simp [prefixDomain_cons_succ]
    | succ k =>
      simpa only [Fin.val_succ, List.get_cons_succ', prefixDomain_cons_succ] using
        ih (operator_image f U) k

theorem prefixDomain_subset (ops : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain ops)) (m : Fin ops.length) :
    prefixDomain ops U m.val ⊆ dom (ops.get m) := by
  induction ops generalizing U with
  | nil => exact m.elim0
  | cons f ops ih =>
    rw [chain_cons] at hU
    obtain ⟨hfirst, hrest⟩ := composed_domains hU
    cases m using Fin.cases with
    | zero => simpa only [Fin.val_zero, List.get_cons_zero, prefixDomain_zero] using hfirst
    | succ k =>
      simpa only [Fin.val_succ, List.get_cons_succ', prefixDomain_cons_succ] using ih hrest k

variable [Fintype I]

private theorem chain_bounds
    (Valid : Operator X bot → Set X → BoundMatrix I → Prop)
    (compose : ∀ {f g : Operator X bot} {U : Set X} {A B : BoundMatrix I},
      U ⊆ dom (g * f) → Valid f U A → Valid g (operator_image f U) B →
      Valid (g * f) U (B * A))
    (steps : List (Operator X bot × BoundMatrix I)) (hne : steps ≠ []) (U : Set X)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hstep : ∀ m : Fin steps.length, Valid (steps.get m).1
      (prefixDomain (steps.map Prod.fst) U m.val) (steps.get m).2) :
    Valid (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact (hne rfl).elim
  | cons s steps ih =>
    have hfirst : Valid s.1 U s.2 := by
      simpa only [Fin.val_zero, List.get_cons_zero, prefixDomain_zero] using
        hstep (0 : Fin (s :: steps).length)
    cases steps with
    | nil => simpa using hfirst
    | cons t rest =>
      have hcomp : U ⊆ dom (chain ((t :: rest).map Prod.fst) * s.1) := by
        simpa only [List.map_cons, chain_cons] using hU
      have htail := ih (hne := by simp) (U := operator_image s.1 U) (composed_domains hcomp).2
        (fun m => by
          simpa only [List.map_cons, List.get_cons_succ', Fin.val_succ, prefixDomain_cons_succ]
            using hstep m.succ)
      simpa only [List.map_cons, chain_cons, matrixProduct_cons] using compose hcomp hfirst htail

variable [Nonempty I] (G : GaugeFamily X I bot)

theorem chain_lip
    (steps : List (Operator X bot × BoundMatrix I)) (hne : steps ≠ []) (U : Set X)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hstep : ∀ m : Fin steps.length, (steps.get m).2 ∈ lipMatricesOn G (steps.get m).1
      (prefixDomain (steps.map Prod.fst) U m.val)) :
    matrixProduct (steps.map Prod.snd) ∈ lipMatricesOn G (chain (steps.map Prod.fst)) U :=
  chain_bounds (IsLipOn G) (fun h => lip_comp G h) steps hne U hU hstep

theorem chain_colip
    (steps : List (Operator X bot × BoundMatrix I)) (hne : steps ≠ []) (U : Set X)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hstep : ∀ m : Fin steps.length, (steps.get m).2 ∈ coLipMatricesOn G (steps.get m).1
      (prefixDomain (steps.map Prod.fst) U m.val)) :
    matrixProduct (steps.map Prod.snd) ∈ coLipMatricesOn G (chain (steps.map Prod.fst)) U :=
  chain_bounds (IsCoLipOn G) (fun h => colip_comp G h) steps hne U hU hstep

end LCH02
```

```lean filename=LCH02/Paths.lean
import LCH02.MatrixBounds
import Mathlib.Data.Fin.Tuple.Basic

namespace LCH02

open scoped BigOperators ENNReal

variable {I : Type}

/-- `n` counts the interior vertices, so there are `n + 1` steps. -/
abbrev IndexPath (I : Type) (n : ℕ) := Fin n → I

def pathVertices {n : ℕ} (i j : I) (p : IndexPath I n) : Fin (n + 2) → I :=
  Fin.cons i (Fin.snoc p j)

@[simp] theorem pathVertices_zero {n : ℕ} (i j : I) (p : IndexPath I n) :
    pathVertices i j p 0 = i := by
  simp [pathVertices]

@[simp] theorem pathVertices_last {n : ℕ} (i j : I) (p : IndexPath I n) :
    pathVertices i j p (Fin.last (n + 1)) = j := by
  rw [← Fin.succ_last]
  simp [pathVertices]

@[simp] theorem pathVertices_interior {n : ℕ} (i j : I)
    (p : IndexPath I n) (k : Fin n) :
    pathVertices i j p k.castSucc.succ = p k := by
  simp [pathVertices]

def pathEntry {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I)
    (p : IndexPath I n) (m : Fin (n + 1)) : ℝ≥0∞ :=
  M m (pathVertices i j p m.succ) (pathVertices i j p m.castSucc)

def PositivePath {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I)
    (p : IndexPath I n) : Prop :=
  ∀ m, 0 < pathEntry M i j p m

theorem empty_path_unique (p : IndexPath I 0) : p = Fin.elim0 :=
  funext fun k => k.elim0

theorem pathEntry_one (M : Fin 1 → BoundMatrix I) (i j : I)
    (p : IndexPath I 0) (m : Fin 1) :
    pathEntry M i j p m = M 0 j i := by
  have hm : m = 0 := Subsingleton.elim _ _
  subst m
  change M 0 (pathVertices i j p (Fin.last 1)) (pathVertices i j p 0) = M 0 j i
  rw [pathVertices_last, pathVertices_zero]

private theorem positivePath_cons {n : ℕ} (M : Fin (n + 2) → BoundMatrix I)
    (i k j : I) (p : IndexPath I n) :
    PositivePath M i j (Fin.cons k p) ↔
      0 < M 0 k i ∧ PositivePath (fun m => M m.succ) k j p := by
  rw [PositivePath, Fin.forall_fin_succ]
  simp only [PositivePath, pathEntry, pathVertices, ← Fin.cons_snoc_eq_snoc_cons,
    Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

variable [Fintype I]

theorem matrixProduct_pos_iff {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    0 < matrixProduct (List.ofFn M) j i ↔ ∃ p : IndexPath I n, PositivePath M i j p := by
  induction n generalizing i with
  | zero =>
    rw [List.ofFn_succ, List.ofFn_zero, matrixProduct_singleton]
    simp only [PositivePath, pathEntry_one]
    exact ⟨fun h => ⟨Fin.elim0, fun _ => h⟩, fun ⟨_, h⟩ => h 0⟩
  | succ n ih =>
    rw [List.ofFn_succ, matrixProduct_cons, matrix_mul_entry,
      Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _), Fin.exists_fin_succ_pi]
    simp only [Finset.mem_univ, true_and, ENNReal.mul_pos_iff, positivePath_cons, ih]
    constructor
    · rintro ⟨k, ⟨p, hp⟩, hk⟩
      exact ⟨k, p, hk, hp⟩
    · rintro ⟨k, p, hk, hp⟩
      exact ⟨k, ⟨p, hp⟩, hk⟩

theorem matrixProduct_zero_iff {n : ℕ} (M : Fin (n + 1) → BoundMatrix I) (i j : I) :
    matrixProduct (List.ofFn M) j i = 0 ↔
      ∀ p : IndexPath I n, ∃ m : Fin (n + 1), pathEntry M i j p m = 0 := by
  classical
  constructor
  · intro hz p
    by_contra hzero
    have hp : PositivePath M i j p :=
      fun m => pos_of_ne_zero (fun hm => hzero ⟨m, hm⟩)
    exact ((matrixProduct_pos_iff M i j).2 ⟨p, hp⟩).ne' hz
  · intro hpaths
    by_contra hprod
    obtain ⟨p, hp⟩ := (matrixProduct_pos_iff M i j).1 (pos_of_ne_zero hprod)
    obtain ⟨m, hm⟩ := hpaths p
    exact (hp m).ne' hm

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
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.IsLipOn"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.IsLip"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lipMatricesOn"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lipMatrices"}
      ],
      "representation": "GaugeFamily 用 Fintype、Nonempty 和冻结的 ExtendedPseudoMetric 表示背景规范族。IsLipOn 要求 U ⊆ dom f，并对每个 x,y ∈ U 逐分量给出矩阵作用后的距离上界。IsLip 取 U = dom f，两个证书族由满足相应谓词的全部矩阵组成。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.IsCoLipOn"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.coLipMatricesOn"}
      ],
      "representation": "IsCoLipOn 同时要求 U.Nonempty、U ⊆ dom f，以及对每个 x,y ∈ U 和每个输出分量，矩阵作用后的输入距离不超过输出距离。coLipMatricesOn 收集所有满足者，取 U = dom f 得到全域证书族。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.BoundMatrix"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrix_mul_entry"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrix_mulVec_entry"}
      ],
      "representation": "BoundMatrix 是以 I 为行列指标的 ENNReal 矩阵，允许无穷条目并沿用 ENNReal 的零乘无穷约定。A j i 对应 i→j。任意 i,j 的 (B*A) j i 对中间指标 k 求和 B j k * A k i，矩阵作用于距离向量的第 j 个分量按同一行求和。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.identityMatrix"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.identityMatrix_entry"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct_nil"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct_cons"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.matrixProduct_singleton"}
      ],
      "representation": "单位矩阵的任意条目在行列相同处取 1，其余取 0。matrixProduct 对按作用顺序给定的列表逆序取积，空表取单位矩阵，单元素表取该矩阵，首步 A 在乘积的最右侧。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_nil"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_cons"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.chain_singleton"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.prefixDomain"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.prefixDomain_zero"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.prefixDomain_step"},
        {"file": "LCH02/Chains.lean", "name": "LCH02.prefixDomain_subset"},
        {"file": "LCH02/MatrixBounds.lean", "name": "LCH02.composed_domains"}
      ],
      "representation": "chain 将按作用顺序列出的算子逆序传给冻结的 OperatorChain。prefixDomain ops U m 是前 m 步复合在 U 上的像，对应 U_{m+1}。前缀零步为 U，每个合法步号的下一个域恰为当前算子的像。从 U ⊆ dom c_k 推出每步的实际输入域包含在该步算子定义域内。",
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "LCH02/Paths.lean", "name": "LCH02.IndexPath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathVertices"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathVertices_zero"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathVertices_last"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathVertices_interior"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathEntry"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.PositivePath"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.empty_path_unique"},
        {"file": "LCH02/Paths.lean", "name": "LCH02.pathEntry_one"}
      ],
      "representation": "对于 n+1 步，IndexPath I n = Fin n → I 恰好记录 n 个中间指标。pathVertices 添入端点 i,j，pathEntry 在每个 m : Fin (n+1) 取第 m.val+1 步从前一顶点到后一顶点的条目。PositivePath 要求每步条目严格正。单步只有一个空中间序列，其条目为 M 0 j i。",
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_single_component"}],
      "representation": "Subsingleton I 在规范族的非空条件下表示唯一分量 i。对任意 f,A，全域证书成员关系等价于对所有 x,y ∈ dom f 的标量上界 d_i(f x,f y) ≤ A i i * d_i(x,y)。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_restrict"}],
      "representation": "固定 f，任意 U ⊆ V ⊆ dom f 上的结论为 V 的受限 Lip 矩阵族包含于 U 的受限 Lip 矩阵族，覆盖 U 为空的情形。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.lip_comp"}],
      "representation": "f,g 对应第一、二步，g*f 是 g∘f。对任意 U ⊆ dom(g*f)，A 的输入域是 U，B 的输入域恰是 operator_image f U。由这两个受限证书推出 B*A 是 g*f 在 U 上的 Lip 证书。",
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.colip_restrict"}],
      "representation": "固定 f，对任意非空 U ⊆ V ⊆ dom f，V 的受限 co-Lip 矩阵族包含于 U 的受限 co-Lip 矩阵族。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.colip_entry_eq_zero"}],
      "representation": "对任意 f、输入 i、输出 j 及全域 co-Lip 证书 A，若存在 x,y ∈ dom f 使输出第 j 分量为零且输入第 i 分量严格正，则 A j i = 0。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.colip_comp"}],
      "representation": "对任意 f,g 及 U ⊆ dom(g*f)，A、B 分别是在 U、精确像域 operator_image f U 上的 co-Lip 证书，故各自输入域非空。结论 B*A 是 g*f 在同一个非空 U 上的 co-Lip 证书。",
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.zero_step_lip"}],
      "representation": "1 是冻结算子幺半群的恒等元。对任意非空 U ⊆ dom(1)，matrixProduct [] 是恒等算子在 U 上的 Lip 证书。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.zero_step_colip"}],
      "representation": "对任意非空 U ⊆ dom(1)，同一个空乘积单位矩阵是恒等算子在 U 上的 co-Lip 证书，成员关系含 U 的非空性。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [{"file": "LCH02/Paths.lean", "name": "LCH02.matrixProduct_pos_iff"}],
      "representation": "任意正长度写成 n+1，M 以 Fin (n+1) 编号，List.ofFn 按步序列出矩阵。任意 i,j 的乘积条目严格正，当且仅当存在一条 i 到 j 的全正路径。n=0 时判据使用唯一空中间序列。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.global_lip_restrict"}],
      "representation": "对任意 f 和 U ⊆ dom f，f 的全域 Lip 矩阵族包含于 f 在 U 上的受限 Lip 矩阵族。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [{"file": "LCH02/MatrixBounds.lean", "name": "LCH02.global_colip_restrict"}],
      "representation": "对任意 f 和非空 U ⊆ dom f，以 dom f 为限制域的 co-Lip 矩阵族包含于 f 在 U 上的受限 co-Lip 矩阵族。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [{"file": "LCH02/Chains.lean", "name": "LCH02.chain_lip"}],
      "representation": "任意非空步列表按作用顺序配对算子和选定 Lip 矩阵。对 U ⊆ dom c_k，每个列表索引的证书只要求在对应实际前缀像域上合法。由这些逐步证书推出逆序矩阵连乘是 c_k 在 U 上的受限 Lip 证书。",
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P04"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [{"file": "LCH02/Chains.lean", "name": "LCH02.chain_colip"}],
      "representation": "任意非空步列表按作用顺序配对算子和选定 co-Lip 矩阵。对 U ⊆ dom c_k，各步证书含对应实际输入像域非空的条件。逆序矩阵连乘属于 c_k 在 U 上的受限 co-Lip 矩阵族，结论包括 U 非空。",
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P08"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [{"file": "LCH02/Paths.lean", "name": "LCH02.matrixProduct_zero_iff"}],
      "representation": "对于任意 n+1 步及任意 i,j，逆序矩阵连乘的 j,i 条目为零，当且仅当对每个中间指标序列存在至少一步的路径条目为零。n=0 时唯一空中间序列只有一个因子 M 0 j i。",
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P14"]
    }
  ]
}
```