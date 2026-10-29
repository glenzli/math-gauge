# 有限记录上的演化筛选

设 $X,Y$ 为任意集合，$B\subseteq Y$ 有限，$q:X\to Y$，$f:X\to X$，$g:Y\to Y$。令 $A=q^{-1}(B)$。只假定对每个 $x\in A$，
\[
q(f(x))=q(x)\quad\text{或}\quad q(f(x))=g(q(x)).
\]
这里允许一次实际演化保持记录不变。域外没有约束，也不要求 $q$ 单射、满射或 $X$ 有限。

定义 $T_0=B$，$T_{n+1}=\{y\in B:g(y)\in T_n\}$，以及
\[
K=\{x\in X:\forall n\in\mathbb N,\ f^n(x)\in A\}.
\]
作者希望用 $T_{|B|}$ 完整描述 $K$，声称
\[
K=q^{-1}(T_{|B|}),
\]
并把这个集合识别为包含于 $A$ 的最大 $f$-前向不变集。

附件为作者提交的完整 Lean 实现。审核它的定义、前提、依赖和结论是否覆盖上述目标，给出可定位的数学依据，并分别判断代码中的定理与作者的自然语言主张。若存在范围差异，说明差异是否影响原主张，并给出决定性的论证或反例。无需修改文件。

环境：Lean 4.29.1，Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。仅附件为候选输入；`RecordLayers.lean`、`OrbitModel.lean`、`Candidate.lean` 按此顺序组成项目。


File: `RecordLayers.lean`
```lean
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MathGauge.F109

variable {Y : Type*} [DecidableEq Y]

def layers (B : Finset Y) (g : Y → Y) : ℕ → Finset Y
  | 0 => B
  | n + 1 => B.filter (fun y => g y ∈ layers B g n)

theorem layers_decreasing (B : Finset Y) (g : Y → Y) (n : ℕ) :
    layers B g (n + 1) ⊆ layers B g n := by
  induction n with
  | zero => exact Finset.filter_subset _ _
  | succ n ih =>
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hB, hg⟩
    exact Finset.mem_filter.mpr ⟨hB, ih hg⟩

theorem layers_subset (B : Finset Y) (g : Y → Y) (n : ℕ) : layers B g n ⊆ B := by
  cases n with
  | zero => exact fun _ h => h
  | succ n => exact Finset.filter_subset _ _

theorem layers_stable_tail (B : Finset Y) (g : Y → Y) {m : ℕ}
    (hm : layers B g (m + 1) = layers B g m) (k : ℕ) :
    layers B g (m + k) = layers B g m := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      layers B g (m + (k + 1)) = B.filter (fun y => g y ∈ layers B g (m + k)) := rfl
      _ = B.filter (fun y => g y ∈ layers B g m) := by rw [ih]
      _ = layers B g m := hm

theorem layers_stabilize (B : Finset Y) (g : Y → Y) :
    layers B g (B.card + 1) = layers B g B.card := by
  obtain ⟨m, hm, heq⟩ : ∃ m ≤ B.card, layers B g (m + 1) = layers B g m := by
    by_contra h
    push Not at h
    have hbound : ∀ n ≤ B.card + 1, (layers B g n).card + n ≤ B.card := by
      intro n hn
      induction n with
      | zero => simp [layers]
      | succ n ih =>
        have hn' : n ≤ B.card := by omega
        have hi := ih (by omega)
        have hlt : (layers B g (n + 1)).card < (layers B g n).card :=
          Finset.card_lt_card ⟨layers_decreasing B g n, fun hs => h n hn' (Finset.Subset.antisymm (layers_decreasing B g n) hs)⟩
        omega
    have := hbound (B.card + 1) le_rfl
    omega
  have h₀ := layers_stable_tail B g heq (B.card - m)
  have h₁ := layers_stable_tail B g heq (B.card + 1 - m)
  rw [Nat.add_sub_of_le hm] at h₀
  rw [Nat.add_sub_of_le (by omega : m ≤ B.card + 1)] at h₁
  exact h₁.trans h₀.symm

def terminal (B : Finset Y) (g : Y → Y) : Finset Y := layers B g B.card

theorem terminal_mem (B : Finset Y) (g : Y → Y) (y : Y) :
    y ∈ terminal B g ↔ y ∈ B ∧ g y ∈ terminal B g := by
  have h := layers_stabilize B g
  change y ∈ layers B g B.card ↔ _
  rw [← h]
  change y ∈ B.filter (fun y => g y ∈ layers B g B.card) ↔ _
  rw [Finset.mem_filter]
  rfl

end MathGauge.F109
```


File: `OrbitModel.lean`
```lean
import RecordLayers

namespace MathGauge.F109

variable {X Y : Type*} [DecidableEq Y]

def orbit (f : X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => orbit f n (f x)

def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
  ∀ n, q (orbit f n x) ∈ B

def Realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = g (q x)

theorem safe_step (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) := by
  intro n
  exact hx (n + 1)

theorem safe_in_layers (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (n : ℕ) {x : X} (hx : Safe B q f x) :
    q x ∈ layers B g n := by
  induction n generalizing x with
  | zero => exact hx 0
  | succ n ih =>
    apply Finset.mem_filter.mpr
    refine ⟨hx 0, ?_⟩
    rw [← h x (hx 0)]
    exact ih (safe_step B q f hx)

end MathGauge.F109
```


File: `Candidate.lean`
```lean
import OrbitModel

namespace MathGauge.F109

variable {X Y : Type*} [DecidableEq Y]

theorem terminal_implies_safe (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) {x : X} (hx : q x ∈ terminal B g) : Safe B q f x := by
  intro n
  induction n generalizing x with
  | zero => exact ((terminal_mem B g (q x)).mp hx).1
  | succ n ih =>
    have hx' := (terminal_mem B g (q x)).mp hx
    have hf : q (f x) ∈ terminal B g := by rw [h x hx'.1]; exact hx'.2
    exact ih hf

theorem exact_realization (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  ⟨safe_in_layers B q f g h B.card, terminal_implies_safe B q f g h⟩

theorem maximal_invariant (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g := by
  intro x hx
  apply (exact_realization B q f g h x).mp
  intro n
  apply hB
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => exact ih (f x) (hS x hx)

#print axioms exact_realization
#print axioms maximal_invariant

end MathGauge.F109
```
