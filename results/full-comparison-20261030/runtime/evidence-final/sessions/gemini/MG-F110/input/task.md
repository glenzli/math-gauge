# 有限记录筛选的形式化修订

设 $X,Y$ 为任意集合，$B\subseteq Y$ 有限，$q:X\to Y$，$f:X\to X$，$g:Y\to Y$，$A=q^{-1}(B)$。唯一的演化条件是：对每个 $x\in A$，
\[
q(f(x))=q(x)\quad\text{或}\quad q(f(x))=g(q(x)).
\]
定义 $T_0=B$，$T_{n+1}=\{y\in B:g(y)\in T_n\}$，以及 $K=\{x:\forall n\in\mathbb N, f^n(x)\in A\}$。

附件试图证明 $K=q^{-1}(T_{|B|})$，并以此给出 $A$ 中最大的 $f$-前向不变集。请审核并修订这份实现。保持题面对象和量词：若主张成立，给出覆盖原条件的 Lean 证明；若不成立，给出形式化反例，并在原条件下保留可证明的包含方向，再明确陈述一个能恢复等式的附加条件及其证明。还需在原条件下证明真正安全集合 $K$ 的前向不变性和最大性。不要把附加条件下的结果称为原主张。

交付完整 Lean 源码，每个文件使用单独的 `lean` 代码块，在块前标明文件名；同时给出原文—声明对应说明和改动理由。可复用附件中有效的定义与引理，也接受其他正确证明路线。

环境：Lean 4.29.1，Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。附件仅为 `RecordLayers.lean`、`OrbitModel.lean`、`Candidate.lean`。


File: `RecordLayers.lean`
```lean
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MathGauge.F110

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

end MathGauge.F110
```


File: `OrbitModel.lean`
```lean
import RecordLayers

namespace MathGauge.F110

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

end MathGauge.F110
```


File: `Candidate.lean`
```lean
import OrbitModel

namespace MathGauge.F110

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

end MathGauge.F110
```
