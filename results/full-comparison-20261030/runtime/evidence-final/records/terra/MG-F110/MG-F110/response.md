原等式不成立。取 \(X=Y=\mathrm{Bool}\)、\(B=\{\mathrm{false}\}\)、\(q=f=\mathrm{id}\)，并令 \(g\) 恒为 `true`。原演化条件成立，但 `false` 永远安全，而 \(T_{|B|}=T_1=\varnothing\)。

原条件下仍有
\[
q^{-1}(T_{|B|})\subseteq K.
\]
下列源码还证明了 \(K\subseteq A\)、\(K\) 的前向不变性，以及 \(K\) 包含 \(A\) 中每个前向不变集。这三个结论实际上不需要演化条件。

恢复等式所用的附加条件是
\[
\forall x\in A,\quad \exists k\in\mathbb N,\quad
q(f^k(x))=g(q(x)).
\]
它允许到达该记录前有停留；当 \(g(q(x))=q(x)\) 时，也允许取 \(k=0\)。附件的 `Realizes` 要求每一步立即取 \(g(q(x))\)，因而蕴含这个附加条件。

声明对应关系如下：

- `layers B g n` 和 `terminal B g` 分别对应 \(T_n\) 和 \(T_{|B|}\)；`terminal_mem` 给出终止层的闭包性质。
- `orbit` 是 \(f\) 的迭代；`admissibleSet`、`safeSet`、`candidateSet` 分别对应 \(A\)、\(K\)、\(q^{-1}(T_{|B|})\)。`OneStep` 保留题目的析取条件。
- `counterexample` 和 `original_set_claim_false` 形式化反例；`candidateSet_subset_safeSet` 给出原条件下正确的包含方向。
- `safeSet_forward_invariant` 和 `safeSet_maximal` 给出真正安全集合的性质。`safeSet_eq_candidateSet_of_eventuallyProgress` 的等式明确带有附加条件；附件中的 `exact_realization` 保留为更强的 `Realizes` 条件下的推论。

`Finset` 表示有限集合；`[DecidableEq Y]` 可通过经典逻辑提供，不对数学上的 \(Y\) 增加限制。

**验证限制：**当前环境未启用代码执行工具，因此下面的源码经过静态核查，但未能在指定的 Lean 和 Mathlib 版本中编译验证。

`RecordLayers.lean`

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
  | zero =>
      exact Finset.filter_subset _ _
  | succ n ih =>
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hB, hg⟩
      exact Finset.mem_filter.mpr ⟨hB, ih hg⟩

theorem layers_subset (B : Finset Y) (g : Y → Y) (n : ℕ) :
    layers B g n ⊆ B := by
  cases n with
  | zero =>
      exact fun _ h => h
  | succ n =>
      exact Finset.filter_subset _ _

theorem layers_stable_tail (B : Finset Y) (g : Y → Y) {m : ℕ}
    (hm : layers B g (m + 1) = layers B g m) (k : ℕ) :
    layers B g (m + k) = layers B g m := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        layers B g (m + (k + 1)) =
            B.filter (fun y => g y ∈ layers B g (m + k)) := rfl
        _ = B.filter (fun y => g y ∈ layers B g m) := by
          rw [ih]
        _ = layers B g m := hm

theorem layers_stabilize (B : Finset Y) (g : Y → Y) :
    layers B g (B.card + 1) = layers B g B.card := by
  obtain ⟨m, hm, heq⟩ :
      ∃ m ≤ B.card, layers B g (m + 1) = layers B g m := by
    by_contra h
    have hne : ∀ n, n ≤ B.card →
        layers B g (n + 1) ≠ layers B g n := by
      intro n hn he
      exact h ⟨n, hn, he⟩
    have hbound :
        ∀ n ≤ B.card + 1, (layers B g n).card + n ≤ B.card := by
      intro n
      induction n with
      | zero =>
          intro hn
          simp [layers]
      | succ n ih =>
          intro hn
          have hn' : n ≤ B.card := by omega
          have hi := ih (by omega : n ≤ B.card + 1)
          have hlt :
              (layers B g (n + 1)).card < (layers B g n).card :=
            Finset.card_lt_card
              ⟨layers_decreasing B g n,
                fun hs =>
                  hne n hn'
                    (Finset.Subset.antisymm
                      (layers_decreasing B g n) hs)⟩
          omega
    have hbad := hbound (B.card + 1) le_rfl
    omega
  have h₀ := layers_stable_tail B g heq (B.card - m)
  have h₁ := layers_stable_tail B g heq (B.card + 1 - m)
  rw [Nat.add_sub_of_le hm] at h₀
  rw [Nat.add_sub_of_le (by omega : m ≤ B.card + 1)] at h₁
  exact h₁.trans h₀.symm

def terminal (B : Finset Y) (g : Y → Y) : Finset Y :=
  layers B g B.card

theorem terminal_mem (B : Finset Y) (g : Y → Y) (y : Y) :
    y ∈ terminal B g ↔ y ∈ B ∧ g y ∈ terminal B g := by
  have h := layers_stabilize B g
  change y ∈ layers B g B.card ↔
    y ∈ B ∧ g y ∈ layers B g B.card
  constructor
  · intro hy
    have hn : y ∈ layers B g (B.card + 1) := by
      rw [h]
      exact hy
    change y ∈ B.filter (fun z => g z ∈ layers B g B.card) at hn
    exact Finset.mem_filter.mp hn
  · intro hy
    have hn : y ∈ layers B g (B.card + 1) := by
      change y ∈ B.filter (fun z => g z ∈ layers B g B.card)
      exact Finset.mem_filter.mpr hy
    rw [h] at hn
    exact hn

end MathGauge.F110
```

`OrbitModel.lean`

```lean
import RecordLayers

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

def orbit (f : X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => orbit f n (f x)

def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
  ∀ n, q (orbit f n x) ∈ B

/-- The original evolution condition, only for states whose record is in B. -/
def OneStep (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = q x ∨ q (f x) = g (q x)

/-- A sufficient additional condition for the reverse inclusion. -/
def EventuallyProgress (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → ∃ k : ℕ, q (orbit f k x) = g (q x)

/-- The stronger condition used by the original attachment. -/
def Realizes (B : Finset Y) (q : X → Y) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = g (q x)

def admissibleSet (B : Finset Y) (q : X → Y) : Set X :=
  q ⁻¹' (B : Set Y)

def safeSet (B : Finset Y) (q : X → Y) (f : X → X) : Set X :=
  {x | Safe B q f x}

def candidateSet (B : Finset Y) (q : X → Y) (g : Y → Y) : Set X :=
  q ⁻¹' (terminal B g : Set Y)

theorem safe_step (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) := by
  intro n
  exact hx (n + 1)

theorem safe_orbit (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) (n : ℕ) :
    Safe B q f (orbit f n x) := by
  induction n generalizing x with
  | zero =>
      exact hx
  | succ n ih =>
      change Safe B q f (orbit f n (f x))
      apply ih
      exact safe_step B q f hx

theorem orbit_mem_of_invariant (f : X → X) (S : Set X)
    (hS : ∀ x ∈ S, f x ∈ S) (n : ℕ) {x : X} (hx : x ∈ S) :
    orbit f n x ∈ S := by
  induction n generalizing x with
  | zero =>
      exact hx
  | succ n ih =>
      change orbit f n (f x) ∈ S
      apply ih
      exact hS x hx

theorem safeSet_subset_admissibleSet
    (B : Finset Y) (q : X → Y) (f : X → X) :
    safeSet B q f ⊆ admissibleSet B q := by
  intro x hx
  change Safe B q f x at hx
  change q x ∈ B
  exact hx 0

theorem safeSet_forward_invariant
    (B : Finset Y) (q : X → Y) (f : X → X) :
    ∀ x ∈ safeSet B q f, f x ∈ safeSet B q f := by
  intro x hx
  change Safe B q f x at hx
  change Safe B q f (f x)
  exact safe_step B q f hx

theorem safeSet_maximal
    (B : Finset Y) (q : X → Y) (f : X → X) (S : Set X)
    (hA : S ⊆ admissibleSet B q)
    (hS : ∀ x ∈ S, f x ∈ S) :
    S ⊆ safeSet B q f := by
  intro x hx
  change Safe B q f x
  intro n
  exact hA (orbit_mem_of_invariant f S hS n hx)

theorem realizes_oneStep
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) :
    OneStep B q f g := by
  intro x hx
  exact Or.inr (h x hx)

theorem realizes_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) :
    EventuallyProgress B q f g := by
  intro x hx
  refine ⟨1, ?_⟩
  exact h x hx

/--
A safe state belongs to every layer if its record eventually reaches
the prescribed g-successor. The original OneStep condition is not needed
for this direction.
-/
theorem safe_in_layers_of_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : EventuallyProgress B q f g) (n : ℕ) {x : X}
    (hx : Safe B q f x) :
    q x ∈ layers B g n := by
  induction n generalizing x with
  | zero =>
      exact hx 0
  | succ n ih =>
      change q x ∈ B.filter (fun y => g y ∈ layers B g n)
      apply Finset.mem_filter.mpr
      refine ⟨hx 0, ?_⟩
      obtain ⟨k, hk⟩ := h x (hx 0)
      rw [← hk]
      apply ih
      exact safe_orbit B q f hx k

/-- Compatibility with the valid lemma from the attachment. -/
theorem safe_in_layers
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (n : ℕ) {x : X}
    (hx : Safe B q f x) :
    q x ∈ layers B g n :=
  safe_in_layers_of_eventuallyProgress B q f g
    (realizes_eventuallyProgress B q f g h) n hx

end MathGauge.F110
```

`Candidate.lean`

```lean
import OrbitModel

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

/-- Under the original condition, the candidate is forward invariant. -/
theorem terminal_step
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) {x : X}
    (hx : q x ∈ terminal B g) :
    q (f x) ∈ terminal B g := by
  obtain ⟨hxB, hxg⟩ := (terminal_mem B g (q x)).mp hx
  rcases h x hxB with hs | hg
  · rw [hs]
    exact hx
  · rw [hg]
    exact hxg

theorem candidateSet_forward_invariant
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) :
    ∀ x ∈ candidateSet B q g, f x ∈ candidateSet B q g := by
  intro x hx
  change q x ∈ terminal B g at hx
  change q (f x) ∈ terminal B g
  exact terminal_step B q f g h hx

/-- This implication uses precisely the original evolution condition. -/
theorem terminal_implies_safe
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) {x : X}
    (hx : q x ∈ terminal B g) :
    Safe B q f x := by
  intro n
  induction n generalizing x with
  | zero =>
      exact ((terminal_mem B g (q x)).mp hx).1
  | succ n ih =>
      change q (orbit f n (f x)) ∈ B
      apply ih
      exact terminal_step B q f g h hx

theorem candidateSet_subset_safeSet
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g) :
    candidateSet B q g ⊆ safeSet B q f := by
  intro x hx
  change q x ∈ terminal B g at hx
  change Safe B q f x
  exact terminal_implies_safe B q f g h hx

/-- A concrete counterexample to the reverse inclusion. -/
theorem counterexample :
    ∃ (B : Finset Bool) (q : Bool → Bool) (f : Bool → Bool)
      (g : Bool → Bool) (x : Bool),
      OneStep B q f g ∧
      Safe B q f x ∧
      q x ∉ terminal B g := by
  refine ⟨({false} : Finset Bool), id, id, (fun _ => true), false,
    ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl rfl
  · intro n
    induction n with
    | zero =>
        decide
    | succ n ih =>
        exact ih
  · decide

/-- Even the Bool instance of the proposed set equality is false. -/
theorem original_set_claim_false :
    ¬ (∀ (B : Finset Bool) (q f g : Bool → Bool),
      OneStep B q f g →
      safeSet B q f = candidateSet B q g) := by
  intro claim
  rcases counterexample with ⟨B, q, f, g, x, hstep, hsafe, hnot⟩
  have heq := claim B q f g hstep
  have hx : x ∈ safeSet B q f := hsafe
  rw [heq] at hx
  exact hnot hx

/-- Equality is restored by the explicitly stated additional condition. -/
theorem safe_iff_terminal_of_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g)
    (hp : EventuallyProgress B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g := by
  constructor
  · intro hx
    exact safe_in_layers_of_eventuallyProgress B q f g hp B.card hx
  · intro hx
    exact terminal_implies_safe B q f g h hx

theorem safeSet_eq_candidateSet_of_eventuallyProgress
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : OneStep B q f g)
    (hp : EventuallyProgress B q f g) :
    safeSet B q f = candidateSet B q g := by
  apply Set.ext
  intro x
  change Safe B q f x ↔ q x ∈ terminal B g
  exact safe_iff_terminal_of_eventuallyProgress B q f g h hp x

/--
The attachment's exact-realization theorem is valid with its stronger
Realizes hypothesis; it is not the original OneStep claim.
-/
theorem exact_realization
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  safe_iff_terminal_of_eventuallyProgress B q f g
    (realizes_oneStep B q f g h)
    (realizes_eventuallyProgress B q f g h) x

/-- The attachment's maximality conclusion under its stronger hypothesis. -/
theorem maximal_invariant
    (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B)
    (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g := by
  intro x hx
  apply (exact_realization B q f g h x).mp
  intro n
  exact hB (orbit f n x) (orbit_mem_of_invariant f S hS n hx)

end MathGauge.F110
```