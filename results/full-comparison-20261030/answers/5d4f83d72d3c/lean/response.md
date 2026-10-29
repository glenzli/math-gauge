### 审查分析与形式化修订说明

#### 1. 原题面与附件实现的主要偏差
- **演化条件失真**：
  原题面给出的唯一演化条件是：对每个 $x \in A$（即 $q(x) \in B$），
  \[
  q(f(x)) = q(x) \quad\text{或}\quad q(f(x)) = g(q(x))
  \]
  而附件在 [OrbitModel.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) 中定义了严格确定性转移 [`Realizes`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean)（$\forall x,\, q(x) \in B \to q(f(x)) = g(q(x))$），完全去掉了允许“停滞/自环”（$q(f(x)) = q(x)$）的分支。
- **原主张不成立**：
  在原演化条件 [`Evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) 下，原主张 $K = q^{-1}(T_{|B|})$ **不成立**。反向包含 $K \subseteq q^{-1}(T_{|B|})$ 会失败：当 $x \in B$ 且 $g(q(x)) \notin B$ 时，$q(x) \notin T_1$（从而 $q(x) \notin T_{|B|}$）；但由于允许 $q(f(x)) = q(x)$，动力系统 $f$ 可以选择停滞在 $x$，使得轨道始终位于 $A$ 内，即 $x \in K$。因此 $K \not\subseteq q^{-1}(T_{|B|})$。我们在 [Candidate.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) 中给出了完全形式化的反例 [`counterexample`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) 与主张否定定理 [`original_claim_false`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean)。
- **保留的原条件下成立方向**：
  正向包含 $q^{-1}(T_{|B|}) \subseteq K$ 在原演化条件 [`Evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) 下**完全成立**（[`terminal_subset_safe`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean)）。若 $q(x) \in T_{|B|}$，无论下一步取 $q(f(x)) = q(x)$ 还是 $q(f(x)) = g(q(x))$，都有 $q(f(x)) \in T_{|B|}$，故整条轨道永远保持在 $T_{|B|} \subseteq B$ 中。
- **恢复等式的附加条件**：
  附加条件即附件实际使用的强化条件 [`Realizes`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean)（即要求系统必须沿 $g$ 演化，消除停滞自由度）。在该附加条件下，证明了等式恢复定理 [`exact_realization_of_realizes`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean)。
- **真正的最大前向不变集**：
  在原演化条件下，真正的安全集 $K$ 满足 $f$-前向不变性（[`safe_invariant`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean)），且对于任意满足 $S \subseteq A$ 且 $f(S) \subseteq S$ 的不变子集，必有 $S \subseteq K$（[`safe_maximal_of_evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean)）。这确立了 $K$ 是 $A$ 中最大的 $f$-前向不变集，而并非 $q^{-1}(T_{|B|})$。

---

### 原文与声明对应说明及改动理由

| 模块 / 文件 | 原文声明 / 缺陷 | 修订后声明 | 改动理由 |
| :--- | :--- | :--- | :--- |
| [RecordLayers.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/RecordLayers.lean) | `layers_stabilize` 中含有非法语法 `push Not at h`，且归纳变元依赖导致策略脆弱 | 修复 [`layers_stabilize`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/RecordLayers.lean) 证明；增补 [`terminal_subset`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/RecordLayers.lean) | 消除 Lean 4 语法错误，保证核心引理的稳定编译与复用 |
| [OrbitModel.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) | 仅有 [`Realizes`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean)，缺少题面析取演化条件 | 新增 [`Evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) 与 [`realizes_implies_evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) | 忠实形式化题面给定的演化条件，并严格区分原条件与附加条件 |
| [OrbitModel.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) | 无独立的不变集轨道包含引理 | 新增 [`orbit_mem_of_invariant`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) 与 [`safe_maximal`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean) | 为后续在原条件下证明真实安全集 $K$ 的最大性提供通用基石 |
| [Candidate.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) | 误以为原主张成立且将其作为定理证明 | 新增 [`counterexample`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) 与 [`original_claim_false`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) | 反驳原主张在原条件下的有效性，构造具体反例 |
| [Candidate.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) | 仅在 `Realizes` 下证明双向 | 新增 [`terminal_subset_safe`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean)（基于原演化条件 [`Evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/OrbitModel.lean)） | 保留并证明原条件下的可证明单向包含 $q^{-1}(T_{\vert B\vert}) \subseteq K$ |
| [Candidate.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) | 混淆原主张与附加条件主张 | 命名为 [`exact_realization_of_realizes`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) 并保留兼容别名 | 明确恢复等式需引入确定性附加条件，不误称为原主张 |
| [Candidate.lean](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) | 将最大不变集指向 $q^{-1}(T_{\vert B\vert})$ | 证明真实安全集 $K$ 的不变性 [`safe_invariant`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) 与最大性 [`safe_maximal_of_evolves`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F110/work/Candidate.lean) | 纠正不变集对象，严格在原条件下给出 $A$ 中最大前向不变集的形式化证明 |

---

### 完整源码交付

#### `RecordLayers.lean`
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
    have hne : ∀ n ≤ B.card, layers B g (n + 1) ≠ layers B g n := by
      intro n hn heq
      exact h ⟨n, hn, heq⟩
    have hbound : ∀ n, n ≤ B.card + 1 → (layers B g n).card + n ≤ B.card := by
      intro n
      induction n with
      | zero => intro _; simp [layers]
      | succ n ih =>
        intro hn
        have hn' : n ≤ B.card := by omega
        have hi := ih (by omega)
        have hlt : (layers B g (n + 1)).card < (layers B g n).card :=
          Finset.card_lt_card ⟨layers_decreasing B g n, fun hs =>
            hne n hn' (Finset.Subset.antisymm (layers_decreasing B g n) hs)⟩
        omega
    have := hbound (B.card + 1) le_rfl
    omega
  have h₀ := layers_stable_tail B g heq (B.card - m)
  have h₁ := layers_stable_tail B g heq (B.card + 1 - m)
  rw [Nat.add_sub_of_le hm] at h₀
  rw [Nat.add_sub_of_le (by omega : m ≤ B.card + 1)] at h₁
  exact h₁.trans h₀.symm

def terminal (B : Finset Y) (g : Y → Y) : Finset Y := layers B g B.card

theorem terminal_subset (B : Finset Y) (g : Y → Y) : terminal B g ⊆ B :=
  layers_subset B g B.card

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

#### `OrbitModel.lean`
```lean
import RecordLayers

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

/-- 动力系统轨道：从 x 出发迭代 n 步的状态 f^[n](x) -/
def orbit (f : X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => orbit f n (f x)

/-- 安全集合谓词：所有演化时刻的观测值始终属于有限集合 B -/
def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
  ∀ n, q (orbit f n x) ∈ B

/-- 原题面的演化条件：对每个 x ∈ A（即 q x ∈ B），q (f x) = q x 或 q (f x) = g (q x) -/
def Evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = q x ∨ q (f x) = g (q x)

/-- 附加条件（严格确定性实现）：对每个 x ∈ A，演化严格满足 q (f x) = g (q x) -/
def Realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = g (q x)

/-- 附加条件严格强于原题面演化条件 -/
theorem realizes_implies_evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) : Evolves B q f g :=
  fun x hx => Or.inr (h x hx)

/-- 安全状态单步前向演化仍保持安全 -/
theorem safe_step (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) := by
  intro n
  exact hx (n + 1)

/-- 不变子集上的轨道包含引理 -/
theorem orbit_mem_of_invariant (f : X → X) (S : Set X) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ (n : ℕ) {x : X}, x ∈ S → orbit f n x ∈ S
  | 0, _, hx => hx
  | n + 1, x, hx => by
    change orbit f n (f x) ∈ S
    exact orbit_mem_of_invariant f S hS n (hS x hx)

/-- 真正的安全集合 K 在 A 中的最大性（一般动力系统下均成立） -/
theorem safe_maximal (B : Finset Y) (q : X → Y) (f : X → X) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, Safe B q f x := by
  intro x hx n
  exact hB _ (orbit_mem_of_invariant f S hS n hx)

/-- 附加条件 Realizes 下安全点在各记录层中的包含性 -/
theorem safe_in_layers (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) : ∀ (n : ℕ) {x : X}, Safe B q f x → q x ∈ layers B g n
  | 0, _, hx => hx 0
  | n + 1, x, hx => by
    rw [layers, Finset.mem_filter]
    refine ⟨hx 0, ?_⟩
    rw [← h x (hx 0)]
    exact safe_in_layers B q f g h n (safe_step B q f hx)

end MathGauge.F110
```

#### `Candidate.lean`
```lean
import OrbitModel

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

/-!
### 1. 原主张的审查与形式化反例

原题面演化条件允许停滞（`q (f x) = q x`）。当 `g (q x) ∉ B` 时系统若选择停滞，
则该状态依然安全（属于 `K`），但被 `terminal B g` 排除。因此原主张在原条件下不成立。
-/

def cex_X : Type := Unit
def cex_Y : Type := Bool
def cex_B : Finset Bool := {false}
def cex_q : Unit → Bool := fun _ => false
def cex_f : Unit → Unit := id
def cex_g : Bool → Bool := fun _ => true

theorem cex_evolves : Evolves cex_B cex_q cex_f cex_g := by
  intro x _
  left
  rfl

theorem cex_safe : Safe cex_B cex_q cex_f () := by
  intro n
  have horbit : orbit cex_f n () = () := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change orbit cex_f n (cex_f ()) = ()
      exact ih
  change cex_q (orbit cex_f n ()) ∈ cex_B
  rw [horbit]
  exact Finset.mem_singleton.mpr rfl

theorem cex_not_terminal : cex_q () ∉ terminal cex_B cex_g := by
  intro h
  have hmem := (terminal_mem cex_B cex_g (cex_q ())).mp h
  have hstep := (terminal_mem cex_B cex_g (cex_g (cex_q ()))).mp hmem.2
  have htrue : (true : Bool) ∈ ({false} : Finset Bool) := hstep.1
  rw [Finset.mem_singleton] at htrue
  cases htrue

/-- 形式化反例：存在系统满足原演化条件 Evolves，但真正安全集不被 terminal 覆盖 -/
theorem counterexample :
    ∃ (X Y : Type) (_ : DecidableEq Y) (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y),
      Evolves B q f g ∧ ∃ x : X, Safe B q f x ∧ q x ∉ terminal B g :=
  ⟨cex_X, cex_Y, inferInstance, cex_B, cex_q, cex_f, cex_g, cex_evolves, (), cex_safe, cex_not_terminal⟩

/-- 原主张在原演化条件 Evolves 下不成立 -/
theorem original_claim_false :
    ¬ (∀ (X Y : Type) [DecidableEq Y] (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y),
        Evolves B q f g → ∀ x, Safe B q f x ↔ q x ∈ terminal B g) := by
  intro h
  exact cex_not_terminal ((h cex_X cex_Y cex_B cex_q cex_f cex_g cex_evolves ()).mp cex_safe)

/-!
### 2. 原条件下保留的可证明单向包含

在原演化条件 Evolves 下，`q⁻¹(terminal B g) ⊆ K` 依然成立。
-/

theorem terminal_implies_safe_of_evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Evolves B q f g) : ∀ (n : ℕ) {x : X}, q x ∈ terminal B g → q (orbit f n x) ∈ B
  | 0, x, hx => ((terminal_mem B g (q x)).mp hx).1
  | n + 1, x, hx => by
    have hx' := (terminal_mem B g (q x)).mp hx
    have hf : q (f x) ∈ terminal B g := by
      rcases h x hx'.1 with hq | hg
      · rw [hq]; exact hx
      · rw [hg]; exact hx'.2
    change q (orbit f n (f x)) ∈ B
    exact terminal_implies_safe_of_evolves B q f g h n hf

/-- 原条件下的包含定理：`q x ∈ terminal B g → Safe B q f x` -/
theorem terminal_subset_safe (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Evolves B q f g) {x : X} (hx : q x ∈ terminal B g) : Safe B q f x :=
  fun n => terminal_implies_safe_of_evolves B q f g h n hx

/-!
### 3. 恢复等式的附加条件及其证明

附加条件：严格确定性实现条件 `Realizes B q f g`（消除了停滞分支）。
在此附加条件下，`Safe ↔ terminal` 等式得以恢复。
-/

/-- 附加条件下的等式恢复定理 -/
theorem exact_realization_of_realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  ⟨safe_in_layers B q f g h B.card,
   terminal_subset_safe B q f g (realizes_implies_evolves B q f g h)⟩

/-- 兼容原命名（注：依赖附加条件 Realizes，不可作为原主张） -/
theorem exact_realization (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  exact_realization_of_realizes B q f g h x

/-!
### 4. 原条件下真正安全集合 K 的前向不变性与最大性
-/

/-- 原条件下真正安全集 K 的前向不变性 -/
theorem safe_invariant (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) :=
  safe_step B q f hx

/-- 原条件下真正安全集 K 是 A 中最大的 f-前向不变集 -/
theorem safe_maximal_of_evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (_h : Evolves B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, Safe B q f x :=
  safe_maximal B q f S hB hS

/-- 附加条件 Realizes 下终端层诱导集为最大不变集（原附件证明的真实内涵） -/
theorem maximal_invariant_of_realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g := by
  intro x hx
  exact (exact_realization_of_realizes B q f g h x).mp (safe_maximal B q f S hB hS x hx)

/-- 兼容原命名 -/
theorem maximal_invariant (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g :=
  maximal_invariant_of_realizes B q f g h S hB hS

#print axioms counterexample
#print axioms original_claim_false
#print axioms terminal_subset_safe
#print axioms exact_realization_of_realizes
#print axioms safe_maximal_of_evolves

end MathGauge.F110
```
