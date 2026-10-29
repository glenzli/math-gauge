{}
### 审核结论摘要

作者提交的 Lean 实现**未能完整覆盖**其自然语言提出的目标。
- **代码内的定理**：在形式化代码自身设定的前提 `Realizes` 下完全成立，证明无误且公理使用标准。
- **作者的自然语言主张**：**不成立（为假命题）**。
- **范围差异的性质**：代码中的前提 `Realizes` 强行删去了自然语言中“允许一次实际演化保持记录不变（即 $q(f(x)) = q(x)$）”的弱前提分支。该范围差异**决定性地破坏了原主张**，存在明显的反例。

---

### 一、 定义、前提、依赖与结论逐项审核

#### 1. 前提与范围差异（关键断裂点）
- **自然语言前提**：
  对任意 $x \in A = q^{-1}(B)$，只假定
  $$q(f(x)) = q(x) \quad \text{或} \quad q(f(x)) = g(q(x))$$
  作者明确指出“这里允许一次实际演化保持记录不变”。
- **代码实现前提**：
  在 [`OrbitModel.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/OrbitModel.lean#L14-L15) 中，作者定义为：
  ```lean
  def Realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
    ∀ x, q x ∈ B → q (f x) = g (q x)
  ```
  **差异定位**：代码中的 `Realizes` 是强确定性假设，要求记录演化**必须且只能**按 $g$ 步进（$q(f(x)) = g(q(x))$），彻底排除了 $q(f(x)) = q(x)$（除非恰好 $g(q(x)) = q(x)$）。这属于**关键性前提强化（Premise Strengthening）**。

#### 2. 定义对应性
- **记录层 $T_n$ 与终端层 $T_{|B|}$**：
  在 [`RecordLayers.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/RecordLayers.lean#L8-L10) 与 [L52](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/RecordLayers.lean#L52) 中：
  ```lean
  def layers (B : Finset Y) (g : Y → Y) : ℕ → Finset Y
    | 0 => B
    | n + 1 => B.filter (fun y => g y ∈ layers B g n)

  def terminal (B : Finset Y) (g : Y → Y) : Finset Y := layers B g B.card
  ```
  精确对应了集合序列 $T_0 = B$，$T_{n+1} = \{y \in B : g(y) \in T_n\}$ 以及 $T_{|B|}$。
- **演化轨道与安全集 $K$**：
  在 [`OrbitModel.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/OrbitModel.lean#L8-L12) 中：
  ```lean
  def orbit (f : X → X) : ℕ → X → X
    | 0, x => x
    | n + 1, x => orbit f n (f x)

  def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
    ∀ n, q (orbit f n x) ∈ B
  ```
  因为 $f^n(x) \in A \iff q(f^n(x)) \in B$，所以 `Safe B q f x` 精确刻画了 $x \in K$。

#### 3. 依赖与公理
- 代码仅依赖 Mathlib 的有限集基数模块 `Mathlib.Data.Finset.Card` 与自动化策略 `Mathlib.Tactic`。
- 全项目无 `sorry`，末尾的 `#print axioms` 仅使用 Lean 标准公理（如 `Classical.choice`、`propext`、`Quot.sound`），依赖完全合规且自洽。

#### 4. 结论对应性
- [`exact_realization`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/Candidate.lean#L18-L21)：在前提 `Realizes B q f g` 下证明了 `Safe B q f x ↔ q x ∈ terminal B g`（即 $K = q^{-1}(T_{|B|})$）。
- [`maximal_invariant`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/Candidate.lean#L23-L33)：在前提 `Realizes B q f g` 下证明了若 $S \subseteq A$ 且 $f(S) \subseteq S$，则 $S \subseteq q^{-1}(T_{|B|})$。
- **结论评价**：代码内的定理在假设 `Realizes` 下完全正确，但**没有证明**包含二元分支 $q(f(x)) = q(x) \lor q(f(x)) = g(q(x))$ 的原命题。

---

### 二、 定理与自然语言主张的分项判定

| 项目 | 判断 | 说明 |
| :--- | :---: | :--- |
| **代码中的定理** (`exact_realization`, `maximal_invariant`) | **正确** | 在代码自身给定的强假设 `Realizes` 下，利用有穷集单调递减链的稳定原理（[`layers_stabilize`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F109/work/RecordLayers.lean#L36-L50)）导出的等价性与最大不变性证明完全无误。 |
| **作者的自然语言主张** ($K = q^{-1}(T_{|B|})$ 且为最大不变集) | **错误** | 在允许 $q(f(x)) = q(x)$（记录不变）的前提下，系统可以通过原地停滞永不离开 $A$。此时 $K$ 严格大于 $q^{-1}(T_{|B|})$，原结论被破坏。 |

---

### 三、 范围差异的决定性影响与反例

#### 1. 决定性反例
取极小的有限系统：
- 设 $X = \{a\}$，$Y = \{0, 1\}$，$B = \{0\}$（满足 $B$ 有限，且 $|B| = 1$）。
- 定义投影与演化映射：
  $$q(a) = 0$$
  $$f(a) = a$$
  $$g(0) = 1, \quad g(1) = 1$$
- **检验自然语言前提**：
  $A = q^{-1}(B) = \{a\}$。
  对唯一元素 $a \in A$：
  $$q(f(a)) = q(a) = 0$$
  满足自然语言中的分支 $q(f(x)) = q(x)$。
- **计算终端层 $T_{|B|}$ 与原像**：
  - $T_0 = B = \{0\}$
  - $T_1 = \{y \in B : g(y) \in T_0\} = \{0 : g(0) \in \{0\}\} = \emptyset$（因为 $g(0) = 1 \notin B$）
  - 因为 $|B| = 1$，所以终端层 $T_{|B|} = T_1 = \emptyset$
  - 从而 $q^{-1}(T_{|B|}) = q^{-1}(\emptyset) = \emptyset$
- **计算安全集 $K$**：
  - 对任意 $n \in \mathbb N$，$f^n(a) = a \in A$
  - 因此 $a \in K$，即 $K = \{a\}$
- **结论对比**：
  $$K = \{a\} \neq \emptyset = q^{-1}(T_{|B|})$$
  同时，$K = \{a\}$ 本身是包含于 $A$ 的非空 $f$-前向不变集（$f(K) = K \subseteq A$），而 $q^{-1}(T_{|B|}) = \emptyset$ 根本不是最大不变集。作者的主张在反例下完全失效。

#### 2. 数学机理分析
在包含“允许保持记录不变”的弱前提下：
1. **单向包含仍然成立**：$q^{-1}(T_{|B|}) \subseteq K$。
   - 若 $y \in T_{|B|}$，则 $y \in B$ 且 $g(y) \in T_{|B|}$；由 $q(f(x)) \in \{q(x), g(q(x))\}$ 可知，若 $q(x) \in T_{|B|}$，则无论走哪个分支都有 $q(f(x)) \in T_{|B|}$。归纳可知 $q^{-1}(T_{|B|})$ 确实是包含于 $A$ 的一个 $f$-前向不变集。
2. **反向包含与最大性彻底失效**：$K \not\subseteq q^{-1}(T_{|B|})$。
   - $T_n$ 的构造完全由 $g$ 的确定性单步转移驱动；一旦某状态 $y \in B$ 满足 $g(y) \notin B$，它在第 1 层就被剔除（$y \notin T_1$）。
   - 然而在实际演化 $f$ 中，原像点 $x$ 可以始终选择停滞分支 $q(f(x)) = q(x)$，永远不会实际执行转移 $g$。这类安全轨道点 $x$ 属于 $K$，但因 $g(q(x)) \notin B$ 而无法进入 $T_{|B|}$。
   - 因此，不加约束地允许停滞时，仅凭 $g$ 的迭代序列 $T_{|B|}$ 无法完整捕获 $K$。
