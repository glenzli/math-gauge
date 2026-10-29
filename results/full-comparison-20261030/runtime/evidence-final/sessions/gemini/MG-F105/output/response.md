本审核报告针对提交的形式化代码 [`Core.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean)、[`Bridge.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Bridge.lean) 与 [`Candidate.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean)，从声明与定义的对应性、逐项数学依据、代码有效性与覆盖范围三个维度进行审核。

---

### 一、 声明、定义与依赖审核

提交代码完整、精确地形式化了目标命题，各要素对应关系如下：

| 数学对象 / 条件 | 形式化表示 | 所在文件及符号 | 审核结论 |
| :--- | :--- | :--- | :--- |
| 阿贝尔群 $G$ | `variable {G : Type*} [AddCommGroup G]` | [`Core.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L7) | **完全一致**。使用可交换加法群标准型类。 |
| 有限子集 $A \subset G$ | `(A : Finset G)` | [`Core.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L9) | **完全一致**。以 `Finset` 表达有限集合。 |
| 子群 $H \le G$ 及元素 $x\in G$ | `(H : AddSubgroup G) (x : G)` | [`Core.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L9) | **完全一致**。加法子群与群元素。 |
| 切片 $B = \{a \in A : a - x \in H\}$ | [`cosetSlice`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L9-L11) | `A.filter (fun a => a - x ∈ H)` | **完全一致**。并在 [`mem_cosetSlice`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L16-L19) 证得充要特征。 |
| 覆盖关系 $\forall a\in A\,\exists t\in F, a-t\in H$ | [`Covers`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L13-L14) | `∀ a ∈ A, ∃ t ∈ F, a - t ∈ H` | **完全一致**。谓词逐字刻画原定义。 |
| 前提 $B \ne \varnothing$ | `(hB : (cosetSlice A H x).Nonempty)` | [`Candidate.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean#L8) | **完全一致**。在有限集上 `Nonempty` 等价于非空。 |
| 前提 $|A+A| \le K|A|$ ($K \in \mathbb{R}$) | `(hK : ((A + A).card : ℝ) ≤ K * A.card)` | [`Candidate.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean#L9) | **完全一致**。基数经实数强制转换后比较。 |
| 目标构造 $F \subseteq A$、界与覆盖 | [`dense_coset_cover`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean#L7-L11) | `∃ F, F ⊆ A ∧ F.card ≤ K * A.card / B.card ∧ Covers A H F` | **完全一致**。完整表达目标结论。 |

**依赖项评估**：
- 引入了 `Mathlib.Combinatorics.Additive.RuzsaCovering`（鲁扎覆盖引理 `Finset.ruzsa_covering_add`）。
- 引入了 `Mathlib.Algebra.Group.Subgroup.Basic` 与 `Mathlib.Tactic`（提供点式运算 `Pointwise` 与代数判定策略 `abel`）。
- 依赖项属于题目允许的 Mathlib 范围，无任何自定义未证明公理（axiom-free of sorry）。

---

### 二、 逐项数学依据

证明主线由以下四个数学环节严密组合构成：

1. **差集在子群中的闭合性**（[`slice_difference`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Bridge.lean#L7-L12)）：
   - *数学事实*：若 $b, c \in B$，则 $b - x \in H$ 且 $c - x \in H$。由 $G$ 可交换及 $H$ 为子群：
     $$b - c = (b - x) - (c - x) \in H.$$
     即差集满足 $B - B \subseteq H$。
   - *代码实现*：通过 `H.sub_mem` 取差，再经 `abel` 自动化简恒等式 $(b - x) - (c - x) = b - c$。

2. **从代数差集覆盖提升为子群模覆盖**（[`lift_cover`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Bridge.lean#L14-L24)）：
   - *数学事实*：若 $A \subseteq F + (B - B)$，则对任意 $a \in A$，存在 $t \in F$ 及 $d \in B - B$ 使 $a = t + d$。将 $d$ 分解为 $b - c$（$b, c \in B$），则 $a - t = b - c$。由步 1 知 $b - c \in H$，故 $a - t \in H$。
   - *代码实现*：利用点式加减法引理 `Finset.mem_add.mp` 与 `Finset.mem_sub.mp` 解构元素，并调用 [`slice_difference`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Bridge.lean#L7-L12)。

3. **和集大小的单调性与放缩**（[`Candidate.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean#L14-L20)）：
   - *数学事实*：由于 $B \subseteq A$（由 [`slice_subset`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Core.lean#L21-L24) 保证），显然有 $A + B \subseteq A + A$。因此：
     $$|A + B| \le |A + A| \le K|A|.$$
     又因 $B \ne \varnothing$，有 $|B| > 0$（由 `hpos` 给出），将上式改写为 Ruzsa 覆盖引理所需形式：
     $$|A + B| \le \left(\frac{K|A|}{|B|}\right)|B|.$$
   - *代码实现*：利用 `Finset.card_le_card` 传递不等式，结合 `div_mul_cancel₀` 完成向目标系数形式的改写。

4. **应用鲁扎覆盖引理（Ruzsa Covering Lemma）**（[`Candidate.lean`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean#L21-L22)）：
   - *数学事实*：取常数 $C = \frac{K|A|}{|B|}$。对非空有限集 $B$ 及有限集 $A$，满足 $|A + B| \le C|B|$，据鲁扎覆盖引理加法版本，存在 $F \subseteq A$ 满足：
     $$|F| \le C = \frac{K|A|}{|B|},\qquad A \subseteq F + B - B.$$
   - *代码实现*：直接实例化 `Finset.ruzsa_covering_add hB hbound`，得到存在性元组 $\langle F, hFA, hcard, hcov\rangle$，结合 [`lift_cover`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Bridge.lean#L14-L24) 闭合证明。

---

### 三、 代码有效性与覆盖范围区分

#### 1. 代码有效性（Code Validity）
- **类型论与语法正确**：在 Lean 4.29.1 / Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6 环境下：
  - 各定义与引理类型完全一致，特别是 `lift_cover` 期望类型 `A ⊆ F + (B - B)` 与 `Finset.ruzsa_covering_add` 输出类型严格同构，无结合性类型错位。
  - 自然数到实数基数的类型转换（`exact_mod_cast`、`simpa`）均完全闭合目标。
- **公理独立性**：[`#print axioms dense_coset_cover`](file:///private/tmp/math-gauge-full-comparison-20261030/sessions/gemini/MG-F105/work/Candidate.lean#L24) 仅引入标准经典逻辑公理：
  - `Classical.choice`
  - `Quot.sound`
  - `propext`
  完全不含 `sorry`，亦无任何虚构假定，代码有效性为 100%。

#### 2. 覆盖范围与数学广度（Scope & Coverage）
- **群的普遍性**：$G$ 仅声明为加法阿贝尔群 `[AddCommGroup G]`，未附加有限群或特征限制，完备覆盖任意阿贝尔群。
- **关于 `[DecidableEq G]` 约束**：
  - 形式化引入了 `[DecidableEq G]`，这是 Lean 内部处理 `Finset` 基础操作（如 `filter`、`card`、点式运算）的常规技术类型类。
  - 题目明确声明“允许使用经典逻辑”。在经典逻辑下，任何类型均具有可判定相等性（`Classical.decEq`），故该参数不构成对命题数学一般性的任何实质性收缩。
- **边界与退化情形处理**：
  - **$K$ 的取值**：当 $K < 0$ 时，因 $|A+A| \ge 0$，若 $A$ 非空则前提 $hK$ 不可能成立，蕴涵式在前件为假时自然成立，代码对任意实数 $K$ 均严格健壮。
  - **$A$ 与 $B$ 的非空性**：前提 $hB$ 给出 $B \ne \varnothing$。由 $B \subseteq A$ 可得 $A \ne \varnothing$ 且 $|B| > 0$，排除了分母为零的情形。

---

### 四、 总体评估结论

附件三份文件结构分工清晰（定义层 `Core` $\to$ 代数桥接层 `Bridge` $\to$ 主定理层 `Candidate`），数学推导无缝衔接，严格、完整且精确地形式化并证明了目标定理。
