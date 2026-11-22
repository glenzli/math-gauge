# 审阅结论总览

经对照原题 [original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md) 与待审答卷 [original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md)（材料关系见 [materials.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/materials.md)），答卷各部分的判定结论如下：

| 题号 | 最终结论是否正确 | 论证是否完整/严格 | 核心问题摘要 |
| --- | --- | --- | --- |
| **S1** | 等化子结论正确 | **有实质错误与缺失** | 第 3 节对「$\dim \mathcal{O}_{X, x_i} \ge 1 \implies \mathcal{O}_{X, x_i}$ 非有限生成 $\mathcal{O}_{X, \Sigma}$-代数」的断言**错误**（$n=1$、1 维曲线及「仅其余点维数为 $1$」的高维情形均给出反例）；拓扑证明缺失同连通分支假设及 $\mathfrak{q}\not\subset\mathfrak{p}_i$ 的证明；未证 $\{U_i\cap U_j\}$ 在 $S_i\cap S_j$ 开邻域中的余终性。 |
| **S2** | 正确 | **有关键逻辑跳跃** | 未界定 $U_0, V, U$ 为 $S$ 的开子集（若为 $X$ 的开集则限制映射 $H(S)\to H(U)$ 不存在）且漏掉「分开」条件 $x_2\notin U_0, x_1\notin V$；未证明使 MV 列正合的覆盖族**非空**、构成**有向系统**及在 $S_1, S_2, S_1\times_S S_2$ 邻域系统中的**余终性**。 |
| **S3** | 正确 | **完整、严格** | 支配性、相容性与双向典范同构构造均严密无误。 |
| **S4** | 正确 | **完整、严格** | 反例 $X=\mathbb{A}^1_k, \Sigma=\{0\}, W=D(t)$ 满足全部前提且论证充分。 |
| **S5** | 目标成立的结论正确 | **核心证明存在致命错误与大段缺失** | **定理（稠密开浸入单射性）及其推论 1、2 均错误**（反例：$F=\mathrm{Pic}$）；由此导致将 S2 直接套用于 $H=F$ 及 $T=S_1\times_S S_2,\,S'\times_S S_n$ 的单射性基础失效；核心几何引理（半局部单射性、MV 收缩引理）几乎空缺；未说明所引 Voevodsky 定理的适用条件、未处理一般域 $k$（有限域/非完美域）与含可比较点的 $\Sigma$。 |
| **S6** | 正确 | **完整、严格** | 第一问反例与第二问两种证明均准确无误。 |

总体判断：**答卷在 S3、S4、S6 上正确且完整；在 S2 上图追逐主干正确，但关键的余极限非空性、有向性与余终性前置验证缺失；在 S1 的反例说明与 S5 的主干论证上存在明确数学错误与重要证明缺口，不能视为完整无误的解答。**

---

## 逐题详细审阅

### S1：层的半局部拼接

* **对应文本**：[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L7-L9)，[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L5-L44)。

1. **第 1–2 节（等化子证明）主干正确，存在两处缺口与若干记号瑕疵**：
   * **未证 $\{U_i\cap U_j\}$ 余终性及仿射极限细节**：在 [original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L14) 与 [L30-L33](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L30-L33)，答卷直接将 $G(S_i \times_S S_j)$ 写作 $\varinjlim_{x_i \in U_i,\, x_j \in U_j} G(U_i \cap U_j)$。按题意 [original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L9)「值以开邻域滤过余极限延拓」，若将 $G(S_i \times_S S_j)$ 理解为延拓至 $S_i \cap S_j \subset X$ 全体开邻域 $W$ 的余极限 $\varinjlim_{S_i\cap S_j\subset W} G(W)$，需补充验证 $\{U_i\cap U_j \mid x_i\in U_i, x_j\in U_j\}$ 在其中余终：在仿射开集 $\operatorname{Spec} A$ 上，$S_i\times_S S_j = \operatorname{Spec}((A\setminus \mathfrak{p}_i)(A\setminus \mathfrak{p}_j))^{-1}A$ 在 $\operatorname{Spec} A$ 中的素理想恰为同时包含于 $\mathfrak{p}_i$ 与 $\mathfrak{p}_j$ 的素理想（因素理想避开乘积 $(A\setminus \mathfrak{p}_i)(A\setminus \mathfrak{p}_j)$ 当且仅当同时避开两个因子集），即 $S_i\cap S_j$；若 $W\cap \operatorname{Spec} A = \operatorname{Spec} A \setminus V(I)$ 包含 $S_i\cap S_j$，则 $I$ 在 $((A\setminus \mathfrak{p}_i)(A\setminus \mathfrak{p}_j))^{-1}A$ 中生成单位理想，从而存在 $f\notin \mathfrak{p}_i, g\notin \mathfrak{p}_j$ 使 $fg\in I$，于是 $x_i\in D(f)$、$x_j\in D(g)$ 且 $D(f)\cap D(g)=D(fg)\subset W$（当 $S_i\cap S_j=\emptyset$ 时局部化环为零环，$0$ 可分解为这样的 $fg$，$D(fg)=\emptyset\subset W$ 同样成立）。此外，[L31](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L31) 的概形逆极限 $\varprojlim (U_i\cap U_j)$ 应取仿射开邻域（如 $D(f)\cap D(g)=D(fg)$）这一余终子族，以确保过渡态射为仿射态射使逆极限存在且与张量积的 $\operatorname{Spec}$ 一致；[L33](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L33) 对对角项 $i=j$ 左侧仅有单变量 $U_i$ 而右侧写为两独立变量 $(U_i, U_j)$ 记号不严（因对角嵌入 $\{(U,U)\}\hookrightarrow \{(U,V)\}$ 余终，极限值相同）。
   * **小细节**：[L8](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L8) 额外假设了基概形为域 $k$，原题未明写基域，但在域或仿射基上拟射影概形的有限点集确实落在某个仿射开子概形中。[L22](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L22) 与 [L37](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L37) 在 `0 → ...` 正合列形式中直接写入平行的双箭头 $\rightrightarrows$ 属记号混用（作正合列应写作差映射 $\operatorname{pr}_1^*-\operatorname{pr}_2^*$，作等化子图通常不写前导 `0 →`；但紧接着的文字说明补清了语义）。

2. **第 3 节（说明 $S_i$ 不必是开子概形）存在明确错误与缺漏**：
   * **概形层面断言错误**（[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L43)）：
     答卷断言：「然而当 $\dim \mathcal{O}_{X, x_i} \ge 1$ 时，局部环 $\mathcal{O}_{X, x_i}$ 作为 $\mathcal{O}_{X, \Sigma}$-代数不是有限生成的，故态射 $S_i \to S$ ……因而不是开子概形。」
     **该断言为假**，以下三类情形均给出直接反例：
     1. **$n=1$ 情形**：无论 $\dim \mathcal{O}_{X, x_1}$ 多大，$S_1 = S$，$\mathcal{O}_{X, x_1} = \mathcal{O}_{X, \Sigma}$，显然有限生成且 $S_1 \to S$ 是开浸入。
     2. **$n\ge 2$ 且 $\dim \mathcal{O}_{X, x_i} = 1$（光滑曲线）**：取 $X = \mathbb{A}^1_k = \operatorname{Spec} k[t]$，$\Sigma = \{x_1, x_2\}$（$x_1=(t),\, x_2=(t-1)$）。此时 $\dim \mathcal{O}_{X, x_1} = \dim k[t]_{(t)} = 1 \ge 1$，但任何 $f(t)\in k[t]\setminus (t)$ 均可写作 $(t-1)^m g(t)$（$t\nmid g,\, (t-1)\nmid g$，故 $g\in M$），因此
        $$\mathcal{O}_{X, x_1} = k[t]_{(t)} = (M^{-1}k[t])\left[\frac{1}{t-1}\right],$$
        作为 $\mathcal{O}_{X, \Sigma}$-代数由单个元素 $(t-1)^{-1}$ 有限生成，$S_1 = D(t-1) = S \setminus \{x_2\}$ **确是 $S$ 的开子概形**。
     3. **$n \ge 2$ 且 $\dim \mathcal{O}_{X, x_i} \ge 2$，但其余点均有 $\dim \mathcal{O}_{X, x_j} = 1$**：取 $X = \mathbb{A}^2_k = \operatorname{Spec} k[x, y]$，$x_1=(x, y)$（$\dim \mathcal{O}_{X, x_1} = 2$），$x_2=(y-1)$（直线 $y=1$ 的泛型点，$\dim \mathcal{O}_{X, x_2} = 1$；两者互相不可特化，恰为 $S$ 的全部闭点）。因 $M^{-1}k[x, y]$ 中任何包含于 $\mathfrak{p}_2=(y-1)$ 的素理想只有 $(0)\subset \mathfrak{p}_1$ 与 $\mathfrak{p}_2$ 本身，故 $S_1 = S \setminus \{x_2\} = D(y-1)$，$\mathcal{O}_{X, x_1} = (M^{-1}k[x, y])[(y-1)^{-1}]$ 仍是有限生成 $\mathcal{O}_{X,\Sigma}$-代数且 $S_1 \to S$ 仍为开浸入（仅 $S_2$ 不是开子概形）。
   * **拓扑层面论证缺失两个前提/步骤**（[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L42)）：
     1. **未要求 $x_i, x_j$ 处于同一连通分支**：若 $X = \mathbb{A}^2_k \sqcup \mathbb{A}^2_k$，$x_1, x_2$ 分处不同连通分支，则 $\dim \mathcal{O}_{X, x_1} = \dim \mathcal{O}_{X, x_2} = 2$，$n=2$，但 $S = S_1 \sqcup S_2$，从而 $S_1$ 仍为 $S$ 的开子概形；同时 $f \notin \mathfrak{p}_i$（如取第一分支上为 $1$、第二分支上为 $0$ 的幂等元）在第二分支上为零，不再能保证「非零元 $f$ 仅包含于 $\mathfrak{p}_j$ 中有限多个高度 1 素理想」。
     2. **漏证 $\mathfrak{q}\not\subset \mathfrak{p}_i$**：即便 $x_i, x_j$ 在同一连通分支（故其局部环所在的分支整环上 $f\notin \mathfrak{p}_i$ 非零）且 $\dim \mathcal{O}_{X, x_j} \ge 2$，当 $\dim \mathcal{O}_{X, x_i} \ge 2$ 时，$\mathfrak{p}_i \cap \mathfrak{p}_j$ 中也存在无穷多个高度 1 素理想（例如 $X=\mathbb{A}^3_k$ 中过两闭点的曲面）。因此仅凭「$\mathfrak{p}_j$ 有无穷多个高度 1 素理想且 $f$ 只在有限个中」不能直接推出存在避开 $\mathfrak{p}_i$ 的 $\mathfrak{q}\subset \mathfrak{p}_j$。严格证法应将 $\operatorname{Spec} A$ 缩至仅含该连通分支（整环），利用素理想避开引理对 $\mathfrak{p}_j$ 避开 $\mathfrak{p}_i$（因 $x_i,x_j$ 为不同闭点故 $\mathfrak{p}_j\not\subset\mathfrak{p}_i$）以及 $f A_{\mathfrak{p}_j}$ 的有限个极小素理想 $\mathfrak{q}_1,\dots,\mathfrak{q}_r$（若 $f\notin\mathfrak{p}_j$ 则无极小素理想；若 $f\in\mathfrak{p}_j$ 则因高度 $1 < 2 \le \operatorname{ht}(\mathfrak{p}_j)$ 故 $\mathfrak{p}_j\not\subset \mathfrak{q}_k$），取 $g \in \mathfrak{p}_j \setminus (\mathfrak{p}_i \cup \bigcup_{k=1}^r \mathfrak{q}_k)$，再由 Krull 主理想定理取 $A_{\mathfrak{p}_j}$ 中包含 $g$ 的高度 1 素理想 $\mathfrak{q}$，即有 $\mathfrak{q}\subset \mathfrak{p}_j$、$g\in \mathfrak{q}\setminus \mathfrak{p}_i$ 故 $\mathfrak{q}\not\subset\mathfrak{p}_i$，且 $f\notin\mathfrak{q}$。
     3. **术语错误**：「相对维数 $\dim \mathcal{O}_{X, x_i}$」应为局部环的 Krull 维数。

* **影响**：S1 的主命题（等化子刻画）证明主干成立；但第 3 节本只需提供一个反例（或严格证明一个充分条件）以说明「不必是开子概形」，答卷却给出了一个错误的普遍代数充分条件和缺少关键步骤的拓扑论证，构成实质缺陷。

---

### S2：分离预层的比较图

* **对应文本**：[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L11-L13)，[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L47-L96)。

1. **第 1 节与第 3 节正确**：
   * [L50-L56](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L50-L56) 将 $n=2$ 的 S1 等化子化为核正合列 $0 \to G(S) \to G(S_1)\oplus G(S_2) \to G(S_1\times_S S_2)$ 正确（$S_i\to S$ 为局部化所诱导的单态射，故 $S_i\times_S S_i \cong S_i$，对角差为零；$S_1\times_S S_2 \cong S_2\times_S S_1$ 使 $(1,2)$ 与 $(2,1)$ 分量等价）。
   * [L68-L95](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L68-L95) 的比较图与四引理图追逐完全严密（[L79](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L79) 指出 $\eta_S$ 单射既可直接由 $T=S$ 得出，也可从顶行正合与中竖直同构推出，均成立）。

2. **第 2 节（[L58-L67](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L58-L67)）存在重要逻辑跳步**：
   * **未界定 $U_0, V, U$ 所在的拓扑空间与 $H(U)$ 的定义**：在正合列 $0\to H(S)\to H(U)\oplus H(V)\to H(U\cap V)$ 中，若 $U, V$ 只是 $X$ 的开集且不覆盖 $S$ 全部（$U$ 不含 $x_2$），则不存在自然限制映射 $H(S)\to H(U)$；它们必须是 **$S$ 的开子集**（此时 $U\subset S$，从而 $H(S)=\varinjlim_{S\subset \widetilde{W}\subset X} H(\widetilde{W}) \to H(U):=\varinjlim_{U\subset \widetilde{U}\subset X} H(\widetilde{U})$ 自然存在）。答卷对此未加界定。
   * **漏写「分开 $x_1, x_2$」的条件**：[L59](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L59) 写为 `（x_1 \in U_0, x_2 \in V 且覆盖 S）`，漏掉了 $x_2 \notin U_0$ 且 $x_1 \notin V$。
   * **未证明「使该序列正合的可缩覆盖 $(U, V)$」非空、构成有向系统及余终性**（[L61-L65](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L61-L65)）：
     1. **非空性**：必须先存在至少一个分开 $x_1, x_2$ 的二开覆盖（如取 $U_0 = S\setminus\{x_2\},\, V = S\setminus\{x_1\}$，利用 $x_1, x_2$ 是 $S$ 的不同闭点故 $U_0, V$ 开且覆满 $S$），再收缩得到正合覆盖；否则常值系统的余极限 [L64](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L64) 将退化为 $0$ 而非 $H(S)$。（顺带指出，[L64](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L64) 的「常值或全覆盖余极限 $H(S)$」用语亦不严谨，此处就是非空有向集上常值函子 $H(S)$ 的余极限。）
     2. **有向性**：两个使 MV 序列正合的覆盖 $(U_1, V_1), (U_2, V_2)$ 之交 $(U_1\cap U_2, V_1\cap V_2)$ **未必自动保持正合**，必须先验证它仍覆盖 $S$（因 $x_1\in U_k$ 开集故 $S_1\subset U_1\cap U_2$，同理 $S_2\subset V_1\cap V_2$，而 $S=S_1\cup S_2$）且分开 $x_1,x_2$，再重新应用题设收缩条件得出新的正合覆盖，才能证明该指标集是有向偏序集。
     3. **余终性与迭代余极限等同**：欲得 [L62-L63](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L62-L63) 的 $\varinjlim H(U)=H(S_1)$、$\varinjlim H(V)=H(S_2)$、$\varinjlim H(U\cap V)=H(S_1\times_S S_2)$，需证明对任意 $x_1, x_2$ 在 $X$ 中的开邻域 $W_1, W_2$，取 $U_0=(W_1\cap S)\setminus\{x_2\},\, V=(W_2\cap S)\setminus\{x_1\}$ 确实构成覆盖 $S$ 且分开 $x_1, x_2$ 的开覆盖（利用 $x_1, x_2$ 为 $S$ 的闭点以及 $S_1\subset W_1\cap S$、$S_2\subset W_2\cap S$ 且 $x_2\notin S_1, x_1\notin S_2$），收缩后有 $U\subset W_1$、$V\subset W_2$、$U\cap V\subset W_1\cap W_2$，结合 S1 中 $W_1\cap W_2$ 在 $S_1\cap S_2$ 开邻域中的余终性以及 $H(U)=\varinjlim_{U\subset \widetilde{U}\subset X} H(\widetilde{U})$ 的迭代余极限，方能将极限项等同于 $H(S_1), H(S_2), H(S_1\times_S S_2)$。答卷对上述步均直接跳过。

* **影响**：图追逐思路正确，但在关键前置——非空性、有向性与余终性验证——存在实质缺漏，影响论证完整性。

---

### S3：含指定点的开集

* **对应文本**：[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L15-L17)，[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L99-L132)。
* **审阅意见**：**完全正确且严密。**
  [L101-L119](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L101-L119) 完整验证了 $\mathcal{I}_W$ 在 $\mathcal{I}$ 中的支配性与相容性；[L120-L131](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L120-L131) 利用预层限制映射与泛性质构造了典范同态 $\phi$ 与显式逆 $\psi$，并核验 $\psi\circ\phi=\mathrm{id}$ 与 $\phi\circ\psi=\mathrm{id}$。

---

### S4：稠密开与邻域系统

* **对应文本**：[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L19-L21)，[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L135-L162)。
* **审阅意见**：**完全正确且严密。**
  反例 $X=\mathbb{A}^1_k=\operatorname{Spec} k[t]$、$\Sigma=\{0\}$、$W=X\setminus\{0\}=D(t)$ 满足域 $k$ 上光滑积分仿射概形、有限非空点集、稠密开子集等全部前提，严格推导出 $\mathcal{I}_W = \emptyset$ 而 $\mathcal{I}\neq\emptyset$，并准确补充了余终的充要条件 $\Sigma\subset W$。

---

### S5：整体对象与全部恢复目标

* **对应文本**：[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L23-L50)，[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L165-L252)。

结论「$\eta_S: F(S) \to F_{\mathrm{Zar}}(S)$ 是同构」在原题条件下成立，但答卷的证明**存在根本性的数学错误以及大段核心步骤缺失**，逐项指出如下：

#### 1. 致命数学错误：整体稠密开单射性与整体 Zariski 分离性均为假（[L189-L207](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L189-L207)）

* **错误断言 1（[L191-L194](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L191-L194)）**：
  答卷声称「设 $Y\in \mathrm{Sm}/k$ 是连通光滑整概形，$W\subset Y$ 是稠密开子集。则限制映射 $F(Y)\to F(W)$ 是单射。」
* **错误断言 2（[L202](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L202)）**：
  答卷由此推论「$F$ 是 Zariski 分离预层：若开覆盖 $(U_\alpha)$ 上 $s|_{U_\alpha}=0$，则 $s$ 在稠密集 $\bigcup U_\alpha$ 上处处为 0，由上述单射性知 $s=0$。」（此外该句表述亦循环：$\bigcup U_\alpha = Y$，已知各 $s|_{U_\alpha}=0$ 并不能推出 $s|_{\bigcup U_\alpha}=0$，除非已先知分离性；即使用上一条也只能取单个非空 $U_\alpha$。）
* **错误断言 3（[L203](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L203)）**：
  答卷推论「分离预层到其层化的典范态射 $F(U)\to F_{\mathrm{Zar}}(U)$ 对任一开子集 $U$ 均是单射。」

* **可核查反例（一例同时证伪断言 1、2、3）**：
  在任意基域 $k$ 上，取 $F(Y) = \mathrm{Pic}(Y) \cong H^1_{\mathrm{Zar}}(Y, \mathcal{O}_Y^\times)$（$Y\in\mathrm{Sm}/k$）。
  1. **满足全部题设条件**：
     * 任一 $Y\in\mathrm{Sm}/k$ 均光滑从而正则且局部阶乘，故 $\mathrm{Pic}(Y)\cong\mathrm{CH}^1(Y)$（按各连通分支取直和）。在任意域 $k$ 上，光滑概形之间的对应按相交乘积与推前 $\alpha^*(\gamma) = (p_Y)_*(\alpha \cdot p_Z^*\gamma)$ 作用在 Chow 群 $\mathrm{CH}^1$ 上（等价地，对在 $Y_0$ 上有限满射的整闭子概形 $V\subset Y\times_k Z$，将 $Z$ 上线丛表示为支撑避开 $V$ 泛型点像的 Cartier 除子、拉回至 $V$ 的正规化 $\widetilde{V}$ 再作 Weil 除子推前，由 $\mathrm{Nm}_{k(V)/k(Y_0)}$ 保持主除子；相交乘积理论保证复合 $(V\circ W)^*=W^*\circ V^*$ 严格成立），从而赋予 $\mathrm{Pic}: \mathrm{Cor}_k^{\mathrm{op}} \to \mathrm{Ab}$ 良定的加性反变函子结构（且图对应 $\Gamma_f$ 诱导线丛拉回 $f^*$），不依赖任何层化定理。
     * 对任意正则概形 $Y\in \mathrm{Sm}/k$，投影诱导出同构 $\mathrm{Pic}(Y) \xrightarrow{\sim} \mathrm{Pic}(Y\times_k \mathbb{A}^1_k)$。
  2. **证伪断言 1**：取 $Y = \mathbb{P}^1_k$，$W = \mathbb{A}^1_k = \mathbb{P}^1_k \setminus \{\infty\}$（稠密开）。限制映射
     $$\mathrm{Pic}(\mathbb{P}^1_k) \cong \mathbb{Z} \longrightarrow \mathrm{Pic}(\mathbb{A}^1_k) = 0$$
     **不是单射**。（即便限定 $Y$ 为光滑**仿射**概形，在任意域 $k$ 上取具有至少两个不同 $k$-有理点 $P_0 \neq P_1$ 的椭圆曲线 $E$——例如当 $k=\mathbb{F}_2$ 时可取 $y^2+y=x^3+x$ 及其点 $P_0=\infty, P_1=(0,0)$——令 $Y = E\setminus\{P_0\}$、$W = Y\setminus\{P_1\}$，由除子局化正合列有 $\mathrm{Pic}(Y)\cong \mathrm{Pic}^0(E)$ 且 $[P_1]-[P_0]\neq 0$ 落在 $\ker(\mathrm{Pic}(Y)\to\mathrm{Pic}(W))$ 中。）
  3. **证伪断言 2**：取 $Y = \mathbb{P}^1_k$ 的 Zariski 开覆盖 $\{U_1, U_2\}$，其中 $U_1 = \mathbb{P}^1_k \setminus \{\infty\} \cong \mathbb{A}^1_k$，$U_2 = \mathbb{P}^1_k \setminus \{0\} \cong \mathbb{A}^1_k$。非零截面 $s = [\mathcal{O}_{\mathbb{P}^1}(1)] \in \mathrm{Pic}(\mathbb{P}^1_k)$ 满足 $s|_{U_1} = 0$ 且 $s|_{U_2} = 0$。故 **$F = \mathrm{Pic}$ 不是 Zariski 分离预层**。
  4. **证伪断言 3**：因任意线丛在 Zariski 局部皆平凡，故 $(\mathrm{Pic})_x = 0$ 对一切点 $x\in|Y|$ 成立，从而 $F_{\mathrm{Zar}} = \mathrm{Pic}_{\mathrm{Zar}} = 0$。对开集 $U = \mathbb{P}^1_k$，典范态射 $\eta_{\mathbb{P}^1_k}: \mathrm{Pic}(\mathbb{P}^1_k) \cong \mathbb{Z} \to 0$ **不是单射**。

* **对后续步骤的连锁影响**：
  * **推论 3（[L204-L206](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L204-L206)）失去依据**：答卷对 $T = S_1 \times_S S_2$（[L233](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L233)）和 $T = S' \times_S S_n$（[L247](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L247)）的单射性是通过对 [L203](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L203) 取滤过余极限得到的；既然 [L203](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L203) 为假，该论证直接坍塌。
  * **不能用「半局部单射性」直接修补 $T = S_1 \times_S S_2$ 或对 $H=F$ 套用 S2**：一方面，当 $\dim X \ge 2$ 时（在**任意域** $k$ 上取 $X=\mathbb{A}^2_k$，$x_1=(0,0),\, x_2=(1,0)$），不可约多项式 $y - x(x-1)g(x)$（$g(x)\in k[x]$ 任意）均对应同时过 $x_1,x_2$ 的不可约曲线，给出 $S_1 \times_S S_2$ 中**无穷多个闭点**，故 $S_1 \times_S S_2$ 并非有限点集处的半局部化；即便把 [L191-L194](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L191-L194) 修正为正确的「半局部稠密开单射性」，也无法直接得到 $\eta_{S_1\times_S S_2}$ 单射。另一方面，S2 明确假设 $H$ 为**分离**预层，而 $F$ 未必分离（如 $F=\mathrm{Pic}$），故不能将 S2 直接套用于 $H=F$。
  * **正确的修补路径**：先证明半局部单射性（由此得 $\eta_S: F(S)\to F_{\mathrm{Zar}}(S)$ 对一切有限点半局部化 $S$ 单射），再证明 $K := \ker(F \to F_{\mathrm{Zar}})$ 是带转移子预层（若 $s\in K(Z)$ 在开覆盖 $\{U_\alpha\}$ 上消失且 $V\in\mathrm{Cor}_k(Y_0,Z)$ 整而有限满射于连通分支 $Y_0$，则 $V$ 的泛型点像落入某个 $U_\alpha$，由 $V\to Y_0$ 有限闭知 $V^*(s)$ 在 $Y_0$ 的某个稠密开子集 $W_Y$ 上消失，再在 $Y_0$ 每一点的仿射邻域处应用单点半局部单射性即知 $V^*(s)\in K(Y_0)$——此法不依赖 $Z$ 拟射影），从而商预层 $F' := F/K \cong \operatorname{im}(F\to F_{\mathrm{Zar}})$ 是一个**分离的**同伦不变带转移预层，且对一切有限点半局部化有 $F'(S)=F(S)$、层化仍为 $F_{\mathrm{Zar}}$；此后对 $F'$ 证明两开覆盖收缩 MV 引理，方可将 S2（及对点数 $n$ 的归纳）合法应用于 $H=F'$。答卷直接对 $H=F$ 应用 S2，在逻辑上不成立。

#### 2. 核心几何证明大段空缺与「黑箱」援引

* **未说明定理适用条件且黑箱援引 Voevodsky 层化定理（[L181-L185](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L181-L185)）**：
  原题明确要求 [original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L3)「援引前项或标准定理时说明实际适用条件」且 [L50](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L50)「给出完整论证」。答卷直接援引 Voevodsky 层化定理（且给出自相矛盾的文献编号：`Theorem 4.18/5.7` 在 [L182](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L182) 用于层化定理，而 [L226](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L226) 又将 `5.7` 写作 `MVW Lemma 4.22 / 5.7` 的收缩引理），既未说明适用域条件（经典文献中层化定理的完全版本通常在**完美域**上陈述），且在数学依赖上 $\eta_S: F(S)\xrightarrow{\sim} F_{\mathrm{Zar}}(S)$ 本身正是建立 $F_{\mathrm{Zar}}$ 具有转移结构、保持同伦不变与等于 $F_{\mathrm{Nis}}$ 的核心步骤之一。
* **半局部单射性的几何构造实为几句口号（[L196-L200](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L196-L200)）**：
  1. 「在 $Y$ 的局部存在标准三元组 $(p: C\to B, Z\subset C\subset \bar{C})$」本身只得到局部开邻域 $C\subset Y$（并得不到全空间 $Y$ 上的等式），且曲线移动构造有理函数使对应避开 $Z$ 需要将底局部化为**半局部概形**（使无穷远截面与 $Z$ 之并在 $\bar{C}_S$ 上的限制成为半局部概形从而线丛平凡），并非对一般仿射底 $B$ 成立。
  2. 原题仅设「$k$ 为域」（[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L27)），未排除**有限域**与**非完美域**。在有限域上，不能直接用线性投影得到标准三元组，需说明高次 Bertini/插值构造或用两个互素次数有限可分扩域上的迹/转移消去核与余核；在非完美域上，射影闭包 $\bar{X}$ 即使正规化在 $\bar{X}\setminus X$ 处也未必对 $k$ 光滑，需要避免依赖无穷远处光滑性的构造（如仅要求 $\bar{C}\to B$ 平坦射影且沿 $C$ 光滑）。答卷对此完全未提。
* **两开覆盖的收缩引理完全未证（[L226-L229](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L226-L229)）**：
  只以「利用曲线纤维化中有限对应对切触截面的移动技术」一句话代过，没有任何实质证明、半局部基变换构造或同伦闭链的验证。

#### 3. 其它步骤缺口（[L223-L250](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L223-L250)）

1. **$\Sigma \subset |X|$ 含可比较点（非闭点）的情形未化归**：与 S1 不同，S5 [original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L39) 仅设 $\Sigma \subset |X|$ 为有限非空点集，未假定其互不特化，故 $\Sigma$ 中的点未必全是 $S$ 的闭点（若 $x_1$ 特化到 $x_2$，即 $\mathfrak{p}_1 \subsetneq \mathfrak{p}_2$，则无法用二开覆盖分开 $x_1, x_2$）。需先将 $\Sigma$ 替换为 $\{\mathfrak{p}_x \mid x \in \Sigma\}$ 中按包含关系**极大**的素理想所对应的点子集 $\Sigma_0$（即 $S$ 的全体闭点，不被 $\Sigma$ 中任何其他点严格特化），说明 $\bigcup_{x\in\Sigma}\mathfrak{p}_x=\bigcup_{x\in\Sigma_0}\mathfrak{p}_x$ 故 $M, S$ 不变，且任意开集包含 $\Sigma_0$ 即自动包含 $\Sigma$ 故邻域余极限不变。答卷 [L223-L250](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L223-L250) 默认 $\Sigma$ 全部是 $S$ 的闭点。
2. **$n=2$ 与 $n\ge 3$ 归纳步的图正合性与余极限过渡缺失**：
   * [L235](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L235) 直接宣称由收缩引理得到 $0\to F(S)\to F(S_1)\oplus F(S_2)\to F(S_1\times_S S_2)$ 正合，跳过由覆盖 $(U,V)$ 过到滤过余极限的非空性、有向性与余终性验证。
   * [L237-L250](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L237-L250) 的归纳步将 $S$ 分为 $S'$ 与 $S_n$，构造了比较梯形图，但：(i) 未定义 $F(S'\times_S S_n)$ 与 $F_{\mathrm{Zar}}(S'\times_S S_n)$ 及说明其与二开交 $U\cap V$（$\Sigma'\subset U, x_n\in V$）余极限的等同；(ii) 底行 $0\to F_{\mathrm{Zar}}(S)\to F_{\mathrm{Zar}}(S')\oplus F_{\mathrm{Zar}}(S_n)\to F_{\mathrm{Zar}}(S'\times_S S_n)$ 并不能仅凭口头「由层的拼接 S1 给出」而略去证明（S1 给的是 $n$ 份局部化 $S_1,\dots,S_n$ 的等化子，需再由 S1 对 $S$ 与 $S'$ 导出或按二元覆盖 $U\supset \Sigma', V\ni x_n$ 取余极限证明）；(iii) 顶行正合性同样缺少对 $\Sigma'\sqcup\{x_n\}$ 的收缩引理与余极限验证；(iv) 右竖直箭头 $\eta_{S'\times_S S_n}$ 再次依赖前述错误的整体分离性。
3. **小细节**：[L176](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L176) 未显式核验光滑拟射影 $k$-概形 $X$ 及其开子概形均分离、有限型从而属于 $\mathrm{Sm}/k$；[L179](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L179) 未写出从 $p^*$ 为同构结合 $p\circ i_0=\mathrm{id}_Y=p\circ i_1$ 推出 $i_0^*=(p^*)^{-1}=i_1^*$ 的一步。

---

### S6：极限正合与阶段正合

* **对应文本**：[original-task.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-task.md#L52-L54)，[original-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L255-L332)。
* **审阅意见**：**完全正确且严密。**
  1. **第一问（[L257-L291](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L257-L291)）**：构造 $(\mathbb{N}, \le)$ 上的二项复形系统 $C_1^{(i)}=\mathbb{Z}\xrightarrow{\times 2}\mathbb{Z}=C_0^{(i)}$，过渡链映射两端皆为 $\times 2$。每阶段 $H_1=0, H_0=\mathbb{Z}/2\mathbb{Z}\neq 0$ 均不正合，而余极限为 $\mathbb{Z}[1/2]\xrightarrow{\times 2}\mathbb{Z}[1/2]$（群同构），严格正合。链映射交换性与余极限算子皆核验无误。
  2. **第二问（[L295-L332](file:///private/tmp/math-gauge-hydrogen-neutral-seven-20261122-v1/runtime/attempts/R004/physical-1/session/work/.revision-input/R004/materials/original-answer.md#L295-L332)）**：方法一利用 $\mathrm{Ab}$ 中滤过余极限正合从而与同调函子交换，直接由每阶段同调类最终消亡推出 $\varinjlim H_n(C_\bullet^{(i)})=0$；方法二直接进行元素追逐验证 $\ker(d_n^\infty)=\operatorname{im}(d_{n+1}^\infty)$。将其限制于集中于两相邻次数的二项复形亦完全成立，两法均严密完整。

---

## 本轮修订说明与自评

* **保留部分**：全部六题的总体对错判定结论；S3、S4、S6 的完整肯定及核验依据；S1 第 1–2 节的余终性补缺分析与第 3 节的拓扑/代数缺陷拆解；S2 第 2 节的有向性与余终性跳步分析；S5 以 $F=\mathrm{Pic}$ 证伪整体稠密开单射与 Zariski 分离性的核心反例结构、Voevodsky 定理黑箱/矛盾编号批评、有限域/非完美域与非闭点 $\Sigma$ 缺失项。
* **新增与修正部分**：
  1. 清理了前稿开头的冗余字符 `{}`，并将全部文件链接修正为当前工作区路径及逐行核实过的真实行号；
  2. 在 **S1** 中增补第 3 节第三类反例（$X=\mathbb{A}^2_k$、$x_1=(0,0)$ 与直线泛型点 $x_2=(y-1)$，说明即便 $n\ge 2$ 且 $\dim\mathcal{O}_{X,x_1}\ge 2$ 仍可成立 $S_1=D(y-1)$ 为开子概形），补全拓扑反例中环与素理想避开细节，并补充 [L22]/[L37] 箭头记号混用的小瑕疵；
  3. 在 **S2** 中补充指明正合覆盖族**非空性**之必要（否则常值余极限 $H(S)$ 退化为 $0$），并指出 [L64]「常值或全覆盖余极限」的用语不严；
  4. 在 **S5** 中修正了仿射反例中误设「非挠类 $[P_1]-[P_0]$」（在 $\overline{\mathbb{F}}_p$ 上不存在）的疏漏，改为任意域上具备两点 $P_0\neq P_1\in E(k)$（仅需 $[P_1]-[P_0]\neq 0$）；改进了 $\mathrm{Pic}$ 带转移结构与 $S_1\times_S S_2$ 无穷多闭点例子对**任意域**（含有限域）的表述；将修补路径中「$K=\ker(F\to F_{\mathrm{Zar}})$ 保持转移」改为不依赖 $Z$ 拟射影的泛型点与单点半局部单射性论证，同时改写 $\Sigma_0$ 的素理想极大性描述使之无歧义。
* **仍未完成/不确定部分**：按审阅任务要求不重做原题整套几何证明，故 S5 中半局部单射性与两开覆盖收缩引理（含有限域、非完美域细节）仅指出缺失位置与合法修补结构，未展开完整施工证明；此外，未检索外部文献核对 `Theorem 4.18/5.7` 与 `MVW Lemma 4.22 / 5.7` 在原书中的真实编号对应，仅就待审答卷内部自相矛盾与缺少域条件进行核查。
* **自评**：对照通用审阅标准，本稿准确区分了待审答卷中真正成立的结论（S3、S4、S6 与 S2 主干、S1 等化子）与实质性数学错误/重要逻辑缺口（S1 第 3 节伪断言、S2 余极限前置条件、S5 整体分离性伪定理及其连锁坍塌），全部反例、行号与依赖分析均已基于文本逐一核实且消除了前稿的细节疏漏，未以未验证断言或篇幅代替依据。