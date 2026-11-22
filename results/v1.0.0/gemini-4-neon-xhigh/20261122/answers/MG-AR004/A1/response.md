### 总体审阅结论

在原题（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L16-L72)）给定的条件下，该答卷（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L75-L324)、[01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L1-L86)）**总体不正确且不完整**。

各阶段判定汇总如下：

| 题项 | 最终结论方向 | 论证正确性与完整性 | 主要问题概述 |
| :--- | :--- | :--- | :--- |
| **S1** | 正确 | **不完全正确** | 等化子主证基本正确（有轻微余终性省略）；第 3 部分“$S_i$ 不必是开子概形”含**明确错误命题**（概形层面结论对 $n=1$ 或 1 维曲线不成立）与**漏洞/漏前提**（拓扑层面未要求同连通分支，且未证 $\mathfrak{q}\not\subset\mathfrak{p}_i$）。 |
| **S2** | 正确 | **不完整** | 第 1、3 节正确；第 2 节跳过关键论证（未澄清 $U,V$ 为 $S$ 的开覆盖、遗漏“分开 $x_1,x_2$”条件、未证明正合收缩覆盖族非空、有向且余终）。 |
| **S3** | 正确 | **正确且完整** | 余终性证明与预层余极限典范同构构造均无误。 |
| **S4** | 正确（否定） | **正确且完整** | 反例满足全部前提，验证与充要条件均正确。 |
| **S5** | 正确（成立） | **严重错误且严重不完整** | 第 3 节的“整体稠密开浸入单射性”、$F$ 的 Zariski 分离性、对任意开集 $U$ 的 $F(U)\hookrightarrow F_{\mathrm{Zar}}(U)$ **均错误**（反例 $F=\operatorname{Pic}=\mathrm{CH}^1$）；第 2(3) 节援引层化定理遗漏基域完美性并存在逻辑循环；第 5 节核心几何收缩/Mayer–Vietoris 引理**完全无证明**，遗漏有限域 $k$ 与 $\Sigma$ 中存在特化可比点的处理，且对 S1、S2 的套用均不合法。 |
| **S6** | 正确（否定；后半成立） | **正确且完整** | 反例严谨，第二问两种证明均正确。 |

以下按 S1–S6 逐项给出可核查的数学依据与影响分析。

---

### 逐项详细审阅

#### S1：层的半局部拼接
原题：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L24-L26)；答卷：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L81-L120)。

1. **第 2 节（等化子证明）——主干正确，有两处轻微疏漏**：
   - 在有向集 $\mathcal{I}=\prod_{i=1}^n\mathcal{I}_{x_i}$ 上对 Zariski 开覆盖 $\{U_i\}$ 的层等化子正合列取滤过余极限，利用 $\mathbf{U}\mapsto\bigcup_i U_i$ 的余终性及 $\mathrm{Ab}$ 中滤过余极限与有限极限（有限积、等化子）可交换，主体思路正确。
   - **疏漏 1（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L90)、[L106-L109](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L106-L109)）**：题干规定 $G$ 的值按“开邻域滤过余极限延拓”，即 $G(S_i\times_S S_j)=\varinjlim_{|S_i\times_S S_j|\subset W\subset X\,\text{开}} G(W)$。答卷直接将其写为 $\varinjlim_{x_i\in U_i,\,x_j\in U_j} G(U_i\cap U_j)$，未证明 $\{U_i\cap U_j\}$ 在 $|S_i\times_S S_j|$ 的全体开邻域中余终。
     - *可核查补证*：在 $\operatorname{Spec} A\supset\Sigma$ 中，令 $T_i=A\setminus\mathfrak{p}_i, T_j=A\setminus\mathfrak{p}_j$，则 $S_i\times_S S_j=\operatorname{Spec}((T_i T_j)^{-1}A)$。若开集 $W\subset X$ 包含 $|S_i\times_S S_j|$，记 $W\cap\operatorname{Spec} A=\operatorname{Spec} A\setminus V(I)$，则 $I\cdot (T_i T_j)^{-1}A=(T_i T_j)^{-1}A$，从而存在 $f\in T_i, g\in T_j$ 使 $fg\in I$，于是 $x_i\in D(f)$、$x_j\in D(g)$ 且 $D(f)\cap D(g)=D(fg)\subset W$（即便 $S_i\times_S S_j=\emptyset$，亦有 $0\in T_i T_j$，故 $D(f)\cap D(g)=\emptyset\subset W$）。
   - **疏漏 2（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L109)）**：当 $i=j$ 时，$\prod_{i,j}G(U_i\cap U_j)$ 的 $(i,i)$ 分量实际是单指标的 $G(U_i\cap U_i)=G(U_i)$，它等于双指标余极限 $\varinjlim_{x_i\in U_i, x_i\in U_i'} G(U_i\cap U_i')=G(S_i\times_S S_i)$ 依赖对角线 $\mathcal{I}_{x_i}\to\mathcal{I}_{x_i}\times\mathcal{I}_{x_i}$ 的余终性及 $S_i\times_S S_i\cong S_i$，答卷未加区分。

2. **第 3 节（“$S_i$ 不必是 $S$ 的开子概形”）——存在明确错误与逻辑缺口**：
   - **错误断言（概形层面，[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L119)）**：答卷断言“当 $\dim\mathcal{O}_{X,x_i}\ge 1$ 时，局部环 $\mathcal{O}_{X,x_i}$ 作为 $\mathcal{O}_{X,\Sigma}$-代数不是有限生成的，故 $S_i\to S$ 不是有限型的，因而不是开子概形”。**该断言错误**，存在如下反例：
     - **反例 A（$n=1$）**：取任意维数 $\ge 1$ 的光滑概形与单点 $\Sigma=\{x_1\}$，则 $\mathcal{O}_{X,x_1}=\mathcal{O}_{X,\Sigma}$ 显然是有限生成代数，$S_1=S$ 是开子概形。
     - **反例 B（$n=2$，$\dim\mathcal{O}_{X,x_i}=1$）**：取 $X=\mathbb{A}^1_k=\operatorname{Spec} k[t]$，$\Sigma=\{x_1,x_2\}$ 对应极大理想 $\mathfrak{p}_1=(t)$ 与 $\mathfrak{p}_2=(t-1)$，这里 $\dim\mathcal{O}_{X,x_1}=\dim\mathcal{O}_{X,x_2}=1$。记 $M=k[t]\setminus((t)\cup(t-1))$，$R=M^{-1}k[t]=\mathcal{O}_{X,\Sigma}$。对任意 $a/b\in k[t]_{(t)}$（$t\nmid b$），可分解 $b=(t-1)^m c$ 使 $t\nmid c$ 且 $(t-1)\nmid c$，即 $c\in M$，故 $a/b=(a/c)\cdot (t-1)^{-m}\in R[(t-1)^{-1}]$。因此
       $$\mathcal{O}_{X,x_1}=R\left[\frac{1}{t-1}\right]$$
       是有限生成 $\mathcal{O}_{X,\Sigma}$-代数，且 $S_1=D(t-1)=S\setminus\{x_2\}$ **正是** $S$ 的主开子概形。（对任意光滑曲线上的任意有限闭点集均成立，因为半局部 Dedekind 整环皆为主理想整环。）
     - **反例 C（不连通 $X$，任意高维）**：取 $X=\mathbb{A}^2_k\sqcup\mathbb{A}^2_k$，$x_1,x_2$ 分属两个连通分支，则 $S=S_1\sqcup S_2$，$S_1$ 为开闭子概形。
   - **漏洞与漏前提（拓扑层面，[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L118)）**：
     - 答卷断言当 $\dim\mathcal{O}_{X,x_i}\ge 1$、$n\ge 2$ 且 $\dim\mathcal{O}_{X,x_j}\ge 2$（$j\neq i$）时，$S_i$ 在 $S$ 中不是开子集。这在 $x_i,x_j$ 位于不同连通分支时**不成立**（同反例 C：此时 $f=(1,0)\in\mathcal{O}_{X,\Sigma}$ 满足 $f\notin\mathfrak{p}_1$ 但 $D(f)=S_1$，且 $f$ 在第二分支恒零，从而落入 $\mathfrak{p}_2$ 中的**所有**素理想，“非零元 $f$ 仅包含于其中有限多个”失效）。
     - 即使假定 $x_i,x_j$ 处于同一连通分支（整环情形），“$\mathfrak{p}_j$ 中有无穷多个高度 1 素理想，非零元 $f$ 仅含于其中有限多个”仅能得到 $\mathfrak{q}\subset\mathfrak{p}_j$ 使 $f\notin\mathfrak{q}$，**无法直接推出** $\mathfrak{q}\not\subset\mathfrak{p}_i$——因为同时含于 $\mathfrak{p}_i\cap\mathfrak{p}_j$ 的高度 1 素理想也可能有无穷多个（例如同时过 $x_i,x_j$ 的不可约曲线）。要严格补全，须对含 $f$ 的有限个高度 1 素理想 $\mathfrak{q}_1,\dots,\mathfrak{q}_r$ 及 $\mathfrak{p}_i$ 应用素理想避让引理：由 $\operatorname{ht}(\mathfrak{p}_j)\ge 2$ 且 $\mathfrak{p}_j\not\subset\mathfrak{p}_i$，取 $g\in\mathfrak{p}_j\setminus(\mathfrak{p}_i\cup\bigcup_{l=1}^r\mathfrak{q}_l)$，再取 $\mathfrak{p}_j$ 中极小包含 $(g)$ 的素理想 $\mathfrak{q}$；由 Krull 主理想定理 $\operatorname{ht}(\mathfrak{q})=1$，且 $g\in\mathfrak{q}$ 同时保证 $\mathfrak{q}\not\subset\mathfrak{p}_i$ 与 $f\notin\mathfrak{q}$。
     - 另注：将 $\dim\mathcal{O}_{X,x_i}$ 称为“相对维数”用词不当（应为局部环的 Krull 维数，即 $x_i$ 在 $X$ 中的余维数）。
   - **影响**：原题仅要求说明“这里的 $S_i$ 不必是开子概形”（例如举 $X=\mathbb{A}^2_k$ 上两个闭点即可），答卷给出两条过强的一般性命题，其中一条有反例、另一条漏前提且推理有缺口，构成 S1 的实质性失分点。

---

#### S2：分离预层的比较图
原题：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L28-L30)；答卷：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L123-L172)。

1. **正确部分**：第 1 节将 S1 的 $n=2$ 情形化简为核正合列 $0\to G(S)\xrightarrow{\alpha_G}G(S_1)\oplus G(S_2)\xrightarrow{\delta_G}G(S_1\times_S S_2)$ 正确；第 3 节（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L144-L172)）在两行正合的前提下利用图追逐证明 $\eta_S$ 是同构完全严谨。
2. **第 2 节（预层 $H$ 的滤过余极限，[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L134-L143)）的关键论证缺失**：
   - **未澄清 $U,V$ 的空间归属**：正合列 $0\to H(S)\to H(U)\oplus H(V)\to H(U\cap V)$ 要存在限制映射 $H(S)\to H(U)\oplus H(V)$，$(U,V)$ 须为 $S$ 的开覆盖（即 $U=\tilde{U}\cap S, V=\tilde{V}\cap S$，其截面由相应邻域局部化余极限 $H(U)=\varinjlim_{\Sigma\subset\Omega}H(\tilde{U}\cap\Omega)$ 定义）。答卷未交代这一点，第 140 行“第一项为常值或全覆盖余极限 $H(S)$”暴露出对 $U,V$ 属于 $S$ 还是 $X$ 的混淆。
   - **遗漏“分开 $x_1,x_2$”的分离条件（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L135)）**：括号内仅写“$x_1\in U_0, x_2\in V$ 且覆盖 $S$”，漏掉了 $x_2\notin U_0$ 且 $x_1\notin V$。该条件在收缩步骤中**不可或缺**：只有当 $x_1\notin V$ 时，收缩 $(U_0,V)$ 为仍覆盖 $S$ 的 $(U,V)$ 才能迫使 $x_1\in U$（否则 $U$ 可缩为空集）。
   - **完全未证指标集的非空性、有向性（滤过性）与余终性（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L137-L140)）**：答卷直接写“在所有使该序列正合的可缩覆盖 $(U,V)$ 构成的有向系统上取滤过余极限”，却完全没有论证：
     1. 记该集合为 $\mathcal{P}_{\mathrm{good}}$，为何非空（因为 $x_1,x_2$ 是 $S$ 的两个不同闭点，$(S\setminus\{x_2\}, S\setminus\{x_1\})$ 是分开 $x_1,x_2$ 的开覆盖，收缩后即得元素）；
     2. 为何 $\mathcal{P}_{\mathrm{good}}$ **有向**：给定 $(U_1,V_1),(U_2,V_2)\in\mathcal{P}_{\mathrm{good}}$，为何 $(U_1\cap U_2, V_1\cap V_2)$ **仍然覆盖 $S$**？（这实质利用了 $S$ 的半局部性：$S$ 的每一点均特化到 $x_1$ 或 $x_2$，故任何含 $x_1$ 的开集必含 $x_1$ 的全部泛化点，含 $x_2$ 的开集必含 $x_2$ 的全部泛化点，从而 $(U_1\cap U_2)\cup(V_1\cap V_2)=S$；再对此分开覆盖应用题设收缩才得到共同上界。）
     3. 为何 $\mathcal{P}_{\mathrm{good}}$ 在 $(x_1,x_2)$ 的全体开邻域对中**余终**，以及为何取该余极限确得 $\varinjlim H(U)=H(S_1)$、$\varinjlim H(V)=H(S_2)$ 和 $\varinjlim H(U\cap V)=H(S_1\times_S S_2)$。
   - **影响**：使顶部正合列 $0\to H(S)\to H(S_1)\oplus H(S_2)\to H(S_1\times_S S_2)$ 的导出存在明显逻辑缺口，证明不完整。

---

#### S3：含指定点的开集
原题：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L32-L34)；答卷：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L175-L208)。

- **结论：正确且完整。**
- 支配性（取 $U=V\cap W$）与相容性（取 $U_3=U_1\cap U_2$）验证无误；典范同态 $\phi$ 与逆态射 $\psi$（通过 $\mathcal{F}(V)\to\mathcal{F}(V\cap W)\to\varinjlim_{\mathcal{I}_W}\mathcal{F}$ 与余极限泛性质构造）的相容性及 $\psi\circ\phi=\mathrm{id},\,\phi\circ\psi=\mathrm{id}$ 验证清楚。

---

#### S4：稠密开与邻域系统
原题：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L36-L38)；答卷：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L211-L238)。

- **结论：正确且完整。**
- 否定结论正确；所给反例（任意域 $k$，$X=\mathbb{A}^1_k$，$\Sigma=\{0\}$，$W=D(t)=X\setminus\{0\}$）满足光滑、积分、仿射、有限非空与稠密开的全部前提，推出 $\mathcal{I}_W=\emptyset$ 不在非空有向集 $\mathcal{I}$ 中余终的论证严谨，附带的充要条件 $\Sigma\subset W$ 亦正确。

---

#### S5：整体对象与全部恢复目标
原题：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L40-L67)；答卷：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L241-L324) 与 [01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L1-L5)。

首先确认：原题命题**本身在给定条件下（任意域 $k$，无需完美或无限假设）成立**，即 $\eta_S:F(S)\to F_{\mathrm{Zar}}(S)$ 确为同构；答卷第 1 节的判定结论及第 4 节 $|\Sigma|=1$ 的茎同构证明（[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L286-L294)）是正确的。

但是，答卷对 S5 的**核心证明存在多项致命数学错误与严重缺口，整体论证不成立**：

##### 问题 5.1（致命错误）：第 3 节“稠密开浸入单射性”及推论 1、2 均**错误**，推论 3 失去依据
位置：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L265-L282)。

- **错误断言清单**：
  1. 定理（[L267-L270](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L267-L270)）：对任意连通光滑整概形 $Y\in\mathrm{Sm}/k$ 与稠密开子集 $W\subset Y$，限制映射 $F(Y)\to F(W)$ 单射。
  2. 推论 1（[L278](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L278)）：$F$ 是 Zariski 分离预层。
  3. 推论 2（[L279](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L279)）：对任意开子集 $U$，$F(U)\to F_{\mathrm{Zar}}(U)$ 单射。

- **严格反例（对任意域 $k$ 均成立）**：取 $F=\operatorname{Pic}\cong\mathrm{CH}^1:\mathrm{Cor}_k^{\mathrm{op}}\to\mathrm{Ab}$。
  - **满足全部前提**：对光滑概形 $Y,Z\in\mathrm{Sm}/k$，$Y\times_k Z$ 光滑，每个基本有限对应 $V\subset Y_0\times_k Z$（在连通分支 $Y_0$ 上有限满射，投影记作 $p:V\to Y_0, q:V\to Z$）通过光滑概形上的 Chow 对应作用 $V^*(\alpha)=p_*(c_1(q^*\alpha)\cap [V])$（参见 Fulton, *Intersection Theory*, Prop. 16.1.2）诱导良定义的群同态 $\mathrm{CH}^1(Z)\to\mathrm{CH}^1(Y_0)$，与 $\mathrm{Cor}_k$ 中交积推前复合严格兼容，对图态射退化为通常拉回；显然可加。又因每个 $Y\in\mathrm{Sm}/k$ 正则从而正规，投影诱导同构 $\operatorname{Pic}(Y)\xrightarrow{\sim}\operatorname{Pic}(Y\times_k\mathbb{A}^1_k)$。
  - **逐条推翻**：
    1. 取 $Y=\mathbb{P}^1_k\in\mathrm{Sm}/k$（连通、光滑、整、分离、有限型）及稠密开子集 $W=\mathbb{A}^1_k\subset\mathbb{P}^1_k$。则 $F(\mathbb{P}^1_k)=\operatorname{Pic}(\mathbb{P}^1_k)\cong\mathbb{Z}$，而 $F(\mathbb{A}^1_k)=\operatorname{Pic}(\mathbb{A}^1_k)=0$，限制映射 $\mathbb{Z}\to 0$ **不是单射**。（即便额外要求 $Y$ 仿射，该定理仍不成立：例如 $k=\mathbb{R}$ 时取光滑整仿射曲线 $Y=\operatorname{Spec}\mathbb{R}[x,y]/(x^2+y^2-1)$，其为 $\mathbb{P}^1_{\mathbb{R}}$ 除去一个 2 次闭点，故 $\operatorname{Pic}(Y)\cong\mathbb{Z}/2\mathbb{Z}\neq 0$；再去掉有理点 $P=(1,0)$ 得稠密开集 $W=Y\setminus\{P\}\cong\operatorname{Spec}\mathbb{R}[t,(t^2+1)^{-1}]$，为主理想整环，故 $\operatorname{Pic}(W)=0$。）
    2. 在 $\mathbb{P}^1_k$ 的标准 Zariski 开覆盖 $\{U_0,U_1\}$（$U_0\cong U_1\cong\mathbb{A}^1_k$）上，非零元素 $\mathcal{O}_{\mathbb{P}^1}(1)\in\operatorname{Pic}(\mathbb{P}^1_k)$ 在 $U_0,U_1$ 上的限制皆为 $0$，故 **$F$ 不是 Zariski 分离预层**。
    3. 因线丛 Zariski 局部平凡，对任意 $x\in Y$ 有 $\operatorname{Pic}(\operatorname{Spec}\mathcal{O}_{Y,x})=0$，故 $F_{\mathrm{Zar}}=0$；于是 $F(\mathbb{P}^1_k)=\mathbb{Z}\to F_{\mathrm{Zar}}(\mathbb{P}^1_k)=0$ **不是单射**。

- **证明过程本身的多重错漏**：
  - [L272-L275](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L272-L275)：标准三元组只存在在**局部**开邻域 $C\subset Y$ 上，且在构造回避 $Z$ 的 $\mathbb{A}^1$-同伦时，还必须基变换到**半局部化 $S$**（使 $X_{\infty,S}\cup Z_S$ 半局部从而线丛在其上平凡；否则即使在单个标准三元组上，例如椭圆曲线 $C=E\setminus\{\infty\}\to\operatorname{Spec}\mathbb{C}$ 与 $Z=\{P\}$，$F=\operatorname{Pic}$ 上依然无整体回避 $Z$ 的同伦）。答卷既混淆局部与整体，又用“高斯除法”等空泛措辞替代严格构造。
  - [L278](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L278)：“若开覆盖 $(U_\alpha)$ 上 $s|_{U_\alpha}=0$，则 $s$ 在稠密集 $\bigcup U_\alpha$ 上处处为 0”本身是**循环论证**（$\bigcup U_\alpha=Y$，由此推出在并集上为 0 正是待证的分离性）。
  - [L280-L282](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L280-L282)：推论 3 完全建立在错误的推论 2 上，因此 $\eta_S$ 的单射性未获有效证明；更严重的是，对纤维积 $T=S_1\times_S S_2$ 或 $S'\times_S S_n$，当 $\dim X\ge 2$ 时 $T$ 含无穷多个闭点（如同时过 $x_1,x_2$ 的全部不可约超曲面/曲线），**不是半局部概形**，因而即便将错误定理修正为正确的半局部单射定理 $F(S)\hookrightarrow F(S\cap W)$，也**不能直接推出** $\eta_{S_1\times_S S_2}$ 单射。
- **影响**：直接导致第 5.2 节（套用 S2）与第 5.3 节（归纳步右侧箭头单射性）所依赖的前提全部失效。

##### 问题 5.2（前提遗漏与逻辑循环）：第 2(3) 节援引 Voevodsky 层化定理
位置：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L257-L262)。

- 原题明确要求“援引前项或标准定理时说明实际适用条件”，且 S5 中 $k$ 为**任意域**。答卷直接援引 Voevodsky 层化定理声称 $F_{\mathrm{Zar}}$ 具唯一转移结构、保持同伦不变性且自动为 Nisnevich 层并与 Zariski 上同调一致，却**未说明经典定理对基域 $k$ 完美性的前提要求**。
- **逻辑依赖循环**：在 Voevodsky 的理论框架中，赋予 $F_{\mathrm{Zar}}$ 转移结构（及证明 $F_{\mathrm{Zar}}=F_{\mathrm{Nis}}$）恰恰依赖于先建立半局部比较同构 $F(S)\xrightarrow{\sim}F_{\mathrm{Zar}}(S)$（因为有限对应在局部概形上的原像只给出目标概形上的半局部概形），这正是 S5 要证明的结论。将其前置作为“基础定理”在逻辑上倒置（且答卷下文实际也未使用 2(3)）。
- 另注：答卷在 [L258](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L258) 与 [L302](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L302) 标注的 Mazza–Voevodsky–Weibel *Lectures on Motivic Cohomology*（MVW）编号 “Theorem 4.18/5.7”、“Lemma 4.22/5.7” 与该书章节不符（MVW 第 4、5 讲分别讨论权 1 动机上同调与 Milnor $K$-理论，半局部定理与层化定理位于第 22 讲）。

##### 问题 5.3（致命缺口与逻辑错误）：第 5 节核心几何步骤完全无证明，并遗漏关键情形
位置：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L297-L324)、[01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L1-L5)。

1. **核心收缩 / Mayer–Vietoris 引理无证明（第 5.1 节，[L302-L305](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L302-L305)）**：
   - 原题明确要求“完成全部构造、分类与性质的证明……建立它为同构的结论，并给出完整论证”。答卷仅以一句口号式描述（“利用曲线纤维化中有限对应对切触截面的移动技术，存在可缩开邻域 $U\subset U_0$……使得差截面可经同伦由交集推回两翼”）一笔带过，完全没有构造标准三元组、有限对应 $\mathbb{A}^1$-同伦及验证支撑有限满射性。
   - **记号与逻辑混淆**：将 $U_0,V$ 写作含 $\Sigma_1,\Sigma_2$ 的开邻域（未说明是 $S$ 的开子集），却写出 $0\to F(S)\to F(U)\oplus F(V)\to F(U\cap V)$——若 $U,V$ 为 $X$ 的开集，限制映射 $F(S)\to F(U)$ 甚至不存在。此外，“在有向滤过收缩下严格正合”模糊了“单个收缩覆盖 $(U,V)$ 上的阶段正合”（S2 所需前提）与“滤过余极限正合”（S6 专门指出二者不等价）的区别。
2. **未将 $\Sigma$ 约化为 $S$ 的闭点集（[L299](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L299)、[L314](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L314)）**：
   - S5 仅设 $\Sigma\subset|X|$ 为有限非空点集，未假定其中各点互不为特化关系。若存在 $x_i,x_j\in\Sigma$ 满足 $x_j\in\overline{\{x_i\}}$（即 $\mathfrak{p}_i\subsetneq\mathfrak{p}_j$），则**不存在**分开 $x_i$ 与 $x_j$ 的开邻域，直接按 $|\Sigma|=n$ 划分 $\Sigma=\Sigma'\sqcup\{x_n\}$ 进行归纳失效。必须先删去非极大素理想（该约化不改变 $M,S$ 及含 $\Sigma$ 的开邻域族），将 $\Sigma$ 化归为 $S$ 的闭点集。
3. **完全遗漏有限域 $k$（以及 0 维 / 不连通 $X$）的情形**：
   - 当 $k$ 为有限域时，在基域 $k$ 上未必存在避开 $\Sigma$ 的一般线性投影或 Artin 初等纤维化，需要（例如）利用有限可分扩张的有限对应转移恒等式 $\pi_*\circ\pi^*=[L:k]\cdot\mathrm{id}$，通过两个互素素数幂无限可分扩张 $k_{\ell_1},k_{\ell_2}$ 约化到无限域情形（或使用有限域上的几何表示引理）。答卷全程未提及基域有限性问题；也未对 $X$ 不连通或含 0 维连通分支（此时无相对 1 维曲线纤维化，需由加性直接处理）做分情况说明。
4. **第 5.2 节与第 5.3 节对 S2 与 S1 的援引不合法（[L306-L324](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L306-L324)、[01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L1-L3)）**：
   - 第 5.2 节直接将 S2 应用于 $H=F$，但如问题 5.1 所示，$F$ 未必是分离预层，且 $\eta_{S_1\times_S S_2}$ 的单射性与收缩正合性均未证明。（若走 S2 路线，须先独立证明半局部单射性 $F(S)\hookrightarrow F_{\mathrm{Zar}}(S)$，再转到分离商预层 $H=\operatorname{im}(\eta:F\to F_{\mathrm{Zar}})$ 上验证；或者直接在标准三元组上构造 $\mathbb{A}^1$-同伦抬升并用 $F(S_i)\hookrightarrow F(K(X))$ 检验，无需经过 $F(S_1\times_S S_2)$。）
   - 第 5.3 节归纳步中：右侧箭头 $\eta_{S'\times_S S_n}$ 的单射性仍依赖错误的“分离性”；底行正合列 $0\to F_{\mathrm{Zar}}(S)\to F_{\mathrm{Zar}}(S')\oplus F_{\mathrm{Zar}}(S_n)\to F_{\mathrm{Zar}}(S'\times_S S_n)$ 声称“由 S1 给出”，但 S1 给出的是按全部单个闭点 $S_1,\dots,S_n$ 展开的等化子，答卷既未定义 $F_{\mathrm{Zar}}(S'\times_S S_n)$，也未说明如何从 S1（或类似的二片余极限）得到 $(S',S_n)$ 的二片拼接正合列；顶行正合性同样无证明。

---

#### S6：极限正合与阶段正合
原题：[01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-001.txt#L69-L71)；答卷：[01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L8-L85)。

- **结论：正确且完整。**
- **第一问（[01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L10-L45)）**：判定否定正确。反例 $C_1^{(i)}=C_0^{(i)}=\mathbb{Z}$、$d_i=\times 2$、过渡链映射 $\phi_i=(\times 2,\times 2)$ 交换性无误；每阶段 $H_0=\mathbb{Z}/2\mathbb{Z}\neq 0$ 故均不正合，而余极限为 $\mathbb{Z}[1/2]\xrightarrow{\times 2}\mathbb{Z}[1/2]$，为群同构故严格正合。（即便将“二项复形”理解为两步微分的三项复形 $\mathbb{Z}\xrightarrow{\times 2}\mathbb{Z}\to 0$，该反例同样有效。）
- **第二问（[01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/MG-AR004/physical-1/session/work/.visible-input/MG-AR004/01-user-002.txt#L48-L85)）**：方法一（利用 $\mathrm{Ab}$ 中滤过余极限正合从而与同调交换）与方法二（直接元素追逐）均严格正确。（仅作轻微备注：答卷将滤过系统限定为有向偏序集 $I$；若按一般滤过范畴理解，只需将“$j\ge i$”改为“存在态射 $i\to j$”，论证完全平行，不影响正确性。）