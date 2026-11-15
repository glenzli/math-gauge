{}
# 答卷审阅报告

## 一、总体结论

对照原题 [original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md) 与待审答卷 [original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md)（材料说明见 [materials.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/materials.md)），答卷对各阶段的**命题真假判定与主结论方向全部正确**，其中 **S3、S4、S6** 的证明与反例严谨完整；但答卷在原题条件下**并非完全正确、亦不完整**：

1. **S5 存在实质性数学错误与核心证明缺失（最严重问题）**：答卷所立核心中间命题“稠密开浸入限制 $F(Y)\to F(W)$ 单射”及推论“$F$ 是 Zariski 分离预层”“$F(U)\to F_{\mathrm{Zar}}(U)$ 对任意开集 $U$ 单射”**全部是假命题**；这直接导致其对 S2 的援引违反分离预层前提，并使纤维积 $S_1\times_S S_2$（及归纳步 $S'\times_S S_n$）上的单射性失去依据。此外，S5 的几何移动/同伦与 Mayer–Vietoris 收缩仅以定性概述代替实质证明，漏去了任意有限集 $\Sigma$ 向半局部闭点集的约化、有限域扩张转移处理，以及援引 Voevodsky 层化定理时的**完美域（perfect field）**适用条件说明。
2. **S1 存在错误的普遍断言与局部跳步**：在说明“$S_i$ 不必是开子概形”时，断言“当 $\dim\mathcal{O}_{X,x_i}\ge 1$ 时 $\mathcal{O}_{X,x_i}$ 作为 $\mathcal{O}_{X,\Sigma}$-代数不是有限生成的，故不是开子概形”**为假命题**（一维半局部概形给出直接反例）；拓扑层面的高度 1 素理想计数亦存在漏条件与集合论推理跳步；等化子证明中未验证 $\{U_i\cap U_j\}$ 在 $S_i\times_S S_j$ 全体开邻域中的余终性。
3. **S2 存在有向性与余终性论证缺口**：对“分开 $x_1,x_2$”的定义漏掉了关键互斥条件 $x_1\notin V,\,x_2\notin U_0$，未明确开集所属底空间为 $S$（而非 $X$），且未证明使正合列成立的可缩覆盖子族为何构成有向系统及为何余终。

| 阶段 | 结论/判定 | 审阅评级 | 核心评价 |
| :--- | :--- | :--- | :--- |
| **S1** | 正确 | 部分有误/缺口 | 等化子主线成立但缺 $S_i\times_S S_j$ 邻域余终性验证；第 3 节含错误普遍断言与逻辑跳步 |
| **S2** | 正确 | 基本正确但有缺口 | 四引理图追逐严格正确；但漏写分离条件 $x_1\notin V, x_2\notin U_0$，未证正合子族的有向性与余终性 |
| **S3** | 正确 | 完全正确 | 偏序/范畴余终性与预层滤过余极限互逆同构证明完整严密 |
| **S4** | 正确（否定） | 完全正确 | 反例 $\mathbb{A}^1_k, \Sigma=\{0\}, W=D(t)$ 满足全部前提，论证无懈可击 |
| **S5** | 正确（成立） | 证明不成立/不完整 | 核心单射性与分离性引理为假命题，S2 前提不满足，核心几何引理无实质证明，漏完美域条件与闭点约化 |
| **S6** | 正确（否定+证明） | 完全正确 | 反例 $\mathbb{Z}\xrightarrow{\times 2}\mathbb{Z}$ 与两种余极限正合证明均严格无误 |

---

## 二、逐题审阅与可核查数学依据

### S1 层的半局部拼接
- **原题与答卷位置**：[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L7-L9)，[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L5-L44)。
- **问题 1（第 3 节概形层面的普遍断言为假命题）**：
  - **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L43) 断言：“当 $\dim\mathcal{O}_{X,x_i}\ge 1$ 时，局部环 $\mathcal{O}_{X,x_i}$ 作为 $\mathcal{O}_{X,\Sigma}$-代数不是有限生成的，故态射 $S_i\to S$ 虽然是平坦单射，但不是有限型的，因而不是开子概形。”
  - **数学反例**：
    1. 即使在 $n\ge 2$ 且连通的情形，取一维光滑仿射概形 $X=\mathbb{A}^1_k=\operatorname{Spec}k[t]$，闭点集 $\Sigma=\{x_1,x_2\}$ 对应 $\mathfrak{p}_1=(t),\,\mathfrak{p}_2=(t-1)$。此时 $\dim\mathcal{O}_{X,x_1}=\dim k[t]_{(t)}=1\ge 1$。然而 $\mathcal{O}_{X,\Sigma}=M^{-1}k[t]$（$M=k[t]\setminus((t)\cup(t-1))$）是仅有两个极大理想 $(t),(t-1)$ 的半局部主理想整环。任取 $h\in k[t]\setminus(t)$，可写成 $h=(t-1)^r g$（其中 $t\nmid g,\,t-1\nmid g$），故 $g\in M$ 在 $\mathcal{O}_{X,\Sigma}$ 中已可逆。于是仅局部化单个元素 $t-1$ 即有
       $$\mathcal{O}_{X,\Sigma}\left[\frac{1}{t-1}\right]=k[t]_{(t)}=\mathcal{O}_{X,x_1}.$$
       因此 $\mathcal{O}_{X,x_1}$ 作为 $\mathcal{O}_{X,\Sigma}$-代数是**有限生成的**（单元素生成），且 $S_1=D(t-1)=S\setminus\{x_2\}\hookrightarrow S$ **恰是主开浸入（开子概形）**。
    2. 此外，当 $n=1$ 时 $S_1=S$；或当 $X$ 不连通且 $x_i$ 独占一个连通分支时，$S_i$ 也是 $S$ 的既开又闭子概形。
- **问题 2（第 3 节拓扑层面的漏条件与推理跳步）**：
  - **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L42) 声称：当 $\dim\mathcal{O}_{X,x_j}\ge 2$（$j\neq i$）时，“$\mathfrak{p}_j$ 中存在无穷多个高度 1 素理想，非零元 $f$ 仅包含于其中有限多个；因而必存在高度 1 素理想 $\mathfrak{q}\subset\mathfrak{p}_j$ 使得 $f\notin\mathfrak{q}$ 且 $\mathfrak{q}\not\subset\mathfrak{p}_i$。”
  - **数学依据**：
    1. **漏连通分支前提**：原题未设 $X$ 连通。若 $x_i,x_j$ 位于 $\operatorname{Spec}A=\operatorname{Spec}A_1\times\operatorname{Spec}A_2$ 的不同连通分支，取 $f=(1,0)\notin\mathfrak{p}_i$，则 $f\neq 0$，但 $f$ 在 $\operatorname{Spec}A_2$ 上恒为零，从而包含于 $\mathfrak{p}_j$ 内**全部（无穷多个）**高度 1 素理想中（此时 $D(f)=S_i$ 确实是开的）。
    2. **集合论跳步**：即便 $x_i,x_j$ 在同一不可约分支上，同时包含于 $\mathfrak{p}_i\cap\mathfrak{p}_j$ 的高度 1 素理想本身也可以有**无穷多个**（例如 $\mathbb{A}^2_{\mathbb{C}}$ 中过 $x_1=(0,0),\,x_2=(1,0)$ 的抛物线族 $y-cx(x-1)=0,\,c\in\mathbb{C}$）。仅由“$\{\operatorname{ht}\mathfrak{q}=1:\mathfrak{q}\subset\mathfrak{p}_j\}$ 无穷”和“含 $f$ 者有限”只能推出存在 $\mathfrak{q}\subset\mathfrak{p}_j$ 使 $f\notin\mathfrak{q}$，**不能直接推出 $\mathfrak{q}\not\subset\mathfrak{p}_i$**。需补充素避开引理与 Krull 主理想定理证明 $\{\operatorname{ht}\mathfrak{q}=1:\mathfrak{q}\subset\mathfrak{p}_j,\,\mathfrak{q}\not\subset\mathfrak{p}_i\}$ 无穷，或直接给出具体反例（如 $X=\mathbb{A}^2_k,\,x_1=(0,0),\,x_2=(1,0)$，一族两两互素不可约元 $y-(x-1)^m\in\mathfrak{p}_2\setminus\mathfrak{p}_1$，$m\ge 1$）。
  - **影响**：原题仅要求说明“不必是开子概形”，给出一个具体高维反例即可；答卷试图作一般刻画却引入了假命题与推理缺口。
- **问题 3（第 1–2 节漏验 $S_i\times_S S_j$ 开邻域余终性及对角线记号混用）**：
  - **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L14) 与 [#L30-L33](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L30-L33)。
  - **数学依据**：按题设“值以开邻域滤过余极限延拓”，$G(S_i\times_S S_j)$ 应为 $\varinjlim_{\operatorname{im}(S_i\times_S S_j)\subset W\subset X\,\text{开}}G(W)$。答卷直接将其定义为 $\varinjlim_{x_i\in U_i,x_j\in U_j}G(U_i\cap U_j)$，未说明为何任意包含 $\operatorname{im}(S_i\times_S S_j)$ 的开集 $W$ 必包含某个 $U_i\cap U_j$（此性质并非一般拓扑空间恒成立，需用到仿射局部化 $A_{\mathfrak{p}_i}\otimes_{M^{-1}A}A_{\mathfrak{p}_j}\cong ((A\setminus\mathfrak{p}_i)(A\setminus\mathfrak{p}_j))^{-1}A=\varinjlim_{f\notin\mathfrak{p}_i,g\notin\mathfrak{p}_j}A_{fg}$ 及素理想性质 $fg\in\mathfrak{q}\Rightarrow f\in\mathfrak{q}\text{ 或 }g\in\mathfrak{q}$）。此外第 33 行在 $i=j$ 时写作 $\varinjlim_{x_i\in U_i,x_j\in U_j}G(U_i\cap U_j)$ 复用了约束变量名 $U_i$（由于局部化 $S_i\to S$ 是单态射，$S_i\times_S S_i\cong S_i$，实质结果仍为 $G(S_i)$，不影响等化子结论）。

---

### S2 分离预层的比较图
- **原题与答卷位置**：[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L11-L13)，[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L47-L96)。
- **正确部分**：第 1 节将 $n=2$ 的四分量积等化子简化为差映射核正合列（[#L49-L57](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L49-L57)），以及第 3 节的四引理图追逐（[#L68-L95](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L68-L95)）严格正确。
- **问题（第 2 节滤过余极限系统的构造缺口）**：
  - **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L59-L66)。
  - **数学依据与影响**：
    1. **漏掉“分开 $x_1,x_2$”的互斥条件**：第 59 行将“分开 $x_1,x_2$ 的二开覆盖”仅写为“$x_1\in U_0, x_2\in V$ 且覆盖 $S$”，遗漏了 **$x_1\notin V$ 且 $x_2\notin U_0$**。若允许 $x_1\in V$（例如 $V=S$），则 $(U_0,V)$ 缩为 $(U,V)=(\emptyset,S)$ 仍覆盖 $S$，导致 $x_1\notin U$，根本无法迫使 $U$ 收缩为 $x_1$ 的邻域。正是 $x_1\notin V,\,x_2\notin U_0$ 与 $U\cup V=S$ 共同强制 $x_1\in U\setminus V$。
    2. **未区分 $S$ 的开子概形与 $X$ 的开子概形**：序列 $0\to H(S)\to H(U)\oplus H(V)\to H(U\cap V)$ 中存在限制映射 $H(S)\to H(U)\oplus H(V)$，要求 $U,V$ 是 **$S$ 的开子概形**（若 $U,V$ 是 $X$ 的开集且 $S\subsetneq U\cup V$，则限制方向相反，不存在 $H(S)\to H(U)$）。第 64 行写“第一项为常值或全覆盖余极限 $H(S)$”反映出该概念含混。
    3. **未证明正合覆盖子族 $\mathcal{E}$ 的有向性与余终性**：两个使序列正合的覆盖 $(U_1,V_1),(U_2,V_2)\in\mathcal{E}$ 取交 $(U_1\cap U_2,V_1\cap V_2)$ 后，不再自动保持正合。需先说明：因 $x_1\neq x_2$ 是 $S$ 的闭点且 $|S|=|S_1|\cup|S_2|$，全体分开 $x_1,x_2$ 的二开覆盖族 $\mathcal{C}=\{(U_0,V)\text{ 为 }S\text{ 的开覆盖}\mid x_1\in U_0\setminus V,\,x_2\in V\setminus U_0\}$ 对逐分量交构成有向集；再由题设“对任意 $c\in\mathcal{C}$ 存在 $e\in\mathcal{E}$ 使 $e\ge c$”推出 $\mathcal{E}$ 自身为有向集且在 $\mathcal{C}$ 中余终；最后对任意 $X$ 中开邻域 $\widetilde{U}_1\ni x_1,\,\widetilde{U}_2\ni x_2$，取 $U_0=(\widetilde{U}_1\cap S)\setminus\{x_2\},\,V=(\widetilde{U}_2\cap S)\setminus\{x_1\}\in\mathcal{C}$（注意 $|S_1|\cap|S_2|$ 不含闭点 $x_1,x_2$，故仍含于 $U_0\cap V$），方可推出三项余极限分别为 $H(S_1),\,H(S_2),\,H(S_1\times_S S_2)$。

---

### S3 含指定点的开集
- **原题与答卷位置**：[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L15-L17)，[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L99-L132)。
- **审阅意见**：**完全正确且完整**。支配性（$U=V\cap W$）、有向相容性以及利用泛性质构造互逆同态 $\phi,\psi$ 的验证均准确无误。

---

### S4 稠密开与邻域系统
- **原题与答卷位置**：[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L19-L21)，[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L135-L162)。
- **审阅意见**：**完全正确且完整**。反例 $X=\mathbb{A}^1_k=\operatorname{Spec}k[t]$、$\Sigma=\{0\}$、$W=D(t)$ 严格满足“域 $k$ 上光滑、积分、仿射概形，有限非空点集，稠密开子集”的全部前提，且导出 $\mathcal{I}_W=\emptyset$ 而 $\mathcal{I}\neq\emptyset$，充要条件补充亦准确。

---

### S5 整体对象与全部恢复目标
- **原题与答卷位置**：[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L23-L50)，[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L165-L252)。
- **总体判定**：目标结论“$\eta_S:F(S)\to F_{\mathrm{Zar}}(S)$ 是同构”在任意域 $k$ 上确实成立（Voevodsky, *Cohomological Theory of Presheaves with Transfers*, Prop. 3.1.8），但**答卷给出的证明存在多处严重错误与实质性空白，不能成立**。

#### 错误 1：第 3 节核心定理与两条推论全为假命题（可核查反例）
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L191-L206) 给出：
  1. **所谓“定理（稠密开浸入单射性）”**（[#L191-L194](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L191-L194)）：对连通光滑整概形 $Y\in\mathrm{Sm}/k$ 与稠密开子集 $W\subset Y$，限制 $F(Y)\to F(W)$ 是单射；
  2. **单射性推论 1**（[#L202](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L202)）：$F$ 是 Zariski 分离预层；
  3. **单射性推论 2**（[#L203](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L203)）：典范态射 $F(U)\to F_{\mathrm{Zar}}(U)$ 对任一开子集 $U$ 均是单射。
- **初等自包含反例（对任意域 $k$ 成立）**：
  定义 $F:\mathrm{Cor}_k^{\mathrm{op}}\to\mathrm{Ab}$ 为
  $$F(Y):=\operatorname{coker}\Big(\mathrm{Cor}_k(Y\times_k\mathbb{A}^1_k,\,\mathbb{P}^1_k)\xrightarrow{i_0^*-i_1^*}\mathrm{Cor}_k(Y,\,\mathbb{P}^1_k)\Big).$$
  - **检验题设前提**：$\mathrm{Cor}_k(-,\mathbb{P}^1_k)$ 是加性反变函子，故其商函子 $F$ 也是加性反变函子；利用乘法态射 $\mu:\mathbb{A}^1_k\times_k\mathbb{A}^1_k\to\mathbb{A}^1_k,\,(s,t)\mapsto st$ 构造同伦，对任意 $\alpha\in\mathrm{Cor}_k(Y\times_k\mathbb{A}^1_k,\mathbb{P}^1_k)$，$(\mathrm{id}_Y\times\mu)^*(\alpha)$ 连接 $p^*i_0^*(\alpha)$ 与 $\alpha$，故 $p^*:F(Y)\to F(Y\times_k\mathbb{A}^1_k)$ 以 $i_0^*$ 为逆，是同构。$F$ 满足 S5 的全部假设。
  - **反驳上述三项断言**：取连通光滑整概形 $Y=\mathbb{P}^1_k$（齐次坐标 $[X_0:X_1]$），考察 $\xi:=[\Delta]-[C_0]\in F(\mathbb{P}^1_k)$，其中 $\Delta=\Gamma_{\mathrm{id}_{\mathbb{P}^1_k}}$（由 $X_0Y_1-X_1Y_0=0$ 定义，双次数 $(1,1)$），$C_0=\mathbb{P}^1_k\times\{[0:1]\}$（由 $Y_0=0$ 定义，双次数 $(0,1)$）。
    1. **$\xi\neq 0\in F(\mathbb{P}^1_k)$**：$\mathrm{Cor}_k(\mathbb{P}^1_k\times_k\mathbb{A}^1_k,\mathbb{P}^1_k)$ 的任意整生成元 $H=V(P)$ 由 $k[t][X_0,X_1,Y_0,Y_1]$ 中双齐次多项式 $P$ 定义；因 $H$ 在 $\mathbb{P}^1_k\times_k\mathbb{A}^1_k$ 上有限，$P|_{t=0}$ 与 $P|_{t=1}$ 均非零且具有相同的 $(X,Y)$-双次数 $(d_1,d_2)$，从而 $i_0^*(H)-i_1^*(H)$ 在 $\operatorname{Pic}(\mathbb{P}^1_k\times_k\mathbb{P}^1_k)\cong\mathbb{Z}\oplus\mathbb{Z}$ 中的双次数恒为 $(0,0)$。而 $\xi$ 的双次数为 $(1,1)-(0,1)=(1,0)\neq(0,0)$，故 $\xi\neq 0$。
    2. **在稠密开集上限制为零（反驳“定理”）**：取稠密开集 $W_1=\mathbb{P}^1_k\setminus\{[1:0]\}=\operatorname{Spec}k[x]$（$[x:1]$），态射 $h_1:W_1\times_k\mathbb{A}^1_k\to\mathbb{P}^1_k,\,(x,t)\mapsto[tx:1]$ 在 $t=1,0$ 处分别为 $\Delta|_{W_1}$ 与 $C_0|_{W_1}$，故 $\xi|_{W_1}=0\in F(W_1)$。因此 $F(\mathbb{P}^1_k)\to F(W_1)$ **不是单射**。
    3. **非分离性与层化映射非单射（反驳推论 1、2）**：再取开集 $W_2=\mathbb{P}^1_k\setminus\{[1:1]\}=\operatorname{Spec}k[z]$（其中 $z=\frac{X_0}{X_0-X_1}$，点坐标为 $[z:z-1]$），态射 $h_2:W_2\times_k\mathbb{A}^1_k\to\mathbb{P}^1_k,\,(z,t)\mapsto[tz:tz-1]$（因 $tz-(tz-1)=1\neq 0$ 处处良定）在 $t=1,0$ 处分别为 $\Delta|_{W_2}$ 与 $C_0|_{W_2}$，故 $\xi|_{W_2}=0\in F(W_2)$。由于 $\mathbb{P}^1_k=W_1\cup W_2$ 是二开覆盖，$\xi\neq 0$ 却在 $W_1,W_2$ 上均为零，故 **$F$ 不是 Zariski 分离预层**，且对 $X=U=\mathbb{P}^1_k$ 有 $\eta_U(\xi)=0$，**$F(U)\to F_{\mathrm{Zar}}(U)$ 不是单射**。
  - *(注：即使额外要求 $Y$ 仿射，取 $F(Y)=\mathrm{CH}^1(Y)\cong\operatorname{Pic}(Y)$ 及 $k=\mathbb{C}$ 上椭圆曲线去点仿射概形 $Y=E\setminus\{\infty\}$，非零阶点 $P\in E(\mathbb{C})\setminus\{\infty\}$ 与 $W=E\setminus\{\infty,P\}$，同样给出 $F(Y)\to F(W)$ 非单射、$Y$ 上 $F$ 非分离且 $F_{\mathrm{Zar}}=0$。)*
- **错因剖析与下游影响**：
  1. 在 [#L197-L200](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L197-L200) 中，标准三元组 $(p:C\to B,Z\subset C\subset\bar{C})$ 仅在有限点集的**局部开邻域 $C\subset Y$** 上存在，$\Phi\in\mathrm{Cor}_k(C,W)$ 仅能推出 $s|_C=\Phi^*(s|_W)=0\in F(C)$，**不能推出全局 $s=0\in F(Y)$**（若试图由局部处处为零推出全局为零，又会循环依赖待证的“$F$ 分离”）。正确的 Voevodsky 单射性定理仅对**半局部概形** $S$ 给出 $F(S)\hookrightarrow\prod_{\eta\in S^{(0)}}F(\eta)$ 单射，进而 $\eta_S:F(S)\to F_{\mathrm{Zar}}(S)$ 单射。
  2. **破坏对 S2 的援引与纤维积项单射性**（[#L204-L206](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L204-L206), [#L233](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L233), [#L247](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L247)）：由于 $F$ 未必是分离预层，**直接取 $H=F$ 违反 S2 的显式前提“设 $H$ 为分离阿贝尔群预层”**；同时当 $\dim X\ge 2$ 时，$S_1\times_S S_2$ 含无穷多个极大理想（对应同时含于 $\mathfrak{p}_1\cap\mathfrak{p}_2$ 的无穷多个高度 1 素理想），**不是半局部概形**，因此即使用正确的半局部单射性定理也无法直接得出 $\eta_{S_1\times_S S_2}$ 单射（需先过渡到分离商预层 $H=\operatorname{im}(F\to F_{\mathrm{Zar}})$ 并为其建立收缩同调消亡，或直接对 $F_{\mathrm{Zar}}(S)$ 的局部代表元做粘贴而不经过 $S_1\times_S S_2$）。

#### 错误 2：核心几何引理缺失实质证明，且混淆阶段正合与余极限同调消亡
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L196-L200) 与 [#L226-L229](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L226-L229)。
- **数学依据与影响**：
  1. **证明不完整**：原题明确要求“完成全部构造、分类与性质的证明”“给出完整论证”（[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L25), [#L50](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L50)）。答卷对相对曲线上有限对应的构造与 Mayer–Vietoris 收缩均仅用一句定性描述带过，未给出任何实质构造；且当基域 $k$ 为**有限域**时，标准三元组未必在 $k$ 上直接存在，必须借助互素次数的有限可分扩张 $L_1,L_2/k$ 作有限平展转移（范数回推），答卷完全未涉及。
  2. **阶段正合 vs 后阶段消亡（漏掉了与 S6 的核心关联）**：第 227–228 行在 $\operatorname{Spec}A$ 中取开集 $U_0,V$ 却写下 $0\to F(S)\to F(U)\oplus F(V)\to F(U\cap V)$（类型不匹配：若 $U,V\subset\operatorname{Spec}A$ 则无映射 $F(S)\to F(U)$）；且在 Voevodsky 实际证明（Lemma 3.1.7）中，给定包含 $\Sigma$ 的开覆盖 $X'=U_0\cup V$，几何同伦给出的是存在更小邻域 $X''\supset\Sigma$ 使 $\ker(F(U_0)\oplus F(V)\to F(U_0\cap V))$ 限制到 $(U_0\cap X'',V\cap X'')$ 后落入 $F(X'')$ 的像——即**每个阶段的同调类在更后阶段消亡**（这正是原题设计 **S6 第二问**的原因），而非单阶段正合。

#### 错误 3：漏去将一般有限集 $\Sigma$ 约化为半局部闭点集，且归纳步援引 S1 不严密
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L223) 与 [#L237-L249](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L237-L249)。
- **数学依据与影响**：
  1. 原题 S5 仅设“$\Sigma\subset |X|$ 是有限非空点集”（[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L39)），并未假设 $\Sigma$ 中各点互不特化。例如 $X=\mathbb{A}^1_k$，$\Sigma=\{\eta,0\}$（泛点与原点，$|\Sigma|=2$），此时任何含 $0$ 的开集必含 $\eta$，**根本不存在分开 $\eta$ 与 $0$ 的二开覆盖**，实际闭点数仅为 $1$。证明前必须先取 $\{\mathfrak{p}_x:x\in\Sigma\}$ 中关于包含关系的极大元对应点集 $\Sigma_{\max}$（即 $S$ 的闭点集），说明 $M=A\setminus\bigcup_{x\in\Sigma_{\max}}\mathfrak{p}_x$ 且含 $\Sigma$ 的开集与含 $\Sigma_{\max}$ 的开集完全一致，再对 $|\Sigma_{\max}|$ 归纳。
  2. 第 248 行对 $S'$（$n-1$ 个点的半局部化）与 $S_n$ 声称“底行由层的拼接 S1 给出”，而 S1 仅证明了单点局部化族 $\{S_i\}_{i=1}^n$ 的等化子，应用于半局部化 $S'$ 与 $S_n$ 的二元拼接需补充对指标集 $\mathcal{I}_{\Sigma'}\times\mathcal{I}_{x_n}$ 的适配说明。

#### 错误 4：援引 Voevodsky 层化定理漏掉完美域条件且定理编号失实
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L181-L185)。
- **数学依据与影响**：原题第 3 行明确要求“援引前项或标准定理时说明实际适用条件”，且 S5 仅设“$k$ 为域”（允许非完美域）。但答卷无条件断言 $F_{\mathrm{Zar}}$ 保持 $\mathbb{A}^1$-同伦不变性、自动为 Nisnevich 层且两者上同调一致——这些结论（Voevodsky 2000, Theorem 3.1.12；MVW Lectures 13 & 22）**均以 $k$ 为完美域为实质前提**（非完美域上存在反例），且在逻辑顺序上它们是先证完 $\eta_S$ 同构后才推出的后续定理（前置援引存在循环论证之嫌）；此外所引 MVW “Theorem 4.18/5.7”（及第 226 行 “Lemma 4.22 / 5.7”）与原书实际章节编号（标准三元组与层化定理位于第 11、13、22 讲）不符。

---

### S6 极限正合与阶段正合
- **原题与答卷位置**：[original-task.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-task.md#L52-L54)，[original-answer.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane2-20261114-v6/attempts/MG-AR004/physical-1/session/work/original-answer.md#L255-L332)。
- **审阅意见**：**完全正确且完整**。
  - 第一问以 $C_1^{(i)}=\mathbb{Z}\xrightarrow{\times 2}\mathbb{Z}=C_0^{(i)}$ 及链映射 $(\times 2,\times 2)$ 构造滤过序列，各阶段 $H_0=\mathbb{Z}/2\mathbb{Z}\neq 0$ 均不正合，而余极限 $\mathbb{Z}[1/2]\xrightarrow{\times 2}\mathbb{Z}[1/2]$ 为同构（正合），反例简洁严密。
  - 第二问分别通过 $\mathrm{Ab}$ 中滤过余极限的正合性（同调函子与滤过余极限交换）与直接元素追逐完成了严格证明。
