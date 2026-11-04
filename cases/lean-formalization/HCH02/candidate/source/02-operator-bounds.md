## #h-5d30f7f93769bbd7 算子界

在扩展规范空间中，输入与输出分别由多个分量伪度量读取；对于同一算子，一个输出分量距离可以受到多个输入分量距离的共同约束。常规的标量分析，例如相对于一对给定距离使用标量 Lipschitz 常数，不能同时保留全部跨分量关系。为记录这些关系，本章分别引入 Lipschitz 上界矩阵与 co-Lipschitz 下界矩阵，并建立它们在有限复合、局部限制和分量通道中的基本运算法则。

### #h-af85899693cc8750 矩阵界与有限复合

> **约定（证书）**：全文称一组显式数据为某个上界、下界、零化、容量或路径结论的**证书**，若这些数据满足某个已证明命题的全部相关前提，并且代入该命题后推出对应结论。证书不是额外假设模式，也不是对真实取值的断言；它只记录可被核验的参数、矩阵、点对、路径域、覆盖或分离数据。若没有给出相应证书，则不得从同名结论的形式、谱半径条件或路径编号变化推出该结论。

#### Lipschitz 上界矩阵

**定义（Lipschitz 矩阵）**：对 $\phi \in \mathcal{X}_{\mathrm{op}}$，称非负矩阵 $\mathbf{L} = (L_{i \to j})_{i, j \in I}$（$L_{i \to j} \in \bar{\mathbb{R}}_+$）为 $\phi$ 的一个**合法 Lipschitz 矩阵**，若对所有 $x, y \in \mathrm{dom}(\phi)$ 和所有 $j \in I$：

$$d_j(\phi(x), \phi(y)) \;\leq\; \sum_{i \in I} L_{i \to j} \cdot d_i(x, y)$$

> **约定（广义 Lip）**：Lip 矩阵条目取值于 $\bar{\mathbb{R}}_+$（与 @h-b4babd684de7c112 一致），即允许 $L_{i \to j} = +\infty$。需要有限性时显式标注。求和中的 $\bar{\mathbb{R}}_+$ 算术遵循 @h-b4babd684de7c112 约定（特别地 $+\infty \cdot 0 = 0$）。即若某条目 $L_{i \to j} = +\infty$ 但 $d_i(x, y) = 0$，则该项对右端求和的贡献为零；这只说明该输入分量在该项中不贡献 $d_j$-输出上界，不排除其他输入分量或其他求和项给出非零贡献。当 $L_{i \to j} = +\infty$ 且 $d_i(x, y) > 0$ 时，该项为 $+\infty$，不等式平凡成立。

记 $\phi$ 的全体合法 Lip 矩阵之集为 $\mathscr{L}(\phi)$。本章始终把 $\mathscr L(\phi)$ 作为证书族使用，不预设其中存在同时实现所有条目下确界的指定矩阵。

> **注 #h-c4369c63c86cbacf（单分量情形下的标量 Lip 界）**：当 $|I|=1$ 且 $I=\{i\}$ 时，Lip 矩阵条件退化为单个标量不等式
>
> $$d_i(\phi(x),\phi(y))\le L_{i\to i}d_i(x,y)\qquad(x,y\in\mathrm{dom}(\phi)).$$
>
> **证明**：定义中的求和指标集只有一个元素 $i$，矩阵仅含条目 $L_{i\to i}$，代入 @h-af85899693cc8750 的 Lip 矩阵不等式即得。

**定义（子集受限 Lip 矩阵）**：对子集 $U \subseteq \mathrm{dom}(\phi)$，如果在 $U$ 上对任意 $x, y \in U$ 均满足上述距离放缩不等式，则称 $\mathbf{L}$ 为 $\phi$ 在 $U$ 上的一个受限 Lip 矩阵，记其合法矩阵集为 $\mathscr{L}(\phi)\big|_U$。由定义有 $\mathscr{L}(\phi) \subseteq \mathscr{L}(\phi)\big|_U$；评估域缩小时，可行证书族只会扩大，每个原有证书仍然合法。若另行逐条目取下确界，则该下确界只能不增。

**命题 #h-193cebcc1a7f9259（Lip 矩阵复合律）**：对于复合算子 $\phi_2 \circ \phi_1$，选定起始定义域的局部子集 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，记像集 $U_2 = \phi_1(U_1)$（由复合定义直接保证 $U_2 \subseteq \mathrm{dom}(\phi_2)$）。若 $\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_{U_1}$ 且 $\mathbf{L}_2 \in \mathscr{L}(\phi_2)\big|_{U_2}$，则 $\mathbf{L}_2 \cdot \mathbf{L}_1 \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。

**证明**：对任意 $x, y \in U_1$，复合映射不仅合法，且有像点

$$
\phi_1(x),\phi_1(y)\in U_2.
$$

对于任意 $j \in I$ 展开。

根据 $\mathbf{L}_2 \in \mathscr{L}(\phi_2)\big|_{U_2}$，代入像点对 $(\phi_1(x), \phi_1(y))$：

$$
d_j((\phi_2 \circ \phi_1)(x),(\phi_2 \circ \phi_1)(y))
\leq
\sum_{k \in I} L^{(2)}_{k \to j}\,d_k(\phi_1(x),\phi_1(y)).
$$

由于 $\mathbf{L}_1 \in \mathscr{L}(\phi_1)\big|_{U_1}$，对一切 $k \in I$ 均有

$$
d_k(\phi_1(x),\phi_1(y))
\leq
\sum_{i \in I} L^{(1)}_{i \to k}\,d_i(x,y).
$$

因 $L^{(2)}_{k \to j} \geq 0$，同乘 $L^{(2)}_{k \to j}$ 并对 $k \in I$ 求和，不等号方向不变（由 $0 \cdot (+\infty) = 0$ 约定保证代数一致性）：

$$
\leq
\sum_{k \in I} L^{(2)}_{k \to j}
\left(\sum_{i \in I} L^{(1)}_{i \to k}\,d_i(x,y)\right).
$$

利用 $\bar{\mathbb{R}}_+$ 对有限和的加法交换律与乘法分配律，交换求和次序：

$$
=
\sum_{i \in I}
\left(\sum_{k \in I} L^{(2)}_{k \to j}L^{(1)}_{i \to k}\right)d_i(x,y).
$$

内部加和即为代数矩阵乘法元素 $(\mathbf{L}_2 \cdot \mathbf{L}_1)_{i \to j}$ 的定义，故 $\mathbf{L}_2 \cdot \mathbf{L}_1 \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。$\square$

#### co-Lipschitz 下界矩阵

**定义（子集受限 co-Lipschitz 矩阵）**：对 $\phi \in \mathcal{X}_{\mathrm{op}}$ 与给定的非空子集 $U \subseteq \mathrm{dom}(\phi)$，称非负矩阵 $\mathbf{K} = (K_{i \to j})_{i, j \in I}$（$K_{i \to j} \in \bar{\mathbb{R}}_+$）为 $\phi$ 在 $U$ 上的一个**合法受限 co-Lipschitz 矩阵**（后续可简称为 co-Lip 矩阵），若对所有 $x, y \in U$ 和所有 $j \in I$：

$$d_j(\phi(x), \phi(y)) \;\geq\; \sum_{i \in I} K_{i \to j} \cdot d_i(x, y)$$

记 $\phi$ 在 $U$ 上的全体合法 co-Lip 矩阵之集为 $\mathscr{K}(\phi)\big|_U$。凡出现 $\mathscr{K}(\phi)\big|_U$，均包含这里的非空性条件 $U\neq\emptyset$。本章把该集合视为下界证书族，不预设其中存在同时实现所有条目上确界的指定矩阵。

> **注 #h-88784dcbfff0ea66（co-Lip 通道退化的点对判据）**：若存在 $x,y\in\mathrm{dom}(\phi)$ 使
>
> $$d_j(\phi(x),\phi(y))=0,\qquad d_i(x,y)>0,$$
>
> 则任一全域 co-Lip 矩阵 $\mathbf K\in\mathscr K(\phi)\big|_{\mathrm{dom}(\phi)}$ 必满足 $K_{i\to j}=0$。
>
> **证明**：把该点对代入 co-Lip 不等式，得到
>
> $$0=d_j(\phi(x),\phi(y))\ge \sum_{k\in I}K_{k\to j}d_k(x,y)\ge K_{i\to j}d_i(x,y).$$
>
> 由于 $K_{i\to j}\ge0$ 且 $d_i(x,y)>0$，只能有 $K_{i\to j}=0$。因此引入受限域 $U$ 的作用，是排除使特定 co-Lip 通道平凡化的点对，在非退化局部区域中记录非零下界。


**命题 #h-0f256e6f1d38a612（co-Lip 矩阵复合律）**：对于复合算子 $\phi_2 \circ \phi_1$，选定起始定义域的局部子集 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，记像集 $U_2 = \phi_1(U_1)$（由复合定义直接保证 $U_2 \subseteq \mathrm{dom}(\phi_2)$）。若 $\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_{U_1}$ 且 $\mathbf{K}_2 \in \mathscr{K}(\phi_2)\big|_{U_2}$，则 $\mathbf{K}_2 \cdot \mathbf{K}_1 \in \mathscr{K}(\phi_2 \circ \phi_1)\big|_{U_1}$。

**证明**：对任意 $x, y \in U_1$，复合映射不仅合法，且有像点

$$
\phi_1(x),\phi_1(y)\in U_2.
$$

对于任意 $j \in I$ 展开。

根据 $\mathbf{K}_2 \in \mathscr{K}(\phi_2)\big|_{U_2}$，代入像点对 $(\phi_1(x), \phi_1(y))$：

$$
d_j((\phi_2 \circ \phi_1)(x),(\phi_2 \circ \phi_1)(y))
\geq
\sum_{k \in I} K^{(2)}_{k \to j}\,d_k(\phi_1(x),\phi_1(y)).
$$

由于 $\mathbf{K}_1 \in \mathscr{K}(\phi_1)\big|_{U_1}$，对一切 $k \in I$ 均有

$$
d_k(\phi_1(x),\phi_1(y))
\geq
\sum_{i \in I} K^{(1)}_{i \to k}\,d_i(x,y).
$$

因 $K^{(2)}_{k \to j} \geq 0$，同乘 $K^{(2)}_{k \to j}$ 并对 $k \in I$ 求和，不等号方向不变（由 $0 \cdot (+\infty) = 0$ 约定保证代数一致性）：

$$
\geq
\sum_{k \in I} K^{(2)}_{k \to j}
\left(\sum_{i \in I} K^{(1)}_{i \to k}\,d_i(x,y)\right).
$$

利用 $\bar{\mathbb{R}}_+$ 对有限和的加法交换律与乘法分配律，交换求和次序：

$$
=
\sum_{i \in I}
\left(\sum_{k \in I} K^{(2)}_{k \to j}K^{(1)}_{i \to k}\right)d_i(x,y).
$$

内部加和即为代数矩阵乘法元素 $(\mathbf{K}_2 \cdot \mathbf{K}_1)_{i \to j}$ 的定义，故 $\mathbf{K}_2 \cdot \mathbf{K}_1 \in \mathscr{K}(\phi_2 \circ \phi_1)\big|_{U_1}$。$\square$



**命题 #h-b959b42f25710105（两个算子的点对像距扰动界）**：设 $\phi_1,\phi_2\in\mathcal X_{\mathrm{op}}$，$U\subseteq\mathrm{dom}(\phi_1,\phi_2)$。若存在 $\boldsymbol\delta=(\delta_j)_{j\in I}\in\bar{\mathbb R}_+^I$，使得对任意 $z\in U$ 与 $j\in I$，

$$
d_j(\phi_1(z),\phi_2(z))\le \delta_j,
$$

则对任意 $x,y\in U$ 与 $j\in I$：

**(i)（点对像距双向扰动）**

$$
d_j(\phi_2(x),\phi_2(y))
\le
d_j(\phi_1(x),\phi_1(y))+2\delta_j,
$$

且交换 $\phi_1,\phi_2$ 得

$$
d_j(\phi_1(x),\phi_1(y))
\le
d_j(\phi_2(x),\phi_2(y))+2\delta_j.
$$

**(ii)（Lip 上界桥接）** 若 $\mathbf L_1\in\mathscr L(\phi_1)\big|_U$，则

$$
d_j(\phi_2(x),\phi_2(y))
\le
\sum_{i\in I}[\mathbf L_1]_{i\to j}d_i(x,y)+2\delta_j.
$$

**(iii)（co-Lip 下界桥接）** 若 $\mathbf K_1\in\mathscr K(\phi_1)\big|_U$，则

$$
\sum_{i\in I}[\mathbf K_1]_{i\to j}d_i(x,y)
\le
d_j(\phi_2(x),\phi_2(y))+2\delta_j.
$$

交换 $\phi_1,\phi_2$ 后，可得到 $\phi_2$ 的 Lip 或 co-Lip 证书对 $\phi_1$ 的对应桥接结论。

**证明**：由伪度量对称性，扰动前提也给出

$$
d_j(\phi_2(z),\phi_1(z))\le \delta_j
\qquad(z\in U,\ j\in I).
$$

对 $x,y\in U$，三角不等式给出

$$
d_j(\phi_2(x),\phi_2(y))
\le
d_j(\phi_2(x),\phi_1(x))
+d_j(\phi_1(x),\phi_1(y))
+d_j(\phi_1(y),\phi_2(y)).
$$

首尾两项均由扰动前提控制，故得到 (i) 的第一式；交换 $\phi_1,\phi_2$ 得第二式。

若 $\mathbf L_1\in\mathscr L(\phi_1)\big|_U$，则

$$
d_j(\phi_1(x),\phi_1(y))
\le
\sum_{i\in I}[\mathbf L_1]_{i\to j}d_i(x,y).
$$

代入 (i) 的第一式即得 (ii)。若 $\mathbf K_1\in\mathscr K(\phi_1)\big|_U$，则

$$
\sum_{i\in I}[\mathbf K_1]_{i\to j}d_i(x,y)
\le
d_j(\phi_1(x),\phi_1(y)).
$$

再由 (i) 的第二式放缩，即得 (iii)。$\square$

#### 有限复合的局部矩阵界

**推论 #h-c80171fa685dc795（有限复合的局部矩阵界）**：设有限复合 $c_k=\phi_k\circ\cdots\circ\phi_1$（$k\geq1$），并取起始定义域子集 $U_1 \subseteq \mathrm{dom}(c_k)$。递归定义中间像集 $U_{m+1} = \phi_m(U_m)$（$m = 1, \dots, k$）。在复合链语境中，若无特别说明，$\mathbf L^{(m)}$、$\mathbf K^{(m)}$ 分别表示第 $m$ 步在实际输入域 $U_m$ 上选取的局部证书。则全复合的局部距离测量矩阵判定如下：

**(i) Lip 矩阵放缩上限**：若各单步具有合法矩阵 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$，则全复合满足：
   $$\mathbf{L}^{(k)} \cdot \cdots \cdot \mathbf{L}^{(1)} \;\in\; \mathscr{L}(c_k)\big|_{U_1}$$
**(ii) co-Lip 矩阵保距下限**：若各单步具有合法矩阵 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$，则全复合满足：
   $$\mathbf{K}^{(k)} \cdot \cdots \cdot \mathbf{K}^{(1)} \;\in\; \mathscr{K}(c_k)\big|_{U_1}$$

**证明**：由 $U_1 \subseteq \mathrm{dom}(c_k)$ 与复合定义逐步递推，得

$$
U_m \subseteq \mathrm{dom}(\phi_m)
\qquad(m=1,\ldots,k).
$$

分别对 @h-193cebcc1a7f9259 与 @h-0f256e6f1d38a612 做有限归纳，即得 (i) 与 (ii)。$\square$

> **注 #h-11006ddd8c43bfec（零步复合的单位矩阵证书）**：当边界情形 $k=0$ 时，$c_0 = \mathrm{id}_{\mathcal{X}}$。定义矩阵空复合乘积为单位矩阵 $\mathbf{I}$。对任意非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，$\mathbf{I} \in \mathscr{L}(\mathrm{id}_{\mathcal{X}})\big|_U \cap \mathscr{K}(\mathrm{id}_{\mathcal{X}})\big|_U$。
>
> **证明**：恒等映射满足 $d_j(x,y)=\sum_{i\in I}\mathbf{I}_{i\to j}d_i(x,y)$，故同一单位矩阵同时满足 Lip 与 co-Lip 不等式。

该推论只断言所选单步证书的连乘仍是合法证书，不断言所得矩阵在全复合的证书族中具有任何极值性质。

**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）**：对于任意有限复合 $c_n = \phi_n \circ \cdots \circ \phi_1$（$n\ge1$），设 $U_1 \subseteq \mathrm{dom}(c_n)$，并递归定义 $U_{m+1}=\phi_m(U_m)$（$m=1,\dots,n$）。沿该复合链取局部证书 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$ 与 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$。则对任意 $i,j\in I$：

**(i) Lip 乘积条目的零值判据**：$[\mathbf{L}^{(n)}\cdots\mathbf{L}^{(1)}]_{i \to j}=0$，当且仅当对任意指标序列 $(k_1, k_2, \dots, k_{n-1})$，必然存在至少一个层级 $m \in \{1,\dots,n\}$ 使得：
$$ [\mathbf{L}^{(m)}]_{k_{m-1} \to k_m} = 0 $$
（其中约定起止指标 $k_0 = i, k_n = j$）。

**(ii) co-Lip 乘积条目的正值判据**：$[\mathbf{K}^{(n)}\cdots\mathbf{K}^{(1)}]_{i \to j}>0$，当且仅当存在**至少一条**指标序列 $(k_1, k_2, \dots, k_{n-1})$，使得沿该路径的所有单步矩阵条目均严格正：
$$ \forall m \in \{1,\dots,n\},\quad [\mathbf{K}^{(m)}]_{k_{m-1} \to k_m} > 0 $$

当 $n=1$ 时，中间指标序列为空，唯一空序列按约定满足 $k_0=i$、$k_1=j$；上述两条判据分别退化为单个矩阵条目 $[\mathbf L^{(1)}]_{i\to j}=0$ 与 $[\mathbf K^{(1)}]_{i\to j}>0$。

**证明**：将矩阵乘积按定义在 $\bar{\mathbb{R}}_+$ 中展开：
当 $n=1$ 时展开式就是 $[\mathbf L^{(1)}]_{i\to j}$；当 $n\ge2$ 时，

$$[\mathbf{L}^{(n)} \cdots \mathbf{L}^{(1)}]_{i \to j} = \sum_{k_{n-1}\in I} \cdots \sum_{k_1\in I} \left( [\mathbf{L}^{(n)}]_{k_{n-1} \to j} \cdots [\mathbf{L}^{(2)}]_{k_1 \to k_2} \cdot [\mathbf{L}^{(1)}]_{i \to k_1} \right).$$

**(i)** 由于 $\bar{\mathbb{R}}_+$ 中所有求和项皆非负，多项总和为 $0$ 的充要条件是每一条路径乘积严格等于 $0$。由乘法规则（含 $0 \cdot +\infty = 0$ 约定），乘积为 $0$ 等价于其因子中存在至少一个零元素。

**(ii)** 同理，$\bar{\mathbb{R}}_+$ 中多个非负项累加严格 $>0$，意味着存在至少一组严格 $>0$ 的乘积项。该乘积项的所有因子均必须严格正（否则乘积为 $0$）。得证。$\square$

### #h-7fa97eb6e24d5527 分量解耦与通道分辨保持

**定义（矩阵证书的通道结构）**：为描述算子在子集 $U \subseteq \mathrm{dom}(\phi)$ 上的分量传递，固定一组受限证书 $\mathbf L\in\mathscr L(\phi)\big|_U$ 或 $\mathbf K\in\mathscr K(\phi)\big|_U$。

矩阵条目依赖所选证书；若只关心单一输入分量对单一输出分量的最佳上界，可定义不依赖具体矩阵证书的通道常数。

#### 定义（单通道 Lip 常数）

对固定的分量对 $(i, j) \in I \times I$，将其视为从输入分量 $d_i$ 到输出分量 $d_j$ 的一个**分量通道**。

定义算子 $\phi$ 在作用域 $U\subseteq\mathrm{dom}(\phi)$ 上关于分量通道 $(i, j)$ 的**单通道 Lip 常数**：

$$\underline{L}_{i \to j}(\phi;U) := \inf\bigl\{\lambda \in \bar{\mathbb{R}}_+ \;\big|\; \forall x, y \in U,\; d_j(\phi(x), \phi(y)) \leq \lambda \cdot d_i(x, y)\bigr\}$$

即从 $(U, d_i)$ 到 $(\phi(U), d_j)$ 的可行 Lipschitz 常数集的下确界。若可行集合为空，则按 $\inf\emptyset=+\infty$ 约定。此定义自然处理所有边界情形：当存在 $d_i(x,y) = 0$ 且 $d_j(\phi(x), \phi(y)) > 0$ 的点对时，没有任何 $\lambda\in\bar{\mathbb R}_+$ 满足上式，因为 $\lambda\cdot0=0$（包括 $\lambda=+\infty$），故可行集合为空并有 $\underline{L}_{i\to j}(\phi;U)=+\infty$。当 $d_i(x,y)=+\infty$ 时，$\lambda\cdot(+\infty)=+\infty$ 对任何 $\lambda>0$ 成立；但按本书约定 $0\cdot(+\infty)=0$，故下确界为 $0$ 时仍需另行判断 $\lambda=0$ 是否可行。

当 $0 < \underline{L}_{i\to j}(\phi;U) < \infty$ 时，下确界可被取到：合法常数集

$$
\mathcal{S} = \{\lambda \in \bar{\mathbb{R}}_+ : \forall x,y\in U,\; d_j(\phi(x),\phi(y)) \leq \lambda \cdot d_i(x,y)\}
$$

向上封闭（若 $\lambda_0 \in \mathcal{S}$ 且 $\lambda_1 \geq \lambda_0$，则 $\lambda_1 \in \mathcal{S}$）。记 $a=\underline{L}_{i\to j}(\phi;U)$。对任意 $\lambda>a$，由下确界定义与向上封闭性得 $\lambda\in\mathcal S$。固定 $x,y\in U$，记

$$A=d_j(\phi(x),\phi(y)),\qquad B=d_i(x,y).$$

若 $B=0$，则对所有 $\lambda>a$ 有 $A\le \lambda\cdot0=0$，故 $A=0=aB$。若 $0<B<+\infty$，反设 $A>aB$；由于 $0<a<+\infty$ 且 $B$ 有限正，可取 $\lambda>a$ 使 $\lambda B<A$，这与 $\lambda\in\mathcal S$ 矛盾。若 $B=+\infty$，则 $aB=+\infty$，不等式 $A\le aB$ 自动成立。因此对任意 $x,y\in U$ 均有

$$
d_j(\phi(x),\phi(y))\le \underline{L}_{i\to j}(\phi;U)\,d_i(x,y).
$$

> **注 #h-57de7918859a9de2（单通道常数与矩阵条目）**：单通道 Lip 常数 $\underline{L}_{i \to j}(\phi;U)$ 与 Lip 矩阵元素 $[\mathbf{L}]_{i \to j}$ 是不同对象。当 $0<\underline{L}_{i\to j}(\phi;U)<+\infty$ 时，前者本身给出单分量上界
>
> $$d_j(\phi(x),\phi(y))\le \underline{L}_{i\to j}(\phi;U)\,d_i(x,y)\qquad(x,y\in U),$$
>
> 后者只是多分量求和上界
>
> $$d_j(\phi(x),\phi(y))\le\sum_{k\in I}[\mathbf L]_{k\to j}d_k(x,y)$$
>
> 中的一个系数。若 $\underline{L}_{i\to j}(\phi;U)=0$，则每个有限正数 $\lambda$ 均给出上述单分量上界，但 $\lambda=0$ 未必可行。无论下确界是否取到，$\underline{L}_{i \to j}(\phi;U) < +\infty$ 等价于存在有限常数 $\lambda<+\infty$ 使 $\phi:(U,d_i)\to(\phi(U),d_j)$ 满足 $d_j(\phi(x),\phi(y))\le \lambda d_i(x,y)$。
>
> **证明**：第一句是两个定义的直接比较：$\underline{L}$ 的定义只允许输入分量 $d_i$ 参与右端，而 Lip 矩阵条目处于对所有 $k\in I$ 的求和中。
>
> 若 $0<\underline{L}<+\infty$，由上段下确界取到性质可取 $\lambda=\underline{L}$。若 $\underline{L}=0$，任取有限正数 $\lambda$，由下确界定义与向上封闭性得 $\lambda$ 属于可行集合；这一步不声称 $\lambda=0$ 可行。
>
> 反之，若存在有限 $\lambda$ 满足单分量上界，则 $\lambda$ 属于定义 $\underline{L}$ 的可行集合，故 $\underline{L}\le \lambda<+\infty$。

> **约定（矩阵行列方向）**：条目 $M_{i\to j}$ 的箭头左端 $i$ 是输入分量，右端 $j$ 是输出分量。把该系数族写成通常的行列矩阵时，输出指标 $j$ 标记行，输入指标 $i$ 标记列；即第 $j$ 行第 $i$ 列的条目写作 $M_{i\to j}$。因此下文“第 $j$ 行”表示固定输出指标 $j$，“第 $i$ 列”表示固定输入指标 $i$。这一约定与复合律 $(\mathbf M_2\mathbf M_1)_{i\to j}=\sum_{k\in I}(\mathbf M_2)_{k\to j}(\mathbf M_1)_{i\to k}$ 一致。

**(i) 通道隔离与正下界传递**：若 $L_{i\to j}=0$，则在该上界证书中，$d_i$-项不参与 $d_j$ 的输出上界；若 $K_{i\to j}>0$，则该 co-Lip 证书给出从输入分量 $d_i$ 到输出分量 $d_j$ 的正下界传递。

**(ii) 行解耦**：若存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 使得第 $j$ 行至多有一项非零（即 $\exists\, i \in I$ 使 $L_{k \to j} = 0$ 对所有 $k \neq i$），则称 $\phi$ 在 $U$ 上关于输出分量 $d_j$ **行解耦**。此时 $d_j(\phi(x), \phi(y)) \leq L_{i \to j} \cdot d_i(x, y)$。

**(iii) 列解耦**：若存在 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 使得第 $i$ 列至多有一项非零（即 $\exists\, j \in I$ 使 $L_{i \to k} = 0$ 对所有 $k \neq j$），则称 $\phi$ 在 $U$ 上关于输入分量 $d_i$ **列解耦**。此时在该上界证书中，$d_i$ 的输入差异至多进入单一输出分量 $d_j$ 的上界。

**(iv) 完全解耦体系**：若 $\mathbf{L}$ 为对角矩阵（所有非对角项为 $0$），则称该上界证书给出**完全解耦体系**。此时各分量独立满足标量放缩：
$$\forall x,y\in U,\qquad d_i(\phi(x),\phi(y))\le L_{i\to i}\,d_i(x,y)\quad(i\in I).$$

**引理 #h-6a98a58b5bc95360（对角输入项的标量双侧界）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi)$，$j \in I$。给定 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若 $\phi$ 在 $U$ 上关于输出分量 $d_j$ 满足只保留对角输入项的 Lip 上界

$$L_{k \to j} = 0\quad(\forall k \neq j),$$

则对任意 $x,y\in U$ 有标量双侧不等式：

$$K_{j \to j} \cdot d_j(x, y) \;\leq\; d_j(\phi(x), \phi(y)) \;\leq\; L_{j \to j} \cdot d_j(x, y) \qquad \forall\, x, y \in U$$

**证明**：由 Lip 矩阵定义与 $L_{k\to j}=0$（$k\neq j$）：

$$d_j(\phi(x), \phi(y)) \leq L_{j \to j} \cdot d_j(x, y).$$

由 co-Lip 矩阵定义及各项非负，

$$K_{j\to j}d_j(x,y)\le\sum_{k\in I}K_{k\to j}d_k(x,y)\le d_j(\phi(x),\phi(y)).$$

合并即得。$\square$

若上述对角输入项条件对所有 $j \in I$ 均成立，则得到逐分量的标量双侧不等式。若进一步要求 $L_{j \to j}, K_{j \to j} < +\infty$，则得到有限标量双侧放缩界。

**命题 #h-f82672ec0dd48f28（正 co-Lip 通道的可分辨保持）**：设 $\mathbf K\in\mathscr K(\phi)\big|_U$。

**(i)** 若 $K_{i\to j}>0$，则对任意 $x,y\in U$，

$$
d_i(x,y)>0
\quad\Longrightarrow\quad
d_j(\phi(x),\phi(y))>0.
$$

**(ii)** 若 $K_{j\to j}>0$ 对所有 $j\in I$ 成立，则 $\phi$ 反射族零距关系：对任意 $x,y\in U$，

$$
\phi(x)\sim_{\mathcal G}\phi(y)
\quad\Longrightarrow\quad
x\sim_{\mathcal G}y.
$$

**证明**：对任意 $x,y\in U$，co-Lip 不等式与非负性给出

$$
d_j(\phi(x),\phi(y))
\ge
\sum_{k\in I}K_{k\to j}d_k(x,y)
\ge
K_{i\to j}d_i(x,y).
$$

若 $K_{i\to j}>0$ 且 $d_i(x,y)>0$，则右侧严格大于零，故 (i) 成立。

对 (ii)，设 $\phi(x)\sim_{\mathcal G}\phi(y)$。固定 $j\in I$；若 $d_j(x,y)>0$，则由 (i) 取通道 $(j,j)$ 可得 $d_j(\phi(x),\phi(y))>0$，与族零距关系矛盾。因此 $d_j(x,y)=0$。由于 $j$ 任意，得到 $x\sim_{\mathcal G}y$。$\square$

Lipschitz 矩阵与 co-Lipschitz 矩阵分别给出跨分量上界与受限域下界。它们在复合中按矩阵乘法传播，但始终只是所选证书给出的代数界；上界不能替代下界，下界也不能替代上界。通道隔离、正下界传递和复合零/正条目判据只描述这些证书的矩阵结构，不直接穷尽算子的实际点态行为。

----
*[OE] ⊢ [GLENZLI] ⊢ [卷 01] ⊢ [02-operator-bounds] ⊢ [2d2f76c8392daf62]*
