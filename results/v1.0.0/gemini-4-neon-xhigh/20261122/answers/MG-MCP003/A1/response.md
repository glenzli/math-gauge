以 CH1 给出的扩展规范空间 $(\mathcal{X},\mathcal{G},\bot)$（其中 $\mathcal{G}=\{d_i\}_{i\in I}$，$I$ 为有限非空指标集）及算子空间 $\mathcal{X}_{\mathrm{op}}$ 为基础，下面将“多分量矩阵 Lipschitz 上界、矩阵下界、支持 $+\infty$ 的统一扩展，以及与之对等的输入范畴致输出不可区分矩阵”整理为一个自洽的数学框架，并给出基本性质与严格论证。

---

## 一、准备记号与扩展矩阵半环

### 1.1 距离向量与扩展矩阵半环

对任意 $x,y\in\mathcal{X}$，定义其**规范距离向量**（简称距离向量）：
$$
\mathbf{d}(x,y) := \bigl(d_i(x,y)\bigr)_{i\in I} \in \bar{\mathbb{R}}_+^I.
$$
按分量序 $\le$，$\mathbf{d}$ 满足 $\mathbf{d}(x,x)=\mathbf{0}$、$\mathbf{d}(x,y)=\mathbf{d}(y,x)$、$\mathbf{d}(x,z)\le\mathbf{d}(x,y)+\mathbf{d}(y,z)$，且对任意 $x\neq\bot$ 有 $\mathbf{d}(x,\bot)=\boldsymbol{\infty}:=(+\infty)_{i\in I}$。

记 $\mathcal{M}_I(\bar{\mathbb{R}}_+) := \bar{\mathbb{R}}_+^{I\times I}$ 为指标集 $I$ 上的扩展非负矩阵空间，其上配备按分量偏序 $A\le B \iff \forall i,j\in I,\, A_{ij}\le B_{ij}$。采用 CH1 的 $\bar{\mathbb{R}}_+$ 算术约定（特别地 $0\cdot(+\infty)=0$），定义矩阵乘法与矩阵-向量乘法：
$$
(AB)_{ik} := \sum_{j\in I} A_{ij}B_{jk}, \qquad (A\mathbf{v})_i := \sum_{j\in I} A_{ij}v_j \qquad \bigl(A,B\in\mathcal{M}_I(\bar{\mathbb{R}}_+),\;\mathbf{v}\in\bar{\mathbb{R}}_+^I\bigr).
$$
常用特殊矩阵与运算如下：
- 零矩阵 $\mathbf{0}$、全无穷矩阵 $\boldsymbol{\infty}_{I\times I}$、单位矩阵 $E=(\delta_{ij})_{i,j\in I}$、无穷对角矩阵 $E_\infty:=\mathrm{diag}(+\infty,\dots,+\infty)$。
- **支集指示函数** $\mathrm{supp}:\bar{\mathbb{R}}_+\to\{0,1\}$ 定义为 $\mathrm{supp}(0)=0$、$\mathrm{supp}(a)=1$（$a>0$），并按分量推广至矩阵 $\mathrm{supp}(A)\in\{0,1\}^{I\times I}$。记 $\infty\cdot\mathrm{supp}(A)$ 为将 $A$ 的正元替换为 $+\infty$、零元保持为 $0$ 的矩阵。
- **逐元倒数** $a^{-1}\in\bar{\mathbb{R}}_+$ 约定 $0^{-1}:=+\infty$、$(+\infty)^{-1}:=0$；对矩阵 $A$ 记 $A^{\circ(-1)}:=(A_{ij}^{-1})_{i,j\in I}$。
- **支集极大积（support-max product）** $A\odot B\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 定义为
  $$
  (A\odot B)_{ik} := \max_{j\in I}\bigl(\mathrm{supp}(A_{ij})\,B_{jk}\bigr).
  $$

**命题 1.1（扩展矩阵代数基础）**
1. $(\bar{\mathbb{R}}_+,+,\cdot,0,1)$ 是有序交换半环；因此 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 上的矩阵乘法满足结合律 $(AB)C=A(BC)$、$(AB)\mathbf{v}=A(B\mathbf{v})$、分配律、双侧保序性，且以 $E$ 为乘法单位元、$\mathbf{0}$ 为吸收元。对任意 $\lambda,\mu\in\bar{\mathbb{R}}_+$，有 $(\lambda A+\mu B)\mathbf{v}=\lambda(A\mathbf{v})+\mu(B\mathbf{v})$。
2. 支集极大积 $\odot$ 满足结合律 $(A\odot B)\odot C = A\odot(B\odot C)$ 与双侧保序性，且 $E_\infty\odot B = E\odot B = B$。
3. 赋予 $\bar{\mathbb{R}}_+=[0,+\infty]$ 标准序拓扑（紧致 Hausdorff 空间），则加法连续；对固定 $d\in[0,+\infty)$，映射 $a\mapsto a\cdot d$ 连续；而对 $d=+\infty$，映射 $a\mapsto a\cdot(+\infty)$ 在 $[0,+\infty]$ 上**下半连续**，但在 $a=0$ 处**非上半连续**（由 $0\cdot(+\infty)=0$ 导致）。

**证明**：
1. 只需核验 $\bar{\mathbb{R}}_+$ 上乘法对加法的分配律 $a(b+c)=ab+ac$ 与保序性。当 $a=0$ 时，由 $0\cdot(+\infty)=0$，两边均为 $0$；当 $0<a<+\infty$ 时显然；当 $a=+\infty$ 时，若 $b=c=0$ 则两边均为 $0$，若 $b>0$ 或 $c>0$ 则 $b+c>0$ 且两边均为 $+\infty$。保序性同理可验。$I$ 有限，故矩阵乘法的结合律、分配律与保序性由半环公理直接推出。
2. 对任意 $i,\ell\in I$，注意到 $(A\odot B)_{ik}>0 \iff \exists j\in I$ 使 $A_{ij}>0$ 且 $B_{jk}>0$，于是
   $$
   \bigl((A\odot B)\odot C\bigr)_{i\ell}
   = \max_{k:\,(A\odot B)_{ik}>0} C_{k\ell}
   = \max_{j:\,A_{ij}>0}\;\max_{k:\,B_{jk}>0} C_{k\ell}
   = \bigl(A\odot(B\odot C)\bigr)_{i\ell}
   $$
   （约定空集之 $\max$ 为 $0$，与定义中 $\mathrm{supp}=0$ 贡献 $0$ 一致）。双侧保序性与 $E_\infty\odot B=E\odot B=B$ 显然。
3. 当 $a_n\to a$ 时，若 $d=+\infty$ 且 $a>0$，则充分大 $n$ 有 $a_n>0$，从而 $a_n d=+\infty=ad$；若 $a=0$，则 $ad=0\le \liminf_{n\to\infty} a_n d$，但取 $a_n=1/n\downarrow 0$ 时 $\lim a_n d=+\infty>0=ad$，故仅下半连续。 $\square$

---

### 1.2 不可区分关系与为何限制在 $\mathrm{dom}(\phi)$ 上

由于 CH1 **不预设族分离性**，在 $\mathcal{X}$ 上自然诱导出以下等价关系：
- **第 $i$ 分量不可区分**：$x \sim_i y :\iff d_i(x,y)=0$；
- **全分量不可区分**：$x \sim_{\mathcal{G}} y :\iff \mathbf{d}(x,y)=\mathbf{0}$。

由公理 (iv)（吸收元隔离），$\bot$ 在每个 $\sim_i$（及 $\sim_{\mathcal{G}}$）下的等价类均为单点集 $\{\bot\}$。据此，对算子 $\phi\in\mathcal{X}_{\mathrm{op}}$，引入两个核心相容条件：
- **（全零距离保持性 / $\mathcal{G}$-外延性）**：$\forall x,y\in\mathrm{dom}(\phi),\; \mathbf{d}(x,y)=\mathbf{0} \implies \mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$。
  （等价于 $\phi|_{\mathrm{dom}(\phi)}$ 诱导商空间 $\mathrm{dom}(\phi)/\!\sim_{\mathcal{G}}\to\mathcal{X}/\!\sim_{\mathcal{G}}$ 上的良定映射。）
- **（全零距离反射性 / $\mathcal{G}$-伪单射性）**：$\forall x,y\in\mathrm{dom}(\phi),\; \mathbf{d}(\phi(x),\phi(y))=\mathbf{0} \implies \mathbf{d}(x,y)=\mathbf{0}$。

> **注记 1.2（为何度量估计定义在 $\mathrm{dom}(\phi)\times\mathrm{dom}(\phi)$ 上）**：
> 若强行在整个 $\mathcal{X}\times\mathcal{X}$ 上要求不等式，吸收元隔离 $d_i(x,\bot)=+\infty$（$x\neq\bot$）会引发三类病态退化：
> 1. 若 $\phi$ 在非吸收元上取常数 $x_0\neq\bot$（$\phi(\bot)=\bot$），则对 $x\in\mathrm{dom}(\phi),y=\bot$ 有 $d_i(\phi(x),\phi(\bot))=+\infty$，从而零矩阵 $\mathbf{0}$ 既无法成为其上 Lipschitz 矩阵，也无法成为其坍缩矩阵；
> 2. 若 $\phi$ 为真偏算子（存在 $x_0\in(\mathcal{X}\setminus\{\bot\})\setminus\mathrm{dom}(\phi)$），取 $(x_0,\bot)$ 有 $\mathbf{d}(\phi(x_0),\phi(\bot))=\mathbf{0}$ 而 $\mathbf{d}(x_0,\bot)=\boldsymbol{\infty}$，将迫使任意下界矩阵退化为 $\mathbf{0}$，任意反向界矩阵不存在；
> 3. 若 $x\in\mathrm{dom}(\phi),y\notin\mathrm{dom}(\phi)$ 且 $\mathbf{d}(x,y)=\mathbf{0}$（非分离空间中完全允许），则 $d_i(\phi(x),\phi(y))=+\infty$ 而 $(L\mathbf{d}(x,y))_i=0$，连 $\boldsymbol{\infty}_{I\times I}$ 都不满足。
>
> 因此，将四类矩阵统一定义在有效定义域 $\mathrm{dom}(\phi)\times\mathrm{dom}(\phi)$ 上是 CH1 公理体系下的唯一自洽选择。此外，若需刻画算子在某个局部区域 $S\subseteq\mathcal{X}$ 上的行为，只需构造限制算子 $\phi|_S\in\mathcal{X}_{\mathrm{op}}$（令 $x\in S$ 时 $\phi|_S(x)=\phi(x)$，$x\notin S$ 时 $\phi|_S(x)=\bot$），其有效定义域恰为 $S\cap\mathrm{dom}(\phi)$，局部性质由此无缝纳入同一理论。

---

## 二、四类对等算子矩阵的严格定义

在单一伪度量（$|I|=1$）下，上界、下界和不可区分阈值各对应一个标量常数；但在多分量规范结构（$|I|\ge 2$）下，各伪度量间可能存在耦合，**一般不存在唯一的极值矩阵**（见命题 3.4）。因此，忠实且严谨的做法是将每个算子 $\phi\in\mathcal{X}_{\mathrm{op}}$ 关联到 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中的**容许矩阵族**（admissible matrix classes）。

**定义 2.1（上 Lipschitz 矩阵族）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$。称矩阵 $L\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**上 Lipschitz 矩阵**（或简称 **Lipschitz 上界矩阵**），如果
$$
\forall x,y\in\mathrm{dom}(\phi),\qquad \mathbf{d}\bigl(\phi(x),\phi(y)\bigr) \le L\,\mathbf{d}(x,y),
$$
即对每个 $i\in I$，
$$
d_i\bigl(\phi(x),\phi(y)\bigr) \le \sum_{j\in I} L_{ij}\,d_j(x,y).
$$
记 $\phi$ 的全体上 Lipschitz 矩阵之集为 $\mathcal{L}^+(\phi)$。若存在 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$（全有限矩阵），称 $\phi$ 是**有限矩阵 Lipschitz 的**。

---

**定义 2.2（下界矩阵族：前向下 Lipschitz 矩阵与反向 Lipschitz 矩阵）**
当 $|I|=1$ 时，$d(\phi(x),\phi(y))\ge m\,d(x,y)$ 与 $d(x,y)\le b\,d(\phi(x),\phi(y))$ 在 $m,b\in(0,+\infty)$ 时仅差取倒数 $b=m^{-1}$；但在 $|I|\ge 2$ 时，二者会**本质分化**为两种互不可替代的矩阵概念：

1. **前向下 Lipschitz 矩阵（扩张下界矩阵）**：称 $M\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**前向下 Lipschitz 矩阵**，如果
   $$
   \forall x,y\in\mathrm{dom}(\phi),\qquad \mathbf{d}\bigl(\phi(x),\phi(y)\bigr) \ge M\,\mathbf{d}(x,y),
   $$
   即对每个 $i\in I$，$d_i(\phi(x),\phi(y))\ge \sum_{j\in I} M_{ij}d_j(x,y)$。全体此类矩阵记为 $\mathcal{L}^-(\phi)$。
2. **反向 Lipschitz 矩阵（逆向稳定界矩阵）**：称 $B\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**反向 Lipschitz 矩阵**，如果
   $$
   \forall x,y\in\mathrm{dom}(\phi),\qquad \mathbf{d}(x,y) \le B\,\mathbf{d}\bigl(\phi(x),\phi(y)\bigr),
   $$
   即对每个 $j\in I$，$d_j(x,y)\le \sum_{i\in I} B_{ji}d_i(\phi(x),\phi(y))$。全体此类矩阵记为 $\mathcal{L}^{\mathrm{inv}}(\phi)$。

> **注记 2.3（为何同时保留 $\mathcal{L}^-$ 与 $\mathcal{L}^{\mathrm{inv}}$）**：
> - $\mathcal{L}^-(\phi)$ 与 $\mathcal{L}^+(\phi)$ 构成最直接的双边夹逼 $M\mathbf{d}(x,y)\le\mathbf{d}(\phi(x),\phi(y))\le L\mathbf{d}(x,y)$，恒非空（含 $\mathbf{0}$），且适合刻画**单个输出分量对输入分量的逐分量扩张下界**（即便其他分量坍缩，如 $\psi(x_1,x_2)=(2x_1,0)$ 仍有非平凡 $M=\mathrm{diag}(2,0)$）。
> - 但对于**分量耦合的双向稳定映射**（如 $\mathbb{R}^2$ 上旋转或混叠 $\phi(x_1,x_2)=(x_1+x_2,x_1-x_2)$），任一单独输出分量都有非平凡零核，导致 $\mathcal{L}^-(\phi)=\{\mathbf{0}\}$ 失去分辨力；此时唯有 $\mathcal{L}^{\mathrm{inv}}(\phi)$ 能捕捉整体双 Lipschitz 下界（$B=\frac{1}{2}\begin{pmatrix}1&1\\1&1\end{pmatrix}$），且当 $\phi$ 可逆时恰等于 $\mathcal{L}^+(\phi^{-1})$（见命题 5.2）。

---

**定义 2.4（不可区分 / 坍缩矩阵族）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$。称矩阵 $W\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**不可区分矩阵**（亦称**坍缩率矩阵**，indistinguishability / collapse matrix），如果对任意 $x,y\in\mathrm{dom}(\phi)$ 与任意 $i\in I$，
$$
\bigl(W\,\mathbf{d}(x,y)\bigr)_i < 1 \;\implies\; d_i\bigl(\phi(x),\phi(y)\bigr) = 0,
$$
即
$$
\sum_{j\in I} W_{ij}\,d_j(x,y) < 1 \;\implies\; d_i\bigl(\phi(x),\phi(y)\bigr) = 0.
$$
记 $\phi$ 的全体不可区分矩阵之集为 $\mathcal{K}(\phi)$。

#### 对定义 2.4 的几何解释与“对等性”论证

1. **逐元含义与几何范畴**：对每个输出分量 $i\in I$，第 $i$ 行 $W_{i,\cdot}$ 在输入距离空间 $\bar{\mathbb{R}}_+^I$ 中切出一个**加权单纯形型坍缩范畴**
   $$
   \Delta_i(W) := \Bigl\{\,\mathbf{v}\in\bar{\mathbb{R}}_+^I \;\Big|\; \sum_{j\in I} W_{ij}v_j < 1\,\Bigr\}
   $$
   （写成逐元倒数阈值半径 $\Theta_{ij}:=W_{ij}^{-1}\in\bar{\mathbb{R}}_+$ 时，直观上即 $\sum_{j\in I} d_j(x,y)/\Theta_{ij} < 1$）。各极端值在 CH1 的 $0\cdot(+\infty)=0$ 约定下全部无缝工作：
   - **$W_{ij}=0$（对应阈值半径 $\Theta_{ij}=+\infty$）**：因 $0\cdot d_j(x,y)=0$（即使 $d_j=+\infty$），输入分量 $j$ 的任意变动都不受约束；整行 $W_{i,\cdot}=\mathbf{0}$ 意味着输出分量 $i$ 完全坍缩（恒不可区分）。
   - **$0<W_{ij}<+\infty$（对应有限正阈值 $\Theta_{ij}=W_{ij}^{-1}$）**：$W_{ij}$ 越小（阈值半径 $\Theta_{ij}$ 越大），输出分量 $i$ 对输入分量 $j$ 的容忍范畴越宽，坍缩越强。
   - **$W_{ij}=+\infty$（对应零阈值 $\Theta_{ij}=0$）**：由 $(+\infty)\cdot 0=0<1$ 而 $(+\infty)\cdot d_j=+\infty\not<1$（$d_j>0$），该项恰好仅允许 $d_j(x,y)=0$，表示输出分量 $i$ 对输入分量 $j$ 无正容忍半径（仅保持零距离）。

2. **与 $L,M$ 的结构对等性**：
   - 三者均落在同一空间 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中，且均通过同一线性作用 $\mathbf{d}(x,y)\mapsto A\,\mathbf{d}(x,y)$ 表达各分量间关系；
   - $W$ 与 $L$ 具有完全相同的单调方向（元越大约束越弱，故均构成上集）、完全相同的存在判据（定理 3.1）、完全相同的依赖支集结构（定理 5.3），且在复合下服从普通矩阵乘法 $W_\psi L_\phi\in\mathcal{K}(\psi\circ\phi)$（定理 4.2）；
   - 事实上，引入扩展指示函数 $\chi_{(1,+\infty]}(t)$（$t<1$ 时取 $0$，$t\ge 1$ 时取 $+\infty$），定义 2.4 可改写为与定义 2.1 完全并列的不等式形式：
     $$
     d_i\bigl(\phi(x),\phi(y)\bigr) \le \chi_{[1,+\infty]}\!\bigl((W\,\mathbf{d}(x,y))_i\bigr).
     $$

3. **与盒式阈值矩阵（$\max$ 型 / $\le \Theta_{ij}$ 型）的精确比较**：
   若考虑直观上的“盒式”不可区分定义
   $$
   \mathcal{K}_{\mathrm{box}}(\phi):=\Bigl\{W\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\;\Big|\;\forall x,y\in\mathrm{dom}(\phi),\,\forall i\in I,\;\max_{j\in I} W_{ij}d_j(x,y)<1 \implies d_i(\phi(x),\phi(y))=0\Bigr\},
   $$
   以及闭盒阈值形式 $\mathcal{T}_{\le}(\phi):=\{\Theta\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\mid (\forall j,\,d_j(x,y)\le \Theta_{ij})\implies d_i(\phi(x),\phi(y))=0\}$，则我们有如下定量等价关系：

   **命题 2.5（线性坍缩矩阵与盒式阈值矩阵的等价性）**
   1. $\mathcal{K}_{\mathrm{box}}(\phi) \subseteq \mathcal{K}(\phi)$，且对任意 $W\in\mathcal{K}(\phi)$ 有 $|I|\,W\in\mathcal{K}_{\mathrm{box}}(\phi)$；特别地，当 $|I|=1$ 时 $\mathcal{K}_{\mathrm{box}}(\phi)=\mathcal{K}(\phi)$。
   2. 若 $\Theta\in\mathcal{T}_{\le}(\phi)$，则 $\Theta^{\circ(-1)}\in\mathcal{K}_{\mathrm{box}}(\phi)\subseteq\mathcal{K}(\phi)$；反之，若 $W\in\mathcal{K}(\phi)$，则对任意常数 $c>|I|$ 有 $(cW)^{\circ(-1)}\in\mathcal{T}_{\le}(\phi)$。

   **证明**：
   1. 若 $W\in\mathcal{K}_{\mathrm{box}}(\phi)$ 且 $(W\mathbf{d})_i<1$，则 $\max_j W_{ij}d_j\le\sum_j W_{ij}d_j<1$，故 $d_i(\phi(x),\phi(y))=0$，即 $W\in\mathcal{K}(\phi)$。反之，若 $W\in\mathcal{K}(\phi)$ 且 $\max_j (|I|W_{ij}d_j)<1$，则每项 $W_{ij}d_j<1/|I|$，对 $j\in I$ 求和得 $(W\mathbf{d})_i<1$，故 $d_i(\phi(x),\phi(y))=0$。
   2. 设 $\Theta\in\mathcal{T}_{\le}(\phi)$，$W=\Theta^{\circ(-1)}$。若 $\max_j W_{ij}d_j<1$，对每个 $j$ 分情形：$\Theta_{ij}=+\infty$ 则 $d_j\le\Theta_{ij}$ 显然；$\Theta_{ij}=0$ 则 $W_{ij}=+\infty$，由 $(+\infty)\cdot d_j<1$ 必有 $d_j=0=\Theta_{ij}$；$0<\Theta_{ij}<+\infty$ 则 $d_j<\Theta_{ij}$。故 $\forall j,\,d_j\le\Theta_{ij}$，得 $d_i(\phi(x),\phi(y))=0$。反之，若 $W\in\mathcal{K}(\phi)$、$c>|I|$ 且 $\forall j,\,d_j\le (cW_{ij})^{-1}$，则当 $W_{ij}=0$ 或 $W_{ij}=+\infty$（此时 $(cW_{ij})^{-1}=0\implies d_j=0$）时均有 $W_{ij}d_j=0$；当 $0<W_{ij}<+\infty$ 时 $W_{ij}d_j\le 1/c$。求和得 $(W\mathbf{d})_i\le |I|/c<1$，从而 $d_i(\phi(x),\phi(y))=0$。 $\square$

   > **为何以 $\mathcal{K}(\phi)$（线性求和 + 严格 $<1$）为标准定义？**
   > 1. **凸性**：$\mathcal{K}(\phi)$ 恒为凸集（命题 3.2），而 $\mathcal{K}_{\mathrm{box}}(\phi)$ 不凸（例如两条件 $d_1<1$ 与 $d_2<1$ 的中点 $\max(\frac{1}{2}d_1,\frac{1}{2}d_2)<1$ 允许 $(d_1,d_2)=(1.5,1.5)$，不能保证两者之一成立）；
   > 2. **无因子损失的矩阵复合**：$\mathcal{K}(\phi)$ 直接满足 $W_\psi L_\phi\in\mathcal{K}(\psi\circ\phi)$，而盒式形式在复合时会引入额外的 $|I|$ 因子；
   > 3. **边界闭性与避免空真**：若改用 $d_j<\Theta_{ij}$，则单个 $\Theta_{ij}=0$ 会使整行条件恒假而空真，且 $\Theta_{ij}=+\infty$ 无法覆盖 $d_j=+\infty$；若改用 $(W\mathbf{d})_i\le 1$，则在闭间隔域（如 $\mathrm{dom}(\phi)=(-\infty,-1]\cup[1,+\infty)$）上连有限距离下的极限点 $W=1/2$ 都取不到，丧失闭性（对比命题 3.3）。而 $(W\mathbf{d})_i<1$ 同时回避了以上全部缺陷。

---

## 三、存在性、序结构、凸性、闭性与极值矩阵

先注意到：四类矩阵的定义条件均按行解耦。分别记第 $i$ 行（对 $\mathcal{L}^{\mathrm{inv}}$ 为第 $j$ 行）的容许行向量集为 $\mathcal{L}_i^+(\phi),\,\mathcal{L}_i^-(\phi),\,\mathcal{L}_j^{\mathrm{inv}}(\phi),\,\mathcal{K}_i(\phi)\subseteq\bar{\mathbb{R}}_+^I$，则四类矩阵族均分解为行集合的笛卡尔积：
$$
\mathcal{L}^+(\phi)=\prod_{i\in I}\mathcal{L}_i^+(\phi),\quad
\mathcal{L}^-(\phi)=\prod_{i\in I}\mathcal{L}_i^-(\phi),\quad
\mathcal{L}^{\mathrm{inv}}(\phi)=\prod_{j\in I}\mathcal{L}_j^{\mathrm{inv}}(\phi),\quad
\mathcal{K}(\phi)=\prod_{i\in I}\mathcal{K}_i(\phi).
$$

### 3.1 存在性与退化算子的完整刻画

**定理 3.1（存在性判据与极端值意义）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **（上界与坍缩的共同存在判据）** 以下五条等价：
   - (a) $\mathcal{L}^+(\phi)\neq\emptyset$；
   - (b) $\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^+(\phi)$；
   - (c) $\mathcal{K}(\phi)\neq\emptyset$；
   - (d) $\boldsymbol{\infty}_{I\times I}\in\mathcal{K}(\phi)$；
   - (e) $\phi$ 在 $\mathrm{dom}(\phi)$ 上保持全零距离（$\mathbf{d}(x,y)=\mathbf{0}\implies\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$）。

   特别地，当规范族 $\mathcal{G}$ 具有**族分离性**时，**一切**算子 $\phi\in\mathcal{X}_{\mathrm{op}}$ 都自动满足 $\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^+(\phi)\cap\mathcal{K}(\phi)$，从而在引入 $+\infty$ 后实现了对所有算子的统一矩阵表示；而在不预设族分离性的 CH1 设定下，(e) 恰是 $+\infty$ 扩展的精确边界障碍。
2. **（前向下界恒非空）** 恒有 $\mathbf{0}\in\mathcal{L}^-(\phi)$；此外，$\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^-(\phi)$ 当且仅当对所有 $x,y\in\mathrm{dom}(\phi)$，$\mathbf{d}(x,y)\neq\mathbf{0}\implies\mathbf{d}(\phi(x),\phi(y))=\boldsymbol{\infty}$。
3. **（反向界的存在判据）** $\mathcal{L}^{\mathrm{inv}}(\phi)\neq\emptyset \iff \boldsymbol{\infty}_{I\times I}\in\mathcal{L}^{\mathrm{inv}}(\phi) \iff \phi$ 在 $\mathrm{dom}(\phi)$ 上反射全零距离。
4. **（完全坍缩判据）** $\mathbf{0}\in\mathcal{L}^+(\phi) \iff \mathbf{0}\in\mathcal{K}(\phi) \iff \forall x,y\in\mathrm{dom}(\phi),\,\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$。
5. **（特殊算子）**
   - 空定义域算子 $\phi_\bot\equiv\bot$（$\mathrm{dom}(\phi_\bot)=\emptyset$）使四类矩阵族均等于全空间 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$；
   - 恒等算子 $\mathrm{id}_{\mathcal{X}}$ 满足 $E\in\mathcal{L}^+(\mathrm{id}_{\mathcal{X}})\cap\mathcal{L}^-(\mathrm{id}_{\mathcal{X}})\cap\mathcal{L}^{\mathrm{inv}}(\mathrm{id}_{\mathcal{X}})$ 且 $E_\infty\in\mathcal{K}(\mathrm{id}_{\mathcal{X}})$；
   - 若 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$ 在有效定义域上互逆（$\phi(\mathrm{dom}(\phi))=\mathrm{dom}(\psi)$ 且 $\psi\circ\phi|_{\mathrm{dom}(\phi)}=\mathrm{id}_{\mathrm{dom}(\phi)}$、$\phi\circ\psi|_{\mathrm{dom}(\psi)}=\mathrm{id}_{\mathrm{dom}(\psi)}$），则 $\mathcal{L}^{\mathrm{inv}}(\phi)=\mathcal{L}^+(\psi)$ 且 $\mathcal{L}^+(\phi)=\mathcal{L}^{\mathrm{inv}}(\psi)$。

**证明**：
1. (a)$\Rightarrow$(e)：若 $L\in\mathcal{L}^+(\phi)$ 且 $\mathbf{d}(x,y)=\mathbf{0}$，由 $L_{ij}\cdot 0=0$ 得 $d_i(\phi(x),\phi(y))\le 0$，即 $\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$。
   (e)$\Rightarrow$(b)：设 (e) 成立，取 $x,y\in\mathrm{dom}(\phi)$。若 $\mathbf{d}(x,y)=\mathbf{0}$，则 $\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}=\boldsymbol{\infty}_{I\times I}\mathbf{0}$；若 $\mathbf{d}(x,y)\neq\mathbf{0}$，则存在 $j_0\in I$ 使 $d_{j_0}(x,y)>0$，故对一切 $i\in I$ 有 $(\boldsymbol{\infty}_{I\times I}\mathbf{d}(x,y))_i\ge(+\infty)\cdot d_{j_0}(x,y)=+\infty\ge d_i(\phi(x),\phi(y))$。故 $\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^+(\phi)$。
   (c)$\Rightarrow$(e)：若 $W\in\mathcal{K}(\phi)$ 且 $\mathbf{d}(x,y)=\mathbf{0}$，则对一切 $i$ 有 $(W\mathbf{d}(x,y))_i=0<1$，故 $d_i(\phi(x),\phi(y))=0$。
   (e)$\Rightarrow$(d)：若 $(\boldsymbol{\infty}_{I\times I}\mathbf{d}(x,y))_i<1$，则对一切 $j\in I$ 必有 $(+\infty)\cdot d_j(x,y)<1$，故 $d_j(x,y)=0$，即 $\mathbf{d}(x,y)=\mathbf{0}$，由 (e) 得 $d_i(\phi(x),\phi(y))=0$。显然 (b)$\Rightarrow$(a) 且 (d)$\Rightarrow$(c)。
2. 显然 $\mathbf{0}\,\mathbf{d}(x,y)=\mathbf{0}\le\mathbf{d}(\phi(x),\phi(y))$；$\boldsymbol{\infty}_{I\times I}$ 情形与 (1) 同理。
3. 将 (1) 中 $\mathbf{d}(x,y)$ 与 $\mathbf{d}(\phi(x),\phi(y))$ 互换即得。
4. $(\mathbf{0}\,\mathbf{d}(x,y))_i=0$ 对一切 $x,y$ 恒成立，且 $0<1$ 恒成立，故两条件均等价于 $\mathbf{d}(\phi(x),\phi(y))\equiv\mathbf{0}$。
5. 空定义域时全称命题空真；恒等算子直接代入检验（特别地 $(E_\infty\mathbf{d}(x,y))_i=(+\infty)\cdot d_i(x,y)<1\iff d_i(x,y)=0$）；互逆情形仅作变量代换 $u=\phi(x),v=\phi(y)$ 即得。 $\square$

---

### 3.2 序结构、凸性与拓扑闭性

**命题 3.2（单调性、凸性与限制单调性）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **序闭性**：$\mathcal{L}^+(\phi)$、$\mathcal{L}^{\mathrm{inv}}(\phi)$ 与 $\mathcal{K}(\phi)$ 在 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中是**上闭集**（若 $A$ 属于该族且 $A\le A'$，则 $A'$ 亦属于该族）；$\mathcal{L}^-(\phi)$ 是**下闭集**（若 $M\in\mathcal{L}^-(\phi)$ 且 $\mathbf{0}\le M'\le M$，则 $M'\in\mathcal{L}^-(\phi)$）。
2. **凸性**：四类矩阵族 $\mathcal{L}^+(\phi),\,\mathcal{L}^-(\phi),\,\mathcal{L}^{\mathrm{inv}}(\phi),\,\mathcal{K}(\phi)$ 均为**凸集**（对任意 $\lambda\in[0,1]$ 及同族两矩阵 $A_1,A_2$，$\lambda A_1+(1-\lambda)A_2$ 仍在族内）。
3. **定义域限制单调性**：对任意子集 $S\subseteq\mathcal{X}$，限制算子 $\phi|_S$ 满足 $\mathcal{C}(\phi)\subseteq\mathcal{C}(\phi|_S)$（$\mathcal{C}\in\{\mathcal{L}^+,\mathcal{L}^-,\mathcal{L}^{\mathrm{inv}},\mathcal{K}\}$）。

**证明**：
1. 由矩阵-向量乘法的保序性直接得 $\mathcal{L}^+,\mathcal{L}^-,\mathcal{L}^{\mathrm{inv}}$ 的序闭性。对 $\mathcal{K}(\phi)$：若 $W\in\mathcal{K}(\phi)$ 且 $W\le W'$，则 $(W'\mathbf{d})_i<1\implies(W\mathbf{d})_i\le(W'\mathbf{d})_i<1\implies d_i(\phi(x),\phi(y))=0$。
2. $\lambda\in\{0,1\}$ 平凡；设 $\lambda\in(0,1)$。对 $\mathcal{L}^+$、$\mathcal{L}^-$、$\mathcal{L}^{\mathrm{inv}}$，由命题 1.1(1) 的分配律及 $\lambda a+(1-\lambda)a=a$（对含 $+\infty$ 的一切 $a\in\bar{\mathbb{R}}_+$ 成立）立即得到。对 $\mathcal{K}(\phi)$：设 $W_1,W_2\in\mathcal{K}(\phi)$，$W=\lambda W_1+(1-\lambda)W_2$。若 $(W\mathbf{d}(x,y))_i=\lambda(W_1\mathbf{d}(x,y))_i+(1-\lambda)(W_2\mathbf{d}(x,y))_i<1$，则不可能同时有 $(W_1\mathbf{d}(x,y))_i\ge 1$ 与 $(W_2\mathbf{d}(x,y))_i\ge 1$（否则凸组合 $\ge\lambda+(1-\lambda)=1$，包括取 $+\infty$ 情形）。故必有其一严格小于 $1$，从而 $d_i(\phi(x),\phi(y))=0$。
3. 因 $\mathrm{dom}(\phi|_S)=S\cap\mathrm{dom}(\phi)\subseteq\mathrm{dom}(\phi)$，定义条件中全称量词的范围缩小。 $\square$

---

**命题 3.3（拓扑闭性、紧性与 $0\cdot(+\infty)=0$ 效应）**
在 $\mathcal{M}_I(\bar{\mathbb{R}}_+)=\bar{\mathbb{R}}_+^{I\times I}$ 的乘积序拓扑（紧致 Hausdorff 空间）下：
1. **$\mathcal{L}^-(\phi)$ 恒为闭集（从而紧致）**，无需对距离作任何有限性假设；特别地，每个 $M\in\mathcal{L}^-(\phi)$ 都可被 $\mathcal{L}^-(\phi)$ 中的某个极大元控制。
2. **若 $\mathrm{dom}(\phi)$ 上各距离均有限**（$\forall x,y\in\mathrm{dom}(\phi),\,\forall j\in I,\,d_j(x,y)<+\infty$），则 $\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)$ 均为**闭集（从而紧致）**；若 $\phi(\mathrm{dom}(\phi))$ 上各距离均有限，则 $\mathcal{L}^{\mathrm{inv}}(\phi)$ 为**闭集（从而紧致）**。此时非空族中的每个矩阵都控制着至少一个极小元。
3. **（无穷距离反例）** 当允许距离取 $+\infty$ 时，$\mathcal{L}^+(\phi),\,\mathcal{L}^{\mathrm{inv}}(\phi),\,\mathcal{K}(\phi)$ 未必在零元处封闭：取 $\mathcal{X}=\{a,b,\bot\}$，$|I|=1$，$d(a,b)=+\infty$，$\phi=\mathrm{id}_{\mathcal{X}}$，则
   $$
   \mathcal{L}^+(\phi)=\mathcal{L}^{\mathrm{inv}}(\phi)=\mathcal{K}(\phi)=(0,+\infty]\quad\text{（非闭）},
   \qquad \mathcal{L}^-(\phi)=[0,+\infty]\quad\text{（闭）}.
   $$

**证明**：
1. 设网（或序列，因空间可度量化）$M^{(n)}\in\mathcal{L}^-(\phi)$ 收敛于 $M$。对任意 $x,y\in\mathrm{dom}(\phi)$ 与 $i\in I$，由命题 1.1(3) 中 $a\mapsto a\cdot d_j(x,y)$ 的下半连续性，对每个 $j$ 有 $M_{ij}d_j(x,y)\le\liminf_{n\to\infty} M^{(n)}_{ij}d_j(x,y)$。对有限指标 $j\in I$ 求和，利用超可加性得
   $$
   (M\mathbf{d}(x,y))_i \le \liminf_{n\to\infty}(M^{(n)}\mathbf{d}(x,y))_i \le d_i\bigl(\phi(x),\phi(y)\bigr),
   $$
   故 $M\in\mathcal{L}^-(\phi)$。紧致空间上的闭子集紧致；由 Zorn 引理（任意全序上升链在闭集中有上确界极限），每个元都被极大元控制。
2. 设 $\mathrm{dom}(\phi)$ 上 $d_j(x,y)<+\infty$ 恒成立。
   - 若 $L^{(n)}\in\mathcal{L}^+(\phi)$ 且 $L^{(n)}\to L$，则由命题 1.1(3)，对每个 $j$ 有 $L^{(n)}_{ij}d_j(x,y)\to L_{ij}d_j(x,y)$，相加得 $(L\mathbf{d}(x,y))_i=\lim_n(L^{(n)}\mathbf{d}(x,y))_i\ge d_i(\phi(x),\phi(y))$，故 $L\in\mathcal{L}^+(\phi)$。
   - 若 $W^{(n)}\in\mathcal{K}(\phi)$ 且 $W^{(n)}\to W$，取满足 $(W\mathbf{d}(x,y))_i<1$ 的 $x,y\in\mathrm{dom}(\phi)$。对每个 $j\in I$：若 $d_j(x,y)=0$，则 $W^{(n)}_{ij}d_j(x,y)=0=W_{ij}d_j(x,y)$；若 $0<d_j(x,y)<+\infty$，由 $W_{ij}d_j(x,y)<1$ 必有 $W_{ij}<+\infty$，故 $W^{(n)}_{ij}d_j(x,y)\to W_{ij}d_j(x,y)$。于是 $\lim_{n\to\infty}(W^{(n)}\mathbf{d}(x,y))_i=(W\mathbf{d}(x,y))_i<1$，从而充分大 $n$ 时 $(W^{(n)}\mathbf{d}(x,y))_i<1$，推出 $d_i(\phi(x),\phi(y))=0$。故 $W\in\mathcal{K}(\phi)$。
   - $\mathcal{L}^{\mathrm{inv}}(\phi)$ 的闭性与 $\mathcal{L}^+(\phi)$ 完全对偶。
3. 在反例中，对 $(a,b)$，$+\infty\le L\cdot(+\infty)$ 与 $W\cdot(+\infty)<1\implies +\infty=0$ 均等价于 $L>0$、$W>0$；而 $+\infty\ge M\cdot(+\infty)$ 对一切 $M\in[0,+\infty]$ 成立。 $\square$

---

### 3.3 多分量非唯一极值性与可分解空间上的唯一极小矩阵

**命题 3.4（$|I|\ge 2$ 时唯一最优矩阵一般不存在）**
取 $\mathcal{X}=\{a,b,\bot\}$，$I=\{1,2\}$，$d_1(a,b)=d_2(a,b)=1$，$\phi=\mathrm{id}_{\mathcal{X}}$。令
$$
A_1=\begin{pmatrix}1&0\\1&0\end{pmatrix},\qquad A_2=\begin{pmatrix}0&1\\0&1\end{pmatrix}.
$$
则 $A_1,A_2$ 同为 $\mathcal{L}^+(\phi)$、$\mathcal{L}^{\mathrm{inv}}(\phi)$、$\mathcal{K}(\phi)$ 的极小元，但其逐元下确界 $A_1\wedge A_2=\mathbf{0}$ 均不属于这三个族；同时 $A_1,A_2$ 也同为 $\mathcal{L}^-(\phi)$ 的极大元，但其逐元上确界 $A_1\vee A_2=\begin{pmatrix}1&1\\1&1\end{pmatrix}$ 不属于 $\mathcal{L}^-(\phi)$（因 $1+1=2>1$）。 $\square$

然而，当有效定义域在各规范分量之间可以**独立分解**时（例如有限个伪度量空间的直积），$\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)$ 均恢复**唯一极小矩阵**！

**定义 3.5（分量可分解性）**
称子集 $S\subseteq\mathcal{X}$ 是**分量可分解的**，如果存在 $I$ 的某个排列 $(i_1,\dots,i_m)$，使得对任意 $x,y\in S$，存在链 $z_0=x,z_1,\dots,z_m=y\in S$，满足对每个 $r=1,\dots,m$：
$$
d_{i_r}(z_{r-1},z_r)\le d_{i_r}(x,y), \qquad \forall k\in I\setminus\{i_r\},\; d_k(z_{r-1},z_r)=0.
$$

对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$，定义其**偏上 Lipschitz 矩阵** $L^*(\phi)$ 与**偏坍缩率矩阵** $W^*(\phi)$（约定 $\sup\emptyset=0$）：
$$
L^*_{ij}(\phi) := \sup\left\{\,\frac{d_i(\phi(u),\phi(v))}{d_j(u,v)} \;\middle|\; u,v\in\mathrm{dom}(\phi),\; d_j(u,v)\in(0,+\infty),\; \forall k\neq j,\,d_k(u,v)=0\,\right\},
$$
$$
W^*_{ij}(\phi) := \sup\left\{\,\frac{1}{d_j(u,v)} \;\middle|\; u,v\in\mathrm{dom}(\phi),\; d_i(\phi(u),\phi(v))>0,\; d_j(u,v)\in(0,+\infty),\; \forall k\neq j,\,d_k(u,v)=0\,\right\}.
$$

**定理 3.6（分量可分解域上的唯一极小矩阵定理）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$ 在 $\mathrm{dom}(\phi)$ 上保持全零距离，且 $\mathrm{dom}(\phi)$ 分量可分解。
1. 对任意 $L\in\mathcal{L}^+(\phi)$ 恒有 $L\ge L^*(\phi)$，对任意 $W\in\mathcal{K}(\phi)$ 恒有 $W\ge W^*(\phi)$；且逐元下确界满足 $\inf\mathcal{L}^+(\phi)=L^*(\phi)$、$\inf\mathcal{K}(\phi)=W^*(\phi)$。
2. 若进一步 $\mathrm{dom}(\phi)$ 上各距离均有限（$\forall u,v\in\mathrm{dom}(\phi),\,\forall j\in I,\,d_j(u,v)<+\infty$），则
   $$
   L^*(\phi)\in\mathcal{L}^+(\phi), \qquad W^*(\phi)\in\mathcal{K}_{\mathrm{box}}(\phi)\subseteq\mathcal{K}(\phi),
   $$
   即 $L^*(\phi)$ 与 $W^*(\phi)$ 分别是 $\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)$ 的**唯一极小元**（且 $W^*(\phi)$ 甚至满足更强的盒式条件）。

**证明**：
- **下界性**：若 $L\in\mathcal{L}^+(\phi)$，取任一满足 $d_j(u,v)\in(0,+\infty)$ 且 $d_k(u,v)=0$（$\forall k\neq j$）的 $u,v\in\mathrm{dom}(\phi)$，则 $d_i(\phi(u),\phi(v))\le L_{ij}d_j(u,v)$，除以有限正数 $d_j(u,v)$ 即得 $L_{ij}\ge L^*_{ij}(\phi)$。同理，若 $W\in\mathcal{K}(\phi)$ 且该对还满足 $d_i(\phi(u),\phi(v))>0$，则必有 $W_{ij}d_j(u,v)=(W\mathbf{d}(u,v))_i\ge 1$，故 $W_{ij}\ge 1/d_j(u,v)$，从而 $W_{ij}\ge W^*_{ij}(\phi)$。
- **有限距离下的可达性（(2)）**：设 $\mathrm{dom}(\phi)$ 距离全有限。对任意 $x,y\in\mathrm{dom}(\phi)$，取分解链 $z_0=x,\dots,z_m=y\in\mathrm{dom}(\phi)$。
  - 对 $L^*(\phi)$：由三角不等式 $d_i(\phi(x),\phi(y))\le\sum_{r=1}^m d_i(\phi(z_{r-1}),\phi(z_r))$。对每个 $r$（记 $j=i_r$）：若 $d_j(z_{r-1},z_r)=0$，则 $\mathbf{d}(z_{r-1},z_r)=\mathbf{0}$，由全零距离保持性得 $d_i(\phi(z_{r-1}),\phi(z_r))=0=L^*_{ij}\cdot 0$；若 $0<d_j(z_{r-1},z_r)<+\infty$，由 $L^*_{ij}$ 定义得 $d_i(\phi(z_{r-1}),\phi(z_r))\le L^*_{ij}d_j(z_{r-1},z_r)\le L^*_{ij}d_j(x,y)$。求和即得 $d_i(\phi(x),\phi(y))\le(L^*(\phi)\mathbf{d}(x,y))_i$。
  - 对 $W^*(\phi)$：设 $\max_{j\in I} W^*_{ij}d_j(x,y)<1$。对每个 $r$（记 $j=i_r$），有 $W^*_{ij}d_j(z_{r-1},z_r)\le W^*_{ij}d_j(x,y)<1$。若 $d_j(z_{r-1},z_r)=0$，同上得 $d_i(\phi(z_{r-1}),\phi(z_r))=0$；若 $0<d_j(z_{r-1},z_r)<+\infty$，假设反证 $d_i(\phi(z_{r-1}),\phi(z_r))>0$，则由 $W^*_{ij}$ 定义有 $W^*_{ij}\ge 1/d_j(z_{r-1},z_r)$，从而 $W^*_{ij}d_j(z_{r-1},z_r)\ge 1$，矛盾！故对一切 $r$ 均有 $d_i(\phi(z_{r-1}),\phi(z_r))=0$，由三角不等式得 $d_i(\phi(x),\phi(y))=0$。故 $W^*(\phi)\in\mathcal{K}_{\mathrm{box}}(\phi)\subseteq\mathcal{K}(\phi)$。
- **一般情形的 $\inf$ 刻画（(1) 后半）**：即使允许 $d_j(u,v)=+\infty$，对任意 $\varepsilon>0$，将 $L^*(\phi)$（或 $W^*(\phi)$）中的全部 $0$ 元替换为 $\varepsilon$ 得到矩阵 $L^{(\varepsilon)}$（或 $W^{(\varepsilon)}$）。对任意分解链步骤，若 $d_j(z_{r-1},z_r)=+\infty$，则 $L^{(\varepsilon)}_{ij}\cdot(+\infty)=+\infty\ge d_i(\phi(z_{r-1}),\phi(z_r))$，且 $W^{(\varepsilon)}_{ij}\cdot(+\infty)=+\infty\not<1$（前提不触发）；有限步骤仍同上成立。故 $L^{(\varepsilon)}\in\mathcal{L}^+(\phi)$、$W^{(\varepsilon)}\in\mathcal{K}(\phi)$，令 $\varepsilon\downarrow 0$ 即得 $\inf\mathcal{L}^+(\phi)=L^*(\phi)$、$\inf\mathcal{K}(\phi)=W^*(\phi)$。 $\square$

**推论 3.7（单伪度量情形 $|I|=1$ 的精确还原）**
当 $|I|=1$ 且 $\mathrm{dom}(\phi)$ 上距离有限时（任意集合自动分量可分解），若 $\phi$ 保持零距离，则：
- $\mathcal{L}^+(\phi)=[L^*(\phi),+\infty]$，其中 $L^*(\phi)=\sup_{d(x,y)>0}\frac{d(\phi(x),\phi(y))}{d(x,y)}$ 为经典扩展 Lipschitz 常数；
- $\mathcal{L}^-(\phi)=[0,M^*(\phi)]$，其中 $M^*(\phi)=\inf_{d(x,y)>0}\frac{d(\phi(x),\phi(y))}{d(x,y)}$（约定 $\inf\emptyset=+\infty$）为经典反 Lipschitz 常数；
- 若 $\phi$ 还反射零距离且 $\phi(\mathrm{dom}(\phi))$ 距离有限，则 $\mathcal{L}^{\mathrm{inv}}(\phi)=[(M^*(\phi))^{-1},+\infty]$；
- $\mathcal{K}(\phi)=[W^*(\phi),+\infty]$，其中 $W^*(\phi)=(\Theta^*(\phi))^{-1}$，$\Theta^*(\phi):=\inf\{d(x,y)\mid x,y\in\mathrm{dom}(\phi),\,d(\phi(x),\phi(y))>0\}$ 恰为最大不可区分半径。 $\square$

---

## 四、算子复合演算与迭代性质

**引理 4.1（复合定义域控制）**
对任意 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$，有 $\psi\circ\phi\in\mathcal{X}_{\mathrm{op}}$，且
$$
\mathrm{dom}(\psi\circ\phi)=\phi^{-1}\bigl(\mathrm{dom}(\psi)\bigr)\subseteq\mathrm{dom}(\phi),
\qquad \phi\bigl(\mathrm{dom}(\psi\circ\phi)\bigr)\subseteq\mathrm{dom}(\psi).
$$

**证明**：$(\psi\circ\phi)(\bot)=\psi(\bot)=\bot$，故 $\psi\circ\phi\in\mathcal{X}_{\mathrm{op}}$。若 $x\in\mathrm{dom}(\psi\circ\phi)$，即 $\psi(\phi(x))\neq\bot$，则直接有 $\phi(x)\in\mathrm{dom}(\psi)$；又因 $\psi(\bot)=\bot$，故 $\bot\notin\mathrm{dom}(\psi)$，从而 $\phi(x)\neq\bot$，即 $x\in\mathrm{dom}(\phi)$。 $\square$

**定理 4.2（四类矩阵的复合演算律）**
设 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$，且 $L_\phi\in\mathcal{L}^+(\phi)$、$L_\psi\in\mathcal{L}^+(\psi)$、$M_\phi\in\mathcal{L}^-(\phi)$、$M_\psi\in\mathcal{L}^-(\psi)$、$B_\phi\in\mathcal{L}^{\mathrm{inv}}(\phi)$、$B_\psi\in\mathcal{L}^{\mathrm{inv}}(\psi)$、$W_\phi\in\mathcal{K}(\phi)$、$W_\psi\in\mathcal{K}(\psi)$。则：
1. **（上界协变律）** $L_\psi L_\phi \in \mathcal{L}^+(\psi\circ\phi)$；
2. **（前向下界协变律）** $M_\psi M_\phi \in \mathcal{L}^-(\psi\circ\phi)$；
3. **（反向界反变律）** $B_\phi B_\psi \in \mathcal{L}^{\mathrm{inv}}(\psi\circ\phi)$；
4. **（坍缩经上界拉回律）** $W_\psi L_\phi \in \mathcal{K}(\psi\circ\phi)$；
5. **（坍缩前推律）** $W_\psi\odot W_\phi \in \mathcal{K}(\psi\circ\phi)$ 且 $L_\psi\odot W_\phi \in \mathcal{K}(\psi\circ\phi)$；
6. **（分通道混合坍缩律）** 对固定行 $i\in I$ 及中间指标集 $I$ 的任意划分 $I=J_1\sqcup J_2$，定义行向量 $\mathbf{w}^{(i)}=(w_k)_{k\in I}$ 为
   $$
   w_k := \max\!\left(\max_{j\in J_1}\bigl(\mathrm{supp}((W_\psi)_{ij})\,(W_\phi)_{jk}\bigr),\;\sum_{j\in J_2}(W_\psi)_{ij}(L_\phi)_{jk}\right)
   $$
   （$J_1=\emptyset$ 时前项取 $0$），则 $\mathbf{w}^{(i)}\in\mathcal{K}_i(\psi\circ\phi)$。（取 $J_1=\emptyset$ 还原 (4)，取 $J_2=\emptyset$ 还原 (5) 前式。）

**证明**：
任取 $x,y\in\mathrm{dom}(\psi\circ\phi)$。由引理 4.1，$x,y\in\mathrm{dom}(\phi)$ 且 $\phi(x),\phi(y)\in\mathrm{dom}(\psi)$。利用命题 1.1(1) 中矩阵乘法的结合律与保序性：
1. $\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))\le L_\psi\mathbf{d}(\phi(x),\phi(y))\le L_\psi(L_\phi\mathbf{d}(x,y))=(L_\psi L_\phi)\mathbf{d}(x,y)$。
2. $\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))\ge M_\psi\mathbf{d}(\phi(x),\phi(y))\ge M_\psi(M_\phi\mathbf{d}(x,y))=(M_\psi M_\phi)\mathbf{d}(x,y)$。
3. $\mathbf{d}(x,y)\le B_\phi\mathbf{d}(\phi(x),\phi(y))\le B_\phi(B_\psi\mathbf{d}(\psi(\phi(x)),\psi(\phi(y))))=(B_\phi B_\psi)\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))$。
4. 若 $((W_\psi L_\phi)\mathbf{d}(x,y))_i<1$，则
   $$
   \bigl(W_\psi\mathbf{d}(\phi(x),\phi(y))\bigr)_i \le \bigl(W_\psi(L_\phi\mathbf{d}(x,y))\bigr)_i = \bigl((W_\psi L_\phi)\mathbf{d}(x,y)\bigr)_i < 1,
   $$
   由 $W_\psi\in\mathcal{K}(\psi)$ 得 $d_i(\psi(\phi(x)),\psi(\phi(y)))=0$。
5. 对 $L_\psi\odot W_\phi$：若 $((L_\psi\odot W_\phi)\mathbf{d}(x,y))_i<1$，则对每个满足 $(L_\psi)_{ij}>0$ 的 $j\in I$ 及每个 $k\in I$，有 $(W_\phi)_{jk}\le (L_\psi\odot W_\phi)_{ik}$，故 $(W_\phi\mathbf{d}(x,y))_j\le((L_\psi\odot W_\phi)\mathbf{d}(x,y))_i<1$，推出 $d_j(\phi(x),\phi(y))=0$。从而
   $$
   d_i\bigl(\psi(\phi(x)),\psi(\phi(y))\bigr) \le \sum_{j:\,(L_\psi)_{ij}>0}(L_\psi)_{ij}\cdot 0 + \sum_{j:\,(L_\psi)_{ij}=0} 0\cdot d_j(\phi(x),\phi(y)) = 0.
   $$
   $W_\psi\odot W_\phi$ 为 (6) 中 $J_2=\emptyset$ 的特例。
6. 设 $\sum_{k\in I} w_k d_k(x,y)<1$。对每个 $j\in J_1$：若 $(W_\psi)_{ij}>0$，则对所有 $k$ 有 $(W_\phi)_{jk}\le w_k$，故 $(W_\phi\mathbf{d}(x,y))_j\le\sum_k w_k d_k(x,y)<1$，得 $d_j(\phi(x),\phi(y))=0$，从而 $(W_\psi)_{ij}d_j(\phi(x),\phi(y))=0$；若 $(W_\psi)_{ij}=0$，此项亦为 $0$。对 $J_2$ 部分：
   $$
   \sum_{j\in J_2}(W_\psi)_{ij}d_j(\phi(x),\phi(y))
   \le \sum_{j\in J_2}(W_\psi)_{ij}\sum_{k\in I}(L_\phi)_{jk}d_k(x,y)
   = \sum_{k\in I}\!\left(\sum_{j\in J_2}(W_\psi)_{ij}(L_\phi)_{jk}\right)\!d_k(x,y)
   \le \sum_{k\in I} w_k d_k(x,y) < 1.
   $$
   两部分相加得 $(W_\psi\mathbf{d}(\phi(x),\phi(y)))_i<1$，故 $d_i(\psi(\phi(x)),\psi(\phi(y)))=0$。 $\square$

**推论 4.3（迭代幂律与“压缩 + 坍缩 $\implies$ 有限步合并”）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$ 与 $n\ge 1$：
1. 若 $L\in\mathcal{L}^+(\phi)$、$M\in\mathcal{L}^-(\phi)$、$B\in\mathcal{L}^{\mathrm{inv}}(\phi)$、$W\in\mathcal{K}(\phi)$，则
   $$
   L^n\in\mathcal{L}^+(\phi^n),\quad M^n\in\mathcal{L}^-(\phi^n),\quad B^n\in\mathcal{L}^{\mathrm{inv}}(\phi^n),\quad
   WL^{n-1},\,W^{\odot n},\,L^{\odot(n-1)}\odot W\in\mathcal{K}(\phi^n).
   $$
2. **（有限步精确不可区分定理）** 若存在全有限上界矩阵 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$ 满足谱半径 $\rho(L)<1$，且存在全有限不可区分矩阵 $W\in\mathcal{K}(\phi)\cap\mathbb{R}_+^{I\times I}$，则对任意满足 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$（各分量距离有限）的点对 $x,y\in\mathcal{X}$，存在仅依赖于 $L,W,\mathbf{d}(x,y)$ 的 $N\in\mathbb{N}$，使得对一切 $n\ge N$，只要 $x,y\in\mathrm{dom}(\phi^n)$，即有**精确零距离**：
   $$
   \mathbf{d}\bigl(\phi^n(x),\phi^n(y)\bigr)=\mathbf{0}.
   $$

**证明**：(1) 对 $n$ 归纳并反复应用定理 4.2 即得。(2) 由 $\rho(L)<1$ 知 $\lim_{n\to\infty}L^{n-1}=\mathbf{0}$。因 $W$ 与 $\mathbf{d}(x,y)$ 均为有限矩阵/向量，故 $\lim_{n\to\infty}WL^{n-1}\mathbf{d}(x,y)=\mathbf{0}$。取 $N\ge 1$ 使对一切 $n\ge N$ 与 $i\in I$ 有 $(WL^{n-1}\mathbf{d}(x,y))_i<1$；由 $WL^{n-1}\in\mathcal{K}(\phi^n)$ 即得 $\mathbf{d}(\phi^n(x),\phi^n(y))=\mathbf{0}$。 $\square$

> 这体现了 $L$ 与 $W$ 协同的实质威力：单凭谱半径 $\rho(L)<1$ 仅能得到渐近收敛 $\mathbf{d}(\phi^n(x),\phi^n(y))\to\mathbf{0}$，一旦配合有限坍缩矩阵 $W$，即通过复合律 $WL^{n-1}$ 自动提升为**有限步精确不可区分**。

---

## 五、四类矩阵之间的内在耦合与对偶关系

### 5.1 上界、前向下界与反向界的关系

**命题 5.1（双边夹逼与逐元有序）**
对任意 $M\in\mathcal{L}^-(\phi)$ 与 $L\in\mathcal{L}^+(\phi)$，有
$$
\forall x,y\in\mathrm{dom}(\phi),\qquad M\,\mathbf{d}(x,y)\le\mathbf{d}\bigl(\phi(x),\phi(y)\bigr)\le L\,\mathbf{d}(x,y).
$$
若对固定列指标 $j\in I$，存在 $x,y\in\mathrm{dom}(\phi)$ 满足 $0<d_j(x,y)<+\infty$ 且 $d_k(x,y)=0$（$\forall k\neq j$），则对所有 $i\in I$ 有 $M_{ij}\le L_{ij}$。（若存在 $d_j(x,y)=+\infty$ 且 $d_k(x,y)=0$（$\forall k\neq j$），则 $M_{ij}>0\implies L_{ij}>0$。） $\square$

**命题 5.2（$\mathcal{L}^-$ 与 $\mathcal{L}^{\mathrm{inv}}$ 的矩阵对偶）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. 若 $M\in\mathcal{L}^-(\phi)$ 且 $B\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 满足 $BM\ge E$，则 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$。特别地，若对每个 $j\in I$ 均存在 $i(j)\in I$ 使 $0<M_{i(j),j}<+\infty$，则令 $B_{j,i(j)}:=M_{i(j),j}^{-1}$、其余为 $0$，即得 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$。
2. 若 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$ 且 $M\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 满足 $MB\le E$，则 $M\in\mathcal{L}^-(\phi)$。
3. 当 $M$ 为正有限单项矩阵（带正有限权重的置换矩阵，含正对角矩阵）时，$M\in\mathcal{L}^-(\phi)\iff M^{-1}\in\mathcal{L}^{\mathrm{inv}}(\phi)$。

**证明**：
1. $\mathbf{d}(x,y)=E\mathbf{d}(x,y)\le(BM)\mathbf{d}(x,y)=B(M\mathbf{d}(x,y))\le B\mathbf{d}(\phi(x),\phi(y))$。特例中 $(BM)_{jj}=M_{i(j),j}^{-1}M_{i(j),j}=1$ 且非对角元 $\ge 0$，故 $BM\ge E$。
2. $M\mathbf{d}(x,y)\le M(B\mathbf{d}(\phi(x),\phi(y)))=(MB)\mathbf{d}(\phi(x),\phi(y))\le E\mathbf{d}(\phi(x),\phi(y))=\mathbf{d}(\phi(x),\phi(y))$。
3. 单项矩阵 $M$ 在 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中有精确非负逆 $M^{-1}$ 满足 $M^{-1}M=MM^{-1}=E$，结合 (1)(2) 即得。 $\square$

---

### 5.2 上 Lipschitz 矩阵与不可区分矩阵的支集等价及直径桥接

记 $\phi$ 在各输出分量上的**像集直径向量**为 $\mathbf{D}(\phi)=\bigl(D_i(\phi)\bigr)_{i\in I}\in\bar{\mathbb{R}}_+^I$，其中
$$
D_i(\phi) := \sup_{x,y\in\mathrm{dom}(\phi)} d_i\bigl(\phi(x),\phi(y)\bigr) \qquad (\sup\emptyset:=0).
$$

**定理 5.3（$\mathcal{L}^+$ 与 $\mathcal{K}$ 的直径桥接与依赖支集等价定理）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **（由上界诱导出零容忍坍缩）** 对任意 $L\in\mathcal{L}^+(\phi)$，有 $\infty\cdot\mathrm{supp}(L)\in\mathcal{K}(\phi)$。
2. **（直径桥接：由坍缩诱导出定量上界）** 对任意 $W\in\mathcal{K}(\phi)$，有
   $$
   \mathrm{diag}\bigl(\mathbf{D}(\phi)\bigr)\,W \in \mathcal{L}^+(\phi),
   $$
   从而亦有 $\infty\cdot\mathrm{supp}(W)\in\mathcal{L}^+(\phi)$。
3. **（依赖支集族精确相等）**
   $$
   \bigl\{\,\mathrm{supp}(L)\;\big|\;L\in\mathcal{L}^+(\phi)\,\bigr\}
   = \bigl\{\,\mathrm{supp}(W)\;\big|\;W\in\mathcal{K}(\phi)\,\bigr\}.
   $$

**证明**：
1. 设 $L\in\mathcal{L}^+(\phi)$，记 $\widetilde{W}:=\infty\cdot\mathrm{supp}(L)$。若 $(\widetilde{W}\mathbf{d}(x,y))_i<1$，则对一切满足 $L_{ij}>0$ 的 $j$ 必有 $(+\infty)\cdot d_j(x,y)<1$，即 $d_j(x,y)=0$。于是
   $$
   d_i\bigl(\phi(x),\phi(y)\bigr) \le \sum_{j:\,L_{ij}>0} L_{ij}\cdot 0 + \sum_{j:\,L_{ij}=0} 0\cdot d_j(x,y) = 0,
   $$
   故 $\widetilde{W}\in\mathcal{K}(\phi)$。
2. 设 $W\in\mathcal{K}(\phi)$，取 $x,y\in\mathrm{dom}(\phi)$ 与 $i\in I$。由半环分配律，$(\mathrm{diag}(\mathbf{D}(\phi))W\mathbf{d}(x,y))_i=D_i(\phi)\,(W\mathbf{d}(x,y))_i$。
   - 若 $(W\mathbf{d}(x,y))_i<1$，则由 $W\in\mathcal{K}(\phi)$ 得 $d_i(\phi(x),\phi(y))=0\le D_i(\phi)(W\mathbf{d}(x,y))_i$；
   - 若 $(W\mathbf{d}(x,y))_i\ge 1$，则 $d_i(\phi(x),\phi(y))\le D_i(\phi)=D_i(\phi)\cdot 1\le D_i(\phi)(W\mathbf{d}(x,y))_i$（当 $D_i(\phi)=0$ 时两边均为 $0$；当 $D_i(\phi)=+\infty$ 时右边为 $+\infty$）。
   故 $\mathrm{diag}(\mathbf{D}(\phi))W\in\mathcal{L}^+(\phi)$。又因 $D_i(\phi)W_{ij}\le (\infty\cdot\mathrm{supp}(W))_{ij}$ 恒成立，由上闭性得 $\infty\cdot\mathrm{supp}(W)\in\mathcal{L}^+(\phi)$。
3. 注意 $\mathrm{supp}(\infty\cdot\mathrm{supp}(A))=\mathrm{supp}(A)$，结合 (1)(2) 即得两集合互含。 $\square$

> 定理 5.3 表明：$\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)$ 刻画了**完全相同的分量依赖结构**（哪些输出分量忽略哪些输入分量），而在非零依赖通道上，二者分别给出互补的定量刻画——$L$ 刻画变动增长速率，$W$ 刻画归零坍缩尺度；并且当像集直径有限时，$W$ 直接通过 $\mathrm{diag}(\mathbf{D}(\phi))W$ 给出定量的 Lipschitz 上界估计。

---

### 5.3 下界矩阵与不可区分矩阵的相容约束

**命题 5.4（下界与坍缩的互斥/相容条件）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$，$W\in\mathcal{K}(\phi)$：
1. 对任意 $M\in\mathcal{L}^-(\phi)$、任意 $x,y\in\mathrm{dom}(\phi)$ 与 $i\in I$：
   $$
   \bigl(W\,\mathbf{d}(x,y)\bigr)_i < 1 \implies \bigl(M\,\mathbf{d}(x,y)\bigr)_i = 0.
   $$
   特别地，若存在 $\mathrm{dom}(\phi)$ 中的点对序列 $(x_n,y_n)$ 满足 $d_j(x_n,y_n)\in(0,+\infty)$、$d_j(x_n,y_n)\to 0$ 且 $d_k(x_n,y_n)=0$（$\forall k\neq j$），则
   $$
   M_{ij}>0 \implies W_{ij}=+\infty.
   $$
2. 对任意 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$，有
   $$
   B\odot W \in \mathcal{K}\bigl(\mathrm{id}_{\mathrm{dom}(\phi)}\bigr),
   $$
   其中 $\mathrm{id}_{\mathrm{dom}(\phi)}:=\mathrm{id}_{\mathcal{X}}|_{\mathrm{dom}(\phi)}\in\mathcal{X}_{\mathrm{op}}$。换言之，具有反向 Lipschitz 界的算子，其坍缩程度不可能超过定义域 $\mathrm{dom}(\phi)$ 自身的离散间隙。

**证明**：
1. 若 $(W\mathbf{d}(x,y))_i<1$，则 $0\le(M\mathbf{d}(x,y))_i\le d_i(\phi(x),\phi(y))=0$。在特例中，若 $W_{ij}<+\infty$，则充分大 $n$ 时 $(W\mathbf{d}(x_n,y_n))_i=W_{ij}d_j(x_n,y_n)<1$，迫使 $M_{ij}d_j(x_n,y_n)=0$，与 $M_{ij}>0,d_j(x_n,y_n)>0$ 矛盾。
2. 对任意 $x,y\in\mathrm{dom}(\phi)$ 与 $j\in I$，若 $((B\odot W)\mathbf{d}(x,y))_j<1$，则对每个满足 $B_{ji}>0$ 的 $i$ 及所有 $k\in I$ 均有 $W_{ik}\le(B\odot W)_{jk}$，从而 $(W\mathbf{d}(x,y))_i\le((B\odot W)\mathbf{d}(x,y))_j<1$，推出 $d_i(\phi(x),\phi(y))=0$。代入 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$ 得 $d_j(x,y)\le\sum_i B_{ji}d_i(\phi(x),\phi(y))=0$。 $\square$

---

## 六、不可区分矩阵的链连通刚性

由于伪度量满足三角不等式，不可区分条件在连续连通区域上具有强烈的**链传播刚性**——这是理解何时存在非平凡有限 $W_{ij}\in(0,+\infty)$ 的关键几何现象。

对行向量 $\mathbf{w}=(w_j)_{j\in I}\in\bar{\mathbb{R}}_+^I$ 及子集 $S\subseteq\mathcal{X}$，称 $x,y\in S$ 在 $S$ 中**$\mathbf{w}$-链连通**（记作 $x\equiv_{\mathbf{w},S} y$），如果存在有限点列 $z_0=x,z_1,\dots,z_N=y\in S$（$N\ge 1$），使对一切 $r=1,\dots,N$ 有 $\sum_{j\in I} w_j d_j(z_{r-1},z_r)<1$。易验 $\equiv_{\mathbf{w},S}$ 是 $S$ 上的等价关系。

**定理 6.1（链传播与纤维连通刚性定理）**
设 $W\in\mathcal{K}(\phi)$，记第 $i$ 行为 $\mathbf{w}_i=(W_{ij})_{j\in I}$，并记其有限元指标集为 $F_i:=\{j\in I\mid W_{ij}<+\infty\}$。
1. **（链传播）** 对任意 $x,y\in\mathrm{dom}(\phi)$，若 $x\equiv_{\mathbf{w}_i,\mathrm{dom}(\phi)} y$，则 $d_i(\phi(x),\phi(y))=0$。
2. **（纤维拓扑刚性）** 对 $x_0\in\mathrm{dom}(\phi)$，定义纤维
   $$
   \mathrm{Fib}_{I\setminus F_i}(x_0):=\bigl\{\,y\in\mathrm{dom}(\phi)\;\big|\;\forall k\in I\setminus F_i,\;d_k(x_0,y)=0\,\bigr\}.
   $$
   若 $\mathrm{Fib}_{I\setminus F_i}(x_0)$ 在 $\{d_j\}_{j\in F_i}$ 生成的伪度量拓扑下连通，则对一切 $y\in\mathrm{Fib}_{I\setminus F_i}(x_0)$ 均有 $d_i(\phi(x_0),\phi(y))=0$。特别地：
   - 若每个纤维 $\mathrm{Fib}_{I\setminus F_i}(x_0)$（$x_0\in\mathrm{dom}(\phi)$）均在上述拓扑下连通，则把 $W_{i,\cdot}$ 中全部有限正元归零所得行向量 $\tilde{\mathbf{w}}_i$（$j\in F_i$ 取 $0$，$j\notin F_i$ 取 $+\infty$）仍属于 $\mathcal{K}_i(\phi)$；
   - 当 $F_i=I$（即第 $i$ 行全有限）且 $\mathrm{dom}(\phi)$ 在 $\mathcal{G}$-拓扑下连通时，必有 $\mathbf{0}\in\mathcal{K}_i(\phi)$（输出分量 $i$ 全局坍缩）。

**证明**：
1. 设 $z_0=x,\dots,z_N=y\in\mathrm{dom}(\phi)$ 满足 $\sum_j W_{ij}d_j(z_{r-1},z_r)<1$，则由 $W\in\mathcal{K}(\phi)$ 得每步 $d_i(\phi(z_{r-1}),\phi(z_r))=0$，由三角不等式得 $d_i(\phi(x),\phi(y))\le\sum_{r=1}^N d_i(\phi(z_{r-1}),\phi(z_r))=0$。
2. 对纤维 $F:=\mathrm{Fib}_{I\setminus F_i}(x_0)$ 中任意两点 $y,z$ 及 $k\in I\setminus F_i$，由对称性与三角不等式有 $d_k(y,z)\le d_k(y,x_0)+d_k(x_0,z)=0$，从而 $\sum_{j\in I} W_{ij}d_j(y,z)=\sum_{j\in F_i} W_{ij}d_j(y,z)$。若 $F_i=\emptyset$，该和为 $0<1$，直接得 $d_i(\phi(x_0),\phi(y))=0$。若 $F_i\neq\emptyset$，对任一 $y\in F$，令
   $$
   U(y):=\Bigl\{\,z\in F\;\Big|\;\forall j\in F_i,\;W_{ij}d_j(y,z)<\frac{1}{|F_i|}\,\Bigr\}.
   $$
   因每个 $W_{ij}<+\infty$（$j\in F_i$），$U(y)$ 是有限个开 $d_j$-球（或全集 $F$）之交，故在 $\{d_j\}_{j\in F_i}$-拓扑中是 $y$ 的开邻域，且对任意 $z\in U(y)$ 有 $\sum_{j\in F_i}W_{ij}d_j(y,z)<1$，即 $y\equiv_{\mathbf{w}_i,\mathrm{dom}(\phi)} z$。由此知 $F$ 中每个 $\equiv_{\mathbf{w}_i,\mathrm{dom}(\phi)}$ 等价类既开又闭。由 $F$ 连通得 $F$ 整体与 $x_0$ 链连通，再由 (1) 得 $d_i(\phi(x_0),\phi(y))=0$。
   若此结论对一切 $x_0\in\mathrm{dom}(\phi)$ 成立，则 $\sum_j \tilde{w}_{ij}d_j(x,y)<1\iff \forall k\notin F_i,\,d_k(x,y)=0\iff y\in\mathrm{Fib}_{I\setminus F_i}(x)\implies d_i(\phi(x),\phi(y))=0$，故 $\tilde{\mathbf{w}}_i\in\mathcal{K}_i(\phi)$。 $F_i=I$ 时 $\mathrm{Fib}_\emptyset(x_0)=\mathrm{dom}(\phi)$ 且 $\tilde{\mathbf{w}}_i=\mathbf{0}$。 $\square$

> **几何启示**：定理 6.1 清晰划定了 $W$ 的非平凡区界：
> - 在全局连通空间的全定义域算子上，有限正坍缩率必然自发增强为 $0$（完全忽略该输入分量）；
> - 真正的**有限正坍缩率** $0<W_{ij}<+\infty$ 自然且广泛地出现在四类核心场景中：（a）**带安全间隔/拒绝域的偏算子**（CH1 用 $\bot$ 建模未定义间隔，使 $\mathrm{dom}(\phi)$ 不连通）；（b）**离散、聚类或图度量空间**（如 $\mathbb{Z}$、码字簇）；（c）**超度量/树/前缀空间**（$d(x,y)\le r$ 本身就是等价关系，无链传播扩张）；（d）**含 $+\infty$ 距离分支的扩展规范空间**。

---

## 七、典型算例验证

### 例 7.1（耦合线性映射 vs 坐标投影：揭示 $\mathcal{L}^-$ 与 $\mathcal{L}^{\mathrm{inv}}$ 的分化）

取 $\mathcal{X}=\mathbb{R}^2\cup\{\bot\}$，$d_1(x,y)=|x_1-y_1|$，$d_2(x,y)=|x_2-y_2|$（距离有限且分量可分解）。
1. 令 $\phi(x_1,x_2)=(x_1+x_2,\,x_1-x_2)$（$\phi(\bot)=\bot$）：
   - $\mathcal{L}^+(\phi)$ 有唯一极小元 $L^*(\phi)=\begin{pmatrix}1&1\\1&1\end{pmatrix}$；
   - 由 $x_1=\frac{1}{2}((x_1+x_2)+(x_1-x_2))$ 等得 $B=\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix}\in\mathcal{L}^{\mathrm{inv}}(\phi)$（双 Lipschitz 稳定）；
   - 取 $(1,-1)$ 与 $(0,0)$ 知 $d_1(\phi(x),\phi(y))=0$ 而 $d_1=d_2=1$，同理取 $(1,1)$ 得 $\mathcal{L}^-(\phi)=\{\mathbf{0}\}$；
   - 由定理 6.1（$\mathbb{R}^2$ 连通且两分量均非局部常值），$\mathcal{K}(\phi)=\{\boldsymbol{\infty}_{2\times 2}\}$。
2. 令 $\psi(x_1,x_2)=(2x_1,\,0)$（$\psi(\bot)=\bot$）：
   - 唯一极小上界 $L^*(\psi)=\begin{pmatrix}2&0\\0&0\end{pmatrix}$；
   - 唯一极大前向下界 $M^*(\psi)=\begin{pmatrix}2&0\\0&0\end{pmatrix}\in\mathcal{L}^-(\psi)$；
   - 因丢失第 2 分量（不反射零距离），$\mathcal{L}^{\mathrm{inv}}(\psi)=\emptyset$；
   - 唯一极小坍缩矩阵 $W^*(\psi)=\begin{pmatrix}+\infty&0\\0&0\end{pmatrix}$（输出 1 忽略输入 2，输出 2 全坍缩）。

### 例 7.2（带间隔的偏算子：验证非平凡有限 $W^*$、直径桥接与复合律）

在例 7.1 的空间 $\mathcal{X}=\mathbb{R}^2\cup\{\bot\}$ 上，定义带拒绝间隔 $(-1,1)$ 的混合算子：
$$
\phi(x_1,x_2) := \begin{cases}
\bigl(\tfrac{1}{2}x_1,\;\mathrm{sgn}(x_2)\bigr), & |x_2|\ge 1, \\
\bot, & |x_2|<1 \text{ 或 } (x_1,x_2)=\bot.
\end{cases}
$$
此时 $\mathrm{dom}(\phi)=\mathbb{R}\times\bigl((-\infty,-1]\cup[1,+\infty)\bigr)$ 仍分量可分解且距离全有限。按定理 3.6 直接计算：
- $L^*(\phi)=\begin{pmatrix}1/2&0\\0&1\end{pmatrix}$（第 2 分量极值在 $x_2=1,y_2=-1$ 处取到：$\frac{2}{2}=1$）；
- 极大前向下界 $M^*(\phi)=\begin{pmatrix}1/2&0\\0&0\end{pmatrix}$，而 $\mathcal{L}^{\mathrm{inv}}(\phi)=\emptyset$（因 $\phi(0,1)=\phi(0,2)$）；
- $W^*(\phi)=\begin{pmatrix}+\infty&0\\0&1/2\end{pmatrix}$（第 2 分量只要 $|x_2-y_2|<2$ 即必同号，输出完全不可区分；阈值半径 $\Theta^*_{22}=2$）。
- **验证直径桥接（定理 5.3）**：像集第 2 分量直径 $D_2(\phi)=2$，于是 $D_2(\phi)W^*_{22}=2\cdot\frac{1}{2}=1=L^*_{22}$，精确紧致！
- **验证复合律（定理 4.2）**：与缩放算子 $\eta(x_1,x_2)=(x_1,3x_2)$（$L_\eta=\mathrm{diag}(1,3)$）复合得 $(\phi\circ\eta)(x_1,x_2)=(\frac{1}{2}x_1,\mathrm{sgn}(3x_2))$（$|x_2|\ge 1/3$），公式给出
  $$
  W^*(\phi)\,L_\eta = \begin{pmatrix}+\infty&0\\0&1/2\end{pmatrix}\begin{pmatrix}1&0\\0&3\end{pmatrix} = \begin{pmatrix}+\infty&0\\0&3/2\end{pmatrix}\in\mathcal{K}(\phi\circ\eta),
  $$
  对应第 2 分量精确坍缩半径 $(3/2)^{-1}=2/3$。

### 例 7.3（超度量前缀截断与非分离空间障碍）

1. **超度量全定义域算子**：设 $\Sigma$ 为至少含两个字符的字母表，$\mathcal{X}=\Sigma^\omega\cup\{\bot\}$，取超度量 $d(u,v)=2^{-\mathrm{lcp}(u,v)}$（$\mathrm{lcp}(u,v)=\inf\{n\ge 0\mid u_n\neq v_n\}$，$2^{-\infty}:=0$）。令截断算子 $\phi_k(u)=(u_0,\dots,u_{k-1},s_0,s_0,\dots)$（$k\ge 1$，固定 $s_0\in\Sigma$）。则 $\phi_k$ 在 $\mathcal{X}\setminus\{\bot\}$ 上处处定义且非常值，并且
   $$
   \phi_k(u)\neq\phi_k(v)\iff \mathrm{lcp}(u,v)\le k-1 \iff d(u,v)\ge 2^{-(k-1)},
   $$
   此时 $d(\phi_k(u),\phi_k(v))=d(u,v)$。故 $L^*(\phi_k)=1$、$M^*(\phi_k)=0$、$W^*(\phi_k)=2^{k-1}$（即 $2^{k-1}d(u,v)<1\iff d(u,v)\le 2^{-k}\implies d(\phi_k(u),\phi_k(v))=0$）。
2. **非分离空间障碍**：取 $\mathcal{X}=\{a,b,c,\bot\}$，$|I|=1$，$d(a,b)=0$，$d(a,c)=d(b,c)=1$，定义 $\phi(a)=a,\phi(b)=c,\phi(c)=c,\phi(\bot)=\bot$。因 $d(a,b)=0$ 而 $d(\phi(a),\phi(b))=1>0$，算子破坏零距离保持性，由定理 3.1 知 $\mathcal{L}^+(\phi)=\mathcal{K}(\phi)=\emptyset$（即使允许 $+\infty$ 亦不存在，因为 $(+\infty)\cdot 0=0<1$），而 $\mathcal{L}^-(\phi)=\{0\}$。

---

## 八、四类算子矩阵核心性质对照总表

| 性质 | 上 Lipschitz $\mathcal{L}^+(\phi)$ | 前向下 Lipschitz $\mathcal{L}^-(\phi)$ | 反向 Lipschitz $\mathcal{L}^{\mathrm{inv}}(\phi)$ | 不可区分/坍缩 $\mathcal{K}(\phi)$ |
| :--- | :--- | :--- | :--- | :--- |
| **定义条件**（$\forall x,y\in\mathrm{dom}(\phi)$） | $\mathbf{d}(\phi(x),\phi(y))\le L\mathbf{d}(x,y)$ | $\mathbf{d}(\phi(x),\phi(y))\ge M\mathbf{d}(x,y)$ | $\mathbf{d}(x,y)\le B\mathbf{d}(\phi(x),\phi(y))$ | $(W\mathbf{d}(x,y))_i<1\implies d_i(\phi(x),\phi(y))=0$ |
| **非空充要条件** | 保持全零距离（等价于含 $\boldsymbol{\infty}$） | 恒非空（恒含 $\mathbf{0}$） | 反射全零距离（等价于含 $\boldsymbol{\infty}$） | 保持全零距离（等价于含 $\boldsymbol{\infty}$） |
| **含 $\mathbf{0}$ 充要条件** | 输出全局不可区分 | 恒成立 | $\mathrm{dom}(\phi)$ 全局不可区分 | 输出全局不可区分 |
| **序闭性与凸性** | 上闭、凸、行可分 | 下闭、凸、行可分 | 上闭、凸、行可分 | 上闭、凸、行可分 |
| **拓扑闭性（$\bar{\mathbb{R}}_+^{I\times I}$）** | $\mathrm{dom}(\phi)$ 距离有限时闭 | **恒闭且紧致** | $\phi(\mathrm{dom}(\phi))$ 距离有限时闭 | $\mathrm{dom}(\phi)$ 距离有限时闭 |
| **恒等算子 $\mathrm{id}_{\mathcal{X}}$** | 含 $E$ | 含 $E$ | 含 $E$ | 含 $E_\infty=\mathrm{diag}(+\infty)$ |
| **复合 $\psi\circ\phi$ 律** | $L_\psi L_\phi$（协变） | $M_\psi M_\phi$（协变） | $B_\phi B_\psi$（反变） | $W_\psi L_\phi$、$W_\psi\odot W_\phi$、$L_\psi\odot W_\phi$（及分通道混合律） |
| **关键跨类桥接** | $\infty\cdot\mathrm{supp}(L)\in\mathcal{K}$ | $M\mathbf{d}\le L\mathbf{d}$；$BM\ge E\Rightarrow B\in\mathcal{L}^{\mathrm{inv}}$ | $MB\le E\Rightarrow M\in\mathcal{L}^-$；$B\odot W\in\mathcal{K}(\mathrm{id}_{\mathrm{dom}})$ | $\mathrm{diag}(\mathbf{D}(\phi))W\in\mathcal{L}^+$；与 $\mathcal{L}^+$ 同支集族 |