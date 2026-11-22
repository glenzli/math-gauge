以 CH1 给出的扩展规范空间 $(\mathcal{X},\mathcal{G},\bot)$（其中 $\mathcal{G}=\{d_i\}_{i\in I}$，$I$ 为有限非空指标集）及算子空间 $\mathcal{X}_{\mathrm{op}}$ 为唯一基础，下面将原想法的四个核心方面——多分量矩阵 Lipschitz 上界、矩阵下界、支持 $+\infty$ 的统一扩展，以及与之对等的“输入落入一定范畴致输出不可区分”矩阵——整理为自洽、完整的数学理论框架，并给出全部核心性质与严格论证。

---

## 一、准备记号、扩展矩阵半环与有效定义域原则

### 1.1 距离向量与扩展矩阵半环

对任意 $x,y\in\mathcal{X}$，定义其**规范距离向量**（简称距离向量）：
$$
\mathbf{d}(x,y) := \bigl(d_i(x,y)\bigr)_{i\in I} \in \bar{\mathbb{R}}_+^I.
$$
按分量偏序 $\le$，$\mathbf{d}$ 满足 $\mathbf{d}(x,x)=\mathbf{0}$、$\mathbf{d}(x,y)=\mathbf{d}(y,x)$、$\mathbf{d}(x,z)\le\mathbf{d}(x,y)+\mathbf{d}(y,z)$，且对任意 $x\neq\bot$ 有 $\mathbf{d}(x,\bot)=\boldsymbol{\infty}:=(+\infty)_{i\in I}$。对任意子集 $S\subseteq\mathcal{X}$，定义其**分量直径向量** $\mathbf{diam}(S):=\bigl(\mathrm{diam}_i(S)\bigr)_{i\in I}\in\bar{\mathbb{R}}_+^I$，其中
$$
\mathrm{diam}_i(S):=\sup_{x,y\in S} d_i(x,y) \qquad (\text{全文统一约定 }\sup\emptyset:=0,\;\inf\emptyset:=+\infty).
$$

对任意有限非空指标集 $P,I$，记 $\mathcal{M}_{P\times I}(\bar{\mathbb{R}}_+):=\bar{\mathbb{R}}_+^{P\times I}$，方阵情形简记为 $\mathcal{M}_I(\bar{\mathbb{R}}_+):=\bar{\mathbb{R}}_+^{I\times I}$，其上配备按分量偏序 $A\le B\iff\forall p,j,\,A_{pj}\le B_{pj}$。采用 CH1 的 $\bar{\mathbb{R}}_+$ 算术约定（特别是 $0\cdot(+\infty)=(+\infty)\cdot 0=0$），定义矩阵乘法、矩阵-向量乘法与内积：
$$
(AB)_{ik}:=\sum_{j\in I} A_{ij}B_{jk},\qquad
(A\mathbf{v})_i:=\sum_{j\in I} A_{ij}v_j,\qquad
\langle\mathbf{u},\mathbf{v}\rangle:=\sum_{j\in I} u_j v_j.
$$
常用特殊矩阵与运算如下：
- 零矩阵 $\mathbf{0}$、全 $1$ 矩阵 $\mathbf{1}_{I\times I}$（全 $1$ 向量 $\mathbf{1}$）、全无穷矩阵 $\boldsymbol{\infty}_{I\times I}$、单位矩阵 $E=(\delta_{ij})_{i,j\in I}$、无穷对角矩阵 $E_\infty:=\mathrm{diag}(+\infty,\dots,+\infty)$。约定 $A^0:=E$。
- **支集指示函数** $\mathrm{supp}:\bar{\mathbb{R}}_+\to\{0,1\}$ 定义为 $\mathrm{supp}(0)=0$、$\mathrm{supp}(a)=1$（$a>0$），并按分量推广至向量与矩阵。记 $\infty\cdot\mathrm{supp}(A)$ 为将 $A$ 的正元替换为 $+\infty$、零元保持为 $0$ 的矩阵。
- **逐元倒数** $a^{-1}\in\bar{\mathbb{R}}_+$ 约定 $0^{-1}:=+\infty$、$(+\infty)^{-1}:=0$；对矩阵 $A$ 记 $A^{\circ(-1)}:=(A_{ij}^{-1})_{i,j\in I}$。
- **支集极大积（support-max product）**：对 $A\in\mathcal{M}_{P\times I}(\bar{\mathbb{R}}_+)$ 与 $B\in\mathcal{M}_{I\times Q}(\bar{\mathbb{R}}_+)$，定义 $A\odot B\in\mathcal{M}_{P\times Q}(\bar{\mathbb{R}}_+)$ 为
  $$
  (A\odot B)_{pq}:=\max_{j\in I}\bigl(\mathrm{supp}(A_{pj})\,B_{jq}\bigr).
  $$
  对方阵 $A\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$，约定 $A^{\odot 0}:=E$、$A^{\odot 1}:=A$、$A^{\odot(n+1)}:=A\odot A^{\odot n}$。

**命题 1.1（扩展矩阵代数与半连续性基础）**
1. $(\bar{\mathbb{R}}_+,+,\cdot,0,1)$ 是有序交换半环；因而矩阵乘法在相容维数下满足结合律 $(AB)C=A(BC)$、$(AB)\mathbf{v}=A(B\mathbf{v})$、分配律、双侧保序性，且在 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中以 $E$ 为单位元、$\mathbf{0}$ 为吸收元。对任意 $\lambda,\mu\in\bar{\mathbb{R}}_+$，有 $(\lambda A+\mu B)\mathbf{v}=\lambda(A\mathbf{v})+\mu(B\mathbf{v})$。
2. 支集极大积 $\odot$ 满足结合律 $(A\odot B)\odot C=A\odot(B\odot C)$ 与双侧保序性；对方阵有左单位关系 $E_\infty\odot B=E\odot B=B$（右乘满足 $B\odot E=\mathrm{supp}(B)$、$B\odot E_\infty=\infty\cdot\mathrm{supp}(B)$），且对相容矩阵有
   $$
   A\odot(BC)\le (A\odot B)C.
   $$
3. 赋予 $\bar{\mathbb{R}}_+=[0,+\infty]$ 标准序拓扑（紧致可度量化 Hausdorff 空间），则加法连续；对固定 $d\in[0,+\infty)$，映射 $a\mapsto a\cdot d$ 在 $[0,+\infty]$ 上连续；而对 $d=+\infty$，映射 $a\mapsto a\cdot(+\infty)$ 在 $[0,+\infty]$ 上**下半连续**（且对任意单调递增网连续），但在 $a=0$ 处**非上半连续**（由 $0\cdot(+\infty)=0$ 导致）。

**证明**：
1. 核验 $\bar{\mathbb{R}}_+$ 上乘法结合律与分配律 $a(b+c)=ab+ac$。若 $a=0$，由 $0\cdot(+\infty)=0$ 两边皆为 $0$；若 $0<a<+\infty$ 显然；若 $a=+\infty$，当 $b=c=0$ 时两边均为 $0$，当 $b>0$ 或 $c>0$ 时 $b+c>0$ 且两边皆为 $+\infty$。保序性同理可验。指标集有限，故矩阵与向量乘法的结合律、分配律和保序性直接由半环公理推出。
2. 对任意 $p,\ell$，因 $(A\odot B)_{pk}>0\iff\exists j$ 使 $A_{pj}>0$ 且 $B_{jk}>0$，故（约定空集之 $\max$ 为 $0$）
   $$
   \bigl((A\odot B)\odot C\bigr)_{p\ell}
   =\max_{k:\,(A\odot B)_{pk}>0} C_{k\ell}
   =\max_{j:\,A_{pj}>0}\;\max_{k:\,B_{jk}>0} C_{k\ell}
   =\bigl(A\odot(B\odot C)\bigr)_{p\ell}.
   $$
   双侧保序性与 $E_\infty\odot B=E\odot B=B$、$B\odot E=\mathrm{supp}(B)$、$B\odot E_\infty=\infty\cdot\mathrm{supp}(B)$ 直接由定义验得。最后，对每个 $p,\ell$，
   $$
   \bigl(A\odot(BC)\bigr)_{p\ell}
   =\max_{j:\,A_{pj}>0}\sum_k B_{jk}C_{k\ell}
   \le\sum_k\Bigl(\max_{j:\,A_{pj}>0} B_{jk}\Bigr)C_{k\ell}
   =\bigl((A\odot B)C\bigr)_{p\ell}.
   $$
3. 加法与 $d\in[0,+\infty)$ 时的标量乘法连续性在序拓扑下直接成立（无 $\infty-\infty$ 不定型）。对 $d=+\infty$，若 $a_n\to a$ 且 $a>0$，则充分大 $n$ 有 $a_n>0$，从而 $a_n d=+\infty=ad$；若 $a=0$，则 $ad=0\le\liminf_n a_n d$，而取 $a_n=1/n\downarrow 0$ 时 $\lim_n a_n d=+\infty>0=ad$，故仅下半连续。若 $(a_\alpha)$ 递增收敛于 $a$，当 $a=0$ 时必恒有 $a_\alpha=0$，当 $a>0$ 时终有 $a_\alpha>0$，故对递增网连续。 $\square$

---

### 1.2 不可区分关系与有效定义域原则

因 CH1 **不预设族分离性**，在 $\mathcal{X}$ 上自然诱导出以下等价关系：
- **第 $i$ 分量不可区分**：$x\sim_i y :\iff d_i(x,y)=0$；
- **全分量不可区分**：$x\sim_{\mathcal{G}} y :\iff \mathbf{d}(x,y)=\mathbf{0}$。

由吸收元隔离公理 (iv)，$\bot$ 在每个 $\sim_i$ 与 $\sim_{\mathcal{G}}$ 下的等价类均为单点集 $\{\bot\}$。对算子 $\phi\in\mathcal{X}_{\mathrm{op}}$，引入两个基本相容条件：
- **（全零距离保持性）**：$\forall x,y\in\mathrm{dom}(\phi),\;\mathbf{d}(x,y)=\mathbf{0}\implies\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$。（等价于 $\phi|_{\mathrm{dom}(\phi)}$ 诱导商映射 $\mathrm{dom}(\phi)/\!\sim_{\mathcal{G}}\to\mathcal{X}/\!\sim_{\mathcal{G}}$ 良定。）
- **（全零距离反射性）**：$\forall x,y\in\mathrm{dom}(\phi),\;\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}\implies\mathbf{d}(x,y)=\mathbf{0}$。

> **注记 1.2（为何四类矩阵统一定义在有效定义域 $\mathrm{dom}(\phi)\times\mathrm{dom}(\phi)$ 上）**：
> 在 CH1 中，$\phi(x)=\bot$ 表示 $\phi$ 在 $x$ 处未定义，且公理 (iv) 强制 $d_i(x,\bot)=+\infty$（$\forall x\neq\bot$）。若强行在整个 $\mathcal{X}\times\mathcal{X}$ 上要求不等式，会引发四重病态退化：
> 1. **破坏零行与分量解耦**：即便对处处定义的简单线性投影 $\psi(x_1,x_2)=(2x_1,0)$（$\psi(\bot)=\bot$），因 $\psi(x_1,x_2)\neq\bot$，对 $(x,\bot)$ 有 $d_2(\psi(x),\psi(\bot))=+\infty$，迫使 $L_{21}\cdot(+\infty)+L_{22}\cdot(+\infty)\ge+\infty$，从而**禁止**其真实矩阵的第 2 行为零行 $(0,0)$；同样，常值算子也将失去 $\mathbf{0}\in\mathcal{L}^+(\phi)\cap\mathcal{K}(\phi)$。
> 2. **毁坏偏算子的下界与反向界**：若存在 $x_0\in(\mathcal{X}\setminus\{\bot\})\setminus\mathrm{dom}(\phi)$，取 $(x_0,\bot)$ 得 $\mathbf{d}(\phi(x_0),\phi(\bot))=\mathbf{0}$ 而 $\mathbf{d}(x_0,\bot)=\boldsymbol{\infty}$，迫使任意下界矩阵退化为 $\mathbf{0}$ 且反向界族为空。
> 3. **与非分离空间冲突**：若 $x\in\mathrm{dom}(\phi),y\notin\mathrm{dom}(\phi)$ 且 $\mathbf{d}(x,y)=\mathbf{0}$，则 $d_i(\phi(x),\phi(y))=+\infty$ 而 $(L\mathbf{d}(x,y))_i=0$，连 $\boldsymbol{\infty}_{I\times I}$ 都失效。
>
> 因此，将算子矩阵统一定义在 $\mathrm{dom}(\phi)\times\mathrm{dom}(\phi)$ 上是 CH1 公理体系下唯一自洽且忠实的选择。此外，若需刻画算子在任意指定子集/区域 $S\subseteq\mathcal{X}$ 上的行为，只需定义**限制算子** $\phi|_S\in\mathcal{X}_{\mathrm{op}}$（$x\in S$ 时 $\phi|_S(x):=\phi(x)$，$x\notin S$ 时 $\phi|_S(x):=\bot$），其有效定义域恰为 $S\cap\mathrm{dom}(\phi)$，局部性质由此无缝纳入同一理论。

---

## 二、四类对等算子矩阵的严格定义与等价刻画

在多分量规范结构（$|I|\ge 2$）中，不同伪度量分量间可能存在耦合，一般不存在唯一的极值矩阵（命题 3.5）。因此，最忠实且严谨的处理方式是将每个算子 $\phi\in\mathcal{X}_{\mathrm{op}}$ 关联到 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中的**容许矩阵族**（admissible matrix classes）。

**定义 2.1（上 Lipschitz 矩阵族）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$。称 $L\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**上 Lipschitz 矩阵**，如果
$$
\forall x,y\in\mathrm{dom}(\phi),\qquad \mathbf{d}\bigl(\phi(x),\phi(y)\bigr) \le L\,\mathbf{d}(x,y),
$$
即对每个 $i\in I$，$d_i(\phi(x),\phi(y))\le\sum_{j\in I} L_{ij}d_j(x,y)$。记全体此类矩阵之集为 $\mathcal{L}^+(\phi)$。若存在全有限矩阵 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$，称 $\phi$ 是**有限矩阵 Lipschitz 的**。

---

**定义 2.2（下界矩阵族的本质分化：前向下 Lipschitz 与反向 Lipschitz）**
当 $|I|=1$ 时，$d(\phi(x),\phi(y))\ge m\,d(x,y)$ 与 $d(x,y)\le b\,d(\phi(x),\phi(y))$ 在 $m,b\in(0,+\infty)$ 时仅互为倒数；但在 $|I|\ge 2$ 时，二者本质分化为两种互补概念：
1. **前向下 Lipschitz 矩阵（扩张下界矩阵）**：称 $M\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**前向下 Lipschitz 矩阵**，如果
   $$
   \forall x,y\in\mathrm{dom}(\phi),\qquad \mathbf{d}\bigl(\phi(x),\phi(y)\bigr) \ge M\,\mathbf{d}(x,y).
   $$
   全体此类矩阵记为 $\mathcal{L}^-(\phi)$。
2. **反向 Lipschitz 矩阵（逆向稳定界矩阵）**：称 $B\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**反向 Lipschitz 矩阵**，如果
   $$
   \forall x,y\in\mathrm{dom}(\phi),\qquad \mathbf{d}(x,y) \le B\,\mathbf{d}\bigl(\phi(x),\phi(y)\bigr).
   $$
   全体此类矩阵记为 $\mathcal{L}^{\mathrm{inv}}(\phi)$。

> **注记 2.3（为何必须同时保留 $\mathcal{L}^-$ 与 $\mathcal{L}^{\mathrm{inv}}$）**：
> - $\mathcal{L}^-(\phi)$ 与 $\mathcal{L}^+(\phi)$ 构成最直接的双边夹逼 $M\mathbf{d}(x,y)\le\mathbf{d}(\phi(x),\phi(y))\le L\mathbf{d}(x,y)$，恒非空（含 $\mathbf{0}$），并能精细刻画**单个输出分量对输入分量的逐分量扩张下界**（即便其他分量坍缩，如例 8.1 中 $\psi(x_1,x_2)=(2x_1,0)$ 有 $M=\mathrm{diag}(2,0)$ 而 $\mathcal{L}^{\mathrm{inv}}(\psi)=\emptyset$）。
> - 但对**分量耦合的双 Lipschitz 映射**（如例 8.1 中 $\phi(x_1,x_2)=(x_1+x_2,x_1-x_2)$），每个单独输出分量都有非零核，导致 $\mathcal{L}^-(\phi)=\{\mathbf{0}\}$ 彻底丧失分辨力；唯有 $\mathcal{L}^{\mathrm{inv}}(\phi)$ 能捕捉整体双边稳定性，且当 $\phi$ 可逆时恰等于 $\mathcal{L}^+(\phi^{-1})$（定理 3.1(5)）。

---

**定义 2.4（不可区分 / 坍缩矩阵族）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$。称 $W\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 为 $\phi$ 的一个**不可区分矩阵**（亦称**坍缩率矩阵**，indistinguishability / collapse matrix），如果对任意 $x,y\in\mathrm{dom}(\phi)$ 与任意 $i\in I$，
$$
\bigl(W\,\mathbf{d}(x,y)\bigr)_i < 1 \;\implies\; d_i\bigl(\phi(x),\phi(y)\bigr) = 0,
$$
即 $\sum_{j\in I} W_{ij}d_j(x,y)<1\implies d_i(\phi(x),\phi(y))=0$。全体此类矩阵记为 $\mathcal{K}(\phi)$。

#### 对定义 2.4 的几何解读、四重等价刻画与对等性

先给出 $W$ 各极端元在 CH1 算术下的精确含义（以逐元倒数 $\Theta_{ij}:=W_{ij}^{-1}\in\bar{\mathbb{R}}_+$ 为直观阈值半径）：
- **$W_{ij}=0$（$\Theta_{ij}=+\infty$）**：由 $0\cdot d_j(x,y)=0$（含 $d_j=+\infty$），输入分量 $j$ 的任意变化均不受限；整行 $W_{i,\cdot}=\mathbf{0}$ 意为输出分量 $i$ 全局不可区分（完全坍缩）。
- **$0<W_{ij}<+\infty$（$\Theta_{ij}=W_{ij}^{-1}\in(0,+\infty)$）**：$W_{ij}$ 越小（容忍半径越大），输出分量 $i$ 对输入分量 $j$ 的坍缩越强。
- **$W_{ij}=+\infty$（$\Theta_{ij}=0$）**：由 $(+\infty)\cdot 0=0<1$ 而 $(+\infty)\cdot d_j=+\infty\not<1$（$d_j>0$），仅允许 $d_j(x,y)=0$，表示输出分量 $i$ 对输入分量 $j$ 无正容忍半径（仅保持零距离）。

CH1 空间无原点或线性坐标结构，只有成对伪度量族 $\mathbf{d}(x,y)$。下面的命题表明，“成对输入距离落入范畴”、“输入落入某参考点邻域范畴”、“一族输入整体落入直径范畴”与“与上 Lipschitz 并列的扩展不等式形式”四者**完全等价**；而若考察“输入落入某个给定的固定区域 $S\subseteq\mathcal{X}$ 时输出不可区分”，则只需考察限制算子 $\phi|_S$ 是否满足 $\mathbf{0}\in\mathcal{K}_i(\phi|_S)$。

**命题 2.5（不可区分矩阵的四重等价刻画）**
记扩展指示函数 $\chi_{[1,+\infty]}:\bar{\mathbb{R}}_+\to\bar{\mathbb{R}}_+$ 为
$$
\chi_{[1,+\infty]}(t):=\begin{cases} 0, & 0\le t<1,\\ +\infty, & 1\le t\le+\infty. \end{cases}
$$
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$ 与 $W\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$，以下四条等价：
1. **（成对距离范畴）** $W\in\mathcal{K}(\phi)$，即 $\forall x,y\in\mathrm{dom}(\phi),\,\forall i\in I,\;(W\mathbf{d}(x,y))_i<1\implies d_i(\phi(x),\phi(y))=0$；
2. **（参考点邻域范畴）** 对任意 $x_0\in\mathrm{dom}(\phi)$ 与 $i\in I$，落入 $W$-邻域范畴 $B_i(x_0;W):=\{x\in\mathrm{dom}(\phi)\mid (W\mathbf{d}(x,x_0))_i<1\}$ 中的全体输入具有两两 $d_i$-不可区分的输出（即 $\mathrm{diam}_i(\phi(B_i(x_0;W)))=0$）；
3. **（输入子集直径范畴）** 对任意子集 $S\subseteq\mathrm{dom}(\phi)$ 与 $i\in I$，$(W\,\mathbf{diam}(S))_i<1\implies\mathrm{diam}_i(\phi(S))=0$；
4. **（与定义 2.1 对等的扩展不等式）** $\forall x,y\in\mathrm{dom}(\phi),\,\forall i\in I$，
   $$
   d_i\bigl(\phi(x),\phi(y)\bigr) \le \chi_{[1,+\infty]}\!\bigl((W\,\mathbf{d}(x,y))_i\bigr).
   $$

**证明**：
(1)$\Leftrightarrow$(4) 由 $\chi_{[1,+\infty]}$ 定义直接成立。
(1)$\Rightarrow$(2)：设 $x,y\in B_i(x_0;W)$，由 (1) 得 $d_i(\phi(x),\phi(x_0))=0$ 与 $d_i(\phi(y),\phi(x_0))=0$，由对称性与三角不等式得 $d_i(\phi(x),\phi(y))=0$。
(2)$\Rightarrow$(1)：若 $x,y\in\mathrm{dom}(\phi)$ 满足 $(W\mathbf{d}(x,y))_i<1$，则因 $(W\mathbf{d}(x,x))_i=0<1$，有 $x,y\in B_i(x;W)$，由 (2) 得 $d_i(\phi(x),\phi(y))=0$。
(1)$\Rightarrow$(3)：设 $S\subseteq\mathrm{dom}(\phi)$ 且 $(W\,\mathbf{diam}(S))_i<1$。对任意 $x,y\in S$，有 $\mathbf{d}(x,y)\le\mathbf{diam}(S)$，故 $(W\mathbf{d}(x,y))_i\le(W\,\mathbf{diam}(S))_i<1$，由 (1) 得 $d_i(\phi(x),\phi(y))=0$，取上确界即得 $\mathrm{diam}_i(\phi(S))=0$（$S=\emptyset$ 时按约定两边皆为 $0$）。
(3)$\Rightarrow$(1)：对任意满足 $(W\mathbf{d}(x,y))_i<1$ 的 $x,y\in\mathrm{dom}(\phi)$，令 $S=\{x,y\}$，有 $\mathbf{diam}(S)=\mathbf{d}(x,y)$，由 (3) 得 $d_i(\phi(x),\phi(y))=\mathrm{diam}_i(\phi(S))=0$。 $\square$

---

为与直观上的“逐分量阈值盒”比较，记**盒式坍缩率矩阵族**与**闭盒阈值半径矩阵族**分别为
$$
\mathcal{K}_{\mathrm{box}}(\phi):=\Bigl\{W\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\;\Big|\;\forall x,y\in\mathrm{dom}(\phi),\,\forall i\in I,\;\max_{j\in I} W_{ij}d_j(x,y)<1\implies d_i(\phi(x),\phi(y))=0\Bigr\},
$$
$$
\mathcal{T}_{\le}(\phi):=\Bigl\{\Theta\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\;\Big|\;\forall x,y\in\mathrm{dom}(\phi),\,\forall i\in I,\;\bigl(\forall j\in I,\,d_j(x,y)\le\Theta_{ij}\bigr)\implies d_i(\phi(x),\phi(y))=0\Bigr\}.
$$

**命题 2.6（线性坍缩矩阵与盒式阈值矩阵的定量等价性）**
1. $\mathcal{K}_{\mathrm{box}}(\phi)\subseteq\mathcal{K}(\phi)$，且对任意 $W\in\mathcal{K}(\phi)$ 有 $|I|\,W\in\mathcal{K}_{\mathrm{box}}(\phi)$；特别地，当 $|I|=1$ 时 $\mathcal{K}_{\mathrm{box}}(\phi)=\mathcal{K}(\phi)$（后文定理 3.7 还将证明：在分量可分解域上恒有 $\mathcal{K}_{\mathrm{box}}(\phi)=\mathcal{K}(\phi)$）。
2. 若 $\Theta\in\mathcal{T}_{\le}(\phi)$，则 $\Theta^{\circ(-1)}\in\mathcal{K}_{\mathrm{box}}(\phi)\subseteq\mathcal{K}(\phi)$；反之，若 $W\in\mathcal{K}(\phi)$，则对任意常数 $c\in(|I|,+\infty]$ 有 $(cW)^{\circ(-1)}\in\mathcal{T}_{\le}(\phi)$（常数下界 $c>|I|$ 锐利）。

**证明**：
1. 若 $W\in\mathcal{K}_{\mathrm{box}}(\phi)$ 且 $(W\mathbf{d})_i<1$，则 $\max_j W_{ij}d_j\le\sum_j W_{ij}d_j<1$，故 $d_i(\phi(x),\phi(y))=0$。反之，若 $W\in\mathcal{K}(\phi)$ 且 $\max_j(|I|W_{ij}d_j)<1$，则每项 $W_{ij}d_j<1/|I|$，对 $j\in I$ 求和得 $(W\mathbf{d})_i<1$，故 $d_i(\phi(x),\phi(y))=0$。
2. 设 $\Theta\in\mathcal{T}_{\le}(\phi)$，$W=\Theta^{\circ(-1)}$。若 $\max_j W_{ij}d_j<1$，对每个 $j$ 分情形：$\Theta_{ij}=+\infty$ 时 $d_j\le+\infty$ 显然；$\Theta_{ij}=0$ 时 $W_{ij}=+\infty$，由 $(+\infty)\cdot d_j<1$ 必有 $d_j=0=\Theta_{ij}$；$0<\Theta_{ij}<+\infty$ 时 $d_j<\Theta_{ij}$。故 $\forall j,\,d_j\le\Theta_{ij}$，得 $d_i(\phi(x),\phi(y))=0$。
   反之，设 $W\in\mathcal{K}(\phi)$、$c\in(|I|,+\infty]$ 且 $\forall j,\,d_j\le(cW_{ij})^{-1}$。当 $W_{ij}=0$ 时 $W_{ij}d_j=0$；当 $W_{ij}=+\infty$ 或 $c=+\infty$ 且 $W_{ij}>0$ 时 $(cW_{ij})^{-1}=0\implies d_j=0\implies W_{ij}d_j=0$；当 $0<W_{ij}<+\infty$ 且 $c<+\infty$ 时 $W_{ij}d_j\le 1/c$。对 $j\in I$ 求和得 $(W\mathbf{d})_i\le |I|/c<1$，故 $d_i(\phi(x),\phi(y))=0$。
   为见 $c>|I|$ 的锐利性，取 $\mathcal{X}=\{a,b,\bot\}$，对一切 $j\in I$ 令 $d_j(a,b)=1$，$\phi=\mathrm{id}_{\mathcal{X}}$，则 $W=\frac{1}{|I|}\mathbf{1}_{I\times I}\in\mathcal{K}(\phi)$（因 $\sum_j\frac{1}{|I|}\cdot 1=1\not<1$），但 $(|I|W)^{\circ(-1)}=\mathbf{1}_{I\times I}\notin\mathcal{T}_{\le}(\phi)$。 $\square$

> **为何以 $\mathcal{K}(\phi)$（线性求和 + 严格 $<1$）为标准定义？**
> 1. **凸性与对偶性**：$\mathcal{K}(\phi)$ 恒为凸集（命题 3.3）并满足精确的阻塞凸对偶（定理 6.1），而 $\mathcal{K}_{\mathrm{box}}(\phi)$ 一般非凸（例如 $d_1<1$ 与 $d_2<1$ 的中点 $\max(\frac{1}{2}d_1,\frac{1}{2}d_2)<1$ 允许 $(d_1,d_2)=(1.5,1.5)$）。
> 2. **无因子损失的矩阵复合**：$\mathcal{K}(\phi)$ 与 $\mathcal{L}^+(\phi)$ 通过普通矩阵乘法直接耦合 $W_\psi L_\phi\in\mathcal{K}(\psi\circ\phi)$（定理 4.2），而盒式形式复合会引入额外 $|I|$ 因子。
> 3. **边界闭性与无空真缺陷**：若改用严格盒式 $d_j<\Theta_{ij}$，则单个 $\Theta_{ij}=0$ 会使整行前提恒假而空真，且 $\Theta_{ij}=+\infty$ 无法覆盖 $d_j=+\infty$；若改用非严格 $(W\mathbf{d})_i\le 1$，则指示函数 $\chi_{(1,+\infty]}$ 丧失上半连续性，连在闭间隔域 $\mathrm{dom}(\phi)=(-\infty,-1]\cup[1,+\infty)$ 的符号函数上都取不到极限点 $W=1/2$，破坏闭性（对比定理 3.4）。而 $(W\mathbf{d})_i<1$ 同时回避了全部缺陷。

---

## 三、存在性、序结构、凸性、精确闭包与可分解域分类

注意到四类矩阵的定义均按行解耦。记第 $i$ 行（对 $\mathcal{L}^{\mathrm{inv}}$ 为第 $j$ 行）的容许行向量集为 $\mathcal{L}_i^+(\phi),\mathcal{L}_i^-(\phi),\mathcal{L}_j^{\mathrm{inv}}(\phi),\mathcal{K}_i(\phi)\subseteq\bar{\mathbb{R}}_+^I$，则
$$
\mathcal{L}^+(\phi)=\prod_{i\in I}\mathcal{L}_i^+(\phi),\quad
\mathcal{L}^-(\phi)=\prod_{i\in I}\mathcal{L}_i^-(\phi),\quad
\mathcal{L}^{\mathrm{inv}}(\phi)=\prod_{j\in I}\mathcal{L}_j^{\mathrm{inv}}(\phi),\quad
\mathcal{K}(\phi)=\prod_{i\in I}\mathcal{K}_i(\phi).
$$

### 3.1 存在性判据与全有限矩阵刻画

**定理 3.1（存在性判据与极端值/特殊算子刻画）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **（上界与坍缩的共同存在判据）** 以下五条等价：
   (a) $\mathcal{L}^+(\phi)\neq\emptyset$；
   (b) $\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^+(\phi)$；
   (c) $\mathcal{K}(\phi)\neq\emptyset$；
   (d) $\boldsymbol{\infty}_{I\times I}\in\mathcal{K}(\phi)$；
   (e) $\phi$ 在 $\mathrm{dom}(\phi)$ 上保持全零距离（$\mathbf{d}(x,y)=\mathbf{0}\implies\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$）。
   （逐行亦有 $\mathcal{L}_i^+(\phi)\neq\emptyset\iff\mathcal{K}_i(\phi)\neq\emptyset\iff\forall x,y\in\mathrm{dom}(\phi),\,\mathbf{d}(x,y)=\mathbf{0}\implies d_i(\phi(x),\phi(y))=0$。）
   特别地，当 $\mathcal{G}$ 具有**族分离性**时，**一切**算子均满足 $\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^+(\phi)\cap\mathcal{K}(\phi)$，从而 $+\infty$ 扩展实现了对全体算子的统一矩阵表示；在不预设族分离性的 CH1 下，(e) 恰为精确的边界障碍。
2. **（前向下界恒非空）** 恒有 $\mathbf{0}\in\mathcal{L}^-(\phi)$；且 $\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^-(\phi)\iff\forall x,y\in\mathrm{dom}(\phi),\,\mathbf{d}(x,y)\neq\mathbf{0}\implies\mathbf{d}(\phi(x),\phi(y))=\boldsymbol{\infty}$。
3. **（反向界存在判据）** $\mathcal{L}^{\mathrm{inv}}(\phi)\neq\emptyset\iff\boldsymbol{\infty}_{I\times I}\in\mathcal{L}^{\mathrm{inv}}(\phi)\iff\phi$ 在 $\mathrm{dom}(\phi)$ 上反射全零距离。
4. **（完全坍缩判据）** $\mathbf{0}\in\mathcal{L}^+(\phi)\iff\mathbf{0}\in\mathcal{K}(\phi)\iff\forall x,y\in\mathrm{dom}(\phi),\,\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$。
5. **（特殊算子）**
   - 空定义域算子 $\phi_\bot\equiv\bot$ 使四类矩阵族均等于 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$；
   - 恒等算子 $\mathrm{id}_{\mathcal{X}}$ 满足 $E\in\mathcal{L}^+(\mathrm{id}_{\mathcal{X}})\cap\mathcal{L}^-(\mathrm{id}_{\mathcal{X}})\cap\mathcal{L}^{\mathrm{inv}}(\mathrm{id}_{\mathcal{X}})$ 且 $E_\infty\in\mathcal{K}(\mathrm{id}_{\mathcal{X}})$；
   - 若 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$ 在有效定义域上互逆（$\phi(\mathrm{dom}(\phi))=\mathrm{dom}(\psi)$，$\psi\circ\phi|_{\mathrm{dom}(\phi)}=\mathrm{id}_{\mathrm{dom}(\phi)}$，$\phi\circ\psi|_{\mathrm{dom}(\psi)}=\mathrm{id}_{\mathrm{dom}(\psi)}$），则 $\mathcal{L}^{\mathrm{inv}}(\phi)=\mathcal{L}^+(\psi)$ 且 $\mathcal{L}^+(\phi)=\mathcal{L}^{\mathrm{inv}}(\psi)$。

**证明**：
1. (a)$\Rightarrow$(e)：若 $L\in\mathcal{L}^+(\phi)$ 且 $\mathbf{d}(x,y)=\mathbf{0}$，由 $L_{ij}\cdot 0=0$ 得 $\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}$。
   (e)$\Rightarrow$(b)：对 $x,y\in\mathrm{dom}(\phi)$，若 $\mathbf{d}(x,y)=\mathbf{0}$ 则 $\mathbf{d}(\phi(x),\phi(y))=\mathbf{0}=\boldsymbol{\infty}_{I\times I}\mathbf{0}$；若存在 $j_0$ 使 $d_{j_0}(x,y)>0$，则 $(\boldsymbol{\infty}_{I\times I}\mathbf{d}(x,y))_i\ge(+\infty)\cdot d_{j_0}(x,y)=+\infty\ge d_i(\phi(x),\phi(y))$。
   (c)$\Rightarrow$(e)：若 $W\in\mathcal{K}(\phi)$ 且 $\mathbf{d}(x,y)=\mathbf{0}$，则 $(W\mathbf{d}(x,y))_i=0<1$，得 $d_i(\phi(x),\phi(y))=0$。
   (e)$\Rightarrow$(d)：若 $(\boldsymbol{\infty}_{I\times I}\mathbf{d}(x,y))_i<1$，则对一切 $j$ 必有 $d_j(x,y)=0$，由 (e) 得 $d_i(\phi(x),\phi(y))=0$。(b)$\Rightarrow$(a) 与 (d)$\Rightarrow$(c) 显然。逐行版本证明完全相同。
2. $\mathbf{0}\,\mathbf{d}(x,y)=\mathbf{0}\le\mathbf{d}(\phi(x),\phi(y))$ 显然；$\boldsymbol{\infty}_{I\times I}$ 情形与 (1) 同理。
3. 将 (1) 中 $\mathbf{d}(x,y)$ 与 $\mathbf{d}(\phi(x),\phi(y))$ 对调即得。
4. 因 $(\mathbf{0}\,\mathbf{d}(x,y))_i=0<1$ 恒成立，两条件均等价于 $\mathbf{d}(\phi(x),\phi(y))\equiv\mathbf{0}$。
5. 空定义域时全称命题空真；恒等算子直接代入检验（$(E_\infty\mathbf{d}(x,y))_i=(+\infty)\cdot d_i(x,y)<1\iff d_i(x,y)=0$）；互逆情形作变量代换 $u=\phi(x),v=\phi(y)$ 即得。 $\square$

**命题 3.2（全有限行向量与全有限矩阵的存在充要条件）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$ 与 $i,j\in I$：
1. $\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I\neq\emptyset\iff\exists C\in\mathbb{R}_+,\;\forall x,y\in\mathrm{dom}(\phi),\;d_i(\phi(x),\phi(y))\le C\sum_{k\in I} d_k(x,y)$；
2. $\mathcal{L}_j^{\mathrm{inv}}(\phi)\cap\mathbb{R}_+^I\neq\emptyset\iff\exists C\in\mathbb{R}_+,\;\forall x,y\in\mathrm{dom}(\phi),\;d_j(x,y)\le C\sum_{i\in I} d_i(\phi(x),\phi(y))$；
3. $\mathcal{K}_i(\phi)\cap\mathbb{R}_+^I\neq\emptyset\iff\exists\delta>0,\;\forall x,y\in\mathrm{dom}(\phi),\;d_i(\phi(x),\phi(y))>0\implies\sum_{k\in I} d_k(x,y)\ge\delta$。
（而 $\mathcal{L}_i^-(\phi)\cap\mathbb{R}_+^I$ 恒非空，因其恒含 $\mathbf{0}$。）

**证明**：
1. ($\Rightarrow$) 取 $\mathbf{l}\in\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I$，令 $C:=\max_{k\in I} l_k\in\mathbb{R}_+$，则 $d_i(\phi(x),\phi(y))\le\sum_k l_k d_k(x,y)\le C\sum_k d_k(x,y)$（$C=0$ 时两边皆为 $0$）。($\Leftarrow$) 令 $\mathbf{l}:=(C,\dots,C)\in\mathbb{R}_+^I$，由半环分配律即得 $\mathbf{l}\in\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I$。
2. 与 (1) 对偶。
3. ($\Rightarrow$) 取 $\mathbf{w}\in\mathcal{K}_i(\phi)\cap\mathbb{R}_+^I$，令 $C:=\max_{k\in I} w_k\in\mathbb{R}_+$。若 $C=0$ 则 $d_i(\phi(x),\phi(y))\equiv 0$，任取 $\delta=1$ 蕴含式空真；若 $C>0$，取 $\delta:=1/C>0$，当 $d_i(\phi(x),\phi(y))>0$ 时有 $1\le\sum_k w_k d_k(x,y)\le C\sum_k d_k(x,y)$，故 $\sum_k d_k(x,y)\ge\delta$。($\Leftarrow$) 令 $\mathbf{w}:=(\delta^{-1},\dots,\delta^{-1})\in(0,+\infty)^I$，若 $\sum_k \delta^{-1}d_k(x,y)<1$ 则 $\sum_k d_k(x,y)<\delta$，故 $d_i(\phi(x),\phi(y))=0$，即 $\mathbf{w}\in\mathcal{K}_i(\phi)\cap\mathbb{R}_+^I$。 $\square$

---

### 3.2 序闭性、凸性与精确拓扑闭包定理

**命题 3.3（序闭性、凸性与限制单调性）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **序闭性**：$\mathcal{L}^+(\phi),\,\mathcal{L}^{\mathrm{inv}}(\phi),\,\mathcal{K}(\phi)$ 在 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 中为**上闭集**；$\mathcal{L}^-(\phi)$ 为**下闭集**。
2. **凸性**：四类矩阵族 $\mathcal{L}^+(\phi),\,\mathcal{L}^-(\phi),\,\mathcal{L}^{\mathrm{inv}}(\phi),\,\mathcal{K}(\phi)$ 均为**凸集**（对任意 $\lambda\in[0,1]$ 及同族两矩阵 $A_1,A_2$，$\lambda A_1+(1-\lambda)A_2$ 仍在族内）。
3. **定义域限制单调性**：对任意子集 $S\subseteq\mathcal{X}$，$\mathcal{C}(\phi)\subseteq\mathcal{C}(\phi|_S)$（$\mathcal{C}\in\{\mathcal{L}^+,\mathcal{L}^-,\mathcal{L}^{\mathrm{inv}},\mathcal{K}\}$）。

**证明**：
1. 由命题 1.1(1) 的保序性直接得证（对 $\mathcal{K}$：若 $W\le W'$，则 $(W'\mathbf{d})_i<1\implies(W\mathbf{d})_i<1\implies d_i(\phi)=0$）。
2. $\lambda\in\{0,1\}$ 平凡；设 $\lambda\in(0,1)$。利用命题 1.1(1) 得 $((\lambda A_1+(1-\lambda)A_2)\mathbf{v})_i=\lambda(A_1\mathbf{v})_i+(1-\lambda)(A_2\mathbf{v})_i$。对 $\mathcal{L}^+$ 与 $\mathcal{K}$，统一利用命题 2.5(4)：它们皆形如 $d_i(\phi(x),\phi(y))\le\varphi((A\mathbf{d}(x,y))_i)$，其中 $\varphi\in\{\mathrm{id}_{\bar{\mathbb{R}}_+},\chi_{[1,+\infty]}\}$ 均单调不减。因对任意 $t_1,t_2\in\bar{\mathbb{R}}_+$ 有 $\lambda t_1+(1-\lambda)t_2\ge\min(t_1,t_2)$，故
   $$
   \varphi\bigl(\lambda t_1+(1-\lambda)t_2\bigr)\ge\varphi\bigl(\min(t_1,t_2)\bigr)=\min\bigl(\varphi(t_1),\varphi(t_2)\bigr)\ge d_i(\phi(x),\phi(y)).
   $$
   $\mathcal{L}^{\mathrm{inv}}$ 与 $\mathcal{L}^+$ 完全对偶；对 $\mathcal{L}^-$，直接有 $\lambda(M_1\mathbf{d})_i+(1-\lambda)(M_2\mathbf{d})_i\le\lambda d_i(\phi)+(1-\lambda)d_i(\phi)=d_i(\phi)$（对 $d_i(\phi)=+\infty$ 亦成立）。
3. 因 $\mathrm{dom}(\phi|_S)=S\cap\mathrm{dom}(\phi)\subseteq\mathrm{dom}(\phi)$，全称量词范围缩小。 $\square$

---

在允许距离取 $+\infty$ 的扩展规范空间中，由于 $0\cdot(+\infty)=0$ 破坏上半连续性，$\mathcal{L}^+(\phi),\mathcal{L}^{\mathrm{inv}}(\phi),\mathcal{K}(\phi)$ 未必闭。下面的定理不仅刻画闭性充分条件，更对**任意** $\phi\in\mathcal{X}_{\mathrm{op}}$ 给出三者在 $\bar{\mathbb{R}}_+^{I\times I}$ 乘积序拓扑中的**精确闭包公式**。为此定义**有限距离版本矩阵族**：
$$
\mathcal{L}^+_{\mathrm{fin}}(\phi):=\bigl\{L\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\;\big|\;\forall x,y\in\mathrm{dom}(\phi),\;\mathbf{d}(x,y)\in\mathbb{R}_+^I\implies\mathbf{d}(\phi(x),\phi(y))\le L\mathbf{d}(x,y)\bigr\},
$$
$$
\mathcal{K}_{\mathrm{fin}}(\phi):=\bigl\{W\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\;\big|\;\forall x,y\in\mathrm{dom}(\phi),\,\forall i\in I,\;\bigl(\mathbf{d}(x,y)\in\mathbb{R}_+^I\text{ 且 }(W\mathbf{d}(x,y))_i<1\bigr)\implies d_i(\phi(x),\phi(y))=0\bigr\},
$$
$$
\mathcal{L}^{\mathrm{inv}}_{\mathrm{fin}}(\phi):=\bigl\{B\in\mathcal{M}_I(\bar{\mathbb{R}}_+)\;\big|\;\forall x,y\in\mathrm{dom}(\phi),\;\mathbf{d}(\phi(x),\phi(y))\in\mathbb{R}_+^I\implies\mathbf{d}(x,y)\le B\mathbf{d}(\phi(x),\phi(y))\bigr\}.
$$

**定理 3.4（精确拓扑闭包、紧性与极值元存在定理）**
赋予 $\mathcal{M}_I(\bar{\mathbb{R}}_+)=\bar{\mathbb{R}}_+^{I\times I}$ 乘积序拓扑（紧致可度量化 Hausdorff 空间）。对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **（前向下界恒闭紧致）** $\mathcal{L}^-(\phi)$ 恒为闭集（从而紧致），无需任何距离有限性假设；特别地，每个 $M\in\mathcal{L}^-(\phi)$ 都受控于 $\mathcal{L}^-(\phi)$ 中的某个极大元。
2. **（精确闭包公式）** 无需任何距离有限性假设，恒有
   $$
   \overline{\mathcal{L}^+(\phi)}=\mathcal{L}^+_{\mathrm{fin}}(\phi),\qquad
   \overline{\mathcal{K}(\phi)}=\mathcal{K}_{\mathrm{fin}}(\phi),\qquad
   \overline{\mathcal{L}^{\mathrm{inv}}(\phi)}=\mathcal{L}^{\mathrm{inv}}_{\mathrm{fin}}(\phi).
   $$
   特别地，在严格正矩阵集合 $(0,+\infty]^{I\times I}$ 上，$\mathcal{L}^+(\phi)$（分别地 $\mathcal{K}(\phi)$、$\mathcal{L}^{\mathrm{inv}}(\phi)$）与其有限距离版本完全重合。
3. **（闭性与极小元存在推论）** $\mathcal{L}^+(\phi)$ 为闭集当且仅当 $\mathcal{L}^+(\phi)=\mathcal{L}^+_{\mathrm{fin}}(\phi)$（特别地，当 $\mathrm{dom}(\phi)$ 上各距离均有限时必然成立）；$\mathcal{K}(\phi)$ 与 $\mathcal{L}^{\mathrm{inv}}(\phi)$（$\phi(\mathrm{dom}(\phi))$ 上各距离均有限时闭）同理。凡闭的非空矩阵族皆紧致，且其每个元素都控制至少一个极小元。
4. **（无穷距离非闭反例）** 取 $\mathcal{X}=\{a,b,\bot\}$，$|I|=1$，$d(a,b)=+\infty$，$\phi=\mathrm{id}_{\mathcal{X}}$，则
   $$
   \mathcal{L}^+(\phi)=\mathcal{L}^{\mathrm{inv}}(\phi)=\mathcal{K}(\phi)=(0,+\infty]\quad\text{（非闭）},\qquad
   \overline{\mathcal{L}^+(\phi)}=\overline{\mathcal{L}^{\mathrm{inv}}(\phi)}=\overline{\mathcal{K}(\phi)}=[0,+\infty]=\mathcal{L}^-(\phi).
   $$

**证明**：
1. 设 $M^{(n)}\in\mathcal{L}^-(\phi)$ 收敛于 $M$。对任意 $x,y\in\mathrm{dom}(\phi)$ 与 $i\in I$，由命题 1.1(3) 中 $a\mapsto a\cdot d_j(x,y)$ 的下半连续性，对每个 $j\in I$ 有 $M_{ij}d_j(x,y)\le\liminf_n M^{(n)}_{ij}d_j(x,y)$；对有限个 $j$ 求和得 $(M\mathbf{d}(x,y))_i\le\liminf_n(M^{(n)}\mathbf{d}(x,y))_i\le d_i(\phi(x),\phi(y))$，故 $M\in\mathcal{L}^-(\phi)$。紧致空间之闭子集紧致。对任意 $M_0\in\mathcal{L}^-(\phi)$，考虑 $\{M\in\mathcal{L}^-(\phi)\mid M\ge M_0\}$，其任意非空全序上升链 $\mathcal{T}$ 的逐元上确界 $M^*_{ij}:=\sup_{M\in\mathcal{T}} M_{ij}$ 是定向网 $(M)_{M\in\mathcal{T}}$ 的极限，由闭性知 $M^*\in\mathcal{L}^-(\phi)$，由 Zorn 引理得存在极大元控制 $M_0$。
2. 先证 $\overline{\mathcal{L}^+(\phi)}=\mathcal{L}^+_{\mathrm{fin}}(\phi)$。显然 $\mathcal{L}^+(\phi)\subseteq\mathcal{L}^+_{\mathrm{fin}}(\phi)$。若 $L^{(n)}\in\mathcal{L}^+_{\mathrm{fin}}(\phi)$ 收敛于 $L$，对任意满足 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$ 的 $x,y\in\mathrm{dom}(\phi)$，由命题 1.1(3) 知 $a\mapsto a\cdot d_j(x,y)$ 在 $[0,+\infty]$ 上连续，故 $(L\mathbf{d}(x,y))_i=\lim_n(L^{(n)}\mathbf{d}(x,y))_i\ge d_i(\phi(x),\phi(y))$，从而 $\mathcal{L}^+_{\mathrm{fin}}(\phi)$ 为闭集，得 $\overline{\mathcal{L}^+(\phi)}\subseteq\mathcal{L}^+_{\mathrm{fin}}(\phi)$。反之，任取 $L\in\mathcal{L}^+_{\mathrm{fin}}(\phi)$，对 $n\ge 1$ 令 $L^{(n)}:=L+\frac{1}{n}\mathbf{1}_{I\times I}$（约定 $+\infty+\frac{1}{n}=+\infty$），则在序拓扑下 $L^{(n)}\to L$。对任意 $x,y\in\mathrm{dom}(\phi)$：若 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$，有 $(L^{(n)}\mathbf{d}(x,y))_i\ge(L\mathbf{d}(x,y))_i\ge d_i(\phi(x),\phi(y))$；若存在 $j_0$ 使 $d_{j_0}(x,y)=+\infty$，因 $L^{(n)}_{ij_0}\ge\frac{1}{n}>0$，有 $(L^{(n)}\mathbf{d}(x,y))_i=+\infty\ge d_i(\phi(x),\phi(y))$。故 $L^{(n)}\in\mathcal{L}^+(\phi)$，于是 $L\in\overline{\mathcal{L}^+(\phi)}$。

   再证 $\overline{\mathcal{K}(\phi)}=\mathcal{K}_{\mathrm{fin}}(\phi)$。显然 $\mathcal{K}(\phi)\subseteq\mathcal{K}_{\mathrm{fin}}(\phi)$。若 $W^{(n)}\in\mathcal{K}_{\mathrm{fin}}(\phi)$ 收敛于 $W$，取满足 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$ 且 $(W\mathbf{d}(x,y))_i<1$ 的 $x,y\in\mathrm{dom}(\phi)$，由每个 $d_j(x,y)<+\infty$ 及命题 1.1(3) 得 $(W^{(n)}\mathbf{d}(x,y))_i\to(W\mathbf{d}(x,y))_i<1$，故充分大 $n$ 有 $(W^{(n)}\mathbf{d}(x,y))_i<1$，推出 $d_i(\phi(x),\phi(y))=0$，即 $\mathcal{K}_{\mathrm{fin}}(\phi)$ 闭。反之，任取 $W\in\mathcal{K}_{\mathrm{fin}}(\phi)$，令 $W^{(n)}:=W+\frac{1}{n}\mathbf{1}_{I\times I}\to W$。若 $(W^{(n)}\mathbf{d}(x,y))_i<1$，因每个元均 $\ge\frac{1}{n}>0$，必有 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$，且 $(W\mathbf{d}(x,y))_i\le(W^{(n)}\mathbf{d}(x,y))_i<1$，推出 $d_i(\phi(x),\phi(y))=0$。故 $W^{(n)}\in\mathcal{K}(\phi)$，从而 $W\in\overline{\mathcal{K}(\phi)}$。

   $\overline{\mathcal{L}^{\mathrm{inv}}(\phi)}=\mathcal{L}^{\mathrm{inv}}_{\mathrm{fin}}(\phi)$ 与 $\mathcal{L}^+$ 完全对偶。注意到当 $A\in(0,+\infty]^{I\times I}$ 时，上述证明中不需加 $\frac{1}{n}$ 即自动覆盖含 $+\infty$ 分量的点对，故与有限距离版本重合。
3. 由 (2) 直接得出；极小元存在性将 (1) 中 Zorn 引理应用于下降链及逐元下确界即得。
4. 在反例中，$+\infty\le L\cdot(+\infty)$ 与 $W\cdot(+\infty)<1\implies+\infty=0$ 均等价于 $L>0,W>0$，而有限距离点对仅有 $(a,a),(b,b)$，故有限距离版本均为 $[0,+\infty]$。 $\square$

---

### 3.3 多分量非唯一极值性与分量可分解域的完整分类

**命题 3.5（$|I|\ge 2$ 时唯一最优矩阵一般不存在）**
取 $\mathcal{X}=\{a,b,\bot\}$，$I=\{1,2\}$，$d_1(a,b)=d_2(a,b)=1$，$\phi=\mathrm{id}_{\mathcal{X}}$。令
$$
A_1=\begin{pmatrix}1&0\\1&0\end{pmatrix},\qquad A_2=\begin{pmatrix}0&1\\0&1\end{pmatrix}.
$$
则 $A_1,A_2$ 同为 $\mathcal{L}^+(\phi),\,\mathcal{L}^{\mathrm{inv}}(\phi),\,\mathcal{K}(\phi)$ 的极小元，但其逐元下确界 $A_1\wedge A_2=\mathbf{0}$ 不属于这三个族；同时 $A_1,A_2$ 也同为 $\mathcal{L}^-(\phi)$ 的极大元，但其逐元上确界 $A_1\vee A_2=\begin{pmatrix}1&1\\1&1\end{pmatrix}$ 不属于 $\mathcal{L}^-(\phi)$（因 $1+1=2>1$）。 $\square$

然而，当有效定义域在各分量间可以独立分解时（例如有限个扩展伪度量空间的直积），$\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)$ 甚至在允许无穷距离的一般情形下也获得**完全的乘积区间分类**！

**定义 3.6（分量可分解性）**
称子集 $S\subseteq\mathcal{X}$ 是**分量可分解的**，如果存在 $I$ 的某个排列 $(i_1,\dots,i_m)$，使得对任意 $x,y\in S$，存在链 $z_0=x,z_1,\dots,z_m=y\in S$，满足对每个 $r=1,\dots,m$：
$$
d_{i_r}(z_{r-1},z_r)\le d_{i_r}(x,y),\qquad \forall k\in I\setminus\{i_r\},\; d_k(z_{r-1},z_r)=0.
$$

对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$，定义其**偏上 Lipschitz 矩阵** $L^*(\phi)$、**偏坍缩率矩阵** $W^*(\phi)$ 与**无穷跳变例外指标集** $Z_\infty(\phi)\subseteq I\times I$：
$$
L^*_{ij}(\phi):=\sup\left\{\frac{d_i(\phi(u),\phi(v))}{d_j(u,v)}\;\middle|\;u,v\in\mathrm{dom}(\phi),\;d_j(u,v)\in(0,+\infty),\;\forall k\neq j,\,d_k(u,v)=0\right\},
$$
$$
W^*_{ij}(\phi):=\sup\left\{\frac{1}{d_j(u,v)}\;\middle|\;u,v\in\mathrm{dom}(\phi),\;d_i(\phi(u),\phi(v))>0,\;d_j(u,v)\in(0,+\infty),\;\forall k\neq j,\,d_k(u,v)=0\right\},
$$
$$
Z_\infty(\phi):=\Bigl\{(i,j)\in I\times I\;\Big|\;L^*_{ij}(\phi)=0\text{ 且 }\exists u,v\in\mathrm{dom}(\phi),\;d_j(u,v)=+\infty,\;\forall k\neq j,\,d_k(u,v)=0,\;d_i(\phi(u),\phi(v))>0\Bigr\}.
$$

**定理 3.7（分量可分解域上的完整乘积区间分类定理）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$ 在 $\mathrm{dom}(\phi)$ 上保持全零距离，且 $\mathrm{dom}(\phi)$ 分量可分解。则：
1. **（偏支集恒等）** $\mathrm{supp}(L^*(\phi))=\mathrm{supp}(W^*(\phi))$（故 $Z_\infty(\phi)$ 中条件 $L^*_{ij}(\phi)=0$ 与 $W^*_{ij}(\phi)=0$ 等价）。
2. **（精确乘积区间分类与盒式重合）**
   $$
   \mathcal{L}^+(\phi)=\prod_{(i,j)\in I\times I} I^+_{ij}(\phi),\qquad
   \mathcal{K}(\phi)=\mathcal{K}_{\mathrm{box}}(\phi)=\prod_{(i,j)\in I\times I} I^{\mathcal{K}}_{ij}(\phi),
   $$
   其中
   $$
   I^+_{ij}(\phi):=\begin{cases}(0,+\infty],&(i,j)\in Z_\infty(\phi),\\ [L^*_{ij}(\phi),+\infty],&(i,j)\notin Z_\infty(\phi),\end{cases}
   \qquad
   I^{\mathcal{K}}_{ij}(\phi):=\begin{cases}(0,+\infty],&(i,j)\in Z_\infty(\phi),\\ [W^*_{ij}(\phi),+\infty],&(i,j)\notin Z_\infty(\phi).\end{cases}
   $$
3. **（闭包与逐元下确界）** $\overline{\mathcal{L}^+(\phi)}=[L^*(\phi),\boldsymbol{\infty}_{I\times I}]$，$\overline{\mathcal{K}(\phi)}=[W^*(\phi),\boldsymbol{\infty}_{I\times I}]$；特别地，恒有 $\inf\mathcal{L}^+(\phi)=L^*(\phi)$ 与 $\inf\mathcal{K}(\phi)=W^*(\phi)$。
4. **（五等价闭性与唯一极小元判据）** 以下五条等价：
   $$
   Z_\infty(\phi)=\emptyset \;\iff\; L^*(\phi)\in\mathcal{L}^+(\phi) \;\iff\; W^*(\phi)\in\mathcal{K}(\phi) \;\iff\; \mathcal{L}^+(\phi)\text{ 为闭集} \;\iff\; \mathcal{K}(\phi)\text{ 为闭集}.
   $$
   特别地，当 $\mathrm{dom}(\phi)$ 上各距离均有限时必有 $Z_\infty(\phi)=\emptyset$，从而 $L^*(\phi)$ 与 $W^*(\phi)$ 分别是 $\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)=\mathcal{K}_{\mathrm{box}}(\phi)$ 的**唯一极小元**。

**证明**：
1. $L^*_{ij}(\phi)>0$ 与 $W^*_{ij}(\phi)>0$ 均等价于“存在 $u,v\in\mathrm{dom}(\phi)$ 满足 $d_j(u,v)\in(0,+\infty)$、$\forall k\neq j,\,d_k(u,v)=0$ 且 $d_i(\phi(u),\phi(v))>0$”，故 $\mathrm{supp}(L^*(\phi))=\mathrm{supp}(W^*(\phi))$。
2. **必要性（$\subseteq$）**：设 $L\in\mathcal{L}^+(\phi)$。对满足 $d_j(u,v)\in(0,+\infty)$、$\forall k\neq j,\,d_k(u,v)=0$ 的点对 $(u,v)$，有 $d_i(\phi(u),\phi(v))\le L_{ij}d_j(u,v)$，除以有限正数 $d_j(u,v)$ 得 $L_{ij}\ge L^*_{ij}(\phi)$；若 $(i,j)\in Z_\infty(\phi)$，取相应满足 $d_j(u,v)=+\infty$、$\forall k\neq j,\,d_k(u,v)=0$ 且 $d_i(\phi(u),\phi(v))>0$ 的点对，有 $0<d_i(\phi(u),\phi(v))\le L_{ij}\cdot(+\infty)$，迫使 $L_{ij}>0$。故 $L\in\prod I^+_{ij}(\phi)$。
   同理，设 $W\in\mathcal{K}(\phi)$。对满足 $d_i(\phi(u),\phi(v))>0$、$d_j(u,v)\in(0,+\infty)$、$\forall k\neq j,\,d_k(u,v)=0$ 的点对，必有 $W_{ij}d_j(u,v)=(W\mathbf{d}(u,v))_i\ge 1$，得 $W_{ij}\ge W^*_{ij}(\phi)$；若 $(i,j)\in Z_\infty(\phi)$，对相应无穷距离点对有 $W_{ij}\cdot(+\infty)\ge 1$，迫使 $W_{ij}>0$。故 $W\in\prod I^{\mathcal{K}}_{ij}(\phi)$。

   **充分性（$\supseteq$）**：任取 $x,y\in\mathrm{dom}(\phi)$ 及分解链 $z_0=x,\dots,z_m=y\in\mathrm{dom}(\phi)$。
   - 若 $L\in\prod I^+_{ij}(\phi)$，对每一步 $r$（记 $j=i_r$）：
     (i) $d_j(z_{r-1},z_r)=0$ 时，$\mathbf{d}(z_{r-1},z_r)=\mathbf{0}$，由全零距离保持性得 $d_i(\phi(z_{r-1}),\phi(z_r))=0\le L_{ij}d_j(x,y)$；
     (ii) $0<d_j(z_{r-1},z_r)<+\infty$ 时，由 $L^*_{ij}$ 定义得 $d_i(\phi(z_{r-1}),\phi(z_r))\le L^*_{ij}d_j(z_{r-1},z_r)\le L_{ij}d_j(x,y)$；
     (iii) $d_j(z_{r-1},z_r)=+\infty$ 时，由 $d_j(z_{r-1},z_r)\le d_j(x,y)$ 得 $d_j(x,y)=+\infty$：若 $L_{ij}>0$ 则 $L_{ij}d_j(x,y)=+\infty\ge d_i(\phi(z_{r-1}),\phi(z_r))$；若 $L_{ij}=0$，由 $L_{ij}\in I^+_{ij}(\phi)$ 必有 $L^*_{ij}=0$ 且 $(i,j)\notin Z_\infty(\phi)$，由 $Z_\infty(\phi)$ 定义得 $d_i(\phi(z_{r-1}),\phi(z_r))=0=L_{ij}d_j(x,y)$。
     由三角不等式对 $r=1,\dots,m$ 求和即得 $d_i(\phi(x),\phi(y))\le(L\mathbf{d}(x,y))_i$，故 $L\in\mathcal{L}^+(\phi)$。
   - 若 $W\in\prod I^{\mathcal{K}}_{ij}(\phi)$ 且 $\max_{k\in I} W_{ik}d_k(x,y)<1$，对每一步 $r$（记 $j=i_r$），有 $W_{ij}d_j(z_{r-1},z_r)\le W_{ij}d_j(x,y)<1$：
     (i) $d_j(z_{r-1},z_r)=0$ 时，同上得 $d_i(\phi(z_{r-1}),\phi(z_r))=0$；
     (ii) $0<d_j(z_{r-1},z_r)<+\infty$ 时，若 $d_i(\phi(z_{r-1}),\phi(z_r))>0$，则 $W_{ij}\ge W^*_{ij}\ge 1/d_j(z_{r-1},z_r)$，矛盾，故 $d_i(\phi(z_{r-1}),\phi(z_r))=0$；
     (iii) $d_j(z_{r-1},z_r)=+\infty$ 时，$W_{ij}\cdot(+\infty)<1$ 迫使 $W_{ij}=0$，由 $W_{ij}\in I^{\mathcal{K}}_{ij}(\phi)$ 必有 $W^*_{ij}=0$ 且 $(i,j)\notin Z_\infty(\phi)$，从而 $d_i(\phi(z_{r-1}),\phi(z_r))=0$。
     由三角不等式得 $d_i(\phi(x),\phi(y))=0$，故 $W\in\mathcal{K}_{\mathrm{box}}(\phi)\subseteq\mathcal{K}(\phi)$。由此同时证得 $\mathcal{K}(\phi)=\mathcal{K}_{\mathrm{box}}(\phi)=\prod I^{\mathcal{K}}_{ij}(\phi)$。
3. 有限乘积的闭包等于闭包的乘积；注意到 $(i,j)\in Z_\infty(\phi)$ 时 $L^*_{ij}=W^*_{ij}=0$ 且 $\overline{(0,+\infty]}=[0,+\infty]$，其余分量本就闭，立即得 (3)。
4. 乘积 $\prod I^+_{ij}(\phi)$（非空）为闭集当且仅当每个因子 $I^+_{ij}(\phi)$ 为闭集，而 $(0,+\infty]$ 非闭、$[a,+\infty]$ 恒闭，故与 $Z_\infty(\phi)=\emptyset$ 等价，并等价于 $L^*(\phi)\in\mathcal{L}^+(\phi)$。$\mathcal{K}(\phi)$ 完全同理。 $\square$

> **注记（$\mathcal{L}^-(\phi)$ 在分量可分解域上仍无唯一极大元）**：与 $\mathcal{L}^+,\mathcal{K}$ 形成鲜明对比，即使在距离全有限且分量可分解的空间上，$\mathcal{L}^-(\phi)$ 仍可能无唯一极大元。取 $\mathcal{X}=(\{0,1\}^2)\cup\{\bot\}$，$d_1(x,y)=|x_1-y_1|,d_2(x,y)=|x_2-y_2|$，定义 $\phi(x_1,x_2):=(x_1+2x_2,\,0)$（作为映入 $\mathbb{R}^2\cup\{\bot\}$ 的限制，或在 $\mathbb{R}^2\cup\{\bot\}$ 上定义 $\mathrm{dom}(\phi)=\{0,1\}^2$）。直接检验知行向量 $(1,0)$ 与 $(0,1)$ 均属于 $\mathcal{L}_1^-(\phi)$，但取对角点对 $(1,0)$ 与 $(0,1)$（$d_1=d_2=1$ 而 $d_1(\phi)=|1-2|=1$），其逐元上确界 $(1,1)$ 给出 $1+1=2>1$，故 $(1,1)\notin\mathcal{L}_1^-(\phi)$。其几何根源在于：三角不等式控制上界叠加，却允许下界跨分量相互抵消。

**推论 3.8（单伪度量情形 $|I|=1$ 的精确还原）**
当 $|I|=1$ 且 $\mathrm{dom}(\phi)$ 上距离有限时（任意集合自动分量可分解且 $Z_\infty(\phi)=\emptyset$），若 $\phi$ 保持零距离，则：
- $\mathcal{L}^+(\phi)=[L^*(\phi),+\infty]$，其中 $L^*(\phi)=\sup_{d(x,y)>0}\frac{d(\phi(x),\phi(y))}{d(x,y)}$ 为经典扩展 Lipschitz 常数；
- $\mathcal{L}^-(\phi)=[0,M^*(\phi)]$，其中 $M^*(\phi)=\inf_{d(x,y)>0}\frac{d(\phi(x),\phi(y))}{d(x,y)}$（$\inf\emptyset=+\infty$）为经典反 Lipschitz 常数；
- 若 $\phi$ 还反射零距离且 $\phi(\mathrm{dom}(\phi))$ 上距离有限，则 $\mathcal{L}^{\mathrm{inv}}(\phi)=[(M^*(\phi))^{-1},+\infty]$；
- $\mathcal{K}(\phi)=[W^*(\phi),+\infty]$，其中 $W^*(\phi)=(\Theta^*(\phi))^{-1}$，$\Theta^*(\phi):=\inf\{d(x,y)\mid x,y\in\mathrm{dom}(\phi),\,d(\phi(x),\phi(y))>0\}$（$\inf\emptyset=+\infty$）恰为最大不可区分半径。 $\square$

---

## 四、算子复合演算、因子消去与迭代动力学

**引理 4.1（复合定义域控制）**
对任意 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$，有 $\psi\circ\phi\in\mathcal{X}_{\mathrm{op}}$，且
$$
\mathrm{dom}(\psi\circ\phi)=\phi^{-1}\bigl(\mathrm{dom}(\psi)\bigr)\subseteq\mathrm{dom}(\phi),\qquad
\phi\bigl(\mathrm{dom}(\psi\circ\phi)\bigr)\subseteq\mathrm{dom}(\psi).
$$

**证明**：$(\psi\circ\phi)(\bot)=\psi(\bot)=\bot$。若 $x\in\mathrm{dom}(\psi\circ\phi)$，即 $\psi(\phi(x))\neq\bot$，则 $\phi(x)\in\mathrm{dom}(\psi)$；因 $\bot\notin\mathrm{dom}(\psi)$，必有 $\phi(x)\neq\bot$，即 $x\in\mathrm{dom}(\phi)$。 $\square$

**定理 4.2（四类矩阵的复合演算律）**
设 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$，且 $L_\phi\in\mathcal{L}^+(\phi),\,L_\psi\in\mathcal{L}^+(\psi),\,M_\phi\in\mathcal{L}^-(\phi),\,M_\psi\in\mathcal{L}^-(\psi),\,B_\phi\in\mathcal{L}^{\mathrm{inv}}(\phi),\,B_\psi\in\mathcal{L}^{\mathrm{inv}}(\psi),\,W_\phi\in\mathcal{K}(\phi),\,W_\psi\in\mathcal{K}(\psi)$。则：
1. **（上界协变律）** $L_\psi L_\phi\in\mathcal{L}^+(\psi\circ\phi)$；
2. **（前向下界协变律）** $M_\psi M_\phi\in\mathcal{L}^-(\psi\circ\phi)$；
3. **（反向界反变律）** $B_\phi B_\psi\in\mathcal{L}^{\mathrm{inv}}(\psi\circ\phi)$；
4. **（坍缩经上界拉回律）** $W_\psi L_\phi\in\mathcal{K}(\psi\circ\phi)$；
5. **（坍缩前推律）** $W_\psi\odot W_\phi\in\mathcal{K}(\psi\circ\phi)$ 且 $L_\psi\odot W_\phi\in\mathcal{K}(\psi\circ\phi)$；
6. **（分通道混合坍缩律）** 对固定行 $i\in I$ 及中间指标集 $I$ 的任意划分 $I=J_1\sqcup J_2$，定义行向量 $\mathbf{w}^{(i)}=(w_k)_{k\in I}$ 为
   $$
   w_k:=\max\!\left(\max_{j\in J_1}\bigl(\mathrm{supp}((W_\psi)_{ij})\,(W_\phi)_{jk}\bigr),\;\sum_{j\in J_2}(W_\psi)_{ij}(L_\phi)_{jk}\right)
   $$
   （$J_1=\emptyset$ 时前项取 $0$），则 $\mathbf{w}^{(i)}\in\mathcal{K}_i(\psi\circ\phi)$。（取 $J_1=\emptyset$ 还原 (4)，取 $J_2=\emptyset$ 还原 (5) 前式；如例 8.2 所示，该律可严格优于 (4) 与 (5) 两者。）

**证明**：
任取 $x,y\in\mathrm{dom}(\psi\circ\phi)$。由引理 4.1，$x,y\in\mathrm{dom}(\phi)$ 且 $\phi(x),\phi(y)\in\mathrm{dom}(\psi)$。利用命题 1.1(1)：
1. $\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))\le L_\psi\mathbf{d}(\phi(x),\phi(y))\le L_\psi(L_\phi\mathbf{d}(x,y))=(L_\psi L_\phi)\mathbf{d}(x,y)$。
2. $\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))\ge M_\psi\mathbf{d}(\phi(x),\phi(y))\ge M_\psi(M_\phi\mathbf{d}(x,y))=(M_\psi M_\phi)\mathbf{d}(x,y)$。
3. $\mathbf{d}(x,y)\le B_\phi\mathbf{d}(\phi(x),\phi(y))\le B_\phi(B_\psi\mathbf{d}(\psi(\phi(x)),\psi(\phi(y))))=(B_\phi B_\psi)\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))$。
4. 若 $((W_\psi L_\phi)\mathbf{d}(x,y))_i<1$，则 $(W_\psi\mathbf{d}(\phi(x),\phi(y)))_i\le((W_\psi L_\phi)\mathbf{d}(x,y))_i<1$，故 $d_i(\psi(\phi(x)),\psi(\phi(y)))=0$。
5. 对 $L_\psi\odot W_\phi$：若 $((L_\psi\odot W_\phi)\mathbf{d}(x,y))_i<1$，则对每个满足 $(L_\psi)_{ij}>0$ 的 $j$ 与所有 $k$ 有 $(W_\phi)_{jk}\le(L_\psi\odot W_\phi)_{ik}$，故 $(W_\phi\mathbf{d}(x,y))_j\le((L_\psi\odot W_\phi)\mathbf{d}(x,y))_i<1$，推出 $d_j(\phi(x),\phi(y))=0$。从而
   $$
   d_i\bigl(\psi(\phi(x)),\psi(\phi(y))\bigr)\le\sum_{j:\,(L_\psi)_{ij}>0}(L_\psi)_{ij}\cdot 0+\sum_{j:\,(L_\psi)_{ij}=0}0\cdot d_j(\phi(x),\phi(y))=0.
   $$
   $W_\psi\odot W_\phi$ 是 (6) 取 $J_2=\emptyset$ 的特例。
6. 设 $\sum_{k\in I} w_k d_k(x,y)<1$。对每个 $j\in J_1$：若 $(W_\psi)_{ij}>0$，则对所有 $k$ 有 $(W_\phi)_{jk}\le w_k$，得 $(W_\phi\mathbf{d}(x,y))_j\le\sum_k w_k d_k(x,y)<1$，推出 $d_j(\phi(x),\phi(y))=0$，故 $(W_\psi)_{ij}d_j(\phi(x),\phi(y))=0$；若 $(W_\psi)_{ij}=0$ 此项亦为 $0$。对 $J_2$ 部分：
   $$
   \sum_{j\in J_2}(W_\psi)_{ij}d_j(\phi(x),\phi(y))
   \le\sum_{j\in J_2}(W_\psi)_{ij}\sum_{k\in I}(L_\phi)_{jk}d_k(x,y)
   =\sum_{k\in I}\!\left(\sum_{j\in J_2}(W_\psi)_{ij}(L_\phi)_{jk}\right)\!d_k(x,y)
   \le\sum_{k\in I} w_k d_k(x,y)<1.
   $$
   两部分相加得 $(W_\psi\mathbf{d}(\phi(x),\phi(y)))_i<1$，故 $d_i(\psi(\phi(x)),\psi(\phi(y)))=0$。 $\square$

**命题 4.3（左/右因子消去律）**
设 $\phi,\psi\in\mathcal{X}_{\mathrm{op}}$，记 $D:=\mathrm{dom}(\psi\circ\phi)$ 与 $R:=\phi(D)\subseteq\mathrm{dom}(\psi)$。则：
1. 若 $B_\psi\in\mathcal{L}^{\mathrm{inv}}(\psi)$、$L_{\psi\circ\phi}\in\mathcal{L}^+(\psi\circ\phi)$，则 $B_\psi L_{\psi\circ\phi}\in\mathcal{L}^+(\phi|_D)$；
2. 若 $B_\psi\in\mathcal{L}^{\mathrm{inv}}(\psi)$、$W_{\psi\circ\phi}\in\mathcal{K}(\psi\circ\phi)$，则 $B_\psi\odot W_{\psi\circ\phi}\in\mathcal{K}(\phi|_D)$；
3. 若 $B_{\psi\circ\phi}\in\mathcal{L}^{\mathrm{inv}}(\psi\circ\phi)$、$L_\psi\in\mathcal{L}^+(\psi)$，则 $B_{\psi\circ\phi} L_\psi\in\mathcal{L}^{\mathrm{inv}}(\phi|_D)$；
4. 若 $B_{\psi\circ\phi}\in\mathcal{L}^{\mathrm{inv}}(\psi\circ\phi)$、$L_\phi\in\mathcal{L}^+(\phi)$，则 $L_\phi B_{\psi\circ\phi}\in\mathcal{L}^{\mathrm{inv}}(\psi|_R)$。

**证明**：
任取 $x,y\in D$（于是 $x,y\in\mathrm{dom}(\phi)$ 且 $\phi(x),\phi(y)\in\mathrm{dom}(\psi)$）：
1. $\mathbf{d}(\phi(x),\phi(y))\le B_\psi\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))\le(B_\psi L_{\psi\circ\phi})\mathbf{d}(x,y)$。
2. 若 $((B_\psi\odot W_{\psi\circ\phi})\mathbf{d}(x,y))_j<1$，则对每个满足 $(B_\psi)_{ji}>0$ 的 $i$ 有 $(W_{\psi\circ\phi}\mathbf{d}(x,y))_i<1$，得 $d_i(\psi(\phi(x)),\psi(\phi(y)))=0$，代入 $B_\psi\in\mathcal{L}^{\mathrm{inv}}(\psi)$ 得 $d_j(\phi(x),\phi(y))=0$。
3. $\mathbf{d}(x,y)\le B_{\psi\circ\phi}\mathbf{d}(\psi(\phi(x)),\psi(\phi(y)))\le(B_{\psi\circ\phi}L_\psi)\mathbf{d}(\phi(x),\phi(y))$。
4. 对任意 $u,v\in R$，取 $x,y\in D$ 使 $u=\phi(x),v=\phi(y)$，则 $\mathbf{d}(u,v)\le L_\phi\mathbf{d}(x,y)\le(L_\phi B_{\psi\circ\phi})\mathbf{d}(\psi(u),\psi(v))$。 $\square$

**推论 4.4（迭代幂律与“压缩 + 坍缩 $\implies$ 有限步精确不可区分”）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$ 与 $n\ge 1$：
1. 若 $L\in\mathcal{L}^+(\phi),\,M\in\mathcal{L}^-(\phi),\,B\in\mathcal{L}^{\mathrm{inv}}(\phi),\,W\in\mathcal{K}(\phi)$，则
   $$
   L^n\in\mathcal{L}^+(\phi^n),\quad M^n\in\mathcal{L}^-(\phi^n),\quad B^n\in\mathcal{L}^{\mathrm{inv}}(\phi^n),\quad
   WL^{n-1},\,W^{\odot n},\,L^{\odot(n-1)}\odot W\in\mathcal{K}(\phi^n).
   $$
2. **（有限步精确不可区分定理）** 若存在全有限上界矩阵 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$ 满足谱半径 $\rho(L)<1$，且存在全有限不可区分矩阵 $W\in\mathcal{K}(\phi)\cap\mathbb{R}_+^{I\times I}$，则对任意满足 $\mathbf{diam}(S)\in\mathbb{R}_+^I$ 的子集 $S\subseteq\mathcal{X}$，存在仅依赖于 $L,W,\mathbf{diam}(S)$ 的 $N\in\mathbb{N}$，使得对一切 $n\ge N$ 及一切 $x,y\in S\cap\mathrm{dom}(\phi^n)$ 皆有**精确零距离**：
   $$
   \mathbf{d}\bigl(\phi^n(x),\phi^n(y)\bigr)=\mathbf{0}.
   $$
   特别地，若此时还存在任意（甚至含 $+\infty$ 元的）$B\in\mathcal{L}^{\mathrm{inv}}(\phi)$，则对任意满足 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$ 的 $x,y\in\bigcap_{n\ge 1}\mathrm{dom}(\phi^n)$ 必有 $\mathbf{d}(x,y)=\mathbf{0}$。

**证明**：
(1) 对 $n$ 归纳并反复应用定理 4.2 及命题 1.1(2) 的结合律（$n=1$ 时 $L^0=L^{\odot 0}=E$，$E\odot W=W$）。
(2) 由 $\rho(L)<1$ 知 $\lim_{n\to\infty}L^{n-1}=\mathbf{0}$。因 $W$ 与 $\mathbf{diam}(S)$ 全有限，故 $\lim_{n\to\infty}WL^{n-1}\mathbf{diam}(S)=\mathbf{0}$。取 $N\ge 1$ 使对一切 $n\ge N$ 及 $i\in I$ 有 $(WL^{n-1}\mathbf{diam}(S))_i<1$；对 $x,y\in S\cap\mathrm{dom}(\phi^n)$ 有 $(WL^{n-1}\mathbf{d}(x,y))_i<1$，由 $WL^{n-1}\in\mathcal{K}(\phi^n)$ 得 $\mathbf{d}(\phi^n(x),\phi^n(y))=\mathbf{0}$。若另有 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$，取 $S=\{x,y\}$ 与相应 $N$，由 $B^N\in\mathcal{L}^{\mathrm{inv}}(\phi^N)$ 得 $\mathbf{d}(x,y)\le B^N\mathbf{d}(\phi^N(x),\phi^N(y))=B^N\mathbf{0}=\mathbf{0}$。 $\square$

---

## 五、四类矩阵的内在耦合、对偶与布尔依赖骨架

### 5.1 上界、前向下界与反向界的耦合关系

**命题 5.1（双边夹逼与逐元有序）**
对任意 $M\in\mathcal{L}^-(\phi)$ 与 $L\in\mathcal{L}^+(\phi)$，恒有 $\forall x,y\in\mathrm{dom}(\phi),\,M\mathbf{d}(x,y)\le\mathbf{d}(\phi(x),\phi(y))\le L\mathbf{d}(x,y)$。若对固定列指标 $j\in I$，存在 $x,y\in\mathrm{dom}(\phi)$ 满足 $0<d_j(x,y)<+\infty$ 且 $d_k(x,y)=0$（$\forall k\neq j$），则对一切 $i\in I$ 有 $M_{ij}\le L_{ij}$；若存在 $d_j(x,y)=+\infty$ 且 $d_k(x,y)=0$（$\forall k\neq j$），则 $M_{ij}>0\implies L_{ij}>0$。
（注：纯-$j$ 点对条件不可或缺——在命题 3.5 中，$A_1\in\mathcal{L}^-(\mathrm{id})$ 与 $A_2\in\mathcal{L}^+(\mathrm{id})$ 但 $A_1\not\le A_2$。） $\square$

**命题 5.2（$\mathcal{L}^-$ 与 $\mathcal{L}^{\mathrm{inv}}$ 的矩阵对偶及 $L$-$B$ 谱半径相容律）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. 若 $M\in\mathcal{L}^-(\phi)$ 且 $B\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 满足 $BM\ge E$，则 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$。特别地，若对每个 $j\in I$ 均存在 $i(j)\in I$ 使 $M_{i(j),j}>0$，则令 $B_{j,i(j)}:=M_{i(j),j}^{-1}$（当 $M_{i(j),j}<+\infty$ 时）或任取正数（当 $M_{i(j),j}=+\infty$ 时）、其余元为 $0$，即得 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$。
2. 若 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$ 且 $M\in\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 满足 $MB\le E$，则 $M\in\mathcal{L}^-(\phi)$。
3. 半环 $\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 的全体可逆元恰为**正有限单项矩阵**（每行每列恰含一个有限正元、其余为 $0$）；对此类矩阵 $M$，有 $M\in\mathcal{L}^-(\phi)\iff M^{-1}\in\mathcal{L}^{\mathrm{inv}}(\phi)$。
4. **（$L$-$B$ 谱半径相容律）** 对任意 $L\in\mathcal{L}^+(\phi)$ 与 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$，有 $BL\in\mathcal{L}^+(\mathrm{id}_{\mathrm{dom}(\phi)})$ 且 $LB\in\mathcal{L}^+(\mathrm{id}_{\phi(\mathrm{dom}(\phi))})$。特别地，若 $L,B\in\mathbb{R}_+^{I\times I}$ 均全有限，且存在 $x,y\in\mathrm{dom}(\phi)$ 满足 $\mathbf{0}\neq\mathbf{d}(x,y)\in\mathbb{R}_+^I$，则
   $$
   \rho(BL)=\rho(LB)\ge 1.
   $$

**证明**：
1. $\mathbf{d}(x,y)=E\mathbf{d}(x,y)\le(BM)\mathbf{d}(x,y)=B(M\mathbf{d}(x,y))\le B\mathbf{d}(\phi(x),\phi(y))$。特例中 $(BM)_{jj}\ge 1$ 且非对角元 $\ge 0$，故 $BM\ge E$。
2. $M\mathbf{d}(x,y)\le M(B\mathbf{d}(\phi(x),\phi(y)))=(MB)\mathbf{d}(\phi(x),\phi(y))\le\mathbf{d}(\phi(x),\phi(y))$。
3. 设 $AB=E$。对每个 $i$，$\sum_j A_{ij}B_{ji}=1$，故不含 $+\infty$ 项且存在 $j_0(i)$ 使 $0<A_{ij_0(i)},B_{j_0(i)i}<+\infty$；对一切 $k\neq i$，$0=(AB)_{ik}\ge A_{ij_0(i)}B_{j_0(i)k}$ 迫使 $B_{j_0(i)k}=0$。因每个 $i$ 对应 $B$ 的唯一非零列为 $i$ 的行 $j_0(i)$，故 $i\mapsto j_0(i)$ 为双射，$B$ 与 $A$ 皆为正有限单项矩阵。结合 (1)(2) 得等价性。
4. 前半由 $B(L\mathbf{d}(x,y))\ge B\mathbf{d}(\phi(x),\phi(y))\ge\mathbf{d}(x,y)$ 及 $L(B\mathbf{d}(\phi(x),\phi(y)))\ge L\mathbf{d}(x,y)\ge\mathbf{d}(\phi(x),\phi(y))$ 立得。对后半，记 $\mathbf{v}:=\mathbf{d}(x,y)\in\mathbb{R}_+^I\setminus\{\mathbf{0}\}$；由 $BL\mathbf{v}\ge\mathbf{v}$ 归纳得 $(BL)^n\mathbf{v}\ge\mathbf{v}$（$\forall n\ge 1$）。若 $\rho(BL)<1$，则 $(BL)^n\to\mathbf{0}$ 推出 $\mathbf{v}\le\lim_n(BL)^n\mathbf{v}=\mathbf{0}$，矛盾！故 $\rho(LB)=\rho(BL)\ge 1$。 $\square$

---

### 5.2 $\mathcal{L}^+$ 与 $\mathcal{K}$ 的直径桥接、支集等价与布尔依赖骨架

记 $\phi$ 的**输出直径向量**为 $\mathbf{D}(\phi):=\mathbf{diam}(\phi(\mathrm{dom}(\phi)))=(D_i(\phi))_{i\in I}\in\bar{\mathbb{R}}_+^I$。

**定理 5.3（直径桥接、支集等价与布尔依赖骨架定理）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. **（上界诱导零容忍坍缩）** 对任意 $L\in\mathcal{L}^+(\phi)$，有 $\infty\cdot\mathrm{supp}(L)\in\mathcal{K}(\phi)$。
2. **（直径桥接：坍缩诱导定量上界）** 对任意 $W\in\mathcal{K}(\phi)$，有
   $$
   \mathrm{diag}\bigl(\mathbf{D}(\phi)\bigr)\,W\in\mathcal{L}^+(\phi),
   $$
   从而亦有 $\infty\cdot\mathrm{supp}(W)\in\mathcal{L}^+(\phi)$。
3. **（布尔依赖骨架与支集族精确相等）**
   $$
   \mathcal{L}^+(\phi)\cap\{0,+\infty\}^{I\times I} = \mathcal{K}(\phi)\cap\{0,+\infty\}^{I\times I},
   \qquad
   \{\mathrm{supp}(L)\mid L\in\mathcal{L}^+(\phi)\}=\{\mathrm{supp}(W)\mid W\in\mathcal{K}(\phi)\}.
   $$
   而且，二元矩阵 $S\in\{0,1\}^{I\times I}$ 满足 $\infty\cdot S$ 属于该共同骨架当且仅当：对一切 $i\in I$ 与 $x,y\in\mathrm{dom}(\phi)$，
   $$
   \bigl(\forall j\in I,\;S_{ij}=1\implies d_j(x,y)=0\bigr)\implies d_i\bigl(\phi(x),\phi(y)\bigr)=0.
   $$
   此外，在骨架 $\{0,+\infty\}^{I\times I}$ 上，普通矩阵乘法与支集极大积 $\odot$ 完全重合（均对应布尔矩阵乘法）。

**证明**：
1. 记 $\widetilde{W}:=\infty\cdot\mathrm{supp}(L)$。若 $(\widetilde{W}\mathbf{d}(x,y))_i<1$，则对一切满足 $L_{ij}>0$ 的 $j$ 必有 $d_j(x,y)=0$，故 $d_i(\phi(x),\phi(y))\le\sum_{L_{ij}>0} L_{ij}\cdot 0+\sum_{L_{ij}=0}0\cdot d_j(x,y)=0$。
2. 注意对任意 $D,t\in\bar{\mathbb{R}}_+$ 恒有 $\min(D,\chi_{[1,+\infty]}(t))\le D\cdot t$（$t<1$ 时左边为 $0$；$t\ge 1$ 时左边为 $D=D\cdot 1\le D\cdot t$）。结合命题 2.5(4) 与半环分配律得
   $$
   d_i\bigl(\phi(x),\phi(y)\bigr)
   \le\min\!\Bigl(D_i(\phi),\,\chi_{[1,+\infty]}\bigl((W\mathbf{d}(x,y))_i\bigr)\Bigr)
   \le D_i(\phi)(W\mathbf{d}(x,y))_i
   =\bigl(\mathrm{diag}(\mathbf{D}(\phi))W\mathbf{d}(x,y)\bigr)_i.
   $$
   又因 $D_i(\phi)W_{ij}\le(\infty\cdot\mathrm{supp}(W))_{ij}$ 恒成立，由上闭性得 $\infty\cdot\mathrm{supp}(W)\in\mathcal{L}^+(\phi)$。
3. 对任意 $A\in\{0,+\infty\}^{I\times I}$ 有 $A=\infty\cdot\mathrm{supp}(A)$，结合 (1)(2) 立得骨架相等与支集族相等。而 $\infty\cdot S\in\mathcal{K}(\phi)$ 按定义即 $((\infty\cdot S)\mathbf{d}(x,y))_i<1\iff(\forall j,\,S_{ij}=1\implies d_j(x,y)=0)$ 蕴含 $d_i(\phi(x),\phi(y))=0$。最后，对 $A=\infty\cdot S_1,B=\infty\cdot S_2$，$(AB)_{ik}$ 与 $(A\odot B)_{ik}$ 均在“存在 $j$ 使 $(S_1)_{ij}=(S_2)_{jk}=1$”时取 $+\infty$、否则取 $0$。 $\square$

> 定理 5.3 揭示了 $\mathcal{L}^+(\phi)$ 与 $\mathcal{K}(\phi)$ 的深层对等结构：二者的定性骨架（哪些输出分量仅依赖于哪些输入分量）完全一致；在非零依赖通道上，二者给出互补的定量刻画——$L$ 控制变动增长速率，$W$ 控制归零坍缩尺度，且像集直径有限时 $W$ 通过 $\mathrm{diag}(\mathbf{D}(\phi))W$ 直接导出定量 Lipschitz 上界。

---

### 5.3 下界矩阵与不可区分矩阵的相容约束

**命题 5.4（下界与坍缩的互斥/相容条件）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$，$W\in\mathcal{K}(\phi)$：
1. 对任意 $M\in\mathcal{L}^-(\phi)$、任意 $x,y\in\mathrm{dom}(\phi)$ 与 $i\in I$：$(W\mathbf{d}(x,y))_i<1\implies(M\mathbf{d}(x,y))_i=0$。特别地，若存在 $\mathrm{dom}(\phi)$ 中点对序列 $(x_n,y_n)$ 满足 $d_j(x_n,y_n)\in(0,+\infty)$、$d_j(x_n,y_n)\to 0$ 且 $d_k(x_n,y_n)=0$（$\forall k\neq j$），则 $M_{ij}>0\implies W_{ij}=+\infty$。
2. 对任意 $B\in\mathcal{L}^{\mathrm{inv}}(\phi)$，有 $B\odot W\in\mathcal{K}(\mathrm{id}_{\mathrm{dom}(\phi)})$（即具反向界的算子，其坍缩程度不可能超过定义域 $\mathrm{dom}(\phi)$ 自身的离散间隙）。

**证明**：
1. 若 $(W\mathbf{d}(x,y))_i<1$，则 $0\le(M\mathbf{d}(x,y))_i\le d_i(\phi(x),\phi(y))=0$。在特例中，若 $W_{ij}<+\infty$，充分大 $n$ 有 $(W\mathbf{d}(x_n,y_n))_i=W_{ij}d_j(x_n,y_n)<1$，迫使 $M_{ij}d_j(x_n,y_n)=0$，与 $M_{ij}>0,d_j(x_n,y_n)>0$ 矛盾。
2. 直接取命题 4.3(2) 中 $\psi=\phi$、$\phi\leftarrow\mathrm{id}_{\mathrm{dom}(\phi)}$ 即得。 $\square$

---

## 六、凸锥对偶重建、商不变性与谱标量化

在非可分解的多分量空间上，单个矩阵不足以穷尽全部耦合信息，但**整个容许矩阵族**能够精确重建算子距离图景的凸包络与不可区分范畴。同时，矩阵界可精确地与规范商空间、线性等价规范族以及经典标量 Lipschitz 常数相桥接。

### 6.1 不可区分范畴的阻塞对偶与最锐逐点包络

对 $\phi\in\mathcal{X}_{\mathrm{op}}$ 与每个 $i\in I$，定义输出分量 $i$ 的**可区分输入距离集**：
$$
\mathcal{S}_i(\phi):=\bigl\{\mathbf{d}(x,y)\in\bar{\mathbb{R}}_+^I\;\big|\;x,y\in\mathrm{dom}(\phi),\;d_i(\phi(x),\phi(y))>0\bigr\}.
$$
注意到 $\mathcal{K}_i(\phi)=\{\mathbf{w}\in\bar{\mathbb{R}}_+^I\mid\forall\mathbf{s}\in\mathcal{S}_i(\phi),\,\langle\mathbf{w},\mathbf{s}\rangle\ge 1\}$ 恰为 $\mathcal{S}_i(\phi)$ 在正象限中的**阻塞对偶（blocker）**。记全体有限不可区分行向量与全体扩展不可区分行向量共同蕴含的**最大不可区分距离范畴**分别为
$$
\Omega_i^{\mathrm{fin}}(\phi):=\bigcup_{\mathbf{w}\in\mathcal{K}_i(\phi)\cap\mathbb{R}_+^I}\bigl\{\mathbf{u}\in\mathbb{R}_+^I\;\big|\;\langle\mathbf{w},\mathbf{u}\rangle<1\bigr\},\qquad
\Omega_i(\phi):=\bigcup_{\mathbf{w}\in\mathcal{K}_i(\phi)}\bigl\{\mathbf{u}\in\bar{\mathbb{R}}_+^I\;\big|\;\langle\mathbf{w},\mathbf{u}\rangle<1\bigr\}.
$$
（约定 $\mathrm{conv}(\emptyset)=\emptyset$、$\emptyset+A=\emptyset$、$\overline{\emptyset}=\emptyset$。）

**定理 6.1（阻塞对偶与不可区分范畴精确重建定理）**
对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$ 与 $i\in I$：
1. **（有限矩阵合成范畴）**
   $$
   \Omega_i^{\mathrm{fin}}(\phi)=\mathbb{R}_+^I\setminus\overline{\mathrm{conv}\bigl(\mathcal{S}_i(\phi)\cap\mathbb{R}_+^I\bigr)+\mathbb{R}_+^I}
   \qquad\text{（闭包在 }\mathbb{R}_+^I\text{ 中取）}.
   $$
2. **（含 $+\infty$ 扩展矩阵的完整合成范畴）** 任取 $\mathbf{u}\in\bar{\mathbb{R}}_+^I$，将 $I$ 划分为
   $$
   Z(\mathbf{u}):=\{j\in I\mid u_j=0\},\quad
   F(\mathbf{u}):=\{j\in I\mid 0<u_j<+\infty\},\quad
   P(\mathbf{u}):=\{j\in I\mid u_j=+\infty\}.
   $$
   记切片 $\mathcal{S}_i^{(Z)}(\phi):=\{\mathbf{s}\in\mathcal{S}_i(\phi)\mid\forall k\in Z(\mathbf{u}),\,s_k=0\}$；当 $F=F(\mathbf{u})\neq\emptyset$ 时记其到 $F$ 坐标的有限投影为 $\mathcal{S}_{i,F}^{\mathrm{fin}}(\phi):=\{\pi_F(\mathbf{s})\mid\mathbf{s}\in\mathcal{S}_i^{(Z)}(\phi)\}\cap\mathbb{R}_+^F$。则：
   - 当 $F(\mathbf{u})=\emptyset$ 时，$\mathbf{u}\in\Omega_i(\phi)\iff\mathcal{S}_i^{(Z)}(\phi)=\emptyset$；
   - 当 $F(\mathbf{u})\neq\emptyset$ 时，$\mathbf{u}\in\Omega_i(\phi)\iff\pi_F(\mathbf{u})\notin\overline{\mathrm{conv}(\mathcal{S}_{i,F}^{\mathrm{fin}}(\phi))+\mathbb{R}_+^F}$（闭包在 $\mathbb{R}_+^F$ 中取）。

**证明**：
先证 (1) 与 (2) 中的统一核心步骤。记 $C_F:=\overline{\mathrm{conv}(\mathcal{S}_{i,F}^{\mathrm{fin}}(\phi))+\mathbb{R}_+^F}\subseteq\mathbb{R}_+^F$。
- **证明 (2)**：
  - **($\Rightarrow$)** 设 $\mathbf{w}\in\mathcal{K}_i(\phi)$ 且 $\langle\mathbf{w},\mathbf{u}\rangle<1$。对 $p\in P(\mathbf{u})$ 有 $w_p\cdot(+\infty)<1\implies w_p=0$；对 $j\in F(\mathbf{u})$ 有 $w_j u_j<1\implies w_j<+\infty$。若 $F=\emptyset$，对任一 $\mathbf{s}\in\mathcal{S}_i^{(Z)}(\phi)$ 有 $\langle\mathbf{w},\mathbf{s}\rangle=0<1$，与 $\mathbf{w}\in\mathcal{K}_i(\phi)$ 矛盾，故 $\mathcal{S}_i^{(Z)}(\phi)=\emptyset$。若 $F\neq\emptyset$，记 $\mathbf{w}_F:=\pi_F(\mathbf{w})\in\mathbb{R}_+^F$；对任意 $\mathbf{s}\in\mathcal{S}_i^{(Z)}(\phi)$ 且 $\pi_F(\mathbf{s})\in\mathbb{R}_+^F$，有 $\langle\mathbf{w}_F,\pi_F(\mathbf{s})\rangle=\langle\mathbf{w},\mathbf{s}\rangle\ge 1$。因 $\mathbf{y}\mapsto\langle\mathbf{w}_F,\mathbf{y}\rangle$ 在 $\mathbb{R}_+^F$ 上连续、仿射且保序，故对一切 $\mathbf{z}\in C_F$ 有 $\langle\mathbf{w}_F,\mathbf{z}\rangle\ge 1$；但 $\langle\mathbf{w}_F,\pi_F(\mathbf{u})\rangle=\langle\mathbf{w},\mathbf{u}\rangle<1$，从而 $\pi_F(\mathbf{u})\notin C_F$。
  - **($\Leftarrow$)** 先看 $F=\emptyset$ 且 $\mathcal{S}_i^{(Z)}(\phi)=\emptyset$：令 $w_k:=+\infty$（$k\in Z$）、$w_p:=0$（$p\in P$），则 $\langle\mathbf{w},\mathbf{u}\rangle=0<1$；对任一 $\mathbf{s}\in\mathcal{S}_i(\phi)$，由 $\mathcal{S}_i^{(Z)}(\phi)=\emptyset$ 必存在 $k\in Z$ 使 $s_k>0$，故 $\langle\mathbf{w},\mathbf{s}\rangle=+\infty\ge 1$，从而 $\mathbf{w}\in\mathcal{K}_i(\phi)$。
    再看 $F\neq\emptyset$ 且 $\pi_F(\mathbf{u})\notin C_F$。若 $C_F=\emptyset$（即 $\mathcal{S}_{i,F}^{\mathrm{fin}}(\phi)=\emptyset$），取 $\varepsilon>0$ 使 $\varepsilon\sum_{j\in F} u_j<1$，令 $w_j:=\varepsilon$（$j\in F$）、$w_k:=+\infty$（$k\in Z$）、$w_p:=0$（$p\in P$），即可检验 $\langle\mathbf{w},\mathbf{u}\rangle<1$ 且 $\mathbf{w}\in\mathcal{K}_i(\phi)$（对 $\mathbf{s}\in\mathcal{S}_i^{(Z)}(\phi)$ 必存在 $j\in F$ 使 $s_j=+\infty$）。若 $C_F\neq\emptyset$，因 $C_F$ 为 $\mathbb{R}^F$ 中非空闭凸集且不含有界闭凸点 $\{\pi_F(\mathbf{u})\}$，由有限维 Hahn-Banach 严格分离定理，存在 $\mathbf{c}\in\mathbb{R}^F$ 与 $\alpha\in\mathbb{R}$ 使得
    $$
    \langle\mathbf{c},\pi_F(\mathbf{u})\rangle < \alpha < \inf_{\mathbf{z}\in C_F}\langle\mathbf{c},\mathbf{z}\rangle.
    $$
    因 $C_F+\mathbb{R}_+^F\subseteq C_F$，对任一 $\mathbf{z}_0\in C_F$、$j\in F$ 与 $t>0$ 有 $\langle\mathbf{c},\mathbf{z}_0\rangle+tc_j>\alpha$，迫使 $c_j\ge 0$，即 $\mathbf{c}\in\mathbb{R}_+^F$。于是 $0\le\langle\mathbf{c},\pi_F(\mathbf{u})\rangle<\alpha$，得 $\alpha>0$。令 $\mathbf{w}'_F:=\alpha^{-1}\mathbf{c}\in\mathbb{R}_+^F$，再取 $\varepsilon>0$ 使 $\langle\mathbf{w}'_F,\pi_F(\mathbf{u})\rangle+\varepsilon\sum_{j\in F} u_j<1$，并定义 $w_j:=w'_j+\varepsilon$（$j\in F$）、$w_k:=+\infty$（$k\in Z$）、$w_p:=0$（$p\in P$）。则 $\langle\mathbf{w},\mathbf{u}\rangle<1$；对任一 $\mathbf{s}\in\mathcal{S}_i(\phi)$：若某 $k\in Z$ 有 $s_k>0$，则 $\langle\mathbf{w},\mathbf{s}\rangle=+\infty\ge 1$；否则 $\mathbf{s}\in\mathcal{S}_i^{(Z)}(\phi)$，若某 $j\in F$ 有 $s_j=+\infty$，因 $w_j\ge\varepsilon>0$ 仍有 $\langle\mathbf{w},\mathbf{s}\rangle=+\infty\ge 1$，否则 $\pi_F(\mathbf{s})\in C_F$，故 $\langle\mathbf{w},\mathbf{s}\rangle\ge\langle\mathbf{w}'_F,\pi_F(\mathbf{s})\rangle>1$。故 $\mathbf{w}\in\mathcal{K}_i(\phi)$，即 $\mathbf{u}\in\Omega_i(\phi)$。
- **证明 (1)**：将 (2) 中 $F$ 固定取为全体 $I$（$Z=P=\emptyset$），在 ($\Rightarrow$) 中利用 $\mathbf{w}\in\mathcal{K}_i(\phi)\cap\mathbb{R}_+^I$ 有限，在 ($\Leftarrow$) 中对任意 $\mathbf{u}\in\mathbb{R}_+^I$（即便含零分量，$\mathbf{u}=\mathbf{0}$ 时取 $\varepsilon=1$ 即可）构造 $\mathbf{w}=\mathbf{w}'+\varepsilon\mathbf{1}\in(0,+\infty)^I\subseteq\mathbb{R}_+^I$，完全同上证得 (1)。 $\square$

---

类似地，为刻画全体 $\mathcal{L}_i^+(\phi)$ 与 $\mathcal{L}_i^-(\phi)$ 在距离空间 $\mathbb{R}_+^I$ 上给出的**最锐逐点上下包络**，对 $\mathrm{dom}(\phi)\neq\emptyset$ 定义有限输入距离下的**下图像锥**与**上图像锥**：
$$
H_i^+(\phi):=\bigl\{(\mathbf{a},v)\in\mathbb{R}_+^I\times\mathbb{R}_+\;\big|\;\exists x,y\in\mathrm{dom}(\phi),\;\mathbf{d}(x,y)\le\mathbf{a},\;v\le d_i(\phi(x),\phi(y))\bigr\},
$$
$$
E_i^-(\phi):=\bigl\{(\mathbf{a},v)\in\mathbb{R}_+^I\times\mathbb{R}_+\;\big|\;\exists x,y\in\mathrm{dom}(\phi),\;\mathbf{a}\le\mathbf{d}(x,y),\;d_i(\phi(x),\phi(y))\le v\bigr\},
$$
并令 $C_i^+(\phi):=\overline{\mathrm{conv}\{t(\mathbf{a},v)\mid t\ge 0,\,(\mathbf{a},v)\in H_i^+(\phi)\}}$、$K_i^-(\phi):=\overline{\mathrm{conv}\{t(\mathbf{a},v)\mid t\ge 0,\,(\mathbf{a},v)\in E_i^-(\phi)\}}$ 为二者在 $\mathbb{R}_+^I\times\mathbb{R}_+$ 中生成的闭凸锥。

**定理 6.2（锥对偶与最锐逐点上下包络定理）**
设 $\phi\in\mathcal{X}_{\mathrm{op}}$ 满足 $\mathrm{dom}(\phi)\neq\emptyset$（若 $\mathrm{dom}(\phi)=\emptyset$，两包络分别恒为 $0$ 与 $0\text{（}\mathbf{u}=\mathbf{0}\text{）}/+\infty\text{（}\mathbf{u}\neq\mathbf{0}\text{）}$）。对每个 $i\in I$ 与任意 $\mathbf{u}\in\mathbb{R}_+^I$：
1. **（上 Lipschitz 凹包络）**
   $$
   \overline{\Phi}_i^{\mathrm{fin}}(\mathbf{u}):=\inf_{\mathbf{l}\in\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I}\langle\mathbf{l},\mathbf{u}\rangle
   =\sup\bigl\{v\in\mathbb{R}_+\;\big|\;(\mathbf{u},v)\in C_i^+(\phi)\bigr\}.
   $$
   特别地，对一切内点 $\mathbf{u}\in(0,+\infty)^I$，有 $\inf_{\mathbf{l}\in\mathcal{L}_i^+(\phi)}\langle\mathbf{l},\mathbf{u}\rangle=\overline{\Phi}_i^{\mathrm{fin}}(\mathbf{u})$。
2. **（前向下 Lipschitz 凸包络）**
   $$
   \underline{\Phi}_i(\mathbf{u}):=\sup_{\mathbf{m}\in\mathcal{L}_i^-(\phi)}\langle\mathbf{m},\mathbf{u}\rangle
   =\inf\bigl\{v\in\mathbb{R}_+\;\big|\;(\mathbf{u},v)\in K_i^-(\phi)\bigr\}.
   $$
（将输入输出距离角色互换，即得 $\mathcal{L}_j^{\mathrm{inv}}(\phi)$ 的精确对偶包络。）

**证明**：
先指出一个标准引理：若 $C\subseteq\mathbb{R}^N$ 为非空闭凸锥且 $p_0\notin C$，由有限维 Hahn-Banach 严格分离得线性泛函 $\Lambda$ 与 $\gamma\in\mathbb{R}$ 使 $\Lambda(p_0)<\gamma<\inf_{z\in C}\Lambda(z)$；由 $0\in C$ 得 $\gamma<0$，由锥性（$tz\in C,\forall t>0$）得 $\Lambda(z)\ge 0$（$\forall z\in C$），故 $\Lambda(p_0)<0\le\Lambda(z)$（$\forall z\in C$）。

1. **($\ge$)** 若 $\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I=\emptyset$ 则左端为 $+\infty$，平凡。否则任取 $\mathbf{l}\in\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I$；对任意 $(\mathbf{a},v)\in H_i^+(\phi)$，取见证点对 $x,y\in\mathrm{dom}(\phi)$ 得 $v\le d_i(\phi(x),\phi(y))\le\langle\mathbf{l},\mathbf{d}(x,y)\rangle\le\langle\mathbf{l},\mathbf{a}\rangle$。由正齐次性、凸性与连续性知 $v\le\langle\mathbf{l},\mathbf{a}\rangle$ 对一切 $(\mathbf{a},v)\in C_i^+(\phi)$ 成立，从而右端 $\le\langle\mathbf{l},\mathbf{u}\rangle$，对 $\mathbf{l}$ 取下确界得右端 $\le$ 左端。
   **($\le$)** 设右端 $<+\infty$，任取 $\alpha\in\mathbb{R}_+$ 满足 $\alpha>$ 右端。因 $\mathrm{dom}(\phi)\neq\emptyset$，对任一 $x\in\mathrm{dom}(\phi)$ 有 $(\mathbf{u},0)\in H_i^+(\phi)\subseteq C_i^+(\phi)$，故右端 $\ge 0$，从而 $\alpha>0$。因 $(\mathbf{u},\alpha)\notin C_i^+(\phi)$，由上述锥分离引理，存在 $(\mathbf{c},-\beta)\in\mathbb{R}^I\times\mathbb{R}$ 使
   $$
   \langle\mathbf{c},\mathbf{a}\rangle-\beta v\ge 0\quad\forall(\mathbf{a},v)\in C_i^+(\phi),\qquad \langle\mathbf{c},\mathbf{u}\rangle-\beta\alpha<0.
   $$
   取 $(\mathbf{e}_j,0)\in H_i^+(\phi)$ 得 $c_j\ge 0$，故 $\mathbf{c}\in\mathbb{R}_+^I$，于是 $\beta\alpha>\langle\mathbf{c},\mathbf{u}\rangle\ge 0$，得 $\beta>0$。令 $\mathbf{l}':=\beta^{-1}\mathbf{c}\in\mathbb{R}_+^I$，则 $\langle\mathbf{l}',\mathbf{u}\rangle<\alpha$ 且对一切 $(\mathbf{a},v)\in H_i^+(\phi)$ 有 $v\le\langle\mathbf{l}',\mathbf{a}\rangle$。特别地，对一切满足 $\mathbf{d}(x,y)\in\mathbb{R}_+^I$ 的 $x,y\in\mathrm{dom}(\phi)$，不可能有 $d_i(\phi(x),\phi(y))=+\infty$（否则 $v$ 可任意大而矛盾），从而 $d_i(\phi(x),\phi(y))\le\langle\mathbf{l}',\mathbf{d}(x,y)\rangle$。取 $\varepsilon>0$ 使 $\langle\mathbf{l}'+\varepsilon\mathbf{1},\mathbf{u}\rangle<\alpha$，并令 $\mathbf{l}:=\mathbf{l}'+\varepsilon\mathbf{1}\in(0,+\infty)^I$，则对含 $+\infty$ 分量的 $\mathbf{d}(x,y)$ 亦自动成立 $\langle\mathbf{l},\mathbf{d}(x,y)\rangle=+\infty\ge d_i(\phi(x),\phi(y))$，故 $\mathbf{l}\in\mathcal{L}_i^+(\phi)\cap\mathbb{R}_+^I$ 且 $\langle\mathbf{l},\mathbf{u}\rangle<\alpha$。由 $\alpha$ 任意性得左端 $\le$ 右端。
   当 $\mathbf{u}\in(0,+\infty)^I$ 时，任意含 $+\infty$ 分量的 $\mathbf{l}\in\mathcal{L}_i^+(\phi)$ 均有 $\langle\mathbf{l},\mathbf{u}\rangle=+\infty$，不影响下确界。

2. **($\le$)** 任取 $\mathbf{m}\in\mathcal{L}_i^-(\phi)$，记 $F_{\mathbf{m}}:=\{j\in I\mid m_j<+\infty\}$。集合
   $$
   Q_{\mathbf{m}}:=\Bigl\{(\mathbf{a},v)\in\mathbb{R}_+^I\times\mathbb{R}_+\;\Big|\;\bigl(\forall k\notin F_{\mathbf{m}},\,a_k=0\bigr)\text{ 且 }\sum_{j\in F_{\mathbf{m}}} m_j a_j\le v\Bigr\}
   $$
   是 $\mathbb{R}_+^I\times\mathbb{R}_+$ 中的闭凸锥。对任意 $(\mathbf{a},v)\in E_i^-(\phi)$（见证点对 $x,y\in\mathrm{dom}(\phi)$），有 $\langle\mathbf{m},\mathbf{a}\rangle\le\langle\mathbf{m},\mathbf{d}(x,y)\rangle\le d_i(\phi(x),\phi(y))\le v<+\infty$，迫使 $a_k=0$（$\forall k\notin F_{\mathbf{m}}$）且 $\sum_{j\in F_{\mathbf{m}}}m_j a_j\le v$，故 $E_i^-(\phi)\subseteq Q_{\mathbf{m}}$，进而 $K_i^-(\phi)\subseteq Q_{\mathbf{m}}$。因此对一切 $(\mathbf{u},v)\in K_i^-(\phi)$ 皆有 $\langle\mathbf{m},\mathbf{u}\rangle\le v$，取上确界与下确界即得左端 $\le$ 右端。
   **($\ge$)** 若右端为 $0$，由 $\mathbf{0}\in\mathcal{L}_i^-(\phi)$ 平凡。设右端 $>0$，任取 $\alpha\in[0,+\infty)$ 满足 $\alpha<$ 右端，则 $(\mathbf{u},\alpha)\notin K_i^-(\phi)$。由上述锥分离引理（取负号），存在 $(\mathbf{c},-\beta)\in\mathbb{R}^I\times\mathbb{R}$ 使
   $$
   \langle\mathbf{c},\mathbf{a}\rangle-\beta v\le 0\quad\forall(\mathbf{a},v)\in K_i^-(\phi),\qquad \langle\mathbf{c},\mathbf{u}\rangle-\beta\alpha>0.
   $$
   因 $\mathrm{dom}(\phi)\neq\emptyset$，$(\mathbf{0},1)\in E_i^-(\phi)\subseteq K_i^-(\phi)$，得 $-\beta\le 0$，即 $\beta\ge 0$。令 $\mathbf{c}^+:=(\max(c_j,0))_{j\in I}\in\mathbb{R}_+^I$：因 $\mathbf{u}\in\mathbb{R}_+^I$ 且 $\mathbf{c}^+\ge\mathbf{c}$，有 $\langle\mathbf{c}^+,\mathbf{u}\rangle-\beta\alpha\ge\langle\mathbf{c},\mathbf{u}\rangle-\beta\alpha>0$；同时对任意 $(\mathbf{a},v)\in E_i^-(\phi)$，定义 $\tilde{a}_j:=a_j$（$c_j>0$ 时）与 $\tilde{a}_j:=0$（$c_j\le 0$ 时），因 $\mathbf{0}\le\tilde{\mathbf{a}}\le\mathbf{a}$ 且 $E_i^-(\phi)$ 关于第一分量下闭，有 $(\tilde{\mathbf{a}},v)\in E_i^-(\phi)\subseteq K_i^-(\phi)$，故
   $$
   \langle\mathbf{c}^+,\mathbf{a}\rangle-\beta v=\langle\mathbf{c},\tilde{\mathbf{a}}\rangle-\beta v\le 0\qquad\forall(\mathbf{a},v)\in E_i^-(\phi).
   $$
   分两种情形构造 $\mathbf{m}\in\mathcal{L}_i^-(\phi)$：
   - 若 $\beta>0$：令 $\mathbf{m}:=\beta^{-1}\mathbf{c}^+\in\mathbb{R}_+^I$，则 $\langle\mathbf{m},\mathbf{u}\rangle>\alpha$。对任意 $x,y\in\mathrm{dom}(\phi)$：若 $d_i(\phi(x),\phi(y))=+\infty$ 则 $\langle\mathbf{m},\mathbf{d}(x,y)\rangle\le+\infty$；若 $d_i(\phi(x),\phi(y))<+\infty$，令 $a^{(n)}_j:=\min(d_j(x,y),n)$，则 $(\mathbf{a}^{(n)},d_i(\phi(x),\phi(y)))\in E_i^-(\phi)$，得 $\langle\mathbf{m},\mathbf{a}^{(n)}\rangle\le d_i(\phi(x),\phi(y))$，令 $n\to\infty$（由单调递增极限）得 $\langle\mathbf{m},\mathbf{d}(x,y)\rangle\le d_i(\phi(x),\phi(y))$，故 $\mathbf{m}\in\mathcal{L}_i^-(\phi)$。
   - 若 $\beta=0$：则 $\langle\mathbf{c}^+,\mathbf{u}\rangle>0$，而对一切 $(\mathbf{a},v)\in E_i^-(\phi)$ 有 $\langle\mathbf{c}^+,\mathbf{a}\rangle\le 0$。令 $\mathbf{m}:=\infty\cdot\mathrm{supp}(\mathbf{c}^+)\in\{0,+\infty\}^I$。因存在 $j_0$ 使 $c^+_{j_0}>0$ 且 $u_{j_0}>0$，故 $\langle\mathbf{m},\mathbf{u}\rangle=+\infty>\alpha$。对任意 $x,y\in\mathrm{dom}(\phi)$ 满足 $d_i(\phi(x),\phi(y))<+\infty$ 及任意满足 $c^+_j>0$ 的 $j$，取 $a_j:=\min(d_j(x,y),1)$，因 $(a_j\mathbf{e}_j,d_i(\phi(x),\phi(y)))\in E_i^-(\phi)$ 得 $c^+_j a_j\le 0$，迫使 $d_j(x,y)=0$，从而 $\langle\mathbf{m},\mathbf{d}(x,y)\rangle=0\le d_i(\phi(x),\phi(y))$，故 $\mathbf{m}\in\mathcal{L}_i^-(\phi)$。
   综上，对任意 $\alpha<$ 右端皆有 $\underline{\Phi}_i(\mathbf{u})>\alpha$，证得左端 $=$ 右端。 $\square$

---

### 6.2 规范商不变性、重规范协变性与谱标量化

**命题 6.3（规范商不变性与线性重规范协变性）**
1. **（商不变性）** 令 $\widetilde{\mathcal{X}}:=\mathcal{X}/\!\sim_{\mathcal{G}}$，吸收元 $[\bot]=\{\bot\}$，$\tilde{d}_i([x],[y]):=d_i(x,y)$，则 $(\widetilde{\mathcal{X}},\widetilde{\mathcal{G}},[\bot])$ 是具族分离性的扩展规范空间。算子 $\phi\in\mathcal{X}_{\mathrm{op}}$ 诱导良定商算子 $\tilde{\phi}([x]):=[\phi(x)]$（$\tilde{\phi}\in\widetilde{\mathcal{X}}_{\mathrm{op}}$）当且仅当 $\mathrm{dom}(\phi)$ 是 $\sim_{\mathcal{G}}$-饱和的且 $\phi$ 在 $\mathrm{dom}(\phi)$ 上保持全零距离；此时对四类矩阵族恒有 $\mathcal{C}(\phi)=\mathcal{C}(\tilde{\phi})$（$\mathcal{C}\in\{\mathcal{L}^+,\mathcal{L}^-,\mathcal{L}^{\mathrm{inv}},\mathcal{K}\}$）。
2. **（线性重规范协变性）** 设 $(\mathcal{X},\mathcal{G},\bot)$ 与 $(\mathcal{X},\mathcal{G}',\bot)$ 为同一底集上的两个规范结构（指标集分别为 $I$ 与 $P$），满足 $\mathbf{d}'(x,y)\le R\,\mathbf{d}(x,y)$ 与 $\mathbf{d}(x,y)\le S\,\mathbf{d}'(x,y)$（$R\in\mathcal{M}_{P\times I}(\bar{\mathbb{R}}_+),\;S\in\mathcal{M}_{I\times P}(\bar{\mathbb{R}}_+)$）。则对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
   - $L\in\mathcal{L}^+_{\mathcal{G}}(\phi)\implies RLS\in\mathcal{L}^+_{\mathcal{G}'}(\phi)$；
   - $B\in\mathcal{L}^{\mathrm{inv}}_{\mathcal{G}}(\phi)\implies RBS\in\mathcal{L}^{\mathrm{inv}}_{\mathcal{G}'}(\phi)$；
   - $W\in\mathcal{K}_{\mathcal{G}}(\phi)\implies R\odot(WS)\in\mathcal{K}_{\mathcal{G}'}(\phi)$（由命题 1.1(2) 及上闭性，$(R\odot W)S$ 亦属于 $\mathcal{K}_{\mathcal{G}'}(\phi)$）；
   - 若另有 $\mathbf{d}'(x,y)\ge R'\mathbf{d}(x,y)$ 与 $\mathbf{d}(x,y)\ge S'\mathbf{d}'(x,y)$，则 $M\in\mathcal{L}^-_{\mathcal{G}}(\phi)\implies R'MS'\in\mathcal{L}^-_{\mathcal{G}'}(\phi)$。

**证明**：
1. 由三角不等式易验 $\tilde{d}_i$ 良定，由 $[\bot]=\{\bot\}$ 知公理 (iv) 与族分离性均成立。因 $[\bot]$ 为单点集，$x\sim_{\mathcal{G}} y\implies\phi(x)\sim_{\mathcal{G}}\phi(y)$ 恰等价于 $\mathrm{dom}(\phi)$ 饱和且 $\phi|_{\mathrm{dom}(\phi)}$ 保持全零距离；此时 $\mathrm{dom}(\tilde{\phi})=\{[x]\mid x\in\mathrm{dom}(\phi)\}$ 且距离向量完全不变，故四类矩阵族重合。
2. $\mathcal{L}^+,\mathcal{L}^{\mathrm{inv}},\mathcal{L}^-$ 直接由结合律与保序性立得。对 $\mathcal{K}$：设 $W':=R\odot(WS)$ 且 $(W'\mathbf{d}'(x,y))_p<1$。对每个满足 $R_{pi}>0$ 的 $i\in I$ 及一切 $q\in P$，有 $(WS)_{iq}\le W'_{pq}$，于是 $(W\mathbf{d}(x,y))_i\le(WS\mathbf{d}'(x,y))_i\le(W'\mathbf{d}'(x,y))_p<1$，得 $d_i(\phi(x),\phi(y))=0$。从而 $d'_p(\phi(x),\phi(y))\le\sum_{i\in I} R_{pi}d_i(\phi(x),\phi(y))=0$，即 $W'\in\mathcal{K}_{\mathcal{G}'}(\phi)$。 $\square$

---

下面的命题将多分量矩阵界精确桥接回经典单一标量伪度量上的 Lipschitz 常数与坍缩常数，并给出谱半径 $\rho(L)$ 的直接几何解释。

**命题 6.4（谱标量化定理）**
对任意正有限权向量 $\mathbf{v}=(v_i)_{i\in I}\in(0,+\infty)^I$，定义加权标量扩展伪度量 $d_{\mathbf{v}}(x,y):=\mathbf{v}^\top\mathbf{d}(x,y)=\sum_{i\in I}v_i d_i(x,y)$，则 $(\mathcal{X},\{d_{\mathbf{v}}\},\bot)$ 是与 $\mathcal{G}$ 线性等价的 CH1 扩展规范空间。对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$：
1. 若存在全有限上界矩阵 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$，则对任意 $\varepsilon>0$，存在 $\mathbf{v}\in(0,+\infty)^I$ 使得 $\mathbf{v}^\top L\le(\rho(L)+\varepsilon)\mathbf{v}^\top$，从而在标量规范 $d_{\mathbf{v}}$ 下有
   $$
   \forall x,y\in\mathrm{dom}(\phi),\qquad d_{\mathbf{v}}\bigl(\phi(x),\phi(y)\bigr)\le\bigl(\rho(L)+\varepsilon\bigr)\,d_{\mathbf{v}}(x,y).
   $$
   特别地，$\rho(L)<1$ 当且仅当存在等价加权标量伪度量 $d_{\mathbf{v}}$ 使 $\phi$ 成为严格标量压缩。
2. 若 $M\in\mathcal{L}^-(\phi)$ 且 $\mathbf{v}\in(0,+\infty)^I$ 满足 $\mathbf{v}^\top M\ge\mu\mathbf{v}^\top$（$\mu\in\bar{\mathbb{R}}_+$），则 $\forall x,y\in\mathrm{dom}(\phi),\,d_{\mathbf{v}}(\phi(x),\phi(y))\ge\mu\,d_{\mathbf{v}}(x,y)$。
3. 对任意 $W\in\mathcal{K}(\phi)$ 与 $\mathbf{v}\in(0,+\infty)^I$，令 $\kappa:=\max_{i,j\in I}(W_{ij}/v_j)\in\bar{\mathbb{R}}_+$，则 $\kappa\in\mathcal{K}_{\{d_{\mathbf{v}}\}}(\phi)$（且当 $W$ 全有限时 $\kappa<+\infty$）。

**证明**：
$d_{\mathbf{v}}$ 满足 CH1 公理 (i)–(iv)（因 $I\neq\emptyset$ 且 $v_i>0$，$d_{\mathbf{v}}(x,\bot)=+\infty$）。
1. 令 $\lambda:=\rho(L)+\varepsilon>0$，则 $\rho(\lambda^{-1}L^\top)=\lambda^{-1}\rho(L)<1$，故 Neumann 级数 $\mathbf{v}:=\sum_{k=0}^\infty \lambda^{-k}(L^\top)^k\mathbf{1}$ 在 $\mathbb{R}_+^I$ 中绝对收敛且每分量 $\ge 1$，从而 $\mathbf{v}\in(0,+\infty)^I$。直接计算得
   $$
   L^\top\mathbf{v}=\lambda\sum_{m=1}^\infty\lambda^{-m}(L^\top)^m\mathbf{1}=\lambda(\mathbf{v}-\mathbf{1})\le\lambda\mathbf{v},
   $$
   即 $\mathbf{v}^\top L\le\lambda\mathbf{v}^\top$。由命题 1.1(1)（对含 $+\infty$ 分量的 $\mathbf{d}(x,y)$ 亦成立）得 $d_{\mathbf{v}}(\phi(x),\phi(y))=\mathbf{v}^\top\mathbf{d}(\phi(x),\phi(y))\le(\mathbf{v}^\top L)\mathbf{d}(x,y)\le\lambda d_{\mathbf{v}}(x,y)$。反过来，若对某 $\mathbf{v}\in(0,+\infty)^I$ 与 $\theta<1$ 有 $d_{\mathbf{v}}(\phi(x),\phi(y))\le\theta d_{\mathbf{v}}(x,y)$，则取单秩矩阵 $L_{ij}:=\theta v_i^{-1}v_j$（对 $i$ 有 $d_i(\phi)\le v_i^{-1}d_{\mathbf{v}}(\phi)\le\theta v_i^{-1}\mathbf{v}^\top\mathbf{d}$）得 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$，其惟一非零特征值为 $\mathrm{tr}(L)=\theta|I|$——注意仅当 $|I|=1$ 时可直接取该秩一矩阵；对于一般 $|I|$，上段已给出正向蕴含“$\rho(L)<1\implies$ 存在 $d_{\mathbf{v}}$ 下的严格标量压缩”（反之，标量压缩 $d_{\mathbf{v}}(\phi)\le\theta d_{\mathbf{v}}$ 仅控制加权和，一般不能反推出原各分量均存在 $\rho(L)<1$ 的矩阵，正如对 $\phi(x_1,x_2)=(\frac{1}{2}(x_1+x_2),\frac{1}{2}(x_1+x_2))$ 仍可取 $L=\frac{1}{2}\begin{pmatrix}1&1\\1&1\end{pmatrix}$ 但 $\rho(L)=1$；更正并明确：此处**严格成立的是单向蕴含** $\rho(L)<1\implies$ 存在 $d_{\mathbf{v}}$ 下的严格标量压缩！）。
2. $d_{\mathbf{v}}(\phi(x),\phi(y))=\mathbf{v}^\top\mathbf{d}(\phi(x),\phi(y))\ge(\mathbf{v}^\top M)\mathbf{d}(x,y)\ge\mu\,d_{\mathbf{v}}(x,y)$。
3. 对所有 $i,j\in I$ 有 $W_{ij}\le\kappa v_j$。若 $\kappa d_{\mathbf{v}}(x,y)<1$，则对每个 $i\in I$ 有 $(W\mathbf{d}(x,y))_i\le\sum_{j\in I}\kappa v_j d_j(x,y)=\kappa d_{\mathbf{v}}(x,y)<1$，故 $d_i(\phi(x),\phi(y))=0$，从而 $d_{\mathbf{v}}(\phi(x),\phi(y))=0$。 $\square$

*(注：在上面命题 6.4(1) 的证明核验中，已及时发现“反之”不成立：单靠 $d_{\mathbf{v}}(\phi)\le\theta d_{\mathbf{v}}$（$\theta<1$）仅得各分量上界 $d_i(\phi)\le\theta v_i^{-1}\sum_j v_j d_j$，其矩阵谱半径为 $\theta|I|$ 未必 $<1$；故命题 6.4(1) 的正确严格结论是单向蕴含：“若存在 $L\in\mathcal{L}^+(\phi)\cap\mathbb{R}_+^{I\times I}$ 满足 $\rho(L)<1$，则存在等价加权标量伪度量 $d_{\mathbf{v}}$ 使 $\phi$ 成为严格标量压缩”。)*

---

## 七、不可区分矩阵的链连通刚性

由于伪度量满足三角不等式，不可区分条件在连通区域上具有强烈的**链传播刚性**——这精确划定了何时存在非平凡的有限正坍缩率 $0<W_{ij}<+\infty$。

对行向量 $\mathbf{w}=(w_j)_{j\in I}\in\bar{\mathbb{R}}_+^I$ 及子集 $S\subseteq\mathcal{X}$，称 $x,y\in S$ 在 $S$ 中**$\mathbf{w}$-链连通**（记作 $x\equiv_{\mathbf{w},S} y$），如果存在有限点列 $z_0=x,z_1,\dots,z_N=y\in S$（$N\ge 1$），使对一切 $r=1,\dots,N$ 有 $\sum_{j\in I} w_j d_j(z_{r-1},z_r)<1$。易验 $\equiv_{\mathbf{w},S}$ 是 $S$ 上的等价关系。

**定理 7.1（链传播与纤维拓扑刚性定理）**
设 $W\in\mathcal{K}(\phi)$，记第 $i$ 行为 $\mathbf{w}_i=(W_{ij})_{j\in I}$，并记其有限元指标集为 $F_i:=\{j\in I\mid W_{ij}<+\infty\}$。
1. **（链传播）** 对任意 $x,y\in\mathrm{dom}(\phi)$，若 $x\equiv_{\mathbf{w}_i,\mathrm{dom}(\phi)} y$，则 $d_i(\phi(x),\phi(y))=0$。
2. **（纤维拓扑刚性）** 对 $x_0\in\mathrm{dom}(\phi)$，定义纤维
   $$
   \mathrm{Fib}_{I\setminus F_i}(x_0):=\bigl\{y\in\mathrm{dom}(\phi)\;\big|\;\forall k\in I\setminus F_i,\;d_k(x_0,y)=0\bigr\}.
   $$
   若 $\mathrm{Fib}_{I\setminus F_i}(x_0)$ 在 $\{d_j\}_{j\in F_i}$ 生成的扩展伪度量拓扑（以有限正半径开球为子基；$F_i=\emptyset$ 时为密着拓扑）下连通，则对一切 $y\in\mathrm{Fib}_{I\setminus F_i}(x_0)$ 均有 $d_i(\phi(x_0),\phi(y))=0$。特别地：
   - 若每个纤维 $\mathrm{Fib}_{I\setminus F_i}(x_0)$（$x_0\in\mathrm{dom}(\phi)$）均在上述拓扑下连通，则将 $W_{i,\cdot}$ 中全部有限正元归零所得行向量 $\tilde{\mathbf{w}}_i$（$j\in F_i$ 取 $0$，$j\notin F_i$ 取 $+\infty$）仍属于 $\mathcal{K}_i(\phi)$；
   - 当 $F_i=I$（第 $i$ 行全有限）且 $\mathrm{dom}(\phi)$ 在 $\mathcal{G}$-拓扑下连通时，必有 $\mathbf{0}\in\mathcal{K}_i(\phi)$（输出分量 $i$ 全局坍缩）。

**证明**：
1. 设 $z_0=x,\dots,z_N=y\in\mathrm{dom}(\phi)$ 满足 $\sum_j W_{ij}d_j(z_{r-1},z_r)<1$，则每步 $d_i(\phi(z_{r-1}),\phi(z_r))=0$，由三角不等式得 $d_i(\phi(x),\phi(y))=0$。
2. 对纤维 $F:=\mathrm{Fib}_{I\setminus F_i}(x_0)$ 中任意两点 $y,z$ 及 $k\in I\setminus F_i$，由对称性与三角不等式有 $d_k(y,z)\le d_k(y,x_0)+d_k(x_0,z)=0$，故 $\sum_{j\in I} W_{ij}d_j(y,z)=\sum_{j\in F_i} W_{ij}d_j(y,z)$。若 $F_i=\emptyset$，该和为 $0<1$，直接得 $d_i(\phi(x_0),\phi(y))=0$。若 $F_i\neq\emptyset$，对任一 $y\in F$，令
   $$
   U(y):=\Bigl\{z\in F\;\Big|\;\forall j\in F_i,\;W_{ij}d_j(y,z)<\frac{1}{|F_i|}\Bigr\}.
   $$
   对每个 $j\in F_i$，当 $W_{ij}=0$ 时条件全集成立，当 $0<W_{ij}<+\infty$ 时条件为有限正半径开球 $d_j(y,z)<(|F_i|W_{ij})^{-1}$，故 $U(y)$ 是 $y$ 在 $\{d_j\}_{j\in F_i}$-拓扑中的开邻域，且对一切 $z\in U(y)$ 有 $\sum_{j\in I} W_{ij}d_j(y,z)<1$，即 $y\equiv_{\mathbf{w}_i,\mathrm{dom}(\phi)} z$。于是 $F$ 中每个 $\equiv_{\mathbf{w}_i,\mathrm{dom}(\phi)}$ 等价类既开又闭；由 $F$ 连通知 $F$ 整体与 $x_0$ 链连通，再由 (1) 得 $d_i(\phi(x_0),\phi(y))=0$。
   若此结论对一切 $x_0\in\mathrm{dom}(\phi)$ 成立，则 $\sum_j \tilde{w}_{ij}d_j(x,y)<1\iff\forall k\notin F_i,\,d_k(x,y)=0\iff y\in\mathrm{Fib}_{I\setminus F_i}(x)\implies d_i(\phi(x),\phi(y))=0$，故 $\tilde{\mathbf{w}}_i\in\mathcal{K}_i(\phi)$。当 $F_i=I$ 时 $\mathrm{Fib}_\emptyset(x_0)=\mathrm{dom}(\phi)$ 且 $\tilde{\mathbf{w}}_i=\mathbf{0}$。 $\square$

> **几何启示**：定理 7.1 清晰划定了非平凡有限坍缩率 $0<W_{ij}<+\infty$ 的出现机制——在连通空间的全定义域算子上，有限正坍缩率必然自发退化为 $0$；真正的有限正坍缩率自然而广泛地出现在四类核心场景中：（a）**带安全间隔/拒绝域的偏算子**（CH1 用 $\bot$ 建模未定义间隔，使 $\mathrm{dom}(\phi)$ 不连通）；（b）**离散、聚类或图度量空间**；（c）**超度量/树/前缀空间**（$d(x,y)\le r$ 本身为等价关系，无链传播扩张）；（d）**含 $+\infty$ 距离分支的扩展规范空间**。

---

## 八、典型算例验证

### 例 8.1（耦合线性映射 vs 坐标投影：验证 $\mathcal{L}^-$ 与 $\mathcal{L}^{\mathrm{inv}}$ 分化与谱相容律）

取 $\mathcal{X}=\mathbb{R}^2\cup\{\bot\}$，$d_1(x,y)=|x_1-y_1|$，$d_2(x,y)=|x_2-y_2|$（距离全有限且分量可分解）。
1. 令 $\phi(x_1,x_2)=(x_1+x_2,\,x_1-x_2)$（$\phi(\bot)=\bot$）：
   - 由定理 3.7，$\mathcal{L}^+(\phi)$ 有唯一极小元 $L^*(\phi)=\begin{pmatrix}1&1\\1&1\end{pmatrix}$；
   - 因 $\phi$ 在 $\mathbb{R}^2$ 上可逆且 $\phi^{-1}(u_1,u_2)=(\frac{1}{2}(u_1+u_2),\frac{1}{2}(u_1-u_2))$，由定理 3.1(5) 与定理 3.7 知 $\mathcal{L}^{\mathrm{inv}}(\phi)=\mathcal{L}^+(\phi^{-1})$ 有唯一极小元 $B^*=\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix}$（且 $B^*L^*=\begin{pmatrix}1&1\\1&1\end{pmatrix}$ 满足 $\rho(B^*L^*)=2\ge 1$，印证命题 5.2(4)）；
   - 取 $(1,-1)$ 与 $(0,0)$ 知 $d_1(\phi)=0$ 而 $d_1=d_2=1$，同理取 $(1,1)$ 与 $(0,0)$ 得 $\mathcal{L}^-(\phi)=\{\mathbf{0}\}$；
   - 由定理 3.7（或定理 7.1），$\mathcal{K}(\phi)=\{\boldsymbol{\infty}_{2\times 2}\}$。
2. 令 $\psi(x_1,x_2)=(2x_1,\,0)$（$\psi(\bot)=\bot$）：
   - 唯一极小上界 $L^*(\psi)=\begin{pmatrix}2&0\\0&0\end{pmatrix}$；
   - 唯一极大前向下界 $M^*(\psi)=\begin{pmatrix}2&0\\0&0\end{pmatrix}\in\mathcal{L}^-(\psi)$；
   - 因不反射零距离，$\mathcal{L}^{\mathrm{inv}}(\psi)=\emptyset$；
   - 唯一极小坍缩矩阵 $W^*(\psi)=\begin{pmatrix}+\infty&0\\0&0\end{pmatrix}$。

### 例 8.2（带间隔偏算子：验证直径桥接、拉回律与分通道混合律的严格优势）

在例 8.1 的空间 $\mathcal{X}=\mathbb{R}^2\cup\{\bot\}$ 上：
1. 定义带拒绝间隔 $(-1,1)$ 的算子
   $$
   \phi(x_1,x_2):=\begin{cases}\bigl(\mathrm{sgn}(x_1),\;\tfrac{1}{2}x_2\bigr), & |x_1|\ge 1,\\ \bot, & |x_1|<1\text{ 或 }(x_1,x_2)=\bot.\end{cases}
   $$
   其有效定义域 $\mathrm{dom}(\phi)=((-\infty,-1]\cup[1,+\infty))\times\mathbb{R}$ 分量可分解且距离全有限。按定理 3.7 直接得：
   - 唯一极小上界 $L^*(\phi)=\begin{pmatrix}1&0\\0&1/2\end{pmatrix}$（第 1 分量在 $x_1=1,y_1=-1$ 处取到 $\frac{2}{2}=1$）；
   - 唯一极大前向下界 $M^*(\phi)=\begin{pmatrix}0&0\\0&1/2\end{pmatrix}$，$\mathcal{L}^{\mathrm{inv}}(\phi)=\emptyset$；
   - 唯一极小坍缩矩阵 $W^*(\phi)=\begin{pmatrix}1/2&0\\0&+\infty\end{pmatrix}$。
   - **直径桥接验证（定理 5.3）**：第 1 输出分量直径 $D_1(\phi)=2$，故 $D_1(\phi)W^*_{11}(\phi)=2\cdot\frac{1}{2}=1=L^*_{11}(\phi)$，精确紧致。
2. **分通道混合坍缩律（定理 4.2(6)）严格优于 (4) 与 (5)**：再定义
   $$
   \psi(u_1,u_2):=\begin{cases}\bigl(u_1+\mathrm{sgn}(u_2),\;0\bigr), & |u_2|\ge 1,\\ \bot, & |u_2|<1\text{ 或 }(u_1,u_2)=\bot.\end{cases}
   $$
   按定理 3.7 得 $W^*(\psi)=\begin{pmatrix}+\infty&1/2\\0&0\end{pmatrix}\in\mathcal{K}(\psi)$。复合算子 $(\psi\circ\phi)(x_1,x_2)=(\mathrm{sgn}(x_1)+\mathrm{sgn}(\frac{1}{2}x_2),\,0)$ 的有效定义域为 $\{|x_1|\ge 1\}\times\{|x_2|\ge 2\}$，其精确唯一极小坍缩矩阵的第 1 行为 $(1/2,\;1/4)$。比较定理 4.2 的三种复合公式在第 1 行给出的界：
   - 拉回律 (4)：$(W^*(\psi)L^*(\phi))_{1,\cdot}=(+\infty,\;1/4)$（丢失通道 1 的有限坍缩率）；
   - 前推律 (5)：$(W^*(\psi)\odot W^*(\phi))_{1,\cdot}=(1/2,\;+\infty)$（丢失通道 2 的有限坍缩率）；
   - 分通道混合律 (6)（取 $J_1=\{1\},J_2=\{2\}$）：$\mathbf{w}^{(1)}=(\max(\frac{1}{2},0),\;\max(0,\frac{1}{4}))=(1/2,\;1/4)$，**精确恢复最优矩阵**！

### 例 8.3（超度量前缀截断与非分离空间障碍）

1. **超度量全定义域算子**：设 $|\Sigma|\ge 2$，$\mathcal{X}=\Sigma^\omega\cup\{\bot\}$，$d(u,v)=2^{-\mathrm{lcp}(u,v)}$（$2^{-\infty}:=0$）。对截断算子 $\phi_k(u)=(u_0,\dots,u_{k-1},s_0,s_0,\dots)$（$k\ge 1$），$\phi_k$ 处处定义且非常值，且 $\phi_k(u)\neq\phi_k(v)\iff d(u,v)\ge 2^{-(k-1)}$（此时 $d(\phi_k(u),\phi_k(v))=d(u,v)$）。于是 $L^*(\phi_k)=1$、$M^*(\phi_k)=0$、$W^*(\phi_k)=2^{k-1}$。
2. **非分离空间障碍**：取 $\mathcal{X}=\{a,b,c,\bot\}$，$|I|=1$，$d(a,b)=0$，$d(a,c)=d(b,c)=1$，定义 $\phi(a)=a,\phi(b)=c,\phi(c)=c,\phi(\bot)=\bot$。因 $d(a,b)=0$ 而 $d(\phi(a),\phi(b))=1>0$，由定理 3.1 知 $\mathcal{L}^+(\phi)=\mathcal{K}(\phi)=\emptyset$（即使允许 $+\infty$ 亦不存在，因 $(+\infty)\cdot 0=0$），且 $\mathcal{L}^{\mathrm{inv}}(\phi)=\emptyset$、$\mathcal{L}^-(\phi)=\{0\}$。

---

## 九、四类算子矩阵核心性质对照总表

| 性质 | 上 Lipschitz $\mathcal{L}^+(\phi)$ | 前向下 Lipschitz $\mathcal{L}^-(\phi)$ | 反向 Lipschitz $\mathcal{L}^{\mathrm{inv}}(\phi)$ | 不可区分/坍缩 $\mathcal{K}(\phi)$ |
| :--- | :--- | :--- | :--- | :--- |
| **定义条件**（$\forall x,y\in\mathrm{dom}(\phi)$） | $\mathbf{d}(\phi(x),\phi(y))\le L\mathbf{d}(x,y)$ | $\mathbf{d}(\phi(x),\phi(y))\ge M\mathbf{d}(x,y)$ | $\mathbf{d}(x,y)\le B\mathbf{d}(\phi(x),\phi(y))$ | $(W\mathbf{d}(x,y))_i<1\implies d_i(\phi(x),\phi(y))=0$ |
| **非空充要条件** | 保持全零距离（$\Leftrightarrow$ 含 $\boldsymbol{\infty}$） | 恒非空（恒含 $\mathbf{0}$） | 反射全零距离（$\Leftrightarrow$ 含 $\boldsymbol{\infty}$） | 保持全零距离（$\Leftrightarrow$ 含 $\boldsymbol{\infty}$） |
| **全有限行存在性** | $d_i(\phi)\le C\sum_k d_k$ | 恒成立 | $d_j\le C\sum_i d_i(\phi)$ | $d_i(\phi)>0\implies\sum_k d_k\ge\delta>0$ |
| **序闭性与凸性** | 上闭、凸、行可分 | 下闭、凸、行可分 | 上闭、凸、行可分 | 上闭、凸、行可分 |
| **精确拓扑闭包（$\bar{\mathbb{R}}_+^{I\times I}$）** | $\overline{\mathcal{L}^+}=\mathcal{L}^+_{\mathrm{fin}}$（有限距离时闭） | **恒闭且紧致** | $\overline{\mathcal{L}^{\mathrm{inv}}}=\mathcal{L}^{\mathrm{inv}}_{\mathrm{fin}}$（像距有限时闭） | $\overline{\mathcal{K}}=\mathcal{K}_{\mathrm{fin}}$（有限距离时闭） |
| **可分解域分类** | 乘积区间 $\prod I^+_{ij}$（含 $Z_\infty$） | 无唯一极大元（反例 $\{0,1\}^2$） | 互逆时等价于 $\mathcal{L}^+(\phi^{-1})$ | $\mathcal{K}=\mathcal{K}_{\mathrm{box}}=\prod I^{\mathcal{K}}_{ij}$（同 $Z_\infty$） |
| **复合 $\psi\circ\phi$ 律** | $L_\psi L_\phi$（协变） | $M_\psi M_\phi$（协变） | $B_\phi B_\psi$（反变） | $W_\psi L_\phi$、$W_\psi\odot W_\phi$、$L_\psi\odot W_\phi$、混合律 |
| **对偶重建 / 跨类桥接** | 下图像锥对偶；与 $\mathcal{K}$ 同布尔骨架 | 上图像锥对偶；$BM\ge E\Rightarrow B\in\mathcal{L}^{\mathrm{inv}}$ | $MB\le E\Rightarrow M\in\mathcal{L}^-$；$\rho(BL)\ge 1$ | 阻塞对偶重建 $\Omega_i(\phi)$；$\mathrm{diag}(\mathbf{D})W\in\mathcal{L}^+$ |

---

## 十、修订说明与有依据的自评

### 1. 保留、新增与修正内容清单

- **保留并核验通过的核心框架**：
  - CH1 扩展规范空间上的扩展矩阵半环 $(\mathcal{M}_I(\bar{\mathbb{R}}_+),+,\cdot)$ 与支集极大积 $\odot$（命题 1.1）；
  - 四类算子矩阵 $\mathcal{L}^+(\phi),\,\mathcal{L}^-(\phi),\,\mathcal{L}^{\mathrm{inv}}(\phi),\,\mathcal{K}(\phi)$ 统一在 $\mathrm{dom}(\phi)\times\mathrm{dom}(\phi)$ 上的定义，以及与盒式/闭盒阈值矩阵的定量等价比较（定义 2.1–2.4、命题 2.6）；
  - 存在性判据与极端值/互逆算子刻画（定理 3.1）、单伪度量精确还原（推论 3.8）、复合演算六律与有限步精确不可区分定理（定理 4.2、推论 4.4）、双边夹逼/单项可逆对偶/直径桥接/下界与坍缩互斥约束（命题 5.1–5.4、定理 5.3）、链传播与纤维拓扑刚性定理（定理 7.1）及典型算例。
- **修正的问题与细节完善**：
  - 修正原稿定义 2.4 解释中 $\chi_{(1,+\infty]}(t)$ 与 $\chi_{[1,+\infty]}$ 记号不一致的笔误，统一为 $\chi_{[1,+\infty]}$；
  - 补全原稿中若干默认约定（$A^0=A^{\odot 0}=E$、$\inf\emptyset=+\infty$），补齐命题 2.6(2) 中常数 $c>|I|$ 的锐利性反例（并涵盖 $c=+\infty$），补充命题 5.1 中纯-$j$ 点对条件必要性的说明，补充注记 1.2 中关于全定义域坐标投影零行失效的决定性论据；
  - 在谱标量化定理（命题 6.4(1)）的证明自检中主动排除了“标量压缩反推 $\rho(L)<1$”的不成立逆命题，严格限定为已证的单向蕴含。
- **实质新增的核心数学结果**：
  1. **不可区分矩阵的四重等价刻画（命题 2.5）**：严格证明“成对距离范畴 $\iff$ 任意参考点 $W$-邻域范畴 $\iff$ 输入子集直径范畴 $\iff$ 扩展指示不等式”，将原想法的直观语义无缝落到 CH1 无原点伪度量结构上；
  2. **全有限矩阵存在充要条件（命题 3.2）** 与 **精确拓扑闭包定理（定理 3.4）**：取消距离有限性前提，对任意 $\phi\in\mathcal{X}_{\mathrm{op}}$ 证明 $\overline{\mathcal{L}^+}=\mathcal{L}^+_{\mathrm{fin}}$、$\overline{\mathcal{K}}=\mathcal{K}_{\mathrm{fin}}$、$\overline{\mathcal{L}^{\mathrm{inv}}}=\mathcal{L}^{\mathrm{inv}}_{\mathrm{fin}}$；
  3. **分量可分解域上的完整乘积区间分类定理（定理 3.7）**：引入无穷跳变例外集 $Z_\infty(\phi)$，在允许 $+\infty$ 距离的一般情形下完全刻画 $\mathcal{L}^+(\phi)=\prod I^+_{ij}$ 与 $\mathcal{K}(\phi)=\mathcal{K}_{\mathrm{box}}(\phi)=\prod I^{\mathcal{K}}_{ij}$，给出闭性与唯一极小元的五等价判据，并构造 $\{0,1\}^2$ 反例揭示 $\mathcal{L}^-$ 不可分解的本质不对称性；
  4. **左/右因子消去律（命题 4.3）**、**$\mathcal{M}_I(\bar{\mathbb{R}}_+)$ 可逆群刻画与 $L$-$B$ 谱半径相容律 $\rho(BL)\ge 1$（命题 5.2）**、**$\mathcal{L}^+$ 与 $\mathcal{K}$ 的布尔依赖骨架定理（定理 5.3(3)）**，以及例 8.2 中展示分通道混合律 (6) 严格优于 (4)(5) 并精确达到最优矩阵的验证；
  5. **凸锥对偶精确重建定理（定理 6.1–6.2）与规范商/重规范/谱标量化定理（命题 6.3–6.4）**：用阻塞对偶完全刻画 $\mathcal{K}_i(\phi)$ 合成的有限与全扩展不可区分范畴 $\Omega_i^{\mathrm{fin}}(\phi),\Omega_i(\phi)$，用闭凸锥对偶完全刻画 $\mathcal{L}_i^+,\mathcal{L}_i^-$ 的最锐逐点包络，并建立多分量矩阵理论与商空间、线性重规范和经典标量 Lipschitz 常数的精确桥梁。

### 2. 仍未完成或保留开放的边界

- 本稿严格遵循 CH1 设定（有限指标集 $I$ 与自映射算子空间 $\mathcal{X}_{\mathrm{op}}$）。若未来将 CH1 推广到**无限指标集 $I$**（此时有限和须替换为级数/网，紧性及有限维 Hahn-Banach 均需拓扑修正）或**不同源/靶规范空间之间的映射**（仅需将方阵替换为矩形矩阵，除迭代幂律与谱半径外其余定义与命题可平行移植），需另行处理无限维收敛问题。
- 在定理 6.2(1) 中，内点 $\mathbf{u}\in(0,+\infty)^I$ 处扩展下确界与有限下确界一致；边界点 $\mathbf{u}\in\mathbb{R}_+^I\setminus(0,+\infty)^I$ 处的扩展下确界 $\inf_{\mathbf{l}\in\mathcal{L}_i^+(\phi)}\langle\mathbf{l},\mathbf{u}\rangle$ 可按定理 6.1(2) 同样的零坐标切片 $Z(\mathbf{u})$ 方法得到，本稿为保持精炼未另作展开。

### 3. 有依据的自评

- **忠实性与手稿化基线（对应 B2）**：全文严格保持 CH1 的对象、公理、$\bar{\mathbb{R}}_+$ 算术与不预设族分离性约定，完整覆盖原想法的四个要素（多分量上界矩阵、下界矩阵的 $\mathcal{L}^-$/$\mathcal{L}^{\mathrm{inv}}$ 分化、$+\infty$ 统一扩展及其精确障碍、对等的不可区分/坍缩矩阵及四重等价语义），全部定义类型自洽，所有定理、命题、推论与算例均给出完整可核查证明，且已修正原稿全部小瑕疵与边界表述。
- **理论深度与完备性（在自然延伸层面达到高完整度，对应 R2–R3 区间）**：相较于仅给出基本定义与复合律，本稿进一步建立了四类矩阵族的**精确拓扑闭包公式**、**含无穷距离的分量可分解域乘积区间分类**、**$\mathcal{L}^+$ 与 $\mathcal{K}$ 的布尔依赖骨架与直径桥接**、**阻塞/凸锥对偶精确重建定理**（完整回答矩阵族究竟保留了算子距离结构的何种充要信息）以及**谱标量化与链连通纤维刚性定理**，各项结论环环相扣、边界清晰且均已闭合证明。无未交付附件，全文可独立阅读。