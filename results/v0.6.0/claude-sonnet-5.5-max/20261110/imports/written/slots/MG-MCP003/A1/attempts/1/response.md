# 算子的矩阵型 Lipschitz 上/下界、∞ 扩展与坍缩阈值矩阵

## 总览：想法与数学对象的对应

| 原想法 | 数学化 |
|---|---|
| 单一 Lip 常数不够，用矩阵表示分量间关系 | **上 Lipschitz 矩阵** $L$：$D(\phi x,\phi y)\preceq L\,D(x,y)$（定义 1.1(U)） |
| 除上限外还要下限 | **下 Lipschitz 矩阵** $\ell$：$\ell\,D(x,y)\preceq D(\phi x,\phi y)$（定义 1.1(D)） |
| 不是所有函数都有 Lip，支持 ∞ | 矩阵元取值于 $[0,\infty]$，配合 $0\cdot\infty=0$。定理 2.2 给出存在性的精确条件 |
| 输入落入某范畴则输出不可区分，要一个与 Lip 对等的矩阵 | **坍缩阈值矩阵** $\Theta$：$D(x,y)\preceq\Theta_{j\cdot}\Rightarrow d_j(\phi x,\phi y)=0$（定义 1.1(C)）。命题 1.2 说明它与 Lip 矩阵同构 |

我做了四个解读选择，后文严格遵守。

- **(I1)** “矩阵”取联合型（求和型）增益矩阵，即向量值度量意义下的 Perov 型。逐对型是它的特例（命题 2.6），例 3.1 说明为什么不能只用逐对型。
- **(I2)** 全局量词取遍整个 $\mathcal X$（含 $\bot$），这样未定义性由 $\infty$ 算术自动处理。限制到子集的版本见注 4.1。
- **(I3)** “不可区分”指零距离（$d_j=0$ 或 $D=\mathbf 0$），不是“相等”。这是因为本卷不预设族分离。
- **(I4)** “输入落入一定范畴”指输入距离向量落入盒子 $\prod_i[0,\Theta_{ji}]$。

---

## 0. 记号、约定与预备

**0.1 算术。** 记 $\mathbb S:=\bar{\mathbb R}_+=[0,\infty]$，运算按 CH1 约定（$0\cdot\infty=0$，$a\cdot\infty=\infty\ (a>0)$，$a+\infty=\infty$）。另约定 $\infty/2=\infty$。

**引理 0.1** $(\mathbb S,+,\cdot,0,1)$ 是交换半环，$+$ 与 $\cdot$ 关于 $\le$ 单调。对 $a>0$，$b\mapsto ab$ 是 $\mathbb S$ 上保序双射且固定 $0,\infty$。

*证* 若某个因子为 $0$，结合律与分配律两边都是 $0$。否则诸因子在 $(0,\infty]$ 内，乘法是通常乘法的延拓，故结合。当 $a>0$ 时，$b\mapsto ab$ 在 $[0,\infty)$ 上是伸缩，且 $\infty\mapsto\infty$，所以它对 $+$ 可加，即 $a(b+c)=ab+ac$（$a=0$ 平凡）。单调性：$ab>0$ 时 $a,b>0$，增大因子不会使积变小；$ab=0$ 平凡。∎

**注 0.2（唯一的“病灶”）** 乘法保定向上确界，但不保下确界：$\inf_n\frac1n\cdot\infty=\infty\neq0=0\cdot\infty$。后文所有“最优常数取不到”的现象都只来源于此（见命题 2.6、例 3.4、例 3.6）。

**0.2 矩阵。** $I$ 有限非空，$n=|I|$。记 $\mathbb M:=\mathbb S^{I\times I}$。行指标 $j$ 是**输出分量**，列指标 $i$ 是**输入分量**。定义 $(Av)_j=\sum_iA_{ji}v_i$ 和 $(AB)_{ji}=\sum_kA_{jk}B_{ki}$。$A\le B$ 表示逐元序，$\preceq$ 表示 $\mathbb S^I$ 的逐分量序。$E$ 是单位阵，$O$ 是零阵，$\Omega$ 是全 $\infty$ 阵。$\mathbf 0,\boldsymbol\infty\in\mathbb S^I$ 是全 $0$、全 $\infty$ 向量。

**引理 0.3** 设 $A,B,C\in\mathbb M$，$u,v\in\mathbb S^I$，$\lambda\in\mathbb S$。

- (a) $A(u+v)=Au+Av$，$A(\lambda u)=\lambda Au$，$(AB)u=A(Bu)$，$(AB)C=A(BC)$，$Eu=u$。
- (b) 若 $A\le B$ 且 $u\preceq v$，则 $Au\preceq Bv$。
- (c) $(Au)_j=0\iff\forall i:\ A_{ji}=0$ 或 $u_i=0$。$(Au)_j=\infty\iff\exists i:\ A_{ji}u_i=\infty$，即 ($A_{ji}=\infty$ 且 $u_i>0$) 或 ($A_{ji}>0$ 且 $u_i=\infty$)。特别地，$(A\boldsymbol\infty)_j=\infty$ 当且仅当第 $j$ 行非零，否则为 $0$。

*证* (a)(b) 由引理 0.1 和 $I$ 有限得到。(c) 非负项之和为 $0$ 当且仅当各项为 $0$；有限个项之和为 $\infty$ 当且仅当某项为 $\infty$。∎

**0.3 距离向量与“不可区分”。** 记 $D(x,y):=(d_i(x,y))_{i\in I}$。由 (i)–(iv) 得：

- $D(x,x)=\mathbf 0$。
- $D$ 对称。
- $D(x,z)\preceq D(x,y)+D(y,z)$。
- $x\ne\bot\Rightarrow D(x,\bot)=\boldsymbol\infty$。

定义三个等价关系（均由三角不等式得到）：

- $x\sim_j y:\iff d_j(x,y)=0$（单分量不可区分）。
- $x\sim y:\iff D(x,y)=\mathbf 0$（全分量不可区分）。
- $x\approx y:\iff D(x,y)\in[0,\infty)^I$（有限距离）。

因 $I\neq\emptyset$，$\boldsymbol\infty\ne\mathbf 0$ 且 $\boldsymbol\infty\notin[0,\infty)^I$，所以 $\{\bot\}$ 是 $\sim$ 与 $\approx$ 的单点类。**不预设族分离**，所以 $\sim$ 一般比“$=$”粗。

**定义 0.4** 称 $\phi$ **零相容**，若 $D(x,y)=\mathbf 0\Rightarrow D(\phi x,\phi y)=\mathbf 0$，即 $\phi$ 在商空间 $\mathcal X/{\sim}$ 上良定义。族分离时，每个算子都零相容。

---

## 1. 定义

固定 $\phi\in\mathcal X_{\rm op}$。

**定义 1.1**

- **(U) 上 Lipschitz 矩阵。** $L\in\mathbb M$ 满足 $D(\phi x,\phi y)\preceq L\,D(x,y)$ 对一切 $x,y\in\mathcal X$ 成立。即对每个 $j$，$d_j(\phi x,\phi y)\le\sum_iL_{ji}d_i(x,y)$。全体记 $\mathcal L^+(\phi)$。元素全有限者称**有限型**，允许 $\infty$ 者称**扩展型**。
- **(D) 下 Lipschitz 矩阵。** $\ell\in\mathbb M$ 满足 $\ell\,D(x,y)\preceq D(\phi x,\phi y)$ 对一切 $x,y$ 成立。全体记 $\mathcal L^-(\phi)$。$(\ell,L)\in\mathcal L^-(\phi)\times\mathcal L^+(\phi)$ 称**双 Lipschitz 对**。
- **(C) 坍缩（不可区分）阈值矩阵。** $\Theta\in\mathbb M$ 满足：对每个 $j$ 和一切 $x,y$，若 $d_i(x,y)\le\Theta_{ji}$ 对所有 $i$ 成立，则 $d_j(\phi x,\phi y)=0$。全体记 $\mathcal C(\phi)$。

**读法**

- $L_{ji}$ 是第 $i$ 输入分量到第 $j$ 输出分量的增益上限。对角元是同分量增益，非对角元是分量间“串扰”。
- $L_{ji}=0$：$i$ 对 $j$ 无传递。由 $0\cdot\infty=0$，即使 $d_i=\infty$ 也不起作用。
- $L_{ji}=\infty$：无有限控制，但只要 $d_i>0$ 就不再约束。
- $\ell_{ji}$ 是增益下限。$\ell_{ji}=\infty$ 表示 $d_i(x,y)>0\Rightarrow d_j(\phi x,\phi y)=\infty$。
- $\Theta_{ji}$：当所有输入分量同时落入盒子 $\prod_i[0,\Theta_{ji}]$ 时，输出的第 $j$ 分量必不可区分。$\Theta_{ji}=\infty$ 表示对 $i$ 分量不设限（与 $L_{ji}=0$ 对应）。$\Theta_{ji}=0$ 表示只要求 $i$ 分量不可区分（与 $L_{ji}>0$ 对应）。

**命题 1.2（响应函数刻画，三者“对等”的精确含义）** 对 $v\in\mathbb S^I$ 定义

$$\rho_j(v)=\sup\{d_j(\phi x,\phi y):D(x,y)\preceq v\},\qquad \varrho_j(v)=\inf\{d_j(\phi x,\phi y):D(x,y)\succeq v\}\quad(\inf\emptyset=\infty).$$

则：

1. $L\in\mathcal L^+(\phi)\iff\rho_j(v)\le(Lv)_j$ 对一切 $j,v$ 成立。
2. $\ell\in\mathcal L^-(\phi)\iff(\ell v)_j\le\varrho_j(v)$ 对一切 $j,v$ 成立。
3. $\Theta\in\mathcal C(\phi)\iff\rho_j(\Theta_{j\cdot})=0$ 对一切 $j$ 成立。

等价地：$L$ 是线性上包络，$\ell$ 是线性下包络，$\Theta$ 是**阶梯上包络**。后者是指 $d_j(\phi x,\phi y)\le\chi_{\Theta_j}(D(x,y))$，其中 $\chi_t(v)=0\ (v\preceq t)$，$\chi_t(v)=\infty$（否则）。Lip 与坍缩因此是对同一响应函数的两种“读数”。

*证* (1) “$\Rightarrow$”：若 $D(x,y)\preceq v$，则 $d_j'\le(LD)_j\le(Lv)_j$（引理 0.3(b)），取上确界。“$\Leftarrow$”：取 $v=D(x,y)$。(2) 同理，取下确界。(3) 由定义直接得到。∎

**推论 1.3**

- (i) $\mathcal L^+(\phi)$ 向上封闭，$\mathcal L^-(\phi)$ 与 $\mathcal C(\phi)$ 向下封闭。
- (ii) 三者都**按行解耦**：每一行（每个输出分量）独立。
- (iii) 一般**没有最小的上矩阵**，上矩阵不唯一。例：$\mathcal X=\mathbb R\cup\{\bot\}$，$d_1=|x-y|$，$d_2=2|x-y|$，$\phi=\mathrm{id}$。第 1 行的容许集是 $\{r:r_1+2r_2\ge1\}$，其中 $(1,0)$ 与 $(0,\tfrac12)$ 都是极小元且不可比。故“Lipschitz 矩阵”是容许性质，不是 $\phi$ 的唯一取值。典范数值见命题 2.6。
- (iv) $|I|=1$ 时，三者化为经典的 $d(\phi x,\phi y)\le L\,d(x,y)$、$\ell\,d(x,y)\le d(\phi x,\phi y)$ 以及“$d(x,y)\le\Theta\Rightarrow\phi x\sim\phi y$”。

---

## 2. 基本性质

**定理 2.1（复合与恒等）** 设 $\phi,\psi\in\mathcal X_{\rm op}$。则 $\psi\circ\phi\in\mathcal X_{\rm op}$，且 $\mathrm{dom}(\psi\circ\phi)=\phi^{-1}(\mathrm{dom}\,\psi)$。

1. $E\in\mathcal L^+(\phi)\cap\mathcal L^-(\phi)\iff D(\phi x,\phi y)=D(x,y)$ 恒成立（逐分量等距）。
2. 若 $L\in\mathcal L^+(\phi)$，$L'\in\mathcal L^+(\psi)$，则 $L'L\in\mathcal L^+(\psi\circ\phi)$。特别地，$L^m\in\mathcal L^+(\phi^m)$。
3. 若 $\ell\in\mathcal L^-(\phi)$，$\ell'\in\mathcal L^-(\psi)$，则 $\ell'\ell\in\mathcal L^-(\psi\circ\phi)$。
4. 若 $\Theta\in\mathcal C(\phi)$，$L'\in\mathcal L^+(\psi)$，令 $\Theta''_{ji}:=\min\{\Theta_{ki}:L'_{jk}>0\}$（$\min\emptyset=\infty$），则 $\Theta''\in\mathcal C(\psi\circ\phi)$。
5. 若 $L\in\mathcal L^+(\phi)$，$\Theta'\in\mathcal C(\psi)$，且 $\tau\in\mathbb S^I$ 满足 $L\tau\preceq\Theta'_{j\cdot}$，则 $D(x,y)\preceq\tau\Rightarrow d_j(\psi\phi x,\psi\phi y)=0$。特别地，当 $L$ 有限时，令 $s_k=\sum_iL_{ki}$，$r_j=\min\{\Theta'_{jk}/s_k:s_k>0\}$（$\min\emptyset=\infty$），则 $\max_id_i(x,y)\le r_j\Rightarrow d_j(\psi\phi x,\psi\phi y)=0$。

*证*

- (1) 直接由定义。
- (2) 由单调性和结合律：$D(\psi\phi x,\psi\phi y)\preceq L'D(\phi x,\phi y)\preceq L'(LD(x,y))=(L'L)D(x,y)$。
- (3) $(\ell'\ell)D=\ell'(\ell D)\preceq\ell'D(\phi x,\phi y)\preceq D(\psi\phi x,\psi\phi y)$。
- (4) 设 $D(x,y)\preceq\Theta''_{j\cdot}$。对每个满足 $L'_{jk}>0$ 的 $k$，有 $D(x,y)\preceq\Theta_{k\cdot}$，故 $d_k(\phi x,\phi y)=0$。于是 $d_j(\psi\phi x,\psi\phi y)\le\sum_kL'_{jk}d_k(\phi x,\phi y)=0$。其中 $L'_{jk}=0$ 的项即使 $d_k(\phi x,\phi y)=\infty$ 也为 $0$，这里用到了 $0\cdot\infty=0$。
- (5) 若 $D(x,y)\preceq\tau$，则 $D(\phi x,\phi y)\preceq LD(x,y)\preceq L\tau\preceq\Theta'_{j\cdot}$，由 $\Theta'$ 的定义得 $d_j(\psi\phi x,\psi\phi y)=0$。再取 $\tau=(r_j,\dots,r_j)$：若 $s_k=0$，则 $(L\tau)_k=0$；若 $s_k>0$，则 $(L\tau)_k=s_kr_j\le\Theta'_{jk}$。∎

**推论** 具有扩展上矩阵（或有限上矩阵、或下矩阵）的算子在复合下封闭，构成 $(\mathcal X_{\rm op},\circ)$ 的子幺半群，矩阵乘法与复合对应。

**定理 2.2（存在性：∞ 能做到什么、做不到什么）** 对 $\phi\in\mathcal X_{\rm op}$，下列等价：

- (a) $\mathcal L^+(\phi)\ne\emptyset$。
- (b) $\Omega\in\mathcal L^+(\phi)$。
- (c) $\phi$ 零相容。
- (d) $O\in\mathcal C(\phi)$。
- (e) $\mathcal C(\phi)\ne\emptyset$。

另外 $O\in\mathcal L^-(\phi)$ 恒成立。

*证*

- (a)⇒(c)：若 $D(x,y)=\mathbf 0$，则 $D(\phi x,\phi y)\preceq L\mathbf 0=\mathbf 0$。
- (c)⇒(b)：若 $D(x,y)=\mathbf 0$，则 $D(\phi x,\phi y)=\mathbf 0\preceq\Omega\mathbf 0$。若 $D(x,y)\ne\mathbf 0$，则某个 $d_i>0$，$(\Omega D)_j\ge\infty\cdot d_i=\infty$。
- (b)⇒(a) 平凡。
- (c)⇔(d)：$O\in\mathcal C(\phi)$ 恰说 $D(x,y)=\mathbf 0\Rightarrow D(\phi x,\phi y)=\mathbf 0$。
- (d)⇒(e) 平凡。
- (e)⇒(c)：若 $D(x,y)=\mathbf 0$，则 $D\preceq\Theta_{j\cdot}$ 对每个 $j$ 成立，故 $D(\phi x,\phi y)=\mathbf 0$。
- $O\in\mathcal L^-$ 显然。∎

**推论** 族分离时，每个算子都有扩展 Lipschitz 矩阵 $\Omega$。这正是引入 $\infty$ 的“统一表达”。**不分离时 $\infty$ 兜不住底**：见例 3.2。因为 $0\cdot\infty=0$，“零距离变正距离”（比值 $a/0=\infty$）无法用乘积型不等式表达。

**命题 2.3（$\bot$ 与有效定义域）** 设 $\mathrm{dom}\,\phi\ne\emptyset$（这里用到 $\mathcal X\setminus\{\bot\}\neq\emptyset$ 才有非平凡算子）。

1. 若 $x\in\mathrm{dom}\,\phi$，$y\notin\mathrm{dom}\,\phi$，$L\in\mathcal L^+(\phi)$，则对每个 $j$ 存在 $i$ 使 $L_{ji}d_i(x,y)=\infty$。特别地，$L$ 的每一行非零。
2. 若 $L\in\mathcal L^+(\phi)$ 是**有限型**，且 $x\in\mathrm{dom}\,\phi$，$x\approx y$，则 $y\in\mathrm{dom}\,\phi$。即有限型算子的 $\mathrm{dom}$ 是若干 $\approx$-类之并，“有定义/无定义”不会在有限距离内跳变。
3. 若 $\ell\in\mathcal L^-(\phi)$ 有非零行，则 $\phi^{-1}(\bot)=\{\bot\}$。反之，只要某个 $x\ne\bot$ 有 $\phi x=\bot$，就有 $\mathcal L^-(\phi)=\{O\}$。若 $\ell_{ji}>0$，则 $d_j(\phi x,\phi y)=0\Rightarrow d_i(x,y)=0$，且 $d_i(x,y)=\infty\Rightarrow d_j(\phi x,\phi y)=\infty$。若 $\ell$ 的每一列都非零，则 $D(\phi x,\phi y)=\mathbf 0\Rightarrow D(x,y)=\mathbf 0$，即 $\phi$ 在 $\mathcal X/{\sim}$ 上单射。
4. 若 $\Theta\in\mathcal C(\phi)$，$x\in\mathrm{dom}\,\phi$，$y\notin\mathrm{dom}\,\phi$，则对每个 $j$ 存在 $i$ 使 $d_i(x,y)>\Theta_{ji}$。特别地，$\Theta$ 的每一行含有限元。

*证* 设 $x\in\mathrm{dom}\,\phi$，$y\notin\mathrm{dom}\,\phi$，则 $x\neq\bot$，$\phi y=\bot$，$\phi x\ne\bot$，故 $D(\phi x,\phi y)=\boldsymbol\infty$。

- (1) 由定义和引理 0.3(c) 得到前一句。取 $y=\bot$ 时 $D(x,\bot)=\boldsymbol\infty$，得 $\boldsymbol\infty\preceq L\boldsymbol\infty$，故各行非零。
- (2) 若 $y\notin\mathrm{dom}\,\phi$，则 $\infty=d_j'\le\sum_iL_{ji}d_i(x,y)$，而右边是有限和，矛盾。
- (3) 若 $x\ne\bot$ 且 $\phi x=\bot$，对 $(x,\bot)$ 有 $\ell\boldsymbol\infty\preceq D(\bot,\bot)=\mathbf 0$，故 $\ell=O$。其余各条由 $0=d_j'\ge\ell_{ji}d_i$ 及 $\ell_{ji}\cdot\infty=\infty$ 得到。
- (4) $d_j(\phi x,\phi y)=\infty\neq0$，故定义 1.1(C) 的前提不成立。∎

**命题 2.4（三类矩阵之间的关系）**

- (a)（零元↔∞阈值）若 $L\in\mathcal L^+(\phi)$，令 $\Theta^L_{ji}=0$（$L_{ji}>0$），$=\infty$（$L_{ji}=0$），则 $\Theta^L\in\mathcal C(\phi)$。*证*：若 $d_i\le\Theta^L_{ji}$ 对所有 $i$ 成立，则 $L_{ji}>0$ 的项有 $d_i=0$，$L_{ji}=0$ 的项由 $0\cdot\infty=0$ 也为 $0$，故 $d_j'\le\sum_iL_{ji}d_i=0$。因此 Lip 矩阵只给出 $\{0,\infty\}$ 型阈值，**有限正阈值是新信息**（例 3.5）。
- (b)（下界与坍缩互斥）若 $\ell\in\mathcal L^-(\phi)$，$\Theta\in\mathcal C(\phi)$，且 $D(x,y)\preceq\Theta_{j\cdot}$，则 $\ell_{ji}d_i(x,y)=0$ 对一切 $i$ 成立。*证*：$0=d_j'\ge\sum_i\ell_{ji}d_i$。故 $\ell_{ji}>0$ 时，坍缩盒内的点对都有 $d_i=0$。
- (c)（一致性）若 $\ell\in\mathcal L^-(\phi)$，$L\in\mathcal L^+(\phi)$，则 $\ell D(x,y)\preceq LD(x,y)$ 对一切 $x,y$ 成立。
- (d)（全分量坍缩）若 $\Theta\in\mathcal C(\phi)$，$\tau_i:=\min_j\Theta_{ji}$，则 $D(x,y)\preceq\tau\Rightarrow D(\phi x,\phi y)=\mathbf 0$。
- (e)（球形读法）记 $B(c;r)=\{x:d_i(x,c)\le r_i\ \forall i\}$。若 $\Theta\in\mathcal C(\phi)$，则 $x,y\in B(c;\Theta_{j\cdot}/2)\Rightarrow d_j(\phi x,\phi y)=0$。反之，若 $\phi$ 在所有 $B(c;r)$ 上第 $j$ 分量不可区分，则 $r$ 是第 $j$ 个坍缩行（取 $c=x$）。故“成对”与“成球”两种读法至多差因子 $2$（三角不等式）。

**命题 2.5（标量化：与单一 Lip 常数的关系）** 记 $d_\vee=\max_id_i$，$d_\Sigma=\sum_id_i$。它们仍是满足 (i)–(iv) 的扩展伪度量，故 $(\mathcal X,\{d_\vee\},\bot)$ 仍是规范空间。

1. 若 $L\in\mathcal L^+(\phi)$，则 $d_\vee(\phi x,\phi y)\le\big(\max_j\sum_iL_{ji}\big)d_\vee(x,y)$，且 $d_\Sigma(\phi x,\phi y)\le\big(\max_i\sum_jL_{ji}\big)d_\Sigma(x,y)$。
2. 若 $d_\vee(\phi x,\phi y)\le c\,d_\vee(x,y)$，则 $c\mathbf J\in\mathcal L^+(\phi)$（$\mathbf J$ 为全 $1$ 阵）。
3. 若 $\ell\in\mathcal L^-(\phi)$，则 $d_\Sigma(\phi x,\phi y)\ge\big(\min_i\sum_j\ell_{ji}\big)d_\Sigma(x,y)$。
4. $\mathrm{diag}(c_j)\in\mathcal L^+(\phi)\iff d_j(\phi x,\phi y)\le c_jd_j(x,y)$（分量式 Lipschitz）。非对角元描述分量间串扰。

*证* (1) $d_j'\le\sum_iL_{ji}d_i\le(\sum_iL_{ji})d_\vee$，再对 $j$ 取最大。第二式对 $j$ 求和即可。(2) $d_j'\le d_\vee'\le c\,d_\vee\le c\sum_id_i$。(3) $\sum_jd_j'\ge\sum_i(\sum_j\ell_{ji})d_i$。(4) 直接验证。∎

**命题 2.6（逐对“通道”形式：典范数值、取到性、不对称）** 对 $i,j\in I$ 令

- $\mathcal A^+_{ji}=\{c\in\mathbb S:d_j(\phi x,\phi y)\le c\,d_i(x,y)\ \forall x,y\}$。
- $\mathcal A^-_{ji}=\{c\in\mathbb S:c\,d_i(x,y)\le d_j(\phi x,\phi y)\ \forall x,y\}$。
- $\mathcal C_{ji}=\{t\in\mathbb S:d_i(x,y)\le t\Rightarrow d_j(\phi x,\phi y)=0\ \forall x,y\}$。

它们恰是联合定义中只含单个“活跃”列的行。定义典范数值

$$\lambda^+_{ji}=\inf\mathcal A^+_{ji}\ (\inf\emptyset:=\infty),\qquad \lambda^-_{ji}=\sup\mathcal A^-_{ji},\qquad \theta_{ji}=\inf\{d_i(x,y):d_j(\phi x,\phi y)>0\}\ (\inf\emptyset=\infty).$$

则：

1. **下**：$\mathcal A^-_{ji}=[0,\lambda^-_{ji}]$，上确界总可取到。若存在点对满足 $d_i=\infty>d_j'$，则 $\lambda^-_{ji}=0$。否则 $\lambda^-_{ji}=\inf\{d_j'/d_i:0<d_i<\infty\}$（$d_j'=\infty$ 时比值记 $\infty$，$\inf\emptyset=\infty$）。
2. **上**：若通道 $i\to j$ 零相容（$d_i=0\Rightarrow d_j'=0$），则 $\lambda^+_{ji}=\sup\{d_j'/d_i:0<d_i<\infty\}$（$\sup\emptyset=0$），且 $\mathcal A^+_{ji}=[\lambda^+_{ji},\infty]$。唯一例外：$\lambda^+_{ji}=0$ 且存在 $d_i=\infty$、$d_j'>0$ 的点对，此时 $\mathcal A^+_{ji}=(0,\infty]$，下确界取不到。通道不零相容时 $\mathcal A^+_{ji}=\emptyset$，$\lambda^+_{ji}=\infty$ 仅是占位。
3. **阈值**：$[0,\theta_{ji})\subseteq\mathcal C_{ji}\subseteq[0,\theta_{ji}]$。$\theta_{ji}\in\mathcal C_{ji}$ 当且仅当没有满足 $d_j'>0$ 的点对使 $d_i(x,y)=\theta_{ji}$。
4. **通道⇒联合**：若 $c_i\in\mathcal A^+_{ji}$（或 $c_i\in\mathcal A^-_{ji}$）对一切 $i$ 成立，则对任意权 $w_i\ge0$、$\sum_iw_i=1$，行 $(w_ic_i)_i$ 属于联合型第 $j$ 行容许集。逆命题不成立（例 3.1）。
5. **复合**：$\mathcal A^\pm_{jk}(\psi)\cdot\mathcal A^\pm_{ki}(\phi)\subseteq\mathcal A^\pm_{ji}(\psi\circ\phi)$。因此 $\lambda^-_{ji}(\psi\phi)\ge\max_k\lambda^-_{jk}(\psi)\lambda^-_{ki}(\phi)$ 总成立。上式在两个最优值都取到时给出 $\lambda^+_{ji}(\psi\phi)\le\min_k\lambda^+_{jk}(\psi)\lambda^+_{ki}(\phi)$。**一般的数值乘积律在 $0\cdot\infty$ 处失效**（例 3.6），所以本文的复合律都陈述在可容许矩阵（证书）上。

*证*

- (1) $\mathcal A^-_{ji}$ 是下集。若 $c_\alpha\uparrow c^*$ 且各 $c_\alpha$ 容许：对 $d_i<\infty$ 的点对，乘法对上确界连续；对 $d_i=\infty$ 的点对，$c^*>0$ 时某个 $c_\alpha>0$，故 $d_j'=\infty$，而 $c^*\cdot\infty=\infty$ 也成立。所以 $c^*$ 容许，取到上确界。公式由逐类点对的约束得到：$d_i=\infty$ 的点对迫使 $c=0$ 或 $d_j'=\infty$；$0<d_i<\infty$ 的点对给出 $c\le d_j'/d_i$。
- (2) 约束按 $d_i$ 的取值分三类：$d_i=0$ 的点对只要求零相容；$0<d_i<\infty$ 的点对给出 $c\ge d_j'/d_i$；$d_i=\infty$ 的点对要求 $c>0$ 或 $d_j'=0$。当 $\lambda^+>0$ 时下确界取到（有限乘法连续，且 $c>0$）。
- (3) 可见点对（$d_j'>0$）的 $d_i$ 均 $\ge\theta_{ji}$，故 $t<\theta_{ji}$ 时前提 $d_i\le t$ 不会碰到可见点对。$t>\theta_{ji}$ 时必有可见点对满足 $d_i<t$。边界情形同理。
- (4) $d_j'=\sum_iw_id_j'\le\sum_iw_ic_id_i$。下界用 $\sum_iw_ic_id_i\le\max_ic_id_i\le d_j'$。
- (5) 逐步用单调性和乘法结合律。∎

---

## 3. 例子与反例（说明各条款的必要性）

**例 3.1（为什么必须是联合型矩阵）** 取 $\mathcal X=\mathbb R^2\cup\{\bot\}$，$d_i=|\Delta_i|$（$i=1,2$），$\phi(x)=(x_1+2x_2,\,3x_1)$。

- 联合型：$L=\begin{pmatrix}1&2\\3&0\end{pmatrix}\in\mathcal L^+(\phi)$，且每行的容许集有最小元，所以 $L$ 是最小的上矩阵。
- 逐对型：第 1 行的通道都不零相容（例如 $\Delta_1=0$ 而 $\Delta_2\ne0$ 时 $d_1'>0$），第 2 行的 $2\to2$ 通道也不零相容。只有 $\lambda^+_{21}=3$ 有意义，其余全是占位的 $\infty$。逐对型丢掉了绝大部分信息。
- 单一常数：$d_\vee$ 下的 Lip 常数 $\le3$，看不出 $d_2'$ 不依赖 $d_2$。
- 下矩阵（联合型）：$\ell=\begin{pmatrix}0&0\\3&0\end{pmatrix}$ 是最大的下矩阵。第 1 行必为 $0$，因为 $\Delta_1=-2\Delta_2$ 时输出分量 $1$ 为 $0$。
- 逆向形式（注 4.2）：$D\preceq MD'$，其中 $M=\begin{pmatrix}0&1/3\\1/2&1/6\end{pmatrix}$。

**例 3.2（非分离：$\infty$ 失效）** 取 $\mathcal X=\{a,b,\bot\}$，$d_i(a,b)=0$，$d_i(a,\bot)=d_i(b,\bot)=\infty$。这满足 (i)–(iv)，但族不分离。令 $\phi(a)=a$，$\phi(b)=\bot$，$\phi(\bot)=\bot$。则 $D(a,b)=\mathbf 0$ 而 $D(\phi a,\phi b)=\boldsymbol\infty$。$\phi$ 不零相容，由定理 2.2，$\mathcal L^+(\phi)=\mathcal C(\phi)=\emptyset$，连 $\Omega$ 都不行。而 $\mathcal L^-(\phi)=\{O\}$，与命题 2.3(3) 一致。

**例 3.3（定义域截断，说明 $\infty$ 的统一作用）** 取 $\mathcal X=\mathbb R\cup\{\bot\}$，$d=|x-y|$，$\phi_S(x)=x\ (x\in S=[0,1])$，其余取 $\bot$。族分离，故 $\Omega\in\mathcal L^+(\phi_S)$。但没有有限上矩阵：取 $x=0\in S$，$y=-\varepsilon\notin S$，与命题 2.3(2) 矛盾。同时 $\mathcal L^-(\phi_S)=\{O\}$。把量词限制到 $S$ 后（注 4.1），$1$ 同时是上、下矩阵。

**例 3.4（$\infty$ 元素自然出现，以及无极小元）** 取 $\mathcal X=\mathbb R\cup\{\bot\}$，$d_1=|x-y|$，$d_2(x,y)=\infty\cdot[x\ne y]$（离散通道，$d_2(x,\bot)=\infty$ 满足 (iv)）。$\phi=\mathrm{id}$。

- 下矩阵：最大元是 $\begin{pmatrix}1&0\\\infty&\infty\end{pmatrix}$。离散通道把任何可分辨性放大成无穷可分辨性。
- 上矩阵：第 1 行容许集是 $\{r_1\ge1\}\cup\{r_2>0\}$。$(0,\varepsilon)$ 对任意 $\varepsilon>0$ 可行，$(0,0)$ 不可行，所以**无极小元**。这正是注 0.2 的现象。

**例 3.5（有限正阈值）** 取 $\mathcal X=\{10m,\,10m+\tfrac12:m\in\mathbb Z\}\cup\{\bot\}$，单通道 $d=|x-y|$，$\phi(10m)=\phi(10m+\tfrac12)=10m$（“簇吸附”）。

- $\theta=9.5$，由 $x=10m+\tfrac12$、$y=10(m+1)$ 取到，故 $\mathcal C=[0,9.5)$。
- $\lambda^+=20/19$，取到。
- $\lambda^-=0$，与命题 2.4(b) 一致。
- $\phi\circ\phi=\phi$，由定理 2.1(4) 得 $\Theta''=\Theta$，也一致。

**例 3.6（数值乘积律失效）** 取 $\mathcal X=\{a,b,u,v,\bot\}$，单通道，$d(a,b)=1$，其余不同点对距离 $\infty$。令 $\phi:a\mapsto u,\ b\mapsto v$，$\psi:a,b\mapsto a$，其余点不动。则 $\mathcal A^+(\phi)=\{\infty\}$，$\mathcal A^+(\psi)=(0,\infty]$，$\mathcal A^+(\psi\phi)=\{\infty\}$。于是 $\lambda^+(\psi\phi)=\infty>0=\lambda^+(\psi)\lambda^+(\phi)$。但在容许常数层面，$c'\cdot\infty=\infty$ 对 $c'>0$ 成立，没有矛盾。

---

## 4. 注记与小结

**注 4.1（区域化）** 对子集 $S\subseteq\mathcal X$，把定义 1.1 中的量词改为 $x,y\in S$，得 $\mathcal L^\pm(\phi;S)$ 与 $\mathcal C(\phi;S)$。

- 若 $\phi(S)\subseteq S'$，则复合律照旧：$L\in\mathcal L^+(\phi;S)$，$L'\in\mathcal L^+(\psi;S')\Rightarrow L'L\in\mathcal L^+(\psi\phi;S)$。
- “$\phi$ 在区域 $S$ 上第 $j$ 分量不可区分”等价于 $0$ 是 $\mathcal L^+_j(\phi;S)$ 的第 $j$ 行容许元。这样 ReLU 型“死区”也在框架内。
- $\mathcal L^+(\phi)=\{L\in\mathcal L^+(\phi;\mathrm{dom}\,\phi):\forall x\in\mathrm{dom}\,\phi,\,y\notin\mathrm{dom}\,\phi:\ LD(x,y)=\boldsymbol\infty\}$。右边第二个条件是 $\bot$ 带来的边界条件。
- 在连通空间（如 $\mathbb R^n$ 配欧氏度量）中，一致的有限正阈值只能是平凡的。有意义的有限阈值出现在带间隙的空间（例 3.5），或由无穷距离分块的空间。

**注 4.2（变体）**

- **求和型 vs 取最大型。** 把 $\sum_i$ 换成 $\max_i$，即半环 $(\mathbb S,\max,\cdot)$，全部结论平行成立。两者只差因子 $n$：$\mathcal L^+_{\max}\subseteq\mathcal L^+_\Sigma$ 且 $n\mathcal L^+_\Sigma\subseteq\mathcal L^+_{\max}$。下界方向相反：$\mathcal L^-_\Sigma\subseteq\mathcal L^-_{\max}$ 且 $\tfrac1n\mathcal L^-_{\max}\subseteq\mathcal L^-_\Sigma$。
- **下界的逆向形式。** 矩阵情形下，下界还有另一种读法：$D(x,y)\preceq M\,D(\phi x,\phi y)$，$M$ 的行指标是输入分量。它的复合律是 $M_{\psi\phi}=M_\phi M_\psi$。标量情形下 $M=1/\ell$。矩阵情形下两种形式不等价：例 3.1 中直接下矩阵的第 1 行为 $0$，而逆向矩阵 $M$ 存在。
- **有限性 $|I|<\infty$** 用于有限和、矩阵乘法与上述因子 $n$。

**小结**

1. **矩阵化。** 定义 1.1(U)。复合对应矩阵乘法（定理 2.1），并可回到单一常数（命题 2.5）。
2. **下限。** 定义 1.1(D)。它总存在（$O$），但与 $\bot$、坍缩互斥（命题 2.3(3)、2.4(b)）。
3. **$\infty$ 扩展。** 矩阵元取值于 $[0,\infty]$。扩展上矩阵存在当且仅当零相容。族分离时恒存在；不分离时，$\infty$ 无法弥补零距离被拉成正距离（定理 2.2、例 3.2）。数值最优值有取不到的情形（命题 2.6、注 0.2），所以复合律陈述在容许矩阵上。
4. **不可区分矩阵。** 定义 1.1(C)。它与 Lip 矩阵同属“对输出分量的上包络”，一个是线性的，一个是阶梯的（命题 1.2）。Lip 矩阵的零元给出 $\infty$ 阈值（命题 2.4(a)）。它与 Lip 矩阵的混合复合律见定理 2.1(4)(5)。

我用随机有限空间对定理 2.1、2.2、命题 2.3、2.4 中的 $\Theta^L$ 与 $\ell$ 部分以及命题 2.6 的公式做了数值核对，没发现反例。命题 1.2、2.5 和各例子为手工验证。