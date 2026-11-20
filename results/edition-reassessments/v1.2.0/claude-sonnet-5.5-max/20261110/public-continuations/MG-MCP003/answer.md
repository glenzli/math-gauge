# 算子的矩阵型 Lipschitz 上/下界、∞ 扩展与坍缩阈值矩阵（修订稿）

本稿自包含，没有额外交付文件。相对上一版，有四处订正（见 §5）：例 3.4 的“无极小元”误述、推论 2.1′ 的误述、命题 2.3(3) 的单射条件、原注 4.1 的含糊断言。

## 总览：想法与数学对象的对应

| 原想法 | 数学化 |
|---|---|
| 单一 Lip 常数不够，用矩阵表示分量间关系 | **上 Lipschitz 矩阵** $L$：$D(\phi x,\phi y)\preceq L\,D(x,y)$（定义 1.1(U)） |
| 除上限外还要下限 | **下 Lipschitz 矩阵** $\ell$：$\ell D(x,y)\preceq D(\phi x,\phi y)$（(D)，直接形式）。**反向下界矩阵** $M$：$D(x,y)\preceq M\,D(\phi x,\phi y)$（(R)，余 Lipschitz）。$\lvert I\rvert=1$ 时 $M=1/\ell$，矩阵情形二者不等价（例 3.1） |
| 不是所有函数都有 Lip，支持 ∞ | 矩阵元取值于 $[0,\infty]$，配合 $0\cdot\infty=0$。存在性的精确条件见定理 2.2，与单一常数的关系见命题 2.5 |
| 输入落入某范畴则输出不可区分，要与 Lip 对等的矩阵 | **坍缩阈值矩阵** $\Theta$：$D(x,y)\preceq\Theta_{j\cdot}\Rightarrow d_j(\phi x,\phi y)=0$（(C)）。它与 Lip 矩阵是同一“响应函数”的两种读数：线性包络与阶梯包络（命题 1.2） |

全文遵守的解读选择：

- **(I1)** “矩阵”取联合型（求和型）增益矩阵，即向量值度量意义下的 Perov 型。逐对型（命题 2.6）和取最大型（注 4.2）作为特例或变体并列处理。例 3.1、例 3.7 说明联合型不可省。
- **(I2)** 全局量词取遍整个 $\mathcal X$（含 $\bot$），未定义性由 $\infty$ 算术自动处理。限制到子集见注 4.1。
- **(I3)** “不可区分”指零距离（$d_j=0$ 或 $D=\mathbf 0$），不是“相等”，因为本卷不预设族分离。
- **(I4)** “输入落入一定范畴”指输入距离向量落入盒子 $\prod_i[0,\Theta_{ji}]$。
- **(I5)** “下限”有两种矩阵读法，(D) 与 (R) 都给出。

---

## 0. 记号、约定与预备

**0.1 算术。** 记 $\mathbb S:=[0,\infty]$，运算按 CH1 约定（$0\cdot\infty=0$，$a\cdot\infty=\infty\ (a>0)$，$a+\infty=\infty$）。另约定 $\infty/s=\infty\ (0<s<\infty)$，仅用于 $\Theta/2$、$\Theta_{jk}/s_k$ 这类记号。

**引理 0.1** $(\mathbb S,+,\cdot,0,1)$ 是交换半环，且 $+$、$\cdot$ 关于 $\le$ 单调（$a\le a',\,b\le b'\Rightarrow ab\le a'b'$）。

*证* 乘法结合律：某因子为 $0$ 时两边都是 $0$，否则诸因子在 $(0,\infty]$ 内，乘法是通常乘法的延拓。分配律 $a(b+c)=ab+ac$：$a=0$ 平凡；$a>0$ 时 $b\mapsto ab$ 在 $[0,\infty)$ 上是伸缩且 $\infty\mapsto\infty$，故对 $+$ 可加。单调性：$ab>0$ 时 $a,b>0$，从而 $a',b'>0$ 且 $a'b'\ge ab$；$ab=0$ 平凡。∎

**注 0.2（唯一的“病灶”）** 乘法保定向上确界，但不保下确界：$\inf_k\frac1k\cdot\infty=\infty\ne0=0\cdot\infty$。后文所有“最优常数取不到”“无极小元”的现象都只来源于此（命题 2.6、例 3.4、例 3.6）。

**0.2 矩阵。** $I$ 有限非空，$n=|I|$，$\mathbb M:=\mathbb S^{I\times I}$。

- 行指标 $j$ 是输出分量，列指标 $i$ 是输入分量（(R) 型例外，见定义 1.1）。
- $(Av)_j=\sum_iA_{ji}v_i$，$(AB)_{ji}=\sum_kA_{jk}B_{ki}$。
- $A\le B$ 是逐元序，$\preceq$ 是 $\mathbb S^I$ 的逐分量序。
- $E,O,\Omega$ 分别是单位阵、零阵、全 $\infty$ 阵；$\mathbf 0,\boldsymbol\infty\in\mathbb S^I$ 是全 $0$、全 $\infty$ 向量。

**引理 0.3** 设 $A,B,C\in\mathbb M$，$u,v\in\mathbb S^I$，$\lambda\in\mathbb S$。

- (a) $A(u+v)=Au+Av$，$A(\lambda u)=\lambda Au$，$(AB)u=A(Bu)$，$(AB)C=A(BC)$，$Eu=u$。
- (b) 若 $A\le B$ 且 $u\preceq v$，则 $Au\preceq Bv$。
- (c) $(Au)_j=0\iff\forall i:\ A_{ji}u_i=0$。$(Au)_j=\infty\iff\exists i:\ A_{ji}u_i=\infty$，即（$A_{ji}=\infty,u_i>0$）或（$A_{ji}>0,u_i=\infty$）。特别地，$(A\boldsymbol\infty)_j=\infty$ 当且仅当第 $j$ 行非零，否则为 $0$。

*证* (a)(b) 由引理 0.1 和 $I$ 有限得到。(c) 非负项的有限和为 $0$（或 $\infty$）当且仅当各项为 $0$（或某项为 $\infty$）。∎

**0.3 距离向量与不可区分。** 记 $D(x,y):=(d_i(x,y))_{i\in I}$。由 (i)–(iv)：$D(x,x)=\mathbf 0$，$D$ 对称，$D(x,z)\preceq D(x,y)+D(y,z)$，$x\ne\bot\Rightarrow D(x,\bot)=\boldsymbol\infty$。

由三角不等式，下列三个关系都是等价关系：

- $x\sim_jy:\iff d_j(x,y)=0$。
- $x\sim y:\iff D(x,y)=\mathbf 0$。
- $x\approx y:\iff D(x,y)\in[0,\infty)^I$。

因 $I\ne\emptyset$，$\{\bot\}$ 是 $\sim$ 与 $\approx$ 的单点类。不预设族分离，所以 $\sim$ 一般比 “$=$” 粗。

**定义 0.4** 称 $\phi$ **零相容**，若 $D(x,y)=\mathbf 0\Rightarrow D(\phi x,\phi y)=\mathbf 0$。称 $\phi$ **零反射**，若 $D(\phi x,\phi y)=\mathbf 0\Rightarrow D(x,y)=\mathbf 0$。

- 零相容等价于 $\phi$ 在 $\mathcal X/{\sim}$ 上良定义。
- 族分离时，零相容恒成立，零反射等价于单射。

**注 0.5（商空间）** 设 $\phi$ 零相容。$\bar d_i([x],[y]):=d_i(x,y)$ 良定义：若 $x\sim x'$，$y\sim y'$，则 $d_i(x,y)\le d_i(x',y')$，反向同理。$(\mathcal X/{\sim},\{\bar d_i\},\{\bot\})$ 仍满足 (i)–(iv) 且族分离。$\phi$ 诱导 $\bar\phi$，下文四类矩阵对 $\phi$ 与 $\bar\phi$ 相同。所以对零相容算子可不妨设族分离；对非零相容算子，(U) 与 (C) 型矩阵根本不存在（定理 2.2）。

---

## 1. 定义

固定 $\phi\in\mathcal X_{\rm op}$。

**定义 1.1**

- **(U) 上 Lipschitz 矩阵。** $L\in\mathbb M$ 满足 $D(\phi x,\phi y)\preceq L\,D(x,y)$ 对一切 $x,y\in\mathcal X$ 成立，即 $d_j(\phi x,\phi y)\le\sum_iL_{ji}d_i(x,y)$。全体记 $\mathcal L^+(\phi)$。元素全有限者称**有限型**，允许 $\infty$ 者称**扩展型**。
- **(D) 下 Lipschitz 矩阵。** $\ell\in\mathbb M$ 满足 $\ell\,D(x,y)\preceq D(\phi x,\phi y)$ 对一切 $x,y$ 成立。全体记 $\mathcal L^-(\phi)$。$(\ell,L)\in\mathcal L^-(\phi)\times\mathcal L^+(\phi)$ 称**双 Lipschitz 对**。
- **(R) 反向下界（余 Lipschitz）矩阵。** $M\in\mathbb M$ 满足 $D(x,y)\preceq M\,D(\phi x,\phi y)$ 对一切 $x,y$ 成立。这里 $M_{ij}$ 的行指标 $i$ 是输入分量，列指标 $j$ 是输出分量。全体记 $\mathcal L^{\leftarrow}(\phi)$。
- **(C) 坍缩（不可区分）阈值矩阵。** $\Theta\in\mathbb M$ 满足：对每个 $j$ 和一切 $x,y$，若 $d_i(x,y)\le\Theta_{ji}$ 对所有 $i$ 成立，则 $d_j(\phi x,\phi y)=0$。全体记 $\mathcal C(\phi)$。

**读法**

- $L_{ji}$ 是输入分量 $i$ 到输出分量 $j$ 的增益上限。对角元是同分量增益，非对角元是分量间“串扰”。
  - $L_{ji}=0$：$i$ 对 $j$ 无传递，由 $0\cdot\infty=0$，即使 $d_i=\infty$ 也不起作用。
  - $L_{ji}=\infty$：无有限控制，但只要 $d_i>0$ 就不再约束。
- $\ell_{ji}$ 是增益下限。$\ell_{ji}=\infty$ 表示 $d_i>0\Rightarrow d_j(\phi x,\phi y)=\infty$。
- (R) 是反向关系 $\{(D(\phi x,\phi y),D(x,y))\}$ 的“上 Lipschitz 矩阵”：输入距离由输出各分量联合控制。$|I|=1$ 且 $0<\ell<\infty$ 时，$\ell\in\mathcal L^-\iff1/\ell\in\mathcal L^\leftarrow$。
- $\Theta_{ji}$：所有输入分量同时落入盒子 $\prod_i[0,\Theta_{ji}]$ 时，输出第 $j$ 分量必不可区分。$\Theta_{ji}=\infty$ 表示该分量不设限，$\Theta_{ji}=0$ 表示只要求该分量不可区分。

**命题 1.2（响应函数刻画：Lip 与坍缩“对等”的精确含义）** 对 $v,w\in\mathbb S^I$ 定义

$$\rho_j(v)=\sup\{d_j(\phi x,\phi y):D(x,y)\preceq v\},\quad \varrho_j(v)=\inf\{d_j(\phi x,\phi y):D(x,y)\succeq v\},\quad \sigma_i(w)=\sup\{d_i(x,y):D(\phi x,\phi y)\preceq w\}$$

（$\inf\emptyset=\infty$）。记 $V_j:=\{D(x,y):d_j(\phi x,\phi y)>0\}$（第 $j$ 分量的“可见剖面”），$\uparrow V_j$ 为其按 $\preceq$ 的上闭包。则：

1. $L\in\mathcal L^+(\phi)\iff\rho_j(v)\le(Lv)_j$ 对一切 $j,v$ 成立。
2. $\ell\in\mathcal L^-(\phi)\iff(\ell v)_j\le\varrho_j(v)$ 对一切 $j,v$ 成立。
3. $M\in\mathcal L^\leftarrow(\phi)\iff\sigma_i(w)\le(Mw)_i$ 对一切 $i,w$ 成立。
4. $\Theta\in\mathcal C(\phi)\iff\rho_j(\Theta_{j\cdot})=0\ \forall j\iff\Theta_{j\cdot}\notin{\uparrow}V_j\ \forall j$。

所以 $L$ 是 $\rho$ 的线性上包络，$\ell$ 是 $\varrho$ 的线性下包络，$\Theta$ 描述 $\rho$ 的零集，即阶梯上包络 $d_j(\phi x,\phi y)\le\chi_{\Theta_{j\cdot}}(D(x,y))$，其中 $\chi_t(v)=0\ (v\preceq t)$，$=\infty$（否则）。

*证*

- (1) “$\Rightarrow$”：若 $D(x,y)\preceq v$，则 $d_j(\phi x,\phi y)\le(LD(x,y))_j\le(Lv)_j$（引理 0.3(b)），取上确界。“$\Leftarrow$”：取 $v=D(x,y)$。
- (2)(3) 同理，(2) 取下确界。
- (4) 前一等价是定义。$\rho_j(\Theta_{j\cdot})>0$ 当且仅当存在 $(x,y)$ 使 $D(x,y)\preceq\Theta_{j\cdot}$ 且 $d_j(\phi x,\phi y)>0$，即 $\Theta_{j\cdot}\in{\uparrow}V_j$。∎

**推论 1.3**

- (i) $\mathcal L^+(\phi)$、$\mathcal L^\leftarrow(\phi)$ 向上封闭，$\mathcal L^-(\phi)$、$\mathcal C(\phi)$ 向下封闭。
- (ii) 四者都**按行解耦**：矩阵属于其中之一，当且仅当它的每一行属于相应的行容许集，各行可独立选取。
- (iii) 行容许集是凸的，但一般**没有最小元**，所以“Lipschitz 矩阵”是容许性质而非 $\phi$ 的唯一取值。
  - 凸性：若 $r,r'$ 是 (U) 的第 $j$ 行容许元，$\lambda\in[0,1]$，则 $\sum_i(\lambda r_i+(1-\lambda)r_i')d_i=\lambda\sum r_id_i+(1-\lambda)\sum r_i'd_i\ge d_j(\phi x,\phi y)$（引理 0.1）。
  - 例：$\mathcal X=\mathbb R\cup\{\bot\}$，$d_1=|x-y|$，$d_2=2|x-y|$（含 $\bot$ 的对取 $\infty$），$\phi=\mathrm{id}$。第 1 行容许集是 $\{r:r_1+2r_2\ge1\}$，其中 $(1,0)$ 与 $(0,\tfrac12)$ 是不可比的极小元。
- (iv) $|I|=1$ 时，四者化为经典的 $d(\phi x,\phi y)\le L\,d(x,y)$、$\ell\,d(x,y)\le d(\phi x,\phi y)$、$d(x,y)\le M\,d(\phi x,\phi y)$ 与 “$d(x,y)\le\Theta\Rightarrow\phi x\sim\phi y$”。

---

## 2. 基本性质

### 2.1 复合

**定理 2.1（复合与恒等）** 设 $\phi,\psi\in\mathcal X_{\rm op}$。则 $\psi\circ\phi\in\mathcal X_{\rm op}$，且 $\mathrm{dom}(\psi\circ\phi)=\phi^{-1}(\mathrm{dom}\,\psi)$。

1. $E\in\mathcal L^+(\phi)\cap\mathcal L^-(\phi)\iff D(\phi x,\phi y)=D(x,y)$ 恒成立（逐分量等距）。
2. 若 $L\in\mathcal L^+(\phi)$，$L'\in\mathcal L^+(\psi)$，则 $L'L\in\mathcal L^+(\psi\circ\phi)$。特别地，$L^m\in\mathcal L^+(\phi^m)$。
3. 若 $\ell\in\mathcal L^-(\phi)$，$\ell'\in\mathcal L^-(\psi)$，则 $\ell'\ell\in\mathcal L^-(\psi\circ\phi)$。
4. 若 $M\in\mathcal L^\leftarrow(\phi)$，$M'\in\mathcal L^\leftarrow(\psi)$，则 $MM'\in\mathcal L^\leftarrow(\psi\circ\phi)$（次序反转）。
5. 若 $\Theta\in\mathcal C(\phi)$，$L'\in\mathcal L^+(\psi)$，令 $\Theta''_{ji}:=\min\{\Theta_{ki}:L'_{jk}>0\}$（$\min\emptyset=\infty$），则 $\Theta''\in\mathcal C(\psi\circ\phi)$。
6. 若 $L\in\mathcal L^+(\phi)$，$\Theta'\in\mathcal C(\psi)$，且 $\tau\in\mathbb S^I$ 满足 $L\tau\preceq\Theta'_{j\cdot}$，则 $D(x,y)\preceq\tau\Rightarrow d_j(\psi\phi x,\psi\phi y)=0$。特别地，当 $L$ 有限时，令 $s_k=\sum_iL_{ki}$，$r_j=\min\{\Theta'_{jk}/s_k:s_k>0\}$（$\min\emptyset=\infty$），则 $\max_id_i(x,y)\le r_j\Rightarrow d_j(\psi\phi x,\psi\phi y)=0$。

*证*

- $\psi\phi(\bot)=\psi(\bot)=\bot$。若 $\phi x=\bot$，则 $\psi\phi x=\bot$。若 $\phi x\ne\bot$，则 $\psi\phi x\ne\bot\iff\phi x\in\mathrm{dom}\,\psi$。故定义域公式成立。
- (1) 直接由定义。
- (2) $D(\psi\phi x,\psi\phi y)\preceq L'D(\phi x,\phi y)\preceq L'(LD(x,y))=(L'L)D(x,y)$。
- (3) $(\ell'\ell)D=\ell'(\ell D)\preceq\ell'D(\phi x,\phi y)\preceq D(\psi\phi x,\psi\phi y)$。
- (4) $D(x,y)\preceq MD(\phi x,\phi y)\preceq M(M'D(\psi\phi x,\psi\phi y))=(MM')D(\psi\phi x,\psi\phi y)$。
- (5) 设 $D(x,y)\preceq\Theta''_{j\cdot}$。对满足 $L'_{jk}>0$ 的 $k$，有 $D(x,y)\preceq\Theta_{k\cdot}$，故 $d_k(\phi x,\phi y)=0$。于是 $d_j(\psi\phi x,\psi\phi y)\le\sum_kL'_{jk}d_k(\phi x,\phi y)=0$。其中 $L'_{jk}=0$ 的项即使 $d_k(\phi x,\phi y)=\infty$ 也为 $0$，这里用到 $0\cdot\infty=0$。
- (6) 若 $D(x,y)\preceq\tau$，则 $D(\phi x,\phi y)\preceq LD(x,y)\preceq L\tau\preceq\Theta'_{j\cdot}$，由 $\Theta'$ 的定义得结论。取 $\tau=(r_j,\dots,r_j)$：若 $s_k=0$，则 $(L\tau)_k=0$。若 $s_k>0$，则 $(L\tau)_k=s_kr_j\le\Theta'_{jk}$。若 $r_j=\infty$，则所有 $s_k=0$，$L=O$。∎

**推论 2.1′（子幺半群）** 记

- $\mathsf Z^+=\{\phi:\mathcal L^+(\phi)\ne\emptyset\}$，
- $\mathsf Z^+_{\rm fin}=\{\phi:\mathcal L^+(\phi)\text{ 含有限型矩阵}\}$，
- $\mathsf Z^\leftarrow=\{\phi:\mathcal L^\leftarrow(\phi)\ne\emptyset\}$。

三者都含 $\mathrm{id}$ 且对 $\circ$ 封闭，所以是 $(\mathcal X_{\rm op},\circ)$ 的子幺半群，证书按矩阵乘法复合（(U)：$L'L$；(R)：$MM'$）。

**注意**：“具有非零下矩阵”的算子类对 $\circ$ **不封闭**。反例：$\mathcal X=\mathbb R^2\cup\{\bot\}$，$d_i=|\Delta_i|$，$\phi(x)=(0,x_1)$，$\psi(x)=(x_1,0)$。则 $\begin{pmatrix}0&0\\1&0\end{pmatrix}\in\mathcal L^-(\phi)$，$\begin{pmatrix}1&0\\0&0\end{pmatrix}\in\mathcal L^-(\psi)$。但 $\psi\phi$ 把 $\mathbb R^2$ 压成一点，故 $\mathcal L^-(\psi\phi)=\{O\}$，与 $\ell'\ell=O$ 相符。（上一版把“具有下矩阵”也列为子幺半群是错的：因 $O$ 恒为下矩阵，该类是全体算子，该说法空洞。）

### 2.2 存在性：∞ 能做到什么、做不到什么

**定理 2.2**

- **(A)** 对 $\phi\in\mathcal X_{\rm op}$，下列等价：
  - (a) $\mathcal L^+(\phi)\ne\emptyset$；
  - (b) $\Omega\in\mathcal L^+(\phi)$；
  - (c) $\phi$ 零相容；
  - (d) $O\in\mathcal C(\phi)$；
  - (e) $\mathcal C(\phi)\ne\emptyset$。
- **(B)** 下列等价：
  - (f) $\mathcal L^\leftarrow(\phi)\ne\emptyset$；
  - (g) $\Omega\in\mathcal L^\leftarrow(\phi)$；
  - (h) $\phi$ 零反射。
- **(C)** $O\in\mathcal L^-(\phi)$ 恒成立。

*证*

- (A)
  - (a)⇒(c)：若 $D(x,y)=\mathbf 0$，则 $D(\phi x,\phi y)\preceq L\mathbf 0=\mathbf 0$。
  - (c)⇒(b)：若 $D(x,y)=\mathbf 0$，则 $D(\phi x,\phi y)=\mathbf 0\preceq\Omega\mathbf 0$。若 $D(x,y)\ne\mathbf 0$，则某个 $d_i>0$，$(\Omega D)_j\ge\infty\cdot d_i=\infty$。
  - (b)⇒(a) 平凡。
  - (c)⇔(d)：$O\in\mathcal C(\phi)$ 恰说 $D(x,y)=\mathbf 0\Rightarrow D(\phi x,\phi y)=\mathbf 0$。
  - (d)⇒(e) 平凡。
  - (e)⇒(c)：若 $D(x,y)=\mathbf 0$，则 $D\preceq\Theta_{j\cdot}$ 对每个 $j$ 成立，故 $D(\phi x,\phi y)=\mathbf 0$。
- (B)
  - (f)⇒(h)：$D(\phi x,\phi y)=\mathbf 0\Rightarrow D(x,y)\preceq M\mathbf 0=\mathbf 0$。
  - (h)⇒(g)：若 $D(\phi x,\phi y)=\mathbf 0$，则 $D(x,y)=\mathbf 0$。若 $D(\phi x,\phi y)\ne\mathbf 0$，则某个 $d_j'>0$，$(\Omega D')_i=\infty$ 对每个 $i$ 成立。
  - (g)⇒(f) 平凡。
- (C) 显然。∎

**推论** 族分离时，每个算子都有扩展 Lipschitz 矩阵 $\Omega$，这正是引入 $\infty$ 的“统一表达”。反向矩阵存在当且仅当 $\phi$ 单射。**不分离时 $\infty$ 兜不住底**（例 3.2）：$0\cdot\infty=0$ 使“零距离变正距离”无法用乘积型不等式表达。对偶地说：扩展上矩阵存在 $\iff$ 保零，扩展反向矩阵存在 $\iff$ 反射零，而直接下矩阵没有此障碍。

### 2.3 ⊥ 与有效定义域

**命题 2.3** 设 $\mathrm{dom}\,\phi\ne\emptyset$（这时 $\mathcal X\setminus\{\bot\}\neq\emptyset$ 保证了非平凡算子的存在）。

1. 若 $x\in\mathrm{dom}\,\phi$，$y\notin\mathrm{dom}\,\phi$，$L\in\mathcal L^+(\phi)$，则对每个 $j$ 存在 $i$ 使 $L_{ji}d_i(x,y)=\infty$。特别地，$L$ 的每一行非零。
2. 若 $L\in\mathcal L^+(\phi)$ 是有限型，$x\in\mathrm{dom}\,\phi$，$x\approx y$，则 $y\in\mathrm{dom}\,\phi$。即有限型算子的 $\mathrm{dom}$ 是若干 $\approx$-类之并，“有定义/无定义”不会在有限距离内跳变。
3. 若 $\ell\in\mathcal L^-(\phi)$ 有非零行，则 $\phi^{-1}(\bot)=\{\bot\}$。反之，只要某个 $x\ne\bot$ 有 $\phi x=\bot$，就有 $\mathcal L^-(\phi)=\{O\}$。若 $\ell_{ji}>0$，则 $d_j(\phi x,\phi y)=0\Rightarrow d_i(x,y)=0$，且 $d_i(x,y)=\infty\Rightarrow d_j(\phi x,\phi y)=\infty$。若 $\ell$ 每一列非零，则 $\phi$ 零反射；此时若 $\phi$ 又零相容，则 $\phi$ 在 $\mathcal X/{\sim}$ 上良定义且单射。
4. 若 $\Theta\in\mathcal C(\phi)$，$x\in\mathrm{dom}\,\phi$，$y\notin\mathrm{dom}\,\phi$，则对每个 $j$ 存在 $i$ 使 $d_i(x,y)>\Theta_{ji}$。特别地，$\Theta$ 的每一行含有限元。
5. 若 $\mathcal L^\leftarrow(\phi)\ne\emptyset$，则 $\phi^{-1}(\bot)=\{\bot\}$，即 $\mathrm{dom}\,\phi=\mathcal X\setminus\{\bot\}$。

*证* 设 $x\in\mathrm{dom}\,\phi$，$y\notin\mathrm{dom}\,\phi$，则 $x\ne\bot$，$\phi y=\bot$，$\phi x\ne\bot$，故 $D(\phi x,\phi y)=\boldsymbol\infty$。

- (1) 由定义和引理 0.3(c)。取 $y=\bot$（$\bot\notin\mathrm{dom}\,\phi$），$D(x,\bot)=\boldsymbol\infty$，得各行非零。
- (2) 若 $y\notin\mathrm{dom}\,\phi$，则 $\infty\le\sum_iL_{ji}d_i(x,y)$，右边是有限和，矛盾。
- (3) 若 $x\ne\bot$ 且 $\phi x=\bot$，对 $(x,\bot)$ 有 $\ell\boldsymbol\infty\preceq D(\bot,\bot)=\mathbf 0$，故 $\ell=O$。其余由 $0=d_j'\ge\ell_{ji}d_i$ 及 $\ell_{ji}\cdot\infty=\infty$ 得到。列非零时，对每个 $i$ 取 $j$ 使 $\ell_{ji}>0$，则 $D(\phi x,\phi y)=\mathbf 0\Rightarrow d_i(x,y)=0$。
- (4) $d_j(\phi x,\phi y)=\infty\ne0$，故 (C) 的前提不成立。
- (5) 若 $x\ne\bot$，$\phi x=\bot$，则 $D(\phi x,\phi\bot)=\mathbf 0$ 而 $D(x,\bot)=\boldsymbol\infty$，$\phi$ 不零反射，由定理 2.2(B) 得证。∎

### 2.4 四类矩阵之间的关系

**命题 2.4**

- (a)（零元↔∞阈值）若 $L\in\mathcal L^+(\phi)$，令 $\Theta^L_{ji}=0\ (L_{ji}>0)$，$=\infty\ (L_{ji}=0)$，则 $\Theta^L\in\mathcal C(\phi)$。*证*：若 $d_i\le\Theta^L_{ji}$ 对所有 $i$ 成立，则 $L_{ji}>0$ 的项有 $d_i=0$，$L_{ji}=0$ 的项由 $0\cdot\infty=0$ 也为 $0$，故 $d_j'\le\sum_iL_{ji}d_i=0$。所以 Lip 矩阵只给出 $\{0,\infty\}$ 型阈值，有限正阈值是新信息（例 3.5）。
- (b)（下界与坍缩互斥）若 $\ell\in\mathcal L^-(\phi)$，$\Theta\in\mathcal C(\phi)$，且 $D(x,y)\preceq\Theta_{j\cdot}$，则 $\ell_{ji}d_i(x,y)=0$ 对一切 $i$ 成立。*证*：$0=d_j'\ge\sum_i\ell_{ji}d_i$。
- (c)（一致性）若 $\ell\in\mathcal L^-(\phi)$，$L\in\mathcal L^+(\phi)$，则 $\ell D(x,y)\preceq LD(x,y)$ 对一切 $x,y$ 成立。
- (d)（全分量坍缩）若 $\Theta\in\mathcal C(\phi)$，$\tau_i:=\min_j\Theta_{ji}$，则 $D(x,y)\preceq\tau\Rightarrow D(\phi x,\phi y)=\mathbf 0$。
- (e)（球形读法）记 $B(c;r)=\{x:d_i(x,c)\le r_i\ \forall i\}$。若 $\Theta\in\mathcal C(\phi)$，则 $x,y\in B(c;\Theta_{j\cdot}/2)\Rightarrow d_j(\phi x,\phi y)=0$。反之，若 $\phi$ 在所有 $B(c;r)$ 上第 $j$ 分量不可区分，则 $r$ 是第 $j$ 个坍缩行。*证*：前者由 $D(x,y)\preceq D(x,c)+D(c,y)\preceq\Theta_{j\cdot}$。后者取 $c=x$，此时 $x,y\in B(x;r)$。故“成对”与“成球”两种读法至多差因子 $2$。
- (f)（左逆给出反向矩阵）若 $\ell\in\mathcal L^-(\phi)$ 且 $N\in\mathbb M$ 满足 $(N\ell)_{ii}\ge1$ 对一切 $i$ 成立，则 $N\in\mathcal L^\leftarrow(\phi)$。*证*：$((N\ell)D)_i\ge(N\ell)_{ii}d_i\ge d_i$，故 $D\preceq(N\ell)D=N(\ell D)\preceq ND(\phi x,\phi y)$。
- (g)（反向下界与坍缩互斥）若 $M\in\mathcal L^\leftarrow(\phi)$，$\Theta\in\mathcal C(\phi)$，$\tau$ 如 (d)，则 $D(x,y)\preceq\tau\Rightarrow D(x,y)=\mathbf 0$。*证*：由 (d)，$D(\phi x,\phi y)=\mathbf 0$，故 $D(x,y)\preceq M\mathbf 0=\mathbf 0$。

### 2.5 与单一 Lip 常数的关系

**命题 2.5** 记 $d_\vee=\max_id_i$，$d_\Sigma=\sum_id_i$。它们仍是满足 (i)–(iv) 的扩展伪度量。

1. 若 $L\in\mathcal L^+(\phi)$，则 $d_\vee(\phi x,\phi y)\le\big(\max_j\sum_iL_{ji}\big)d_\vee(x,y)$，且 $d_\Sigma(\phi x,\phi y)\le\big(\max_i\sum_jL_{ji}\big)d_\Sigma(x,y)$。
2. 若 $d_\vee(\phi x,\phi y)\le c\,d_\vee(x,y)$，则 $c\mathbf J\in\mathcal L^+(\phi)$（$\mathbf J$ 为全 $1$ 阵）。
3. 若 $\ell\in\mathcal L^-(\phi)$，则 $d_\Sigma(\phi x,\phi y)\ge\big(\min_i\sum_j\ell_{ji}\big)d_\Sigma(x,y)$。
4. $\mathrm{diag}(c_j)\in\mathcal L^+(\phi)\iff d_j(\phi x,\phi y)\le c_jd_j(x,y)$（分量式 Lipschitz）。
5. 设 $\mathrm{dom}\,\phi\ne\emptyset$。则下列等价：
   - (α) $\mathcal L^+(\phi)$ 含有限型矩阵；
   - (β) 存在 $c<\infty$ 使 $d_\vee(\phi x,\phi y)\le c\,d_\vee(x,y)$；
   - (γ) 存在 $c'<\infty$ 使 $d_\Sigma(\phi x,\phi y)\le c'\,d_\Sigma(x,y)$。

   所以有限型矩阵的**存在性**并不比单一常数更一般，矩阵的价值在于定量细化（分量间串扰）与复合/压缩判据（定理 2.1、命题 2.7）。

*证*

- (1) $d_j'\le\sum_iL_{ji}d_i\le(\sum_iL_{ji})d_\vee$，再对 $j$ 取最大。第二式对 $j$ 求和并交换求和次序。
- (2) $d_j'\le d_\vee'\le c\,d_\vee\le c\sum_id_i$。
- (3) $\sum_jd_j'\ge\sum_i(\sum_j\ell_{ji})d_i\ge(\min_i\sum_j\ell_{ji})\sum_id_i$。
- (4) 直接验证。
- (5) (α)⇒(β) 由 (1)。(β)⇒(α) 由 (2)。(β)⇔(γ)：由 $d_\vee\le d_\Sigma\le n\,d_\vee$，(β)⇒(γ) 取 $c'=nc$，(γ)⇒(β) 取 $c=nc'$。∎

### 2.6 逐对“通道”形式：典范数值、取到性、不对称

对 $i,j\in I$ 令

- $\mathcal A^+_{ji}=\{c\in\mathbb S:d_j(\phi x,\phi y)\le c\,d_i(x,y)\ \forall x,y\}$，
- $\mathcal A^-_{ji}=\{c:c\,d_i(x,y)\le d_j(\phi x,\phi y)\ \forall x,y\}$，
- $\mathcal C_{ji}=\{t:d_i(x,y)\le t\Rightarrow d_j(\phi x,\phi y)=0\ \forall x,y\}$。

它们恰是联合定义中只含单个“活跃”列的行（(U)：$L_{j\cdot}=ce_i$；(D) 同理；(C)：$\Theta_{ji}=t$，其余 $=\infty$）。定义典范数值

$$\lambda^+_{ji}=\inf\mathcal A^+_{ji}\ (\inf\emptyset:=\infty),\qquad\lambda^-_{ji}=\sup\mathcal A^-_{ji},\qquad\theta_{ji}=\inf\{d_i(x,y):d_j(\phi x,\phi y)>0\}\ (\inf\emptyset=\infty).$$

**命题 2.6**

1. **下**：$\mathcal A^-_{ji}=[0,\lambda^-_{ji}]$，上确界总可取到。若存在点对满足 $d_i=\infty>d_j'$，则 $\lambda^-_{ji}=0$。否则 $\lambda^-_{ji}=\inf\{d_j'/d_i:0<d_i<\infty\}$（$d_j'=\infty$ 时比值记 $\infty$；$\inf\emptyset=\infty$）。
2. **上**：若通道 $i\to j$ 零相容（$d_i=0\Rightarrow d_j'=0$），则 $\lambda^+_{ji}=\sup\{d_j'/d_i:0<d_i<\infty\}$（$\sup\emptyset=0$），且 $\mathcal A^+_{ji}=[\lambda^+_{ji},\infty]$。唯一例外：$\lambda^+_{ji}=0$ 且存在 $d_i=\infty,\ d_j'>0$ 的点对，此时 $\mathcal A^+_{ji}=(0,\infty]$，下确界取不到。通道不零相容时 $\mathcal A^+_{ji}=\emptyset$，$\lambda^+_{ji}=\infty$ 仅是占位。
3. **阈值**：$[0,\theta_{ji})\subseteq\mathcal C_{ji}\subseteq[0,\theta_{ji}]$，且 $\theta_{ji}\in\mathcal C_{ji}$ 当且仅当没有满足 $d_j'>0$ 的点对使 $d_i(x,y)=\theta_{ji}$。
4. **通道⇒联合**：若 $c_i\in\mathcal A^+_{ji}$（或 $c_i\in\mathcal A^-_{ji}$）对一切 $i$ 成立，则对任意权 $w_i\ge0$，$\sum_iw_i=1$，行 $(w_ic_i)_i$ 属于联合型第 $j$ 行的容许集。若 $t_i\in\mathcal C_{ji}$，则 $(\infty,\dots,t_i,\dots,\infty)\in\mathcal C_j$。逆命题不成立（例 3.1、例 3.7）。
5. **复合**：$\mathcal A^\pm_{jk}(\psi)\cdot\mathcal A^\pm_{ki}(\phi)\subseteq\mathcal A^\pm_{ji}(\psi\circ\phi)$。因此 $\lambda^-_{ji}(\psi\phi)\ge\max_k\lambda^-_{jk}(\psi)\lambda^-_{ki}(\phi)$ 总成立。两个最优上值都取到时，$\lambda^+_{ji}(\psi\phi)\le\min_k\lambda^+_{jk}(\psi)\lambda^+_{ki}(\phi)$。**一般的数值乘积律在 $0\cdot\infty$ 处失效**（例 3.6），所以本文的复合律陈述在容许矩阵（证书）上。

*证*

- (1) 约束按 $d_i$ 取值分类：
  - $d_i=0$：$0\le d_j'$，平凡；
  - $0<d_i<\infty$：$c\le d_j'/d_i$；
  - $d_i=\infty$：$c\cdot\infty\le d_j'\iff c=0$ 或 $d_j'=\infty$。

  故有“坏点对”（$d_i=\infty>d_j'$）时 $\mathcal A^-=\{0\}$，否则 $\mathcal A^-=[0,\inf\text{比值}]$，是闭下集。
- (2) 约束：
  - $d_i=0$：$d_j'=0$（即通道零相容，否则 $\mathcal A^+=\emptyset$）；
  - $0<d_i<\infty$：$c\ge d_j'/d_i$；
  - $d_i=\infty$：$c>0$ 或 $d_j'=0$。

  令 $R=\sup\{d_j'/d_i:0<d_i<\infty\}$。$R>0$ 时 $\mathcal A^+=[R,\infty]$。$R=0$ 时，$\mathcal A^+=[0,\infty]$（无 $d_i=\infty,d_j'>0$ 的点对）或 $(0,\infty]$。
- (3) 可见点对（$d_j'>0$）的 $d_i$ 均 $\ge\theta_{ji}$。故 $t<\theta_{ji}$ 时前提 $d_i\le t$ 碰不到可见点对。$t>\theta_{ji}$ 时必有可见点对满足 $d_i<t$。$t=\theta_{ji}$ 时 $t\in\mathcal C_{ji}$ 当且仅当无可见点对满足 $d_i=\theta_{ji}$。
- (4) $d_j'=\sum_iw_id_j'\le\sum_iw_ic_id_i$。下界：$\sum_iw_ic_id_i\le\sum_iw_id_j'=d_j'$。阈值行：只需某个 $i$ 满足 $d_i\le t_i$ 即可得 $d_j'=0$。
- (5) 逐步用单调性与结合律：上界 $d_j(\psi\phi)\le c'd_k(\phi)\le c'c\,d_i$，下界同理。∎

### 2.7 应用：Perov 型压缩原理

矩阵常数的实质用处在于下面的压缩判据：单一常数 $\max_j\sum_iL_{ji}$ 可以远大于 $1$，而谱半径仍 $<1$。

**命题 2.7** 设 $L\in\mathcal L^+(\phi)$ 为有限型，且谱半径 $\rho(L)<1$（把 $L$ 看作实非负 $n\times n$ 矩阵）。标准事实：此时 $L^m\to O$，$\sum_{k\ge0}L^k=(E-L)^{-1}$ 收敛且逐元非负有限。

- (a)（唯一性）若 $y\approx z$ 且 $D(y,\phi y)=D(z,\phi z)=\mathbf 0$，则 $y\sim z$。
- (b)（先验估计）若 $x\approx\phi x$，记 $\delta=D(x,\phi x)\in[0,\infty)^I$，$x_k=\phi^kx$，则对 $m\ge n$ 有 $D(x_n,x_m)\preceq L^n(E-L)^{-1}\delta$。故 $(x_k)$ 对每个 $d_i$ 是 Cauchy 列。
- (c)（存在性）若 $D(x_k,x^*)\to\mathbf 0$（例如 $x$ 的 $\approx$-类关于 $\mathcal G$ 完备），则 $D(x^*,\phi x^*)=\mathbf 0$，且 $D(x_n,x^*)\preceq L^n(E-L)^{-1}\delta$。族分离时 $\phi x^*=x^*$。

*证*

- (a) $D(y,z)\preceq D(y,\phi y)+D(\phi y,\phi z)+D(\phi z,z)=D(\phi y,\phi z)\preceq L\,D(y,z)$。令 $u=D(y,z)$ 有限，则 $u\preceq Lu\preceq\dots\preceq L^mu\to\mathbf 0$。
- (b) 归纳：$D(x_k,x_{k+1})=D(\phi x_{k-1},\phi x_k)\preceq L\,D(x_{k-1},x_k)\preceq L^k\delta$（有限）。再由三角不等式 $D(x_n,x_m)\preceq\sum_{k=n}^{m-1}L^k\delta\preceq\sum_{k\ge n}L^k\delta=L^n(E-L)^{-1}\delta$。
- (c) $D(x^*,\phi x^*)\preceq D(x^*,x_{n+1})+D(\phi x_n,\phi x^*)\preceq D(x^*,x_{n+1})+L\,D(x_n,x^*)\to\mathbf 0$（$L$ 有限）。估计：对固定 $n$，令 $m\to\infty$，用 $d_i(x_n,x^*)\le d_i(x_n,x_m)+d_i(x_m,x^*)$。∎

**注** $\phi(x)=(x_1/2+10x_2,\ x_2/2)$ 在 $\mathbb R^2$（$d_i=|\Delta_i|$）上取 $L=\begin{pmatrix}1/2&10\\0&1/2\end{pmatrix}$，$\rho(L)=1/2$，命题 2.7 适用。但 $d_\vee$ 下 $\phi$ 的 Lip 常数 $\ge10$（取 $\Delta=(0,1)$），命题 2.5(1) 的标量常数 $\max_j\sum_iL_{ji}=10.5>1$，故对 $d_\vee$ 直接用 Banach 原理不行。

---

## 3. 例子与反例

**例 3.1（为什么必须是联合型矩阵，以及为什么需要反向形式）** $\mathcal X=\mathbb R^2\cup\{\bot\}$，$d_i=|\Delta_i|$（$i=1,2$），$\phi(x)=(x_1+2x_2,\,3x_1)$。

- 联合型：$L=\begin{pmatrix}1&2\\3&0\end{pmatrix}\in\mathcal L^+(\phi)$，且每行容许集有最小元（取 $\Delta=(1,0),(0,1)$ 得 $r_1\ge1,r_2\ge2$ 等），故 $L$ 是最小的上矩阵。
- 逐对型：第 1 行的两条通道都不零相容（$\Delta_1=0,\Delta_2\ne0$ 时 $d_1'>0$；$\Delta_2=0,\Delta_1\neq0$ 时同样），第 2 行的 $2\to2$ 通道也不零相容。只有 $\lambda^+_{21}=3$ 有意义，其余全是占位的 $\infty$。
- 单一常数：$d_\vee$ 下的 Lip 常数恰为 $3$，看不出 $d_2'$ 不依赖 $d_2$。
- 直接下矩阵：最大者是 $\ell=\begin{pmatrix}0&0\\3&0\end{pmatrix}$。第 1 行必为 $0$，因为 $\Delta_1=-2\Delta_2$ 时输出分量 1 为 $0$。
- 反向矩阵：$M=\begin{pmatrix}0&1/3\\1/2&1/6\end{pmatrix}\in\mathcal L^\leftarrow(\phi)$，因为 $|\Delta_1|=|\Delta_2'|/3$，$|\Delta_2|\le|\Delta_1'|/2+|\Delta_2'|/6$。含 $\bot$ 的对要求 $M$ 各行非零，成立。

可见分量混合型映射的“可逆性”只被 (R) 捕捉，(D) 在此给出 $0$ 行。命题 2.4(f) 的左逆条件不满足：$\ell$ 的第 2 列为零。

**例 3.2（非分离：$\infty$ 失效）** $\mathcal X=\{a,b,\bot\}$，$d_i(a,b)=0$，$d_i(a,\bot)=d_i(b,\bot)=\infty$，满足 (i)–(iv)。令 $\phi(a)=a$，$\phi(b)=\bot$。则 $D(a,b)=\mathbf 0$ 而 $D(\phi a,\phi b)=\boldsymbol\infty$，$\phi$ 不零相容。由定理 2.2，$\mathcal L^+(\phi)=\mathcal C(\phi)=\emptyset$，连 $\Omega$ 都不行。又 $\mathcal L^-(\phi)=\{O\}$（命题 2.3(3)），$\mathcal L^\leftarrow(\phi)=\emptyset$（命题 2.3(5)）。

**例 3.3（定义域截断）** $\mathcal X=\mathbb R\cup\{\bot\}$，$d=|x-y|$，$\phi_S=\mathrm{id}$ 于 $S=[0,1]$，其余取 $\bot$。族分离，故 $\Omega\in\mathcal L^+(\phi_S)$。但无有限上矩阵（取 $x=0$，$y=-\varepsilon$，命题 2.3(2)），$\mathcal L^-(\phi_S)=\{O\}$，$\mathcal L^\leftarrow(\phi_S)=\emptyset$。限制到 $S$ 后（注 4.1），$1$ 同时是上、下矩阵。

**例 3.4（$\infty$ 元素自然出现；容许集有极小元但不被其控制）** $\mathcal X=\mathbb R\cup\{\bot\}$，$d_1=|x-y|$，$d_2(x,y)=\infty\cdot[x\ne y]$（含 $\bot$，满足 (iv)），$\phi=\mathrm{id}$。

- 下矩阵（直接形式）：第 1 行由 $x\ne y\in\mathbb R$ 得 $\ell_{11}|\Delta|+\ell_{12}\cdot\infty\le|\Delta|$，即 $\ell_{12}=0,\ \ell_{11}\le1$。第 2 行无约束。故最大下矩阵是 $\begin{pmatrix}1&0\\\infty&\infty\end{pmatrix}$：离散通道把任何可分辨性放大成无穷可分辨性。
- 上矩阵：第 1 行容许集是 $A=\{r:\ r_1\ge1\ \text{或}\ r_2>0\}$（$\bot$ 对要求 $r\ne0$，已含于其中）。
  - $(1,0)$ 是 $A$ 的极小元。
  - 但对任意 $\varepsilon>0$，容许元 $(0,\varepsilon)$ 之下**没有**任何极小容许元：若 $r\le(0,\varepsilon)$ 容许，则 $r_1=0,r_2>0$，而 $(0,r_2/2)$ 仍容许且更小。
  - $A$ 对逐元取小不封闭：$(1,0)\wedge(0,\varepsilon)=(0,0)\notin A$。
  - 这是注 0.2 的现象：$(0,1/k)$ 的下确界 $(0,0)$ 不容许。
- 若所有距离都有限，则不会发生：每个约束 $\sum_ir_id_i\ge c$ 定义紧空间 $[0,\infty]^I$ 的闭集（$r_i\mapsto r_id_i$ 连续），$A$ 闭。对 $r\in A$，在紧集 $\{r'\in A:r'\le r\}$ 上最小化 $\sum_i\arctan r_i'$ 得极小元。

（上一版此处误称 $A$ “无极小元”。）

**例 3.5（有限正阈值）** $\mathcal X=\{10m,\,10m+\tfrac12:m\in\mathbb Z\}\cup\{\bot\}$，单通道 $d=|x-y|$，$\phi(10m)=\phi(10m+\tfrac12)=10m$（“簇吸附”）。

- $\theta=9.5$，由 $x=10m+\tfrac12$、$y=10(m+1)$ 取到，故 $\mathcal C=[0,9.5)$。
- $\lambda^+=20/19$，取到。$\lambda^-=0$，与命题 2.4(b) 一致。
- Lip 矩阵 $20/19>0$ 只给出 $\Theta^L=0$（命题 2.4(a)），有限阈值 $9.5$ 是新信息。

**例 3.6（数值乘积律失效）** $\mathcal X=\{a,b,u,v,\bot\}$，单通道，$d(a,b)=1$，其余不同点对距离 $\infty$（这是满足三角不等式的族分离空间）。令 $\phi(a)=u,\phi(b)=v$，$\psi(a)=\psi(b)=a$，其余点（含 $u,v,\bot$）不动。则 $\mathcal A^+(\phi)=\{\infty\}$，$\mathcal A^+(\psi)=(0,\infty]$，$\mathcal A^+(\psi\phi)=\{\infty\}$。于是 $\lambda^+(\psi\phi)=\infty>0=\lambda^+(\psi)\lambda^+(\phi)$。在容许常数层面，$c'\cdot\infty=\infty\ (c'>0)$ 无矛盾，这正是复合律陈述在证书上的原因。

**例 3.7（联合阈值不能还原为通道阈值）** $\mathcal X=\{p,p',q,r,\bot\}$，$I=\{1,2\}$，距离 $(d_1,d_2)$ 为：

| 点对 | $(d_1,d_2)$ |
|---|---|
| $pp'$ | $(5,5)$ |
| $pq$ | $(1,100)$ |
| $p'q$ | $(6,105)$ |
| $pr$ | $(100,1)$ |
| $p'r$ | $(105,6)$ |
| $qr$ | $(100,100)$ |
| 含 $\bot$ 的对 | $(\infty,\infty)$ |

两个分量都满足三角不等式（已逐三元组核对）。令 $\phi(p)=\phi(p')=p$，$\phi(q)=q$，$\phi(r)=r$，$\phi(\bot)=\bot$。

- 第 1 分量的可见剖面是 $(1,100),(6,105),(100,1),(105,6),(100,100)$ 及含 $\bot$ 的 $(\infty,\infty)$。
- 盒子 $[0,50]^2$ 内只有点对 $(p,p')$（剖面 $(5,5)$），它被坍缩。故 $\Theta_{1\cdot}=(50,50)\in\mathcal C_1$，非平凡。
- 而通道阈值 $\theta_{11}=\theta_{12}=1$，$\mathcal C_{11},\mathcal C_{12}\subseteq[0,1]$。通道形式看不到这条坍缩信息。

---

## 4. 注记

**注 4.1（区域化）** 对子集 $S\subseteq\mathcal X$，把定义 1.1 的量词改为 $x,y\in S$，得 $\mathcal L^\pm(\phi;S)$、$\mathcal L^\leftarrow(\phi;S)$、$\mathcal C(\phi;S)$。

- 若 $\phi(S)\subseteq S'$，则 $L\in\mathcal L^+(\phi;S)$，$L'\in\mathcal L^+(\psi;S')\Rightarrow L'L\in\mathcal L^+(\psi\phi;S)$。
- “$\phi$ 在 $S$ 上第 $j$ 分量不可区分”等价于 $0$ 是第 $j$ 行容许元，这样“死区”型算子也在框架内。
- $\mathcal L^+(\phi)=\{L\in\mathcal L^+(\phi;\mathrm{dom}\,\phi):\forall x\in\mathrm{dom}\,\phi,\ y\notin\mathrm{dom}\,\phi:\ LD(x,y)=\boldsymbol\infty\}$。分情形即得：两点都在定义域内是区域版；两点都不在时 $D=\mathbf 0$ 平凡；一在一不在时 $D(\phi x,\phi y)=\boldsymbol\infty$，要求 $LD(x,y)=\boldsymbol\infty$。右边第二个条件是 $\bot$ 带来的边界条件。

**命题 4.1（链连通性迫使有限阈值平凡）** 设 $\Theta\in\mathcal C(\phi)$，$j\in I$。若 $x,y$ 被 $\Theta_{j\cdot}$-链连接（$x=z_0,\dots,z_N=y$，$D(z_{k-1},z_k)\preceq\Theta_{j\cdot}$），则 $d_j(\phi x,\phi y)=0$。特别地，若 $\Theta_{j\cdot}$ 的各分量有限（此时 $\bot$ 与其他点不相连）且 $\mathcal X\setminus\{\bot\}$ 是 $\Theta_{j\cdot}$-链连通的（例如 $\mathbb R^m$ 配坐标距离族且各 $\Theta_{ji}>0$），则 $\mathrm{dom}\,\phi=\emptyset$，或 $\mathrm{dom}\,\phi=\mathcal X\setminus\{\bot\}$ 且 $d_j(\phi x,\phi y)=0$ 对一切 $x,y\ne\bot$ 成立。

*证* 由 $d_j$ 的三角不等式，$d_j(\phi x,\phi y)\le\sum_kd_j(\phi z_{k-1},\phi z_k)=0$。若某链上 $\phi x=\bot\ne\phi y$，则 $d_j=\infty\ne0$，矛盾，所以链连通类上定义域“全有或全无”。∎

所以有意义的有限正阈值只出现在带间隙的空间（例 3.5、例 3.7），或某些 $\Theta_{ji}=0$ 使盒子退化的情形。

**注 4.2（变体）**

- **取最大型 vs 求和型。** 把 $\sum_i$ 换成 $\max_i$（半环 $(\mathbb S,\max,\cdot)$，$(A\otimes v)_j=\max_iA_{ji}v_i$，$(A\otimes B)_{ji}=\max_kA_{jk}B_{ki}$），得 $\mathcal L^\pm_\vee$。凡只用到引理 0.3 的 (b)(c) 与结合律的结论逐字平行成立，即：
  - 定理 2.1 与定理 2.2（含 (R)）；
  - 命题 1.2；
  - 命题 2.3、2.4(a)–(g)（命题 2.4(f) 需把 $N\ell$ 换为 $N\otimes\ell$）；
  - 命题 2.6（通道量不变）。

  变化的只是命题 2.5 中的常数。两类矩阵的关系：$\mathcal L^+_\vee\subseteq\mathcal L^+_\Sigma$，$n\mathcal L^+_\Sigma\subseteq\mathcal L^+_\vee$，$\mathcal L^-_\Sigma\subseteq\mathcal L^-_\vee$，$\tfrac1n\mathcal L^-_\vee\subseteq\mathcal L^-_\Sigma$。
- **下矩阵的典范最大元。** $\ell\in\mathcal L^-_\vee(\phi)\iff\ell_{ji}\in\mathcal A^-_{ji}\ \forall i,j\iff\ell\le\lambda^-$（命题 2.6(1)）。故取最大型的下矩阵有**最大元** $\lambda^-$。求和型下矩阵满足 $\tfrac1n\lambda^-\in\mathcal L^-_\Sigma(\phi)\subseteq\{\ell\le\lambda^-\}$：$\sum_i\tfrac{\lambda^-_{ji}}n d_i\le\sum_i\tfrac1nd_j'=d_j'$。上矩阵则无此典范性（推论 1.3(iii)、例 3.4）。
- $|I|<\infty$ 用于有限和、矩阵乘法与上述因子 $n$。

---

## 5. 小结、修订说明与自评

**小结**

1. **矩阵化。** (U) 与 (C) 的复合律对应矩阵乘法与盒子运算（定理 2.1），并可回到单一常数（命题 2.5）。有限型存在性等价于标量 $d_\vee$-Lipschitz，矩阵的增益在于定量细化与压缩判据（命题 2.7）。
2. **下限。** (D) 总存在（$O$），但与 $\bot$、坍缩互斥（命题 2.3(3)、2.4(b)）。(R) 的存在性恰为零反射（定理 2.2(B)），按相反次序复合。$|I|=1$ 时 $M=1/\ell$，矩阵情形二者不等价（例 3.1）。取最大型下矩阵有典范最大元 $\lambda^-$（注 4.2）。
3. **$\infty$ 扩展。** 扩展上矩阵存在 $\iff$ 零相容，扩展反向矩阵存在 $\iff$ 零反射。族分离时前者恒存在，不分离时 $\infty$ 无法弥补零距离被拉成正距离（定理 2.2、例 3.2）。数值最优值有取不到的情形（命题 2.6、注 0.2），所以复合律陈述在容许矩阵上。
4. **不可区分矩阵。** (C) 与 Lip 矩阵同属对输出分量的上包络，一个是线性的，一个是阶梯的（命题 1.2）。Lip 矩阵的零元给出 $\infty$ 阈值（命题 2.4(a)），混合复合见定理 2.1(5)(6)。联合型阈值严格强于通道型（例 3.7），有限正阈值需要带间隙的空间（命题 4.1）。

**相对上一版**

- **保留**：总体框架、(U)(D)(C) 的定义、定理 2.1(1)–(3)、2.2(A)、命题 1.2、2.3(1)(2)(4)、2.4(a)–(e)、2.5(1)–(4)、2.6 及例 3.1–3.3、3.5、3.6。这些已重新核对，未改动结论。
- **修正**：
  - 例 3.4 的“无极小元”是错的，$(1,0)$ 是极小元，正确表述是“存在不被任何极小元控制的容许元”，并补了有限距离情形的反面结论。
  - 推论 2.1′ 里“具有下矩阵的算子类构成子幺半群”是空洞/错误的，已改并给出反例。
  - 命题 2.3(3) 的“单射”需要零相容，已补。
  - 总览表中“同构”一词夸大，已改为“同一响应函数的两种读数”。
  - 原注 4.1 关于连通空间的含糊断言，换成命题 4.1。
  - 注 4.2 的“全部结论平行成立”收紧为明确列出的范围。
- **新增**：(R) 反向下界矩阵及其复合律与存在性判据（定理 2.1(4)、2.2(B)、命题 2.3(5)、2.4(f)(g)）；命题 1.2 中 $\mathcal C$ 的“可见剖面上闭包补集”刻画；行容许集的凸性；命题 2.5(5)（有限型存在性等价于标量 Lipschitz）；命题 2.7（Perov 型压缩）；取最大型下矩阵的典范最大元；例 3.7。
- **核对**：本轮用本地脚本（不随答卷提交）做了随机有限空间核对。空间含 4–6 个点（含 $\bot$），分量由带零距离与 $\infty$ 距离的随机图伪度量、倍数、和、最大值与二值离散度量生成，算子随机（含映到 $\bot$ 者），矩阵取自网格 $\{0,\tfrac12,1,2,\infty\}$。
  - $|I|=2$（450 个空间）与 $|I|=3$（80 个空间）：定理 2.1(2)–(6)（共约 3.2 万次复合检验）、定理 2.2(A)、命题 2.3、2.4(a)–(d)、2.6 的全部公式，均无反例。
  - $|I|=2$（另 300 个空间）：定理 2.2(B) 的 $\Omega$ 判据、定理 2.1(4)、命题 1.2(1)(4)、2.4(f)(g)、命题 4.1 的链结论、行容许集凸性，无反例。
  - 数值抽样：例 3.1、3.5，Perov 先验估计（2000 个随机 $2\times2$ 仿射映射）。例 3.7 的距离表与三角不等式也已机器核对。
  - 其余（命题 2.4(e)、2.5(5)、2.7(a)(c)、例 3.2–3.4、3.6）为手工推导。核对只是反例搜索，不替代上面写出的证明。

**仍未完成/不确定**

- 解读选择 (I1)–(I5) 是否与出题者本意完全一致，无法验证。我保留了求和型、取最大型、逐对型三种读法并说明关系。
- (C) 的复合阈值 $\Theta''$ 是充分的，未证最优。(C) 与 (U) 之间只建立了 $\{0,\infty\}$ 型对应与混合复合，没有给出完整的 Galois 型最优对应。
- 随机核对只覆盖 $|I|\le3$ 的小有限空间与有限网格，无穷空间上的结论依赖证明本身。

**自评**

- 就本题（把想法整理成自洽定义与基本性质并给出论证）而言，我认为在声称范围内完整正确，应属 B2。上一版的 4 处错误或空洞表述已在本稿订正。
- 研究增量方面，新增结果是局部的：对偶存在性判据、与标量 Lipschitz 的等价、一个应用（Perov）、一个典范最大下矩阵。我只主张 R1 级的局部推进，不主张更高。