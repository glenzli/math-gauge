# 扩展规范空间上算子的上、下 Lipschitz 矩阵与坍缩半径矩阵

**对四个问题的回答概要：**

- **矩阵化。** 对每对"输入分量 $i$、输出分量 $j$"各取一个最优常数，组成矩阵。
- **下限。** 定义下 Lipschitz 矩阵。
- **支持 $\infty$。** 三个矩阵的元素都取值于 $[0,+\infty]$，每个算子都有唯一确定的矩阵。$\infty$ 的含义靠两种乘法区分：上界用 $0\star\infty=\infty$（$\infty$ 表示"无约束"），下界沿用题设的 $0\cdot\infty=0$。
- **"输出不可区分"。** 定义坍缩半径矩阵 $\mathbf R$。它与 Lipschitz 矩阵是同一类东西：同样逐元素取最优值、可以取到、有复合律，并且满足 $\overline L_{ji}=0\iff R_{ji}=\infty$。

本文只写数学论证，没有用 Lean 或数值计算核对。

---

## 0 设定、记号与两种乘法

**0.1 空间与算子。** 设 $(\mathcal X,\{d_i\}_{i\in I},\bot)$、$(\mathcal Y,\{e_j\}_{j\in J},\bot)$、$(\mathcal Z,\{f_k\}_{k\in K},\bot)$ 是扩展规范空间。为了讨论复合，记
$$\mathrm{Op}(\mathcal X,\mathcal Y)=\{\phi:\mathcal X\to\mathcal Y\mid\phi(\bot)=\bot\},\qquad \mathrm{dom}\,\phi=\{x\mid \phi(x)\neq\bot\}.$$
CH1 的算子空间就是 $\mathcal X_{op}=\mathrm{Op}(\mathcal X,\mathcal X)$，此时 $J=I$，矩阵是方阵。下文所有结论对它都成立。记 $\mathcal X^\circ=\mathcal X\setminus\{\bot\}$，显然 $\mathrm{dom}\,\phi\subseteq\mathcal X^\circ$。

**0.2 矩阵。** 矩阵 $A\in\bar{\mathbb R}_+^{J\times I}$ 的行标是输出分量 $j$，列标是输入分量 $i$。元素 $A_{ji}$ 描述输入分量 $d_i$ 对输出分量 $e_j$ 的控制。矩阵之间按元素比较大小。记 $\mathbf d(x,y)=(d_i(x,y))_{i\in I}$。

**0.3 两种乘法。** 全文约定不变，乘法 $a\cdot b$ 满足 $0\cdot\infty=0$。另外单独命名一个运算：
$$a\star b=\begin{cases}ab,& a,b<\infty,\\ +\infty,& a=\infty\ \text{或}\ b=\infty.\end{cases}$$
两者只在 $0$ 与 $\infty$ 相乘时不同。可以这样理解：在点 $(0,\infty)$ 处，$\cdot$ 取乘积的下极限（下半连续延拓），$\star$ 取上极限（上半连续延拓）。

逐情形验证可知：两种乘法都交换、结合，并且对每个变元单调不减；$0$ 对 $\cdot$ 是吸收元，$\infty$ 对 $\star$ 是吸收元；$\star$ 对 $+$ 有分配律。因此 $(\bar{\mathbb R}_+,\max,\cdot)$ 和 $(\bar{\mathbb R}_+,\min,\star)$ 都是交换半环。据此定义两种矩阵积，它们满足结合律，并对每个因子单调：
$$(A\boxtimes B)_{ki}=\min_j A_{kj}\star B_{ji},\qquad (A\boxdot B)_{ki}=\max_j A_{kj}\cdot B_{ji}.$$

**0.4 考察区域。** 下面每个量都相对于一个子集 $S\subseteq\mathcal X$ 定义（$S$ 可以含 $\bot$），用上标 $S$ 标出。$S$ 用来形式化"输入落入的范畴"。

---

## 1 上 Lipschitz 矩阵

**定义 1.1。** 设 $\phi\in\mathrm{Op}(\mathcal X,\mathcal Y)$，$S\subseteq\mathcal X$。称有限数 $a\in[0,\infty)$ 为 **$(j,i)$-上界常数**，如果
$$e_j(\phi x,\phi y)\le a\,d_i(x,y)\qquad \forall x,y\in S,\ d_i(x,y)<\infty. \tag{1.1}$$
定义 $\overline L^S_{ji}(\phi)=\inf\{a<\infty: a\text{ 满足 }(1.1)\}$，并约定 $\inf\varnothing=+\infty$。称 $\overline{\mathbf L}^S(\phi)=(\overline L^S_{ji}(\phi))$ 为**上 Lipschitz 矩阵**，规范版本取 $\overline{\mathbf L}(\phi):=\overline{\mathbf L}^{\mathcal X}(\phi)$。

**为什么只看有限距离点对。** (1.1) 等价于对一切 $x,y\in S$ 有 $e_j(\phi x,\phi y)\le a\star d_i(x,y)$。当 $d_i=\infty$ 时，任何 $a>0$ 都自动满足不等式。只有 $a=0$ 时，约定 $0\cdot\infty=0$ 才会制造一个虚假约束。例如对 $x\in\mathrm{dom}\,\phi$ 有 $d_i(x,\bot)=e_j(\phi x,\bot)=\infty$。如果把这类点对也算进去，常值算子的下确界就会是"0 但取不到"。

**引理 1.2。**
- **(a) 比值刻画。** 下式中 $u/0:=\infty$（$u>0$），$\infty/v:=\infty$（$0<v<\infty$），$\sup\varnothing=0$：
$$\overline L^S_{ji}(\phi)=\sup\Bigl\{\tfrac{e_j(\phi x,\phi y)}{d_i(x,y)}:\ x,y\in S,\ d_i(x,y)<\infty,\ (d_i,e_j)\neq(0,0)\Bigr\}.$$
- **(b) 可达。** 若 $\overline L^S_{ji}<\infty$，则它本身满足 (1.1)。
- **(c) 单调。** $S'\subseteq S\Rightarrow \overline{\mathbf L}^{S'}\le\overline{\mathbf L}^{S}$。
- **(d) 与 $\bot$ 无关。** $\overline{\mathbf L}^{S\cup\{\bot\}}=\overline{\mathbf L}^S$。
- **(e) 退化情形。** $|I|=|J|=1$ 时，它就是经典最优 Lipschitz 常数；没有有限常数时取 $+\infty$。

*证明。* (a)(b)：固定一对点，记 $d=d_i<\infty$，$e=e_j$。
- 若 $d=e=0$，任意 $a$ 都满足不等式。
- 若 $d=0<e$，没有有限的 $a$ 满足，而比值为 $\infty$。
- 若 $0<d<\infty$，则 $e\le ad\iff a\ge e/d$。

所以有限可行常数之集恰为 $[\rho,\infty)$，其中 $\rho$ 是 (a) 中的上确界；$\rho=\infty$ 时此集为空。这同时给出 (a) 和 (b)。

(c) 区域越小，约束越少。

(d) 新增的点对 $(x,\bot)$（$x\neq\bot$）满足 $d_i=\infty$，不进入 (1.1)；点对 $(\bot,\bot)$ 给出 $e_j(\bot,\bot)=0$。∎

**命题 1.3（矩阵不等式与唯一最优性）。** 对一切 $x,y\in S$，
$$\mathbf e(\phi x,\phi y)\le \overline{\mathbf L}^S(\phi)\boxtimes\mathbf d(x,y),\quad\text{即}\quad e_j\le\min_i \overline L^S_{ji}\star d_i .$$
如果矩阵 $A$ 也对一切 $x,y\in S$ 满足 $\mathbf e\le A\boxtimes\mathbf d$，那么 $\overline{\mathbf L}^S(\phi)\le A$。所以 $\overline{\mathbf L}^S(\phi)$ 是满足这个不等式的唯一最小矩阵。

*证明。* 若 $\overline L_{ji}=\infty$ 或 $d_i=\infty$，右端对应项为 $\infty$；否则由 1.2(b) 得 $e_j\le\overline L_{ji}d_i$。

反过来，若 $A_{ji}<\infty$，则对 $d_i<\infty$ 的点对有 $e_j\le A_{ji}\star d_i=A_{ji}d_i$，所以 $A_{ji}$ 满足 (1.1)，从而 $\overline L_{ji}\le A_{ji}$。∎

**命题 1.4（取值 $0$ 与 $\infty$ 的含义；零兼容）。**

*零兼容的定义：* 称 $\phi$ 在 $S$ 上 **$(j,i)$-零兼容**，如果对 $x,y\in S$，$d_i(x,y)=0$ 蕴含 $e_j(\phi x,\phi y)=0$。也就是说，$d_i$ 下不可区分的输入给出 $e_j$ 下不可区分的输出。本卷不预设族分离，而且即使整个族分离，单个 $d_i$ 也未必分离，所以这是一个实质条件。

- **(a)** $\overline L_{ji}=0$ 当且仅当 $S$ 中所有 $d_i$-有限距离的点对，其输出的 $e_j$-距离都为 $0$。
- **(b)** $\overline L_{ji}<\infty$ 蕴含 $(j,i)$-零兼容。
- **(c)** $(j,i)$-零兼容当且仅当在标准算术下 $a=+\infty$ 满足 (1.1)。

*证明。* (a) 由 1.2(b)。(b) $d_i=0$ 的点对在 (1.1) 的范围内，于是 $e_j\le\overline L\cdot0=0$。(c) 当 $0<d_i<\infty$ 时 $\infty\cdot d_i=\infty$，不等式自动成立；当 $d_i=0$ 时约束变为 $e_j\le0$。∎

因此 $\overline L_{ji}=\infty$ 有两种来源：
- 零兼容，但没有有限斜率，例如 $\mathbb R$ 上的 $x\mapsto x^2$；
- 不零兼容。此时 $\bar{\mathbb R}_+$ 中任何常数都不满足 (1.1)，包括标准算术下的 $\infty$。

两种情形统一记为 $\infty$。由于 $\infty\star d=\infty$，在命题 1.3 的不等式里 $\infty$ 元素表示"无约束"。所以**每个算子都有唯一的 $\overline{\mathbf L}(\phi)$**，这就是"支持 $\infty$"的统一表达。

**定理 1.5（复合律）。** 设 $\phi\in\mathrm{Op}(\mathcal X,\mathcal Y)$，$\psi\in\mathrm{Op}(\mathcal Y,\mathcal Z)$，$\phi(S)\subseteq T$。则
$$\overline{\mathbf L}^S(\psi\circ\phi)\le\overline{\mathbf L}^T(\psi)\boxtimes\overline{\mathbf L}^S(\phi).$$
由此得到三个特例：
1. **全局版：** $\overline{\mathbf L}(\psi\phi)\le\overline{\mathbf L}(\psi)\boxtimes\overline{\mathbf L}(\phi)$。
2. **定义域版：** $\overline{\mathbf L}^{\mathrm{dom}(\psi\phi)}(\psi\phi)\le\overline{\mathbf L}^{\mathrm{dom}\psi}(\psi)\boxtimes\overline{\mathbf L}^{\mathrm{dom}\phi}(\phi)$。
3. **迭代：** 对 $\phi\in\mathcal X_{op}$ 有 $\overline{\mathbf L}(\phi^n)\le\overline{\mathbf L}(\phi)^{\boxtimes n}$，即
$$\overline L_{i_ni_0}(\phi^n)\le\min_{i_1,\dots,i_{n-1}}\overline L_{i_ni_{n-1}}\star\cdots\star\overline L_{i_1i_0}.$$
这可以读作"分量之间的最优传递路径"。特别地 $\overline L_{ii}(\phi^n)\le\overline L_{ii}(\phi)^n$。

*证明。* 记 $a=\overline L^T_{kj}(\psi)$，$b=\overline L^S_{ji}(\phi)$。若 $a$ 或 $b$ 为 $\infty$，则 $a\star b=\infty$，结论平凡。否则两者都有限且可达。对 $x,y\in S$，$d_i(x,y)<\infty$：
$$e_j(\phi x,\phi y)\le b\,d_i<\infty,\quad\text{又}\ \phi x,\phi y\in T,\quad\text{故}\ f_k(\psi\phi x,\psi\phi y)\le a\,e_j\le ab\,d_i .$$
所以 $ab$ 是可行常数，再对 $j$ 取最小值。

定义域版：若 $x\in\mathrm{dom}(\psi\phi)$，则 $\phi x\neq\bot$（否则 $\psi\phi x=\psi\bot=\bot$），并且 $\phi x\in\mathrm{dom}\,\psi$。所以 $\phi(\mathrm{dom}(\psi\phi))\subseteq\mathrm{dom}\,\psi$。再由 $\mathrm{dom}(\psi\phi)\subseteq\mathrm{dom}\,\phi$、1.2(c) 和 $\boxtimes$ 的单调性即得。迭代版由结合律和归纳得到。∎

**反例：若用标准乘法 $0\cdot\infty=0$，复合律不成立。**
- 取 $\mathcal X=\mathbb R\cup\{\bot\}$，$d=|\cdot|$；$\mathcal Y=\{0,1,\bot\}$，$e(0,1)=\infty$；$\mathcal Z=\{0,1,\bot\}$，$f(0,1)=1$。各点到 $\bot$ 的距离都是 $\infty$，条件 (i)–(iv) 显然成立。
- 令 $\phi(x)=\mathbf 1[x\ge0]$，$\psi$ 为恒等嵌入。
- $\mathcal Y$ 中 $e$-距离有限的点对只有对角对，所以 $\overline L(\psi)=0$。
- 看点对 $(-\varepsilon,0)$：$\phi$ 把它们映到 $e$-距离 $\infty$，$\psi\phi$ 映到 $f$-距离 $1$，所以 $\overline L(\phi)=\overline L(\psi\phi)=\infty$。
- 标准乘法给出错误的界 $\overline L(\psi\phi)\le 0\cdot\infty=0$；而 $0\star\infty=\infty$ 给出正确的界。

**推论 1.6（分量比较矩阵）。** 令 $\mathbf C_{\mathcal X}:=\overline{\mathbf L}(\mathrm{id}_{\mathcal X})$。它的元素 $(\mathbf C_{\mathcal X})_{i'i}$ 是在 $d_i$-有限点对上使 $d_{i'}\le c\,d_i$ 成立的最优常数，描述规范结构内部各分量之间的强弱关系。则：
- $(\mathbf C_{\mathcal X})_{ii}\le1$；
- $\mathbf C_{\mathcal X}\boxtimes\mathbf C_{\mathcal X}=\mathbf C_{\mathcal X}$；
- 对任意 $\phi$，$\overline{\mathbf L}(\phi)=\mathbf C_{\mathcal Y}\boxtimes\overline{\mathbf L}(\phi)\boxtimes\mathbf C_{\mathcal X}$。

也就是说，最优矩阵已经自动吸收了分量之间的比较关系。

*证明。* $c=1$ 可行，故对角元 $\le1$。由 $\phi=\phi\circ\mathrm{id}$ 和定理 1.5 得 $\overline{\mathbf L}(\phi)\le\overline{\mathbf L}(\phi)\boxtimes\mathbf C_{\mathcal X}$。反向：取中间指标为 $i$，得 $(\overline{\mathbf L}(\phi)\boxtimes\mathbf C_{\mathcal X})_{ji}\le\overline L_{ji}\star C_{ii}\le\overline L_{ji}$。左乘 $\mathbf C_{\mathcal Y}$ 同理。取 $\phi=\mathrm{id}$ 即得幂等性。∎

**命题 1.7（与单一常数的关系）。** $d_{\max}=\max_i d_i$ 仍满足 (i)–(iv)，$e_{\max}$ 同理。在这两个单分量结构下，$\phi$ 的上 Lipschitz 常数满足
$$\mathrm{Lip}^S(\phi;d_{\max}\to e_{\max})\le\max_j\min_i\overline L^S_{ji}(\phi).$$

*证明。* 设右端为有限的 $c$。对每个 $j$ 取 $i_j$ 使 $\overline L_{ji_j}\le c$。若 $d_{\max}<\infty$，则 $e_j\le\overline L_{ji_j}d_{i_j}\le c\,d_{\max}$ 对每个 $j$ 成立。∎

矩阵通常比单一常数多含信息，见例 5.1。

**注 1.8（联合型界矩阵）。** $\overline{\mathbf L}$ 只记录"单个输入分量控制单个输出分量"。若需要刻画联合依赖，可以考虑矩阵集合
$$\mathfrak J^S(\phi)=\Bigl\{A:\ e_j(\phi x,\phi y)\le\textstyle\sum_i A_{ji}\star d_i(x,y),\ \forall x,y\in S,\ \forall j\Bigr\}.$$
它有以下性质：
- **(a)** 每行只在一个位置取 $\overline{\mathbf L}$ 的相应元素、其余为 $0$ 的矩阵都属于 $\mathfrak J^S$（由命题 1.3）。
- **(b)** 复合封闭：用积 $(AB)_{ki}=\sum_jA_{kj}\star B_{ji}$，有 $\mathfrak J^T(\psi)\cdot\mathfrak J^S(\phi)\subseteq\mathfrak J^S(\psi\phi)$。证明同定理 1.5，用单调性、结合律和分配律。
- **(c)** 它能捕捉联合依赖。例如 $\phi(x)=x_1+x_2$（从带坐标伪度量的 $\mathbb R^2$ 到 $\mathbb R$）既不 $(1,1)$-零兼容也不 $(1,2)$-零兼容，所以 $\overline{\mathbf L}=(\infty,\infty)$；但 $(1,1)\in\mathfrak J$。
- **(d)** 它一般没有最小元。例如 $d_1=d_2=|\cdot|$ 时，恒等映射满足 $(a_1,a_2)\in\mathfrak J\iff a_1+a_2\ge1$。

因此本文以分量矩阵 $\overline{\mathbf L}$ 作为规范（唯一最优）的对象，$\mathfrak J$ 作为集合值的细化。

---

## 2 下 Lipschitz 矩阵

**定义 2.1。** 对 $S\subseteq\mathcal X$，令
$$\underline L^S_{ji}(\phi)=\sup\{b\in\bar{\mathbb R}_+:\ e_j(\phi x,\phi y)\ge b\cdot d_i(x,y)\ \ \forall x,y\in S\}. \tag{2.1}$$
这里用标准乘法，并且对**一切**点对提要求。规范版本取 $\underline{\mathbf L}(\phi):=\underline{\mathbf L}^{\mathrm{dom}\,\phi}(\phi)$，理由见命题 2.5。

**引理 2.2。**
- **(a) 比值刻画。** $\underline L^S_{ji}=\inf\{e_j\oslash d_i:\ x,y\in S,\ d_i>0\}$，约定 $\inf\varnothing=\infty$。这里对 $v<\infty$ 取 $u\oslash v=u/v$；对 $v=\infty$，$\infty\oslash\infty=\infty$，而 $u<\infty$ 时 $u\oslash\infty=0$。
- **(b) 可达。** (2.1) 的可行集恰为 $[0,\underline L^S_{ji}]$，所以上确界总能取到（包括值为 $\infty$ 时）。
- **(c) 单调。** $S'\subseteq S\Rightarrow\underline{\mathbf L}^{S'}\ge\underline{\mathbf L}^S$。
- **(d) 极端值。** $\underline L=\infty$ 当且仅当 $S$ 中 $d_i>0$ 的点对都有 $e_j=\infty$。若 $\underline L>0$，则 $\phi$ 零反射（$e_j=0\Rightarrow d_i=0$），并且 $e_j<\infty\Rightarrow d_i<\infty$。

*证明。* 对单个点对检验"$b$ 可行 $\iff b\le e\oslash d$"：
- $d=0$：$b\cdot 0=0\le e$，恒成立；
- $0<d<\infty$：$e\ge bd\iff b\le e/d$（$b=\infty$ 时两边都等价于 $e=\infty$）；
- $d=\infty$：$b=0$ 恒可行；$b>0$ 可行当且仅当 $e=\infty$。

所以可行集是 $[0,\inf\text{比值}]$，(a)(b) 得证。(c) 显然。(d) 由 (a)(b) 直接读出。∎

**命题 2.3（唯一最优性）。** 对一切 $x,y\in S$，$\mathbf e\ge\underline{\mathbf L}^S(\phi)\boxdot\mathbf d$。满足 $\mathbf e\ge B\boxdot\mathbf d$ 的矩阵恰为 $B\le\underline{\mathbf L}^S(\phi)$，所以 $\underline{\mathbf L}^S(\phi)$ 是唯一最大的矩阵。理由是该不等式可以逐元素拆开，再用引理 2.2(b)。

**定理 2.4（复合律）。** 若 $\phi(S)\subseteq T$，则 $\underline{\mathbf L}^S(\psi\phi)\ge\underline{\mathbf L}^T(\psi)\boxdot\underline{\mathbf L}^S(\phi)$。由此得到：
- 定义域版：$\underline{\mathbf L}(\psi\phi)\ge\underline{\mathbf L}(\psi)\boxdot\underline{\mathbf L}(\phi)$；
- 迭代：$\underline{\mathbf L}(\phi^n)\ge\underline{\mathbf L}(\phi)^{\boxdot n}$。

*证明。* 记 $a=\underline L^T_{kj}(\psi)$，$b=\underline L^S_{ji}(\phi)$，两者都可达。于是
$$f_k\ge a\,e_j\ge a(b\,d_i)=(ab)\,d_i,$$
这里只用到标准乘法的单调性和结合律，不需要任何例外情形。定义域版的论证同定理 1.5。∎

**命题 2.5（吸收元与下界）。**
- **(a)** 若 $S$ 含两点 $x,y\notin\mathrm{dom}\,\phi$（可以是 $\bot$），且 $d_i(x,y)>0$，则对一切 $j$ 有 $\underline L^S_{ji}=0$。特别地，若 $\phi$ 不是全定义的，则 $\underline{\mathbf L}^{\mathcal X}(\phi)=\mathbf 0$。
- **(b)** 若 $S\subseteq\mathrm{dom}\,\phi$，则 $\underline{\mathbf L}^{S\cup\{\bot\}}=\underline{\mathbf L}^S$。

*证明。* (a) 此时 $e_j(\bot,\bot)=0$，而 $d_i>0$。若 $x\in\mathcal X^\circ\setminus\mathrm{dom}\,\phi$，取 $y=\bot$，则 $d_i(x,\bot)=\infty$。(b) 对 $x\in\mathrm{dom}\,\phi$ 有 $e_j(\phi x,\bot)=\infty$，不构成约束。∎

所以全局下界只对全定义算子有意义，下界的自然区域是有效定义域。

---

## 3 坍缩半径矩阵（"输入落入某个范围后输出不可区分"）

**定义 3.1。**

局部坍缩半径（$x\in S$）：
$$R^S_{ji}(\phi;x)=\sup\{r:\ \forall y\in S,\ d_i(x,y)<r\Rightarrow e_j(\phi x,\phi y)=0\}.$$

全局坍缩半径：
$$R^S_{ji}(\phi)=\sup\{r:\ \forall x,y\in S,\ d_i(x,y)<r\Rightarrow e_j(\phi x,\phi y)=0\}.$$

两者都在 $\bar{\mathbb R}_+$ 中取值。
- 局部半径度量 $x$ "落入坍缩区的深度"：$\phi$ 把整个 $d_i$-开球映入 $\phi(x)$ 的 $e_j$-不可区分类。
- 全局半径组成矩阵 $\mathbf R^S(\phi)$，规范版本取 $\mathbf R(\phi):=\mathbf R^{\mathcal X}(\phi)$。
- 若 $R^C_{ji}(\phi)=\infty$，称 $\phi$ 在区域 $C$ 上 $(j,i)$-坍缩。

**引理 3.2。**
- **(a)** 两个可行集都形如 $[0,R]$，所以上确界可达。
- **(b)** $R^S_{ji}(\phi)=\inf_{x\in S}R^S_{ji}(\phi;x)$。
- **(c)** $S'\subseteq S\Rightarrow\mathbf R^{S'}\ge\mathbf R^S$；并且 $\mathbf R^{S\cup\{\bot\}}=\mathbf R^S$。
- **(d)** $R^S_{ji}=\infty$ 当且仅当 $S$ 中所有 $d_i$-有限点对都被 $e_j$-坍缩，也当且仅当 $\overline L^S_{ji}=0$。

*证明。* (a) $r=0$ 时条件空真；可行集向下封闭。若 $r_n\uparrow r$ 都可行且 $d<r$，则存在 $n$ 使 $d<r_n$，所以 $r$ 可行。

(b) $r$ 全局可行当且仅当它在每个 $x$ 处局部可行，即 $r\le R(\phi;x)$ 对所有 $x$ 成立。

(c) 对 $x\neq\bot$ 有 $d_i(x,\bot)=\infty$，由于不等号是严格的，$\infty<r$ 永不成立，这类点对不进入条件。

(d) 对照命题 1.4(a)。∎

**定理 3.3（复合律）。** 设 $\phi(S)\subseteq T$。
- **(C1) 坍缩不可逆。** 若 $\psi$ 在 $T$ 上 $(k,j)$-零兼容（例如 $R^T_{kj}(\psi)>0$，或 $\overline L^T_{kj}(\psi)<\infty$），则 $R^S_{ki}(\psi\phi)\ge R^S_{ji}(\phi)$。
- **(C2) 收缩把输入送进下游坍缩区。** 若 $b=\overline L^S_{ji}(\phi)<\infty$ 且 $a=R^T_{kj}(\psi)>0$，则 $R^S_{ki}(\psi\phi)\ge a/b$，约定 $a/0=\infty$，$\infty/b=\infty$。

*证明。* (C1) 若 $d_i<R_{ji}(\phi)$，则 $e_j(\phi x,\phi y)=0$；由零兼容得 $f_k=0$。

(C2) 若 $d_i<a/b$，则 $d_i<\infty$，于是 $e_j\le b\,d_i$。当 $b>0$ 时 $b\,d_i<a$；当 $b=0$ 时 $e_j=0<a$。两种情况都有 $e_j<a$，所以 $f_k=0$。∎

**命题 3.4（连续区域上的二分性）。** 称 $S$ 是 **$d_i$-链连通**的，如果任意两点 $d_i(x,y)<\infty$ 之间，对任意 $\varepsilon>0$，都有一条落在 $S$ 内、每步 $d_i$-距离小于 $\varepsilon$ 的链。此时对一切 $\phi$ 和 $j$，有 $R^S_{ji}(\phi)\in\{0,\infty\}$。

*证明。* 若 $R>0$，取 $\varepsilon=R$ 的链。每一步的 $e_j$-距离为 $0$，由三角不等式，$e_j(\phi x,\phi y)$ 不超过各步之和，也为 $0$。∎

因此在连续区域上，有信息量的是局部半径 $R(\phi;x)$ 和区域版本 $R^C=\infty$，例如 ReLU 的饱和区（例 5.2）。有限的正全局半径出现在簇状或离散的输入上（例 5.3）。

---

## 4 三个矩阵之间的关系

记 $S$ 在 $d_i$ 下的分辨尺度为 $\sigma_i(S)=\inf\{d_i(x,y):x,y\in S,\ d_i(x,y)>0\}$，约定 $\inf\varnothing=\infty$。

**命题 4.1。** 固定 $(j,i)$ 与 $S$：
- **(a)** $\overline L=0\iff R=\infty$。
- **(b)** $R>0$ 或 $\overline L<\infty$ 都蕴含 $(j,i)$-零兼容。
- **(c)** 零兼容蕴含 $R\ge\sigma_i(S)$；$\underline L>0$ 蕴含 $R\le\sigma_i(S)$。两者同时成立时 $R=\sigma_i(S)$。也就是说，非退化的下界与超出分辨尺度的坍缩互斥。
- **(d)** 若 $S$ 中存在点对使 $0<d_i<\infty$，则 $\underline L\le\overline L$。没有这种点对时可能反向：例如 $\mathcal X^\circ=\{p,q\}$，$d(p,q)=\infty$，$\phi=\mathrm{id}$，此时 $\overline L=0$ 而 $\underline L=\infty$。
- **(e) 分量包络。** 对一切 $x,y\in S$：
$$\underline L_{ji}\,d_i\ \le\ e_j(\phi x,\phi y)\ \le\ \begin{cases}0,& d_i<R_{ji},\\ \overline L_{ji}\star d_i,&\text{否则}.\end{cases}$$

*证明。*
- (a) 即引理 3.2(d)。(b) 见命题 1.4(b) 与定理 3.3。
- (c) 若 $d_i<\sigma_i$，则 $d_i=0$，由零兼容得 $e_j=0$，所以 $\sigma_i$ 可行。若 $\underline L>0$ 而 $R>\sigma_i$，则存在 $0<d_i<R$ 的点对，于是 $e_j=0$；但由引理 2.2(d) 的零反射得 $d_i=0$，矛盾。
- (d) 对这样的点对有 $\underline L\,d\le e\le\overline L\,d$，且 $0<d<\infty$。
- (e) 由命题 1.3、2.3 和 $R$ 的可达性。∎

**命题 4.2（与 $\bot$ 和有效定义域的关系）。** 设 $x\in\mathrm{dom}\,\phi$，$y\in\mathcal X^\circ\setminus\mathrm{dom}\,\phi$。
- **(a)** $d_i(x,y)\ge R^{\mathcal X}_{ji}(\phi;x)\ge R^{\mathcal X}_{ji}(\phi)$。
- **(b)** 若存在 $j$ 使 $\overline L^{\mathcal X}_{ji}(\phi)<\infty$，则 $d_i(x,y)=\infty$。

*证明。* 由 (iv) 与 $\phi x\neq\bot$，有 $e_j(\phi x,\bot)=\infty$。(a) 中若 $d_i<R(\phi;x)$，应有 $e_j=0$，矛盾。(b) 中 $(x,y)$ 是有限距离点对，而 $\infty\le a\,d_i$ 对有限 $a$ 不成立。∎

含义：全局矩阵把"跳到未定义"计为无穷扩张，这与 $\bot$ 的隔离公理一致。对于定义域边界离定义点有限远的偏算子，应使用定义域版本，它同样有复合律（定理 1.5 第 2 条）。

**取值含义一览：**

| | 值为 $0$ | 值为 $\infty$ |
|---|---|---|
| $\overline L_{ji}$ | $S$ 中 $d_i$-有限点对全部被 $e_j$-坍缩 | 没有有限斜率界（无约束） |
| $\underline L_{ji}$ | 没有下界信息 | $d_i$-可区分的点对被推到 $e_j$-无穷远 |
| $R_{ji}$ | 没有一致的坍缩尺度 | 与 $\overline L_{ji}=0$ 等价 |

---

## 5 例子

**例 5.1（对角伸缩）。** $\mathcal X=\mathbb R^2\cup\{\bot\}$，$d_i(x,y)=|x_i-y_i|$。整个族分离，但单个 $d_i$ 不分离。取 $\phi(x)=(x_1,2x_2)$，则
$$\overline{\mathbf L}=\begin{pmatrix}1&\infty\\\infty&2\end{pmatrix},\qquad \underline{\mathbf L}=\begin{pmatrix}1&0\\0&2\end{pmatrix},\qquad \mathbf R=\mathbf 0 .$$
非对角的 $\infty$ 来自非零兼容：只改动另一个坐标时 $d_i=0$ 而 $e_j>0$。单一常数（$d_{\max}\to e_{\max}$）为 $2$，而矩阵还显示第 1 分量是等距的。

**例 5.2（ReLU）。** $\mathcal X=\mathbb R\cup\{\bot\}$，$\phi(x)=\max(x,0)$。
- $\overline L=1$；$\underline L^{\mathrm{dom}}=0$，但 $\underline L^{[0,\infty)}=1$。
- 全局 $R=0$，局部 $R(\phi;x)=\max(-x,0)$。
- $R^{(-\infty,0]}=\infty$：饱和区被整体坍缩。这与命题 3.4 一致。

**例 5.3（簇上的量化）。** $\mathcal X^\circ=[0,1]\cup[3,4]$，$d=|\cdot|$；$\phi$ 在 $[0,1]$ 上取 $0$，在 $[3,4]$ 上取 $1$。
- $R=2$，即两簇之间的间隙。
- 局部半径：$x\in[0,1]$ 时为 $3-x$，$x\in[3,4]$ 时为 $x-1$，下确界为 $2$。
- $\overline L=\tfrac12$，在点对 $(1,3)$ 处取到；$\underline L=0$。
- 包络给出 $e\le\tfrac12\,d\cdot\mathbf 1[d\ge2]$。直观上，输入落在同一簇里（距离小于 $2$）时，输出不可区分。

---

## 6 小结

- **三个矩阵。** 对每个算子 $\phi$ 和每对分量 $(j,i)$，定义三个 $\bar{\mathbb R}_+$ 值的最优常数，组成 $J\times I$ 矩阵 $\overline{\mathbf L}$、$\underline{\mathbf L}$、$\mathbf R$。它们无需任何存在性前提，最优值总能取到（$\overline{\mathbf L}$ 在有限时可达）。
- **矩阵不等式。** 上、下界分别是 $(\min,\star)$ 与 $(\max,\cdot)$ 半环中唯一最优的矩阵界：$\mathbf e\le\overline{\mathbf L}\boxtimes\mathbf d$，$\mathbf e\ge\underline{\mathbf L}\boxdot\mathbf d$。
- **复合律。** $\overline{\mathbf L}$ 在复合下次乘，$\underline{\mathbf L}$ 超乘。$\mathbf R$ 由"坍缩不可逆"（C1）和"收缩把输入送进坍缩区"（C2）两条规律控制。
- **两种 $\infty$ 约定的必要性。** 上界必须用 $0\star\infty=\infty$，否则复合律失效（定理 1.5 后的反例）；下界沿用题设的 $0\cdot\infty=0$。
- **零兼容。** 由于不预设族分离，"$d_i$-不可区分蕴含 $e_j$-不可区分"是有限上界和正坍缩半径的共同前提，也把三个矩阵联系在一起。