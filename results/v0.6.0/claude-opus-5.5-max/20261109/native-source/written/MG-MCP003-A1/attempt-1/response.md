# 扩展规范空间上算子的 Lipschitz 矩阵、下界矩阵与不可区分矩阵

## 总览

- **上界矩阵 $\overline L$**：第 $(i,j)$ 项是"输出第 $i$ 分量被输入第 $j$ 分量控制"的最优倍数。
- **下界矩阵 $\underline L$**：第 $(i,j)$ 项是对应的最优下界倍数。
- **不可区分半径矩阵 $K$**：第 $(i,j)$ 项是最大的半径 $r$，使得"输入的 $d_j$ 距离小于 $r$"时输出在 $d_i$ 下不可区分。

三个矩阵的每一项都取值于 $\bar{\mathbb R}_+$，所以每个算子都有这三个矩阵；最优值都能取到。三者都是同一个"控制系数" $\Lambda$ 的特例。在倒数形式下，$+\infty$ 和 $0$ 都与约定 $0\cdot\infty=0$ 相容。$K$ 恰好是 $\phi$ 相对于"可区分性规范"的上 Lipschitz 矩阵的逐项倒数；这就是它与 Lip 矩阵"对等"的精确含义（定理 4.3）。

---

## 0. 记号与约定

下文固定 $(\mathcal X,\mathcal G,\bot)$，$\mathcal G=\{d_i\}_{i\in I}$。在 $\bar{\mathbb R}_+$ 中约定 $\inf\emptyset=+\infty$，$\sup\emptyset=0$。

**$\bar{\mathbb R}_+$ 运算的三个事实**（按约定逐情形验证即可）：

- **(F1)** 乘法交换、结合。若某个因子为 $0$，两边都是 $0$；否则积为 $\infty$ 当且仅当某个因子为 $\infty$，其余情形是通常乘积。
- **(F2)** 乘法单调：$a\le b\Rightarrow ca\le cb$。
  - $c=\infty$ 时，映射 $t\mapsto\infty\cdot t$ 在 $t=0$ 取 $0$，在 $t>0$ 取 $\infty$，仍非降。
  - 因而 $c\max(a,b)=\max(ca,cb)$。
- **(F3)** 当 $c\in(0,\infty)$ 时，$t\mapsto ct$ 是 $\bar{\mathbb R}_+$ 的保序双射，逆映射为 $t\mapsto c^{-1}t$。

**倒数与上乘积。**
- 倒数：$0^{-1}:=+\infty$，$(+\infty)^{-1}:=0$，其余 $a^{-1}=1/a$。
  - 它是反序对合：$a\le b\iff b^{-1}\le a^{-1}$，且 $(a^{-1})^{-1}=a$。因此它把 $\inf$ 变成 $\sup$，把 $\min$ 变成 $\max$。
  - $(ab)^{-1}=a^{-1}b^{-1}$ 恒成立，唯一例外是 $\{a,b\}=\{0,\infty\}$。
- 上乘积：定义 $a\star b:=(a^{-1}b^{-1})^{-1}$。
  - 它满足 $a\star b=ab$，唯一例外是 $0\star\infty=\infty\star 0=+\infty$。
  - 这是新引入的运算，**不改变**全文约定 $0\cdot\infty=0$。
  - $\star$ 交换、结合，并且对每个变元单调不减。

**测试集、拉回与可区分性。**
- 对 $\phi\in\mathcal X_{\rm op}$ 取测试集 $A\subseteq\operatorname{dom}\phi$；缺省 $A=\operatorname{dom}\phi$，此时省略 $A$。
- 对 $\rho:\mathcal X^2\to\bar{\mathbb R}_+$，记拉回 $\phi^*\rho(x,y):=\rho(\phi x,\phi y)$。
- 记 $\sigma(0)=0$，$\sigma(a)=1$（$a>0$），并令 $\delta_i:=\sigma\circ d_i$。

**引理 0.1.** $\delta_i$ 满足 (i)(ii)(iii)，即它是取值于 $\{0,1\}$ 的伪度量（"$i$-可区分性"），并且 $\delta_i(x,y)=0\iff d_i(x,y)=0$。

*证.* (i)(ii) 显然。对 (iii)：若 $\delta_i(x,z)=1$，则 $d_i(x,z)>0$；由三角不等式，$d_i(x,y)$ 与 $d_i(y,z)$ 至少一个为正，所以右边 $\ge 1$。∎

**注 0.2（为何限制在定义域内）。** 若 $x\in\operatorname{dom}\phi$、$y\notin\operatorname{dom}\phi$，则由 (iv)，对一切 $i$ 有 $\phi^*d_i(x,y)=d_i(\phi x,\bot)=\infty$。如果把这种跨越定义域边界的对计入，"未定义"会和"无界伸长"混为一谈，所以只在 $A\subseteq\operatorname{dom}\phi$ 上考虑点对。"输入落入某个范围"的局部化也用 $A$ 来表达。

---

## 1. 基本工具：控制系数

**定义 1.1.** 设 $P$ 为集合，$f,g:P\to\bar{\mathbb R}_+$。令

$$
S_P(f|g):=\{\lambda\in\bar{\mathbb R}_+:\lambda f(p)\le g(p)\ \forall p\in P\},\qquad
\Lambda_P(f|g):=\sup S_P(f|g).
$$

对单点情形，记 $q(a,b):=\Lambda_{\{*\}}(a|b)$，取值如下：

| $a=f(*)$ | $b=g(*)$ | $q(a,b)$ |
|---|---|---|
| $0$ | 任意 | $\infty$ |
| $0<a<\infty$ | 任意 | $b/a$（$b=\infty$ 时为 $\infty$） |
| $\infty$ | $\infty$ | $\infty$ |
| $\infty$ | $b<\infty$ | $0$ |

**引理 1.2.**
- (a) $S_P(f|g)=[0,\Lambda_P(f|g)]$。特别地，上确界可以取到，且 $0\in S_P(f|g)$。
- (b) $\Lambda_P(f|g)=\inf_{p\in P}q(f(p),g(p))$。
- (c) 单调性：若 $f\le f'$、$g'\le g$（逐点），且 $P'\subseteq P$，则 $\Lambda_{P'}(f|g)\ge\Lambda_P(f'|g')$。
- (d) 链式法则：$\Lambda_P(f|h)\ge\Lambda_P(f|g)\cdot\Lambda_P(g|h)$。
- (e) 对有限族 $f_1,\dots,f_m$：$\Lambda_P(\max_l f_l\,|\,g)=\min_l\Lambda_P(f_l|g)$。

*证.*
- **单点情形。** 记 $a=f(*)$，$b=g(*)$。
  - 若 $a=0$：对一切 $\lambda$ 有 $\lambda a=0\le b$，所以 $S=[0,\infty]$。
  - 若 $0<a<\infty$：由 (F3)，$\lambda a\le b\iff\lambda\le b/a$；$\lambda=\infty$ 的情形同样成立。所以 $S=[0,b/a]$。
  - 若 $a=\infty$：$\lambda=0$ 总可容许；$\lambda>0$ 时 $\lambda a=\infty$，可容许当且仅当 $b=\infty$。所以 $S=[0,\infty]$ 或 $S=[0,0]$。
  - 三种情形都有 $S=[0,q(a,b)]$。
- **一般情形，即 (a)(b)。** $S_P=\bigcap_p[0,q_p]=[0,\inf_p q_p]$；$P=\emptyset$ 时为 $[0,\infty]$，与 $\inf\emptyset=\infty$ 一致。
- **(c)** 若 $\lambda\in S_P(f'|g')$，则对 $p\in P'$，由 (F2) 有 $\lambda f(p)\le\lambda f'(p)\le g'(p)\le g(p)$。
- **(d)** 记 $\alpha=\Lambda(f|g)$，$\beta=\Lambda(g|h)$。由 (a)，$\alpha f\le g$ 且 $\beta g\le h$。由 (F1)(F2)，$(\alpha\beta)f=\beta(\alpha f)\le\beta g\le h$。
- **(e)** 由 (F2)，$\lambda\max_l f_l=\max_l\lambda f_l$，所以 $S(\max_l f_l|g)=\bigcap_l S(f_l|g)$。∎

下文总取 $P=A\times A$，并把 $\Lambda_{A\times A}$ 记作 $\Lambda_A$。

---

## 2. 上 Lipschitz 矩阵

**定义 2.1.** 对 $i,j\in I$，令

$$
\overline L_{ij}(\phi;A):=\inf\Bigl\{c\in[0,\infty):\ d_i(\phi x,\phi y)\le c\,d_j(x,y)\ \ \forall x,y\in A,\ d_j(x,y)<\infty\Bigr\}.
$$

$\overline L(\phi;A):=(\overline L_{ij})\in\bar{\mathbb R}_+^{I\times I}$ 称为**上 Lipschitz 矩阵**。$\overline L_{ij}=+\infty$ 正是"没有（有限的）Lip 常数"的统一编码。

**命题 2.2（统一表达与可达性）.**
- (a) $\overline L_{ij}(\phi;A)=\Lambda_A(\phi^*d_i\,|\,d_j)^{-1}$。
- (b) **倒数形式的统一不等式**：对一切 $x,y\in A$，
  $$\overline L_{ij}^{-1}\,d_i(\phi x,\phi y)\le d_j(x,y),$$
  并且 $\overline L_{ij}$ 是使上式对一切 $x,y\in A$ 成立的最小 $L\in\bar{\mathbb R}_+$。因此任何算子的上界矩阵都存在，最优值都能取到。
- (c) 若 $\overline L_{ij}<\infty$，则下确界可达：凡 $x,y\in A$ 且 $d_j(x,y)<\infty$，都有 $d_i(\phi x,\phi y)\le\overline L_{ij}\,d_j(x,y)$。
- (d) 显式公式：$\overline L_{ij}=\sup_{x,y\in A}\dfrac{d_i(\phi x,\phi y)}{d_j(x,y)}$。这里的商 $a/b:=q(a,b)^{-1}$，即：
  - $0/b=0$（包括 $0/0=0$）；
  - $a/0=\infty$（$a>0$）；
  - $a/\infty=0$（包括 $\infty/\infty=0$）；
  - $\infty/b=\infty$（$b<\infty$）；
  - 其余为通常的商。
- (e) 极端值：
  - $\overline L_{ij}=0$ 当且仅当：凡 $x,y\in A$ 且 $d_j(x,y)<\infty$，都有 $d_i(\phi x,\phi y)=0$。
  - $\overline L_{ij}=\infty$ 当且仅当 (d) 中的商无界。例如存在一对点使 $d_j=0<d_i(\phi x,\phi y)$，或使 $d_j<\infty=d_i(\phi x,\phi y)$。

*证.*
- **(a)** 令 $\lambda^*=\Lambda_A(\phi^*d_i|d_j)$，$C$ 为定义 2.1 中可容许常数的集合。对一对点，记 $a=d_i(\phi x,\phi y)$，$b=d_j(x,y)$。先证：对 $c\in[0,\infty)$，$c\in C\iff c^{-1}\in S_A(\phi^*d_i|d_j)$。
  - $c\in(0,\infty)$：当 $b<\infty$ 时，由 (F3)，$a\le cb\iff c^{-1}a\le b$；当 $b=\infty$ 时，$c^{-1}a\le b$ 自动成立，而 $C$ 对这类对本来没有要求。
  - $c=0$：$0\in C$ 等价于"凡 $b<\infty$ 必有 $a=0$"，也就是"每一对都有 $a=0$ 或 $b=\infty$"，也就是"每一对都有 $\infty\cdot a\le b$"，即 $\infty=0^{-1}\in S$。
  - 由引理 1.2(a)，$S=[0,\lambda^*]$。所以 $C=\{c<\infty: c\ge(\lambda^*)^{-1}\}$。若 $(\lambda^*)^{-1}<\infty$，$C$ 的下确界 $(\lambda^*)^{-1}$ 可达；否则 $C=\emptyset$，$\inf C=\infty$。两种情形都有 $\overline L_{ij}=(\lambda^*)^{-1}$。
- **(b)** $\overline L_{ij}^{-1}=\lambda^*\in S$；并且 $L^{-1}\in S\iff L^{-1}\le\lambda^*\iff L\ge\overline L_{ij}$。
- **(c)** 由 (a) 的证明，$\overline L_{ij}\in C$。
- **(d)** 由引理 1.2(b)，$\overline L_{ij}=(\inf q)^{-1}=\sup q^{-1}$；逐情形计算 $q^{-1}$ 即得所列约定。
- **(e)** 由 (c) 与 (d) 直接得到。∎

**注 2.3（$\infty$ 的两种读法）.**
1. **为何排除 $d_j=\infty$ 的对。** 若定义 2.1 也要求这类对满足 $d_i(\phi x,\phi y)\le c\cdot\infty$，对 $c>0$ 毫无影响，只改变 $c=0$ 是否可容许。因为 $C$ 是上集，下确界的数值不变，但在 $0$ 处可能不再可达。
   - 例：$A=\{x,y\}$，$d_j(x,y)=\infty$，$0<d_i(\phi x,\phi y)$。此时一切 $c>0$ 可容许，而 $c=0$ 不可容许。
   - 排除这类对，正好保证了可达性。
2. **"代入 $c=+\infty$"不是空话。** 把 $c=+\infty$ 代入乘法形式 $d_i(\phi x,\phi y)\le(+\infty)\cdot d_j(x,y)$ 时，由于 $\infty\cdot0=0$，它恰好等价于"$d_j(x,y)=0\Rightarrow d_i(\phi x,\phi y)=0$"。在不预设族分离性时，这是一个实质条件。
   - 所以我们让 $\overline L_{ij}=\infty$ 只表示"没有有限常数"；此时倒数形式 $0\cdot d_i\le d_j$ 是空话。
   - "零距离是否被保持"这一定性信息交给第 4 节处理。

**注 2.4（为何逐项定义）.** 若用"$d_i(\phi x,\phi y)\le\sum_j M_{ij}d_j(x,y)$"来定义可容许矩阵 $M$，则可容许集对逐项取 $\min$ 不封闭，没有典范的最优矩阵。
- 例：在 $\mathbb R$ 上取 $d_1=d_2=|x-y|$，$\phi=\mathrm{id}$。第一行 $(1,0)$ 与 $(0,1)$ 都可容许，但逐项最小 $(0,0)$ 不可容许。
- 逐项定义下，每一项都是独立的最优常数，因而是典范的；它们合起来给出 $d_i(\phi x,\phi y)\le\min_j\overline L_{ij}d_j(x,y)$（在 2.2(c) 的条件下）。

---

## 3. 下 Lipschitz 矩阵

**定义 3.1.**

$$
\underline L_{ij}(\phi;A):=\sup\{c\in\bar{\mathbb R}_+:\ c\,d_j(x,y)\le d_i(\phi x,\phi y)\ \forall x,y\in A\}=\Lambda_A(d_j\,|\,\phi^*d_i).
$$

这里约束对所有点对生效，包括 $d_j=\infty$ 的对。

**命题 3.2.**
- (a) 上确界可达：对一切 $x,y\in A$，$\underline L_{ij}\,d_j(x,y)\le d_i(\phi x,\phi y)$；可容许集是 $[0,\underline L_{ij}]$，其中 $0$ 是总成立的平凡下界。
- (b) 公式：$\underline L_{ij}=\inf_{x,y\in A}q\bigl(d_j(x,y),\,d_i(\phi x,\phi y)\bigr)$。也就是说：
  - $d_j=0$ 的对不施加约束；
  - $0<d_j<\infty$ 的对贡献比值 $d_i(\phi x,\phi y)/d_j(x,y)$；
  - $d_j=\infty$ 的对，当 $d_i(\phi x,\phi y)=\infty$ 时贡献 $\infty$，否则贡献 $0$。
- (c) 含义：
  - 若 $\underline L_{ij}>0$，则 $d_j(x,y)>0\Rightarrow d_i(\phi x,\phi y)>0$（$j$-可区分的输入在 $i$ 中仍可区分），并且 $d_j=\infty\Rightarrow d_i(\phi x,\phi y)=\infty$。
  - $\underline L_{ij}=\infty$ 当且仅当 $d_j(x,y)>0\Rightarrow d_i(\phi x,\phi y)=\infty$。

*证.* (a)(b) 即引理 1.2(a)(b)。(c) 的第一条：若 $c>0$，则 $b>0\Rightarrow cb>0$，且 $b=\infty\Rightarrow cb=\infty$。第二条：$\infty\in S$ 等价于每一对都有 $\infty\cdot b\le a$。∎

**命题 3.3（上下界相容）.** 若存在 $x_0,y_0\in A$ 使 $0<d_j(x_0,y_0)<\infty$，则 $\underline L_{ij}\le\overline L_{ij}$。这一假设不可去掉：当 $A$ 为单点时，$\overline L_{ij}=0$ 而 $\underline L_{ij}=\infty$。

*证.* 不妨设 $\overline L_{ij}<\infty$。记 $b=d_j(x_0,y_0)$，由 3.2(a) 与 2.2(c)，$\underline L_{ij}\,b\le d_i(\phi x_0,\phi y_0)\le\overline L_{ij}\,b$；由 (F3) 两边除以 $b$。∎

**命题 3.4（对偶）.** 设 $\phi|_A$ 是单射，$\chi\in\mathcal X_{\rm op}$ 满足 $\chi(\phi x)=x$（$x\in A$）。这样的 $\chi$ 存在：在 $\phi(A)$ 上按此定义，其余处取 $\bot$；因为 $\bot\notin\phi(A)$，有 $\chi(\bot)=\bot$。于是 $\phi(A)\subseteq\operatorname{dom}\chi$，并且

$$
\underline L_{ij}(\phi;A)=\overline L_{ji}(\chi;\phi(A))^{-1}.
$$

特别地，$\underline L(\mathrm{id};A)$ 等于 $\overline L(\mathrm{id};A)^{\top}$ 的逐项倒数：下界矩阵就是逆算子上界矩阵的转置倒数。

*证.* $\overline L_{ji}(\chi;\phi(A))^{-1}=\Lambda_{\phi(A)}(\chi^*d_j\,|\,d_i)$。映射 $(x,y)\mapsto(\phi x,\phi y)$ 是 $A^2\to\phi(A)^2$ 的双射，且 $\chi^*d_j(\phi x,\phi y)=d_j(x,y)$，所以两个可容许集相同，结果等于 $\Lambda_A(d_j\,|\,\phi^*d_i)$。∎

---

## 4. 不可区分半径矩阵

**定义 4.1.** 对 $r\in\bar{\mathbb R}_+$，若

$$
\forall x,y\in A:\quad d_j(x,y)<r\ \Longrightarrow\ d_i(\phi x,\phi y)=0,
$$

则称 $\phi$ 在 $A$ 上 **$(i\leftarrow j)$ 于尺度 $r$ 坍缩**：输入在第 $j$ 分量落入半径 $r$ 以内时，输出在第 $i$ 分量不可区分。

定义**不可区分半径** $\kappa_{ij}(\phi;A):=\sup\{r\in\bar{\mathbb R}_+:\phi\text{ 于尺度 }r\text{ 坍缩}\}$，矩阵 $K(\phi;A):=(\kappa_{ij})$。

**定义 4.2（零尺度保持）.** 若对一切 $x,y\in A$ 有 $d_j(x,y)=0\Rightarrow d_i(\phi x,\phi y)=0$，记作 $Z_{ij}(\phi;A)$。这给出一个布尔矩阵 $Z(\phi;A)$。

**定理 4.3（对等定理）.**
- (a) $\kappa_{ij}(\phi;A)=\Lambda_A(\phi^*\delta_i\,|\,d_j)$。等价地，
  $$\kappa_{ij}(\phi;A)^{-1}=\overline L^{\delta}_{ij}(\phi;A),$$
  其中 $\overline L^{\delta}$ 是把定义 2.1 中的输出规范 $d_i$ 换成可区分性伪度量 $\delta_i$ 后得到的上 Lipschitz 矩阵。命题 2.2 的证明只用到取值于 $\bar{\mathbb R}_+$，所以对 $\delta_i$ 照样成立。换言之，**不可区分矩阵就是 $\phi$ 关于可区分性规范 $\{\delta_i\}$ 的上 Lipschitz 矩阵的逐项倒数**。
- (b) 上确界可达：$\phi$ 于尺度 $\kappa_{ij}$ 坍缩，可容许尺度集是 $[0,\kappa_{ij}]$。
- (c) 公式：$\kappa_{ij}(\phi;A)=\inf\{d_j(x,y):x,y\in A,\ d_i(\phi x,\phi y)>0\}$。
- (d) 含义：
  - $\kappa_{ij}=\infty$ 当且仅当：凡 $d_j(x,y)<\infty$，都有 $d_i(\phi x,\phi y)=0$。
  - $\kappa_{ij}>0\Rightarrow Z_{ij}$。
  - $\kappa_{ij}=0$ 当且仅当：存在输出 $i$-可区分的点对，其输入 $d_j$ 距离可以任意小（可以为 $0$）。
- (e) 以下三者等价：$Z_{ij}(\phi;A)$；$\Lambda_A(\phi^*\delta_i|\delta_j)\ge1$；$\Lambda_A(\phi^*\delta_i|\delta_j)>0$。它们也等价于：乘法形式 $d_i(\phi x,\phi y)\le(+\infty)\cdot d_j(x,y)$ 对一切 $x,y\in A$ 成立。

*证.*
- **(a)(b)** 对一对点：若 $\delta_i(\phi x,\phi y)=0$，条件 $r\cdot 0\le d_j$ 恒成立；若 $\delta_i(\phi x,\phi y)=1$，条件是 $r\le d_j(x,y)$。所以
  $$r\in S_A(\phi^*\delta_i|d_j)\iff \bigl(d_i(\phi x,\phi y)>0\Rightarrow d_j(x,y)\ge r\bigr)\iff\phi\text{ 于尺度 }r\text{ 坍缩}.$$
  再用引理 1.2(a) 与命题 2.2(a)。
- **(c)** 由 (a) 的刻画，$S=\{r: r\le d_j(x,y)\ \text{对所有输出可区分的对}\}$，其上确界就是该下确界。
- **(d)** 由 (c) 直接得到；对第二条，$d_j=0<\kappa$ 意味着该对必坍缩。
- **(e)** 条件 $\lambda\,\delta_i(\phi x,\phi y)\le\delta_j(x,y)$ 只对 $\delta_i(\phi x,\phi y)=1$ 的对有约束，约束为 $\lambda\le\delta_j(x,y)\in\{0,1\}$。所以 $\Lambda\in\{0,1,\infty\}$，且 $\Lambda\ge1\iff\Lambda>0$ 当且仅当不存在"$\delta_i(\phi x,\phi y)=1$ 而 $\delta_j(x,y)=0$"的对。最后一条：$b>0$ 时 $(+\infty)\cdot b=\infty$；$b=0$ 时条件变为 $a=0$。∎

**命题 4.4（三个矩阵之间的关系）.**
- (a) $\kappa_{ij}=\infty\iff\overline L_{ij}=0$。
- (b) $\overline L_{ij}<\infty\Rightarrow Z_{ij}$；$\kappa_{ij}>0\Rightarrow Z_{ij}$。
- (c) 记 $g_j(A):=\inf\{d_j(x,y):x,y\in A,\ d_j(x,y)>0\}$，即 $A$ 在 $d_j$ 下的分辨率。
  - 若 $\underline L_{ij}>0$，则 $\kappa_{ij}\le g_j(A)$；若再有 $Z_{ij}$，则 $\kappa_{ij}=g_j(A)$。
  - 特别地，若 $\kappa_{ij}>0$ 且 $\underline L_{ij}>0$，则 $A$ 中没有满足 $0<d_j(x,y)<\kappa_{ij}$ 的点对。直观地说：有正下界的算子只能在输入本身分辨不出的尺度以下坍缩。
- (d) **区域形式**："输入落入同一区域 $A$ 则输出不可区分"。若 $D_j:=\sup_{x,y\in A}d_j(x,y)<\infty$，下列四条等价：
  1. 对一切 $x,y\in A$，$d_i(\phi x,\phi y)=0$；
  2. $\kappa_{ij}(\phi;A)=\infty$；
  3. $\kappa_{ij}(\phi;A)>D_j$；
  4. $\overline L_{ij}(\phi;A)=0$。

*证.*
- **(a)** 由 2.2(e) 与 4.3(d)，两边都等价于"$d_j<\infty\Rightarrow d_i(\phi x,\phi y)=0$"。
- **(b)** 由 2.2(c)，$d_j=0$ 时 $d_i(\phi x,\phi y)\le\overline L_{ij}\cdot0=0$；第二条见 4.3(d)。
- **(c)** 由 3.2(c)，作为 $A^2$ 的子集有 $\{d_j>0\}\subseteq\{\phi^*d_i>0\}$。在更小的指标集上取下确界，由 4.3(c) 得 $\kappa_{ij}\le g_j(A)$。$Z_{ij}$ 给出反向包含，所以两集合相等，从而等号成立。若存在 $0<d_j(x,y)<\kappa_{ij}$，则 $g_j(A)\le d_j(x,y)<\kappa_{ij}\le g_j(A)$，矛盾。
- **(d)**
  - 1⇒2：4.3(c) 中的集合为空。
  - 2⇒3：因为 $D_j<\infty$。
  - 3⇒1：若有一对满足 $d_i(\phi x,\phi y)>0$，则 $\kappa_{ij}\le d_j(x,y)\le D_j$，矛盾。
  - 2⇔4：即 (a)。∎

---

## 5. 单调性与复合律

**定理 5.1（对测试集的单调性）.** 若 $B\subseteq A\subseteq\operatorname{dom}\phi$，则逐项有
- $\overline L(\phi;B)\le\overline L(\phi;A)$；
- $\underline L(\phi;B)\ge\underline L(\phi;A)$；
- $K(\phi;B)\ge K(\phi;A)$；
- $Z_{ij}(\phi;A)\Rightarrow Z_{ij}(\phi;B)$。

*证.* 由引理 1.2(c)（取 $B^2\subseteq A^2$），再用倒数的反序性。∎

**引理 5.2.** 若 $\phi,\psi\in\mathcal X_{\rm op}$，则 $\psi\circ\phi\in\mathcal X_{\rm op}$，且 $\operatorname{dom}(\psi\circ\phi)=\{x\in\operatorname{dom}\phi:\phi x\in\operatorname{dom}\psi\}$。

*证.* $\psi\phi(\bot)=\psi(\bot)=\bot$。若 $\psi(\phi x)\ne\bot$，则 $\phi x\ne\bot$（否则 $\psi(\phi x)=\psi(\bot)=\bot$），所以 $x\in\operatorname{dom}\phi$ 且 $\phi x\in\operatorname{dom}\psi$。反方向是显然的。∎

**定理 5.3（复合律）.** 设 $A\subseteq\operatorname{dom}(\psi\circ\phi)$，$B:=\phi(A)$；由引理 5.2，$B\subseteq\operatorname{dom}\psi$。对一切 $i,j,k$：
- (a) $\overline L_{ik}(\psi\phi;A)\le\overline L_{ij}(\psi;B)\star\overline L_{jk}(\phi;A)$；
- (b) $\underline L_{ik}(\psi\phi;A)\ge\underline L_{ij}(\psi;B)\cdot\underline L_{jk}(\phi;A)$；
- (c) $\kappa_{ik}(\psi\phi;A)\ge\kappa_{ij}(\psi;B)\cdot\overline L_{jk}(\phi;A)^{-1}$；
- (d) 若 $Z_{ij}(\psi;B)$，则 $\kappa_{ik}(\psi\phi;A)\ge\kappa_{jk}(\phi;A)$；并且 $Z_{ij}(\psi;B)\wedge Z_{jk}(\phi;A)\Rightarrow Z_{ik}(\psi\phi;A)$。

**矩阵形式。** 取 $A=\operatorname{dom}(\psi\phi)$，用定理 5.1 与 $\star$、乘法的单调性，再对 $j$ 取最优，得到

$$
\overline L(\psi\phi)\le\overline L(\psi)\circledast\overline L(\phi),\qquad
\underline L(\psi\phi)\ge\underline L(\psi)\odot\underline L(\phi),\qquad
K(\psi\phi)\ge K(\psi)\odot\overline L(\phi)^{\langle-1\rangle},
$$

其中：
- $(P\circledast Q)_{ik}=\min_j P_{ij}\star Q_{jk}$；
- $(P\odot Q)_{ik}=\max_j P_{ij}Q_{jk}$，用标准约定 $0\cdot\infty=0$；
- $\langle-1\rangle$ 表示逐项取倒数。

*证.*
- **(a)** 令 $\alpha=\Lambda_B(\psi^*d_i|d_j)$，$\beta=\Lambda_A(\phi^*d_j|d_k)$。对 $x,y\in A$，有 $(\phi x,\phi y)\in B^2$，所以 $\alpha\,d_i(\psi\phi x,\psi\phi y)\le d_j(\phi x,\phi y)$，即 $\alpha\in S_A\bigl((\psi\phi)^*d_i\,|\,\phi^*d_j\bigr)$。由链式法则 1.2(d)，$\Lambda_A((\psi\phi)^*d_i|d_k)\ge\alpha\beta$。取倒数得
  $$\overline L_{ik}(\psi\phi;A)\le(\alpha\beta)^{-1}=\overline L_{ij}\star\overline L_{jk}.$$
- **(b)** 令 $\gamma=\underline L_{jk}(\phi;A)$，$\eta=\underline L_{ij}(\psi;B)$。在 $A^2$ 上有 $\gamma\,d_k\le\phi^*d_j$ 与 $\eta\,\phi^*d_j\le(\psi\phi)^*d_i$，用链式法则即得。
- **(c)** 由 $\kappa_{ij}(\psi;B)=\Lambda_B(\psi^*\delta_i|d_j)$，在 $A^2$ 上有 $\kappa_{ij}(\psi;B)\,(\psi\phi)^*\delta_i\le\phi^*d_j$；再与 $\beta$ 用链式法则。
- **(d)** 若 $d_k(x,y)<\kappa_{jk}(\phi;A)$，由 4.3(b) 得 $d_j(\phi x,\phi y)=0$，再由 $Z_{ij}(\psi;B)$ 得 $d_i(\psi\phi x,\psi\phi y)=0$。$Z$ 的传递同理。∎

**注 5.4.**
1. **$\star$ 不能换成普通乘积。** 二者只在 $\{0,\infty\}$ 处不同。例 7.2 中，$\overline L_{12}(\mathrm{id})=\infty$，$\overline L_{21}(\pi)=0$，但 $\overline L_{11}(\mathrm{id}\circ\pi)=1$；若用 $\infty\cdot 0=0$，会错误地推出 $\overline L_{11}\le 0$。根源就是注 2.3(2)：$\overline L=\infty$ 不保证零距离被保持。
2. **补上零尺度信息即可改进。** 若 $\overline L_{jk}(\phi;A)=0$ 且 $Z_{ij}(\psi;B)$，则 $\overline L_{ik}(\psi\phi;A)=0$。证明：依次用 4.4(a)、5.3(d)、4.4(a)。由此可见，不可区分结构（$K$ 与 $Z$）与 Lipschitz 矩阵在复合中互相补全。
3. **迭代。** 令 $P^{\circledast1}=P$，$P^{\circledast n}=P\circledast P^{\circledast(n-1)}$（$\odot$ 的幂同样定义）。由于 $\operatorname{dom}\phi^n\subseteq\operatorname{dom}\phi^{n-1}$，用定理 5.1 与 $\circledast$ 的单调性归纳，得到 $\overline L(\phi^n)\le\overline L(\phi)^{\circledast n}$ 与 $\underline L(\phi^n)\ge\underline L(\phi)^{\odot n}$。

---

## 6. 与单一 Lipschitz 常数的关系

令 $d_{\max}:=\max_i d_i$，它满足 (i)–(iv)。定义标量常数（即 $|I|=1$ 时的定义 2.1 与 3.1）：
- $\overline L^{\max}(\phi;A):=\Lambda_A(\phi^*d_{\max}|d_{\max})^{-1}$；
- $\underline L^{\max}(\phi;A):=\Lambda_A(d_{\max}|\phi^*d_{\max})$。

**命题 6.1.**

$$
\overline L^{\max}\le\max_i\min_j\overline L_{ij},\qquad
\underline L^{\max}\ge\min_j\max_i\underline L_{ij}.
$$

*证.*
- **上界。** 由 1.2(e)，$\Lambda(\phi^*d_{\max}|d_{\max})=\min_i\Lambda(\phi^*d_i|d_{\max})$；由 1.2(c) 与 $d_j\le d_{\max}$，它 $\ge\min_i\max_j\Lambda(\phi^*d_i|d_j)$。取倒数（反序，并交换 $\min$ 与 $\max$）即得第一式。
- **下界。** 令 $c=\min_j\max_i\underline L_{ij}$。由 (F2)，对每个 $j$ 有 $c\,d_j\le\max_i\underline L_{ij}d_j\le\max_i\phi^*d_i=\phi^*d_{\max}$。所以 $c\,d_{\max}=\max_j c\,d_j\le\phi^*d_{\max}$。∎

因此单一 Lip 常数只是矩阵的粗略概括；例 7.2 说明矩阵严格包含更多信息。

---

## 7. 例子

**构造。** 设 $\{\rho_i\}$ 是集合 $Y$ 上的伪度量族。令 $\mathcal X=Y\sqcup\{\bot\}$，并规定 $d_i|_{Y^2}=\rho_i$，$d_i(y,\bot)=d_i(\bot,y)=\infty$（$y\in Y$），$d_i(\bot,\bot)=0$。则 (i)–(iv) 成立：任何涉及 $\bot$ 的三角不等式，要么右边含有一个 $\infty$ 项，要么左边为 $0$。

**例 7.1（取整：输入落入同一格，输出不可区分）.** 取 $Y=\mathbb R$，$\rho_1=|x-y|$，$\rho_2=|\lfloor x\rfloor-\lfloor y\rfloor|$，$\phi(x)=\lfloor x\rfloor$，$\phi(\bot)=\bot$。此时 $\phi^*d_1=\phi^*d_2=d_2$，于是

$$
\overline L(\phi)=\begin{pmatrix}\infty&1\\ \infty&1\end{pmatrix},\quad
\underline L(\phi)=\begin{pmatrix}0&1\\0&1\end{pmatrix},\quad
K(\phi)=\begin{pmatrix}0&1\\0&1\end{pmatrix},\quad
Z(\phi)\equiv 1.
$$

各项的依据：
- 第一列的 $\infty$：取 $x=1-\varepsilon$，$y=1$，比值为 $1/\varepsilon$。
- $\underline L_{i1}=0$：取 $x=0$，$y=\tfrac12$。
- $\kappa_{i1}=\inf\{|x-y|:\lfloor x\rfloor\ne\lfloor y\rfloor\}=0$。
- $\kappa_{i2}=g_2(\mathbb R)=1$。

解读：
- 用细规范 $d_1$ 看，$\phi$ 既不是 Lipschitz 的，也没有正的坍缩半径。
- 用"范畴之差"$d_2$ 看，$\kappa_{12}=1$ 精确表达了"落入同一格（$d_2<1$）则输出不可区分"。
- 在每个格 $A_n=[n,n+1)$ 上，$D_1=1<\infty$，由 4.4(d) 有 $\kappa_{11}(\phi;A_n)=\infty$，即 $\overline L_{11}(\phi;A_n)=0$。
- 与 4.4(c) 一致：$\underline L_{12}=1>0$ 且 $Z_{12}$ 成立，所以 $\kappa_{12}=g_2(\mathbb R)=1$。

**例 7.2（分量结构与复合的边界情形）.** 取 $Y=\mathbb R^2$，$\rho_i=|x_i-y_i|$。每个 $\rho_i$ 单独都不分离点。

| 算子 | $\overline L$ | $\underline L$ | $K$ |
|---|---|---|---|
| 交换 $s(x_1,x_2)=(x_2,x_1)$ | $\begin{pmatrix}\infty&1\\1&\infty\end{pmatrix}$ | $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ | $0$ |
| 恒等 $\mathrm{id}$ | $\begin{pmatrix}1&\infty\\\infty&1\end{pmatrix}$ | $\begin{pmatrix}1&0\\0&1\end{pmatrix}$（与 3.4 吻合） | $0$ |
| 投影 $\pi(x)=(x_1,0)$ | $\begin{pmatrix}1&\infty\\0&0\end{pmatrix}$ | $\begin{pmatrix}1&0\\0&0\end{pmatrix}$ | $\begin{pmatrix}0&0\\\infty&\infty\end{pmatrix}$ |

- $s$ 与 $\mathrm{id}$ 的标量常数都是 $\overline L^{\max}=1$，但矩阵把二者区分开了。
- 复合 $\mathrm{id}\circ\pi=\pi$：$(\overline L(\mathrm{id})\circledast\overline L(\pi))_{11}=\min(1\star1,\ \infty\star0)=1$，这个界是精确的；而按普通乘积计算 $\infty\cdot0=0$ 会得出错误结论。

---

## 8. 小结

记 $\Lambda(f|g)=\max\{\lambda\in\bar{\mathbb R}_+:\lambda f\le g\}$。三个矩阵只是比较的对象不同：

| 矩阵 | 统一形式 | 取 $\infty$ 的含义 | 取 $0$ 的含义 | 复合律 |
|---|---|---|---|---|
| $\overline L$（上界） | $\overline L_{ij}^{-1}=\Lambda(\phi^*d_i\mid d_j)$ | 没有有限常数 | 有限 $d_j$ 距离的点对全部坍缩 | $\min$–$\star$ |
| $\underline L$（下界） | $\underline L_{ij}=\Lambda(d_j\mid\phi^*d_i)$ | $d_j>0\Rightarrow d_i(\phi x,\phi y)=\infty$ | 没有正下界 | $\max$–$\times$ |
| $K$（不可区分） | $\kappa_{ij}=\Lambda(\phi^*\delta_i\mid d_j)$ | 等价于 $\overline L_{ij}=0$ | 存在任意小尺度上的可区分输出 | 与 $\overline L$ 混合（5.3(c)(d)） |

- 三者的最优值都能取到，并且对每个算子都有定义。
- 上界与下界通过对偶 $\underline L(\phi)=\bigl(\overline L(\phi^{-1})^{\top}\bigr)^{\langle-1\rangle}$ 联系。
- 不可区分矩阵就是"可区分性规范"下的 Lipschitz 矩阵的倒数；它与零尺度结构 $Z$ 一起，补全了 $0\cdot\infty$ 处 Lipschitz 矩阵丢失的定性信息。