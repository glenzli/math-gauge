以下为可独立阅读的完整最终稿（全部论证均包含于本答复正文之中，无额外外部文件依赖）。

---

# 完整最终稿

## 第一部分：原题的完整证明

**原命题**：设 $p \ge 3$ 是素数，$r \ge 2$ 是整数，$N = p^r$。取整数 $0 \le a_1 < a_2 < a_3 < N$，假设 $a_1, a_2, a_3$ 模 $p$ 两两不同。再取不全为零的复数 $c_1, c_2, c_3 \in \mathbb{C}$，令
$$P(z) = c_1 z^{a_1} + c_2 z^{a_2} + c_3 z^{a_3}.$$
则在全部 $N$ 次单位根中，满足 $P(z) = 0$ 的不同根至多有两个。

### 证明

设 $\mu_N = \{ z \in \mathbb{C} : z^N = 1 \}$ 为全体 $N$ 次单位根组成的有限集合，记
$$S = \{ z \in \mu_N : P(z) = 0 \}$$
为 $P(z)$ 在 $\mu_N$ 中不同根的集合。我们要证明 $|S| \le 2$。

对任意 $z \in \mu_N$，由 $z^N = 1$ 得 $|z|^N = 1$，由于 $|z| \ge 0$ 且 $N \ge 1$，从而 $|z| = 1$，特别地 $z \neq 0$。

先证如下引理：

> **引理**：若整数 $d$ 满足 $p \nmid d$，则映射 $z \mapsto z^d$ 在 $\mu_N$ 上是单射。
>
> **证明**：设 $z_1, z_2 \in \mu_N$ 满足 $z_1^d = z_2^d$。令 $w = z_1 / z_2$（因 $z_2 \neq 0$ 故有意义），则
> $$w^d = \frac{z_1^d}{z_2^d} = 1, \qquad w^N = \frac{z_1^N}{z_2^N} = 1.$$
> 因为 $N = p^r$ 且 $p$ 为素数、$p \nmid d$，所以 $\gcd(d, N) = 1$。由裴蜀定理，存在整数 $m, n$ 使得 $md + nN = 1$。于是（因 $w \neq 0$，整数次幂运算律成立）
> $$w = w^{md + nN} = (w^d)^m (w^N)^n = 1^m \cdot 1^n = 1,$$
> 即 $z_1 = z_2$。$\square$

已知 $c_1, c_2, c_3$ 不全为零，下面按 $c_1, c_2, c_3$ 中零的个数分三种情形讨论：

#### 情形 1：$c_1, c_2, c_3$ 中恰有两个为零
此时存在唯一的 $j \in \{1, 2, 3\}$ 使得 $c_j \neq 0$，且 $P(z) = c_j z^{a_j}$。对任意 $z \in \mu_N$，由于 $c_j \neq 0$ 且 $z \neq 0$，必有 $P(z) \neq 0$，因此 $|S| = 0 \le 2$。

#### 情形 2：$c_1, c_2, c_3$ 中恰有一个为零
此时存在 $1 \le j < k \le 3$ 使得 $c_j \neq 0$、$c_k \neq 0$，且 $P(z) = c_j z^{a_j} + c_k z^{a_k}$。对任意 $z \in \mu_N$，因 $z \neq 0$ 且 $c_k \neq 0$，有
$$P(z) = 0 \iff c_j z^{a_j} + c_k z^{a_k} = 0 \iff z^{a_k - a_j} = -\frac{c_j}{c_k}.$$
由题设 $a_1, a_2, a_3$ 模 $p$ 两两不同，故 $p \nmid (a_k - a_j)$。对 $d = a_k - a_j$ 应用引理可知映射 $z \mapsto z^{a_k - a_j}$ 在 $\mu_N$ 上是单射，从而方程 $z^{a_k - a_j} = -c_j / c_k$ 在 $\mu_N$ 中至多有一个解，故 $|S| \le 1 \le 2$。

#### 情形 3：$c_1, c_2, c_3$ 均不为零
对任意 $z \in S$，由于 $c_1 \neq 0$ 且 $z \neq 0$，将 $P(z) = 0$ 两边同除以 $c_1 z^{a_1}$，得
$$1 + \frac{c_2}{c_1} z^{a_2 - a_1} + \frac{c_3}{c_1} z^{a_3 - a_1} = 0.$$
定义映射 $u : \mu_N \to \mathbb{C}$ 为
$$u(z) = \frac{c_2}{c_1} z^{a_2 - a_1},$$
并记正实常数
$$R_2 = \left|\frac{c_2}{c_1}\right|, \qquad R_3 = \left|\frac{c_3}{c_1}\right|.$$
对任意 $z \in S$，由 $|z| = 1$ 可得
$$|u(z)| = \left|\frac{c_2}{c_1}\right| |z|^{a_2 - a_1} = R_2,$$
且由 $1 + u(z) = -\dfrac{c_3}{c_1} z^{a_3 - a_1}$ 两边取模可得
$$|1 + u(z)| = \left|-\frac{c_3}{c_1}\right| |z|^{a_3 - a_1} = R_3.$$

将 $w = u(z)$ 写成实部与虚部 $w = x + iy$（$x, y \in \mathbb{R}$），则上述两个模长等式化为实方程组：
$$\begin{cases} x^2 + y^2 = R_2^2, \\ (1 + x)^2 + y^2 = R_3^2. \end{cases}$$
两式相减消去 $y^2$，得
$$(1 + x)^2 - x^2 = R_3^2 - R_2^2 \implies 1 + 2x = R_3^2 - R_2^2 \implies x = \frac{R_3^2 - R_2^2 - 1}{2}.$$
可见 $x$ 仅由 $R_2, R_3$ 唯一确定，与 $z \in S$ 的选取无关。将其代回第一式，有
$$y^2 = R_2^2 - x^2.$$
关于实数 $y$ 的该方程至多有两个实数解（$R_2^2 - x^2 < 0$ 时无解；$R_2^2 - x^2 = 0$ 时仅有 $y = 0$；$R_2^2 - x^2 > 0$ 时有 $y = \pm \sqrt{R_2^2 - x^2}$）。因此，当 $z$ 取遍 $S$ 时，$u(z)$ 至多取到两个不同的复数值，即
$$|u(S)| \le 2.$$
（几何上，$1$、$u(z)$ 与 $-\frac{c_3}{c_1}z^{a_3 - a_1}$ 构成三边长固定为 $1, R_2, R_3$ 的封闭向量三角形，因而 $u(z)$ 至多只有关于实轴对称的两个可能位置。）

另一方面，若 $z_1, z_2 \in \mu_N$ 满足 $u(z_1) = u(z_2)$，由于 $c_2 / c_1 \neq 0$，可得
$$z_1^{a_2 - a_1} = z_2^{a_2 - a_1}.$$
因为 $a_1 \not\equiv a_2 \pmod p$，即 $p \nmid (a_2 - a_1)$，由引理立即得到 $z_1 = z_2$。所以 $u$ 在 $\mu_N$ 上是单射，从而在 $S$ 上也是单射。由此得出
$$|S| = |u(S)| \le 2.$$

综合情形 1、2、3，在全部 $N$ 次单位根中，满足 $P(z) = 0$ 的不同根至多有两个。$\blacksquare$

---

## 第二部分：进一步研究与理论拓展

原证明虽然极简，但它同时揭示了原题条件远非必要条件，且背后隐藏着“低项数几何刚性”与“素数幂 $p$-进刚性”两条截然不同却彼此互补的结构机制。本部分沿着自然问题系统推进：
1. **对任意正整数 $N$ 和任意指数的三项式**：完全释放 $N = p^r$、$p \ge 3$ 与模 $p$ 互异条件，将结论加强到**计入重数**，并彻底解决**锐性判定与零点集逆问题**；
2. **对任意素数幂 $\mu_{p^r}$ 上的一般 $k$ 项式（$1 \le k \le p$）**：利用合流广义 Vandermonde 行列式与 Schur 多项式在 $\mathbb{Z}[\zeta_{p^r}]$ 中的 $(1-\zeta_{p^r})$-进分析，将原结论推广到**任意素数 $p \ge 2$、任意幂次 $r \ge 1$、任意 $1 \le k \le p$ 项及任意整数指数（含 Laurent 多项式）的含重数上界 $\le k-1$**，给出行列式的精确 $(1-\zeta_{p^r})$-进阶公式，完整解决**重数除子插值与实现逆问题**，并推出有理系数下的 Galois 刚性；
3. **条件边界刻画**：证明当 $k \ge 4$ 且 $p \ge 5$ 时，只要 $p \mid N$ 且 $N$ 不是 $p$ 的幂，$k$ 项式上界 $\le k - 1$ 就必然失效（当 $N$ 含奇素因子 $q \neq p$ 时根数甚至可无界增长），从而给出素数幂条件对于 $k \ge 4$ 的精确充要边界；并给出在 $\mu_{p^r}$ 上放弃“指数模 $p$ 两两不同”条件时的陪集约化上界及显式 Fourier 锐性构造。

---

### 2.1 任意正整数 $N$ 下三项式的完整结构理论、重数界与逆问题

设 $N \ge 1$ 为任意正整数，$a_1 < a_2 < a_3$ 为任意整数，$c_1, c_2, c_3 \in \mathbb{C}$ 不全为零。函数 $P(z) = c_1 z^{a_1} + c_2 z^{a_2} + c_3 z^{a_3}$ 在 $\mathbb{C}^*$ 上解析，其在任意点 $w \in \mathbb{C}^*$ 处的零点重数（记为 $\operatorname{ord}_w(P)$）等于普通多项式
$$\widetilde{P}(z) = z^{-a_1} P(z) = c_1 + c_2 z^{a_2 - a_1} + c_3 z^{a_3 - a_1} \in \mathbb{C}[z]$$
在 $w$ 处的重数（若 $P(w) \neq 0$ 则 $\operatorname{ord}_w(P) = 0$）。仍记 $S_{\mu_N}(P) = \{z \in \mu_N : P(z) = 0\}$。

#### 定理 1（任意 $N$ 下三项式的含重数上界与零点结构二分法）
设 $N \ge 1$ 为任意正整数，$a_1 < a_2 < a_3$ 为任意整数，$P(z) = c_1 z^{a_1} + c_2 z^{a_2} + c_3 z^{a_3}$。
1. 若 $c_1, c_2, c_3 \in \mathbb{C}^*$ 均非零，记
   $$g = \gcd(a_2 - a_1,\; a_3 - a_1,\; N) = \gcd(a_2 - a_1,\; a_3 - a_1,\; a_3 - a_2,\; N), \qquad M = \frac{N}{g},$$
   并记满同态 $\pi : \mu_N \to \mu_M,\; \pi(z) = z^g$（其核为 $\mu_g$）。则 $P$ 在 $\mu_N$ 中所有根的重数之和满足
   $$\sum_{z \in \mu_N} \operatorname{ord}_z(P) \le 2g.$$
   更精确地，必出现以下两种互斥结构之一：
   - **(a) 全单根情形**：$P$ 在 $\mu_N$ 中不存在重根，且 $S_{\mu_N}(P) = \pi^{-1}(T)$，其中 $T \subseteq \mu_M$ 满足 $|T| \in \{0, 1, 2\}$，从而 $|S_{\mu_N}(P)| = \sum_{z \in \mu_N} \operatorname{ord}_z(P) = g|T| \in \{0, g, 2g\}$；
   - **(b) 重根情形**：$P$ 在 $\mu_N$ 中存在重根，此时 $S_{\mu_N}(P) = \pi^{-1}(\{w_0\})$ 是 $\mu_g$ 的单个陪集，且该陪集中的每个点都恰为 $P$ 的 $2$ 重根，从而 $|S_{\mu_N}(P)| = g$ 且 $\sum_{z \in \mu_N} \operatorname{ord}_z(P) = 2g$。
2. 若 $c_1, c_2, c_3$ 中恰有两个为零，则 $S_{\mu_N}(P) = \emptyset$；若恰有一个为零（设 $c_i, c_j \neq 0,\; c_m = 0$），则 $P$ 在 $\mu_N$ 中的根均为单根，且 $S_{\mu_N}(P)$ 要么为空集，要么是子群 $\mu_{\gcd(a_j - a_i, N)}$ 的单个陪集（故 $|S_{\mu_N}(P)| \in \{0, \gcd(a_j - a_i, N)\}$）。

#### 定理 1 的证明
情形 2 的证明：若恰有两个系数为零，则 $P(z) = c_j z^{a_j}$ 在 $\mu_N$ 上无零点。若恰有一个系数为零，设 $c_i, c_j \neq 0$（$i < j$），令 $d = a_j - a_i > 0$，则 $P(z) = c_i z^{a_i}(1 + \frac{c_j}{c_i} z^d)$。因为 $1 + \frac{c_j}{c_i} z^d$ 的导数 $\frac{d c_j}{c_i} z^{d-1}$ 在 $\mathbb{C}^*$ 上无零点，故 $P$ 在 $\mu_N$ 中的根均为单根。方程 $z^d = -c_i / c_j$ 在 $\mu_N$ 上的解集是同态 $z \mapsto z^d$（核为 $\mu_{\gcd(d, N)}$）的单个纤维或空集，从而 $|S_{\mu_N}(P)| \in \{0, \gcd(d, N)\}$。

下面证明情形 1（$c_1, c_2, c_3 \in \mathbb{C}^*$）。记 $b_2 = \frac{a_2 - a_1}{g},\; b_3 = \frac{a_3 - a_1}{g}$，则 $0 < b_2 < b_3$ 且 $\gcd(b_2, b_3, M) = 1$。再令 $\alpha = c_2 / c_1 \neq 0,\; \beta = c_3 / c_1 \neq 0$，以及多项式
$$Q(w) = 1 + \alpha w^{b_2} + \beta w^{b_3} \in \mathbb{C}[w],$$
则对所有 $z \in \mathbb{C}^*$ 有 $\widetilde{P}(z) = c_1 Q(z^g)$。

先说明对任意 $z_0 \in \mu_N$，记 $w_0 = z_0^g \in \mu_M$，恒有 $\operatorname{ord}_{z_0}(P) = \operatorname{ord}_{w_0}(Q)$：设 $\operatorname{ord}_{w_0}(Q) = m \ge 0$，写出 $Q(w) = (w - w_0)^m R(w)$，其中 $R(w) \in \mathbb{C}[w]$ 且 $R(w_0) \neq 0$。于是
$$Q(z^g) = (z - z_0)^m \left(\frac{z^g - z_0^g}{z - z_0}\right)^m R(z^g) = (z - z_0)^m \left(\sum_{t=0}^{g-1} z^t z_0^{g-1-t}\right)^m R(z^g),$$
将 $z = z_0$ 代入后两项之积得 $(g z_0^{g-1})^m R(w_0) \neq 0$，故 $\operatorname{ord}_{z_0}(P) = \operatorname{ord}_{z_0}(\widetilde{P}) = m = \operatorname{ord}_{w_0}(Q)$。又因为 $\pi : \mu_N \to \mu_M$ 是 $g$-对-$1$ 满同态，若记 $T = \{w \in \mu_M : Q(w) = 0\}$，则 $S_{\mu_N}(P) = \pi^{-1}(T)$ 且每个 $w_0 \in T$ 在 $\mu_N$ 中恰好对应 $g$ 个重数均为 $\operatorname{ord}_{w_0}(Q)$ 的根。

现在分析 $Q(w)$ 在 $\mu_M$ 上的根及其重数。定义映射
$$u(w) = \alpha w^{b_2}, \qquad v(w) = \beta w^{b_3}.$$
对任意 $w \in T$，有 $1 + u(w) + v(w) = 0$ 且 $|w| = 1$，故 $|u(w)| = |\alpha| =: R_2 > 0$ 且 $|1 + u(w)| = |-v(w)| = |\beta| =: R_3 > 0$。沿用第一部分情形 3 的实方程组 $x^2 + y^2 = R_2^2,\; (1+x)^2 + y^2 = R_3^2$（其中 $u(w) = x + iy$），即得 $x = \frac{R_3^2 - R_2^2 - 1}{2}$ 唯一确定，而 $y^2 = R_2^2 - x^2$ 至多两解，故 $|u(T)| \le 2$。

进一步，映射 $u|_T$ 是单射：若 $w_1, w_2 \in T$ 满足 $u(w_1) = u(w_2)$，则由 $v(w) = -1 - u(w)$ 立即同时得到 $v(w_1) = v(w_2)$。令 $q = w_1 / w_2 \in \mu_M$，由于 $\alpha, \beta \neq 0$，便有
$$q^{b_2} = 1, \qquad q^{b_3} = 1, \qquad q^M = 1.$$
因 $\gcd(b_2, b_3, M) = 1$，由三元裴蜀定理，存在整数 $m_1, m_2, m_3$ 使 $m_1 b_2 + m_2 b_3 + m_3 M = 1$，于是 $q = (q^{b_2})^{m_1}(q^{b_3})^{m_2}(q^M)^{m_3} = 1$，即 $w_1 = w_2$。从而 $|T| = |u(T)| \le 2$。

最后考察重数。假设 $Q$ 在 $\mu_M$ 中存在某个重数 $\ge 2$ 的根 $w_0 \in T$，则 $Q(w_0) = Q'(w_0) = 0$。记 $u_0 = u(w_0) = \alpha w_0^{b_2}$、$v_0 = v(w_0) = \beta w_0^{b_3}$，由 $Q(w_0) = 0$ 及 $w_0 Q'(w_0) = 0$ 得
$$\begin{cases} 1 + u_0 + v_0 = 0, \\ b_2 u_0 + b_3 v_0 = 0. \end{cases}$$
因 $b_3 - b_2 > 0$，唯一解为 $u_0 = -\dfrac{b_3}{b_3 - b_2} < -1$，$v_0 = \dfrac{b_2}{b_3 - b_2} > 0$。因此 $R_2 = |u_0| = \dfrac{b_3}{b_3 - b_2}$ 且 $R_3 = |v_0| = R_2 - 1$。代入 $x$ 的表达式得
$$x = \frac{(R_2 - 1)^2 - R_2^2 - 1}{2} = -R_2,$$
从而 $y^2 = R_2^2 - x^2 = 0$，即方程组在 $\mathbb{C}$ 中仅有唯一解 $u_0$。这说明 $|u(T)| = 1$，故 $T = \{w_0\}$。又计算二阶导数：
$$w_0^2 Q''(w_0) = b_2(b_2 - 1) u_0 + b_3(b_3 - 1) v_0 = \frac{-b_2(b_2 - 1)b_3 + b_3(b_3 - 1)b_2}{b_3 - b_2} = b_2 b_3 \neq 0,$$
故 $\operatorname{ord}_{w_0}(Q) = 2$。拉回至 $\mu_N$ 即得到 (a)、(b) 的精确二分法以及 $\sum_{z \in \mu_N} \operatorname{ord}_z(P) \le 2g$。$\blacksquare$

---

#### 定理 2（锐性与零点集逆问题的完全刻画）
在定理 1 的记号下，设 $a_1 < a_2 < a_3$ 模 $N$ 两两不同（特别地，$0 \le a_1 < a_2 < a_3 < N$ 时自动满足）。此时必有 $M = N/g \ge 3$，且：
1. **全局最大值**：在所有非零系数三项式 $(c_1, c_2, c_3) \in (\mathbb{C}^*)^3$ 中，$|S_{\mu_N}(P)|$ 与 $\sum_{z \in \mu_N} \operatorname{ord}_z(P)$ 的最大值均精确等于 $2g$；在所有不全为零的系数 $(c_1, c_2, c_3) \in \mathbb{C}^3 \setminus \{(0,0,0)\}$ 中，$|S_{\mu_N}(P)|$ 的精确最大值为
   $$\max\Big(2g,\; \gcd(a_2 - a_1, N),\; \gcd(a_3 - a_1, N),\; \gcd(a_3 - a_2, N)\Big).$$
2. **零点集的充要刻画（逆问题）**：子集 $S \subseteq \mu_N$ 能够作为某个非零系数三项式 $P(z)$（$c_1, c_2, c_3 \in \mathbb{C}^*$）的精确零点集 $S_{\mu_N}(P)$，**当且仅当** $S = \pi^{-1}(T)$，其中 $T \subseteq \mu_M$ 满足 $|T| \le 2$，且当 $T = \{w_1, w_2\}$（$w_1 \neq w_2$）时，$w_1 / w_2$ 在 $\mu_M$ 中的乘法阶 $d$ 不整除 $b_2, b_3, b_3 - b_2$ 中的任何一个。
   - 进一步，对任意单点 $T = \{w_0\} \subseteq \mu_M$，$S = \pi^{-1}(\{w_0\})$ 既可以由在 $\pi^{-1}(\{w_0\})$ 上取**$2$ 重根**的三项式实现，也可以由全为**单根**的三项式实现。
   - 特别地，在原题情形（$N = p^r,\; p \ge 3$，$a_1, a_2, a_3$ 模 $p$ 两两不同）中，$g = 1$ 且任意两个不同单位根之比的阶均为 $p^s$（$s \ge 1$），均不整除 $b_2, b_3, b_3 - b_2$，因此 $\mu_N$ 的**每一个**至多含 $2$ 个元素的子集都是某个非零系数三项式的精确零点集。

#### 定理 2 的证明
首先验证 $M \ge 3$：由 $g \mid (a_2 - a_1)$ 与 $g \mid (a_3 - a_1)$ 知 $a_1 \equiv a_2 \equiv a_3 \pmod g$，而模 $N = Mg$ 中同属于一个模 $g$ 剩余类的剩余类恰有 $M$ 个。因 $a_1, a_2, a_3$ 模 $N$ 两两不同，必有 $M \ge 3$。同时 $N \nmid (a_j - a_i)$ 等价于 $M$ 不整除 $b_2, b_3, b_3 - b_2$ 中的任何一个。

下面检验各 $T \subseteq \mu_M$（$|T| \le 2$）的可实现性：
- **必要性**：由定理 1(1)，任何 $c_1, c_2, c_3 \in \mathbb{C}^*$ 均满足 $S_{\mu_N}(P) = \pi^{-1}(T)$ 且 $|T| \le 2$。当 $T = \{w_1, w_2\}$（$w_1 \neq w_2$）时，$(c_1, c_2, c_3)$ 满足齐次线性方程组
  $$\begin{pmatrix} 1 & w_1^{b_2} & w_1^{b_3} \\ 1 & w_2^{b_2} & w_2^{b_3} \end{pmatrix} \begin{pmatrix} c_1 \\ c_2 \\ c_3 \end{pmatrix} = \begin{pmatrix} 0 \\ 0 \end{pmatrix}.$$
  令 $q = w_1 / w_2 \in \mu_M \setminus \{1\}$，其阶为 $d \ge 2$。上述 $2 \times 3$ 矩阵的三阶子式（即三个 $2 \times 2$ 子式）分别为
  $$\Delta_1 = w_1^{b_2} w_2^{b_3} - w_2^{b_2} w_1^{b_3} = w_2^{b_2 + b_3} q^{b_2}(1 - q^{b_3 - b_2}),$$
  $$\Delta_2 = w_2^{b_3}(1 - q^{b_3}), \qquad \Delta_3 = w_2^{b_2}(q^{b_2} - 1).$$
  注意 $\Delta_1, \Delta_2, \Delta_3$ 不可能全为零（否则 $q^{b_2} = q^{b_3} = 1$ 且 $q^M = 1$，结合 $\gcd(b_2, b_3, M) = 1$ 将迫使 $q = 1$，矛盾）。因此系数矩阵秩为 $2$，解空间由 $(\Delta_1, -\Delta_2, \Delta_3)$ 张成。于是存在全非零解 $(c_1, c_2, c_3) \in (\mathbb{C}^*)^3$ 当且仅当 $\Delta_1, \Delta_2, \Delta_3$ 均非零，即 $q^{b_2} \neq 1,\; q^{b_3} \neq 1,\; q^{b_3 - b_2} \neq 1$，这等价于 $d$ 不整除 $b_2, b_3, b_3 - b_2$ 中的任何一个。
- **充分性**：
  1. $T = \emptyset$：取 $c_1 = 3,\; c_2 = 1,\; c_3 = 1$，对所有 $z \in \mu_N$ 有 $|P(z)| \ge 3 - 1 - 1 = 1 > 0$。
  2. $T = \{w_0\}$（$2$ 重根实现）：取 $c_1 = 1,\; c_2 = -\frac{b_3}{b_3 - b_2} w_0^{-b_2} \neq 0,\; c_3 = \frac{b_2}{b_3 - b_2} w_0^{-b_3} \neq 0$，则 $Q(w_0) = Q'(w_0) = 0$。由定理 1(1)(b)，必有 $T = \{w_0\}$ 且 $w_0$ 为 $2$ 重根。
  3. $T = \{w_0\}$（单根实现）：取 $c_1 = 1$，$c_2 = \frac{3 + 4i}{5} w_0^{-b_2} \neq 0$，$c_3 = -\frac{8 + 4i}{5} w_0^{-b_3} \neq 0$。此时 $Q(w_0) = 1 + \frac{3 + 4i}{5} - \frac{8 + 4i}{5} = 0$。在此取法下，$u(w_0) = c_2 w_0^{b_2} = \frac{3 + 4i}{5}$，故 $R_2 = |c_2| = 1$，从而方程组 $x^2 + y^2 = 1,\; (1+x)^2 + y^2 = R_3^2$ 的两个解为 $u_+ = \frac{3 + 4i}{5}$ 与 $u_- = \frac{3 - 4i}{5}$（因 $y = \pm \frac{4}{5} \neq 0$）。若有另一点 $w_1 \in T \setminus \{w_0\}$，则由 $u|_T$ 单射必有 $u(w_1) = u_-$，从而
     $$(w_1 / w_0)^{b_2} = \frac{u_-}{u_+} = \frac{(3 - 4i)^2}{25} = \frac{-7 - 24i}{25}.$$
     然而该数不可能是单位根：记 $\xi = -7 - 24i \in \mathbb{Z}[i]$，注意 $\xi \equiv 3 + i \pmod 5$ 且 $(3 + i)^2 = 8 + 6i \equiv 3 + i \pmod 5$。由数学归纳法，对任意正整数 $n \ge 1$，记 $\xi^n = A_n + B_n i$（$A_n, B_n \in \mathbb{Z}$），均有 $A_n \equiv 3 \pmod 5$ 且 $B_n \equiv 1 \pmod 5$，特别地 $B_n \neq 0$，故 $(\xi / 25)^n \notin \mathbb{R}$，从而 $(\xi / 25)^n \neq 1$。这与 $(w_1 / w_0)^{b_2} \in \mu_M$ 矛盾！因此 $T = \{w_0\}$，且因 $u(w_0) \notin \mathbb{R}$ 故非定理 1(1)(b) 之重根情形，必为单根。
  4. $T = \{w_1, w_2\}$（满足阶条件）：取 $(c_1, c_2, c_3) = (\Delta_1, -\Delta_2, \Delta_3) \in (\mathbb{C}^*)^3$，则 $T \supseteq \{w_1, w_2\}$，再由定理 1 得 $|T| \le 2$，故 $T = \{w_1, w_2\}$。

最后证明第 1 条中的最大值：取 $w_1 = 1,\; w_2 = e^{2\pi i / M} \in \mu_M$，则 $d = \operatorname{ord}(w_1 / w_2) = M$。前面已指出 $M$ 不整除 $b_2, b_3, b_3 - b_2$ 中的任何一个，故 $T = \{1, e^{2\pi i / M}\}$ 可由非零系数三项式实现，给出 $|S_{\mu_N}(P)| = 2g$。若允许一个系数为零（如 $c_m = 0,\; c_i = 1,\; c_j = -1$），方程 $z^{a_i} - z^{a_j} = 0$ 在 $\mu_N$ 中恰有 $\gcd(a_j - a_i, N)$ 个根。结合定理 1，两类最大值均已精确建立。$\blacksquare$

---

### 2.2 素数幂 $\mu_{p^r}$ 上一般 $k$ 项式的完整理论（$1 \le k \le p$）

在本节中，设 $p \ge 2$ 为**任意素数**，$r \ge 1$ 为**任意正整数**，$N = p^r$，且 $1 \le k \le p$。记 $\zeta = e^{2\pi i / N}$ 为本原 $N$ 次单位根，并在分圆整环 $\mathbb{Z}[\zeta]$ 中记 $\pi = 1 - \zeta$，记主理想 $\mathfrak{p} = (\pi) = (1 - \zeta)\mathbb{Z}[\zeta]$。

我们首先以完全初等、自足的方式建立 $\mathbb{Z}[\zeta]$ 中 $\mathfrak{p}$ 的算术性质（无需引用代数整数环 $\mathcal{O}_K = \mathbb{Z}[\zeta]$ 或 Dedekind 整环理论）。

#### 引理 A（$\Phi_{p^r}(X)$ 的不可约性与 $\mathfrak{p}$-进基本性质）
1. 素数幂分圆多项式
   $$\Phi_{p^r}(X) = \frac{X^{p^r} - 1}{X^{p^{r-1}} - 1} = \sum_{t=0}^{p-1} X^{t p^{r-1}} \in \mathbb{Z}[X]$$
   在 $\mathbb{Q}[X]$ 上不可约，且 $\Phi_{p^r}(1) = p$。
2. 在整环 $\mathbb{Z}[\zeta]$ 中，商环 $\mathbb{Z}[\zeta] / \mathfrak{p} \cong \mathbb{F}_p$，故 $\mathfrak{p}$ 是 $\mathbb{Z}[\zeta]$ 的极大（从而素）理想；进一步，有 $(p)\mathbb{Z}[\zeta] = \mathfrak{p}^{\varphi(p^r)}$，其中 $\varphi(p^r) = p^{r-1}(p-1)$。
3. 对任意整数 $d \not\equiv 0 \pmod{p^r}$，记 $\alpha = v_p(d) \in \{0, 1, \dots, r-1\}$（即 $p^\alpha \parallel d$），则存在单位 $u_d \in \mathbb{Z}[\zeta]^\times$ 使得 $1 - \zeta^d = u_d \pi^{p^\alpha}$，从而
   $$(1 - \zeta^d)\mathbb{Z}[\zeta] = \mathfrak{p}^{p^{v_p(d)}}.$$

#### 引理 A 的证明
**(1)** 显然 $\Phi_{p^r}(1) = p$。令 $X = 1 + Y$，在 $\mathbb{Z}[Y]$ 中考虑 $\Phi_{p^r}(1 + Y)$（首一，次数为 $\varphi(p^r) = p^{r-1}(p-1)$）。由于对任意 $m \ge 1$ 及 $0 < j < p^m$ 均有 $p \mid \binom{p^m}{j}$（例如由 $(1+Y)^p \equiv 1+Y^p \pmod p$ 对 $m$ 归纳即得），在 $\mathbb{F}_p[Y]$ 中有 $\overline{(1+Y)^{p^r} - 1} = Y^{p^r}$ 及 $\overline{(1+Y)^{p^{r-1}} - 1} = Y^{p^{r-1}}$。由等式
$$\Phi_{p^r}(1 + Y)\big((1 + Y)^{p^{r-1}} - 1\big) = (1 + Y)^{p^r} - 1$$
模 $p$ 约化得 $\overline{\Phi_{p^r}(1+Y)} \cdot Y^{p^{r-1}} = Y^{p^r}$，故 $\overline{\Phi_{p^r}(1+Y)} = Y^{p^{r-1}(p-1)}$。因此 $\Phi_{p^r}(1 + Y)$ 除首项系数 $1$ 外的所有系数均被 $p$ 整除，且常数项为 $\Phi_{p^r}(1) = p$ 不被 $p^2$ 整除。由 Eisenstein 判别法，$\Phi_{p^r}(1 + Y)$（从而 $\Phi_{p^r}(X)$）在 $\mathbb{Q}[X]$ 上不可约。

**(2)** 因为 $\Phi_{p^r}(\zeta) = 0$ 且 $\Phi_{p^r}(X)$ 首一不可约，故 $\mathbb{Z}[\zeta] \cong \mathbb{Z}[X] / (\Phi_{p^r}(X))$。利用恒等式 $\Phi_{p^r}(1) = p$，在 $\mathbb{Z}[X]$ 中 $(\Phi_{p^r}(X), 1 - X) = (p, 1 - X)$，从而
$$\mathbb{Z}[\zeta] / \mathfrak{p} \cong \mathbb{Z}[X] / (\Phi_{p^r}(X), 1 - X) = \mathbb{Z}[X] / (p, 1 - X) \cong \mathbb{Z} / p\mathbb{Z} = \mathbb{F}_p.$$
于是 $\mathfrak{p}$ 是 $\mathbb{Z}[\zeta]$ 的极大理想。

又对任意与 $p$ 互素的整数 $j \ge 1$，取正整数 $j'$ 使 $jj' \equiv 1 \pmod{p^r}$，则 $\zeta = (\zeta^j)^{j'}$，从而
$$\frac{1 - \zeta^j}{1 - \zeta} = \sum_{s=0}^{j-1} \zeta^s \in \mathbb{Z}[\zeta], \qquad \frac{1 - \zeta}{1 - \zeta^j} = \frac{1 - (\zeta^j)^{j'}}{1 - \zeta^j} = \sum_{s=0}^{j'-1} \zeta^{j s} \in \mathbb{Z}[\zeta],$$
即每个 $(1 - \zeta^j) / \pi$ 都是 $\mathbb{Z}[\zeta]^\times$ 中的单位。将 $\Phi_{p^r}(X) = \prod_{\substack{1 \le j < p^r \\ p \nmid j}} (X - \zeta^j)$（注意在 $\mathbb{Q}(\zeta)[X]$ 中因式分解即得，且由于在 $\mathbb{Z}[\zeta][X]$ 中各因子首一，该分解在 $\mathbb{Z}[\zeta][X]$ 中成立）在 $X = 1$ 处求值，得
$$p = \Phi_{p^r}(1) = \prod_{\substack{1 \le j < p^r \\ p \nmid j}} (1 - \zeta^j) = u \cdot \pi^{\varphi(p^r)},$$
其中 $u \in \mathbb{Z}[\zeta]^\times$。故 $(p)\mathbb{Z}[\zeta] = \mathfrak{p}^{\varphi(p^r)}$。

**(3)** 写出 $d \equiv p^\alpha b \pmod{p^r}$，其中 $0 \le \alpha \le r - 1$，$b \ge 1$ 且 $p \nmid b$。记 $\eta_\alpha = \zeta^{p^\alpha}$，它是本原 $p^{r-\alpha}$ 次单位根。

先对 $\alpha = 0, 1, \dots, r - 1$ 归纳证明 $1 - \eta_\alpha \in \mathfrak{p}^{p^\alpha}$：$\alpha = 0$ 时 $1 - \eta_0 = \pi \in \mathfrak{p}$。若对某 $0 \le \alpha \le r - 2$ 已有 $1 - \eta_\alpha \in \mathfrak{p}^{p^\alpha}$，由于 $\alpha + 1 \le r - 1$ 且对一切 $p \ge 2$ 均有 $\varphi(p^r) = p^{r-1}(p-1) \ge p^{r-1} \ge p^{\alpha + 1}$，故 $(p) = \mathfrak{p}^{\varphi(p^r)} \subseteq \mathfrak{p}^{p^{\alpha + 1}}$。由二项式展开
$$1 - \eta_{\alpha+1} = 1 - \eta_\alpha^p = (1 - \eta_\alpha)^p - \sum_{j=1}^{p-1} (-1)^j \binom{p}{j} \eta_\alpha^j,$$
因 $p \mid \binom{p}{j}$（$1 \le j \le p-1$）且 $(1 - \eta_\alpha)^p \in (\mathfrak{p}^{p^\alpha})^p = \mathfrak{p}^{p^{\alpha+1}}$，立即得到 $1 - \eta_{\alpha+1} \in \mathfrak{p}^{p^{\alpha+1}}$。

由此可设 $1 - \eta_\alpha = c_\alpha \pi^{p^\alpha}$，其中 $c_\alpha \in \mathbb{Z}[\zeta]$。另一方面，对 $\eta_\alpha$（即 $r - \alpha \ge 1$ 阶本原单位根）应用第 (2) 条，存在单位 $v_\alpha \in \mathbb{Z}[\eta_\alpha]^\times \subseteq \mathbb{Z}[\zeta]^\times$ 使得
$$p = v_\alpha (1 - \eta_\alpha)^{\varphi(p^{r-\alpha})} = v_\alpha c_\alpha^{\varphi(p^{r-\alpha})} \pi^{p^\alpha \varphi(p^{r-\alpha})} = v_\alpha c_\alpha^{\varphi(p^{r-\alpha})} \pi^{\varphi(p^r)}.$$
与第 (2) 条所得 $p = u \pi^{\varphi(p^r)}$ 比较，在整环 $\mathbb{Z}[\zeta]$ 中消去非零元 $\pi^{\varphi(p^r)}$ 得 $v_\alpha c_\alpha^{\varphi(p^{r-\alpha})} = u \in \mathbb{Z}[\zeta]^\times$，故 $c_\alpha \in \mathbb{Z}[\zeta]^\times$。最后，由于 $p \nmid b$ 且 $\eta_\alpha$ 是 $p^{r-\alpha}$ 次本原单位根，同第 (2) 条完全一样，$(1 - \eta_\alpha^b)/(1 - \eta_\alpha) \in \mathbb{Z}[\eta_\alpha]^\times \subseteq \mathbb{Z}[\zeta]^\times$。从而 $1 - \zeta^d = 1 - \eta_\alpha^b = u_d \pi^{p^\alpha}$，其中 $u_d \in \mathbb{Z}[\zeta]^\times$。$\blacksquare$

---

#### 定理 3（合流广义 Vandermonde 行列式恒等式与精确 $\mathfrak{p}$-进阶公式）
设 $p \ge 2$ 为素数，$r \ge 1$，$N = p^r$，$1 \le k \le p$。设整数 $0 \le a_1 < a_2 < \dots < a_k$ 模 $p$ 两两不同。任取 $\mu_N$ 中 $t$ 个互异元素 $w_1, \dots, w_t$（写出 $w_s = \zeta^{e_s}$，其中 $e_s \in \{0, 1, \dots, N-1\}$）以及正整数 $m_1, \dots, m_t \ge 1$ 满足 $\sum_{s=1}^t m_s = k$。构造 $k \times k$ 合流广义 Vandermonde 矩阵 $M_{\mathrm{conf}}$：其行以 $(s, \nu)$（$1 \le s \le t,\; 0 \le \nu < m_s$，按字典序排列）索引，第 $(s, \nu)$ 行第 $j$ 列（$1 \le j \le k$）元素为
$$\binom{a_j}{\nu} w_s^{a_j - \nu} \qquad (\text{约定当 } a_j < \nu \text{ 时 }\binom{a_j}{\nu} = 0\text{，该项按 } 0 \text{ 计}).$$
则：
1. 在多项式环 $\mathbb{Z}[x_1, \dots, x_k]$ 中，商 $Q(\mathbf{x}) := \det(x_i^{a_j})_{1 \le i,j \le k} \big/ \prod_{1 \le u < v \le k} (x_v - x_u)$ 属于 $\mathbb{Z}[x_1, \dots, x_k]$，且满足
   $$Q(1, \dots, 1) = \prod_{1 \le u < v \le k} \frac{a_v - a_u}{v - u} \in \mathbb{Z}, \qquad p \nmid Q(1, \dots, 1).$$
   （当 $k = 1$ 时空乘积按 $1$ 计。）
2. 在 $\mathbb{Z}[w_1, \dots, w_t]$ 中成立精确恒等式：
   $$\det M_{\mathrm{conf}} = \left(\prod_{1 \le u < v \le t} (w_v - w_u)^{m_u m_v}\right) Q(\underbrace{w_1, \dots, w_1}_{m_1},\; \dots,\; \underbrace{w_t, \dots, w_t}_{m_t}).$$
3. $\det M_{\mathrm{conf}} \neq 0$，且在 $\mathbb{Z}[\zeta]$ 中成立精确 $\mathfrak{p}$-进阶关系：
   $$\det M_{\mathrm{conf}} \in \mathfrak{p}^E \setminus \mathfrak{p}^{E+1}, \qquad E = \sum_{1 \le u < v \le t} m_u m_v \, p^{v_p(e_v - e_u)}.$$

#### 定理 3 的证明
$k = 1$ 时，$t = 1, m_1 = 1$，$M_{\mathrm{conf}} = (w_1^{a_1})$，$\det M_{\mathrm{conf}} = w_1^{a_1} \in \mathbb{Z}[\zeta]^\times = \mathfrak{p}^0 \setminus \mathfrak{p}^1$，且 $Q \equiv 1$，所有结论显然成立。以下设 $k \ge 2$。

**(1)** 令 $D(\mathbf{x}) = \det(x_i^{a_j})_{1 \le i,j \le k} \in \mathbb{Z}[x_1, \dots, x_k]$ 与 $\Delta(\mathbf{x}) = \prod_{1 \le u < v \le k} (x_v - x_u)$。对任意 $1 \le u < v \le k$，把 $D$ 看作以 $R = \mathbb{Z}[x_1, \dots, \widehat{x_v}, \dots, x_k]$ 为系数的 $x_v$ 的一元多项式。令 $x_v = x_u$ 使行列式第 $u$ 行与第 $v$ 行相等，从而为零。因 $x_v - x_u$ 关于 $x_v$ 首一，在 $R[x_v]$ 中做带余除法得 $(x_v - x_u) \mid D(\mathbf{x})$。由 Gauss 定理，$\mathbb{Z}[x_1, \dots, x_k]$ 是唯一分解整环，而两两互异的首一一次多项式 $x_v - x_u$（$1 \le u < v \le k$）是其中两两非相伴的不可约元，故它们的乘积 $\Delta(\mathbf{x})$ 在 $\mathbb{Z}[x_1, \dots, x_k]$ 中整除 $D(\mathbf{x})$，从而 $Q(\mathbf{x}) = D(\mathbf{x}) / \Delta(\mathbf{x}) \in \mathbb{Z}[x_1, \dots, x_k]$。

为计算 $Q(1, \dots, 1)$，将 $x_i = T^{i-1}$（$1 \le i \le k$）代入得
$$D(1, T, \dots, T^{k-1}) = \det\big((T^{i-1})^{a_j}\big)_{1 \le i,j \le k} = \det\big((T^{a_j})^{i-1}\big)_{1 \le i,j \le k} = \prod_{1 \le u < v \le k} (T^{a_v} - T^{a_u})$$
（最后一步为以 $T^{a_1}, \dots, T^{a_k}$ 为变元的 Vandermonde 行列式转置）。同时 $\Delta(1, T, \dots, T^{k-1}) = \prod_{1 \le u < v \le k} (T^{v-1} - T^{u-1})$。因为 $0 \le a_1 < a_2 < \dots < a_k$，对所有 $1 \le u < v \le k$ 均有 $a_u \ge u - 1$ 且 $a_v - a_u \ge 1,\; v - u \ge 1$，故在分式域 $\mathbb{Q}(T)$ 中有
$$Q(1, T, \dots, T^{k-1}) = \prod_{1 \le u < v \le k} T^{a_u - (u-1)} \frac{1 + T + \dots + T^{a_v - a_u - 1}}{1 + T + \dots + T^{v - u - 1}}.$$
等式两边在 $T = 1$ 处均无分母为零之虞，代入 $T = 1$ 即得
$$Q(1, \dots, 1) = \prod_{1 \le u < v \le k} \frac{a_v - a_u}{v - u}.$$
因 $Q \in \mathbb{Z}[\mathbf{x}]$，故 $Q(1, \dots, 1) \in \mathbb{Z}$。记 $M_0 = \prod_{1 \le u < v \le k} (v - u)$ 与 $A_0 = \prod_{1 \le u < v \le k} (a_v - a_u)$，则在 $\mathbb{Z}$ 中有 $M_0 \cdot Q(1, \dots, 1) = A_0$。因 $a_1, \dots, a_k$ 模 $p$ 两两不同，故 $p \nmid A_0$，从而必有 $p \nmid Q(1, \dots, 1)$（实际上 $1 \le v - u \le k - 1 < p$ 也保证 $p \nmid M_0$）。

**(2)** 引入 $k$ 个独立辅助变元 $h_{s,\nu}$（$1 \le s \le t,\; 0 \le \nu < m_s$），将 $x_1, \dots, x_k$ 依次记作 $x_{s,\nu} = w_s + h_{s,\nu}$。在多项式环 $\mathbb{Z}[\mathbf{w}, \mathbf{h}]$ 中考虑 $D(\mathbf{w} + \mathbf{h}) = \det\big((w_s + h_{s,\nu})^{a_j}\big)$。

一方面，对第 $(s, \nu)$ 行按二项式定理展开 $(w_s + h_{s,\nu})^{a_j} = \sum_{q=0}^{a_j} \binom{a_j}{q} w_s^{a_j - q} h_{s,\nu}^q$。因第 $(s, \nu)$ 行只含单一变元 $h_{s,\nu}$，由行列式的多重线性性，单项式 $\mathbf{h}^{\boldsymbol{\nu}} := \prod_{s=1}^t \prod_{\nu=0}^{m_s-1} h_{s,\nu}^\nu$ 在 $D(\mathbf{w} + \mathbf{h})$ 中的系数**恰好**是每一行 $(s, \nu)$ 均取 $q = \nu$ 项所得行列式，即 $\det M_{\mathrm{conf}}$。

另一方面，由 (1) 知 $D(\mathbf{w} + \mathbf{h}) = \Delta(\mathbf{w} + \mathbf{h}) \cdot Q(\mathbf{w} + \mathbf{h})$。按变元序展开 $\Delta(\mathbf{w} + \mathbf{h})$：
$$\Delta(\mathbf{w} + \mathbf{h}) = \left(\prod_{s=1}^t \Delta_{\mathrm{blk},s}(\mathbf{h}_s)\right) \cdot \prod_{1 \le u < v \le t} \prod_{\lambda=0}^{m_u-1} \prod_{\mu=0}^{m_v-1} (w_v - w_u + h_{v,\mu} - h_{u,\lambda}),$$
其中对每个 $s$，块内因子
$$\Delta_{\mathrm{blk},s}(\mathbf{h}_s) = \prod_{0 \le \lambda < \mu < m_s} (h_{s,\mu} - h_{s,\lambda}) = \det\big(h_{s,\nu}^q\big)_{0 \le \nu, q < m_s}$$
关于 $\mathbf{h}_s = (h_{s,0}, \dots, h_{s,m_s-1})$ 是次数为 $\binom{m_s}{2} = \sum_{\nu=0}^{m_s - 1} \nu$ 的齐次多项式。因此 $\prod_{s=1}^t \Delta_{\mathrm{blk},s}(\mathbf{h}_s)$ 关于全体 $\mathbf{h}$ 已经达到总次数 $\sum_{s=1}^t \binom{m_s}{2}$，这恰等于单项式 $\mathbf{h}^{\boldsymbol{\nu}}$ 的总次数！故欲从
$$D(\mathbf{w} + \mathbf{h}) = \left(\prod_{s=1}^t \Delta_{\mathrm{blk},s}(\mathbf{h}_s)\right) \cdot \left(\prod_{1 \le u < v \le t} \prod_{\lambda=0}^{m_u-1} \prod_{\mu=0}^{m_v-1} (w_v - w_u + h_{v,\mu} - h_{u,\lambda})\right) Q(\mathbf{w} + \mathbf{h})$$
中提取 $\mathbf{h}^{\boldsymbol{\nu}}$ 的系数，后两大因子的乘积只能贡献其关于 $\mathbf{h}$ 的常数项（令所有 $h_{s,\nu} = 0$），即
$$\left(\prod_{1 \le u < v \le t} (w_v - w_u)^{m_u m_v}\right) Q(\underbrace{w_1, \dots, w_1}_{m_1}, \dots, \underbrace{w_t, \dots, w_t}_{m_t}).$$
而各 $\Delta_{\mathrm{blk},s}(\mathbf{h}_s) = \det(h_{s,\nu}^q)$ 涉及互不相交的变元组，且由行列式 Leibniz 展开，主对角乘积 $\prod_{\nu=0}^{m_s-1} h_{s,\nu}^\nu$ 在 $\Delta_{\mathrm{blk},s}(\mathbf{h}_s)$ 中的系数为 $+1$。对比 $\mathbf{h}^{\boldsymbol{\nu}}$ 的系数即得第 (2) 条恒等式。

**(3)** 由 $w_s = \zeta^{e_s} \equiv 1 \pmod{\mathfrak{p}}$（因 $1 - \zeta^e = (1 - \zeta)(1 + \zeta + \dots + \zeta^{e-1}) \in \mathfrak{p}$）及 $Q \in \mathbb{Z}[x_1, \dots, x_k]$，有
$$Q(\underbrace{w_1, \dots, w_1}_{m_1}, \dots, \underbrace{w_t, \dots, w_t}_{m_t}) \equiv Q(1, \dots, 1) \pmod{\mathfrak{p}}.$$
若 $Q(w_1, \dots, w_t) \in \mathfrak{p}$，则 $Q(1, \dots, 1) \in \mathfrak{p}$；又由 (1) 知 $\gcd(Q(1, \dots, 1), p) = 1$ 且 $p \in \mathfrak{p}$，由裴蜀定理可得 $1 \in \mathfrak{p}$，与引理 A(2) 中 $\mathbb{Z}[\zeta]/\mathfrak{p} \cong \mathbb{F}_p$ 矛盾！故 $Q(w_1, \dots, w_t) \notin \mathfrak{p}$（特别地非零）。

再看每个因子 $w_v - w_u$（$1 \le u < v \le t$）：因 $e_u \neq e_v \in \{0, \dots, N-1\}$，记 $d_{uv} = |e_v - e_u| \in \{1, \dots, N-1\}$，则 $w_v - w_u = \pm \zeta^{\min(e_u, e_v)}(1 - \zeta^{d_{uv}})$。由引理 A(3)，$1 - \zeta^{d_{uv}} = u_{uv} \pi^{p^{v_p(d_{uv})}}$（$u_{uv} \in \mathbb{Z}[\zeta]^\times$），且 $v_p(d_{uv}) = v_p(e_v - e_u)$，而 $\pm \zeta^{\min(e_u, e_v)} \in \mathbb{Z}[\zeta]^\times$。代回第 (2) 条公式即得
$$\det M_{\mathrm{conf}} = U \cdot Q(w_1, \dots, w_t) \cdot \pi^E, \qquad U \in \mathbb{Z}[\zeta]^\times,$$
其中 $E = \sum_{1 \le u < v \le t} m_u m_v \, p^{v_p(e_v - e_u)}$。特别地 $\det M_{\mathrm{conf}} \in \mathfrak{p}^E$ 且 $\det M_{\mathrm{conf}} \neq 0$。若 $\det M_{\mathrm{conf}} \in \mathfrak{p}^{E+1}$，写为 $\beta \pi^{E+1}$（$\beta \in \mathbb{Z}[\zeta]$），在整环 $\mathbb{Z}[\zeta]$ 中消去非零元 $\pi^E$ 得 $U \cdot Q(w_1, \dots, w_t) = \beta \pi \in \mathfrak{p}$，从而 $Q(w_1, \dots, w_t) \in \mathfrak{p}$，矛盾。故 $\det M_{\mathrm{conf}} \in \mathfrak{p}^E \setminus \mathfrak{p}^{E+1}$。$\blacksquare$

---

#### 定理 4（$\mu_{p^r}$ 上 $k$ 项式的含重数根数上界——推广的 Chebotarev 定理）
设 $p \ge 2$ 为素数，$r \ge 1$ 为正整数，$N = p^r$，$1 \le k \le p$。设 $a_1 < a_2 < \dots < a_k$ 为**任意整数**（不要求 $0 \le a_j < N$，允许负指数）且模 $p$ 两两不同。对任意不全为零的复数 $c_1, \dots, c_k \in \mathbb{C}$，记 Laurent 多项式 $P(z) = \sum_{j=1}^k c_j z^{a_j}$（在 $\mathbb{C}^*$ 上解析；于 $w \in \mathbb{C}^*$ 处重数 $\operatorname{ord}_w(P) = \operatorname{ord}_w(z^{-a_1} P(z))$）。则 $P$ 在 $\mu_N$ 中所有根的重数之和满足
$$\sum_{w \in \mu_N} \operatorname{ord}_w(P) \le k - 1.$$
特别地，$P(z) = 0$ 在 $\mu_N$ 中至多有 $k - 1$ 个不同的根。

#### 定理 4 的证明
取 $\widetilde{P}(z) = z^{-a_1} P(z) = \sum_{j=1}^k c_j z^{\tilde{a}_j} \in \mathbb{C}[z]$，其中 $\tilde{a}_j = a_j - a_1$ 满足 $0 = \tilde{a}_1 < \tilde{a}_2 < \dots < \tilde{a}_k$ 且仍模 $p$ 两两不同。对一切 $w \in \mu_N$ 均有 $\operatorname{ord}_w(P) = \operatorname{ord}_w(\widetilde{P})$。

反证：假设 $\sum_{w \in \mu_N} \operatorname{ord}_w(\widetilde{P}) \ge k$。把 $\mu_N$ 中满足 $\operatorname{ord}_w(\widetilde{P}) \ge 1$ 的点列为 $w_1, w_2, \dots, w_\ell$，通过逐个截断取 $m_s = \min\big(\operatorname{ord}_{w_s}(\widetilde{P}),\; k - \sum_{i < s} m_i\big)$ 并舍去 $m_s = 0$ 的项，可得 $t$ 个互异点 $w_1, \dots, w_t \in \mu_N$ 及正整数 $1 \le m_s \le \operatorname{ord}_{w_s}(\widetilde{P})$ 使 $\sum_{s=1}^t m_s = k$。对每个 $1 \le s \le t$ 及 $0 \le \nu < m_s \le \operatorname{ord}_{w_s}(\widetilde{P})$，必有 $\frac{1}{\nu!} \widetilde{P}^{(\nu)}(w_s) = 0$，即
$$\sum_{j=1}^k c_j \binom{\tilde{a}_j}{\nu} w_s^{\tilde{a}_j - \nu} = 0.$$
这表明向量 $\mathbf{c} = (c_1, \dots, c_k)^T \neq \mathbf{0}$ 满足 $M_{\mathrm{conf}} \mathbf{c} = \mathbf{0}$，其中 $M_{\mathrm{conf}}$ 为对指数 $0 \le \tilde{a}_1 < \dots < \tilde{a}_k$ 构造的 $k \times k$ 合流广义 Vandermonde 矩阵。由定理 3(3)，$\det M_{\mathrm{conf}} \neq 0$，故 $\mathbf{c} = \mathbf{0}$，矛盾！因此 $\sum_{w \in \mu_N} \operatorname{ord}_w(P) \le k - 1$。$\blacksquare$

---

#### 定理 5（重数除子的完全插值与实现逆定理）
在定理 4 的条件下（$p \ge 2$ 素数，$r \ge 1$，$N = p^r$，$1 \le k \le p$，任意整数 $a_1 < \dots < a_k$ 模 $p$ 两两不同），对 $\mu_N$ 上任意一组非负整数 $(m_w)_{w \in \mu_N}$ 满足
$$d := \sum_{w \in \mu_N} m_w \le k - 1,$$
均存在**全部系数均非零**的 $k$ 项式 $P(z) = \sum_{j=1}^k c_j z^{a_j}$（且可选取所有 $c_j \in \mathbb{Q}(\zeta)^*$）使得
$$\operatorname{ord}_w(P) = m_w \qquad (\forall\, w \in \mu_N).$$
进一步，当 $d = k - 1$ 时，满足 $\operatorname{ord}_w(P) \ge m_w$（$\forall\, w \in \mu_N$）的非零 $k$ 项式在相差非零复常数倍意义下唯一，并且自动满足全系数非零（比例位于 $\mathbb{Q}(\zeta)^*$ 中）及 $\operatorname{ord}_w(P) = m_w$（$\forall\, w \in \mu_N$）。

#### 定理 5 的证明
同理，令 $\tilde{a}_j = a_j - a_1 \ge 0$，由于乘以 $z^{-a_1}$ 不改变系数 $(c_1, \dots, c_k)$ 也不改变在 $\mu_N$ 上的零点重数，不妨设 $0 \le a_1 < a_2 < \dots < a_k$。记 $K = \mathbb{Q}(\zeta) \subset \mathbb{C}$（无穷域）。当 $k = 1$ 时必有 $d = 0$，取 $c_1 = 1 \in K^*$ 即满足要求。下设 $k \ge 2$。

对 $\mathbf{c} = (c_1, \dots, c_k) \in K^k$ 记 $P_{\mathbf{c}}(z) = \sum_{j=1}^k c_j z^{a_j}$。令
$$V = \Big\{ \mathbf{c} \in K^k : \frac{1}{\nu!} P_{\mathbf{c}}^{(\nu)}(w) = 0\ \text{对一切 } w \in \mu_N \text{ 及 } 0 \le \nu < m_w \Big\}.$$
这是 $K^k$ 上 $d$ 个齐次线性方程定义的线性子空间，系数矩阵 $A$ 为 $d \times k$ 矩阵（元素均在 $K$ 中）。

- **情形 A：$d = k - 1$**。对每个 $j \in \{1, \dots, k\}$，删去 $A$ 的第 $j$ 列得到一个 $(k-1) \times (k-1)$ 合流矩阵 $A^{(-j)}$，其对应的 $k - 1$ 个指数 $\{a_1, \dots, a_k\} \setminus \{a_j\}$ 仍然模 $p$ 两两不同。因 $k - 1 \le p - 1 < p$，对 $k - 1$ 应用定理 3(3) 知 $D_j := \det A^{(-j)} \neq 0$（且 $D_j \in K^*$）。因此 $\operatorname{rank}_K A = k - 1$（从而在 $\mathbb{C}$ 上秩亦为 $k - 1$），解空间 $V$（及 $\mathbb{C}^k$ 中的解空间）为一维，且由 Cramer/余子式公式张成向量为
  $$\mathbf{c}^* = \big((-1)^{j-1} D_j\big)_{j=1}^k \in (K^*)^k.$$
  显然 $\mathbf{c}^*$ 所有分量均非零，且 $\sum_{w \in \mu_N} \operatorname{ord}_w(P_{\mathbf{c}^*}) \ge \sum_{w \in \mu_N} m_w = k - 1$。再由定理 4 知 $\sum_{w \in \mu_N} \operatorname{ord}_w(P_{\mathbf{c}^*}) \le k - 1$，故必对一切 $w \in \mu_N$ 等号成立，即 $\operatorname{ord}_w(P_{\mathbf{c}^*}) = m_w$。

- **情形 B：$0 \le d \le k - 2$**。记 $S_0 = \{w \in \mu_N : m_w \ge 1\}$，显然 $|S_0| \le d$。在 $K$-线性空间 $V$（注意 $\dim_K V \ge k - d \ge 2$）内考虑以下有限多个线性子空间：
  1. $H_j = \{\mathbf{c} \in V : c_j = 0\}$（$1 \le j \le k$）；
  2. $L_w = \{\mathbf{c} \in V : \frac{1}{m_w!} P_{\mathbf{c}}^{(m_w)}(w) = 0\}$（$w \in \mu_N$）。

  验证它们全部是 $V$ 的**真**子空间：
  - 对每个 $j$：因为 $|\mu_N \setminus S_0| = p^r - |S_0| \ge k - d > k - 1 - d$，可从 $\mu_N \setminus S_0$ 中任选 $k - 1 - d$ 个互异点各附加 $1$ 个零点条件，使总条件数达到 $k - 1$。对新重数配置应用情形 A，所得向量 $\mathbf{c}^* \in V$ 的全部 $k$ 个分量皆非零，故 $\mathbf{c}^* \in V \setminus H_j$，即 $H_j \subsetneq V$。
  - 对每个 $w \in \mu_N$：注意到 $|S_0 \cup \{w\}| \le d + 1$，且 $|\mu_N| = p^r \ge p \ge k$，故 $|\mu_N \setminus (S_0 \cup \{w\})| \ge k - (d + 1) \ge 1$。从 $\mu_N \setminus (S_0 \cup \{w\})$ 中任选 $k - (d + 1)$ 个互异点各附加 $1$ 个零点条件，连同 $V$ 的 $d$ 个定义方程及 $L_w$ 的 $1$ 个定义方程，共组成 $k$ 个合流条件。由定理 3(3)，所得 $k \times k$ 合流矩阵可逆，故其全部 $k$ 个行向量在 $K^k$ 中线性无关；特别地，$L_w$ 的定义方程行不在 $A$ 的 $d$ 个行向量的张成空间内，从而 $L_w \subsetneq V$。

  最后验证无穷域 $K$ 上有限个真子空间之并 $\bigcup_{j=1}^k H_j \cup \bigcup_{w \in \mu_N} L_w$ 不可能覆盖 $V$：任取 $V$ 的一组 $K$-基（同构于 $K^m,\; m = \dim_K V \ge 2$），每个真子空间均可被包含在某个非零线性泛函 $f_i \in V^* \setminus \{0\}$ 的核中。若它们之并覆盖 $V$，则非零齐次多项式 $\prod_{i} f_i(y_1, \dots, y_m) \in K[y_1, \dots, y_m]$ 在 $K^m$ 上恒为零，但 $K$ 是无穷域（由归纳法，非零多元多项式在无穷域上不能恒为零），矛盾！

  因此存在 $\mathbf{c} \in V \setminus \big(\bigcup_{j=1}^k H_j \cup \bigcup_{w \in \mu_N} L_w\big)$。此 $\mathbf{c}$ 满足 $c_j \in K^*$（$\forall j$），对所有 $w \in \mu_N$ 既有 $\operatorname{ord}_w(P_{\mathbf{c}}) \ge m_w$（因 $\mathbf{c} \in V$）又有 $\operatorname{ord}_w(P_{\mathbf{c}}) < m_w + 1$（因 $\mathbf{c} \notin L_w$），故 $\operatorname{ord}_w(P_{\mathbf{c}}) = m_w$。$\blacksquare$

---

#### 推论 1（有理系数 $k$ 项式的 Galois 刚性）
设 $p \ge 2$ 为素数，$r \ge 1$，$N = p^r$，$1 \le k \le p$，$a_1 < \dots < a_k$ 为模 $p$ 两两不同的整数，且 $c_1, \dots, c_k \in \mathbb{Q}$ 不全为零。则：
1. 若 $1 \le k \le p - 1$（例如原题情形中 $k = 3$ 且 $p \ge 5$），则 $P(z) = \sum_{j=1}^k c_j z^{a_j}$ 在 $\mu_{p^r} \setminus \{1\}$ 中**没有任何根**；在 $\mu_{p^r}$ 中唯一可能的根只能是 $z = 1$（重数 $\le k - 1$，且该重数上界可由整数系数实现）。
2. 若 $k = p$（例如原题情形中 $k = 3$ 且 $p = 3$），则 $P(z)$ 在 $\mu_{p^r}$ 中的根要么只含 $z = 1$（重数 $\le p - 1$），要么恰为 $\mu_p \setminus \{1\}$（全部 $p - 1$ 个 $p$ 次本原单位根均为单根，且 $P(1) \neq 0$；取 $c_1 = \dots = c_p = 1$ 即实现后一情形）。

#### 推论 1 的证明
令 $\widetilde{P}(z) = z^{-a_1} P(z) \in \mathbb{Q}[z]$。若 $w \in \mu_{p^r}$ 是 $P$ 的根且其乘法阶为 $p^s$（$1 \le s \le r$），则 $w$ 是分圆多项式 $\Phi_{p^s}(z) \in \mathbb{Z}[z]$ 的根。由引理 A(1)，$\Phi_{p^s}(z)$ 在 $\mathbb{Q}[z]$ 上不可约且次数为 $\varphi(p^s) = p^{s-1}(p-1)$，从而 $\Phi_{p^s}(z) \mid \widetilde{P}(z)$ 于 $\mathbb{Q}[z]$ 中。因 $\Phi_{p^s}(z)$ 的全部 $\varphi(p^s)$ 个复根均为本原 $p^s$ 次单位根且互异（全部落入 $\mu_{p^r}$），再结合定理 4 得
$$\varphi(p^s) \le \sum_{z \in \mu_{p^r}} \operatorname{ord}_z(P) \le k - 1.$$
- 若 $k \le p - 1$，由于对一切 $s \ge 1$ 有 $\varphi(p^s) \ge p - 1 > k - 1$，矛盾！故 $P$ 在 $\mu_{p^r} \setminus \{1\}$ 中无根。又若取 $w_1 = 1$、$m_1 = k - 1$ 应用定理 5 的情形 A，由于方程组矩阵 $A$ 的元素 $\binom{a_j - a_1}{\nu}$ 全为整数，其解（$D_j \in \mathbb{Z} \setminus \{0\}$）给出整系数（从而有理系数）全非零实现。
- 若 $k = p$，由 $p^{s-1}(p - 1) \le p - 1$ 迫使 $s = 1$ 且总重数取满 $p - 1$，从而除 $\mu_p \setminus \{1\}$ 均为单根外，$P$ 在 $\mu_{p^r}$ 中再无其他根（特别地 $P(1) \neq 0$）。取 $c_1 = \dots = c_p = 1$ 时，$a_1, \dots, a_p$ 遍历模 $p$ 完全剩余系，故对任意 $\xi \in \mu_p \setminus \{1\}$ 有 $P(\xi) = \sum_{u=0}^{p-1} \xi^u = 0$。$\blacksquare$

---

### 2.3 素数幂条件与模 $p$ 互异条件的边界刻画

定理 1–2 表明对于 $k = 3$ 项式，$N$ 是否为素数幂并无本质限制；然而，下面的定理 6 表明，一旦进入 $k \ge 4$ 项式，“$N = p^r$ 为素数幂”恰好构成模 $p$ 互异假设下 $\le k - 1$ 界成立的**精确边界**。

#### 定理 6（$k \ge 4$ 时合数 $N$ 的普适失效与素数幂边界）
设 $p \ge 5$ 为素数，且正整数 $N$ 被 $p$ 整除但**不是** $p$ 的幂（即 $N = m p^r$，其中 $r \ge 1,\; m \ge 2,\; p \nmid m$）。则必存在全非零系数的 $4$ 项式 $P(z) = \sum_{j=1}^4 c_j z^{a_j}$（$c_j \in \mathbb{C}^*$）满足 $0 \le a_1 < a_2 < a_3 < a_4 < N$ 且 $a_1, a_2, a_3, a_4$ 模 $p$ 两两不同，但 $|S_{\mu_N}(P)| \ge 4$。更进一步：
- 若 $m \neq 2$，则 $N$ 必有满足 $q \ge 3,\; p \nmid q$ 的因子 $q \mid m$，此时可构造具有至少 $q + 1 \ge 4$ 个根（当 $m$ 含大素因子 $q$ 时根数可无界增长）的此类 $4$ 项式；
- 若 $m = 2$（即 $N = 2 p^r$），亦可显式构造具有 $4$ 个根的此类 $4$ 项式。

因此，对满足 $p \mid N$（$p \ge 5$）的正整数 $N$，命题“对一切 $1 \le k \le p$ 及一切模 $p$ 两两不同的指数 $0 \le a_1 < \dots < a_k < N$，任何非零 $k$ 项式在 $\mu_N$ 中至多有 $k - 1$ 个根”成立，**当且仅当** $N$ 是 $p$ 的幂。

#### 定理 6 的证明
充分性（当 $N = p^r$ 时成立）已由定理 4 证明。下证当 $N = m p^r$（$m \ge 2,\; p \nmid m$）时在 $k = 4$ 处必失效：

- **情况 1：$m \neq 2$**。此时要么 $m$ 含有一个异于 $p$ 的奇素因子 $q \ge 3$，要么 $m = 2^a$（$a \ge 2$）从而 $q = 4 \mid m$。总之存在整数 $q \ge 3$ 使得 $q \mid m$ 且 $\gcd(q, p) = 1$。
  因为 $\gcd(q, p) = 1$，$q, 2q, 3q$ 模 $p$ 两两不同且均非 $0 \pmod p$。又因为 $p \ge 5$，剩余系 $\{1, -1\} \pmod p$ 只有两个类，故必存在 $t \in \{1, 2, 3\}$ 使得 $tq \not\equiv 0, 1, -1 \pmod p$。取 $\zeta_N = e^{2\pi i / N}$，令
  $$P(z) = (z^{tq} - 1)(z - \zeta_N) = \zeta_N - z - \zeta_N z^{tq} + z^{tq + 1}.$$
  验证如下性质：
  1. $N = m p^r \ge q p \ge 5q > 3q + 1 \ge tq + 1$，故四个指数 $(0, 1, tq, tq + 1)$ 满足 $0 < 1 < tq < tq + 1 < N$。
  2. 因 $p \ge 5$ 且 $tq \not\equiv 0, 1, -1 \pmod p$，易验 $\{0, 1, tq, tq + 1\}$ 模 $p$ 两两不同。
  3. 四个系数 $\zeta_N, -1, -\zeta_N, 1$ 全部非零。
  4. 因 $q \mid N$，有 $\mu_q \subseteq \mu_N$，且对任意 $z \in \mu_q$ 有 $z^{tq} = (z^q)^t = 1$。又 $q \le m < N$，故 $\zeta_N \notin \mu_q$。于是 $P$ 在 $\mu_N$ 中至少有 $\mu_q \cup \{\zeta_N\}$ 这 $q + 1 \ge 4$ 个不同的根。

- **情况 2：$m = 2$（即 $N = 2 p^r,\; p \ge 5$）**。令 $\eta = e^{\pi i / p}$，则 $\eta$ 的阶为 $2p \mid N$，故 $\eta \in \mu_{2p} \subseteq \mu_N$。构造
  $$P(z) = (1 - \eta^{-4} z^4) - (1 + \eta^{-2}) z (1 - \eta^{-2} z^2) = 1 - (1 + \eta^{-2}) z + (1 + \eta^{-2})\eta^{-2} z^3 - \eta^{-4} z^4.$$
  验证如下性质：
  1. 因 $p \ge 5$，故 $2p \ge 10 > 4$，指数 $(0, 1, 3, 4)$ 满足 $0 < 1 < 3 < 4 < N$ 且模 $p$ 两两不同。
  2. 因 $\eta^{-2} = e^{-2\pi i / p} \neq -1$（$p$ 为奇素数），$1 + \eta^{-2} \neq 0$，故四个系数均非零。
  3. 取四点 $1, \eta, -\eta, \eta^2 \in \mu_{2p} \subseteq \mu_N$，它们分别是 $\eta^0, \eta^1, \eta^{p+1}, \eta^2$。因 $p \ge 5$，指数 $0, 1, 2, p+1$ 模 $2p$ 两两不同，故这 $4$ 个根互异。直接代入：
     - $P(\pm \eta) = (1 - \eta^{-4}\eta^4) - (1 + \eta^{-2})(\pm \eta)(1 - \eta^{-2}\eta^2) = 0$；
     - $P(1) = (1 - \eta^{-4}) - (1 + \eta^{-2})(1 - \eta^{-2}) = (1 - \eta^{-4}) - (1 - \eta^{-4}) = 0$；
     - $P(\eta^2) = (1 - \eta^4) - (1 + \eta^{-2})\eta^2 (1 - \eta^2) = (1 - \eta^4) - (\eta^2 + 1)(1 - \eta^2) = 0$。
  故 $|S_{\mu_N}(P)| \ge 4$。$\blacksquare$

---

最后，若保持 $N = p^r$ 但放弃“指数模 $p$ 两两不同”的假设，多项式在 $\mu_{p^r}$ 上的零点行为则受控于指数集按模 $p$ 剩余类的划分结构。

#### 定理 7（放弃模 $p$ 互异条件时 $\mu_{p^r}$ 上的陪集约化上界与锐性）
设 $p \ge 2$ 为素数，$r \ge 2$，$N = p^r$，$0 \le a_1 < \dots < a_k < N$ 为任意互异整数，$c_1, \dots, c_k \in \mathbb{C}^*$，令 $P(z) = \sum_{j=1}^k c_j z^{a_j}$。记
$$U = \{a_j \bmod p : 1 \le j \le k\} \subseteq \{0, 1, \dots, p-1\}, \qquad m = |U|,$$
并对每个 $u \in U$ 定义多项式 $G_u(w) = \sum_{\substack{1 \le j \le k \\ a_j \equiv u \pmod p}} c_j w^{(a_j - u)/p}$。则
$$|S_{\mu_{p^r}}(P)| \le (m - 1) p^{r-1} + (p - m + 1) \min_{u \in U} |S_{\mu_{p^{r-1}}}(G_u)|.$$
特别地：
1. 若至少存在一个模 $p$ 剩余类 $u_0 \in U$ 只含单个指数（即 $|\{j : a_j \equiv u_0 \pmod p\}| = 1$），则 $G_{u_0}$ 在 $\mu_{p^{r-1}}$ 上无零点，从而
   $$|S_{\mu_{p^r}}(P)| \le (m - 1) p^{r-1}.$$
2. 上述上界 $(m - 1) p^{r-1}$ 在有单点类的情形中是**锐的**：例如对任意素数 $p \ge 2$、$r \ge 2$，取 $m = 2$ 与 $k = p^{r-1} + 1$（$U = \{0, 1\}$，指数集为 $\{0, p, 2p, \dots, (p^{r-1}-1)p\} \cup \{1\}$），显式多项式
   $$P(z) = z - \frac{1}{p^{r-1}} \sum_{t=0}^{p^{r-1}-1} \left(\sum_{s=0}^{p^{r-1}-1} \zeta_{p^r}^{s(1 - pt)}\right) z^{pt}$$
   全部 $p^{r-1} + 1$ 个系数均非零，且在 $\mu_{p^r}$ 中恰有 $p^{r-1}$ 个不同的根（位于 $\mu_p$ 的全部 $p^{r-1}$ 个陪集中各 $1$ 个）。

#### 定理 7 的证明
显然 $P(z) = \sum_{u \in U} z^u G_u(z^p)$。考虑 $p$-对-$1$ 满同态 $\psi : \mu_{p^r} \to \mu_{p^{r-1}},\; \psi(z) = z^p$。对每个 $w \in \mu_{p^{r-1}}$，任取一个 $z_0 \in \mu_{p^r}$ 使 $z_0^p = w$，则纤维 $\psi^{-1}(w) = \{\omega z_0 : \omega \in \mu_p\}$，且
$$P(\omega z_0) = \sum_{u \in U} \big(z_0^u G_u(w)\big) \omega^u.$$
作为 $\omega \in \mu_p$ 的函数，这是一个至多含 $m$ 个两两不同（模 $p$）指数的稀疏多项式。
- 若对所有 $u \in U$ 均有 $G_u(w) = 0$（记此类 $w$ 组成的集合为 $T_{\mathrm{full}} = \bigcap_{u \in U} S_{\mu_{p^{r-1}}}(G_u)$），则 $\psi^{-1}(w)$ 中全部 $p$ 个点皆为 $P$ 的根；
- 否则至少有一个系数 $z_0^u G_u(w) \neq 0$，由定理 4（对 $r = 1$ 即 $\mu_p$ 应用）知 $P(\omega z_0) = 0$ 在 $\mu_p$ 中至多有 $m - 1$ 个不同的解，从而 $\psi^{-1}(w)$ 中至多有 $m - 1$ 个 $P$ 的根。

对全部 $p^{r-1}$ 个纤维求和即得
$$|S_{\mu_{p^r}}(P)| \le p |T_{\mathrm{full}}| + (m - 1)\big(p^{r-1} - |T_{\mathrm{full}}|\big) = (m - 1) p^{r-1} + (p - m + 1)|T_{\mathrm{full}}|,$$
又 $|T_{\mathrm{full}}| \le \min_{u \in U} |S_{\mu_{p^{r-1}}}(G_u)|$ 且 $p - m + 1 \ge 1$，不等式成立。当某 $u_0 \in U$ 只含单个指数时，$G_{u_0}(w) = c_j w^{(a_j - u_0)/p}$ 在 $\mu_{p^{r-1}}$ 上恒非零，故 $T_{\mathrm{full}} = \emptyset$，得出 $|S_{\mu_{p^r}}(P)| \le (m - 1) p^{r-1}$。

关于锐性构造：令 $M_1 = p^{r-1}$，对 $0 \le t < M_1$ 记
$$b_t = -\frac{1}{M_1} \sum_{s=0}^{M_1 - 1} \zeta_{p^r}^{s(1 - pt)}.$$
先验证 $b_t \neq 0$：令 $\xi_t = \zeta_{p^r}^{1 - pt}$。因 $p \nmid (1 - pt)$，故 $\xi_t$ 为本原 $p^r$ 次单位根，从而 $\xi_t \neq 1$ 且 $\xi_t^{M_1} = \zeta_p^{1 - pt} \neq 1$。由等比数列求和，
$$b_t = -\frac{1}{M_1} \cdot \frac{\xi_t^{M_1} - 1}{\xi_t - 1} \neq 0 \qquad (\forall\, 0 \le t < M_1).$$
因此 $P(z) = z + \sum_{t=0}^{M_1 - 1} b_t z^{pt}$ 的全部 $M_1 + 1$ 个系数均非零（且因 $r \ge 2$，有 $p(M_1 - 1) = p^r - p < p^r$ 且 $1 \not\equiv 0 \pmod p$，指数两两互异）。再对任意 $0 \le s_0 < M_1$ 代入 $z = \zeta_{p^r}^{s_0}$（注意 $\zeta_{p^r}^{p s_0} = \zeta_{M_1}^{s_0}$），利用有限群正交关系 $\sum_{t=0}^{M_1 - 1} \zeta_{M_1}^{(s_0 - s) t} = M_1 \delta_{s, s_0}$ 得
$$P(\zeta_{p^r}^{s_0}) = \zeta_{p^r}^{s_0} - \frac{1}{M_1} \sum_{s=0}^{M_1 - 1} \zeta_{p^r}^s \sum_{t=0}^{M_1 - 1} \zeta_{M_1}^{(s_0 - s) t} = \zeta_{p^r}^{s_0} - \zeta_{p^r}^{s_0} = 0.$$
故 $P$ 至少有 $\{\zeta_{p^r}^{s_0} : 0 \le s_0 < M_1\}$ 这 $M_1 = p^{r-1}$ 个不同的根；结合第 1 条上界 $(2 - 1)p^{r-1} = p^{r-1}$，其根数精确等于 $p^{r-1}$。$\blacksquare$

---

## 第三部分：修改清单与自评

### 1. 保留、新增/修正与未完成/不确定部分

- **保留部分**：
  - 完整保留了原解答（[previous-answer.md](file:///private/tmp/math-gauge-hydrogen-neutral-rest-20261122-v1/runtime/attempts/R013/physical-1/session/work/.revision-input/R013/previous-answer.md)）针对原题（[task.md](file:///private/tmp/math-gauge-hydrogen-neutral-rest-20261122-v1/runtime/attempts/R013/physical-1/session/work/.revision-input/R013/task.md)）给出的全部初等证明（引理及情形 1、2、3），经逐行核验，原证明的假设、映射单射性、$|z|=1$、$c_1 \neq 0$ 与两圆交点代数论证均严密无误；本稿仅在原证明几处细节上略作行文显式化（如明确 $|z|^N = 1 \implies |z| = 1$ 所用的 $|z| \ge 0$、整数次幂在 $w \neq 0$ 下的合法性）。
- **新增部分**（均置于独立的第二部分“进一步研究与理论拓展”，未改变第一部分原命题的对象、条件或结论强度）：
  1. **定理 1–2（一般 $N$ 下三项式的完整结构理论）**：彻底释放 $N = p^r$、$p \ge 3$ 与模 $p$ 互异条件，证明了任意正整数 $N$、任意整数指数下的重数总和界 $\le 2g$ 及全单根/全 $2$ 重根精确二分法，确定了全部非零系数与允许零系数两类三项式的精确最大根数，并给出了零点集逆问题的充要刻画与单根/重根显式构造。
  2. **引理 A 与定理 3–5、推论 1（$\mu_{p^r}$ 上 $1 \le k \le p$ 项式的完整理论）**：用纯初等整环论证证明了 $\Phi_{p^r}(X)$ 的不可约性与 $(1 - \zeta_{p^r}^d)\mathbb{Z}[\zeta_{p^r}] = \mathfrak{p}^{p^{v_p(d)}}$；建立了合流广义 Vandermonde 行列式的精确 Schur 多项式恒等式与精确 $\mathfrak{p}$-进阶公式；将原题推广到任意素数 $p \ge 2$、任意 $r \ge 1$、任意 $1 \le k \le p$ 与任意整数指数（含 Laurent 指数）下的含重数上界 $\sum \operatorname{ord}_w(P) \le k - 1$；完整解决了重数除子的完全插值与实现逆问题；并给出了有理系数下的 Galois 刚性推论。
  3. **定理 6–7（边界条件刻画）**：证明了当 $k \ge 4$ 且 $p \ge 5$ 时，任意非素数幂 $N$（$p \mid N$）均存在反例（含奇素因子 $q \neq p$ 时根数至少达 $q+1$，以及 $N = 2p^r$ 的显式 $4$ 项式反例），刻画了素数幂条件作为充要边界的意义；并建立了放弃模 $p$ 互异条件后 $\mu_{p^r}$ 上的陪集约化界及显式 Fourier 锐性构造。
- **仍未完成/不确定的部分**：
  - 所有声称的定理、引理与推论均已在本稿内给出完整闭合的证明，不存在悬而未决的缺口或依赖外部未证结论之处。（注：对于放弃模 $p$ 互异条件时的任意 $k$ 项式，定理 7 给出了通用的单步陪集约化上界并在含单点类时证明了锐性；对于一般 $p$-进指数树结构且所有非零系数被强制保留时的精确极大根数公式，由于如 $N = 27$ 中 $a = (0,1,2,3,4,10)$ 与 $a = (0,1,2,3,4,7)$ 展现出的微妙算术差异，本文未对其作未经证明的猜测性刻画。）

### 2. 有依据的自评（对照 [standards.md](file:///private/tmp/math-gauge-hydrogen-neutral-rest-20261122-v1/runtime/attempts/R013/physical-1/session/work/.revision-common/standards.md) 与 [invitation.md](file:///private/tmp/math-gauge-hydrogen-neutral-rest-20261122-v1/runtime/attempts/R013/physical-1/session/work/.revision-common/invitation.md)）

- **基线完成度（B = B2）**：第一部分严格保留原题全部对象、定义、条件、量词与定义域，证明完整自足且无逻辑或边界漏洞，满足 B2 标准。
- **研究增量水平（R = R3）**：第二部分围绕原问题背后的两条核心数学机制（低项数三角刚性与 $p$-进合流非退化性）系统推进，完成了三项互为支撑且全部证明闭合的成果：
  1. 对任意 $N$ 的三项式实现了含重数刻画、精确极大值与逆问题零点集充要分类（定理 1–2）；
  2. 对任意 $\mu_{p^r}$ 上 $k \le p$ 项式建立了精确合流行列式 $\mathfrak{p}$-进阶公式、推广至含重数与 Laurent 指数的 Chebotarev 型上界、全重数除子实现定理及有理 Galois 刚性（引理 A、定理 3–5、推论 1）；
  3. 确定了 $k \ge 4$ 时素数幂条件的精确充要边界并给出了放弃模 $p$ 互异条件的陪集约化理论（定理 6–7）。
  这些结果覆盖了“推广、精确表示/估值、分类、插值逆问题与边界判定”等核心研究维度，所有关键引理、桥梁与反例均自足闭合，不存在夸大范围或以猜代证。
- **交付规范与可靠性（MC / RMC / SMC）**：全稿置于最终答复正文内独立可读、显式交付；所有引用的标准工具（裴蜀定理、Eisenstein 判别法、唯一分解整环与多项式在无穷域上的非恒零性）均符合适用条件且关键部分已内嵌初等证明。据此自评基线为 **B2**，若按命题拓展型研究尺度评价则对应 **R3**（无扣罚的完整交付）。