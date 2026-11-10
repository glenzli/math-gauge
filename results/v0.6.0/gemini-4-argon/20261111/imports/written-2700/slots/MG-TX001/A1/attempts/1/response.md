{}
这个结论是**正确**的。下面给出完整证明。

---

### 证明

用反证法。假设存在三个两两不同的 $N$ 次单位根 $z_1, z_2, z_3$（满足 $z_i^N = 1$，$i=1,2,3$），使得
$$P(z_i) = c_1 z_i^{a_1} + c_2 z_i^{a_2} + c_3 z_i^{a_3} = 0 \quad (i = 1, 2, 3),$$
其中复数 $c_1, c_2, c_3$ 不全为零。

#### 第一步：归约为行列式条件

记 $b = a_2 - a_1$，$d = a_3 - a_1$。由 $0 \le a_1 < a_2 < a_3 < N$ 可知 $1 \le b < d < N$。因为 $a_1, a_2, a_3$ 模 $p$ 两两不同，所以
$$b = a_2 - a_1, \qquad d = a_3 - a_1, \qquad b - d = a_2 - a_3$$
均不能被 $p$ 整除。

对 $i = 1, 2, 3$，令 $w_i = z_i / z_1$。由于 $z_1, z_2, z_3$ 是两两不同的 $N$ 次单位根，故 $w_1 = 1, w_2, w_3$ 也是两两不同的 $N$ 次单位根；特别地，$w_2 \neq 1$，$w_3 \neq 1$，且 $w_2 \neq w_3$。

在 $P(z_i) = 0$ 两边同乘 $z_i^{-a_1}$，得
$$c_1 + (c_2 z_1^b) w_i^b + (c_3 z_1^d) w_i^d = 0 \quad (i = 1, 2, 3).$$
因为 $z_1 \neq 0$ 且 $(c_1, c_2, c_3) \neq (0, 0, 0)$，所以 $(\tilde{c}_1, \tilde{c}_2, \tilde{c}_3) := (c_1, c_2 z_1^b, c_3 z_1^d) \neq (0, 0, 0)$ 是关于 $\tilde{c}_1, \tilde{c}_2, \tilde{c}_3$ 的齐次线性方程组
$$\begin{cases}
\tilde{c}_1 + \tilde{c}_2 + \tilde{c}_3 = 0, \\
\tilde{c}_1 + \tilde{c}_2 w_2^b + \tilde{c}_3 w_2^d = 0, \\
\tilde{c}_1 + \tilde{c}_2 w_3^b + \tilde{c}_3 w_3^d = 0
\end{cases}$$
的非零解。因此其系数矩阵的行列式必为零：
$$\det \begin{pmatrix}
1 & 1 & 1 \\
1 & w_2^b & w_2^d \\
1 & w_3^b & w_3^d
\end{pmatrix}
= (1 - w_2^b)(1 - w_3^d) - (1 - w_3^b)(1 - w_2^d) = 0.$$

---

#### 第二步：在 $x = 1 - w_2$ 与 $y = 1 - w_3$ 下展开

令 $x = 1 - w_2$，$y = 1 - w_3$。由 $1, w_2, w_3$ 两两不同可知：
$$x \neq 0, \qquad y \neq 0, \qquad y - x = w_2 - w_3 \neq 0.$$

对任意正整数 $k$，由二项式定理有
$$1 - (1 - u)^k = \sum_{m=1}^{k} (-1)^{m-1} \binom{k}{m} u^m = u \, g_k(u),$$
其中整系数多项式 $g_k(u) \in \mathbb{Z}[u]$ 定义为（约定当 $m > k$ 时 $\binom{k}{m} = 0$）：
$$g_k(u) = \sum_{m=0}^{k-1} \alpha_m^{(k)} u^m, \qquad \alpha_m^{(k)} = (-1)^m \binom{k}{m+1} \in \mathbb{Z}.$$
特别地，$\alpha_0^{(k)} = k$，$\alpha_1^{(k)} = -\binom{k}{2}$。

将 $1 - w_2^k = x g_k(x)$ 与 $1 - w_3^k = y g_k(y)$（$k \in \{b, d\}$）代入行列式等式，并约去非零因子 $xy$，得
$$g_b(x) g_d(y) - g_b(y) g_d(x) = 0.$$

将左边按多项式展开：
$$g_b(x) g_d(y) - g_b(y) g_d(x) = \sum_{m \ge 0} \sum_{n \ge 0} \alpha_m^{(b)} \alpha_n^{(d)} \bigl(x^m y^n - y^m x^n\bigr).$$
注意到对任意非负整数 $m, n$，$x^m y^n - y^m x^n$ 在 $\mathbb{Z}[x, y]$ 中都能被 $y - x$ 整除：
- 当 $m = n$ 时，$x^m y^n - y^m x^n = 0$；
- 当 $m \neq n$ 时，商式 $\dfrac{x^m y^n - y^m x^n}{y - x} \in \mathbb{Z}[x, y]$ 是关于 $x, y$ 的 $m + n - 1$ 次齐次整系数多项式。

因此，在 $g_b(x) g_d(y) - g_b(y) g_d(x) = 0$ 两边同除以 $y - x \neq 0$ 后：
1. **常数项**（即 $m + n - 1 = 0$，对应 $(m, n) = (0, 1)$ 与 $(1, 0)$ 的项）为
   $$M_0 := \alpha_0^{(b)} \alpha_1^{(d)} - \alpha_1^{(b)} \alpha_0^{(d)} = b\left(-\binom{d}{2}\right) - \left(-\binom{b}{2}\right)d = \frac{bd(b - d)}{2} \in \mathbb{Z};$$
2. **其余各项**均满足 $m + n \ge 2$，除以 $y - x$ 后的次数为 $m + n - 1 \ge 1$，因此每一项都至少含有一个因子 $x$ 或 $y$。

于是我们得到形如下式的等式：
$$M_0 + x A(x, y) + y B(x, y) = 0,$$
其中 $A(x, y), B(x, y) \in \mathbb{Z}[x, y]$ 是整系数多项式。

---

#### 第三步：利用分圆域（或分圆多项式）导出整除矛盾

设 $\zeta = e^{2\pi i / N}$ 为本原 $N$ 次单位根（$N = p^r$）。因为 $w_2, w_3$ 是不等于 $1$ 的 $N$ 次单位根，故存在整数 $1 \le u, v \le N - 1$ 使得 $w_2 = \zeta^u$，$w_3 = \zeta^v$。从而在环 $\mathbb{Z}[\zeta]$ 中：
$$x = 1 - \zeta^u = (1 - \zeta)\sum_{j=0}^{u-1} \zeta^j \in (1 - \zeta)\mathbb{Z}[\zeta],$$
$$y = 1 - \zeta^v = (1 - \zeta)\sum_{j=0}^{v-1} \zeta^j \in (1 - \zeta)\mathbb{Z}[\zeta].$$
由 $M_0 = -x A(x, y) - y B(x, y)$ 可知
$$M_0 \in (1 - \zeta)\mathbb{Z}[\zeta],$$
即存在整系数多项式 $Q(t) \in \mathbb{Z}[t]$，使得
$$M_0 = (1 - \zeta) Q(\zeta).$$

考察 $N = p^r$ 次分圆多项式
$$\Phi_{p^r}(t) = \frac{t^{p^r} - 1}{t^{p^{r-1}} - 1} = 1 + t^{p^{r-1}} + t^{2p^{r-1}} + \cdots + t^{(p-1)p^{r-1}} \in \mathbb{Z}[t].$$
显然 $\Phi_{p^r}(\zeta) = 0$，且 $\Phi_{p^r}(1) = p$。由熟知结论（对 $\Phi_{p^r}(s+1)$ 应用 Eisenstein 判别法），$\Phi_{p^r}(t)$ 在 $\mathbb{Q}[t]$ 上不可约，是 $\zeta$ 在 $\mathbb{Q}$ 上的首一极小多项式。

因为 $\zeta$ 是整系数多项式 $F(t) := M_0 - (1 - t)Q(t) \in \mathbb{Z}[t]$ 的根，所以 $\Phi_{p^r}(t)$ 在 $\mathbb{Q}[t]$ 中整除 $F(t)$。又因 $\Phi_{p^r}(t)$ 是首一整系数多项式，由带余除法可知商式 $H(t) = F(t) / \Phi_{p^r}(t)$ 也属于 $\mathbb{Z}[t]$，即
$$M_0 - (1 - t)Q(t) = \Phi_{p^r}(t) H(t).$$
在上式中取 $t = 1$，得
$$M_0 = \Phi_{p^r}(1) H(1) = p H(1).$$
由于 $H(1) \in \mathbb{Z}$，故 $p \mid M_0$，即
$$p \;\Big|\; \frac{bd(b - d)}{2}.$$

因为 $p \ge 3$ 是奇素数，$\gcd(p, 2) = 1$，所以 $p \mid bd(b - d)$。由素数的性质知 $p$ 必整除 $b = a_2 - a_1$、$d = a_3 - a_1$ 或 $b - d = a_2 - a_3$ 之一，这与 $a_1, a_2, a_3$ 模 $p$ 两两不同矛盾！

因此假设不成立，在全部 $N$ 次单位根中，满足 $P(z) = 0$ 的不同根至多有两个。$\blacksquare$
