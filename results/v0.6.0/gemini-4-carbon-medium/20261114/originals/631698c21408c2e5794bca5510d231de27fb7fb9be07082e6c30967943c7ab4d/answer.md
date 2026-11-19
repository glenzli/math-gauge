{}
这个结论是**正确**的。下面给出完整证明。

---

### 证明

采用反证法。假设存在三个两两不同的 $N$ 次单位根 $z_1, z_2, z_3$，使得
$$P(z_1) = P(z_2) = P(z_3) = 0.$$

#### 第一步：归结为三阶行列式为零

令 $b_2 = a_2 - a_1$，$b_3 = a_3 - a_1$。由 $0 \le a_1 < a_2 < a_3 < N$ 且 $a_1, a_2, a_3$ 模 $p$ 两两不同，可知 $b_2$、$b_3$、$b_3 - b_2 = a_3 - a_2$ 均不被素数 $p$ 整除。因为 $N = p^r$，所以
$$\gcd(b_2, N) = \gcd(b_3, N) = \gcd(b_3 - b_2, N) = 1.$$

由于单位根均非零，将 $P(z_i) = 0$（$i=1,2,3$）两边同除以 $z_i^{a_1}$，并记
$$w_2 = \frac{z_2}{z_1}, \quad w_3 = \frac{z_3}{z_1}, \qquad c_1' = c_1, \quad c_2' = c_2 z_1^{b_2}, \quad c_3' = c_3 z_1^{b_3}.$$
因为 $(c_1, c_2, c_3) \neq (0, 0, 0)$ 且 $z_1 \neq 0$，所以 $(c_1', c_2', c_3') \neq (0, 0, 0)$，且满足齐次线性方程组
$$\begin{cases}
c_1' + c_2' + c_3' = 0, \\
c_1' + c_2' w_2^{b_2} + c_3' w_2^{b_3} = 0, \\
c_1' + c_2' w_3^{b_2} + c_3' w_3^{b_3} = 0.
\end{cases}$$
该齐次线性方程组有非零解，故其系数矩阵的行列式必为零：
$$\det \begin{pmatrix}
1 & 1 & 1 \\
1 & w_2^{b_2} & w_2^{b_3} \\
1 & w_3^{b_2} & w_3^{b_3}
\end{pmatrix}
= (w_2^{b_2} - 1)(w_3^{b_3} - 1) - (w_2^{b_3} - 1)(w_3^{b_2} - 1) = 0.$$
展开整理得
$$w_2^{b_2} w_3^{b_3} + w_2^{b_3} + w_3^{b_2} - w_2^{b_3} w_3^{b_2} - w_3^{b_3} - w_2^{b_2} = 0. \tag{1}$$

---

#### 第二步：利用分圆多项式的不可约性刻画系数

取本原 $N$ 次单位根 $\zeta = e^{2\pi i / N}$。由于 $z_1, z_2, z_3$ 是两两不同的 $N$ 次单位根，$1, w_2, w_3$ 也是两两不同的 $N$ 次单位根，从而存在唯一的整数 $x, y \in \{1, 2, \dots, N-1\}$（且 $x \neq y$），使得 $w_2 = \zeta^x$，$w_3 = \zeta^y$。

分别取
$$b_2 x + b_3 y, \quad b_3 x, \quad b_2 y$$
模 $N$ 的最小非负剩余，记为 $\alpha_1, \alpha_2, \alpha_3 \in \{0, 1, \dots, N-1\}$；并取
$$b_3 x + b_2 y, \quad b_3 y, \quad b_2 x$$
模 $N$ 的最小非负剩余，记为 $\beta_1, \beta_2, \beta_3 \in \{0, 1, \dots, N-1\}$。由 $\zeta^N = 1$ 及 $(1)$ 式可知，整系数多项式
$$F(T) = T^{\alpha_1} + T^{\alpha_2} + T^{\alpha_3} - T^{\beta_1} - T^{\beta_2} - T^{\beta_3} = \sum_{e=0}^{N-1} d_e T^e \in \mathbb{Z}[T]$$
满足 $F(\zeta) = 0$。

考察第 $p^r$ 个分圆多项式
$$\Phi_{p^r}(T) = \frac{T^{p^r} - 1}{T^{p^{r-1}} - 1} = \sum_{m=0}^{p-1} T^{m p^{r-1}}.$$
注意令 $T = 1 + U$ 时，在 $(\mathbb{Z}/p\mathbb{Z})[U]$ 中有
$$\Phi_{p^r}(1 + U) = \frac{(1+U)^{p^r} - 1}{(1+U)^{p^{r-1}} - 1} \equiv \frac{U^{p^r}}{U^{p^{r-1}}} = U^{(p-1)p^{r-1}} \pmod p,$$
且常数项 $\Phi_{p^r}(1) = p$ 不被 $p^2$ 整除，由 Eisenstein 判别法知 $\Phi_{p^r}(T)$ 在 $\mathbb{Q}[T]$ 中不可约。又因 $\zeta^{p^r} = 1$ 而 $\zeta^{p^{r-1}} = e^{2\pi i/p} \neq 1$，有 $\Phi_{p^r}(\zeta) = 0$，故 $\Phi_{p^r}(T)$ 是 $\zeta$ 在 $\mathbb{Q}$ 上的极小多项式。

于是在 $\mathbb{Q}[T]$ 中 $\Phi_{p^r}(T) \mid F(T)$。由于 $\Phi_{p^r}(T)$ 是首一整系数多项式，商式 $Q(T) = F(T)/\Phi_{p^r}(T)$ 属于 $\mathbb{Z}[T]$。又 $\deg F \le p^r - 1$，而 $\deg \Phi_{p^r} = (p-1)p^{r-1} = p^r - p^{r-1}$，故 $Q(T)$ 的次数不超过 $p^{r-1} - 1$（当 $Q(T)=0$ 时亦可视为此形式），可设
$$Q(T) = \sum_{u=0}^{p^{r-1}-1} q_u T^u \quad (q_u \in \mathbb{Z}).$$
从而
$$F(T) = Q(T)\Phi_{p^r}(T) = \sum_{u=0}^{p^{r-1}-1} \sum_{m=0}^{p-1} q_u T^{u + m p^{r-1}}.$$
因为每个 $e \in \{0, 1, \dots, p^r - 1\}$ 都可唯一写成 $e = u + m p^{r-1}$（其中 $0 \le u < p^{r-1}$，$0 \le m < p$），对比 $T^e$ 的系数可得
$$d_{u + m p^{r-1}} = q_u \quad (\forall\, 0 \le u < p^{r-1},\; 0 \le m < p). \tag{2}$$

---

#### 第三步：证明 $F(T)$ 恒为零多项式

对每个 $e \in \{0, 1, \dots, N-1\}$，记
$$\mu_A(e) = |\{i \in \{1,2,3\} : \alpha_i = e\}|, \qquad \mu_B(e) = |\{j \in \{1,2,3\} : \beta_j = e\}|,$$
则 $d_e = \mu_A(e) - \mu_B(e) \le \mu_A(e)$，且 $\sum_{e=0}^{N-1} \mu_A(e) = \sum_{e=0}^{N-1} \mu_B(e) = 3$。结合 $(2)$ 式，对所有满足 $q_u > 0$ 的下标 $u$ 求和，有
$$p \sum_{u:\, q_u > 0} q_u = \sum_{u:\, q_u > 0} \sum_{m=0}^{p-1} d_{u + m p^{r-1}} = \sum_{e:\, d_e > 0} d_e \le \sum_{e=0}^{N-1} \mu_A(e) = 3. \tag{3}$$
同时，在 $F(T) = Q(T)\Phi_{p^r}(T)$ 中令 $T = 1$，由 $F(1) = 0$ 与 $\Phi_{p^r}(1) = p$ 可得
$$\sum_{u=0}^{p^{r-1}-1} q_u = Q(1) = 0. \tag{4}$$

分两种情形讨论：

- **情形 1：$p \ge 5$**。  
  由 $(3)$ 式得 $p \sum_{u:\, q_u > 0} q_u \le 3 < 5$。因 $q_u \in \mathbb{Z}$，必不存在满足 $q_u > 0$ 的 $u$。再结合 $(4)$ 式知对所有 $u$ 均有 $q_u = 0$，故 $F(T) = 0$。

- **情形 2：$p = 3$**。  
  若存在某个 $q_u \neq 0$，则由 $(3)$ 式 $3 \sum_{u:\, q_u > 0} q_u \le 3$ 与 $(4)$ 式可知，必有 $\sum_{u:\, q_u > 0} q_u = 1$ 且 $\sum_{u:\, q_u < 0} (-q_u) = 1$。即存在唯一的 $u_1, u_2 \in \{0, 1, \dots, 3^{r-1}-1\}$（$u_1 \neq u_2$），使得 $q_{u_1} = 1$，$q_{u_2} = -1$，且其余 $q_u = 0$。

  此时对每个 $m \in \{0, 1, 2\}$，有 $\mu_A(u_1 + m \cdot 3^{r-1}) \ge d_{u_1 + m \cdot 3^{r-1}} = 1$。由于 $\sum_{e=0}^{3^r - 1} \mu_A(e) = 3$，故必有
  $$\{\alpha_1, \alpha_2, \alpha_3\} = \{u_1, \; u_1 + 3^{r-1}, \; u_1 + 2 \cdot 3^{r-1}\}.$$
  同理，对每个 $m \in \{0, 1, 2\}$ 有 $\mu_B(u_2 + m \cdot 3^{r-1}) \ge -d_{u_2 + m \cdot 3^{r-1}} = 1$，故必有
  $$\{\beta_1, \beta_2, \beta_3\} = \{u_2, \; u_2 + 3^{r-1}, \; u_2 + 2 \cdot 3^{r-1}\}.$$
  将两个集合的元素分别求和：
  $$\alpha_1 + \alpha_2 + \alpha_3 = 3u_1 + 3 \cdot 3^{r-1} = 3u_1 + 3^r \equiv 3u_1 \pmod{3^r},$$
  $$\beta_1 + \beta_2 + \beta_3 = 3u_2 + 3 \cdot 3^{r-1} = 3u_2 + 3^r \equiv 3u_2 \pmod{3^r}.$$
  另一方面，由 $\alpha_i$ 和 $\beta_j$ 的定义，在模 $N = 3^r$ 下有
  $$\alpha_1 + \alpha_2 + \alpha_3 \equiv (b_2 x + b_3 y) + b_3 x + b_2 y = (b_2 + b_3)(x + y) \pmod{3^r},$$
  $$\beta_1 + \beta_2 + \beta_3 \equiv (b_3 x + b_2 y) + b_3 y + b_2 x = (b_2 + b_3)(x + y) \pmod{3^r}.$$
  比较可得 $3u_1 \equiv 3u_2 \pmod{3^r}$，即 $3^{r-1} \mid (u_1 - u_2)$。但 $0 \le u_1, u_2 < 3^{r-1}$，故必有 $u_1 = u_2$，与 $u_1 \neq u_2$ 矛盾。

综上，无论 $p \ge 5$ 还是 $p = 3$，多项式 $F(T)$ 都恒为零。

---

#### 第四步：导出矛盾

由 $F(T) = 0$ 得
$$T^{\alpha_1} + T^{\alpha_2} + T^{\alpha_3} = T^{\beta_1} + T^{\beta_2} + T^{\beta_3},$$
因此必有 $\alpha_2 \in \{\beta_1, \beta_2, \beta_3\}$。逐一检验这三种可能：

1. 若 $\alpha_2 = \beta_1$，则 $b_3 x \equiv b_3 x + b_2 y \pmod N$，即 $b_2 y \equiv 0 \pmod N$。由 $\gcd(b_2, N) = 1$ 得 $y \equiv 0 \pmod N$，与 $y \in \{1, 2, \dots, N-1\}$ 矛盾；
2. 若 $\alpha_2 = \beta_2$，则 $b_3 x \equiv b_3 y \pmod N$，即 $b_3(x - y) \equiv 0 \pmod N$。由 $\gcd(b_3, N) = 1$ 得 $x \equiv y \pmod N$，与 $x, y \in \{1, 2, \dots, N-1\}$ 且 $x \neq y$ 矛盾；
3. 若 $\alpha_2 = \beta_3$，则 $b_3 x \equiv b_2 x \pmod N$，即 $(b_3 - b_2)x \equiv 0 \pmod N$。由 $\gcd(b_3 - b_2, N) = 1$ 得 $x \equiv 0 \pmod N$，与 $x \in \{1, 2, \dots, N-1\}$ 矛盾。

三种情形均导出矛盾，因此假设不成立。故在全部 $N$ 次单位根中，满足 $P(z) = 0$ 的不同根至多有两个。 $\blacksquare$
