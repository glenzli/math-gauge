{}
下面给出全部三个目标的完整解答与严格证明。

---

## 0. 全局记号与二次扩张环的基本性质

固定正整数 $r, n_1, \dots, n_r$，令
\[
d = \sum_{i=1}^r n_i, \qquad \kappa = \sum_{i=1}^r \binom{n_i}{2} = \frac{1}{2}\sum_{i=1}^r n_i(n_i-1) \ge 0.
\]
对 $L \in \{F, K_{-1}, K_2\}$（其中 $F = \mathbb Q_2$），记扩张次数 $e_L := [L : \mathbb Q_2] \in \{1, 2\}$，即 $e_F = 1$，$e_{K_{-1}} = e_{K_2} = 2$。

**局部域整数环的显式结构（标准局部域事实）：**
- 对 $\mu = 2$，$x^2 - 2$ 为 $\mathbb Z_2$ 上的 Eisenstein 多项式；对 $\mu = -1$，令 $\pi_{-1} = 1 + \theta_{-1}$，则 $\pi_{-1}^2 - 2\pi_{-1} + 2 = 0$ 为 $\mathbb Z_2$ 上的 Eisenstein 多项式。故 $K_\mu / \mathbb Q_2$ 为全分歧二次域扩张，题设环 $\mathcal O_\mu = \mathbb Z_2[\theta_\mu]$ 恰为 $K_\mu$ 的完整整数环 $\mathcal O_{K_\mu}$（完备离散赋值整环，$2$-进完备且无零因子），并作为自由 $\mathbb Z_2$-模以 $\{1, \theta_\mu\}$ 为基：
  \[
  \mathcal O_\mu = \mathbb Z_2 \oplus \mathbb Z_2 \theta_\mu, \qquad 2^M \mathcal O_\mu = 2^M \mathbb Z_2 \oplus 2^M \mathbb Z_2 \theta_\mu \quad (\forall M \ge 1).
  \]
- 因此自然映射 $\mathcal O_F / 2^M \mathcal O_F = \mathbb Z / 2^M \mathbb Z \hookrightarrow \mathcal O_\mu / 2^M \mathcal O_\mu = (\mathbb Z / 2^M \mathbb Z) \oplus (\mathbb Z / 2^M \mathbb Z)\theta_\mu$ 是单射；Galois 对合 $\sigma_\mu(x + y\theta_\mu) = x - y\theta_\mu$（$x, y \in \mathbb Z_2$）的不动点环恰为 $\mathcal O_\mu^{\sigma_\mu} = \mathbb Z_2 = \mathcal O_F$。
- 在任何 $2$-进完备环 $R = \mathcal O_L$ 或商环 $R = \mathcal O_L / 2^M \mathcal O_L$ 上，若 $N \in 2 M_n(R)$，则几何级数 $\sum_{k=0}^\infty N^k$ 在 $M_n(R)$ 中收敛（在商环中为有限和），故 $I_n - N \in \operatorname{GL}_n(R)$。

再引入两个有限维 $\mathbb F_2$-线性空间（用于刻画不动点集与纤维）：
\[
\mathcal W_C := \left\{ \bar W \in M_d(\mathbb F_2) : \bar W^{\mathsf T} = \bar W,\ [\bar W, E_j] = 0 \ (\forall j) \right\} \cong \bigoplus_{i=1}^r \operatorname{Sym}_{n_i}(\mathbb F_2), \qquad \dim_{\mathbb F_2} \mathcal W_C = \sum_{i=1}^r \frac{n_i(n_i+1)}{2} = \kappa + d,
\]
\[
\mathcal W_R := \left\{ \bar W \in \mathcal W_C : \operatorname{diag}(\bar W) = 0 \right\} \cong \bigoplus_{i=1}^r \operatorname{Sym}_{n_i}^0(\mathbb F_2), \qquad \dim_{\mathbb F_2} \mathcal W_R = \sum_{i=1}^r \binom{n_i}{2} = \kappa.
\]

---

## 1. 典范谱幂等元分解与标准正交约化

本节在不假设 $A_i$ 幂等或 $\sum_i A_i = I_d$ 的前提下，将同时分块问题在 $\mathbb Z_2$ 上典范地解耦为各分块上的二次型正交化问题。

### 引理 1.1（典范正交对称幂等元族）
对任意满足题设的 $A_1, \dots, A_r \in M_d(\mathbb Z_2)$，存在一族矩阵 $\Pi_1, \dots, \Pi_r \in M_d(\mathbb Z_2)$ 满足：
1. 每个 $\Pi_i$ 是以 $A_i$ 为变量的整系数多项式的 $2$-进极限，特别地 $\Pi_i^{\mathsf T} = \Pi_i$，$[\Pi_i, A_j] = 0$ 且 $[\Pi_i, \Pi_j] = 0$（$\forall i, j$）；
2. $\Pi_i^2 = \Pi_i$，$\Pi_i \equiv E_i \pmod 2$，且对 $i \ne j$ 有 $\Pi_i \Pi_j = 0$，以及 $\sum_{i=1}^r \Pi_i = I_d$；
3. 将 $\Pi_i$ 按指标集 $(I_i, I_i^c)$（其中 $I_i^c = \{1, \dots, d\} \setminus I_i$）写成 $2 \times 2$ 分块矩阵：
   \[
   \Pi_i = \begin{pmatrix} G_i & 2 H_i \\ 2 H_i^{\mathsf T} & Q_i \end{pmatrix}, \qquad G_i \in M_{n_i}(\mathbb Z_2),\ H_i \in M_{n_i \times (d-n_i)}(\mathbb Z_2),\ Q_i \in M_{d-n_i}(\mathbb Z_2),
   \]
   并记 $B_i := \frac{1}{2} (A_i)|_{I_i \times I_i^c} \in M_{n_i \times (d-n_i)}(\mathbb Z_2)$，则
   \[
   H_i \equiv B_i \pmod 2, \qquad Q_i \equiv 0 \pmod 4, \qquad G_i = I_{n_i} - 4 S_i,
   \]
   其中 $S_i \in M_{n_i}(\mathbb Z_2)$ 对称且满足 $S_i \equiv B_i B_i^{\mathsf T} \pmod 2$（实际上 $\pmod 4$ 有 $S_i \equiv H_i H_i^{\mathsf T} \pmod 4$）。

**证明：**
固定 $i$，令 $X_0 = A_i$，递推定义 $X_{k+1} = 3 X_k^2 - 2 X_k^3 = f_k(A_i)$（$f_k \in \mathbb Z[x]$）。由恒等式
\[
X_{k+1} - X_k = (X_k^2 - X_k)(I_d - 2 X_k), \qquad X_{k+1}^2 - X_{k+1} = (X_k^2 - X_k)^2 (4 X_k^2 - 4 X_k - 3 I_d),
\]
以及初值 $X_0 \equiv E_i \pmod 2 \implies X_0^2 - X_0 \equiv E_i^2 - E_i = 0 \pmod 2$，归纳即得 $X_k^2 - X_k \in 2^{2^k} M_d(\mathbb Z_2)$ 且 $X_{k+1} - X_k \in 2^{2^k} M_d(\mathbb Z_2)$。故极限 $\Pi_i := \lim_{k\to\infty} X_k \in M_d(\mathbb Z_2)$ 存在，满足 $\Pi_i^2 = \Pi_i$，$\Pi_i^{\mathsf T} = \Pi_i$（因 $A_i^{\mathsf T} = A_i$），且 $\Pi_i \equiv X_0 \equiv E_i \pmod 2$。由于 $A_1, \dots, A_r$ 两两交换，所有 $f_k(A_i)$ 与每个 $A_j$ 及 $f_m(A_j)$ 交换，取极限得 $[\Pi_i, A_j] = 0$ 与 $[\Pi_i, \Pi_j] = 0$。

对 $i \ne j$，令 $P = \Pi_i \Pi_j$。由交换性知 $P^2 = \Pi_i^2 \Pi_j^2 = P$，且 $P \equiv E_i E_j = 0 \pmod 2$。故 $I_d - P \in \operatorname{GL}_d(\mathbb Z_2)$，由 $P(I_d - P) = 0$ 得 $P = 0$。进而令 $S = \sum_{i=1}^r \Pi_i$，由两两正交幂等知 $S^2 = S$，且 $S \equiv \sum_{i=1}^r E_i = I_d \pmod 2 \implies S \in \operatorname{GL}_d(\mathbb Z_2)$，由 $S(I_d - S) = 0$ 得 $S = I_d$。性质 1、2 得证。

对性质 3，因 $X_1^2 - X_1 \in 4 M_d(\mathbb Z_2)$，对一切 $k \ge 1$ 有 $X_{k+1} \equiv X_k \pmod 4$，故 $\Pi_i \equiv X_1 = 3 A_i^2 - 2 A_i^3 \pmod 4$。在 $(I_i, I_i^c)$ 分块下写 $A_i = \begin{pmatrix} I_{n_i} + 2 C_{11} & 2 B_i \\ 2 B_i^{\mathsf T} & 2 C_{22} \end{pmatrix}$，直接乘出模 $4$ 的 $(1, 2)$ 块：
\[
(A_i^2)_{1,2} = (I_{n_i} + 2 C_{11})(2 B_i) + (2 B_i)(2 C_{22}) \equiv 2 B_i \pmod 4, \qquad (A_i^3)_{1,2} \equiv 2 B_i \pmod 4.
\]
于是 $2 H_i = (\Pi_i)_{1,2} \equiv 3(2 B_i) - 2(2 B_i) = 2 B_i \pmod 4$，即 $H_i \equiv B_i \pmod 2$。再展开 $\Pi_i^2 = \Pi_i$ 的对角块：
- $(2, 2)$ 块：$4 H_i^{\mathsf T} H_i + Q_i^2 = Q_i \iff Q_i(I_{d-n_i} - Q_i) = 4 H_i^{\mathsf T} H_i$。因 $Q_i \equiv 0 \pmod 2$，$I_{d-n_i} - Q_i$ 可逆，故 $Q_i \equiv 0 \pmod 4$；
- $(1, 1)$ 块：$G_i^2 + 4 H_i H_i^{\mathsf T} = G_i \iff G_i(I_{n_i} - G_i) = 4 H_i H_i^{\mathsf T}$。因 $G_i \equiv I_{n_i} \pmod 2$ 可逆，令 $S_i := G_i^{-1} H_i H_i^{\mathsf T}$，则 $I_{n_i} - G_i = 4 S_i$（故 $S_i = \frac{1}{4}(I_{n_i} - G_i)$ 自动对称），从而 $G_i \equiv I_{n_i} \pmod 4 \implies G_i^{-1} \equiv I_{n_i} \pmod 4$，故 $S_i \equiv H_i H_i^{\mathsf T} \equiv B_i B_i^{\mathsf T} \pmod 2$。$\blacksquare$

---

### 引理 1.2（有限精度与无限精度下的统一解耦）
设环 $R$ 为 $\mathcal O_L$ 或 $\mathcal O_L / 2^M \mathcal O_L$（$M \ge 2$），我们将 $M_d(\mathbb Z_2)$ 中矩阵经自然环同态映射到 $M_d(R)$。
1. 对任意满足 $U \equiv I_d \pmod{2R}$ 且 $U^{\mathsf T} U = I_d$ 的 $U \in \operatorname{GL}_d(R)$，有等价关系：
   \[
   [U^{\mathsf T} A_i U, E_j] = 0 \ (\forall i, j) \iff U^{\mathsf T} \Pi_j U = E_j \ (\forall j = 1, \dots, r).
   \]
2. 定义典范矩阵
   \[
   V_0 := \sum_{j=1}^r \Pi_j E_j \in M_d(\mathbb Z_2).
   \]
   则 $V_0 \equiv \sum_{j=1}^r E_j^2 = I_d \pmod 2$，故 $V_0 \in \operatorname{GL}_d(\mathbb Z_2)$，$\sigma_\mu(V_0) = V_0$，且满足 $\Pi_j V_0 = \Pi_j^2 E_j = \Pi_j E_j = V_0 E_j$（$\forall j$），以及
   \[
   V_0^{\mathsf T} V_0 = \sum_{j, k=1}^r E_j \Pi_j^{\mathsf T} \Pi_k E_k = \sum_{j=1}^r E_j \Pi_j E_j = \operatorname{diag}(G_1, \dots, G_r).
   \]
   进而映射 $C \mapsto U = V_0 C$ 给出集合
   \[
   \left\{ U \in \operatorname{GL}_d(R) : U \equiv I_d \pmod{2R},\ U^{\mathsf T} U = I_d,\ [U^{\mathsf T} A_i U, E_j] = 0 \ (\forall i, j) \right\}
   \]
   与乘积集合
   \[
   \prod_{i=1}^r \left\{ C_i \in \operatorname{GL}_{n_i}(R) : C_i \equiv I_{n_i} \pmod{2R},\ C_i^{\mathsf T} G_i C_i = I_{n_i} \right\}
   \]
   （经 $C = \operatorname{diag}(C_1, \dots, C_r)$ 嵌入）之间的双射，且该双射与模 $2^M$ 约化、域扩张包含以及 $\sigma_\mu$-作用完全交换。

**证明：**
1. 因 $U^{\mathsf T} U = I_d$，在有限自由模的自同态环 $M_d(R)$ 中 $U^{-1} = U^{\mathsf T}$，故 $U U^{\mathsf T} = I_d$。
   - $(\Leftarrow)$：若对一切 $j$ 有 $U^{\mathsf T} \Pi_j U = E_j$，即 $U E_j U^{\mathsf T} = \Pi_j$，则由引理 1.1(1) 的 $[A_i, \Pi_j] = 0$ 得 $[U^{\mathsf T} A_i U, E_j] = U^{\mathsf T}[A_i, U E_j U^{\mathsf T}]U = U^{\mathsf T}[A_i, \Pi_j]U = 0$。
   - $(\Rightarrow)$：假设对一切 $i, j$ 有 $[U^{\mathsf T} A_i U, E_j] = 0$。固定 $j$，置 $P_j := U E_j U^{\mathsf T} \in M_d(R)$。则 $P_j^2 = U E_j^2 U^{\mathsf T} = P_j$，$P_j \equiv E_j \pmod{2R}$，且 $[A_j, P_j] = U[U^{\mathsf T} A_j U, E_j]U^{\mathsf T} = 0$。因 $\Pi_j = \lim_{k\to\infty} f_k(A_j)$（在 $M_d(\mathcal O_L / 2^M \mathcal O_L)$ 中取充分大的 $k$ 即精确等于 $f_k(A_j)$），$P_j$ 与 $A_j$ 交换蕴含 $P_j$ 与 $\Pi_j$ 在 $M_d(R)$ 中交换。
     对交换幂等元 $P_j, \Pi_j$，令 $\Delta = P_j - \Pi_j \in 2 M_d(R)$，直接展开得恒等式：
     \[
     \Delta^3 = (P_j - \Pi_j)^3 = P_j^3 - 3 P_j^2 \Pi_j + 3 P_j \Pi_j^2 - \Pi_j^3 = P_j - 3 P_j \Pi_j + 3 P_j \Pi_j - \Pi_j = \Delta,
     \]
     即 $(I_d - \Delta^2)\Delta = 0$。因 $\Delta \in 2 M_d(R)$，有 $\Delta^2 \in 4 M_d(R)$，故 $I_d - \Delta^2 \in \operatorname{GL}_d(R)$，左乘其逆即得 $\Delta = 0$，即 $P_j = \Pi_j \iff U^{\mathsf T} \Pi_j U = E_j$。
2. 写 $U = V_0 C$（因 $V_0 \in \operatorname{GL}_d(\mathbb Z_2)$ 且 $V_0 \equiv I_d \pmod 2$，故 $U \equiv I_d \pmod{2R} \iff C \equiv I_d \pmod{2R}$）。在 $U^{\mathsf T} U = I_d$ 前提下：
   - $U^{\mathsf T} \Pi_j U = E_j \iff \Pi_j V_0 C = V_0 C E_j \iff V_0 E_j C = V_0 C E_j \iff E_j C = C E_j$（$\forall j$），即 $C = \operatorname{diag}(C_1, \dots, C_r)$ 为分块对角阵；
   - $U^{\mathsf T} U = I_d \iff C^{\mathsf T} (V_0^{\mathsf T} V_0) C = I_d \iff C_i^{\mathsf T} G_i C_i = I_{n_i}$（$\forall i = 1, \dots, r$）。
   由于 $V_0 \in \operatorname{GL}_d(\mathbb Z_2)$ 元素全在基域整数环 $\mathbb Z_2$ 中，双射与约化、扩域包含及 $\sigma_\mu$-作用逐项相容。$\blacksquare$

---

## 2. 目标 1 的完整解答与证明

### 2.1 明确结论陈述（目标 1）

1. **模 $4$ 可行性判准：**
   对每个 $i \in \{1, \dots, r\}$，由 $A_i \bmod 4$ 定义有限可计算的奇偶不变量
   \[
   \delta_i(A) := \sum_{p \in I_i}\sum_{q \notin I_i} \frac{(A_i)_{pq} \bmod 4}{2} \bmod 2 \in \mathbb F_2
   \]
   （其中 $x \bmod 4 \in \{0, 2\}$，即统计非对角矩形块 $I_i \times I_i^c$ 中满足 $(A_i)_{pq} \equiv 2 \pmod 4$ 的元素个数的奇偶性；当 $r = 1$ 时空和为 $0$，恒有 $\delta_1(A) = 0$）。
   则对**任意** $L \in \{F, K_{-1}, K_2\}$，可行性条件与扩域 $L$ 无关：
   \[
   \mathscr S_L(A) \ne \emptyset \iff \delta_i(A) = 0 \quad (\forall i = 1, \dots, r).
   \]

2. **$\mathscr R_{L,M}(A)$ 与 $\mathscr C_{L,M}(A)$（$M \ge 2$）的空集条件与闭式精确基数：**
   记 $d = \sum_{i=1}^r n_i$，$\kappa = \sum_{i=1}^r \binom{n_i}{2}$，$e_L = [L : \mathbb Q_2] \in \{1, 2\}$。
   - **对 $\mathscr R_{L,M}(A)$（一切 $M \ge 2$）：**
     \[
     \mathscr R_{L,M}(A) = \emptyset \iff \exists i \in \{1, \dots, r\} \text{ 使 } \delta_i(A) = 1;
     \]
     \[
     |\mathscr R_{L,M}(A)| = \begin{cases} 0, & \text{若 } \exists i,\ \delta_i(A) = 1, \\ 2^{\,r + e_L(M-1)\kappa}, & \text{若 } \forall i,\ \delta_i(A) = 0. \end{cases}
     \]
   - **对 $\mathscr C_{L,M}(A)$：**
     - 当 $M = 2$ 时，$\mathscr C_{L,2}(A)$ **永不为空集**（无论 $\delta_i(A)$ 取何值），且恒有
       \[
       |\mathscr C_{L,2}(A)| = 2^{\,e_L(\kappa + d)}.
       \]
     - 当 $M \ge 3$ 时，$\mathscr C_{L,M}(A) = \emptyset \iff \exists i \in \{1, \dots, r\} \text{ 使 } \delta_i(A) = 1$，且
       \[
       |\mathscr C_{L,M}(A)| = \begin{cases} 0, & \text{若 } \exists i,\ \delta_i(A) = 1, \\ 2^{\,r + e_L d + e_L(M-1)\kappa}, & \text{若 } \forall i,\ \delta_i(A) = 0. \end{cases}
       \]

3. **$\bar U \in \mathscr C_{L,M}(A)$ 属于 $\mathscr R_{L,M}(A)$ 的可核验必要充分条件：**
   对一切 $M \ge 2$ 与 $L \in \{F, K_{-1}, K_2\}$，恒有 $\mathscr R_{L,M}(A) = \operatorname{im}(\mathscr C_{L,M+1}(A) \to \mathscr C_{L,M}(A))$。更直接地，对给定 $\bar U \in \mathscr C_{L,M}(A)$，任取其一个矩阵代表元 $U \in M_d(\mathcal O_L)$（只需知其模 $2^{M+1} \mathcal O_L$ 的类，无需搜索），则
   \[
   \bar U \in \mathscr R_{L,M}(A) \iff \operatorname{diag}(U^{\mathsf T} U - I_d) \equiv 0 \pmod{2^{M+1}\mathcal O_L} \iff \sum_{k=1}^d U_{kp}^2 \equiv 1 \pmod{2^{M+1}\mathcal O_L} \quad (\forall p = 1, \dots, d).
   \]

4. **否定结论的具体实例（不可行输入及 $\mathscr R_{L,M}(A) \subsetneq \mathscr C_{L,M}(A)$）：**
   - *不可行输入实例（$r \ge 2$）：* 对任意 $r \ge 2$ 及任意 $(n_1, \dots, n_r)$，取 $p_1 \in I_1, p_2 \in I_2$，令 $J = e_{p_1} e_{p_2}^{\mathsf T} + e_{p_2} e_{p_1}^{\mathsf T}$，定义
     \[
     A_1 = E_1 + 2 J, \qquad A_2 = E_2 - 2 J, \qquad A_i = E_i \quad (3 \le i \le r).
     \]
     因 $A_1, A_2$ 支集落在 $I_1 \cup I_2$ 上且 $A_1 + A_2 = E_1 + E_2$ 在 $I_1 \cup I_2$ 上为恒等阵，易见 $A_i^{\mathsf T} = A_i$、$A_i A_j = A_j A_i$ 且 $A_i \equiv E_i \pmod 2$。此时 $\delta_1(A) = 1 \ne 0$，故对一切 $L \in \{F, K_{-1}, K_2\}$ 有 $\mathscr S_L(A) = \emptyset$、$\mathscr R_{L,M}(A) = \emptyset$（$\forall M \ge 2$）及 $\mathscr C_{L,M}(A) = \emptyset$（$\forall M \ge 3$），但 $\mathscr C_{L,2}(A) \ne \emptyset$（例如当 $r=2, n_1=n_2=1$ 时，$\bar U = \begin{pmatrix} 1 & 2 \\ 2 & 1 \end{pmatrix} \bmod 4 \in \mathscr C_{L,2}(A)$，其列平方和为 $1^2 + 2^2 = 5 \not\equiv 1 \pmod 8$，不在 $\mathscr R_{L,2}(A)$ 中）。
   - *可行输入下 $\mathscr R_{L,M}(A) \subsetneq \mathscr C_{L,M}(A)$ 的统一实例：* 取 $A_i = E_i$（$\forall i$），对任意 $M \ge 3$，取 $\bar U = \operatorname{diag}(1 + 2^{M-1}, 1, \dots, 1) \bmod 2^M\mathcal O_L \in \mathscr C_{L,M}(A)$，其首列平方和为 $(1 + 2^{M-1})^2 \equiv 1 + 2^M \not\equiv 1 \pmod{2^{M+1}\mathcal O_L}$，故 $\bar U \notin \mathscr R_{L,M}(A)$。（当 $M = 2$ 时，仅当 $L = F$ 且 $n_1 = \dots = n_r = 1$ 时 $\mathscr R_{F,2}(A) = \mathscr C_{F,2}(A)$；若 $L = K_\mu$，取 $\bar U = \operatorname{diag}(1 + 2\theta_\mu, 1, \dots, 1) \bmod 4\mathcal O_\mu \in \mathscr C_{K_\mu,2}(A) \setminus \mathscr R_{K_\mu,2}(A)$；若 $L = F$ 且某 $n_{i_0} \ge 2$，在 $I_{i_0}$ 的前两坐标取 $\begin{pmatrix} 1 & 2 \\ 2 & 1 \end{pmatrix} \bmod 4$、其余取 $I$，即得 $\mathscr C_{F,2}(A) \setminus \mathscr R_{F,2}(A)$ 中元素。）

---

### 2.2 目标 1 的证明

#### 第一步：可行性判准与模 $8$ 障碍
由引理 1.1(3)，$\operatorname{tr}(S_i) \equiv \operatorname{tr}(B_i B_i^{\mathsf T}) = \sum_{p \in I_i}\sum_{q \notin I_i} (B_i)_{pq}^2 \equiv \sum_{p \in I_i}\sum_{q \notin I_i} (B_i)_{pq} \equiv \delta_i(A) \pmod 2$。

1. **必要性（若某 $\delta_i(A) = 1$，则对一切 $M \ge 3$ 有 $\mathscr C_{L,M}(A) = \emptyset$，从而 $\mathscr S_L(A) = \emptyset$）：**
   设 $\delta_i(A) = 1$，即 $\operatorname{tr}(S_i) \equiv 1 \pmod 2$。若 $\mathscr C_{L,M}(A) \ne \emptyset$（$M \ge 3$），则模 $8\mathcal O_L$ 约化给出 $\mathscr C_{L,3}(A) \ne \emptyset$。由引理 1.2(2)，存在 $C_i \in \operatorname{GL}_{n_i}(\mathcal O_L / 8\mathcal O_L)$ 使 $C_i^{\mathsf T} G_i C_i \equiv I_{n_i} \pmod{8\mathcal O_L}$。取行列式并利用 $G_i = I_{n_i} - 4 S_i$：
   \[
   \det(G_i) = \det(I_{n_i} - 4 S_i) \equiv 1 - 4\operatorname{tr}(S_i) \equiv 5 \pmod 8,
   \]
   故 $(\det C_i)^2 \cdot 5 \equiv 1 \pmod{8\mathcal O_L}$，即 $5 \equiv (\det C_i)^{-2} \pmod{8\mathcal O_L}$ 为 $\mathcal O_L / 8\mathcal O_L$ 中的单位平方。但：
   - 在 $\mathcal O_F = \mathbb Z_2$ 中，奇数平方模 $8$ 恒为 $1 \not\equiv 5$；
   - 在 $\mathcal O_\mu$（$\mu \in \{-1, 2\}$）中，对任意 $u = a + b\theta_\mu$，$u^2 = (a^2 + \mu b^2) + 2ab\theta_\mu$。若 $u^2 \equiv 5 \pmod{8\mathcal O_\mu}$，则 $a^2 + \mu b^2 \equiv 5 \pmod 8$ 且 $2ab \equiv 0 \pmod 8 \implies ab \equiv 0 \pmod 4$。因 $a^2 + \mu b^2$ 为奇数：
     - 若 $\mu = 2$，则 $a$ 必为奇数，从而 $4 \mid b \implies 2b^2 \equiv 0 \pmod 8 \implies a^2 \equiv 1 \not\equiv 5 \pmod 8$；
     - 若 $\mu = -1$，则 $a, b$ 一奇一偶，奇者不能被 $2$ 整除，故偶者必被 $4$ 整除，平方模 $16$ 为 $0$，于是 $a^2 - b^2 \equiv \pm 1 \not\equiv 5 \pmod 8$。
   两情形均矛盾！故 $\mathscr C_{L,M}(A) = \emptyset$（$\forall M \ge 3$），进而 $\mathscr S_L(A) = \emptyset$。

2. **充分性（若对一切 $i$ 有 $\delta_i(A) = 0$，则 $\mathscr S_F(A) \ne \emptyset$，从而对一切 $L$ 有 $\mathscr S_L(A) \ne \emptyset$）：**
   固定 $i$，设 $\operatorname{tr}(S_i) \equiv 0 \pmod 2$，写 $n = n_i, G = G_i = I_n - 4 S$（$S = S_i \in \operatorname{Sym}_n(\mathbb Z_2)$）。我们在 $\mathbb Z_2$ 上直接构造 $C_* \in \operatorname{GL}_n(\mathbb Z_2)$ 使 $C_* \equiv I_n \pmod 2$ 且 $C_*^{\mathsf T} G C_* = I_n$：
   - **初值（精度 $M = 3$）：** 在以 $\{1, \dots, n\}$ 为顶点集的完全图 $K_n$ 上，因顶点目标奇偶和 $\sum_{p=1}^n S_{pp} = \operatorname{tr}(S) \equiv 0 \pmod 2$，将满足 $S_{pp} \equiv 1 \pmod 2$ 的偶数个顶点两两配对并在配对顶点间连边（当 $n=1$ 时 $S_{11} \equiv 0 \pmod 2$，取空边集），其邻接矩阵给出对称阵 $\bar X \in \operatorname{Sym}_n(\mathbb F_2)$（对角元取 $0$）满足 $\sum_{q \ne p} \bar X_{pq} \equiv S_{pp} \pmod 2$（$\forall p$）。
     取整矩阵提升 $X \in M_n(\mathbb Z_2)$，将下三角元（$q > p$）按 $X_{qp} := -X_{pq} - 2(X^{\mathsf T} X - S)_{pq}$ 修正（注意这不改变 $X \bmod 2$，故 $(X^{\mathsf T} X)_{pq} \bmod 2$ 不变）。则对 $p < q$ 有 $(X + X^{\mathsf T})_{pq} + 2(X^{\mathsf T} X - S)_{pq} \equiv 0 \pmod 4$；对 $p = q$，因 $X_{pp} \equiv 0 \pmod 2$，有
     \[
     \frac{1}{2}(X + X^{\mathsf T})_{pp} + (X^{\mathsf T} X - S)_{pp} = X_{pp} + X_{pp}^2 + \sum_{q \ne p} X_{qp}^2 - S_{pp} \equiv \sum_{q \ne p} \bar X_{pq} - S_{pp} \equiv 0 \pmod 2.
     \]
     于是 $(X + X^{\mathsf T}) + 2(X^{\mathsf T} X - S) \equiv 0 \pmod 4$。令 $C^{(3)} := I_n + 2 X \equiv I_n \pmod 2$，展开得
     \[
     (C^{(3)})^{\mathsf T} G C^{(3)} = (I_n + 2 X^{\mathsf T})(I_n - 4 S)(I_n + 2 X) \equiv I_n + 2(X + X^{\mathsf T}) + 4(X^{\mathsf T} X - S) \equiv I_n \pmod 8.
     \]
   - **归纳提升（$k \to k+1$，$k \ge 3$）：** 设已有 $C^{(k)} \in M_n(\mathbb Z_2)$ 满足 $C^{(k)} \equiv I_n \pmod 2$ 且 $(C^{(k)})^{\mathsf T} G C^{(k)} = I_n + 2^k \Delta_k$（$\Delta_k^{\mathsf T} = \Delta_k$）。
     令对角阵 $Y_k := -\operatorname{diag}((\Delta_k)_{11}, \dots, (\Delta_k)_{nn})$，置 $C' := C^{(k)}(I_n + 2^{k-1} Y_k) \equiv C^{(k)} \pmod{2^{k-1}}$。因 $k \ge 3 \implies 2k - 2 \ge k + 1$，有
     \[
     (C')^{\mathsf T} G C' = (I_n + 2^{k-1} Y_k)(I_n + 2^k \Delta_k)(I_n + 2^{k-1} Y_k) \equiv I_n + 2^k(\Delta_k + Y_k) \pmod{2^{k+1}},
     \]
     其中对称阵 $\Delta_k' := \frac{(C')^{\mathsf T} G C' - I_n}{2^k}$ 的对角元全为偶数！于是取严格上三角阵 $Z_k \in M_n(\mathbb Z_2)$ 使对 $p < q$ 有 $(Z_k)_{pq} = -(\Delta_k')_{pq}$，则 $Z_k + Z_k^{\mathsf T} \equiv -\Delta_k' \pmod 2$。令 $C^{(k+1)} := C'(I_n + 2^k Z_k)$，则 $C^{(k+1)} \equiv C' \equiv C^{(k)} \pmod{2^{k-1}}$，且
     \[
     (C^{(k+1)})^{\mathsf T} G C^{(k+1)} \equiv I_n + 2^k(\Delta_k' + Z_k + Z_k^{\mathsf T}) \equiv I_n \pmod{2^{k+1}}.
     \]
   序列 $\{C^{(k)}\}_{k \ge 3}$ 在 $M_n(\mathbb Z_2)$ 中 $2$-进 Cauchy，其极限 $C_* = \lim_{k\to\infty} C^{(k)}$ 满足 $C_* \equiv I_n \pmod 2$ 且 $C_*^{\mathsf T} G C_* = I_n$。对所有块拼成 $U_* = V_0 \operatorname{diag}(C_{1,*}, \dots, C_{r,*})$，即得 $U_* \in \mathscr S_F(A) \subseteq \mathscr S_L(A)$。

---

#### 第二步：从 $\mathscr C_{L,M}(A)$ 到 $\mathscr R_{L,M}(A)$ 的判准证明
设 $M \ge 2$，$\bar U \in \mathscr C_{L,M}(A)$，任取其提升 $U \in M_d(\mathcal O_L)$。
- **必要性：** 若 $\bar U \in \mathscr R_{L,M}(A)$，则存在真解 $U_{\mathrm{true}} \in \mathscr S_L(A)$ 使 $U \equiv U_{\mathrm{true}} \pmod{2^M\mathcal O_L}$。因 $U_{\mathrm{true}} \in \operatorname{GL}_d(\mathcal O_L)$，可写 $U = U_{\mathrm{true}}(I_d + 2^M Z)$（$Z \in M_d(\mathcal O_L)$）。因 $2M \ge M + 2 > M + 1$，有
  \[
  U^{\mathsf T} U = (I_d + 2^M Z^{\mathsf T}) U_{\mathrm{true}}^{\mathsf T} U_{\mathrm{true}} (I_d + 2^M Z) \equiv I_d + 2^M(Z + Z^{\mathsf T}) \pmod{2^{M+1}\mathcal O_L},
  \]
  其第 $p$ 个对角元为 $1 + 2^{M+1} Z_{pp} \equiv 1 \pmod{2^{M+1}\mathcal O_L}$（$\forall p = 1, \dots, d$）。

- **充分性（及 $\mathscr R_{L,M}(A) = \operatorname{im}(\mathscr C_{L,M+1}(A) \to \mathscr C_{L,M}(A))$）：**
  首先证明：若 $\operatorname{diag}(U^{\mathsf T} U - I_d) \equiv 0 \pmod{2^{M+1}\mathcal O_L}$，则 $\bar U$ 可提升到 $\mathscr C_{L,M+1}(A)$。
  写 $U^{\mathsf T} U = I_d + 2^M \Phi$（$\Phi^{\mathsf T} = \Phi$，且假设给出 $\Phi_{pp} \equiv 0 \pmod{2\mathcal O_L}$）。由引理 1.2(1) 对 $R = \mathcal O_L / 2^M\mathcal O_L$ 的结论，有 $U^{\mathsf T} \Pi_m U = E_m + 2^M R_m$（$R_m^{\mathsf T} = R_m \in M_d(\mathcal O_L)$，$\forall m = 1, \dots, r$）。
  由 $\Pi_m^2 = \Pi_m$ 及 $U U^{\mathsf T} = U(I_d + 2^M \Phi)U^{-1}$？更直接地，$(U^{\mathsf T} \Pi_m U)(U^{\mathsf T} U)^{-1}(U^{\mathsf T} \Pi_m U) = U^{\mathsf T} \Pi_m^2 U = U^{\mathsf T} \Pi_m U$，在模 $2^{M+1}\mathcal O_L$ 下展开（利用 $2M > M+1$）：
  \[
  (E_m + 2^M R_m)(I_d - 2^M \Phi)(E_m + 2^M R_m) \equiv E_m + 2^M(E_m R_m + R_m E_m - E_m \Phi E_m) \equiv E_m + 2^M R_m \pmod{2^{M+1}\mathcal O_L},
  \]
  即 $E_m R_m + R_m E_m - E_m \Phi E_m \equiv R_m \pmod{2\mathcal O_L}$。两端左乘 $E_j$、右乘 $E_k$：
  1. 当 $m \notin \{j, k\}$ 时，$E_j E_m = E_m E_k = 0$，得 $E_j R_m E_k \equiv 0 \pmod{2\mathcal O_L}$（含 $j = k \ne m$ 的情形）；
  2. 再由 $\sum_{m=1}^r (E_m + 2^M R_m) = U^{\mathsf T}(\sum_m \Pi_m)U = U^{\mathsf T} U = I_d + 2^M \Phi$，左乘 $E_j$、右乘 $E_k$ 得：
     - 当 $j \ne k$ 时，$E_j(R_j + R_k)E_k \equiv E_j \Phi E_k \pmod{2\mathcal O_L}$；
     - 当 $j = k$ 时，$E_j R_j E_j \equiv E_j \Phi E_j \pmod{2\mathcal O_L}$。

  现在按分块选取 $Z \in M_d(\mathcal O_L)$：
  - 对 $j \ne k$，置 $E_j Z E_k := -E_j R_j E_k$；则 $E_j(Z + Z^{\mathsf T})E_k = -E_j(R_j + R_k)E_k \equiv -E_j \Phi E_k \pmod{2\mathcal O_L}$；
  - 对 $j = k$，因对称阵 $E_j \Phi E_j$ 的对角元全在 $2\mathcal O_L$ 中，取 $E_j Z E_j$ 为严格上三角块，使其严格上三角元等于 $-E_j \Phi E_j$ 对应元，则 $E_j(Z + Z^{\mathsf T})E_j \equiv -E_j \Phi E_j \pmod{2\mathcal O_L}$。
  令 $\widetilde U := U(I_d + 2^M Z) \equiv U \pmod{2^M\mathcal O_L}$。则：
  - $\widetilde U^{\mathsf T} \widetilde U \equiv I_d + 2^M(\Phi + Z + Z^{\mathsf T}) \equiv I_d \pmod{2^{M+1}\mathcal O_L}$；
  - 对每个 $m$，$\widetilde U^{\mathsf T} \Pi_m \widetilde U \equiv E_m + 2^M(R_m + Z^{\mathsf T} E_m + E_m Z) \pmod{2^{M+1}\mathcal O_L}$，逐块检验 $E_j(R_m + Z^{\mathsf T} E_m + E_m Z)E_k \bmod 2\mathcal O_L$：
    - $m \notin \{j, k\}$ 时为 $0 + 0 + 0 = 0$；
    - $j \ne k, m = j$ 时为 $E_j R_j E_k + 0 - E_j R_j E_k = 0$；$j \ne k, m = k$ 时取转置亦为 $0$；
    - $j = k = m$ 时为 $E_j \Phi E_j - E_j \Phi E_j = 0$。
  故由引理 1.2(1) 知 $\widetilde U \bmod 2^{M+1}\mathcal O_L \in \mathscr C_{L,M+1}(A)$！

  最后证明 $\operatorname{im}(\mathscr C_{L,M+1}(A) \to \mathscr C_{L,M}(A)) \subseteq \mathscr R_{L,M}(A)$：
  设 $\bar U$ 有提升 $\bar U^{(M+1)} \in \mathscr C_{L,M+1}(A)$。因 $M + 1 \ge 3$，由第一步必要性知此时必有 $\forall i, \delta_i(A) = 0$，从而存在真解 $U_* \in \mathscr S_F(A) \subseteq \mathscr S_L(A)$。左乘 $(U_*)^{-1}$ 化归为标准情形 $G_i = I_{n_i}$：在每块 $n = n_i$ 上，代表元 $O^{(M+1)} \in M_n(\mathcal O_L)$ 满足 $(O^{(M+1)})^{\mathsf T} O^{(M+1)} = I_n + 2^{M+1}\Delta_{M+1}$。因 $k := M + 1 \ge 3$，完全照搬第一步充分性中的“归纳提升（$k \to k+1$，$k \ge 3$）”（每步仅在 $2^{k-1}\mathcal O_L$ 处修正对角阵 $Y_k$ 并在 $2^k\mathcal O_L$ 处修正 $Z_k$，该代数计算在任意 $\mathcal O_L$ 上逐字成立！）：
  - 首步 $k = M+1$ 保持模 $2^{(M+1)-1}\mathcal O_L = 2^M\mathcal O_L$ 的剩余类不变；
  - 后续 $k \ge M+2$ 保持模 $2^{k-1}\mathcal O_L \subseteq 2^{M+1}\mathcal O_L$ 不变并 $2$-进收敛到真解 $O^{(\infty)} \in \operatorname{O}_n(\mathcal O_L)$，满足 $O^{(\infty)} \equiv O^{(M+1)} \pmod{2^M\mathcal O_L}$。
  左乘回 $U_*$ 即得真解 $U_{\mathrm{true}} \in \mathscr S_L(A)$ 使 $U_{\mathrm{true}} \bmod 2^M\mathcal O_L = \bar U$，故 $\bar U \in \mathscr R_{L,M}(A)$。

---

#### 第三步：$\mathscr R_{L,M}(A)$ 与 $\mathscr C_{L,M}(A)$ 的精确基数计算
1. **精度 $M = 2$ 下 $|\mathscr C_{L,2}(A)|$（任意合法 $A$）：**
   由引理 1.1(3)，恒有 $G_i \equiv I_{n_i} \pmod 4$。在引理 1.2(2) 下，对 $R = \mathcal O_L / 4\mathcal O_L$，写 $C_i = I_{n_i} + 2 \bar X_i$（$\bar X_i \in M_{n_i}(\mathcal O_L / 2\mathcal O_L)$），则
   \[
   C_i^{\mathsf T} G_i C_i \equiv (I_{n_i} + 2 \bar X_i^{\mathsf T})(I_{n_i} + 2 \bar X_i) = I_{n_i} + 2(\bar X_i + \bar X_i^{\mathsf T}) \equiv I_{n_i} \pmod{4\mathcal O_L} \iff \bar X_i^{\mathsf T} = \bar X_i \in \operatorname{Sym}_{n_i}(\mathcal O_L / 2\mathcal O_L).
   \]
   因 $|\mathcal O_L / 2\mathcal O_L| = 2^{e_L}$，第 $i$ 块解数为 $(2^{e_L})^{n_i(n_i+1)/2}$，对 $i=1,\dots,r$ 相乘得 $|\mathscr C_{L,2}(A)| = 2^{e_L(\kappa + d)}$。

2. **可行情形下（$\forall i, \delta_i(A) = 0$）$|\mathscr R_{L,M}(A)|$ 与 $|\mathscr C_{L,M}(A)|$：**
   固定真解 $U_* \in \mathscr S_F(A)$，左乘 $U_*^{-1}$ 将 $\mathscr S_L(A)$、$\mathscr R_{L,M}(A)$、$\mathscr C_{L,M}(A)$ 分别双射到 $\prod_{i=1}^r \Gamma_L(n_i, 1)$、$\prod_{i=1}^r (\Gamma_L(n_i, 1) / \Gamma_L(n_i, M))$ 与 $\prod_{i=1}^r \mathscr C_{L,M}(I_{n_i})$，其中对 $m \ge 1$ 记同余正交群
   \[
   \Gamma_L(n, m) := \left\{ O \in \operatorname{O}_n(\mathcal O_L) : O \equiv I_n \pmod{2^m\mathcal O_L} \right\}, \qquad \operatorname{SO}_n^{(m)}(\mathcal O_L) := \Gamma_L(n, m) \cap \operatorname{SO}_n(\mathcal O_L).
   \]
   固定单块阶数 $n \ge 1$：
   - **计算 $|\mathscr R_{L,2}(I_n)| = |\Gamma_L(n,1) / \Gamma_L(n,2)|$：**
     由第二步，$\mathscr R_{L,2}(I_n)$ 恰为 $\mathscr C_{L,2}(I_n) = \{I_n + 2\bar X : \bar X \in \operatorname{Sym}_n(\mathcal O_L / 2\mathcal O_L)\}$ 中满足对角条件 $\operatorname{diag}((I_n + 2X^{\mathsf T})(I_n + 2X) - I_n) \equiv 0 \pmod{8\mathcal O_L}$ 的元素，即
     \[
     \bar X_{pp} + \bar X_{pp}^2 + \sum_{q \ne p} \bar X_{pq}^2 = 0 \quad \text{in } \mathcal O_L / 2\mathcal O_L \qquad (\forall p = 1, \dots, n).
     \]
     - 当 $L = F$（$\mathcal O_F / 2\mathcal O_F = \mathbb F_2$，$e_L = 1$）：在 $\mathbb F_2$ 中 $\bar X_{pp} + \bar X_{pp}^2 = 0$，方程化为 $\sum_{q \ne p} \bar X_{pq} = 0$（$\forall p$）。当 $n = 1$ 时为空方程（秩 $0 = n-1$）；当 $n \ge 2$ 时，因对称阵所有非对角元之和 $\sum_{p=1}^n \sum_{q \ne p} \bar X_{pq} = 0$ 且前 $n-1$ 个方程线性无关（考虑星图边变量 $\bar X_{p,n}$），方程组在 $\operatorname{Sym}_n(\mathbb F_2)$ 上的秩恰为 $n - 1$。故解数为 $2^{\frac{n(n+1)}{2} - (n-1)} = 2^{\binom{n}{2} + 1}$。
     - 当 $L = K_\mu$（$\mathcal O_\mu / 2\mathcal O_\mu = \mathbb F_2 \oplus \mathbb F_2 \theta_\mu$，$e_L = 2$）：写 $\bar X_{pq} = a_{pq} + b_{pq}\theta_\mu$（$a_{pq}, b_{pq} \in \mathbb F_2$ 对称）。在模 $2\mathcal O_\mu$ 下，$(a + b\theta_\mu)^2 = a^2 + \mu b^2 \equiv a + \mu b \pmod{2\mathcal O_\mu}$，故 $(a_{pp} + b_{pp}\theta_\mu) + (a_{pp} + b_{pp}\theta_\mu)^2 \equiv \mu b_{pp} + b_{pp}\theta_\mu \pmod{2\mathcal O_\mu}$。比较方程第 $p$ 式的 $\theta_\mu$-分量即得 $b_{pp} = 0$（共 $n$ 个独立方程）；代入 $b_{pp} = 0$ 后，$1$-分量化为 $\sum_{q \ne p} (a_{pq} + \mu b_{pq}) = 0$（$\forall p$），对对称矩阵 $c_{pq} := a_{pq} + \mu b_{pq} \in \mathbb F_2$（$p \ne q$）这同样给出 $n - 1$ 个独立的 $\mathbb F_2$-线性方程！总独立方程数为 $n + (n - 1) = 2n - 1$，故解数为 $2^{2 \cdot \frac{n(n+1)}{2} - (2n-1)} = 2^{2\binom{n}{2} + 1}$。
     综上，对一切 $L$ 与 $n \ge 1$ 恒有 $|\mathscr R_{L,2}(I_n)| = 2^{e_L \binom{n}{2} + 1}$。
   - **Cayley 变换计算 $|\Gamma_L(n,2) / \Gamma_L(n,M)|$（$M \ge 2$）：**
     对任意 $O \in \Gamma_L(n, 2)$，因 $\mathcal O_L$ 为整环，$\det(O) \in \{\pm 1\}$；但 $O \equiv I_n \pmod{4\mathcal O_L} \implies \det(O) \equiv 1 \pmod{4\mathcal O_L}$，而 $-1 \not\equiv 1 \pmod{4\mathcal O_L}$（因 $2 \notin 4\mathcal O_L$），故对一切 $m \ge 2$ 有 $\Gamma_L(n, m) = \operatorname{SO}_n^{(m)}(\mathcal O_L)$。
     令 $\mathfrak{so}_n(\mathcal O_L) := \{K \in M_n(\mathcal O_L) : K^{\mathsf T} = -K\}$，因 $\mathcal O_L$ 无 $2$-挠，它是秩为 $\binom{n}{2}$ 的自由 $\mathcal O_L$-模。对一切 $m \ge 2$，验证 Cayley 映射
     \[
     \Psi : 2^{m-1}\mathfrak{so}_n(\mathcal O_L) \longrightarrow \Gamma_L(n, m), \qquad K \longmapsto (I_n - K)(I_n + K)^{-1}
     \]
     为双射：一方面，因 $K \in 2^{m-1} M_n(\mathcal O_L)$（$m-1 \ge 1$），$I_n + K \in \operatorname{GL}_n(\mathcal O_L)$，易验 $\Psi(K)^{\mathsf T}\Psi(K) = I_n$ 且 $\Psi(K) - I_n = -2K(I_n + K)^{-1} \in 2^m M_n(\mathcal O_L)$，故 $\Psi(K) \in \Gamma_L(n, m)$；另一方面，若 $O = I_n + 2^m Y \in \Gamma_L(n, m)$（$m \ge 2$），则 $I_n + O = 2(I_n + 2^{m-1} Y)$，其中 $I_n + 2^{m-1} Y \in \operatorname{GL}_n(\mathcal O_L)$，定义逆映射 $K := (I_n - O)(I_n + O)^{-1} = -2^{m-1} Y(I_n + 2^{m-1} Y)^{-1} \in 2^{m-1} M_n(\mathcal O_L)$，由 $O^{\mathsf T} = O^{-1}$ 知 $K^{\mathsf T} = -K$ 且 $(I_n - K)(I_n + K)^{-1} = O$。
     因此对一切 $M \ge 2$：
     \[
     |\Gamma_L(n, 2) / \Gamma_L(n, M)| = \left|2\mathfrak{so}_n(\mathcal O_L) / 2^{M-1}\mathfrak{so}_n(\mathcal O_L)\right| = |\mathcal O_L / 2^{M-2}\mathcal O_L|^{\binom{n}{2}} = 2^{e_L(M-2)\binom{n}{2}}.
     \]
     乘上 $|\Gamma_L(n, 1) / \Gamma_L(n, 2)| = 2^{e_L\binom{n}{2} + 1}$，得 $|\mathscr R_{L,M}(I_n)| = 2^{e_L(M-1)\binom{n}{2} + 1}$；对 $i = 1, \dots, r$ 连乘即得 $|\mathscr R_{L,M}(A)| = 2^{r + e_L(M-1)\kappa}$。
   - **计算 $|\mathscr C_{L,M}(A)|$（$M \ge 3$）：**
     由第二步，约化映射 $\pi_{M, M-1} : \mathscr C_{L,M}(I_n) \twoheadrightarrow \mathscr R_{L,M-1}(I_n)$（因 $M - 1 \ge 2$）满射。任取 $\bar O \in \mathscr R_{L,M-1}(I_n)$ 及其真解提升 $O \in \Gamma_L(n, 1)$，则 $\bar O$ 在 $M_n(\mathcal O_L / 2^M\mathcal O_L)$ 中的全部提升唯一表为 $\widetilde O = O(I_n + 2^{M-1} Z)$（$Z \in M_n(\mathcal O_L / 2\mathcal O_L)$）。因 $2(M-1) \ge M + 1 > M$，有
     \[
     \widetilde O^{\mathsf T} \widetilde O \equiv I_n + 2^{M-1}(Z + Z^{\mathsf T}) \equiv I_n \pmod{2^M\mathcal O_L} \iff Z^{\mathsf T} = Z \in \operatorname{Sym}_n(\mathcal O_L / 2\mathcal O_L),
     \]
     故每条纤维大小恒为 $|\operatorname{Sym}_n(\mathcal O_L / 2\mathcal O_L)| = 2^{e_L \frac{n(n+1)}{2}}$。对所有块连乘：
     \[
     |\mathscr C_{L,M}(A)| = |\mathscr R_{L,M-1}(A)| \cdot 2^{e_L(\kappa + d)} = 2^{r + e_L(M-2)\kappa} \cdot 2^{e_L(\kappa + d)} = 2^{r + e_L d + e_L(M-1)\kappa}. \quad \blacksquare
     \]

---

## 3. 目标 2 的完整解答与证明

### 3.1 明确结论陈述（目标 2）

固定 $\mu \in \{-1, 2\}$ 与 $M \ge 2$，记 $d = \sum_{i=1}^r n_i$，$\kappa = \sum_{i=1}^r \binom{n_i}{2}$。

1. **不动点集 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 与 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 的具体矩阵类及与基域集合的精确关系：**
   - **对 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$（一切合法 $A$ 及一切 $M \ge 2$）：**
     每个不动类唯一表示为基域类与高阶对称微扰之和（或乘积）：
     \[
     \mathscr C_{K_\mu,M}(A)^{\sigma_\mu} = \left\{ \bar U_0 + 2^{M-1}\theta_\mu \bar W \;:\; \bar U_0 \in \mathscr C_{F,M}(A),\ \bar W \in \mathcal W_C \right\} = \mathscr C_{F,M}(A) \cdot (I_d + 2^{M-1}\theta_\mu \mathcal W_C),
     \]
     映射 $(\bar U_0, \bar W) \mapsto \bar U_0 + 2^{M-1}\theta_\mu \bar W$ 是双射；与基域矩阵类相交给出精确等式：
     \[
     \mathscr C_{K_\mu,M}(A) \cap M_d(\mathcal O_F / 2^M\mathcal O_F) = \mathscr C_{K_\mu,M}(A)^{\sigma_\mu} \cap M_d(\mathcal O_F / 2^M\mathcal O_F) = \mathscr C_{F,M}(A) \quad (\text{对应 } \bar W = 0).
     \]
   - **对 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$：**
     若 $\exists i, \delta_i(A) = 1$，则 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu} = \mathscr R_{F,M}(A) = \emptyset$。
     若 $\forall i, \delta_i(A) = 0$，定义扭元 $\eta_{\mu,M} \in (\mathcal O_\mu / 2^M\mathcal O_\mu)^{\sigma_\mu}$ 为：
     \[
     \eta_{\mu,M} := \begin{cases} 2(1 + \theta_{-1}) \bmod 4\mathcal O_{-1}, & \text{若 } M = 2 \text{ 且 } \mu = -1, \\ 2^{M-1}\theta_\mu \bmod 2^M\mathcal O_\mu, & \text{若 } M \ge 3 \text{ 或 } (M = 2,\ \mu = 2). \end{cases}
     \]
     则映射 $(\bar U_0, \bar W) \mapsto \bar U_0 + \eta_{\mu,M}\bar W$ 给出双射：
     \[
     \mathscr R_{K_\mu,M}(A)^{\sigma_\mu} = \left\{ \bar U_0 + \eta_{\mu,M}\bar W \;:\; \bar U_0 \in \mathscr R_{F,M}(A),\ \bar W \in \mathcal W_R \right\} = \mathscr R_{F,M}(A) \cdot (I_d + \eta_{\mu,M}\mathcal W_R).
     \]
     （注：当 $M=2, \mu=-1$ 时，$\bar U = (\bar U_0 + 2\bar W) + 2\theta_{-1}\bar W$，若 $\bar W \in \mathcal W_R$ 的某行非对角元之和为奇，则其实部 $\bar U_0 + 2\bar W$ 落在 $\mathscr C_{F,2}(A) \setminus \mathscr R_{F,2}(A)$ 而非 $\mathscr R_{F,2}(A)$ 中！）
     且对一切 $M \ge 2$、$\mu \in \{-1, 2\}$，与基域矩阵类相交均有精确下降等式：
     \[
     \mathscr R_{K_\mu,M}(A) \cap M_d(\mathcal O_F / 2^M\mathcal O_F) = \mathscr R_{K_\mu,M}(A)^{\sigma_\mu} \cap M_d(\mathcal O_F / 2^M\mathcal O_F) = \mathscr R_{F,M}(A) \quad (\text{对应 } \bar W = 0).
     \]

2. **固定点数与 $\langle \sigma_\mu \rangle$-轨道数的闭式公式：**
   - **对 $\mathscr C_{K_\mu,M}(A)$：**
     - 当 $M = 2$（任意合法 $A$）：$\sigma_\mu$ 在整个 $\mathscr C_{K_\mu,2}(A)$ 上平凡作用，故
       \[
       \left|\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}\right| = \left|\mathscr C_{K_\mu,2}(A) / \langle\sigma_\mu\rangle\right| = 2^{2(\kappa + d)}.
       \]
     - 当 $M \ge 3$：若 $\exists i, \delta_i(A) = 1$，固定点数与轨道数均为 $0$；若 $\forall i, \delta_i(A) = 0$，则
       \[
       \left|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\right| = 2^{\,r + 2d + M\kappa}, \qquad \left|\mathscr C_{K_\mu,M}(A) / \langle\sigma_\mu\rangle\right| = 2^{\,r + 2d + M\kappa - 1}\!\left(2^{(M-2)\kappa} + 1\right).
       \]
   - **对 $\mathscr R_{K_\mu,M}(A)$（一切 $M \ge 2$ 统一公式）：**
     若 $\exists i, \delta_i(A) = 1$，固定点数与轨道数均为 $0$；若 $\forall i, \delta_i(A) = 0$，则
     \[
     \left|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\right| = 2^{\,r + M\kappa}, \qquad \left|\mathscr R_{K_\mu,M}(A) / \langle\sigma_\mu\rangle\right| = 2^{\,r + M\kappa - 1}\!\left(2^{(M-2)\kappa} + 1\right).
     \]

3. **从精度 $M+1$ 到 $M$（$M \ge 2$）的约化像 $\operatorname{im}(\pi_{M+1,M})$ 与全部非空纤维大小：**
   - 若 $\exists i, \delta_i(A) = 1$：因 $M + 1 \ge 3$，四个源集合 $\mathscr R_{L,M+1}(A)$、$\mathscr C_{L,M+1}(A)$、$\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}$、$\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$ 全为空集，故约化像均为空集，不存在非空纤维。
   - 若 $\forall i, \delta_i(A) = 0$：全部非空纤维均等势，具体如下表（$L \in \{F, K_{-1}, K_2\}$，$e_L = [L:\mathbb Q_2]$）：
     - $\pi_{M+1,M} : \mathscr R_{L,M+1}(A) \to \mathscr R_{L,M}(A)$：**约化像** $= \mathscr R_{L,M}(A)$（满射），**每个非空纤维大小** $= 2^{e_L \kappa}$（即 $L=F$ 时为 $2^\kappa$，$L=K_\mu$ 时为 $2^{2\kappa}$）；
     - $\pi_{M+1,M} : \mathscr C_{L,M+1}(A) \to \mathscr C_{L,M}(A)$：**约化像** $= \mathscr R_{L,M}(A)$，**每个非空纤维大小** $= 2^{e_L(\kappa + d)}$（即 $L=F$ 时为 $2^{\kappa+d}$，$L=K_\mu$ 时为 $2^{2(\kappa+d)}$）；
     - $\pi_{M+1,M} : \mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu} \to \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$：**约化像** $= \mathscr R_{F,M}(A)$，**每个非空纤维大小** $= 2^{2\kappa}$；
     - $\pi_{M+1,M} : \mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu} \to \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$：**约化像** $= \mathscr R_{F,M}(A)$，**每个非空纤维大小** $= 2^{2(\kappa + d)}$。

4. **提升为 $\sigma_\mu$-固定真解的类，以及逐层相容固定矩阵类序列在精度 $M$ 的分量：**
   无论是在 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 中考察，还是在 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 中考察，下述三个子集**完全重合**，且恰等于基域可提升集 $\mathscr R_{F,M}(A)$：
   1. 能提升为 $\sigma_\mu$-固定真正解 $U \in \mathscr S_{K_\mu}(A)^{\sigma_\mu}$ 的固定矩阵类集合；
   2. 能作为一条逐层相容序列 $(\bar U_m)_{m \ge 2} \in \varprojlim_m \mathscr R_{K_\mu,m}(A)^{\sigma_\mu}$ 在精度 $M$ 的分量 $\bar U_M$ 的集合；
   3. 能作为一条逐层相容序列 $(\bar U_m)_{m \ge 2} \in \varprojlim_m \mathscr C_{K_\mu,m}(A)^{\sigma_\mu}$ 在精度 $M$ 的分量 $\bar U_M$ 的集合。
   显式判别条件为：
   - 对 $\bar U \in \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$：$\bar U \in \mathscr R_{F,M}(A) \iff \bar U \in M_d(\mathcal O_F / 2^M\mathcal O_F)$（即参数表示中 $\bar W = 0$）；
   - 对 $\bar U \in \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$：$\bar U \in \mathscr R_{F,M}(A) \iff \bar U \in M_d(\mathcal O_F / 2^M\mathcal O_F)$ 且对任一提升 $U \in M_d(\mathbb Z_2)$ 有 $\operatorname{diag}(U^{\mathsf T} U - I_d) \equiv 0 \pmod{2^{M+1}\mathbb Z_2}$。
   *否定现象的实际例子：*
   - 在 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu} \setminus \mathscr R_{F,M}(A)$ 中：对任意 $r, (n_1,\dots,n_r)$ 及 $M \ge 2$，取 $A_i = E_i$，$\bar U = \operatorname{diag}(1 + 2^{M-1}\theta_\mu, 1, \dots, 1) \bmod 2^M\mathcal O_\mu \in \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$，因含非零 $\theta_\mu$-部，故不能提升到 $\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$（更不能进入任何相容序列或提升为 $\sigma_\mu$-固定真解）。
   - 在 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu} \setminus \mathscr R_{F,M}(A)$ 中（当且仅当某 $n_{i_0} \ge 2$ 且 $A$ 可行时非空）：取 $A_i = E_i$，在块 $I_{i_0}$ 的前两坐标置 $\begin{pmatrix} 1 & \eta_{\mu,M} \\ \eta_{\mu,M} & 1 \end{pmatrix} \bmod 2^M\mathcal O_\mu$、其余坐标置 $I$，则该类属于 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$（可提升为 $\mathscr S_{K_\mu}(A)$ 中的非不动真解，见第 4 节显式公式），但不在 $\mathscr R_{F,M}(A)$ 中，故既不能提升到 $\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}$（甚至不能提升到 $\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$），也不能提升为 $\mathscr S_{K_\mu}(A)^{\sigma_\mu}$ 中的真解。

---

### 3.2 目标 2 的证明

#### 第一步：$(\mathcal O_\mu / 2^M\mathcal O_\mu)^{\sigma_\mu}$ 与 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 的刻画
在直和分解 $\mathcal O_\mu / 2^M\mathcal O_\mu = (\mathbb Z / 2^M\mathbb Z) \oplus (\mathbb Z / 2^M\mathbb Z)\theta_\mu$ 下，
\[
\sigma_\mu(\bar x + \bar y\theta_\mu) = \bar x - \bar y\theta_\mu = \bar x + \bar y\theta_\mu \iff 2\bar y \equiv 0 \pmod{2^M} \iff \bar y \in 2^{M-1}(\mathbb Z / 2^M\mathbb Z).
\]
因此任何 $\sigma_\mu$-固定的矩阵类 $\bar U \in M_d(\mathcal O_\mu / 2^M\mathcal O_\mu)^{\sigma_\mu}$ 唯一表为
\[
\bar U = \bar U_0 + 2^{M-1}\theta_\mu \bar W, \qquad \bar U_0 \in M_d(\mathbb Z / 2^M\mathbb Z),\quad \bar W \in M_d(\mathbb F_2).
\]
（当 $\bar U_0 \equiv I_d \pmod 2$ 时，因 $2^{M-1}\bar U_0 \equiv 2^{M-1} I_d \pmod{2^M}$，亦有 $\bar U = \bar U_0(I_d + 2^{M-1}\theta_\mu \bar W)$。）
因 $M \ge 2 \implies 2(M-1) \ge M \implies (2^{M-1}\theta_\mu)^2 = \mu 2^{2M-2} \equiv 0 \pmod{2^M\mathcal O_\mu}$，将 $\bar U = \bar U_0 + 2^{M-1}\theta_\mu \bar W$ 代入 $\mathscr C_{K_\mu,M}(A)$ 的定义条件并分离 $\{1, \theta_\mu\}$ 分量：
1. $\bar U \equiv I_d \pmod{2\mathcal O_\mu} \iff \bar U_0 \equiv I_d \pmod 2$（因 $2^{M-1} \equiv 0 \pmod 2$）；
2. 利用 $2^{M-1}\bar U_0 \equiv 2^{M-1} I_d \pmod{2^M}$，有
   \[
   \bar U^{\mathsf T}\bar U = \bar U_0^{\mathsf T}\bar U_0 + 2^{M-1}\theta_\mu(\bar W + \bar W^{\mathsf T}) = I_d \iff \bar U_0^{\mathsf T}\bar U_0 = I_d \text{ 且 } \bar W^{\mathsf T} = \bar W \text{ in } M_d(\mathbb F_2);
   \]
3. 利用 $A_i \equiv E_i \pmod 2$ 与 $\bar U_0 \equiv I_d \pmod 2$，有 $\bar U^{\mathsf T} A_i \bar U = \bar U_0^{\mathsf T} A_i \bar U_0 + 2^{M-1}\theta_\mu(\bar W^{\mathsf T} E_i + E_i \bar W)$，与 $E_j$ 取换位子得：
   - $1$-分量：$[\bar U_0^{\mathsf T} A_i \bar U_0, E_j] = 0$（$\forall i, j$），综合 1、2 知 $\bar U_0 \in \mathscr C_{F,M}(A)$；
   - $\theta_\mu$-分量：在 $M_d(\mathbb F_2)$ 中 $[\bar W E_i + E_i \bar W, E_j] = 0$（$\forall i, j$）。对 $j \ne k$ 取 $i = j$ 并左乘 $E_j$、右乘 $E_k$ 得 $E_j \bar W E_k = 0$；反之若 $\bar W$ 分块对角（$[\bar W, E_i] = 0$），则 $\bar W E_i + E_i \bar W = 2\bar W E_i = 0$。故 $\bar W \in \mathcal W_C$。

这证明了 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu} = \mathscr C_{F,M}(A) + 2^{M-1}\theta_\mu \mathcal W_C$ 的唯一参数化及与基域的交集关系。

---

#### 第二步：$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 的精确矩阵类
设 $\forall i, \delta_i(A) = 0$（否则为空）。取 $\bar U = \bar U_1 + 2^{M-1}\theta_\mu \bar W \in \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$，其中 $\bar U_1 \in \mathscr C_{F,M}(A)$，$\bar W \in \mathcal W_C$。任取提升 $U_1 \in M_d(\mathbb Z_2)$ 与对称分块对角提升 $W \in M_d(\mathbb Z_2)$，令 $U = U_1 + 2^{M-1}\theta_\mu W$。由目标 1 的可提升判准，$\bar U \in \mathscr R_{K_\mu,M}(A)$ 当且仅当对一切 $p = 1, \dots, d$，
\[
(U^{\mathsf T} U - I_d)_{pp} = \left[(U_1^{\mathsf T} U_1 - I_d)_{pp} + \mu 2^{2M-2}(W^{\mathsf T} W)_{pp}\right] + 2^M \theta_\mu (U_1^{\mathsf T} W)_{pp} \equiv 0 \pmod{2^{M+1}\mathcal O_\mu}.
\]
- 先看 $\theta_\mu$-分量：因 $U_1 \equiv I_d \pmod 2$，$(U_1^{\mathsf T} W)_{pp} \equiv W_{pp} \pmod 2$，故 $2^M(U_1^{\mathsf T} W)_{pp} \equiv 0 \pmod{2^{M+1}} \iff \bar W_{pp} = 0$（$\forall p$），即 $\bar W \in \mathcal W_R$！
- 再看 $1$-分量：
  - **情形 A（$M \ge 3$，或 $M = 2$ 且 $\mu = 2$）：** 此时 $v_2(\mu 2^{2M-2}) \ge M + 1$，故 $\mu 2^{2M-2}(W^{\mathsf T} W)_{pp} \equiv 0 \pmod{2^{M+1}}$，方程化为 $(U_1^{\mathsf T} U_1 - I_d)_{pp} \equiv 0 \pmod{2^{M+1}}$（$\forall p$），由目标 1 对 $L = F$ 的判准，这恰等价于 $\bar U_1 \in \mathscr R_{F,M}(A)$！取 $\bar U_0 = \bar U_1$ 即得所证公式。
  - **情形 B（$M = 2$ 且 $\mu = -1$）：** 令 $\bar U_0 := \bar U_1 - 2\bar W \pmod 4$。因 $\bar W \in \mathcal W_R \subseteq \mathcal W_C$，易见 $\bar U_1 \in \mathscr C_{F,2}(A) \iff \bar U_0 \in \mathscr C_{F,2}(A)$，且 $\bar U = \bar U_0 + 2(1 + \theta_{-1})\bar W = \bar U_0 + \eta_{-1,2}\bar W$。取 $\bar U_0$ 的提升 $U_0 \in M_d(\mathbb Z_2)$，因 $U_0 \equiv I_d \pmod 2$ 且 $\bar W \in \mathcal W_R$ 对角元为 $0$（取空心对称整提升 $W_{pp} = 0$），令 $U' = U_0(I_d + 2(1 + \theta_{-1})W) \equiv \bar U \pmod{4\mathcal O_{-1}}$，利用 $(1 + \theta_{-1})^2 = 2\theta_{-1}$ 计算：
    \[
    (U')^{\mathsf T} U' - I_d = (I_d + 2(1 + \theta_{-1})W) U_0^{\mathsf T} U_0 (I_d + 2(1 + \theta_{-1})W) - I_d \equiv (U_0^{\mathsf T} U_0 - I_d) + 4(1 + \theta_{-1})W + 8\theta_{-1} W^2 \pmod{8\mathcal O_{-1}}.
    \]
    因 $W_{pp} = 0$，第 $p$ 个对角元模 $8\mathcal O_{-1}$ 恰为 $(U_0^{\mathsf T} U_0 - I_d)_{pp} \bmod 8$！故 $\bar U \in \mathscr R_{K_{-1},2}(A) \iff (U_0^{\mathsf T} U_0 - I_d)_{pp} \equiv 0 \pmod 8\ (\forall p) \iff \bar U_0 \in \mathscr R_{F,2}(A)$。
    特别地，若 $\bar U \in M_d(\mathcal O_F / 2^M\mathcal O_F)$，则其 $\theta_\mu$-分量为 $0 \implies \bar W = 0 \implies \bar U = \bar U_0 \in \mathscr R_{F,M}(A)$，故 $\mathscr R_{K_\mu,M}(A) \cap M_d(\mathcal O_F / 2^M\mathcal O_F) = \mathscr R_{F,M}(A)$。

---

#### 第三步：固定点数与轨道数
由第一步与第二步双射：
- $|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}| = |\mathscr C_{F,M}(A)| \cdot |\mathcal W_C| = |\mathscr C_{F,M}(A)| \cdot 2^{\kappa + d}$，代入第 2 节 $|\mathscr C_{F,M}(A)|$ 公式即得 $M = 2$ 时为 $2^{2(\kappa + d)}$，$M \ge 3$（可行时）为 $2^{r + d + (M-1)\kappa} \cdot 2^{\kappa + d} = 2^{r + 2d + M\kappa}$；
- 可行时 $|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}| = |\mathscr R_{F,M}(A)| \cdot |\mathcal W_R| = 2^{r + (M-1)\kappa} \cdot 2^\kappa = 2^{r + M\kappa}$。
因 $|\langle\sigma_\mu\rangle| = 2$，对任意有限 $\langle\sigma_\mu\rangle$-集 $X$，轨道只含单点轨道（不动点）与二元轨道，故轨道数恒为 $|X / \langle\sigma_\mu\rangle| = \frac{1}{2}(|X| + |X^{\sigma_\mu}|)$。代入 $|X|$ 与 $|X^{\sigma_\mu}|$ 化简即得 3.1 节全部轨道数公式。

---

#### 第四步：约化像、非空纤维大小及真解提升与相容序列刻画
设 $\forall i, \delta_i(A) = 0$ 且 $M \ge 2$。
1. **$\mathscr R_{L,M+1}(A) \to \mathscr R_{L,M}(A)$：** 两者均为 $\mathscr S_L(A)$ 的同态/陪集约化像，故满射；左乘 $U_*^{-1}$ 后映射为有限群满同态，所有纤维均为核 $\prod_{i=1}^r (\Gamma_L(n_i, M) / \Gamma_L(n_i, M+1))$ 的陪集，大小恒为 $|\mathscr R_{L,M+1}(A)| / |\mathscr R_{L,M}(A)| = 2^{e_L \kappa}$。
2. **$\mathscr C_{L,M+1}(A) \to \mathscr C_{L,M}(A)$：** 第 2.2 节第二步与第三步已证其像恰为 $\mathscr R_{L,M}(A)$，且每条非空纤维大小恒为 $\prod_{i=1}^r |\operatorname{Sym}_{n_i}(\mathcal O_L / 2\mathcal O_L)| = 2^{e_L(\kappa + d)}$。
3. **$\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu} \to \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$：** 因 $M + 1 \ge 3$，$\eta_{\mu, M+1} = 2^M\theta_\mu$，故源集中任意元素唯一表为 $\widetilde{\bar U}_0 + 2^M\theta_\mu \bar W$（$\widetilde{\bar U}_0 \in \mathscr R_{F,M+1}(A)$，$\bar W \in \mathcal W_R$）。模 $2^M\mathcal O_\mu$ 约化时 $2^M\theta_\mu \bar W \equiv 0 \pmod{2^M\mathcal O_\mu}$ 完全消去！故
   \[
   \pi_{M+1,M}(\widetilde{\bar U}_0 + 2^M\theta_\mu \bar W) = \pi_{M+1,M}(\widetilde{\bar U}_0).
   \]
   由性质 1（取 $L = F$），当 $\widetilde{\bar U}_0$ 跑遍 $\mathscr R_{F,M+1}(A)$ 时，$\pi_{M+1,M}(\widetilde{\bar U}_0)$ 满射到 $\mathscr R_{F,M}(A)$ 且对每个 $\bar U_0 \in \mathscr R_{F,M}(A)$ 有 $2^\kappa$ 个 $\widetilde{\bar U}_0$；再乘上自由任取的 $\bar W \in \mathcal W_R$（$2^\kappa$ 个），知约化像恰为 $\mathscr R_{F,M}(A)$，且每条非空纤维大小恒为 $2^\kappa \cdot 2^\kappa = 2^{2\kappa}$。
4. **$\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu} \to \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$：** 同理，源集中任意元素唯一表为 $\widetilde{\bar U}_0 + 2^M\theta_\mu \bar W$（$\widetilde{\bar U}_0 \in \mathscr C_{F,M+1}(A)$，$\bar W \in \mathcal W_C$），模 $2^M\mathcal O_\mu$ 约化消去 $2^M\theta_\mu \bar W$，化为 $\pi_{M+1,M}(\widetilde{\bar U}_0)$。由性质 2（取 $L = F$），$\operatorname{im}(\mathscr C_{F,M+1}(A) \to \mathscr C_{F,M}(A)) = \mathscr R_{F,M}(A)$ 且每个基域纤维大小为 $2^{\kappa + d}$；再乘上自由任取的 $\bar W \in \mathcal W_C$（$2^{\kappa + d}$ 个），知约化像**同样恰为 $\mathscr R_{F,M}(A)$**，且每条非空纤维大小恒为 $2^{\kappa + d} \cdot 2^{\kappa + d} = 2^{2(\kappa + d)}$。
5. **提升为 $\sigma_\mu$-固定真解与逐层相容序列分量：**
   - 因 $\mathcal O_\mu^{\sigma_\mu} = \mathbb Z_2 = \mathcal O_F$，有 $\mathscr S_{K_\mu}(A)^{\sigma_\mu} = \mathscr S_F(A)$，故能提升为 $\sigma_\mu$-固定真解的精度 $M$ 类集合按定义就是 $\mathscr R_{F,M}(A)$。
   - 若 $(\bar U_m)_{m \ge 2}$ 是 $\prod_{m \ge 2} \mathscr C_{K_\mu,m}(A)^{\sigma_\mu}$（或 $\prod_{m \ge 2} \mathscr R_{K_\mu,m}(A)^{\sigma_\mu}$）中的逐层相容序列，则仅由第 $M+1 \to M$ 一步相容性 $\bar U_M = \pi_{M+1,M}(\bar U_{M+1})$ 及上述性质 3、4，即强制 $\bar U_M \in \mathscr R_{F,M}(A)$！反之，若 $\bar U_M \in \mathscr R_{F,M}(A)$，取真解 $U \in \mathscr S_F(A)$ 使其模 $2^M$ 为 $\bar U_M$，令 $\bar U_m := U \bmod 2^m\mathcal O_\mu \in \mathscr R_{F,m}(A)$（$\forall m \ge 2$），即给出通过 $\bar U_M$ 的逐层相容固定矩阵类序列（事实上，对任意相容序列 $(\bar U_m)_{m \ge 2}$，对每个 $m$ 均有 $\bar U_m = \pi_{m+1,m}(\bar U_{m+1}) \in \mathscr R_{F,m}(A)$，故逆极限 $\varprojlim_m \mathscr C_{K_\mu,m}(A)^{\sigma_\mu} = \varprojlim_m \mathscr R_{K_\mu,m}(A)^{\sigma_\mu} = \mathscr S_F(A)$）。$\blacksquare$

---

## 4. 目标 3 的完整解答与证明

### 4.1 明确结论陈述（目标 3）

固定块秩 $(n_1, \dots, n_r)$、$\mu \in \{-1, 2\}$ 和 $M \ge 2$：

1. **最大下降精度 $N \in \{0, \dots, M\}$ 与允许精确下降的块秩：**
   \[
   N = \begin{cases} M, & \text{若 } n_1 = n_2 = \dots = n_r = 1 \ (\text{即 } \max_{1 \le i \le r} n_i = 1), \\ M - 1, & \text{若存在 } i_0 \in \{1, \dots, r\} \text{ 使 } n_{i_0} \ge 2 \ (\text{即 } \max_{1 \le i \le r} n_i \ge 2). \end{cases}
   \]
   特别地，允许普遍精确下降（$N = M$）的块秩**当且仅当**全部分块秩均为 $1$（$n_1 = \dots = n_r = 1$）。

2. **给定具体 $(A, U)$（其中 $U \in \mathscr S_{K_\mu}(A)$ 且 $\sigma_\mu(U) \equiv U \pmod{2^M\mathcal O_\mu}$）能取 $N = M$ 的必要充分条件：**
   下述条件彼此等价，均为存在 $W \in \mathscr S_F(A)$ 使 $U \equiv W \pmod{2^M\mathcal O_\mu}$ 的充要条件：
   - $\sigma_\mu(U) \equiv U \pmod{2^{M+1}\mathcal O_\mu}$；
   - $U \in M_d(\mathbb Z_2) + 2^M M_d(\mathcal O_\mu)$（即写 $U = X + Y\theta_\mu$，$X, Y \in M_d(\mathbb Z_2)$，有 $Y \equiv 0 \pmod{2^M\mathbb Z_2}$，亦即 $U \bmod 2^M\mathcal O_\mu \in M_d(\mathcal O_F / 2^M\mathcal O_F)$）。

---

### 4.2 目标 3 的证明与任意精度统一反例构造

#### 第一步：精确下降块秩（$n_1 = \dots = n_r = 1$ 时 $N = M$）的证明
设 $n_1 = \dots = n_r = 1$（此时 $\kappa = 0$）。对任意合法 $A$，若 $\mathscr S_{K_\mu}(A) = \emptyset$ 结论空真；若存在 $U \in \mathscr S_{K_\mu}(A)$，由第 2 节可行性判准知 $\mathscr S_F(A) \ne \emptyset$，取 $U_* \in \mathscr S_F(A)$。由引理 1.2(2)，$U_*^{-1} U = \operatorname{diag}(c_1, \dots, c_r)$，其中每个 $c_i \in \mathcal O_\mu$ 满足 $c_i^2 = 1$。因 $\mathcal O_\mu$ 是整环，$(c_i - 1)(c_i + 1) = 0 \implies c_i \in \{1, -1\} \subseteq \mathbb Z_2$。故 $U = U_* \operatorname{diag}(c_1, \dots, c_r) \in \mathscr S_F(A)$，直接取 $W = U \in \mathscr S_F(A)$ 即有 $U = W \equiv W \pmod{2^M\mathcal O_\mu}$，故 $N = M$。

---

#### 第二步：给定 $(A, U)$ 能取 $N = M$ 的充要条件证明
设 $U \in \mathscr S_{K_\mu}(A)$ 满足 $\sigma_\mu(U) \equiv U \pmod{2^M\mathcal O_\mu}$。写 $U = X + Y\theta_\mu$（$X, Y \in M_d(\mathbb Z_2)$）。
- 注意 $\sigma_\mu(U) - U = -2Y\theta_\mu$，故
  \[
  \sigma_\mu(U) \equiv U \pmod{2^{M+1}\mathcal O_\mu} \iff 2Y \equiv 0 \pmod{2^{M+1}\mathbb Z_2} \iff Y \equiv 0 \pmod{2^M\mathbb Z_2} \iff U \bmod 2^M\mathcal O_\mu \in M_d(\mathcal O_F / 2^M\mathcal O_F).
  \]
- **必要性：** 若存在 $W \in \mathscr S_F(A) \subseteq M_d(\mathbb Z_2)$ 使 $U \equiv W \pmod{2^M\mathcal O_\mu}$，比较 $\theta_\mu$-分量立得 $Y \equiv 0 \pmod{2^M\mathbb Z_2}$。
- **充分性：** 若 $Y \equiv 0 \pmod{2^M\mathbb Z_2}$，则 $\bar U := U \bmod 2^M\mathcal O_\mu$ 同时属于 $\mathscr R_{K_\mu,M}(A)$ 与 $M_d(\mathcal O_F / 2^M\mathcal O_F)$。由第 3 节已证的精确交集等式 $\mathscr R_{K_\mu,M}(A) \cap M_d(\mathcal O_F / 2^M\mathcal O_F) = \mathscr R_{F,M}(A)$，知 $\bar U \in \mathscr R_{F,M}(A)$，即存在 $W \in \mathscr S_F(A)$ 使 $W \bmod 2^M\mathcal O_\mu = \bar U$，即 $U \equiv W \pmod{2^M\mathcal O_\mu}$。

---

#### 第三步：一般下界 $N \ge M - 1$ 的证明
设 $U \in \mathscr S_{K_\mu}(A)$ 满足 $\sigma_\mu(U) \equiv U \pmod{2^M\mathcal O_\mu}$。因 $\mathscr S_{K_\mu}(A) \ne \emptyset$，由第 2 节知 $\forall i, \delta_i(A) = 0$，故 $\mathscr S_F(A) \ne \emptyset$。
- **若 $M = 2$（即 $M - 1 = 1$）：** 任取 $W \in \mathscr S_F(A)$，由定义 $U \equiv I_d \pmod{2\mathcal O_\mu}$ 且 $W \equiv I_d \pmod{2\mathbb Z_2}$，故 $U \equiv I_d \equiv W \pmod{2^1\mathcal O_\mu}$。
- **若 $M \ge 3$：** 由 $\sigma_\mu(U) \equiv U \pmod{2^M\mathcal O_\mu}$ 可写 $U = X + 2^{M-1} Z\theta_\mu$（$X, Z \in M_d(\mathbb Z_2)$），从而 $\sigma_\mu(U) \equiv U \pmod{2^{(M-1)+1}\mathcal O_\mu}$！将第二步已证的充要条件应用于精度 $M' := M - 1 \ge 2$，立即推出存在 $W \in \mathscr S_F(A)$ 使 $U \equiv W \pmod{2^{M-1}\mathcal O_\mu}$！
（注：利用第 3 节公式亦可一步看出——$\bar U = U \bmod 2^M\mathcal O_\mu \in \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 表为 $\bar U_0 + \eta_{\mu,M}\bar W$，其中 $\bar U_0 \in \mathscr R_{F,M}(A)$。无论 $M \ge 3$ 还是 $M = 2$，恒有 $\eta_{\mu,M} \equiv 0 \pmod{2^{M-1}\mathcal O_\mu}$，故任取提升 $\bar U_0$ 的真解 $W \in \mathscr S_F(A)$ 即满足 $U \equiv \bar U_0 \equiv W \pmod{2^{M-1}\mathcal O_\mu}$！）

---

#### 第四步：当 $\max_i n_i \ge 2$ 时 $N = M - 1$ 最优性的统一显式反例构造（任意精度 $M \ge 2$）
设存在 $i_0 \in \{1, \dots, r\}$ 使 $n_{i_0} \ge 2$。对**任意** $\mu \in \{-1, 2\}$ 与**任意**整数 $M \ge 2$，我们给出完全统一的合法输入 $A$ 与真解 $U^{(M,\mu)} \in \mathscr S_{K_\mu}(A)$，使其满足 $\sigma_\mu(U^{(M,\mu)}) \equiv U^{(M,\mu)} \pmod{2^M\mathcal O_\mu}$，但对**一切** $W \in \mathscr S_F(A)$ 均有 $U^{(M,\mu)} \not\equiv W \pmod{2^M\mathcal O_\mu}$（从而 $N \le M - 1$）：

1. **合法输入 $A$ 的选取：**
   取 $A_i := E_i \in M_d(\mathbb Z_2)$（$i = 1, \dots, r$）（若希望同时满足 $A_i$ 非幂等且 $\sum_i A_i \ne I_d$，可改取 $A_i := 3 E_i$，其对应解集 $\mathscr S_L(A)$ 与 $E_i$ 完全相同）。显然 $A_i^{\mathsf T} = A_i$，$A_i A_j = A_j A_i$，$A_i \equiv E_i \pmod 2$。

2. **任意精度 $M \ge 2$ 下 $2 \times 2$ 正交块 $O_2^{(M,\mu)} \in \operatorname{SO}_2(\mathcal O_\mu)$ 的统一构造：**
   令反对称阵 $K_{M,\mu} = \begin{pmatrix} 0 & -\lambda_{M,\mu} \\ \lambda_{M,\mu} & 0 \end{pmatrix}$ 并置 $O_2^{(M,\mu)} := (I_2 - K_{M,\mu})(I_2 + K_{M,\mu})^{-1}$，按 $\mu$ 取参数 $\lambda_{M,\mu}$ 如下：

   - **情形 $\mu = 2$（一切 $M \ge 2$）：** 取 $\lambda_{M,2} := 2^{M-2}\theta_2 \in \mathcal O_2$。
     此时 $\lambda_{M,2}^2 = 2^{2M-3}$。因 $M \ge 2 \implies 2M - 3 \ge 1$，分母 $1 + 2^{2M-3} \in 1 + 2\mathbb Z_2 \subseteq \mathbb Z_2^\times$ 在 $\mathbb Z_2$ 中可逆！显式写出：
     \[
     O_2^{(M,2)} = \frac{1}{1 + 2^{2M-3}} \begin{pmatrix} 1 - 2^{2M-3} & 2^{M-1}\theta_2 \\ -2^{M-1}\theta_2 & 1 - 2^{2M-3} \end{pmatrix} \in M_2(\mathcal O_2).
     \]
     逐条核验：
     - $(O_2^{(M,2)})^{\mathsf T} O_2^{(M,2)} = \frac{(1 - 2^{2M-3})^2 + 2 \cdot 2^{2M-2}}{(1 + 2^{2M-3})^2} I_2 = I_2$；
     - 因 $1 \pm 2^{2M-3} \equiv 1 \pmod 2$ 且 $2^{M-1} \equiv 0 \pmod 2$（$M \ge 2$），有 $O_2^{(M,2)} \equiv I_2 \pmod{2\mathcal O_2}$；
     - $\sigma_2(O_2^{(M,2)}) - O_2^{(M,2)} = \frac{1}{1 + 2^{2M-3}}\begin{pmatrix} 0 & -2^M\theta_2 \\ 2^M\theta_2 & 0 \end{pmatrix} \in 2^M M_2(\mathcal O_2)$；
     - $(O_2^{(M,2)})_{1,2}$ 的 $\theta_2$-系数为 $\frac{2^{M-1}}{1 + 2^{2M-3}}$，其 $2$-进赋值恰为 $M - 1 < M$，故 $(O_2^{(M,2)})_{1,2} \notin \mathbb Z_2 + 2^M\mathcal O_2$。

   - **情形 $\mu = -1$（一切 $M \ge 2$）：** 取 $\lambda_{M,-1} := 2^{M-2}(1 + \theta_{-1}) \in \mathcal O_{-1}$。
     由 $(1 + \theta_{-1})^2 = 2\theta_{-1}$ 得 $\lambda_{M,-1}^2 = 2^{2M-3}\theta_{-1}$。因 $M \ge 2 \implies 2M - 3 \ge 1$ 且 $4M - 6 \ge 2$，分子分母同乘 $1 - 2^{2M-3}\theta_{-1}$ 将分母有理化为 $1 + 2^{4M-6} \in 1 + 4\mathbb Z_2 \subseteq \mathbb Z_2^\times$，显式写出：
     \[
     O_2^{(M,-1)} = \frac{1}{1 + 2^{4M-6}} \begin{pmatrix} (1 - 2^{4M-6}) - 2^{2M-2}\theta_{-1} & 2^{M-1}(1 + 2^{2M-3}) + 2^{M-1}(1 - 2^{2M-3})\theta_{-1} \\ -2^{M-1}(1 + 2^{2M-3}) - 2^{M-1}(1 - 2^{2M-3})\theta_{-1} & (1 - 2^{4M-6}) - 2^{2M-2}\theta_{-1} \end{pmatrix} \in M_2(\mathcal O_{-1}).
     \]
     逐条核验：
     - 作为反对称阵 $K_{M,-1}$（其中 $1 + \lambda_{M,-1}^2$ 范数为 $1 + 2^{4M-6} \in \mathbb Z_2^\times$，故 $I_2 + K_{M,-1} \in \operatorname{GL}_2(\mathcal O_{-1})$）的 Cayley 变换，恒有 $(O_2^{(M,-1)})^{\mathsf T} O_2^{(M,-1)} = I_2$；
     - 因 $4M - 6 \ge 2, 2M - 2 \ge 2, M - 1 \ge 1$，有 $O_2^{(M,-1)} \equiv I_2 \pmod{2\mathcal O_{-1}}$；
     - 在 $\sigma_{-1}(O_2^{(M,-1)}) - O_2^{(M,-1)}$ 中，对角元为 $\frac{2^{2M-1}}{1 + 2^{4M-6}}\theta_{-1}$（注意 $M \ge 2 \implies 2M - 1 \ge M + 1 > M$），非对角元为 $\mp \frac{2^M(1 - 2^{2M-3})}{1 + 2^{4M-6}}\theta_{-1}$，均属于 $2^M\mathcal O_{-1}$，故 $\sigma_{-1}(O_2^{(M,-1)}) \equiv O_2^{(M,-1)} \pmod{2^M\mathcal O_{-1}}$；
     - $(O_2^{(M,-1)})_{1,2}$ 的 $\theta_{-1}$-系数为 $\frac{2^{M-1}(1 - 2^{2M-3})}{1 + 2^{4M-6}}$，由于 $1 - 2^{2M-3}$ 与 $1 + 2^{4M-6}$ 均为奇数（$\mathbb Z_2^\times$ 中单位），其 $2$-进赋值恰为 $M - 1 < M$，故 $(O_2^{(M,-1)})_{1,2} \notin \mathbb Z_2 + 2^M\mathcal O_{-1}$。

3. **嵌入 $d \times d$ 矩阵：**
   取块 $I_{i_0}$ 的前两个坐标指标 $p_1 < p_2 \in I_{i_0}$，令 $U^{(M,\mu)} \in M_d(\mathcal O_\mu)$ 在 $\{p_1, p_2\} \times \{p_1, p_2\}$ 子块上等于 $O_2^{(M,\mu)}$，在其余坐标上等于恒等阵。则 $U^{(M,\mu)}$ 为分块对角正交阵，满足 $U^{(M,\mu)} \equiv I_d \pmod{2\mathcal O_\mu}$、$(U^{(M,\mu)})^{\mathsf T} U^{(M,\mu)} = I_d$、$[U^{(M,\mu)}, E_j] = 0$（故 $[(U^{(M,\mu)})^{\mathsf T} A_i U^{(M,\mu)}, E_j] = [A_i, E_j] = 0$），即 $U^{(M,\mu)} \in \mathscr S_{K_\mu}(A)$，且 $\sigma_\mu(U^{(M,\mu)}) \equiv U^{(M,\mu)} \pmod{2^M\mathcal O_\mu}$。
   然而对任意 $W \in \mathscr S_F(A) \subseteq M_d(\mathbb Z_2)$，$W_{p_1, p_2} \in \mathbb Z_2$ 的 $\theta_\mu$-系数为 $0$，而 $U^{(M,\mu)}_{p_1, p_2}$ 的 $\theta_\mu$-系数不能被 $2^M$ 整除，故 $U^{(M,\mu)} \not\equiv W \pmod{2^M\mathcal O_\mu}$。这证明了 $N = M - 1$ 对一切满足 $\max_i n_i \ge 2$ 的块秩、一切 $\mu \in \{-1, 2\}$ 及一切精度 $M \ge 2$ 严格最优。$\blacksquare$
