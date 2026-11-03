# 幂等元提升、逆极限与环分解

---

## S1　单层提升

设 $q: R \to S$ 为交换含幺环满射，$\ker q$ 中每个元素幂零。设 $e \in S$ 满足 $e^2 = e$。

### 1. 唯一性论证
设 $\tilde{e}_1, \tilde{e}_2 \in R$ 均为 $e$ 的幂等提升，即 $\tilde{e}_1^2 = \tilde{e}_1$、$\tilde{e}_2^2 = \tilde{e}_2$ 且 $q(\tilde{e}_1) = q(\tilde{e}_2) = e$。
令 $\delta = \tilde{e}_1 - \tilde{e}_2$。由于 $q(\delta) = e - e = 0$，故 $\delta \in \ker q$。依题设，$\delta$ 幂零，存在正整数 $m$ 使得 $\delta^m = 0$。

考虑元素 $\epsilon := \tilde{e}_1(1 - \tilde{e}_2) \in R$。
- **幂等性**：因 $R$ 交换，$\tilde{e}_1$ 与 $1 - \tilde{e}_2$ 可交换且均为幂等元，故
  $$\epsilon^2 = \tilde{e}_1^2 (1 - \tilde{e}_2)^2 = \tilde{e}_1(1 - \tilde{e}_2) = \epsilon.$$
- **幂零性**：注意到 $\epsilon = \tilde{e}_1^2 - \tilde{e}_1 \tilde{e}_2 = \tilde{e}_1(\tilde{e}_1 - \tilde{e}_2) = \tilde{e}_1 \delta$。由交换性，
  $$\epsilon^m = \tilde{e}_1^m \delta^m = \tilde{e}_1 \cdot 0 = 0.$$
非零幂等元绝不幂零（若 $\epsilon^2 = \epsilon$ 且 $\epsilon^m = 0$，则 $\epsilon = \epsilon^2 = \cdots = \epsilon^m = 0$），因此 $\epsilon = 0$。
故 $\tilde{e}_1(1 - \tilde{e}_2) = 0$，即 $\tilde{e}_1 = \tilde{e}_1 \tilde{e}_2$。同理对称可得 $\tilde{e}_2(1 - \tilde{e}_1) = 0 \implies \tilde{e}_2 = \tilde{e}_2 \tilde{e}_1 = \tilde{e}_1 \tilde{e}_2$。
因此 $\tilde{e}_1 = \tilde{e}_2$，幂等提升若存在必唯一。

### 2. 构造与性质验证
由 $q$ 满射，任取原像 $x \in R$ 使得 $q(x) = e$。
由于 $q(x^2 - x) = e^2 - e = 0$，故 $x^2 - x \in \ker q$。由条件存在正整数 $n$ 使得
$$(x^2 - x)^n = 0.$$

在多项式环 $\mathbb{Z}[X]$ 中，由二项式展开：
$$1 = (X + (1 - X))^{2n - 1} = \sum_{k=0}^{2n-1} \binom{2n-1}{k} X^k (1 - X)^{2n-1-k}.$$
定义多项式
$$E_n(X) := \sum_{k=n}^{2n-1} \binom{2n-1}{k} X^k (1 - X)^{2n-1-k} \in \mathbb{Z}[X].$$
此多项式系数皆为整数，不依赖 $2$ 可逆。定义 $\tilde{e} := E_n(x) \in R$。验证其性质：
1. **提升性**（$q(\tilde{e}) = e$）：
   在 $\mathbb{Z}[X]$ 中：
   - 模 $X$ 时，对所有 $k \ge n \ge 1$ 均有 $X \mid X^k$，故 $E_n(X) \equiv 0 \equiv X \pmod X$；
   - 模 $1 - X$ 时，余项 $1 - E_n(X) = \sum_{k=0}^{n-1} \binom{2n-1}{k} X^k (1 - X)^{2n-1-k}$ 中各项因数 $(1 - X)^{2n-1-k}$ 指数至少为 $n \ge 1$，故 $1 - E_n(X) \equiv 0 \pmod{1 - X}$，即 $E_n(X) \equiv 1 \equiv X \pmod{1 - X}$。
   因主理想 $(X)$ 与 $(1 - X)$ 在 $\mathbb{Z}[X]$ 中互素（$X + (1 - X) = 1$），故
   $$E_n(X) - X \in (X) \cap (1 - X) = (X(1 - X)) = (X^2 - X).$$
   由此 $E_n(x) - x \in (x^2 - x)R \subseteq \ker q$，从而 $q(\tilde{e}) = q(E_n(x)) = q(x) = e$。
2. **幂等性**（$\tilde{e}^2 = \tilde{e}$）：
   由定义，$E_n(X)$ 含因子 $X^n$；而 $1 - E_n(X) = \sum_{j=n}^{2n-1} \binom{2n-1}{j} (1 - X)^j X^{2n-1-j}$ 含因子 $(1 - X)^n$。
   因此，在 $\mathbb{Z}[X]$ 中：
   $$E_n(X)(1 - E_n(X)) \in (X^n (1 - X)^n) = ((X^2 - X)^n).$$
   将 $x$ 代入该多项式恒等式，因 $(x^2 - x)^n = 0$，立得
   $$\tilde{e}(1 - \tilde{e}) = E_n(x)(1 - E_n(x)) = 0 \implies \tilde{e}^2 = \tilde{e}.$$
由唯一性，所得 $\tilde{e}$ 与选取的原像 $x$ 及充分大的指数 $n$ 无关。

---

## S2　任意有向逆系

### 1. 构造与指标无关的 $p: L \to S$
设 $x = (x_i)_{i \in I} \in L \subseteq \prod_{i \in I} R_i$ 为相容元组（即 $i \le j \implies \rho_{ij}(x_j) = x_i$）。
任取指标 $i \in I$，定义 $p(x) := p_i(x_i) \in S$。
- **与指标无关性**：设 $i, j \in I$。由于偏序集 $I$ 有向，存在 $k \in I$ 满足 $i \le k$ 且 $j \le k$。由 $x \in L$，有 $x_i = \rho_{ik}(x_k)$，$x_j = \rho_{jk}(x_k)$。由过渡相容性 $p_i \rho_{ik} = p_k$ 与 $p_j \rho_{jk} = p_k$，得
  $$p_i(x_i) = p_i(\rho_{ik}(x_k)) = p_k(x_k) = p_j(\rho_{jk}(x_k)) = p_j(x_j).$$
  因此 $p(x)$ 与指标选取无关。
- **环同态**：因对任意固定的 $i \in I$，$p = p_i \circ \pi_i$（$\pi_i: L \to R_i$ 为典范投影），两同态复合必为含幺环同态。

### 2. 双射 $p_*: D_J(L) \to D_J(S)$ 的证明
- **若 $J = \emptyset$**：
  $\sum_{j \in \emptyset} e_j = 0$。根据定义，$D_\emptyset(R) \neq \emptyset \iff 0 = 1_R$（即 $R$ 为零环）。
  - 若 $S = 0$，则 $1_S = 0$。在任一层中 $p_i(1_{R_i}) = 0 \implies 1_{R_i} \in \ker p_i$。因 $\ker p_i$ 逐元素幂零，$1_{R_i}^m = 0 \implies 1_{R_i} = 0$，各 $R_i = 0$，故 $L = 0$。此时 $D_\emptyset(L)$ 与 $D_\emptyset(S)$ 均只含唯一的空元组，映射为显然双射。
  - 若 $S \neq 0$，则 $1_S \neq 0$，$D_\emptyset(S) = \emptyset$。又 $p(1_L) = 1_S \neq 0$，故 $L \neq 0$，$D_\emptyset(L) = \emptyset$，亦为双射。
- **若有限集 $J \neq \emptyset$**：
  - **单射性**：设 $\tilde{e} = (\tilde{e}_j)_{j \in J}, \tilde{e}' = (\tilde{e}'_j)_{j \in J} \in D_J(L)$ 满足 $p_*(\tilde{e}) = p_*(\tilde{e}')$。
    对任意 $j \in J$ 及任意 $i \in I$，元组分量 $\tilde{e}_{j, i}, \tilde{e}'_{j, i} \in R_i$ 均为幂等元，且 $p_i(\tilde{e}_{j, i}) = p(\tilde{e}_j) = p(\tilde{e}'_j) = p_i(\tilde{e}'_{j, i})$。
    因各 $\ker p_i$ 逐元素幂零且 $R_i$ 交换，援引 **S1 的唯一性**（条件完全适用），在各层必有 $\tilde{e}_{j, i} = \tilde{e}'_{j, i}$。因指标 $i$ 任意，$\tilde{e}_j = \tilde{e}'_j$，单射性得证。
  - **满射性**：任给 $(e_j)_{j \in J} \in D_J(S)$。
    对每个 $j \in J$ 及每个 $i \in I$，由 $p_i: R_i \to S$ 满且 $\ker p_i$ 逐元素幂零，援引 **S1 的构造与唯一性**，存在唯一的幂等元 $\tilde{e}_{j, i} \in R_i$ 提升 $e_j$。
    对任意 $i \le k$，过渡态 $\rho_{ik}: R_k \to R_i$ 为环同态，故 $\rho_{ik}(\tilde{e}_{j, k})$ 仍为 $R_i$ 中幂等元，且
    $$p_i(\rho_{ik}(\tilde{e}_{j, k})) = p_k(\tilde{e}_{j, k}) = e_j.$$
    根据 **S1 在 $R_i$ 中的唯一性**，必有 $\rho_{ik}(\tilde{e}_{j, k}) = \tilde{e}_{j, i}$。
    这证明元组 $\tilde{e}_j := (\tilde{e}_{j, i})_{i \in I}$ 满足相容性条件，即 $\tilde{e}_j \in L$。
    各分量幂等使 $\tilde{e}_j^2 = \tilde{e}_j$ 且 $p(\tilde{e}_j) = e_j$。再验算正交与单位和：
    1. 当 $j \neq k$ 时，在每一层 $R_i$ 中，$p_i(\tilde{e}_{j, i} \tilde{e}_{k, i}) = e_j e_k = 0$。由于 $\tilde{e}_{j, i} \tilde{e}_{k, i}$ 是交换环中的幂等元且属于 $\ker p_i$，由 S1 提升 $0 \in S$ 的唯一幂等元为 $0$，故在各层均有 $\tilde{e}_{j, i} \tilde{e}_{k, i} = 0$，从而在 $L$ 中 $\tilde{e}_j \tilde{e}_k = 0$。
    2. 令 $E_i := \sum_{j \in J} \tilde{e}_{j, i}$。因两两正交，直接展开得 $E_i^2 = E_i$，且 $p_i(E_i) = \sum e_j = 1_S$。由 S1 提升 $1_S$ 的唯一幂等元为 $1_{R_i}$，故 $E_i = 1_{R_i}$，从而在 $L$ 中 $\sum_{j \in J} \tilde{e}_j = 1_L$。
    故 $(\tilde{e}_j)_{j \in J} \in D_J(L)$，满射性得证。

### 3. 分解同构 $L \cong \prod_{j \in J} L / (1 - \tilde{e}_j)L$ 的构造
给定 $\tilde{e} = (\tilde{e}_j)_{j \in J} \in D_J(L)$。
定义典范环同态
$$\Phi: L \longrightarrow \prod_{j \in J} L / (1 - \tilde{e}_j)L, \quad x \longmapsto \left( x + (1 - \tilde{e}_j)L \right)_{j \in J}.$$
定义映射
$$\Psi: \prod_{j \in J} L / (1 - \tilde{e}_j)L \longrightarrow L, \quad \left( x_j + (1 - \tilde{e}_j)L \right)_{j \in J} \longmapsto \sum_{j \in J} \tilde{e}_j x_j.$$
- **良定性**：若 $x_j - x'_j = (1 - \tilde{e}_j)y_j$，则 $\tilde{e}_j(x_j - x'_j) = \tilde{e}_j(1 - \tilde{e}_j)y_j = 0$，故 $\tilde{e}_j x_j = \tilde{e}_j x'_j$。
- **互逆性**：
  - 对任意 $x \in L$，$\Psi(\Phi(x)) = \sum_{j \in J} \tilde{e}_j x = x \sum_{j \in J} \tilde{e}_j = x \cdot 1_L = x$。
  - 对任意元组 $(x_j + (1 - \tilde{e}_j)L)_{j \in J}$，其经 $\Psi$ 映射为 $y = \sum_{k \in J} \tilde{e}_k x_k$。考查其模 $(1 - \tilde{e}_j)L$ 的投影：
    因 $\tilde{e}_j = 1 - (1 - \tilde{e}_j) \equiv 1 \pmod{(1 - \tilde{e}_j)L}$；且当 $k \neq j$ 时，$\tilde{e}_k = \tilde{e}_k (1 - \tilde{e}_j + \tilde{e}_j) = (1 - \tilde{e}_j)\tilde{e}_k + 0 \in (1 - \tilde{e}_j)L$，即 $\tilde{e}_k \equiv 0 \pmod{(1 - \tilde{e}_j)L}$。
    因此 $y \equiv \tilde{e}_j x_j \equiv x_j \pmod{(1 - \tilde{e}_j)L}$。
故 $\Phi$ 与 $\Psi$ 互逆，$\Phi$ 为环同构。

### 4. 分解双射的自然性
设另有一套系统 $(R'_i, \rho'_{ij}, p'_i, S')$，相容族 $u_i: R_i \to R'_i$ 及 $u: S \to S'$ 满足 $u_i \rho_{ij} = \rho'_{ij} u_j$ 及 $p'_i u_i = u p_i$。
族 $(u_i)$ 诱导极限间典范环同态 $v: L \to L'$，定义为 $v((x_i)) = (u_i(x_i))$，其显然满足 $p' \circ v = u \circ p$。
- **提升双射自然性**：由 $p' \circ v = u \circ p$，知诱导映射满足 $p'_* \circ v_* = u_* \circ p_*$。因 $p_*, p'_*$ 皆为双射，两端取逆即得
  $$v_* \circ (p_*)^{-1} = (p'_*)^{-1} \circ u_*,$$
  即对 $S$ 中正交单位分解的提升与系统态射互易。
- **环分解自然性**：设 $\tilde{e}' = v_*(\tilde{e})$。同态 $v$ 将理想 $(1 - \tilde{e}_j)L$ 送入 $(1 - \tilde{e}'_j)L'$，诱导各商环同态 $v_j: L/(1 - \tilde{e}_j)L \to L'/(1 - \tilde{e}'_j)L'$。对任意 $x \in L$，
  $$\prod_j v_j(\Phi(x)) = \left( v(x) + (1 - \tilde{e}'_j)L' \right)_{j \in J} = \Phi'(v(x)),$$
  图表典范交换，分解完全自然。

---

## S3　极限核

### 1. 结论与判断
**结论：否**。$\ker(p: L \to k)$ 中的元素**不**是逐个幂零的。

### 2. 论证
逆系 $R_n = k[t]/(t^{n+1})$ 伴随典范截断过渡，其实际相容元组子环即形式幂级数环：
$$L = \varprojlim_{n \ge 1} k[t]/(t^{n+1}) \cong k[[t]].$$
增广映射 $p: k[[t]] \to k$ 取常数项，其核为理想
$$\ker p = (t) = t k[[t]].$$
取元素 $x = t \in \ker p$：
对任意正整数 $m \ge 1$，在 $R_m = k[t]/(t^{m+1})$ 中，$t^m \not\equiv 0 \pmod{t^{m+1}}$，故其在极限中的像 $t^m \neq 0$。
事实上，形式幂级数环 $k[[t]]$ 为整环，除 $0$ 之外不存在任何幂零元。因此非零元 $t \in \ker p$ 绝不幂零。

### 3. 与 S2 结论的一致性说明
这与 S2 的结论**完全一致，并无矛盾**。
1. **S2 条件适用范围**：S2 的证明仅依赖于**每个有限层**的 $\ker p_i$ 逐元素幂零，以确保每一层上存在且仅存在唯一的幂等提升，从而通过逆系的转移映射自然拼接成 $L$ 中的相容幂等元组。S2 绝未要求、亦未得出“极限核 $\ker p$ 逐元素幂零”的结论。
2. **在当前实例中的对应**：在 $S = k$ 中，由于 $k$ 为域，其仅有的幂等元为 $0$ 和 $1$；而在整环 $L = k[[t]]$ 中，仅有的幂等元同样只有 $0$ 和 $1$。故对于任意有限集 $J$，$D_J(k[[t]]) \cong D_J(k)$ 严格成立。逆极限运算一般并不保持“理想逐元素幂零”这一性质，但这丝毫不影响由有限层唯一性强迫得到的相容幂等元的唯一提升。

---

## S4　相容元素的满射性

### 证明
任取 $s \in S$。我们构造一个元素 $x = (x_n)_{n \ge 1} \in L$ 满足 $p(x) = s$。
这等价于通过数学归纳法选取一列元素 $x_n \in R_n$（$n \ge 1$），满足：
$$\forall n \ge 1, \quad p_n(x_n) = s \quad \text{且} \quad \rho_n(x_{n+1}) = x_n.$$

1. **基础步**（$n = 1$）：
   因 $p_1: R_1 \to S$ 满射，必存在 $x_1 \in R_1$ 满足 $p_1(x_1) = s$。
2. **归纳步**：
   假设已选定 $x_1, \dots, x_n$ 满足对所有 $1 \le k \le n$ 均有 $p_k(x_k) = s$，且对 $1 \le k < n$ 满足 $\rho_k(x_{k+1}) = x_k$。
   现考查 $x_{n+1}$ 的选取：
   - 题设过渡映射 $\rho_n: R_{n+1} \to R_n$ 为**满射**，因此原像集合 $\rho_n^{-1}(x_n) \subseteq R_{n+1}$ **非空**。
   - 任取 $x_{n+1} \in \rho_n^{-1}(x_n)$，即满足 $\rho_n(x_{n+1}) = x_n$。
   - 此时验证其增广值：利用给定的相容关系 $p_{n+1} = p_n \circ \rho_n$，立得
     $$p_{n+1}(x_{n+1}) = p_n(\rho_n(x_{n+1})) = p_n(x_n) = s.$$
     即条件 $p_{n+1}(x_{n+1}) = s$ 被自动满足。

由依赖选择公理（DC），存在序列 $(x_n)_{n=1}^\infty$ 满足对所有 $n \ge 1$ 均有 $\rho_n(x_{n+1}) = x_n$，故 $x = (x_n) \in L$。
其在 $p$ 下的像为 $p(x) = p_1(x_1) = s$。因此 $p: L \to S$ 必满射。证毕。

---

## S5　逐层增广

### 1. 结论与判断
**结论：否**。在共同逆系设定下，即使限制 $I = \mathbb{N}_{\ge 1}$，增广同态 $p: L \to S$ **不必**满射。

### 2. 完整核验反例
设 $k$ 为任意域。取目标交换环 $S := k[x]$。
对每个 $n \ge 1$，令向量空间 $V_n := k[t]$（以 $t$ 为不定式的多项式环）。
定义各层交换环 $R_n$ 为 $S$ 在 $V_n$ 上的平凡扩张（理想化环 $k[x] \ltimes k[t]$）：
- **底层集合**：$R_n = k[x] \times k[t]$，元素记为 $(a(x), P(t))$。
- **加法**：按分量相加。
- **乘法**：$(a_1(x), P_1(t)) \cdot (a_2(x), P_2(t)) = \left( a_1(x)a_2(x), \; a_1(0)P_2(t) + a_2(0)P_1(t) \right)$。
- **单位元**：$(1, 0)$。此乘法满足结合律与交换律，为含幺交换环。

检验设定条件：
1. **增广满射 $p_n$ 与幂零核**：
   定义 $p_n: R_n \to S$ 为 $p_n(a(x), P(t)) = a(x)$。
   $p_n$ 显然是含幺环满射。其核为 $\ker p_n = 0 \times k[t]$。
   对任意 $(0, P(t)) \in \ker p_n$，
   $$(0, P(t))^2 = (0, 0 \cdot P(t) + 0 \cdot P(t)) = (0, 0).$$
   故 $(\ker p_n)^2 = 0$，核中元素平方皆为零，逐元素幂零条件严格成立。
2. **过渡映射 $\rho_n: R_{n+1} \to R_n$**：
   对 $(a(x), P(t)) \in R_{n+1}$，定义
   $$\rho_n(a(x), P(t)) := \left( a(x), \; a'(0) \cdot 1 + t P(t) \right) \in R_n,$$
   其中 $a'(0)$ 为多项式导数在 $0$ 处的值，$1 \in k[t]$ 为常数多项式 $1$，$t P(t)$ 为多项式乘法。
   - **保单位元**：$\rho_n(1, 0) = (1, 0 \cdot 1 + 0) = (1, 0)$。
   - **保加法**：由求导与多项式乘法的线性性显然。
   - **保乘法**：
     一方面，
     $$\rho_n((a_1, P_1)(a_2, P_2)) = \left( a_1 a_2, \; (a_1 a_2)'(0) \cdot 1 + t(a_1(0)P_2 + a_2(0)P_1) \right).$$
     根据导数乘积法则 $(a_1 a_2)'(0) = a_1'(0)a_2(0) + a_1(0)a_2'(0)$，第二分量为
     $$\left( a_1'(0)a_2(0) + a_1(0)a_2'(0) \right) + t a_1(0)P_2 + t a_2(0)P_1.$$
     另一方面，
     $$\rho_n(a_1, P_1)\rho_n(a_2, P_2) = (a_1, a_1'(0) \cdot 1 + t P_1)(a_2, a_2'(0) \cdot 1 + t P_2),$$
     依 $R_n$ 的乘法定义，其第二分量为
     $$a_1(0)\left( a_2'(0) \cdot 1 + t P_2 \right) + a_2(0)\left( a_1'(0) \cdot 1 + t P_1 \right),$$
     两式完全相等，故 $\rho_n$ 为严格的环同态。
   - **相容性**：$p_n(\rho_n(a, P)) = a = p_{n+1}(a, P)$，完全满足 $p_n \rho_n = p_{n+1}$。

3. **$p: L \to S$ 不满射的证明**：
   考查目标元素 $x \in S = k[x]$。
   假设存在 $y = ((a_n(x), P_n(t)))_{n \ge 1} \in L$ 满足 $p(y) = x$。
   - 由相容性 $p_n(y_n) = p(y)$，必有 $a_n(x) = x$（对所有 $n \ge 1$ 恒成立）。
   - 对多项式 $a_n(x) = x$，其导数 $a'_n(0) = 1$。
   - 转移相容条件 $\rho_n(a_{n+1}, P_{n+1}) = (a_n, P_n)$ 要求第二分量满足：
     $$1 + t P_{n+1}(t) = P_n(t) \quad (\forall n \ge 1).$$
   由此递推关系，对任意 $N \ge 1$ 展开可得：
   $$P_1(t) = 1 + t P_2(t) = 1 + t + t^2 P_3(t) = \cdots = \sum_{j=0}^{N-1} t^j + t^N P_{N+1}(t).$$
   这表明多项式 $P_1(t) \in k[t]$ 模任意 $t^N$ 的截断均为 $\sum_{j=0}^{N-1} t^j$。
   即 $P_1(t)$ 的所有项 $t^j$（$j = 0, 1, 2, \dots$）系数全为 $1$。
   但 $k[t]$ 中多项式只有有限项非零，这产生矛盾。
   因此 $x$ 在 $L$ 中不存在原像，$p: L \to S$ 不满射。

---

## S6　乘法结构与唯一性

### 1. 非交换单层提升的唯一性判断与反例
**结论：否**。当不要求环交换时，即使 $\ker q$ 平方为零，单个幂等元的提升也**不必**唯一。

**反例核验**：
设 $k$ 为任意域。取 $R$ 为 $k$ 上的 $2 \times 2$ 上三角矩阵环：
$$R = \left\{ \begin{pmatrix} a & b \\ 0 & c \end{pmatrix} : a, b, c \in k \right\}.$$
取理想 $I = \left\{ \begin{pmatrix} 0 & b \\ 0 & 0 \end{pmatrix} : b \in k \right\}$。
直接计算可知
$$\begin{pmatrix} 0 & b \\ 0 & 0 \end{pmatrix} \begin{pmatrix} 0 & b' \\ 0 & 0 \end{pmatrix} = \begin{pmatrix} 0 & 0 \\ 0 & 0 \end{pmatrix},$$
故 $I^2 = 0$。商环 $S = R / I \cong k \times k$，商同态 $q: R \to S$ 给出为 $q\begin{pmatrix} a & b \\ 0 & c \end{pmatrix} = (a, c)$。

在 $S$ 中取幂等元 $e = (1, 0)$。
在 $R$ 中考查 $e$ 的任意原像：形如 $X_b = \begin{pmatrix} 1 & b \\ 0 & 0 \end{pmatrix}$（$b \in k$）。
直接验算其平方：
$$X_b^2 = \begin{pmatrix} 1 & b \\ 0 & 0 \end{pmatrix} \begin{pmatrix} 1 & b \\ 0 & 0 \end{pmatrix} = \begin{pmatrix} 1 & b \\ 0 & 0 \end{pmatrix} = X_b.$$
因此对每一个 $b \in k$，$X_b$ 均为 $R$ 中的幂等元，且均提升 $e$。
若域 $k$ 至少含两个元素（例如 $k = \mathbb{F}_2$ 或 $\mathbb{Q}$），取 $b = 0$ 与 $b = 1$，则 $X_0 \neq X_1$ 为两个不同的幂等提升。故提升不唯一。

### 2. S1–S5 核心性质逻辑蕴含梳理

下表整理四类概念：
- (A) **元素提升**（单层 $q$ 满射 / 极限增广 $p: L \to S$ 满射）
- (B) **幂等提升存在性**
- (C) **幂等提升唯一性**
- (D) **核逐元素幂零**（各层 $\ker p_i$ 逐元素幂零 / 极限核 $\ker p$ 逐元素幂零）

| 逻辑命题 | 成立与否 | 证据与归属阶段 | 说明 |
| :--- | :---: | :--- | :--- |
| 单层中：(交换 + 核逐元素幂零) $\implies$ 幂等提升唯一 | **已证明** | **S1** | 利用交换性与二项式多项式 $E_n(X)$，在无 $2$ 可逆条件下完成构造与唯一性证明。 |
| 单层中：(非交换 + 核平方为零) $\implies$ 幂等提升唯一 | **不成立** | **S6** (反例) | 上三角矩阵环反例表明，失去交换性后，即使核平方为零，幂等提升亦不唯一。 |
| 各层幂等提升唯一 $\implies$ 极限幂等提升存在且唯一 | **已证明** | **S2** | 相容条件 $\rho_{ij}(\tilde{e}_j) = \tilde{e}_i$ 由各层的**唯一性**自动强迫成立，从而在逆极限中直接拼接出唯一的幂等元组。 |
| 极限幂等提升存在且唯一 $\implies$ 极限元素提升（满射） | **不成立** | **S5** (反例) | S5 满足 S2 的所有条件，因而具有极限幂等提升的唯一性，但一般的多项式元素 $x \in S$ 无法提升到 $L$（逆极限第一导出函子 $\varprojlim^1 \neq 0$ 产生阻碍）。 |
| 各层过渡满射 + 各层元素提升 $\implies$ 极限元素提升 | **已证明** | **S4** | 仅依赖依序选取的相容纤维非空性，不依赖幂零核或交换性即可保证 $p: L \to S$ 满射。 |
| 各层核逐元素幂零 $\implies$ 极限核逐元素幂零 | **不成立** | **S3** (反例) | 各层核 $(t)/(t^{n+1})$ 均为幂零理想，但逆极限核 $tk[[t]]$ 中除 $0$ 外无任何幂零元。 |
| 极限核逐元素幂零 $\implies$ 极限幂等提升唯一 | **不必要** | **S3** 与 **S2** 对比 | S3 中极限核不仅不逐元素幂零，甚至无非零幂零元；但依据 S2，极限上的幂等提升仍然严格唯一。这表明极限核是否幂零并非极限幂等元唯一提升的前提。 |
