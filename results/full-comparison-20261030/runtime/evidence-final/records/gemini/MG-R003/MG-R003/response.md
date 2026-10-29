本题旨在建立关于交换幂有界双算子系统的**双重平均（2D Cesàro 平均）与单算子平均化迭代（Krasnosel'skii-Mann 型迭代）之间的动力学等价性与商记录恢复理论**。

以下给出该理论的主定理、记录恢复映射的严格构造及其完整论证。

---

# 一、符号体系与结构空间

设 $E$ 为实 Banach 空间，$T, S \in \mathcal{B}(E)$ 满足 $TS = ST$，且存在常数 $K_T, K_S \ge 1$ 使得：
$$K_T = \sup_{n \ge 0} \|T^n\| < \infty, \qquad K_S = \sup_{m \ge 0} \|S^m\| < \infty.$$
定义两类关键的闭子空间：
1. **公共不动点空间（不变目标状态空间）**：
   $$F = \ker(I-T) \cap \ker(I-S) = \operatorname{Fix}(T) \cap \operatorname{Fix}(S).$$
   由于 $T, S$ 有界，$F$ 为 $E$ 的闭线性子空间。
2. **耗散扰动闭包空间（信息损失/涨落子空间）**：
   $$Y = \overline{(I-T)E + (I-S)E}.$$
   由定义，$Y$ 为 $E$ 的闭线性子空间。
3. **记录商空间与记录映射**：
   $$Q = E/Y, \qquad q: E \to Q, \quad q(x) = x + Y.$$
   $Q$ 赋予标准商范数 $\|q(x)\|_Q = \inf_{y \in Y} \|x - y\|_E$，成为实 Banach 空间；$q$ 为典范有界线性商投影，且 $\|q\| \le 1$。
4. **双重平均算子与单算子**：
   $$A_{N,M} = \frac{1}{NM}\sum_{i=0}^{N-1}\sum_{j=0}^{M-1} T^i S^j \quad (N, M \ge 1),$$
   $$T_1 = \frac{I+T}{2}, \quad S_1 = \frac{I+S}{2}, \quad R = T_1 S_1 = \frac{1}{4}(I+T)(I+S).$$

---

# 二、主定理 (Main Theorem)

> ### 主定理（双重平均与迭代恢复等价性定理）
> 设 $E$ 为实 Banach 空间，$T, S \in \mathcal{B}(E)$ 交换且幂有界，界分别为 $K_T, K_S$。记 $\mathcal{D} = F \oplus Y$。则：
> 
> 1. **单算子 $R$ 的拓扑谱结构分解**：
>    $$\ker(I-R) = F, \qquad \overline{(I-R)E} = Y, \qquad F \cap Y = \{0\}.$$
> 
> 2. **动力学收敛等价性与极限同构**：
>    对任意 $x \in E$，以下三款命题严格等价：
>    - (i) 双重平均范数收敛：$\lim_{\min(N,M) \to \infty} A_{N,M} x$ 在 $E$ 中按范数收敛；
>    - (ii) 单算子迭代范数收敛：$\lim_{n \to \infty} R^n x$ 在 $E$ 中按范数收敛；
>    - (iii) 状态分解性：$x \in \mathcal{D} = F \oplus Y$。
>    
>    当且仅当上述条件之一成立时，双重平均与单算子迭代收敛到**完全相同的极限状态**：
>    $$\lim_{\min(N,M) \to \infty} A_{N,M} x = \lim_{n \to \infty} R^n x = P_F x \in F,$$
>    其中 $P_F: \mathcal{D} \to F$ 是沿 $Y$ 到 $F$ 的连续线性遍历投影算子，满足 $\|P_F\| \le K_T K_S$。
> 
> 3. **记录恢复映射 (Record Recovery Mapping) 的完整确定**：
>    商映射在 $F$ 上的限制 $q|_F: F \to Q$ 为拓扑同构映射（同胚于其值域）。从记录到初始不变状态的**恢复映射** $\mathcal{R}$ 唯一定义为：
>    $$\mathcal{R} = (q|_F)^{-1}: \operatorname{dom}(\mathcal{R}) \to \operatorname{ran}(\mathcal{R}).$$
>    该映射完全由 $T, S, q$ 确定，其几何与分析性质如下：
>    - **定义域**：
>      $$\operatorname{dom}(\mathcal{R}) = q(\mathcal{D}) = q(F) = (F \oplus Y)/Y \subset Q,$$
>      且 $\operatorname{dom}(\mathcal{R})$ 是 Banach 空间 $Q$ 的**闭子空间**。
>    - **值域**：
>      $$\operatorname{ran}(\mathcal{R}) = F = \ker(I-T) \cap \ker(I-S) = \operatorname{Fix}(T) \cap \operatorname{Fix}(S) \subset E.$$
>    - **动力学可恢复性**：对任意 $x \in \mathcal{D}$，由其商记录 $q(x)$ 可通过单步递推迭代或双重平均完全恢复其不变基底状态：
>      $$\mathcal{R}(q(x)) = \lim_{n \to \infty} R^n x = \lim_{\min(N,M)\to\infty} A_{N,M} x.$$
>    - **Hadamard 适定性与双向稳定性**：
>      $\mathcal{R}$ 为有界线性同构，满足精确的双向范数控制：
>      $$\frac{1}{K_T K_S} \|\mathcal{R}(\xi)\|_E \le \|\xi\|_Q \le \|\mathcal{R}(\xi)\|_E \qquad (\forall \xi \in \operatorname{dom}(\mathcal{R})),$$
>      从而算子范数满足 $\|\mathcal{R}\| \le K_T K_S$。对任意记录扰动 $\delta\xi \in \operatorname{dom}(\mathcal{R})$，恢复误差满足：
>      $$\|\delta x^*\|_E \le K_T K_S \|\delta\xi\|_Q.$$

---

# 三、关键引理与算子范数估计

为给出严谨论证，首先证明关于 $R$ 与 $A_{N,M}$ 的代数与分析性质引理。

### 引理 1（算子的一致幂有界性）
> 算子 $T_1 = \frac{I+T}{2}$，$S_1 = \frac{I+S}{2}$，$R = T_1 S_1$ 及 $A_{N,M}$ 均在 $E$ 上一致幂有界：
> $$\|T_1^n\| \le K_T, \quad \|S_1^n\| \le K_S, \quad \|R^n\| \le K_T K_S \quad (\forall n \ge 0),$$
> $$\|A_{N,M}\| \le K_T K_S \quad (\forall N, M \ge 1).$$

**证明**：
利用二项式展开与 $T^k$ 的幂有界性：
$$\|T_1^n\| = \left\| \frac{1}{2^n}\sum_{k=0}^n \binom{n}{k} T^k \right\| \le \frac{1}{2^n}\sum_{k=0}^n \binom{n}{k} \|T^k\| \le K_T \left(\frac{1}{2^n}\sum_{k=0}^n \binom{n}{k}\right) = K_T.$$
同理 $\|S_1^n\| \le K_S$。因 $TS = ST$，算子 $T_1$ 与 $S_1$ 交换，故：
$$\|R^n\| = \|(T_1 S_1)^n\| = \|T_1^n S_1^n\| \le \|T_1^n\| \|S_1^n\| \le K_T K_S.$$
对双重平均 $A_{N,M}$，注意 $A_{N,M} = A_N(T) A_M(S)$，其中 $A_N(T) = \frac{1}{N}\sum_{i=0}^{N-1} T^i$。显见 $\|A_N(T)\| \le K_T$，$\|A_M(S)\| \le K_S$，故 $\|A_{N,M}\| \le K_T K_S$。 $\blacksquare$

---

### 引理 2（差分衰减与 $O(n^{-1/2})$ 显式算子范数估计）
> 对任意 $n \ge 1$，有显式算子范数估计：
> $$\|T_1^n (I-T)\| \le \frac{2 K_T}{\sqrt{n}}, \qquad \|S_1^n (I-S)\| \le \frac{2 K_S}{\sqrt{n}}.$$
> 进而，单算子迭代在差分子空间上满足：
> $$\|R^n (I-T)\| \le \frac{2 K_T K_S}{\sqrt{n}}, \qquad \|R^n (I-S)\| \le \frac{2 K_T K_S}{\sqrt{n}}.$$
> 特别地，对任意 $y \in Y = \overline{(I-T)E + (I-S)E}$，有：
> $$\lim_{n \to \infty} \|R^n y\|_E = 0, \qquad \lim_{\min(N,M) \to \infty} \|A_{N,M} y\|_E = 0.$$

**证明**：
考查多项式展开：
$$(I+T)^n (I-T) = \sum_{k=0}^n \binom{n}{k} T^k - \sum_{k=0}^n \binom{n}{k} T^{k+1} = I + \sum_{k=1}^n \left[\binom{n}{k} - \binom{n}{k-1}\right] T^k - T^{n+1}.$$
令 $c_0 = 1$，$c_{n+1} = -1$，对 $1 \le k \le n$，令 $c_k = \binom{n}{k} - \binom{n}{k-1}$。
注意当 $k \le \frac{n+1}{2}$ 时，$c_k \ge 0$；当 $k > \frac{n+1}{2}$ 时，$c_k \le 0$。
记 $m = \lfloor \frac{n+1}{2} \rfloor$。由裂项相消求和：
$$\sum_{k=1}^m |c_k| = \sum_{k=1}^m \left[\binom{n}{k} - \binom{n}{k-1}\right] = \binom{n}{m} - 1,$$
$$\sum_{k=m+1}^n |c_k| = \sum_{k=m+1}^n \left[\binom{n}{k-1} - \binom{n}{k}\right] = \binom{n}{m} - 1.$$
加上两端端点系数绝对值 $|c_0| = 1, |c_{n+1}| = 1$，得到系数绝对值总和为：
$$\sum_{k=0}^{n+1} |c_k| = 1 + \left(\binom{n}{m}-1\right) + \left(\binom{n}{m}-1\right) + 1 = 2 \binom{n}{\lfloor (n+1)/2 \rfloor}.$$
利用中心二项式系数的标准 Wallis / Stirling 界：$\frac{\binom{n}{\lfloor (n+1)/2 \rfloor}}{2^n} \le \sqrt{\frac{2}{\pi n}} \le \frac{1}{\sqrt{n}}$，可得：
$$\|T_1^n (I-T)\| = \left\| \frac{1}{2^n} \sum_{k=0}^{n+1} c_k T^k \right\| \le \frac{K_T}{2^n} \sum_{k=0}^{n+1} |c_k| = \frac{2 K_T \binom{n}{\lfloor (n+1)/2 \rfloor}}{2^n} \le \frac{2 K_T}{\sqrt{n}}.$$
同理可得 $\|S_1^n (I-S)\| \le \frac{2 K_S}{\sqrt{n}}$。
由 $R^n = T_1^n S_1^n = S_1^n T_1^n$，直接得到：
$$\|R^n (I-T)\| \le \|S_1^n\| \|T_1^n (I-T)\| \le \frac{2 K_T K_S}{\sqrt{n}},$$
$$\|R^n (I-S)\| \le \|T_1^n\| \|S_1^n (I-S)\| \le \frac{2 K_T K_S}{\sqrt{n}}.$$
对于任意稠密子空间元素 $y_0 = (I-T)u + (I-S)v \in (I-T)E + (I-S)E$，由上述估计：
$$\|R^n y_0\| \le \|R^n(I-T)u\| + \|R^n(I-S)v\| \le \frac{2 K_T K_S}{\sqrt{n}}(\|u\| + \|v\|) \to 0 \quad (n \to \infty).$$
结合 $\|R^n\| \le K_T K_S$ 的一致有界性，由标准 $3\epsilon$ 稠密性论证即知：对任意 $y \in Y = \overline{(I-T)E + (I-S)E}$，均有 $\lim_{n \to \infty} R^n y = 0$。

对双重平均 $A_{N,M}$，注意到裂项恒等式：
$$A_N(T)(I-T) = \frac{I-T^N}{N}, \qquad A_M(S)(I-S) = \frac{I-S^M}{M}.$$
对于 $y_0 = (I-T)u + (I-S)v$：
$$A_{N,M} y_0 = A_M(S) \frac{I-T^N}{N} u + A_N(T) \frac{I-S^M}{M} v.$$
因此：
$$\|A_{N,M} y_0\| \le K_S \frac{1+K_T}{N}\|u\| + K_T \frac{1+K_S}{M}\|v\| \le \frac{C}{\min(N,M)}(\|u\|+\|v\|) \to 0.$$
再由 $\|A_{N,M}\| \le K_T K_S$ 及稠密性，同理得到对所有 $y \in Y$，$\lim_{\min(N,M)\to\infty} A_{N,M} y = 0$。 $\blacksquare$

---

### 引理 3（算子 $R$ 的零空间、值域闭包与直和分解）
> 算子 $R$ 满足：
> 1. $\ker(I-R) = F = \ker(I-T) \cap \ker(I-S)$；
> 2. $\overline{(I-R)E} = Y = \overline{(I-T)E + (I-S)E}$；
> 3. $F \cap Y = \{0\}$，从而 $\mathcal{D} = F \oplus Y$ 是良定的代数与拓扑直和。

**证明**：
1. **零空间相等性**：
   - 若 $x \in F$，则 $Tx = x$ 且 $Sx = x$，从而 $T_1 x = x, S_1 x = x$，故 $Rx = T_1 S_1 x = x$，即 $F \subseteq \ker(I-R)$。
   - 反之，若 $x \in \ker(I-R)$，则 $Rx = x$。归纳可得对任意 $n \ge 1$ 均有 $R^n x = x$。
     因 $T$ 与 $S$ 交换，$T$ 与 $R$ 交换，故 $(I-T)x = (I-T)R^n x = R^n (I-T)x$。
     应用引理 2 的范数衰减估计：
     $$\|(I-T)x\| = \|R^n (I-T) x\| \le \|R^n(I-T)\| \|x\| \le \frac{2 K_T K_S}{\sqrt{n}} \|x\|.$$
     令 $n \to \infty$，右端趋于 0，因此 $(I-T)x = 0$，即 $Tx = x$。
     同理，$\|(I-S)x\| = \|R^n (I-S) x\| \le \frac{2 K_T K_S}{\sqrt{n}} \|x\| \to 0$，故 $Sx = x$。
     这证明了 $x \in \ker(I-T) \cap \ker(I-S) = F$。因此 $\ker(I-R) = F$。

2. **值域闭包相等性**：
   - 代数分解式：
     $$I - R = I - T_1 S_1 = (I-T_1) + T_1(I-S_1) = \frac{1}{2}(I-T) + \frac{1}{2} T_1 (I-S).$$
     对任意 $w \in E$，$(I-R)w = \frac{1}{2}(I-T)w + \frac{1}{2}(I-S)(T_1 w) \in (I-T)E + (I-S)E \subset Y$。
     因 $Y$ 是闭子空间，故必有 $\overline{(I-R)E} \subseteq Y$。
   - 反向包含：对任意 $y \in Y$，由引理 2 已知 $\lim_{n \to \infty} R^n y = 0$。
     注意到恒等式：
     $$y - R^n y = (I - R^n)y = (I-R)\left(\sum_{k=0}^{n-1} R^k y\right) \in (I-R)E.$$
     由于 $\lim_{n \to \infty} (y - R^n y) = y$，这表明 $y$ 是 $(I-R)E$ 中序列的强极限。
     由闭包定义，$y \in \overline{(I-R)E}$。故 $Y \subseteq \overline{(I-R)E}$。
     综上，$\overline{(I-R)E} = Y$。

3. **交集平庸性**：
   设 $x \in F \cap Y$。
   因 $x \in F = \ker(I-R)$，对所有 $n \ge 1$ 均有 $R^n x = x$。
   因 $x \in Y$，由引理 2 有 $\lim_{n \to \infty} R^n x = 0$。
   从而 $x = \lim_{n \to \infty} R^n x = 0$。
   因此 $F \cap Y = \{0\}$。
   这证明了子空间和 $F + Y$ 是无交叠直和 $F \oplus Y$。 $\blacksquare$

---

# 四、主定理的完整论证

### 1. 动力学收敛等价性与极限同构

**证明 (i) $\iff$ (iii)**：
- 若 $x \in \mathcal{D} = F \oplus Y$，唯一表示为 $x = u + y$（$u \in F, y \in Y$）。
  因为 $Tu = u, Su = u$，对任意 $i, j \ge 0$ 均有 $T^i S^j u = u$，从而 $A_{N,M} u = u$。
  由引理 2，$\lim_{\min(N,M)\to\infty} A_{N,M} y = 0$。
  因此：
  $$\lim_{\min(N,M) \to \infty} A_{N,M} x = \lim_{\min(N,M) \to \infty} (A_{N,M} u + A_{N,M} y) = u.$$
  极限按范数存在，且等于不变分量 $u$。
- 反之，假设 $\lim_{\min(N,M)\to\infty} A_{N,M} x = x^*$ 在 $E$ 中按范数存在。
  首先证明 $x^* \in F$：
  $$\|T x^* - x^*\| \le \|T x^* - T A_{N,M} x\| + \|(T-I)A_{N,M} x\| + \|A_{N,M} x - x^*\|.$$
  其中第一项 $\|T(x^* - A_{N,M} x)\| \le K_T \|x^* - A_{N,M} x\| \to 0$；
  第二项注意到：
  $$(T-I)A_{N,M} = (T-I)A_N(T) A_M(S) = \frac{T^N - I}{N} A_M(S),$$
  其范数受控于 $\frac{K_T+1}{N} K_S \to 0$（当 $N \to \infty$ 时一致成立）。
  因此 $\|T x^* - x^*\| = 0$，即 $T x^* = x^*$。同理 $S x^* = x^*$。故 $x^* \in F$。
  其次，考查偏差项 $x - A_{N,M} x$：
  $$x - A_{N,M} x = \frac{1}{NM}\sum_{i=0}^{N-1}\sum_{j=0}^{M-1} (I - T^i S^j)x.$$
  利用代数恒等式：
  $$I - T^i S^j = (I-T^i) + T^i(I-S^j) = (I-T)\sum_{k=0}^{i-1} T^k + (I-S)\left(T^i\sum_{l=0}^{j-1} S^l\right),$$
  每个被积项均位于 $(I-T)E + (I-S)E \subset Y$ 中。由线性组合的封闭性，$x - A_{N,M} x \in Y$。
  因为 $Y$ 是闭子空间，且 $x - A_{N,M} x \to x - x^*$，必有：
  $$x - x^* \in Y.$$
  于是 $x = x^* + (x - x^*) \in F \oplus Y$，且 $x^*$ 恰为其 $F$-分量。

**证明 (ii) $\iff$ (iii)**：
- 若 $x \in \mathcal{D} = F \oplus Y$，写为 $x = u + y$（$u \in F, y \in Y$）。
  因 $u \in F = \ker(I-R)$，对所有 $n$ 有 $R^n u = u$。
  由引理 2，$\lim_{n \to \infty} R^n y = 0$。
  因此：
  $$\lim_{n \to \infty} R^n x = \lim_{n \to \infty} (u + R^n y) = u.$$
- 反之，假设 $\lim_{n \to \infty} R^n x = \tilde{x}$ 在 $E$ 中按范数存在。
  由算子 $R$ 的有界连续性：
  $$R \tilde{x} = R \lim_{n \to \infty} R^n x = \lim_{n \to \infty} R^{n+1} x = \tilde{x}.$$
  因此 $\tilde{x} \in \ker(I-R)$。由引理 3 知 $\ker(I-R) = F$，故 $\tilde{x} \in F$。
  再看偏差序列：
  $$x - R^n x = (I - R)\left(\sum_{k=0}^{n-1} R^k x\right) \in (I-R)E \subset Y.$$
  因为 $Y$ 闭，且 $x - R^n x \to x - \tilde{x}$，故必有 $x - \tilde{x} \in Y$。
  于是 $x = \tilde{x} + (x - \tilde{x}) \in F \oplus Y$，且极限 $\tilde{x} = u$。

由上述双向推导，对任意 $x \in E$：
$$\text{(i) 成立} \iff \text{(ii) 成立} \iff \text{(iii) 成立},$$
且收敛时均给出投影状态 $x^* = \tilde{x} = u$。

---

### 2. 遍历投影算子 $P_F$ 的性质

定义投影映射 $P_F: \mathcal{D} \to F$ 为 $P_F(u + y) = u$（$u \in F, y \in Y$）。
对任意 $x \in \mathcal{D}$，由引理 1 中 $\|R^n\| \le K_T K_S$ 的一致有界性：
$$\|P_F x\| = \lim_{n \to \infty} \|R^n x\| \le \limsup_{n \to \infty} \|R^n\| \|x\| \le K_T K_S \|x\|.$$
因此 $P_F$ 是有界线性算子，算子范数满足：
$$\|P_F\|_{\mathcal{D} \to F} \le K_T K_S.$$
且显然满足 $P_F^2 = P_F$，$\ker(P_F) = Y$，$\operatorname{ran}(P_F) = F$。

---

### 3. 记录映射 $q|_F$ 的同构性与双向范数不等式

考查商映射限制到 $F$ 上的算子 $j = q|_F: F \to Q$。
- **单射性**：若 $u \in F$ 满足 $j(u) = 0$，则 $u \in \ker(q) = Y$，故 $u \in F \cap Y = \{0\}$，即 $u = 0$。
- **连续性（上界估计）**：由商范数定义：
  $$\|q(u)\|_Q = \inf_{y \in Y} \|u - y\|_E \le \|u - 0\|_E = \|u\|_E.$$
- **逆连续性（下界估计）**：对任意 $u \in F$ 及任意 $y \in Y$，注意到 $P_F(u - y) = P_F u - P_F y = u - 0 = u$。
  利用 $P_F$ 的有界性：
  $$\|u\|_E = \|P_F(u - y)\|_E \le \|P_F\| \|u - y\|_E \le K_T K_S \|u - y\|_E.$$
  两边对所有 $y \in Y$ 取下确界，立即得到：
  $$\|u\|_E \le K_T K_S \inf_{y \in Y} \|u - y\|_E = K_T K_S \|q(u)\|_Q.$$
  即：
  $$\|q(u)\|_Q \ge \frac{1}{K_T K_S} \|u\|_E \qquad (\forall u \in F).$$

综合两式，对所有 $u \in F$ 有严密的双向范数等价性：
$$\frac{1}{K_T K_S} \|u\|_E \le \|q(u)\|_Q \le \|u\|_E.$$

---

### 4. 恢复映射 $\mathcal{R}$ 的完整确定

基于上述双向估计，定义恢复映射 $\mathcal{R} = (q|_F)^{-1}$：

1. **定义域确定**：
   $$\operatorname{dom}(\mathcal{R}) = q(F) = q(F \oplus Y) = q(\mathcal{D}) \subset Q.$$
   因为 $F$ 是实 Banach 空间 $E$ 的闭子空间，故 $F$ 本身是完备度量空间；
   由于 $q|_F: F \to Q$ 是有界线性单射且满足下界条件 $\|q(u)\|_Q \ge \frac{1}{K_T K_S}\|u\|_E$，
   值域 $q(F)$ 在商空间 $Q$ 中是**完备的**，因此 $\operatorname{dom}(\mathcal{R}) = q(F)$ 必然是商空间 $Q$ 的**闭线性子空间**。
2. **值域确定**：
   $$\operatorname{ran}(\mathcal{R}) = F = \ker(I-T) \cap \ker(I-S) = \operatorname{Fix}(T) \cap \operatorname{Fix}(S).$$
3. **映射构造与动力学恢复**：
   对任意记录 $\xi \in \operatorname{dom}(\mathcal{R})$，存在唯一的 $u \in F$ 使得 $\xi = q(u)$。
   若 $x \in \mathcal{D}$ 是该记录的一个物理代表元（即 $q(x) = \xi$，也就是 $x = u+y$），则恢复状态直接由迭代极限给出：
   $$\mathcal{R}(\xi) = u = \lim_{n \to \infty} R^n x = \lim_{\min(N,M)\to\infty} A_{N,M} x.$$
4. **稳定性与适定性**：
   对任意 $\xi \in \operatorname{dom}(\mathcal{R})$，记 $u = \mathcal{R}(\xi) \in F$。由下界估计：
   $$\|\mathcal{R}(\xi)\|_E = \|u\|_E \le K_T K_S \|q(u)\|_Q = K_T K_S \|\xi\|_Q.$$
   因此恢复算子满足：
   $$\|\mathcal{R}\| \le K_T K_S.$$
   该问题满足严格的 Hadamard 适定性：解存在、唯一，且恢复映射是 Lipschitz 连续的（条件数受常数 $K_T K_S$ 控制）。 $\blacksquare$

---

# 五、理论深化与几何推论

### 1. 算法复杂度与动力学等价性的物理意义
- **双重平均 $A_{N,M}$**：属于双参数遍历过程，需要保留系统在网格 $0 \le i < N, 0 \le j < M$ 上的二维完整历史轨迹，计算复杂度为 $O(NM)$，存储与同步协调成本高。
- **单算子迭代 $R^n$**：属于单步自主动力系统 $x_{k+1} = R x_k = \frac{1}{4}(I+T)(I+S) x_k$，单步存储开销为 $O(1)$。
- **本理论确立的物理意义**：两者在拓扑、测度与范数结构上收敛域完全一致，且均能从记录商空间 $Q$ 中唯一、稳定地逆向恢复出系统的不变宏观态 $F$。单算子序列 $R^n$ 可直接作为双重遍历平均的**无偏、稳定替代算法**。

### 2. 自反 Banach 空间与 Hilbert 空间特例
> **推论 1（自反空间的全空间无条件恢复）**：
> 若 $E$ 为自反 Banach 空间（例如 $L^p(\Omega)$，其中 $1 < p < \infty$）：
> 由双算子均值遍历定理可知，全空间产生经典分解：
> $$E = F \oplus Y.$$
> 此时收敛域 $\mathcal{D} = E$，记录恢复映射的定义域为**整个商空间**：
> $$\operatorname{dom}(\mathcal{R}) = Q = E/Y.$$
> 对系统任意初始状态 $x \in E$，$A_{N,M} x$ 与 $R^n x$ 均无条件强范数收敛到同一不变态 $\mathcal{R}(q(x))$。

> **推论 2（Hilbert 空间非膨胀情形）**：
> 若 $E = H$ 为实 Hilbert 空间，且 $T, S$ 均为非膨胀线性算子（$\|T\| \le 1, \|S\| \le 1$）：
> 此时 $K_T = K_S = 1$，空间分解退化为正交直和：
> $$H = F \oplus Y, \qquad Y = F^\perp.$$
> 恢复映射满足等距嵌入性质：
> $$\|\mathcal{R}(\xi)\|_H = \|\xi\|_Q \qquad (\forall \xi \in Q),$$
> 即恢复算子为商空间 $Q$ 到不变子空间 $F$ 上的**等距同构**（$\|\mathcal{R}\| = 1$），达到理论最优的绝对稳定性。
