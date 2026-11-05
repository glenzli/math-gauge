# 参数最小不动点、消元与近似传递

---

## S1　参数与消元

### 1. 结构准备与 $\sigma$ 的良定义与单调性

设 $P$ 为偏序集，$A, B, C$ 为完备格，$L = A \times B \times C$ 赋予分量偏序：对于 $x = (a_1, b_1, c_1), y = (a_2, b_2, c_2) \in L$，
$$
x \le_L y \iff a_1 \le_A a_2 \ \wedge\ b_1 \le_B b_2 \ \wedge\ c_1 \le_C c_2.
$$
任意子集 $S \subseteq L$ 的上、下确界由各分量的上、下确界给出：
$$
\bigvee S = \left(\bigvee \pi_A(S), \bigvee \pi_B(S), \bigvee \pi_C(S)\right), \quad \bigwedge S = \left(\bigwedge \pi_A(S), \bigwedge \pi_B(S), \bigwedge \pi_C(S)\right).
$$
因此，$L$ 是完备格，其底元为 $\bot_L = (\bot_A, \bot_B, \bot_C)$，顶元为 $\top_L = (\top_A, \top_B, \top_C)$。

设 $F: P \times L \to A, G: P \times L \to B, H: P \times L \to C$ 联合单调。映射 $\Phi: P \times L \to L$ 定义为
$$
\Phi(p, x) = (F(p, x), G(p, x), H(p, x)).
$$
由分量序定义，$\Phi$ 从 $P \times L$ 到 $L$ 联合单调。对固定 $p \in P$，自映射 $\Phi_p = \Phi(p, -): L \to L$ 单调。

#### (1) $\mu \Phi_p$ 的存在性（Knaster-Tarski 定理适用性说明）
- **条件核验**：$L$ 为完备格，$\Phi_p: L \to L$ 为单调自映射。Knaster-Tarski 定理的全部前提成立。
- **构造与证明**：
  定义前不动点集 $\mathrm{Pre}(\Phi_p) = \{ x \in L \mid \Phi_p(x) \le x \}$。因 $\Phi_p(\top_L) \le \top_L$，有 $\top_L \in \mathrm{Pre}(\Phi_p) \neq \emptyset$。
  令 $x^* = \bigwedge \mathrm{Pre}(\Phi_p)$。
  1. 对任意 $x \in \mathrm{Pre}(\Phi_p)$，由 $x^* \le x$ 及 $\Phi_p$ 单调性得 $\Phi_p(x^*) \le \Phi_p(x) \le x$。因此 $\Phi_p(x^*)$ 是 $\mathrm{Pre}(\Phi_p)$ 的下界，从而 $\Phi_p(x^*) \le \bigwedge \mathrm{Pre}(\Phi_p) = x^*$，即 $x^* \in \mathrm{Pre}(\Phi_p)$。
  2. 再由 $\Phi_p$ 单调性，$\Phi_p(\Phi_p(x^*)) \le \Phi_p(x^*)$，即 $\Phi_p(x^*) \in \mathrm{Pre}(\Phi_p)$。因为 $x^*$ 是 $\mathrm{Pre}(\Phi_p)$ 的最大下界，必有 $x^* \le \Phi_p(x^*)$。
  3. 综合两式得 $\Phi_p(x^*) = x^*$，即 $x^*$ 是不动点。
  4. 对任意不动点 $y = \Phi_p(y)$，显然 $y \in \mathrm{Pre}(\Phi_p)$，故 $x^* \le y$。
  因此 $x^*$ 是 $\Phi_p$ 的唯一最小不动点，记为 $\mu \Phi_p$。

#### (2) 构造 $\sigma: P \to L$ 及其单调性
定义映射 $\sigma: P \to L$ 为
$$
\sigma(p) = \mu \Phi_p.
$$
- **单调性证明**：设 $p_1 \le_P p_2$。
  因 $\Phi$ 联合单调，有
  $$
  \Phi(p_1, \sigma(p_2)) \le \Phi(p_2, \sigma(p_2)) = \sigma(p_2).
  $$
  这表明 $\sigma(p_2) \in \mathrm{Pre}(\Phi_{p_1})$。
  由最小不动点定义，$\sigma(p_1) = \bigwedge \mathrm{Pre}(\Phi_{p_1}) \le \sigma(p_2)$。故 $\sigma$ 单调。

---

### 2. 任意分块消元与 Bekić 定理的良定义与不变性

设完备格 $L$ 被任意划分为两个子系统的笛卡尔积 $X \times Y$（其中 $X, Y$ 分别为 $A, B, C$ 变量按某种分块构成的完备格子空间），即变量写为 $(x, y)$。设联合单调映射为
$$
\Phi(p, x, y) = (f(p, x, y), g(p, x, y)), \quad f: P \times X \times Y \to X,\ g: P \times X \times Y \to Y.
$$

#### (1) 中间参数最小解的良定义与单调性
固定 $(p, y) \in P \times Y$，考察映射 $x \mapsto f(p, x, y)$。
- **良定义**：$X$ 为完备格，$x \mapsto f(p, x, y)$ 为单调自映射。由 Knaster-Tarski 定理，存在唯一最小不动点
  $$
  \hat{x}(p, y) = \mu x.\, f(p, x, y) = \bigwedge \{ x \in X \mid f(p, x, y) \le x \}.
  $$
- **联合单调性**：设 $(p_1, y_1) \le (p_2, y_2)$。
  由 $f$ 的联合单调性与 $\hat{x}(p_2, y_2)$ 的不动点性质，
  $$
  f(p_1, \hat{x}(p_2, y_2), y_1) \le f(p_2, \hat{x}(p_2, y_2), y_2) = \hat{x}(p_2, y_2).
  $$
  从而 $\hat{x}(p_2, y_2)$ 是映射 $f(p_1, -, y_1)$ 的前不动点。由最小性，
  $$
  \hat{x}(p_1, y_1) \le \hat{x}(p_2, y_2).
  $$
  故 $\hat{x}: P \times Y \to X$ 联合单调。

#### (2) 约化系统的良定义与单调性
将中间最小解代入剩余分量，定义约化映射 $\tilde{g}: P \times Y \to Y$ 为
$$
\tilde{g}(p, y) = g(p, \hat{x}(p, y), y).
$$
- **良定义与单调性**：映射 $(p, y) \mapsto (p, \hat{x}(p, y), y)$ 单调，而 $g$ 联合单调，单调映射的复合仍联合单调，故 $\tilde{g}$ 联合单调。
- 对每个 $p \in P$，$\tilde{g}_p: Y \to Y$ 为完备格 $Y$ 上的单调自映射，由 Knaster-Tarski 定理，存在唯一最小不动点
  $$
  y^*(p) = \mu \tilde{g}_p = \mu y.\, g(p, \hat{x}(p, y), y).
  $$
  由上述相同参数单调性论证可知，$y^*: P \to Y$ 单调。
  进而令 $x^*(p) = \hat{x}(p, y^*(p))$，由于 $\hat{x}$ 与 $y^*$ 均单调，复合 $x^*: P \to X$ 亦单调。

#### (3) 约化消元解与全系统最小解重合
记 $z^*(p) = (x^*(p), y^*(p))$。
1. **$z^*(p)$ 是全系统不动点**：
   $$
   g(p, x^*(p), y^*(p)) = g(p, \hat{x}(p, y^*(p)), y^*(p)) = \tilde{g}(p, y^*(p)) = y^*(p),
   $$
   $$
   f(p, x^*(p), y^*(p)) = f(p, \hat{x}(p, y^*(p)), y^*(p)) = \hat{x}(p, y^*(p)) = x^*(p).
   $$
   因此 $\Phi_p(z^*(p)) = z^*(p)$。
2. **$z^*(p)$ 小于等于任意前不动点**：
   设 $(x, y) \in X \times Y$ 满足 $\Phi_p(x, y) \le (x, y)$，即 $f(p, x, y) \le x$ 且 $g(p, x, y) \le y$。
   - 由 $f(p, x, y) \le x$，$x$ 是 $f(p, -, y)$ 的前不动点，由 $\hat{x}(p, y)$ 的最小性，$\hat{x}(p, y) \le x$。
   - 代入 $g$ 并利用单调性：
     $$
     \tilde{g}(p, y) = g(p, \hat{x}(p, y), y) \le g(p, x, y) \le y.
     $$
     从而 $y$ 是 $\tilde{g}_p$ 的前不动点。由 $y^*(p) = \mu \tilde{g}_p$ 的最小性，有 $y^*(p) \le y$。
   - 再利用 $\hat{x}(p, -)$ 的单调性：
     $$
     x^*(p) = \hat{x}(p, y^*(p)) \le \hat{x}(p, y) \le x.
     $$
   因此 $(x^*(p), y^*(p)) \le (x, y)$。
   由 Knaster-Tarski 定理，全系统的最小前不动点唯一即为最小不动点，故
   $$
   (x^*(p), y^*(p)) = \mu \Phi_p = \sigma(p).
   $$

#### (4) 任意变量分块与顺序的独立性
三变量完备格 $L = A \times B \times C$ 的任意分块形式均可归结为：
- 二分块情形：$(A) \times (B \times C)$、$(B) \times (A \times C)$、$(C) \times (A \times B)$ 及其镜像；
- 三分块逐个消元情形：即置换 $\pi \in S_3$ 所对应的消元顺序（如先消 $A$ 再消 $B$ 最后求 $C$，或先消 $C$ 再消 $A$ 等）。
由于笛卡尔积满足结合律 $(A \times B) \times C \cong A \times (B \times C)$，任意三分块逐次消元等价于嵌套应用两次上述两块消元（Bekić 引理）。因每一步中间系统的最小不动点与全系统的唯一最小不动点 $\sigma(p)$ 严格相等，消元所得的最终解必严格唯一且恒等于 $\sigma(p)$。

---

## S2　伴随结构的精确传递

### 1. 精确传递的证明：$\alpha(\sigma(p)) = \mu \Psi_p$

设 $\alpha \dashv \gamma$ 为伽罗瓦连接（Galois connection / Adjunction），即：
$$
\forall x \in L, y \in M, \quad \alpha(x) \le_M y \iff x \le_L \gamma(y).
$$
由此导出伴随标准性质：
- $\alpha, \gamma$ 均单调；
- 单元（unit）与余单元（counit）不等式：$\forall x \in L, x \le \gamma(\alpha(x))$，$\forall y \in M, \alpha(\gamma(y)) \le y$；
- $\alpha$ 保持所有存在的上确界（特别地 $\alpha(\bot_L) = \bot_M$），$\gamma$ 保持所有存在的下确界。

设 $\Psi: P \times M \to M$ 联合单调且满足交换性条件 $\alpha \Phi_p = \Psi_p \alpha$。记 $x^* = \sigma(p) = \mu \Phi_p$，$y^* = \mu \Psi_p$。

#### 步骤 1：证明 $\mu \Psi_p \le \alpha(\sigma(p))$
计算 $\alpha(x^*)$ 在 $\Psi_p$ 下的作用：
$$
\Psi_p(\alpha(x^*)) = (\Psi_p \alpha)(x^*) = (\alpha \Phi_p)(x^*) = \alpha(\Phi_p(x^*)) = \alpha(x^*).
$$
因此 $\alpha(x^*)$ 是 $\Psi_p$ 的不动点。由 $\mu \Psi_p$ 为 $\Psi_p$ 的最小不动点，直接得
$$
y^* \le \alpha(x^*), \quad \text{即} \quad \mu \Psi_p \le \alpha(\sigma(p)).
$$

#### 步骤 2：证明 $\alpha(\sigma(p)) \le \mu \Psi_p$
根据伴随性质 $\alpha(x^*) \le y^* \iff x^* \le \gamma(y^*)$，只需证 $x^* \le \gamma(y^*)$。
又因 $x^* = \mu \Phi_p = \bigwedge \mathrm{Pre}(\Phi_p)$ 为最小前不动点，只需证 $\gamma(y^*) \in \mathrm{Pre}(\Phi_p)$，即
$$
\Phi_p(\gamma(y^*)) \le \gamma(y^*).
$$
再次利用伴随定义，上式等价于
$$
\alpha(\Phi_p(\gamma(y^*))) \le y^*.
$$
利用交换条件与余单元不等式：
$$
\alpha(\Phi_p(\gamma(y^*))) = \Psi_p(\alpha(\gamma(y^*))) \le \Psi_p(y^*).
$$
（其中不等号由余单元 $\alpha(\gamma(y^*)) \le y^*$ 及 $\Psi_p$ 的单调性保证）。
再由 $y^* = \Psi_p(y^*)$ 为不动点，得
$$
\alpha(\Phi_p(\gamma(y^*))) \le y^* \iff \Phi_p(\gamma(y^*)) \le \gamma(y^*).
$$
因此 $\gamma(y^*)$ 是 $\Phi_p$ 的前不动点。从而 $x^* \le \gamma(y^*)$，等价地 $\alpha(x^*) \le y^*$。

综合步骤 1 与步骤 2，严格得到
$$
\alpha(\sigma(p)) = \mu \Psi_p.
$$

---

### 2. 与 S1 分块结果及参数单调性的一致性

1. **参数单调性一致**：
   由 S1 知 $\sigma: P \to L$ 单调；又由伴随性知左伴随 $\alpha: L \to M$ 单调，故复合映射 $p \mapsto \alpha(\sigma(p))$ 单调。这与由 $\Psi$ 联合单调直接推得的 $p \mapsto \mu \Psi_p$ 单调性完全一致。
2. **分块消元一致**：
   S1 证明了对 $L$ 上的系统 $\Phi_p$，任何分块方式、任意中间消元步骤求得的最终解均为唯一的 $\sigma(p)$。故将 $\alpha$ 作用于任意分块消元过程的终态，结果恒为 $\alpha(\sigma(p)) = \mu \Psi_p$。
   若 $M$ 亦相应分块且 $\alpha$ 分量分解（即 $\alpha = \alpha_X \times \alpha_Y$），则交换性 $\alpha \Phi_p = \Psi_p \alpha$ 保证中间参数最小解与约化方程在 $\alpha$ 作用下完全对应，传递在分块消元的每一阶段均逐点成立。

---

## S3　单边更新关系

固定 $p$，记 $T = \Phi_p: L \to L$，$U = \Psi_p: M \to M$ 为完备格上的单调自映射，且 $\alpha \dashv \gamma$。

### 1. 情形一：只假设 $\alpha T \le U \alpha$

- **能推出的有向比较**：
  $$
  \alpha(\mu T) \le \mu U \quad (\text{等价于 } \mu T \le \gamma(\mu U)).
  $$
- **证明**：
  考察 $\gamma(\mu U)$。利用条件 $\alpha T \le U \alpha$ 以及余单元不等式 $\alpha(\gamma(\mu U)) \le \mu U$：
  $$
  \alpha(T(\gamma(\mu U))) \le U(\alpha(\gamma(\mu U))) \le U(\mu U) = \mu U.
  $$
  由伴随关系，$\alpha(T(\gamma(\mu U))) \le \mu U \iff T(\gamma(\mu U)) \le \gamma(\mu U)$。
  因此 $\gamma(\mu U)$ 是 $T$ 的前不动点。
  由 Knaster-Tarski 定理，$\mu T$ 是 $T$ 的最小前不动点，故 $\mu T \le \gamma(\mu U)$。
  再次由伴随关系，即得 $\alpha(\mu T) \le \mu U$。
- **反向比较 $\mu U \le \alpha(\mu T)$ 无法推出**。
- **比较严格的有限格例子（严格不等 $\alpha(\mu T) < \mu U$）**：
  取有限链 $L = \{0, 1\}$（$0 < 1$），$M = \{0, 1\}$（$0 < 1$）。
  取恒等伴随：$\alpha = \mathrm{id}, \gamma = \mathrm{id}$，满足 $\alpha \dashv \gamma$。
  定义单调映射：
  $$
  T(x) = 0 \quad (\forall x \in L), \qquad U(y) = 1 \quad (\forall y \in M).
  $$
  核验单边条件：$\alpha(T(x)) = 0$，$U(\alpha(x)) = 1$。因 $0 \le 1$，对所有 $x \in L$ 均有 $\alpha(T(x)) \le U(\alpha(x))$，条件严格成立。
  计算最小不动点：
  $$
  \mu T = 0 \implies \alpha(\mu T) = 0, \qquad \mu U = 1.
  $$
  此时 $\alpha(\mu T) = 0 < 1 = \mu U$，严格不等。

---

### 2. 情形二：只假设 $U \alpha \le \alpha T$

- **能推出的有向比较**：
  $$
  \mu U \le \alpha(\mu T).
  $$
- **证明**：
  考察 $\alpha(\mu T)$ 在 $U$ 下的作用。利用条件 $U \alpha \le \alpha T$ 以及 $\mu T$ 是 $T$ 的不动点（$T(\mu T) = \mu T$）：
  $$
  U(\alpha(\mu T)) \le \alpha(T(\mu T)) = \alpha(\mu T).
  $$
  这表明 $\alpha(\mu T)$ 是 $U$ 的前不动点。
  由 Knaster-Tarski 定理，$\mu U$ 是 $U$ 的最小前不动点，故直接得出
  $$
  \mu U \le \alpha(\mu T).
  $$
- **反向比较 $\alpha(\mu T) \le \mu U$ 无法推出**。
- **比较严格的有限格例子（严格不等 $\mu U < \alpha(\mu T)$）**：
  取有限格 $L = \{0, 1, 2\}$（$0 < 1 < 2$），$M = \{0, 1\}$（$0 < 1$）。
  定义伴随对 $\alpha: L \to M, \gamma: M \to L$：
  $$
  \alpha(0) = 0, \quad \alpha(1) = 0, \quad \alpha(2) = 1;
  $$
  $$
  \gamma(0) = 1, \quad \gamma(1) = 2.
  $$
  - 核验 $\alpha \dashv \gamma$：
    $\alpha(x) \le 0 \iff x \in \{0, 1\} \iff x \le \gamma(0) = 1$；
    $\alpha(x) \le 1 \iff x \in \{0, 1, 2\} \iff x \le \gamma(1) = 2$。伴随关系成立。
  定义单调映射：
  $$
  T(0) = 1, \quad T(1) = 2, \quad T(2) = 2;
  $$
  $$
  U(0) = 0, \quad U(1) = 0.
  $$
  - 核验单边条件 $U \alpha \le \alpha T$：
    - $x = 0$：$U(\alpha(0)) = U(0) = 0 \le \alpha(T(0)) = \alpha(1) = 0$；
    - $x = 1$：$U(\alpha(1)) = U(0) = 0 \le \alpha(T(1)) = \alpha(2) = 1$；
    - $x = 2$：$U(\alpha(2)) = U(1) = 0 \le \alpha(T(2)) = \alpha(2) = 1$。
    条件对所有 $x \in L$ 均成立。
  计算最小不动点：
  - $T$ 的不动点仅有 $2$，故 $\mu T = 2$，因此 $\alpha(\mu T) = \alpha(2) = 1$。
  - $U$ 的不动点集为 $\{0\}$，故 $\mu U = 0$。
  此时 $\mu U = 0 < 1 = \alpha(\mu T)$，严格不等。

---

## S4　单调半共轭

设 $L, M$ 为完备格，$T: L \to L, U: M \to M$ 单调，$\alpha: L \to M$ 单调且满足半共轭性 $\alpha T = U \alpha$。不假设 $\alpha$ 存在右伴随 $\gamma$。

### 1. 结论判断
**判断：$\alpha(\mu T) = \mu U$ 不一定成立。**

---

### 2. 普遍成立的有向比较与证明
- **普遍成立的有向比较**：
  $$
  \mu U \le \alpha(\mu T).
  $$
- **证明**：
  因为 $L$ 为完备格且 $T$ 单调，由 Knaster-Tarski 定理，$\mu T$ 存在且为不动点，即 $T(\mu T) = \mu T$。
  将 $\alpha$ 作用于该等式两边，并利用半共轭条件 $\alpha T = U \alpha$：
  $$
  U(\alpha(\mu T)) = \alpha(T(\mu T)) = \alpha(\mu T).
  $$
  这表明 $\alpha(\mu T)$ 是 $M$ 上映射 $U$ 的一个不动点。
  因为 $M$ 为完备格且 $U$ 单调，$\mu U$ 是 $U$ 的最小不动点（亦即全体前不动点之最大下界），所以
  $$
  \mu U \le \alpha(\mu T).
  $$
  该论证仅依赖 $\mu T$ 是不动点、$\alpha T = U \alpha$ 以及 $\mu U$ 的最小性，无需 $\alpha$ 的伴随性或连续性。

---

### 3. 反例核验（精确等式失效）

#### 反例（有限格基元反例）
- 取 $L = \{0\}$（单元素完备格），$M = \{0, 1\}$（$0 < 1$ 的二元完备格）。
- 定义单调映射：
  $$
  T(0) = 0, \qquad U(y) = y \quad (\forall y \in M).
  $$
- 定义 $\alpha: L \to M$ 为
  $$
  \alpha(0) = 1.
  $$
  显然 $\alpha$ 单调（定义域为单点集）。
- 核验半共轭交换性：
  $$
  \alpha(T(0)) = \alpha(0) = 1, \qquad U(\alpha(0)) = U(1) = 1.
  $$
  故 $\alpha T = U \alpha$ 恒成立。
- 计算最小不动点：
  $$
  \mu T = 0 \implies \alpha(\mu T) = \alpha(0) = 1;
  $$
  $$
  \mu U = 0 \quad (\text{因 } U(0) = 0 \text{ 且 } 0 \text{ 是 } M \text{ 的底元}).
  $$
- 比较：$\mu U = 0 < 1 = \alpha(\mu T)$，等式不成立。

> **注（关于保底元性）**：即使追加 $\alpha(\bot_L) = \bot_M$，若缺乏下文 S5 的链连续性，结论仍可能失败。例如取 $L = \mathbb{N} \cup \{\omega\}$，$M = \{0, 1\}$，$T(n) = n+1, T(\omega) = \omega$，$U = \mathrm{id}_M$，$\alpha(n) = 0, \alpha(\omega) = 1$。此时 $\alpha(\bot_L) = \bot_M$ 且 $\alpha T = U \alpha$，但 $\alpha(\mu T) = \alpha(\omega) = 1 > 0 = \mu U$。

---

## S5　连续递推的传递

设 $L, M$ 为完备格，$T, U$ 单调且保持递增 $\omega$ 链的上确界（即 $\omega$-连续）。设 $\alpha: L \to M$ 单调、$\alpha(\bot_L) = \bot_M$、保持递增 $\omega$ 链的上确界，并满足 $\alpha T = U \alpha$。不假设 $\alpha$ 有右伴随。

### 1. 结论判断
**判断：最小不动点能精确传递，即 $\alpha(\mu T) = \mu U$ 必成立。**

---

### 2. 论证

#### (1) Kleene 不动点定理的适用性说明与最小不动点表述
- **条件核验**：$L$ 为完备格（具有底元 $\bot_L$），$T$ 单调且 $\omega$-连续。
- 构造 Kleene 迭代序列：$x_0 = \bot_L$，$x_{n+1} = T(x_n) = T^{n+1}(\bot_L)$。
  由于 $\bot_L \le T(\bot_L)$，由 $T$ 的单调性归纳可知 $x_n \le x_{n+1}$（$\forall n < \omega$），故 $(T^n(\bot_L))_{n<\omega}$ 是 $L$ 中的递增 $\omega$ 链。
- 完备格保证其上确界 $x_\omega = \bigvee_{n < \omega} T^n(\bot_L)$ 存在。由 $T$ 的 $\omega$-连续性：
  $$
  T(x_\omega) = T\left(\bigvee_{n<\omega} T^n(\bot_L)\right) = \bigvee_{n<\omega} T\left(T^n(\bot_L)\right) = \bigvee_{n<\omega} T^{n+1}(\bot_L) = \bigvee_{1 \le n < \omega} T^n(\bot_L).
  $$
  因 $T^0(\bot_L) = \bot_L \le T^1(\bot_L)$，添加第 0 项不改变上确界，故 $T(x_\omega) = x_\omega$。
  若 $T(z) \le z$，则 $\bot_L \le z$；归纳可得 $T^n(\bot_L) \le z$（$\forall n$），进而 $x_\omega \le z$。
  因此，
  $$
  \mu T = \bigvee_{n < \omega} T^n(\bot_L).
  $$
- 同理，$M$ 为完备格且 $U$ 为 $\omega$-连续自映射，故
  $$
  \mu U = \bigvee_{n < \omega} U^n(\bot_M).
  $$

#### (2) 沿递推链的精确交换
用数学归纳法证明对任意有限步 $n < \omega$，均有 $\alpha(T^n(\bot_L)) = U^n(\bot_M)$：
1. **基础步（$n = 0$）**：
   $$
   \alpha(T^0(\bot_L)) = \alpha(\bot_L) = \bot_M = U^0(\bot_M).
   $$
   （此处用到了条件 $\alpha(\bot_L) = \bot_M$）。
2. **归纳步**：假设 $\alpha(T^k(\bot_L)) = U^k(\bot_M)$。
   利用半共轭性 $\alpha T = U \alpha$ 以及归纳假设：
   $$
   \alpha(T^{k+1}(\bot_L)) = \alpha(T(T^k(\bot_L))) = U(\alpha(T^k(\bot_L))) = U(U^k(\bot_M)) = U^{k+1}(\bot_M).
   $$
归纳成立，对所有 $n < \omega$ 均有 $\alpha(T^n(\bot_L)) = U^n(\bot_M)$。

#### (3) 极限处的保持性
由于 $(T^n(\bot_L))_{n<\omega}$ 是递增 $\omega$ 链，且 $\alpha$ 保持递增 $\omega$ 链的上确界，结合上述结果：
$$
\alpha(\mu T) = \alpha\left(\bigvee_{n<\omega} T^n(\bot_L)\right) = \bigvee_{n<\omega} \alpha(T^n(\bot_L)) = \bigvee_{n<\omega} U^n(\bot_M) = \mu U.
$$
证毕。

---

## S6　可数阶段与边界

设 $L$ 为完备格、$T: L \to L$ 仅假设单调，记 $x_\omega = \bigvee_{n<\omega} T^n(\bot)$。

### 1. 结论判断
**判断：$x_\omega$ 不一定是 $\mu T$。**

---

### 2. $x_\omega = \mu T$ 的充要条件与证明

- **充要条件**：
  $$
  T(x_\omega) \le x_\omega
  $$
  （或等价表述为：$T(x_\omega) = x_\omega$，即 $x_\omega$ 是 $T$ 的不动点；
  亦等价于：$T$ 在自身底元轨道链上保持上确界，即 $T\left(\bigvee_{n<\omega} T^n(\bot)\right) = \bigvee_{n<\omega} T^{n+1}(\bot)$）。

- **充分必要性证明**：
  首先建立一个先验不等式：由 $\bot \le T(\bot)$ 及 $T$ 单调性可知 $(T^n(\bot))_{n<\omega}$ 为递增链。
  对每个 $n < \omega$，有 $T^n(\bot) \le x_\omega$，故 $T^{n+1}(\bot) \le T(x_\omega)$。
  两边对 $n < \omega$ 取上确界：
  $$
  x_\omega = \bigvee_{n < \omega} T^{n+1}(\bot) \le T(x_\omega).
  $$
  因此不等式 $x_\omega \le T(x_\omega)$ 永远无条件成立。
  1. **充分性**：若 $T(x_\omega) \le x_\omega$，结合先验不等式必有 $T(x_\omega) = x_\omega$，故 $x_\omega$ 是不动点。
     设 $z \in L$ 为任意前不动点（$T(z) \le z$）。因 $\bot \le z$，由单调性归纳得 $T^n(\bot) \le z$（$\forall n < \omega$），从而 $x_\omega = \bigvee_{n<\omega} T^n(\bot) \le z$。
     这说明 $x_\omega$ 小于等于任意前不动点，由 Knaster-Tarski 定理，必有 $x_\omega = \mu T$。
  2. **必要性**：若 $x_\omega = \mu T$，则由最小不动点性质，$x_\omega$ 本身就是不动点，即 $T(x_\omega) = x_\omega$。特别地，显然满足 $T(x_\omega) \le x_\omega$。

---

### 3. 条件失败的完整反例

构造如下序数格及单调映射：
- 取 $L = \omega + 2 = \{0, 1, 2, \dots, \omega, \omega+1\}$，其偏序定义为标准序数序：
  $$
  0 < 1 < 2 < \dots < n < n+1 < \dots < \omega < \omega+1.
  $$
  $L$ 为良序全序集且有最大元 $\omega+1$，故 $L$ 是完备格（链），底元为 $\bot = 0$，顶元为 $\top = \omega+1$。
- 定义自映射 $T: L \to L$ 为：
  $$
  T(x) = \begin{cases}
  x + 1, & x < \omega, \\
  \omega + 1, & x = \omega, \\
  \omega + 1, & x = \omega + 1.
  \end{cases}
  $$
- **核验 $T$ 的单调性**：
  - 若 $m \le n < \omega$，则 $T(m) = m + 1 \le n + 1 = T(n)$；
  - 若 $n < \omega$，则 $T(n) = n + 1 < \omega < \omega + 1 = T(\omega) = T(\omega+1)$；
  - 若 $x, y \in \{\omega, \omega+1\}$，则 $T(x) = \omega+1 \le \omega+1 = T(y)$。
  故 $T$ 在全链上单调。
- **计算可数阶段上确界 $x_\omega$**：
  $T^0(\bot) = 0$，$T^1(\bot) = 1$，$\dots$，$T^n(\bot) = n$。
  $$
  x_\omega = \bigvee_{n < \omega} T^n(\bot) = \bigvee_{n < \omega} n = \omega.
  $$
- **核验充要条件失败**：
  $$
  T(x_\omega) = T(\omega) = \omega + 1.
  $$
  由于 $\omega + 1 > \omega = x_\omega$，不等式 $T(x_\omega) \le x_\omega$ 严格失败！
- **求解真实的 $\mu T$**：
  - 对任何有限序数 $n < \omega$，$T(n) = n+1 \neq n$；
  - 对极限序数 $\omega$，$T(\omega) = \omega+1 \neq \omega$；
  - 对 $\omega+1$，$T(\omega+1) = \omega+1$。
  故 $T$ 的唯一不动点为 $\omega+1$，即 $\mu T = \omega+1$。
- **对比**：$x_\omega = \omega < \omega+1 = \mu T$，可数阶段未达到最小不动点。

---

### 4. 精确传递的两个充分机制梳理及非必要性分析

结合 S2 与 S5，实现最小不动点精确传递 $\alpha(\mu T) = \mu U$ 的两个充分机制为：

| 机制 | 假设条件 | 核心作用原理 | 对不动点闭包阶数的要求 |
| :--- | :--- | :--- | :--- |
| **机制一：伴随结构（Galois 机制，S2）** | $\alpha \dashv \gamma$ 且 $\alpha T = U \alpha$ | 基于前不动点与完全上确界保持：左伴随 $\alpha$ 将 $T$-前不动点转化为 $U$-前不动点，右伴随 $\gamma$ 将 $U$-前不动点逆推为 $T$-前不动点 | **无要求**：即使系统需超穷迭代至不可数阶段，等式依然精确成立 |
| **机制二：$\omega$-连续递推（Kleene 机制，S5）** | $T, U, \alpha$ 均 $\omega$-连续，$\alpha(\bot_L)=\bot_M$，且 $\alpha T = U \alpha$ | 基于可数近似与极限交换：不动点在 $\omega$ 阶段闭合（$\mu T = x_\omega, \mu U = y_\omega$），且 $\alpha$ 逐步与算子交换并与递增极限交换 | **严格要求**：系统必须在 $\omega$ 阶段达到不动点，但无需 $\alpha$ 具有右伴随 |

#### 这两套机制均非必要条件的分析
1. **机制一非必要**：
   在机制二适用的情形下，映射 $\alpha$ 往往仅是连续的（例如在 Domain 理论或赋范空间上的抽象），并不保持任意上确界，因而不存在右伴随 $\gamma$，但精确传递依然成立。
2. **机制二非必要**：
   在机制一适用的情形下，$T$ 和 $U$ 可以是高度不连续的（例如上述需超穷迭代至 $\omega+1$ 或更高序数的反例系统）。只要配备伴随结构 $\alpha \dashv \gamma$，最小不动点无需在可数步收敛，传递依旧精确成立。
3. **两机制可同时不成立而传递依然成立**：
   “$\alpha(\mu T) = \mu U$” 本质上是关于单一点（最小不动点）的局部代数性质，而机制一与机制二施加的都是全局结构性假设（全局伽罗瓦伴随或整空间上的链连续性）。
   例如：若 $T, U$ 满足 $\mu T = \bot_L, \mu U = \bot_M$（迭代在第 0 步即闭合），且 $\alpha(\bot_L) = \bot_M, \alpha T = U \alpha$。此时只要 $\alpha$ 单调，必有 $\alpha(\mu T) = \alpha(\bot_L) = \bot_M = \mu U$，结论平凡成立；在此情形下，$T, U$ 在其他位置可以完全不具备 $\omega$-连续性（机制二失效），$\alpha$ 也无需保持任意上确界从而无右伴随（机制一失效）。
