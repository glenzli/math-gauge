# 答卷审阅报告

审阅范围依据 [materials.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/materials.md) 由原题 [original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md) 与待审答卷 [original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md) 共同确定。

---

## 一、总体判断

- **S1–S5 及 S6 第 1 小问**：结论、构造、证明与反例在原题条件下**均数学正确**（仅含少量不影响论证成立的常规简略与一处措辞方向小瑕疵）。
- **S6 第 2 小问（逻辑蕴含梳理）**：**不完全正确且不完整**。具体存在三方面实质问题：
  1. **蕴含方向写反与反例逻辑误用**（表格第 7 行将逆命题 $Q \implies P$ 的不成立误写为对 $P \implies Q$ 的否定，而 $P \implies Q$ 在交换设定下实由 S1 成立）；
  2. **概念混同与前提遗漏**（在已拆分“存在性”与“唯一性”的前提下，表格第 1、3 行漏写满射性/各层存在性前提）；
  3. **遗漏原题明确要求整理的四类性质“之间”的多组蕴含与不蕴含判断**（如 `极限核逐元素幂零 ⇏ 元素提升`、`元素提升 ⇏ 极限核逐元素幂零`、`元素提升` 与 `幂等提升 / 唯一性` 间的关系等）。

---

## 二、逐阶段核查与数学依据

### 1. S1　单层提升（正确、完整）
- **对应范围**：[original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L9-L11)，[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L5-L45)。
- **核查依据**：
  - **唯一性**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L9-L20)）：对 $\delta = \tilde{e}_1 - \tilde{e}_2 \in \ker q$ 取正整数 $m \ge 1$ 使 $\delta^m = 0$（$\delta = 0$ 或零环时取 $m=1$ 亦成立）。由 $R$ 交换，$\epsilon = \tilde{e}_1(1-\tilde{e}_2) = \tilde{e}_1 \delta$ 既满足 $\epsilon^2 = \epsilon$ 又满足 $\epsilon^m = \tilde{e}_1^m \delta^m = 0$，故 $\epsilon = 0$，对称得 $\tilde{e}_1 = \tilde{e}_1\tilde{e}_2 = \tilde{e}_2$。注意此唯一性证明甚至不依赖 $q$ 满射。
  - **存在性构造**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L22-L45)）：由 $q$ 满射取 $x \in q^{-1}(e)$，则 $(x^2-x)^n = 0$（某 $n \ge 1$）。取整系数多项式 $E_n(X) = \sum_{k=n}^{2n-1}\binom{2n-1}{k}X^k(1-X)^{2n-1-k} \in \mathbb{Z}[X]$。因 $\mathbb{Z}[X]$ 中 $X + (1-X) = 1$，有 $(X) \cap (1-X) = (X(1-X)) = (X^2-X)$；由 $E_n(X) \equiv 0 \pmod X$ 与 $1 - E_n(X) \equiv 0 \pmod{1-X}$ 得 $E_n(X) - X \in (X^2-X)$，代入 $x$ 知 $E_n(x) - x \in (x^2-x)R \subseteq \ker q$，即 $q(\tilde{e}) = e$。又 $X^n \mid E_n(X)$ 且 $(1-X)^n \mid (1-E_n(X))$，故 $E_n(X)(1-E_n(X)) \in (X^n(1-X)^n) = ((X^2-X)^n)$，代入 $x$ 得 $\tilde{e}^2 = \tilde{e}$。全程无需 $2$ 可逆或统一幂零指数。

### 2. S2　任意有向逆系（正确，含少量常规一步简略）
- **对应范围**：[original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L13-L15)，[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L49-L101)。
- **核查依据**：
  - **$p: L \to S$ 构造**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L51-L57)）：由 $I$ 非空取 $i \in I$ 定义 $p(x) = p_i(x_i)$；对任意 $i, j \in I$，由有向性取 $k \ge i, j$，结合相容性 $x_i = \rho_{ik}(x_k)$ 与 $p_i\rho_{ik} = p_k$ 严格证明与指标无关，且 $p = p_i \circ \pi_i$ 为含幺环同态。
  - **$D_J(L) \cong D_J(S)$**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L59-L77)）：严谨区分了 $J = \emptyset$ 与零环边界情形（由 $1_{R_i} \in \ker p_i$ 幂零推出 $S=0 \iff \forall i, R_i = 0 \iff L = 0$）；$J \neq \emptyset$ 时对每层应用 S1 得唯一幂等提升 $\tilde{e}_{j,i}$，再由 $R_i$ 中 S1 唯一性强迫过渡相容 $\rho_{ik}(\tilde{e}_{j,k}) = \tilde{e}_{j,i}$、正交性 $\tilde{e}_{j,i}\tilde{e}_{k,i} = 0$ 及有限正交幂等和 $\sum_{j \in J}\tilde{e}_{j,i} = 1_{R_i}$。
  - **环分解与自然性**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L79-L101)）：$\Phi$ 与 $\Psi$ 的良定性、互逆性（含 $J = \emptyset, L = 0$ 的退化情形）以及提升双射 $v_* \circ (p_*)^{-1} = (p'_*)^{-1} \circ u_*$ 和商环乘积同构 $(\prod_j v_j) \circ \Phi = \Phi' \circ v$ 的自然性均成立。
  - **细微简略（不影响正确性）**：[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L64-L70) 未显式写出含幺环同态 $p$ 保持 $D_J$ 条件（即 $p_*(D_J(L)) \subseteq D_J(S)$）以及 $S = p_i(R_i)$ 自动为交换环从而满足 S1 前提；[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L94-L98) 将 $v(L) \subseteq L'$（因 $\rho'_{ij}(u_j(x_j)) = u_i(\rho_{ij}(x_j)) = u_i(x_i)$）、$p' \circ v = u \circ p$（因 $p'_i(u_i(x_i)) = u(p_i(x_i))$）作“显然”略写，并默认目标系统 $(R'_i, \rho'_{ij}, p'_i, S')$ 同样满足共同逆系条件以保证 $p'_*$ 为双射。

### 3. S3　极限核（结论与实质论证正确，含一处措辞方向小瑕疵）
- **对应范围**：[original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L17-L19)，[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L105-L122)。
- **核查依据**：结论“否”正确。取相容元组 $x = (t \bmod t^{n+1})_{n \ge 1} \in L \cong k[[t]]$，有 $p(x) = 0$；对任意 $m \ge 1$，$x^m$ 在 $R_m = k[t]/(t^{m+1})$ 的分量为 $t^m \bmod t^{m+1} \neq 0$（域 $k$ 中 $1 \neq 0$），故 $x^m \neq 0_L$。与 S2 的一致性说明准确（S2 仅依赖各有限层 $\ker p_n$ 逐元素幂零，不要求亦不推出 $\ker p$ 逐元素幂零，且整环 $k[[t]]$ 与域 $k$ 的幂等元均仅为 $0, 1$）。
- **细微瑕疵（不影响结论）**：[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L116) 写“在 $R_m = k[t]/(t^{m+1})$ 中，$t^m \not\equiv 0 \pmod{t^{m+1}}$，故其在极限中的像 $t^m \neq 0$”，态射方向表述欠妥——逆极限具有典范投影 $\pi_m: L \to R_m$ 而无同态 $R_m \to L$，严格表述应为“$x^m \in L$ 在 $R_m$ 中的投影非零，故 $x^m \neq 0$”（或指 $t^m \in k[t]$ 在 $L$ 中的像）。此外，S3 正文未显式验算 $(\ker p_n)^{n+1} = ((t)/(t^{n+1}))^{n+1} = 0$（仅在 [original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L239) 提及）。

### 4. S4　相容元素的满射性（正确、完整）
- **对应范围**：[original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L21-L23)，[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L126-L145)。
- **核查依据**：由 $p_1$ 满射取 $x_1 \in p_1^{-1}(s)$，由 $\rho_n$ 满射保证 $\rho_n^{-1}(x_n) \neq \emptyset$，并利用 $p_{n+1} = p_n \circ \rho_n$ 验证所取 $x_{n+1}$ 自动满足 $p_{n+1}(x_{n+1}) = s$；在 ZFC 下援引依赖选择公理（DC）获得相容序列 $x = (x_n)_{n \ge 1} \in L$ 使 $p(x) = s$，全程不依赖交换性或幂零核。

### 5. S5　逐层增广（结论与反例核验完全正确）
- **对应范围**：[original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L25-L27)，[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L149-L200)。
- **核查依据**：结论“否”正确。对任意域 $k$（含任意特征），理想化环 $R_n = k[x] \ltimes k[t]$（经由求值同态 $\mathrm{ev}_0: k[x] \to k$ 赋予 $k[t]$ 模结构）为含幺交换环，$p_n(a, P) = a$ 满射且 $(\ker p_n)^2 = 0$。因 $a \mapsto a'(0)\cdot 1$ 为 $\mathrm{ev}_0$-导子、$P \mapsto tP$ 为 $k$-线性映射，$\rho_n(a, P) = (a, a'(0)\cdot 1 + tP(t))$ 严格为满足 $p_n\rho_n = p_{n+1}$ 的含幺环同态（复合即得 $I = \mathbb{N}_{\ge 1}$ 上的完整过渡族）。对 $x \in k[x]$，任何相容原像均迫使 $P_1(t) = \sum_{j=0}^{N-1} t^j + t^N P_{N+1}(t)$（$\forall N \ge 1$），在域（$1_k \neq 0_k$）上与多项式仅有有限项非零矛盾，严格证明 $p: L \to S$ 不满射。

### 6. S6 第 1 小问　非交换单层幂等提升唯一性（正确）
- **对应范围**：[original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L29-L31)，[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L206-L222)。
- **核查依据**：结论“否”正确。域 $k$（如 $\mathbb{F}_2$ 或 $\mathbb{Q}$）上 $2 \times 2$ 上三角矩阵环 $R \xrightarrow{q} k \times k$ 满足 $(\ker q)^2 = 0$，幂等元 $(1,0)$ 有不同幂等提升 $\begin{pmatrix}1&0\\0&0\end{pmatrix} \neq \begin{pmatrix}1&1\\0&0\end{pmatrix}$。（细微处：略去了 $q$ 保乘法的单行验算；[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L222)“若域 $k$ 至少含两个元素”为冗余条件，因域公理自带 $1 \neq 0$，不影响反例有效性。）

---

## 三、主要问题详析：S6 第 2 小问（逻辑蕴含梳理）

原题 [original-task.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-task.md#L31) 要求：
> 再整理S1–S5中“元素提升、幂等提升、幂等提升唯一、极限核逐元素幂零”之间哪些蕴含已证明、哪些不能从现有条件推出。

答卷在 [original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L224-L240) 的整理存在以下具体错误与遗漏：

### 问题 1：表格第 7 行将蕴含方向颠倒，导致真假判断与依据失配
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L240)
  > `极限核逐元素幂零 \implies 极限幂等提升唯一 | 不必要 | S3 与 S2 对比 | S3 中极限核不仅不逐元素幂零……但依据 S2，极限上的幂等提升仍然严格唯一。`
- **数学依据与影响**：
  1. **逻辑方向错误**：记 $P$ 为“极限核逐元素幂零”，$Q$ 为“极限幂等提升唯一”。S3 给出的是 **$P$ 假而 $Q$ 真** 的实例，这证伪的是**逆蕴含** $Q \implies P$（即 `极限幂等提升唯一 ⇏ 极限核逐元素幂零`，说明 $P$ 不是 $Q$ 的必要条件），而**绝不能否定**表中所写的命题 $P \implies Q$（前件为假时蕴含式 $P \implies Q$ 为真）。
  2. **所写命题 $P \implies Q$ 的真实状态被掩盖**：
     - 在**交换环**设定下（S1、S2、S3、S5 中 $L$ 均交换），直接对环同态 $p: L \to S$ 应用 **S1 第 1 部分的唯一性证明**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L9-L20)，无需 $p$ 满射），即可严格**证明** `（交换 +）极限核逐元素幂零 ⟹ 极限幂等提升（若存在则）唯一` **成立**；若同时具备 `元素提升`（$p$ 满射），由 S1 更直接证明 `极限幂等提升存在且唯一`。
     - 在**非交换环**设定下（如 S4 的一般含幺环塔），$P \implies Q$ **不成立**，但反例应取 **S6 第 1 小问**的常值塔 $R_n = R, \rho_n = \mathrm{id}_R$（此时 $(\ker p)^2 = 0$ 故 $P$ 真，但 $Q$ 假），而非 S3。

### 问题 2：表格第 1、3 行混同“(B) 存在性”与“(C) 唯一性”，遗漏必要前提
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L227-L236)。答卷先在 #L227–L229 将概念明确拆分为 `(A) 元素提升`、`(B) 幂等提升存在性`、`(C) 幂等提升唯一性`，随后却在表格中混用：
  1. **第 1 行**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L234)）写 `单层中：(交换 + 核逐元素幂零) ⟹ 幂等提升唯一`，说明栏却写“利用交换性与二项式多项式 $E_n(X)$……完成构造与唯一性证明”。实际上，仅由 `交换 + 核逐元素幂零` 只能得到至多一个提升（唯一性，且无需 $E_n(X)$）；要完成 $E_n(X)$ 的**存在性构造**，必须加入前提 **`(A) 元素提升`（$q$ 满射）**（反例：对角单射 $\mathbb{Z} \hookrightarrow \mathbb{Z} \times \mathbb{Z}$ 满足交换且核为 $0$，但 $(1,0)$ 无提升）。
  2. **第 3 行**（[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L236)）写 `各层幂等提升唯一 ⟹ 极限幂等提升存在且唯一`。左端仅写各层唯一性 `(C)`，右端却声称导出极限存在性 `(B)`。若各层仅有“至多一个幂等提升”而无存在性，极限绝不能推出存在性（反例：常值塔 $\mathbb{Z} \to \mathbb{Z}/6\mathbb{Z}$ 中，$\mathbb{Z}/6\mathbb{Z}$ 的幂等元 $0, 1, 3, 4 \bmod 6$ 在每层 $\mathbb{Z}$ 中均至多有一个幂等提升，但 $3 \bmod 6$ 在极限 $\mathbb{Z}$ 中无幂等提升）。S2 实际证明的是 `各层幂等提升存在且唯一 ⟹ 极限幂等提升存在且唯一`。

### 问题 3：遗漏原题指定四类性质“之间”的多项关键蕴含判断
- **具体位置**：[original-answer.md](file:///private/tmp/math-gauge-carbon-high-lane1-20261115-v1/attempts/MG-AR001/physical-1/session/work/original-answer.md#L232-L240)。答卷将大量篇幅放在“各层条件 $\implies$ 极限性质”（第 3、5、6 行），却漏掉了原题点名的四类性质——**(A) 元素提升、(B) 幂等提升、(C) 幂等提升唯一、(D) 极限核逐元素幂零**——彼此之间的多组关键关系：
  1. **`(D) 极限核逐元素幂零 ⇏ (A) 元素提升`（甚至 `(B) + (C) + (D) ⇏ (A)`）**：
     在 **S5** 的反例中，若 $y = ((a_n, P_n))_{n\ge 1} \in \ker p$，则 $a_n = 0$，从而 $(0, P_n)^2 = (0, 0)$（甚至由 $P_n = tP_{n+1}$ 得 $P_n = 0$，即 $\ker p = \{0\}$），故 **(D) 极限核逐元素幂零在 S5 中成立**，而 **(A) 元素提升不成立**。答卷第 4 行仅从 S5 提取了 `(B)+(C) ⇏ (A)`，漏掉了 `(D) ⇏ (A)`（及三者合取仍不蕴含 `(A)`）。
  2. **`(A) 元素提升 ⇏ (D) 极限核逐元素幂零`（甚至 `(A) + (B) + (C) ⇏ (D)`）**：
     在 **S3** 中，$p: k[[t]] \to k$ 满射，**(A)、(B)、(C) 同时成立**，但 **(D) 不成立**。答卷未列出 `(A) ⇏ (D)`、`(B) ⇏ (D)`（而 `(C) ⇏ (D)` 在第 7 行被写反了箭头）。
  3. **从 `(A) 元素提升` 到 `(B) 幂等提升`、`(C) 幂等提升唯一` 的关系**：
     在 S4 的一般条件下（不假设交换性或各层幂零核），S4 证明了 `(A)`，但不能推出 `(B)`（如常值塔 $\mathbb{Z} \to \mathbb{Z}/6\mathbb{Z}$ 中 $3 \bmod 6$ 无幂等提升），亦不能由 `(A) + (B)` 推出 `(C)`（如常值塔 $k \times k \to k$，或 S6.1 的非交换常值塔——后者甚至满足 `(A) + (B) + (D) ⇏ (C)`）。（而在 S2 的共同逆系设定下，`(B)` 与 `(C)` 已由 S2 无条件成立，无需 `(A)`。）
  4. **`(B) 幂等提升` 与 `(C) 幂等提升唯一` 彼此间的关系**：
     答卷未直接讨论 `(B)` 与 `(C)` 的互推：一般而言 `(B) ⇏ (C)`（非交换有 S6.1 反例，交换无幂零核有 $k \times k \to k$ 反例）；若按答卷将 `(C)` 定义为单纯唯一性（至多一个幂等提升），则即使各层为交换环、$p_n$ 满射且极限核为 $0$（`(D)` 成立），仍有 `(C) + (D) ⇏ (B)`（例如取 $R_n = k[x], S = k \times k, p_n(f) = (f(0), f(1)), \rho_n(f(x)) = f(x^2)$，此时 $L \cong k \xrightarrow{\Delta} k \times k$，$\ker p = 0$，但 $(1,0)$ 无提升；若将“幂等提升唯一”按存在唯一 $\exists!$ 理解，则其平凡蕴含 `(B)`）。
  5. **极限层面的正面蕴含 `（交换 +）(A) 元素提升 + (D) 极限核逐元素幂零 ⟹ (B) 幂等提升 + (C) 幂等提升唯一`**：
     当 $L$ 交换时（S2、S3、S5 设定），直接对满射 $p: L \to S$ 应用 **S1** 即为已证明的蕴含关系，答卷未在极限四性质间予以体现。

### 附：四类性质间蕴含关系核查对照表（将“(C)”区分纯唯一性 $C_{\le 1}$ 与存在唯一 $C_{\exists!}$）

| 待判断蕴含关系（针对 $p: L \to S$） | S1–S5 中的结论状态 | 可核查依据 |
| :--- | :--- | :--- |
| `(交换 +) (D) ⟹ C_{≤1}` | **已证明** | 对 $p: L \to S$ 直接应用 **S1.1**（无需 $p$ 满射）；非交换时 **不成立**（S6.1 常值塔满足 `(A)+(B)+(D)` 但 `C_{≤1}` 假）。 |
| `(交换 +) (A) + (D) ⟹ (B) + C_{∃!}` | **已证明** | 对满射 $p: L \to S$ 直接应用 **S1**。 |
| `(A) + (B) + C_{∃!} ⟹ (D)`（及任一子集 `⟹ (D)`） | **不能推出（反例证伪）** | **S3**：$p: k[[t]] \to k$ 满足 `(A)+(B)+C_{∃!}`，但 $\ker p = tk[[t]]$ 不满足 `(D)`。 |
| `(B) + C_{∃!} + (D) ⟹ (A)`（及任一子集 `⟹ (A)`） | **不能推出（反例证伪）** | **S5**：反例满足 S2 故有 `(B)+C_{∃!}`，且 $\ker p = \{0\}$ 满足 `(D)`，但 $p: L \to S$ 不满射，`(A)` 假。 |
| `(A) ⟹ (B)` 及 `(A) + (B) ⟹ C_{≤1}` | **一般不能推出**（共同逆系设定下 `(B), C_{∃!}` 已由 S2 独立成立） | S4 条件下无幂零核时，常值塔 $\mathbb{Z} \to \mathbb{Z}/6\mathbb{Z}$ 满足 `(A)` 但 `(B)` 假；$k\times k \to k$ 或 S6.1 常值塔满足 `(A)+(B)` 但 `C_{≤1}` 假。 |
| `(B) ⟹ C_{≤1}`；`C_{≤1} + (D) ⟹ (B)` | **一般不能推出**（`C_{∃!} ⟹ (B)` 则平凡成立） | 前者由 S6.1（或 $k\times k \to k$）证伪；后者在不假设各层 nil 核时由 $R_n=k[x]\to k\times k, \rho_n(f(x))=f(x^2)$ 证伪。 |
