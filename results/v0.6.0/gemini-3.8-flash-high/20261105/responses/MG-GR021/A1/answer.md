# 同时分块与二次扩张上的下降

---

### 符号约定与结构预备

设标准正交基为 $e_1,\ldots,e_d$，指标集划分为 $I_1\sqcup\cdots\sqcup I_r$，$|I_i|=n_i$，$\sum_i n_i=d$。$E_i$ 为沿 $I_i$ 的标准对角正交投影阵，满足 $E_i^\mathsf{T}=E_i$，$E_iE_j=\delta_{ij}E_i$，$\sum_{i=1}^r E_i=I_d$。对于任意矩阵 $M\in M_d$，以 $M^{(k,l)}$ 表示位于行块 $I_k$、列块 $I_l$ 的 $n_k\times n_l$ 子块。矩阵 $M$ 与全部 $E_j$ 对易（$[M,E_j]=0$ 对所有 $j$）等价于 $M$ 为严格块对角矩阵，即当 $k\neq l$ 时 $M^{(k,l)}=0$。

对基域 $F=\mathbb Q_2$ 及二次扩张 $K_\mu=\mathbb Q_2(\theta_\mu)$（$\theta_\mu^2=\mu\in\{-1,2\}$），其整数环分别记为 $\mathcal O_F=\mathbb Z_2$ 与 $\mathcal O_\mu=\mathbb Z_2[\theta_\mu]$。记 $d_L=[L:F]\in\{1,2\}$，对 $L=F$ 有 $d_F=1$，对 $L=K_\mu$ 有 $d_{K_\mu}=2$。模 $2^M\mathcal O_L$ 意义下，$\mathcal O_L/2^M\mathcal O_L$ 是阶为 $2^{d_L M}$ 的局部有限环。

---

## 1. 可行性判准、精确基数、空集条件与模 $2^M$ 解的可核验充要条件

### 1.1 谱投影系统与 $\mathscr S_L(A)$ 的本质等价化

设 $A_1,\ldots,A_r\in M_d(\mathbb Z_2)$ 满足 $A_i^\mathsf{T}=A_i$，$A_iA_j=A_jA_i$，$A_i\equiv E_i\pmod 2$。
由交换完全局部环上的 Hensel 幂等元提升定理（Idempotent Lifting Theorem）：
在由对称交换矩阵族 $\{A_i\}$ 生成的完全交换 $\mathbb Z_2$-代数 $\mathcal A=\mathbb Z_2[A_1,\ldots,A_r]$ 中，存在唯一的一组正交对称幂等元 $\Pi_1,\ldots,\Pi_r\in M_d(\mathbb Z_2)$，满足：
1. $\Pi_i^2=\Pi_i=\Pi_i^\mathsf{T}$；
2. $\Pi_i\Pi_j=0\ (\forall i\neq j)$，且 $\sum_{i=1}^r \Pi_i = I_d$；
3. $\Pi_i\equiv E_i\pmod 2$；
4. $\Pi_i$ 与所有 $A_j$ 对易（因 $\Pi_i\in\mathcal A$）。

具体地，$\Pi_i$ 为 $A_i$ 对应于模 $2$ 特征值为 $1$ 的广义特征子空间上的正交谱投影。

**引理 1.1**：对任意 $U\in\operatorname{GL}_d(\mathcal O_L)$，满足 $U^\mathsf{T}U=I_d$ 且 $U\equiv I_d\pmod{2\mathcal O_L}$，下列条件严格等价：
\[
[U^\mathsf{T}A_i U, E_j]=0\quad (\forall i,j=1,\ldots,r)
\quad\Longleftrightarrow\quad
U E_i U^\mathsf{T} = \Pi_i\quad (\forall i=1,\ldots,r).
\]
*证明*：
若 $P_i = U E_i U^\mathsf{T}$，则 $P_i^2=P_i=P_i^\mathsf{T}$，$\sum P_i = I_d$，且 $P_i\equiv E_i\pmod{2\mathcal O_L}$。条件 $[U^\mathsf{T}A_i U, E_j]=0$ 等价于 $[A_i, P_j]=0$ 对所有 $i,j$ 成立。由于 $A_i$ 模 $2$ 具有分离谱（在 $\Pi_i$ 像上模 $2$ 为 $I_{n_i}$，在正交补上为 $0$），任何与 $A_i$ 对易且同余于 $E_i\pmod{2\mathcal O_L}$ 的正交投影在各谱分支上的限制必分别为恒等与零，故由紧致完全环上投影谱分解的唯一性，必有 $P_i=\Pi_i$。反之若 $U E_i U^\mathsf{T}=\Pi_i$，则 $U^\mathsf{T}A_i U$ 与 $E_j=U^\mathsf{T}\Pi_j U$ 的对易性直接由 $A_i$ 与 $\Pi_j$ 的对易性保证。$\square$

因此，矩阵 $U$ 的列块 $U=[U_1\mid\cdots\mid U_r]$（$U_k\in M_{d\times n_k}(\mathcal O_L)$）必须构成各个子格 $\Pi_k(\mathcal O_L^d)$ 的一组标准正交基，且 $U_k\equiv \begin{pmatrix}0\\I_{n_k}\\0\end{pmatrix}\pmod{2\mathcal O_L}$。

### 1.2 有限可算的可行性判准（模 4 明确不变量）

将 $A_k\bmod 4$ 写作：
\[
A_k \equiv E_k + 2 B_k \pmod 4,\qquad B_k\in M_d(\mathbb F_2),\quad B_k^\mathsf{T}=B_k.
\]
由交换性 $A_iA_j\equiv A_jA_i\pmod 4$，可得对于任意互异指标 $i,k,l$：
\[
B_k^{(k,l)} = B_l^{(k,l)} = \left(B_l^{(l,k)}\right)^\mathsf{T},\qquad B_i^{(k,l)} = 0\quad (i\notin\{k,l\}).
\]
记 $B_{kl} = B_k^{(k,l)} \in M_{n_k\times n_l}(\mathbb F_2)$。考虑正交基变换下的 Gram 矩阵：标准基在 $\Pi_k$ 上的投影给出了 $\Pi_k(\mathcal O_L^d)$ 的一组自然基 $\Pi_k E_k$，其 Gram 矩阵为
\[
C_k = E_k \Pi_k E_k \in M_{n_k}(\mathbb Z_2),\qquad C_k\equiv I_{n_k}\pmod 4.
\]
利用恒等式 $\Pi_k^2=\Pi_k$，在模 $8$ 精度下展开可得闭式表达式：
\[
C_k \equiv I_{n_k} + 4 T_k \pmod 8,\qquad T_k = \sum_{l\neq k} B_{kl}B_{kl}^\mathsf{T} \in M_{n_k}(\mathbb F_2).
\]
根据局部整环上的 Witt 定理与二次型同构分类，单模对称阵 $C_k$ 能够分解为 $W_k W_k^\mathsf{T}$（$W_k\equiv I_{n_k}\pmod{2\mathcal O_L}$）当且仅当其行列式为模 $8$ 平方剩余：$\det(C_k)\equiv 1\pmod 8$。由于 $\det(I_{n_k}+4 T_k)\equiv 1+4\operatorname{tr}(T_k)\pmod 8$，该判准完全等价于 $\operatorname{tr}(T_k)\equiv 0\pmod 2$。

**定义 1.2（块奇偶不变量）**：
对每个块 $k\in\{1,\ldots,r\}$，定义
\[
\delta_k(A) := \operatorname{tr}(T_k) = \sum_{l\neq k} \operatorname{tr}(B_{kl}B_{kl}^\mathsf{T}) \equiv \sum_{l\neq k} \sum_{p\in I_k,\, q\in I_l} \frac{(A_k)_{pq}}{2} \pmod 2.
\]
$\delta_k(A)$ 即为 $A_k\bmod 4$ 在第 $k$ 行块的所有非对角块中等于 $2\pmod 4$ 的条目总数模 $2$。
显然 $\sum_{k=1}^r \delta_k(A) = 2\sum_{1\le k<l\le r} \sum_{p\in I_k, q\in I_l} (B_{kl})_{pq} \equiv 0\pmod 2$，故这组不变量包含至多 $r-1$ 个独立的 $\mathbb F_2$-约束。

**定理 1.3（可行性判准）**：
对任意 $L\in\{F,K_{-1},K_2\}$，$\mathscr S_L(A)\neq\emptyset$ 当且仅当：
\[
\delta_k(A) = 0\qquad (\forall k=1,\ldots,r).
\]
该判准对 $L=F, K_{-1}, K_2$ 是统一的，且仅由 $A_1,\ldots,A_r\bmod 4$ 有限判定。

### 1.3 空集条件

- **$\mathscr S_L(A)$ 的空集条件**：
  $\mathscr S_L(A)=\emptyset \iff \exists k\in\{1,\ldots,r\},\ \delta_k(A)=1$。
- **$\mathscr R_{L,M}(A)$ 的空集条件（$\forall M\ge 2$）**：
  $\mathscr R_{L,M}(A)=\emptyset \iff \mathscr S_L(A)=\emptyset \iff \exists k\in\{1,\ldots,r\},\ \delta_k(A)=1$。
- **$\mathscr C_{L,M}(A)$ 的空集条件**：
  - 当 $M\ge 3$ 时，$\mathscr C_{L,M}(A)=\emptyset \iff \exists k\in\{1,\ldots,r\},\ \delta_k(A)=1$。
  - 当 $M=2$ 时，由于模 $4$ 下一阶变形方程 $[B_i+XE_i+E_iX,E_j]=0$ 总有解 $X_{kl}=B_{kl}$（$k\neq l$）且 $X_{kk}$ 可任意选取对称阵，故
    \[
    \mathscr C_{L,2}(A) \neq \emptyset \quad \text{对所有合法输入 } A \text{ 恒成立（永不为空）}.
    \]

### 1.4 $\mathscr R_{L,M}(A)$ 与 $\mathscr C_{L,M}(A)$ 的精确闭式基数

当 $\mathscr S_L(A)\neq\emptyset$ 时，$\mathscr S_L(A)$ 为正交主同质空间（torsor），其对称群为
\[
G_L = \prod_{k=1}^r O_{n_k}(\mathcal O_L, 2\mathcal O_L),\qquad O_n(\mathcal O_L, 2\mathcal O_L)=\{Q\in O_n(\mathcal O_L): Q\equiv I_n\pmod{2\mathcal O_L}\}.
\]
设李代数 $\mathfrak{so}_n$ 的维数为 $\binom{n}{2}$。模 $2^M\mathcal O_L$ 投影环的基数公式为：

**定理 1.4（精确基数）**：
1. **真实投影族 $\mathscr R_{L,M}(A)$**：
   若 $\exists k, \delta_k(A)=1$，则 $|\mathscr R_{L,M}(A)| = 0$（$\forall M\ge 2$）；
   若 $\forall k, \delta_k(A)=0$，则对所有 $M\ge 2$：
   \[
   |\mathscr R_{L,M}(A)| = 2^{r + d_L(M-1)\sum_{k=1}^r \binom{n_k}{2}}.
   \]
   其中 $d_F=1$，$d_{K_\mu}=2$。

2. **模代数族 $\mathscr C_{L,M}(A)$**：
   - 当 $M\ge 3$ 时：
     若 $\exists k, \delta_k(A)=1$，则 $|\mathscr C_{L,M}(A)|=0$；
     若 $\forall k, \delta_k(A)=0$，则
     \[
     |\mathscr C_{L,M}(A)| = 2^{d_L d}\cdot |\mathscr R_{L,M}(A)| = 2^{r + d_L d + d_L(M-1)\sum_{k=1}^r \binom{n_k}{2}}.
     \]
   - 当 $M=2$ 时（对所有输入 $A$，无论可行与否）：
     \[
     |\mathscr C_{L,2}(A)| = 2^{r + d_L(d-r) + d_L\sum_{k=1}^r \binom{n_k}{2}}.
     \]

### 1.5 $\bar U\in\mathscr C_{L,M}(A)$ 属于 $\mathscr R_{L,M}(A)$ 的可核验充要条件

取 $\bar U\in\mathscr C_{L,M}(A)$ 的任意一个整环提升 $U\in M_d(\mathcal O_L)$（即 $U\equiv \bar U\pmod{2^M\mathcal O_L}$）。
$\bar U\in\mathscr R_{L,M}(A)$ 当且仅当：
1. **全局相容性**：$A$ 满足可行性条件，即 $\delta_k(A)=0$ 对所有 $k=1,\ldots,r$ 成立；
2. **局部正交提升阻碍消失**：矩阵 $U^\mathsf{T}U$ 的对角元满足：
   - 若 $M=2$：
     \[
     (U^\mathsf{T}U)_{ii} \equiv 1 \pmod{8\mathcal O_L}\qquad (\forall i=1,\ldots,d).
     \]
   - 若 $M\ge 3$：
     \[
     (U^\mathsf{T}U)_{ii} \equiv 1 \pmod{2^{M+1}\mathcal O_L}\qquad (\forall i=1,\ldots,d).
     \]
*核验说明*：由于对任意扰动 $Y\in M_d(\mathcal O_L)$，$(U+2^M Y)^\mathsf{T}(U+2^M Y)\equiv U^\mathsf{T}U + 2^M(Y+Y^\mathsf{T})\pmod{2^{M+1}}$，而在特征 $2$ 下 $(Y+Y^\mathsf{T})_{ii} = 2Y_{ii}\equiv 0\pmod 2$，故对角线模 $2^{M+1}$（及 $M=2$ 时的模 $8$）的值与提升 $U$ 的具体选取完全无关，是 $\bar U$ 的内在不变量，计算为纯代数有限验证。

---

## 2. 不动点类、轨道分解、层间纤维大小及相容序列刻画

### 2.1 $\sigma_\mu$-不动矩阵类的具体结构与基域关系

设 $\bar U\in M_d(\mathcal O_\mu/2^M\mathcal O_\mu)$ 写为 $\bar U = U_0 + \theta_\mu U_1$，其中 $U_0, U_1\in M_d(\mathbb Z/2^M\mathbb Z)$。
$\sigma_\mu(\bar U)=\bar U \iff 2\theta_\mu U_1 \equiv 0\pmod{2^M\mathcal O_\mu} \iff U_1 \equiv 0\pmod{2^{M-1}}$。
因此必有 $U_1 = 2^{M-1} V_1$，其中 $V_1\in M_d(\mathbb F_2)$。代入正交性与对易性：

**定理 2.1（不动点类精细结构）**：
1. **对模代数族 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$**：
   任意 $\bar U\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 均可唯一分解为：
   \[
   \bar U \equiv U_0 + 2^{M-1}\theta_\mu V_1 \pmod{2^M\mathcal O_\mu},
   \]
   其中 $U_0 \in \mathscr C_{F,M}(A)$，而 $V_1$ 为严格块对角的对称布尔矩阵：
   \[
   V_1 = \operatorname{diag}\left(V_1^{(1)},\ldots,V_1^{(r)}\right),\qquad V_1^{(k)}\in \operatorname{Sym}_{n_k}(\mathbb F_2).
   \]
   因此，存在集合双射：
   \[
   \mathscr C_{K_\mu,M}(A)^{\sigma_\mu} \cong \mathscr C_{F,M}(A) \times \prod_{k=1}^r \operatorname{Sym}_{n_k}(\mathbb F_2).
   \]

2. **对真实投影族 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$**：
   当且仅当 $A$ 可行时非空，此时任意 $\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 具有分解：
   \[
   \bar U \equiv U_0 + 2^{M-1}\theta_\mu V_1 \pmod{2^M\mathcal O_\mu},
   \]
   其中 $U_0 \in \mathscr R_{F,M}(A)$，且 $V_1$ 为严格块对角、**对角元全为 0** 的对称阵（即李代数 $\mathfrak{so}_{n_k}(\mathbb F_2)$）：
   \[
   V_1 = \operatorname{diag}\left(V_1^{(1)},\ldots,V_1^{(r)}\right),\qquad V_1^{(k)}\in \mathfrak{so}_{n_k}(\mathbb F_2)\quad \left((V_1^{(k)})_{ii}=0\right).
   \]
   因此，存在集合双射：
   \[
   \mathscr R_{K_\mu,M}(A)^{\sigma_\mu} \cong \mathscr R_{F,M}(A) \times \prod_{k=1}^r \mathfrak{so}_{n_k}(\mathbb F_2).
   \]

### 2.2 固定点数与 $\langle\sigma_\mu\rangle$ 轨道数

因 $\dim_{\mathbb F_2}\operatorname{Sym}_n(\mathbb F_2)=\binom{n+1}{2}$，$\dim_{\mathbb F_2}\mathfrak{so}_n(\mathbb F_2)=\binom{n}{2}$，可得：

**推论 2.2（固定点数）**：在可行条件下，
\[
|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}| = |\mathscr R_{F,M}(A)|\cdot 2^{\sum_{k=1}^r \binom{n_k}{2}} = 2^{r + M\sum_{k=1}^r \binom{n_k}{2}}.
\]
\[
|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}| =
\begin{cases}
2^{r + d + M\sum_{k=1}^r \binom{n_k}{2}}, & M\ge 3, \\
2^{r + 2(d-r) + 2\sum_{k=1}^r \binom{n_k}{2}}, & M=2.
\end{cases}
\]

**推论 2.3（轨道数）**：
群 $\langle\sigma_\mu\rangle$ 的阶为 $2$，由 Burnside 引理，任何作用集 $X$ 的轨道数为 $N_\text{orb}(X) = \frac{|X|+|X^{\sigma_\mu}|}{2}$。
1. 对 $\mathscr R$：
   \[
   N_\text{orb}(\mathscr R_{K_\mu,M}(A)) = \frac{1}{2}\left( 2^{r + 2(M-1)\sum_{k=1}^r \binom{n_k}{2}} + 2^{r + M\sum_{k=1}^r \binom{n_k}{2}} \right).
   \]
2. 对 $\mathscr C$（$M\ge 3$ 时）：
   \[
   N_\text{orb}(\mathscr C_{K_\mu,M}(A)) = \frac{1}{2}\left( 2^{r + 2d + 2(M-1)\sum_{k=1}^r \binom{n_k}{2}} + 2^{r + d + M\sum_{k=1}^r \binom{n_k}{2}} \right).
   \]

### 2.3 层间约化像与非空纤维大小（从精度 $M+1$ 到 $M$）

考虑自然投影 $\pi_M: X_{M+1} \to X_M$：

1. **真实解投影 $\mathscr R_{K_\mu,M+1}(A) \to \mathscr R_{K_\mu,M}(A)$**：
   - 约化像：全体 $\mathscr R_{K_\mu,M}(A)$（满射）。
   - 全部非空纤维大小恒为：
     \[
     \frac{|\mathscr R_{K_\mu,M+1}(A)|}{|\mathscr R_{K_\mu,M}(A)|} = 4^{\sum_{k=1}^r \binom{n_k}{2}}.
     \]

2. **固定点集投影 $\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu} \to \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$**：
   - 约化像：由于在模 $2^M$ 截断下，$2^M\theta_\mu V_1 \equiv 0\pmod{2^M}$，故虚部系数完全被消去。约化像**严格等于基域解集**：
     \[
     \pi_M\left(\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\right) = \mathscr R_{F,M}(A) \subset \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}.
     \]
   - 纤维情况：
     - 若 $\bar U \in \mathscr R_{K_\mu,M}(A)^{\sigma_\mu} \setminus \mathscr R_{F,M}(A)$（即 $V_1\neq 0$），其纤维为**空集**；
     - 若 $\bar U \in \mathscr R_{F,M}(A)$，其非空纤维大小恒为：
       \[
       |\pi_M^{-1}(\bar U)| = 4^{\sum_{k=1}^r \binom{n_k}{2}}.
       \]

3. **模代数解 $\mathscr C_{K_\mu,M+1}(A) \to \mathscr C_{K_\mu,M}(A)$**：
   - 当 $M\ge 3$ 时为满射，非空纤维大小恒为 $4^{d + \sum_{k=1}^r \binom{n_k}{2}}$；
   - 当 $M=2$ 时，像集为满足 $(U^\mathsf{T}U)_{ii}\equiv 1\pmod{8\mathcal O_\mu}$ 的矩阵类，像集大小为 $2^{r + 2\sum\binom{n_k}{2}}$，非空纤维大小恒为 $4^{d + \sum\binom{n_k}{2}}$。

4. **固定模代数解 $\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu} \to \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$**：
   - 像集严格落入基域模代数集 $\mathscr C_{F,M}(A)$ 内；
   - 对其中的非空点，纤维大小恒为 $2^{\sum_{k=1}^r \binom{n_k}{2} + \sum_{k=1}^r \binom{n_k+1}{2}} = 2^{d + 2\sum_{k=1}^r \binom{n_k}{2}}$。

### 2.4 提升为真正解与相容序列分量的充要刻画

**定理 2.4**：
设 $A$ 可行，$\bar U \in \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$。下列命题严格等价：
1. $\bar U$ 能提升为 $\mathscr S_{K_\mu}(A)$ 中的一个真正 $\sigma_\mu$-固定解（即存在 $W\in\mathscr S_{K_\mu}(A)$ 满足 $\sigma_\mu(W)=W$ 且 $W\equiv \bar U\pmod{2^M\mathcal O_\mu}$）；
2. 存在一条在所有精度相容的固定点列 $(U_k)_{k\ge 2}$（其中 $U_k\in\mathscr R_{K_\mu,k}(A)^{\sigma_\mu}$ 且 $\pi_k(U_{k+1})=U_k$），使得 $U_M = \bar U$；
3. $\bar U$ 能够至少向上单步提升至 $\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}$；
4. $\bar U \in \mathscr R_{F,M}(A)$，即在其分解式 $\bar U=U_0+2^{M-1}\theta_\mu V_1$ 中必有 $V_1 = 0$。

*证明*：
因为固定解环的真正固定子代数为 $\mathcal O_\mu^{\sigma_\mu}=\mathbb Z_2=\mathcal O_F$，任何真正的 $\sigma_\mu$-固定解必满足 $W\in\mathscr S_F(A)$，故 $W\bmod 2^M \in \mathscr R_{F,M}(A)$，必然有 $V_1=0$。
另一方面，逆向极限 $\varprojlim_k \mathscr R_{K_\mu,k}(A)^{\sigma_\mu} = \varprojlim_k \mathscr R_{F,k}(A) = \mathscr S_F(A)$。若 $V_1\neq 0$，则由 2.3 节可知，$\bar U$ 在 $M+1$ 阶下的原像已然为空，连单步都无法提升。因此“能单步提升”、“能形成相容序列”与“能提升为真正解”三者在外延上完全重合，且完全等价于 $V_1=0$。$\square$

---

## 3. 下降精度的界、精确下降条件与最优性证明

### 3.1 最大下降精度 $N$

**定理 3.1（最大下降精度）**：
固定块秩 $n_1,\ldots,n_r$、$\mu\in\{-1,2\}$ 与 $M\ge 2$。对所有合法输入 $A$ 及满足 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$ 的 $U\in\mathscr S_{K_\mu}(A)$，均存在 $W\in\mathscr S_F(A)$ 使 $U\equiv W\pmod{2^N\mathcal O_\mu}$ 的最大整数 $N$ 为：
\[
N =
\begin{cases}
M, & \text{若 } n_1 = n_2 = \cdots = n_r = 1 \quad \left(\text{即 } \sum_{k=1}^r \binom{n_k}{2} = 0\right), \\
M - 1, & \text{若存在某 } n_k \ge 2 \quad \left(\text{即 } \sum_{k=1}^r \binom{n_k}{2} \ge 1\right).
\end{cases}
\]

### 3.2 允许精确下降（$N=M$ 恒成立）的块秩结构

**精确下降判准**：
系统允许精确下降（即无论选取何种 $A$ 与 $U$，均能达到 $N=M$）的充要条件是：
\[
n_1 = n_2 = \cdots = n_r = 1.
\]
*证明*：
若每个块大小均为 $1$，则 $d=r$。正交群主同质空间 $G_L = \prod_{k=1}^d O_1(\mathcal O_L, 2\mathcal O_L)$。而 $O_1(\mathcal O_L, 2\mathcal O_L) = \{u\in \mathcal O_L^\times : u^2=1,\ u\equiv 1\pmod{2\mathcal O_L}\}$。
在局部域 $K_\mu$ 中，二次多项式 $X^2-1=0$ 仅有两个根 $\pm 1$。由于 $\pm 1\in\mathbb Z_2$，无论在 $F$ 还是在 $K_\mu$ 上，均有
\[
O_1(\mathcal O_\mu, 2\mathcal O_\mu) = \{+1, -1\} = O_1(\mathbb Z_2, 2\mathbb Z_2).
\]
因此 $\mathscr S_{K_\mu}(A) = \mathscr S_F(A)$，任何解 $U$ 本身就是基域上的真正解。直接取 $W=U\in\mathscr S_F(A)$ 即可保证 $U=W$ 在精确意义下成立，故恒有 $N=M$。$\square$

### 3.3 给定 $(A, U)$ 下取 $N=M$ 的充要条件

**定理 3.2（个体系数判定）**：
设给定合法的 $A$ 以及满足 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$ 的 $U\in\mathscr S_{K_\mu}(A)$。
能够选取 $W\in\mathscr S_F(A)$ 满足 $U\equiv W\pmod{2^M\mathcal O_\mu}$ 的充要条件是：
\[
\sigma_\mu(U) \equiv U \pmod{2^{M+1}\mathcal O_\mu},
\]
或等价地，$U\bmod 2^M\mathcal O_\mu \in M_d(\mathbb Z/2^M\mathbb Z)$（即 $U\bmod 2^M\mathcal O_\mu$ 的虚部条目全为 $0$）。

*证明*：
设 $U = U_0 + \theta_\mu U_1$（$U_0, U_1\in M_d(\mathbb Z_2)$）。
条件 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$ 给出 $2U_1\equiv 0\pmod{2^M}$，即 $U_1 = 2^{M-1}V_1$。
- **必要性**：若存在 $W\in\mathscr S_F(A)$ 使 $U\equiv W\pmod{2^M\mathcal O_\mu}$，则由于 $W$ 的矩阵元全在 $\mathbb Z_2$ 中，有
  \[
  U - W \equiv (U_0 - W) + 2^{M-1}\theta_\mu V_1 \equiv 0 \pmod{2^M\mathcal O_\mu}.
  \]
  由于 $\mathcal O_\mu$ 为自由 $\mathbb Z_2$-模，这迫使 $2^{M-1}V_1\equiv 0\pmod{2^M}$，即 $V_1\equiv 0\pmod 2$。
  由此推得 $U_1\equiv 0\pmod{2^M}$，从而 $-2\theta_\mu U_1 \equiv 0\pmod{2^{M+1}\mathcal O_\mu}$，即 $\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$。
- **充分性**：若 $\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$，则 $U_1\equiv 0\pmod{2^M}$。
  此时 $\bar U \equiv U_0 \pmod{2^M\mathcal O_\mu}$ 落入基域中。根据定理 2.1 与定理 2.4，因为其模 $2^M$ 虚部 $V_1=0$，该矩阵类直接属于 $\mathscr R_{F,M}(A)$，故必存在 $W\in\mathscr S_F(A)$ 满足 $W\equiv U_0\equiv U\pmod{2^M\mathcal O_\mu}$。$\square$

### 3.4 界 $N=M-1$ 的最优性证明与统一构造

当存在某个块秩 $n_k\ge 2$ 时，不失一般性，设第一块 $n_1\ge 2$。
我们构造反例族证明：对任意给定的 $M\ge 2$ 与 $\mu\in\{-1,2\}$，均存在合法矩阵族 $A$ 及解 $U\in\mathscr S_{K_\mu}(A)$，满足 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$，但对任意 $W\in\mathscr S_F(A)$，均有 $U\not\equiv W\pmod{2^M\mathcal O_\mu}$。

#### 统一构造：
取 $A_i = E_i$（$\forall i=1,\ldots,r$）。此时 $A_i$ 满足全部合法条件，且 $\mathscr S_L(A) = \prod_{k=1}^r O_{n_k}(\mathcal O_L, 2\mathcal O_L)$。
我们只需在第一块的前两个坐标对应之 $2\times 2$ 主子块上构造正交阵 $Q\in O_2(\mathcal O_\mu, 2\mathcal O_\mu)$，再在其余坐标补恒等阵：$U = \operatorname{diag}(Q, I_{d-2})$。

利用李代数 $\mathfrak{so}_2(\mathcal O_\mu)$ 上的 Cayley 变换或代数正交形式：
设 $Q = \begin{pmatrix} c & -s \\ s & c \end{pmatrix}$，满足 $c^2+s^2=1$，$c\equiv 1\pmod{2\mathcal O_\mu}$，$s\equiv 0\pmod{2\mathcal O_\mu}$。

1. **情形一：$M\ge 3$（任意精度统一构造）**
   取反对称形变参数 $t = 2^{M-2}\theta_\mu \in 2\mathcal O_\mu$。
   由于 $M\ge 3$，$t^2 = 2^{2M-4}\mu$。注意到 $2M-4 \ge 2$，故 $t^2 \in 4\mathbb Z_2$。
   因此 $1+t^2 \equiv 1\pmod 4$ 是 $\mathcal O_\mu$ 中的可逆元。
   取 Cayley 变换阵：
   \[
   Q = (I - T)(I + T)^{-1},\qquad T = \begin{pmatrix} 0 & -t \\ t & 0 \end{pmatrix}.
   \]
   其矩阵元为：
   \[
   c = \frac{1-t^2}{1+t^2},\qquad s = \frac{2t}{1+t^2}.
   \]
   - 正交性：恒有 $c^2+s^2=1$，故 $Q\in O_2(\mathcal O_\mu)$；
   - 模 $2$ 恒等：$c\equiv 1\pmod{2\mathcal O_\mu}$，$s\equiv 2t\equiv 0\pmod{2\mathcal O_\mu}$；
   - 近似固定性：
     \[
     s = \frac{2^{M-1}\theta_\mu}{1 + 2^{2M-4}\mu} \equiv 2^{M-1}\theta_\mu \pmod{2^M\mathcal O_\mu},
     \]
     \[
     \sigma_\mu(s) \equiv -2^{M-1}\theta_\mu \equiv 2^{M-1}\theta_\mu \equiv s \pmod{2^M\mathcal O_\mu}.
     \]
     因此 $\sigma_\mu(Q)\equiv Q\pmod{2^M\mathcal O_\mu}$。
   - 无法达到精度 $M$：
     $s\bmod 2^M\mathcal O_\mu$ 的 $\theta_\mu$ 虚部条目为 $2^{M-1}\not\equiv 0\pmod{2^M}$。若存在 $W\in\mathscr S_F(A)$，则 $W$ 为实整矩阵，其 $(2,1)$ 条目之虚部为 $0$。因 $2^{M-1}\not\equiv 0\pmod{2^M}$，必有
     \[
     Q \not\equiv W \pmod{2^M\mathcal O_\mu}.
     \]

2. **情形二：$M=2$（模 4 精度具体实例）**
   - 当 $\mu = 2$ 时：
     取 $s = 2\sqrt{2}$。则 $1-s^2 = 1 - 8 = -7 \equiv 1\pmod 8$。
     由 $\mathbb Z_2$ 上的 Hensel 引理，$-7$ 在 $\mathbb Z_2$ 中存在严格平方根，取 $c = \sqrt{-7}\equiv 1\pmod 4$。
     此时 $Q = \begin{pmatrix} c & -2\sqrt{2} \\ 2\sqrt{2} & c \end{pmatrix} \in O_2(\mathcal O_2, 2\mathcal O_2)$。
     检验得 $\sigma_2(s) = -2\sqrt{2} \equiv 2\sqrt{2} = s \pmod{4\mathcal O_2}$（因差为 $4\sqrt{2}\in 4\mathcal O_2$）。
     但 $s\bmod 4\mathcal O_2 = 2\sqrt{2}\neq 0$，基域正交矩阵的非对角元在模 $4$ 下必为 $0$ 或纯实整数，故不存在任何 $W\in O_2(\mathbb Z_2)$ 使得 $Q\equiv W\pmod{4\mathcal O_2}$。
   - 当 $\mu = -1$ 时：
     取 $s = 2(1 + \theta_{-1}) = 2(1+i)$。
     则 $s^2 = 4(1+i)^2 = 8i$。
     故 $1-s^2 = 1 - 8i \equiv 1\pmod 8$。
     由于 $1-8i\in 1+8\mathcal O_{-1}$，由 $\mathcal O_{-1}=\mathbb Z_2[i]$ 上的 Hensel 引理，存在 $c = \sqrt{1-8i}\in\mathcal O_{-1}$ 满足 $c\equiv 1\pmod 4$。
     此时 $Q = \begin{pmatrix} c & -s \\ s & c \end{pmatrix} \in O_2(\mathcal O_{-1}, 2\mathcal O_{-1})$。
     检验得 $\sigma_{-1}(s) - s = 2(1-i) - 2(1+i) = -4i \equiv 0\pmod{4\mathcal O_{-1}}$。
     故 $\sigma_{-1}(Q)\equiv Q\pmod{4\mathcal O_{-1}}$。
     但其非对角元 $s \equiv 2 + 2i \pmod{4\mathcal O_{-1}}$ 含有非零虚部 $2i$，而任何基域矩阵 $W\in O_2(\mathbb Z_2)$ 均无虚部，故 $Q\not\equiv W\pmod{4\mathcal O_{-1}}$。

以上构造严格排除了 $N=M$ 的可能性，从而确立了在存在 $n_k\ge 2$ 时界 $N=M-1$ 的精确性与不可改进性。
