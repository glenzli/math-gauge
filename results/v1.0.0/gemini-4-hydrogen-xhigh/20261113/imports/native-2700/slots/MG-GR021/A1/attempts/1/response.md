以下给出全部三个目标的完整解答与证明。文中结构清晰地分为“基础准备与正交幂等分解”“目标 1”“目标 2”与“目标 3”四个部分。

---

### 一、局部域性质与标准定理的精确引用

首先列出下文援引的两条标准局部域定理及在本题中的适用条件验证：

1. **Eisenstein 扩张与整数环结构定理**（如 Serre, *Local Fields*, Ch. I, §6, Prop. 17；Neukirch, *Algebraic Number Theory*, Ch. II, §6）：
   若 $K=F(\pi)$ 由 $F$ 上首一 Eisenstein 多项式 $f(x)\in\mathcal O_F[x]$ 定义（即非常数首一多项式，除首项外其余系数均属 $\mathfrak m_F$，且常数项属 $\mathfrak m_F\setminus \mathfrak m_F^2$），则 $K/F$ 为完全分歧扩张，其整数环为 $\mathcal O_K=\mathcal O_F[\pi]$，且 $\pi$ 为 $\mathcal O_K$ 的素元（一致化子），满足 $\mathfrak m_K=\pi\mathcal O_K$、剩余域同构 $\mathcal O_K/\pi\mathcal O_K\cong\mathcal O_F/\mathfrak m_F$ 与 $v_\pi(p_F)=[K:F]$。
   - **在本题中的验证**：对 $F=\mathbb Q_2$（$\mathcal O_F=\mathbb Z_2$，$\mathfrak m_F=2\mathbb Z_2$）：
     - $\mu=2$ 时，取 $\pi_2=\theta_2$，其极小多项式 $x^2-2\in\mathbb Z_2[x]$ 为 $2$-Eisenstein 多项式。故 $\mathcal O_2=\mathbb Z_2[\theta_2]$ 是完备离散赋值环（DVR），一致化子为 $\pi_2=\theta_2$，剩余域为 $\mathbb F_2$，且 $2\mathcal O_2=\pi_2^2\mathcal O_2$（$v_{\pi_2}(2)=2$）。
     - $\mu=-1$ 时，取 $\pi_{-1}=1+\theta_{-1}$，其极小多项式 $(x-1)^2+1=x^2-2x+2\in\mathbb Z_2[x]$ 为 $2$-Eisenstein 多项式。故 $\mathcal O_{-1}=\mathbb Z_2[\pi_{-1}]=\mathbb Z_2[\theta_{-1}]$ 是完备 DVR，一致化子为 $\pi_{-1}=1+\theta_{-1}$，剩余域为 $\mathbb F_2$，且 $\pi_{-1}^2=2\theta_{-1}$ 与 $\theta_{-1}\in\mathcal O_{-1}^\times$ 给出 $2\mathcal O_{-1}=\pi_{-1}^2\mathcal O_{-1}$（$v_{\pi_{-1}}(2)=2$）。
   - 对 $L\in\{F,K_{-1},K_2\}$，记分歧次数 $e_L=[L:F]\in\{1,2\}$（$e_F=1,e_{K_{-1}}=e_{K_2}=2$）。注意 $\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu$ 是秩 $2$ 自由 $\mathbb Z_2$-模，故 $2^k\mathcal O_\mu=2^k\mathbb Z_2\oplus 2^k\theta_\mu\mathbb Z_2$，且对任意 $k\ge1$，
     $$|\mathcal O_L/2^k\mathcal O_L|=2^{e_L k},\qquad \mathbb Z/2^k\mathbb Z\hookrightarrow \mathcal O_\mu/2^k\mathcal O_\mu\text{ 为单同态}.$$
     （从而基域有限集合自然单射包含于扩域集合中。）

2. **完备赋值环上的一般 Hensel 引理**（多赋值形式，如 Neukirch, Ch. II, §4, Lem. 4.6；Eisenbud, *Commutative Algebra*, Thm. 7.3）：
   设 $(R,v)$ 为完备离散赋值环，$f(X)\in R[X]$。若存在 $x_0\in R$ 使 $f'(x_0)\ne0$ 且 $v(f(x_0))>2v(f'(x_0))$，则存在唯一的 $x\in R$ 满足 $f(x)=0$ 与 $v(x-x_0)\ge v(f(x_0))-v(f'(x_0))$。
   - **在本题中的验证**：
     - 对 $R=\mathbb Z_2$（$v=v_2$）与 $u\in 1+8\mathbb Z_2$，$f(X)=X^2-u$，$x_0=1$ 有 $v_2(f(1))=v_2(1-u)\ge 3>2=2v_2(2)=2v_2(f'(1))$，故存在唯一 $\sqrt u\in 1+4\mathbb Z_2$ 使 $(\sqrt u)^2=u$；更一般地，若 $u\equiv 1\pmod{2^k}$ ($k\ge 3$)，则 $\sqrt u\equiv 1\pmod{2^{k-1}}$。
     - 对 $R=\mathcal O_{-1}$（$v=v_{\pi_{-1}}$）与 $f(X)=X^2-(1-8\theta_{-1})$，$x_0=1$ 有 $v_{\pi_{-1}}(f(1))=v_{\pi_{-1}}(8\theta_{-1})=6>4=2\cdot 2=2v_{\pi_{-1}}(f'(1))$，故存在唯一 $a\in\mathcal O_{-1}$ 满足 $a^2=1-8\theta_{-1}$ 与 $v_{\pi_{-1}}(a-1)\ge 6-2=4$，即 $a\equiv 1\pmod{4\mathcal O_{-1}}$。

此外，由于 $\mathcal O_L$ 对 $2$-进拓扑完备且 Hausdorff（$\mathcal O_L\cong\varprojlim_m \mathcal O_L/2^m\mathcal O_L$），矩阵空间 $M_d(\mathcal O_L)$ 亦对 $2$-进拓扑完备且 Hausdorff。

---

### 二、核心结构约化：对称正交幂等分解与块约化

固定 $A=(A_1,\dots,A_r)$ 满足题设。记 $J_i\in M_{d\times n_i}(\mathbb Z_2)$ 为标准坐标包含 $\mathbb Z_2^{I_i}\hookrightarrow\mathbb Z_2^d$ 的矩阵，则 $J_i^{\mathsf T}J_j=\delta_{ij}I_{n_i}$，$J_iJ_i^{\mathsf T}=E_i$，$\sum_{i=1}^r E_i=I_d$。

#### 引理 1（$\mathbb Z_2$ 上的对称正交幂等提升）
对每个 $i=1,\dots,r$，递推定义多项式序列 $X_{i,0}=A_i$，$X_{i,k+1}=3X_{i,k}^2-2X_{i,k}^3\in\mathbb Z[A_i]$。则 $2$-进极限 $P_i=\lim_{k\to\infty}X_{i,k}\in M_d(\mathbb Z_2)$ 存在，且满足：
1. $P_i^2=P_i$，$P_i^{\mathsf T}=P_i$，$P_iP_j=\delta_{ij}P_i$，$\sum_{i=1}^r P_i=I_d$；
2. $P_i\equiv E_i\pmod 2$，且 $P_i\equiv X_{i,k}\pmod{2^{2^k}M_d(\mathbb Z_2)}$（特别地，$P_i\equiv 3A_i^2-2A_i^3\pmod 4$）；
3. 对一切 $i,j$ 有 $P_iA_j=A_jP_i$。

**证明**：对任意交换元素 $X$，置 $Y=X^2-X$，直接展开有
$$(3X^2-2X^3)-(X+(1-2X)Y)=0,\qquad (3X^2-2X^3)^2-(3X^2-2X^3)=Y^2(4Y-3).$$
由 $X_{i,0}=A_i\equiv E_i\pmod 2$ 及 $E_i^2=E_i$，知 $X_{i,0}^2-X_{i,0}\in 2M_d(\mathbb Z_2)$。归纳得 $X_{i,k}^2-X_{i,k}\in 2^{2^k}M_d(\mathbb Z_2)$ 与 $X_{i,k+1}-X_{i,k}=(1-2X_{i,k})(X_{i,k}^2-X_{i,k})\in 2^{2^k}M_d(\mathbb Z_2)$。因 $M_d(\mathbb Z_2)$ $2$-进完备，极限 $P_i=\lim_{k\to\infty}X_{i,k}$ 存在且 $P_i-X_{i,k}\in 2^{2^k}M_d(\mathbb Z_2)$。连续性给出 $P_i^2=P_i$、$P_i^{\mathsf T}=P_i$（因 $A_i^{\mathsf T}=A_i$）、$P_iA_j=A_jP_i$（因 $A_iA_j=A_jA_i$）与 $P_iP_j=P_jP_i$，且 $P_i\equiv A_i\equiv E_i\pmod 2$。

对 $i\ne j$，$Q:=P_iP_j$ 满足 $Q^2=Q$ 且 $Q\equiv E_iE_j=0\pmod 2$。故 $\det(I_d-Q)\equiv 1\pmod 2$ 为单位，$I_d-Q\in\operatorname{GL}_d(\mathbb Z_2)$，从而 $(I_d-Q)Q=0\implies P_iP_j=0$。类似地，$S:=\sum_{i=1}^r P_i$ 满足 $S^2=S$ 与 $S\equiv \sum_{i=1}^r E_i=I_d\pmod 2$，于是 $I_d-S$ 是同余 $0\pmod 2$ 的幂等元，必有 $I_d-S=0$，即 $\sum_{i=1}^r P_i=I_d$。$\square$

#### 引理 2（分块条件与幂等共轭的等价性及 Gram 矩阵约化）
设 $R$ 为 $\mathcal O_L$ 或 $\mathcal O_L/2^M\mathcal O_L$（$M\ge 2$，$L\in\{F,K_{-1},K_2\}$）。
1. 对 $U\in M_d(R)$ 满足 $U\equiv I_d\pmod{2R}$ 与 $U^{\mathsf T}U=I_d$（自动有 $U\in\operatorname{GL}_d(R)$，$U^{-1}=U^{\mathsf T}$），下述两条件等价：
   $$[U^{\mathsf T}A_iU,E_j]=0\ (\forall i,j) \iff U^{\mathsf T}P_iU=E_i\ (\forall i=1,\dots,r).$$
2. 置 $B_i:=P_iJ_i\in M_{d\times n_i}(\mathbb Z_2)$，$G_i:=J_i^{\mathsf T}P_iJ_i=B_i^{\mathsf T}B_i\in M_{n_i}(\mathbb Z_2)$，并定义矩阵 $B:=\sum_{i=1}^r P_iE_i=[B_1\mid\cdots\mid B_r]\in M_d(\mathbb Z_2)$。则：
   - $B\equiv I_d\pmod 2$（故 $B\in\operatorname{GL}_d(\mathbb Z_2)$），且 $B^{\mathsf T}B=\operatorname{diag}(G_1,\dots,G_r)$；
   - $G_i^{\mathsf T}=G_i$ 且 $G_i\equiv I_{n_i}\pmod 4$；
   - 映射
     $$(C_1,\dots,C_r)\longmapsto U=B\operatorname{diag}(C_1,\dots,C_r)=\sum_{i=1}^r B_iC_iJ_i^{\mathsf T}$$
     （其逆映射为 $U\mapsto (G_1^{-1}B_1^{\mathsf T}UJ_1,\dots,G_r^{-1}B_r^{\mathsf T}UJ_r)$）给出 $\sigma_\mu$-等变双射（并与模约化兼容）：
     $$\prod_{i=1}^r \mathscr S_L^{(n_i)}(G_i)\xrightarrow{\ \sim\ }\mathscr S_L(A),\qquad \prod_{i=1}^r \mathscr C_{L,M}^{(n_i)}(G_i)\xrightarrow{\ \sim\ }\mathscr C_{L,M}(A),$$
     其中
     $$\mathscr S_L^{(n)}(G)=\{C\in M_n(\mathcal O_L):C\equiv I_n\pmod{2\mathcal O_L},\ C^{\mathsf T}GC=I_n\},$$
     $$\mathscr C_{L,M}^{(n)}(G)=\{\bar C\in M_n(\mathcal O_L/2^M\mathcal O_L):\bar C\equiv I_n\pmod{2\mathcal O_L},\ \bar C^{\mathsf T}G\bar C=I_n\}.$$

**证明**：
(1) 若 $[U^{\mathsf T}A_iU,E_j]=0$ 对一切 $i,j$ 成立：当 $R=\mathcal O_L$ 时，$U^{\mathsf T}P_iU=\lim_{k\to\infty}X_{i,k}(U^{\mathsf T}A_iU)$；当 $R=\mathcal O_L/2^M\mathcal O_L$ 时，取 $k$ 使 $2^k\ge M$，则 $P_i\equiv X_{i,k}(A_i)\pmod{2^M}$，故 $U^{\mathsf T}P_iU=X_{i,k}(U^{\mathsf T}A_iU)$。两情形下 $Q_i:=U^{\mathsf T}P_iU$ 均与所有 $E_j$ 交换，且 $Q_i^2=Q_i$、$Q_i\equiv E_i\pmod{2R}$。于是 $Q_i=\sum_{j=1}^r E_jQ_iE_j$。对 $j\ne i$，$E_jQ_iE_j$ 是模 $2R$ 为 $0$ 的幂等元，而 $R$ 是局部环且 $2R\subseteq\mathfrak m_R$，故 $I_d-E_jQ_iE_j\equiv I_d\pmod{2R}$ 可逆，得 $E_jQ_iE_j=0$。同理 $E_i-E_iQ_iE_i$ 是模 $2R$ 为 $0$ 的幂等元，故 $E_iQ_iE_i=E_i$，从而 $Q_i=E_i$。

反之，若 $U^{\mathsf T}P_iU=E_i$（$\forall i$），由于 $[A_j,P_i]=0$ 且 $U^{\mathsf T}=U^{-1}$，故 $[U^{\mathsf T}A_jU,E_i]=U^{\mathsf T}[A_j,P_i]U=0$。

(2) 因 $P_i\equiv E_i\pmod 2$，有 $B=\sum_i P_iE_i\equiv\sum_i E_i=I_d\pmod 2$，且 $B_i^{\mathsf T}B_j=J_i^{\mathsf T}P_iP_jJ_j=\delta_{ij}G_i$，故 $B^{\mathsf T}B=\operatorname{diag}(G_1,\dots,G_r)$。又令 $H_i=(I_d-E_i)P_iJ_i=2\tilde H_i$（$\tilde H_i\in M_{d\times n_i}(\mathbb Z_2)$），则 $B_i=J_iG_i+2\tilde H_i$ 且 $J_i^{\mathsf T}\tilde H_i=0$，因此
$$G_i=B_i^{\mathsf T}B_i=G_i^2+4\tilde H_i^{\mathsf T}\tilde H_i.$$
写 $G_i=I_{n_i}+2K_i$，则 $G_i-G_i^2=-2K_i-4K_i^2\in 4M_{n_i}(\mathbb Z_2)\implies K_i\equiv 0\pmod 2$，即 $G_i\equiv I_{n_i}\pmod 4$。

对于 $U=\sum_i B_iC_iJ_i^{\mathsf T}=B\operatorname{diag}(C_1,\dots,C_r)$：
- 总有 $P_iU=B_iC_iJ_i^{\mathsf T}=UE_i$（即 $U^{\mathsf T}P_iU=E_i$ 当 $U^{\mathsf T}U=I_d$ 时）；
- $U^{\mathsf T}U=\operatorname{diag}(C_1^{\mathsf T}G_1C_1,\dots,C_r^{\mathsf T}G_rC_r)$，故 $U^{\mathsf T}U=I_d\iff C_i^{\mathsf T}G_iC_i=I_{n_i}\ (\forall i)$；
- 因 $B\equiv I_d\pmod 2$，故 $U\equiv \operatorname{diag}(C_1,\dots,C_r)\pmod{2R}$，从而 $U\equiv I_d\pmod{2R}\iff C_i\equiv I_{n_i}\pmod{2R}\ (\forall i)$。
反之若 $U^{\mathsf T}P_iU=E_i$，由 $P_iU_i=U_i$（其中 $U_i=UJ_i$）及 $P_i\mathbb Z_2^d$ 以 $B_i$ 列为基（因 $B_i^{\mathsf T}B_i=G_i\in\operatorname{GL}_{n_i}(\mathbb Z_2)$），实际上由 $B^{-1}U=\operatorname{diag}(C_1,\dots,C_r)$（因 $E_j(B^{-1}U)E_k=G_j^{-1}B_j^{\mathsf T}P_jUE_k=G_j^{-1}B_j^{\mathsf T}UE_jE_k=0$ 对 $j\ne k$），其中 $C_i=G_i^{-1}B_i^{\mathsf T}UJ_i$。因 $B,G_i,J_i$ 均定义在 $\mathbb Z_2$ 上，上述双射完全 $\sigma_\mu$-等变，且保持模 $2^N\mathcal O_L$ 同余。$\square$

---

### 三、目标 1：可行性判准、基数闭式、空集条件与提升判准

#### 1.1 $\mathscr S_L(A)$ 的可行性判准（仅由 $A_i\bmod 4$ 计算）

对每个 $i=1,\dots,r$，因 $A_i\equiv E_i\pmod 2$，对所有 $\ell\notin I_i,\ k\in I_i$ 均有 $(A_i)_{\ell,k}\in 2\mathbb Z_2$，从而
$$s_i(A):=\sum_{\ell\notin I_i,\ k\in I_i}\frac{(A_i)_{\ell,k}}{2}\bmod 2\in\mathbb F_2$$
（即 $(I_d-E_i)A_iE_i\bmod 4$ 中等于 $2\pmod 4$ 的元素个数的奇偶性）完全由 $A_i\bmod 4$ 有限确定。

**定理 1（可行性判准）**：对任意合法输入 $A$ 与任意 $L\in\{F,K_{-1},K_2\}$，
$$\mathscr S_L(A)\ne\emptyset\iff s_i(A)=0\quad(\forall i=1,\dots,r)\iff \det(G_i)\equiv 1\pmod 8\quad(\forall i=1,\dots,r).$$
特别地，$\mathscr S_F(A)\ne\emptyset\iff \mathscr S_{K_{-1}}(A)\ne\emptyset\iff \mathscr S_{K_2}(A)\ne\emptyset$。

**证明**：
先计算 $\det(G_i)\bmod 8$。由引理 1，写 $A_i=E_i+2W_i$，则
$$A_i^2\equiv E_i+2(E_iW_i+W_iE_i)\pmod 4,\qquad 2A_i^3\equiv 2E_i^3=2E_i\pmod 4,$$
故
$$P_i\equiv 3A_i^2-2A_i^3\equiv E_i+2(E_iW_i+W_iE_i)\pmod 4.$$
左乘 $I_d-E_i$、右乘 $J_i$ 得
$$2\tilde H_i=(I_d-E_i)P_iJ_i\equiv 2(I_d-E_i)W_iJ_i=(I_d-E_i)A_iJ_i\pmod 4,$$
故 $\tilde H_i\equiv (I_d-E_i)W_iJ_i\pmod 2$。再由引理 2 证明中的恒等式 $G_i-G_i^2=4\tilde H_i^{\mathsf T}\tilde H_i$，写 $G_i=I_{n_i}+4L_i$，有
$$-4L_i-16L_i^2=4\tilde H_i^{\mathsf T}\tilde H_i\implies L_i\equiv \tilde H_i^{\mathsf T}\tilde H_i\pmod 2.$$
从而
$$\det(G_i)=\det(I_{n_i}+4L_i)\equiv 1+4\operatorname{tr}(L_i)\equiv 1+4\operatorname{tr}(\tilde H_i^{\mathsf T}\tilde H_i)=1+4\sum_{\ell\notin I_i,\ k\in I_i}\left(\frac{(A_i)_{\ell,k}}{2}\right)^2\equiv 1+4s_i(A)\pmod 8,$$
因为 $x^2\equiv x\pmod 2$。因此 $\det(G_i)\equiv 1\pmod 8\iff s_i(A)=0$。

**必要性**（且证明当某个 $s_i(A)=1$ 时对一切 $M\ge 3$ 均有 $\mathscr C_{L,M}(A)=\emptyset$）：
若 $\mathscr C_{L,M}(A)\ne\emptyset$（$M\ge 3$），或 $\mathscr S_L(A)\ne\emptyset$（约化模 $8\mathcal O_L$ 得 $\mathscr C_{L,3}(A)\ne\emptyset$），则对每个 $i$ 存在 $\bar C_i\in \mathscr C_{L,3}^{(n_i)}(G_i)$。设 $\widehat C_i\in M_{n_i}(\mathcal O_L)$ 为 $\bar C_i$ 的任一提升，则 $\det(\widehat C_i)=1+2y$（$y\in\mathcal O_L$），且
$$\det(\widehat C_i)^2\det(G_i)=\det(\widehat C_i^{\mathsf T}G_i\widehat C_i)\equiv 1\pmod{8\mathcal O_L}.$$
而 $\det(\widehat C_i)^2=1+4(y^2+y)$。因 $\mathcal O_L/\mathfrak m_L\cong\mathbb F_2$，有 $y(y+1)\in\mathfrak m_L$。若 $s_i(A)=1$ 即 $\det(G_i)\equiv 5\pmod 8$，则 $(1+4(y^2+y))(1+4)\equiv 1+4(y^2+y+1)\pmod{8\mathcal O_L}$；要使其模 $8\mathcal O_L$ 为 $1$，需 $y^2+y+1\in 2\mathcal O_L\subseteq\mathfrak m_L$，与 $y^2+y\in\mathfrak m_L$ 矛盾！故必有 $s_i(A)=0$（$\forall i$）。

**充分性**：设 $s_i(A)=0$ 即 $\det(G_i)\equiv 1\pmod 8$ 对所有 $i$ 成立。只需对每个 $i$ 构造 $C_i\in\mathscr S_F^{(n_i)}(G_i)$（因 $\mathscr S_F\subseteq \mathscr S_{K_\mu}$）。省略下标 $i$，设 $G\in M_n(\mathbb Z_2)$ 对称、$G\equiv I_n\pmod 4$、$\det(G)\equiv 1\pmod 8$。
1. **对称消元对角化**：对 $n$ 归纳。当 $n\ge 2$，写 $G=\begin{pmatrix} u & v^{\mathsf T}\\ v & G'\end{pmatrix}$，$u\in 1+4\mathbb Z_2$，$v\in 4\mathbb Z_2^{n-1}$。取 $R_1=\begin{pmatrix} 1 & -u^{-1}v^{\mathsf T}\\ 0 & I_{n-1}\end{pmatrix}\equiv I_n\pmod 4$，则 $R_1^{\mathsf T}GR_1=\begin{pmatrix} u & 0\\ 0 & G'-u^{-1}vv^{\mathsf T}\end{pmatrix}$ 且 $G'-u^{-1}vv^{\mathsf T}\equiv G'\equiv I_{n-1}\pmod 4$。归纳即得 $R\in\operatorname{GL}_n(\mathbb Z_2)$，$R\equiv I_n\pmod 4$，使 $R^{\mathsf T}GR=\operatorname{diag}(u_1,\dots,u_n)$，各 $u_k\equiv 1\pmod 4$。由 $\det(R)\equiv 1\pmod 4$ 得 $\prod_{k=1}^n u_k=\det(R)^2\det(G)\equiv 1\pmod 8$。
2. **局部平方根与 $2\times 2$ 消去**：各 $u_k\equiv 1$ 或 $5\pmod 8$，由乘积 $\equiv 1\pmod 8$ 知满足 $u_k\equiv 5\pmod 8$ 的下标数为偶数。
   - 若 $u_k\equiv 1\pmod 8$，由 Hensel 引理存在 $w_k=\sqrt{u_k}\in 1+4\mathbb Z_2$，取 $1\times 1$ 块 $w_k^{-1}\equiv 1\pmod 4$ 满足 $(w_k^{-1})^2 u_k=1$。
   - 将所有 $u_k\equiv 5\pmod 8$ 两两配对为 $(u_a,u_b)$：写 $u_a=5w_a^2,\ u_b=5w_b^2$（$w_a,w_b\in 1+4\mathbb Z_2$），取 $D=\frac{1}{5}\begin{pmatrix} 1 & 2\\ -2 & 1\end{pmatrix}\in M_2(\mathbb Z_2)$。显然 $D\equiv I_2\pmod 2$ 且 $D^{\mathsf T}(5I_2)D=I_2$，于是 $C_{a,b}=\operatorname{diag}(w_a^{-1},w_b^{-1})D\equiv I_2\pmod 2$ 满足 $C_{a,b}^{\mathsf T}\operatorname{diag}(u_a,u_b)C_{a,b}=I_2$。
   经置换阵 $\Pi$ 共轭组合（注意 $\Pi^{\mathsf T}M\Pi\equiv I_n\pmod 2\iff M\equiv I_n\pmod 2$），得 $C_0\equiv I_n\pmod 2$ 使 $C_0^{\mathsf T}(R^{\mathsf T}GR)C_0=I_n$。令 $C=RC_0\equiv I_n\pmod 2$，则 $C\in\mathscr S_F^{(n)}(G)$。$\square$

---

#### 1.2 $\mathscr R_{L,M}(A)$ 与 $\mathscr C_{L,M}(A)$ 的可核验提升判准、空集条件与闭式精确基数

先统一处理基点约化：
- **当 $A$ 可行**（即 $\forall i,\ s_i(A)=0$）：取定 $W_0\in\mathscr S_F(A)$，左乘 $W_0^{-1}$ 给出与模 $2^M\mathcal O_L$ 约化及 $\sigma_\mu$-作用均兼容的双射
  $$\mathscr S_L(A)\xrightarrow{\ \sim\ }\prod_{i=1}^r \operatorname{O}_{n_i}^{(1)}(\mathcal O_L),\quad \mathscr R_{L,M}(A)\xrightarrow{\ \sim\ }\prod_{i=1}^r \mathscr R_{L,M}^{(n_i)}(I_{n_i}),\quad \mathscr C_{L,M}(A)\xrightarrow{\ \sim\ }\prod_{i=1}^r \mathscr C_{L,M}^{(n_i)}(I_{n_i}),$$
  其中 $\operatorname{O}_n^{(1)}(\mathcal O_L):=\mathscr S_L^{(n)}(I_n)$，$\mathscr C_{L,M}^{(n)}:=\mathscr C_{L,M}^{(n)}(I_n)$，$\mathscr R_{L,M}^{(n)}:=\{\bar Q=Q\bmod 2^M\mathcal O_L:Q\in\operatorname{O}_n^{(1)}(\mathcal O_L)\}$。
- **当 $A$ 不可行**（即 $\exists i,\ s_i(A)=1$）：由定理 1 证明已得 $\mathscr S_L(A)=\emptyset$，故 $\mathscr R_{L,M}(A)=\emptyset$（$\forall M\ge 2$）；且 $\mathscr C_{L,M}(A)=\emptyset$（$\forall M\ge 3$）。而当 $M=2$ 时，由引理 2，$B\bmod 4$ 满足 $B\equiv I_d\pmod 2$，$B^{\mathsf T}B=\operatorname{diag}(G_1,\dots,G_r)\equiv I_d\pmod 4$，且 $B^{\mathsf T}P_iB=E_iG_i\equiv E_i\pmod 4$，故 $\bar U_0:=B\bmod 4\in \mathscr C_{F,2}(A)\subseteq\mathscr C_{L,2}(A)$ 非空！并且左乘 $\bar U_0^{-1}$ 仍给出 $\sigma_\mu$-等变双射 $\mathscr C_{L,2}(A)\xrightarrow{\sim}\prod_{i=1}^r \mathscr C_{L,2}^{(n_i)}(I_{n_i})$（因 $G_i\equiv I_{n_i}\pmod 4$）。

下述核心引理刻画单块群 $\mathscr C_{L,M}^{(n)}$ 与 $\mathscr R_{L,M}^{(n)}$：

#### 引理 3（正交矩阵类的逐层提升与 $\mathscr R_{L,M}(A)$ 判准）
设 $n\ge 1$，$M\ge 2$，$L\in\{F,K_{-1},K_2\}$。
1. 对任意 $Q\in\mathscr C_{L,M}^{(n)}$，取其任一提升 $\widehat Q\in M_n(\mathcal O_L)$（或模 $2^{M+1}\mathcal O_L$ 代表元），写出 $\widehat Q^{\mathsf T}\widehat Q=I_n+2^M S$（$S^{\mathsf T}=S\in M_n(\mathcal O_L)$）。则对角线模 $2\mathcal O_L$ 类 $S_{kk}\bmod 2\mathcal O_L$（即 $(\widehat Q^{\mathsf T}\widehat Q)_{kk}\bmod 2^{M+1}\mathcal O_L$）与提升 $\widehat Q$ 的选取无关，且：
   $$Q\in\operatorname{im}\big(\mathscr C_{L,M+1}^{(n)}\to \mathscr C_{L,M}^{(n)}\big)\iff S_{kk}\equiv 0\pmod{2\mathcal O_L}\quad(\forall k=1,\dots,n).$$
   若此条件成立，则其在 $\mathscr C_{L,M+1}^{(n)}$ 中的纤维恰有 $2^{e_L\binom{n+1}{2}}$ 个元素。
2. 进一步，对一切 $M\ge 2$ 均有
   $$\mathscr R_{L,M}^{(n)}=\operatorname{im}\big(\mathscr C_{L,M+1}^{(n)}\to \mathscr C_{L,M}^{(n)}\big)=\left\{Q\in\mathscr C_{L,M}^{(n)}: (\widehat Q^{\mathsf T}\widehat Q)_{kk}\equiv 1\pmod{2^{M+1}\mathcal O_L}\ \forall k=1,\dots,n\right\},$$
   且自然约化映射 $\mathscr R_{L,M+1}^{(n)}\to\mathscr R_{L,M}^{(n)}$ 恒为满射，每个纤维恰有 $2^{e_L\binom{n}{2}}$ 个元素。
3. 当 $M=2$ 时，$Q\in\mathscr C_{L,2}^{(n)}$ 皆形如 $Q=(I_n+2\bar X)\bmod 4\mathcal O_L$（其中 $\bar X\in M_n(\mathcal O_L/2\mathcal O_L)$ 对称，$\bar X^{\mathsf T}=\bar X$），且
   $$Q\in\mathscr R_{L,2}^{(n)}\iff \bar X_{kk}\in\mathbb F_2\subseteq \mathcal O_L/2\mathcal O_L\ \text{且}\ \sum_{j\ne k}\bar X_{jk}^2=0\in\mathcal O_L/2\mathcal O_L\quad(\forall k=1,\dots,n).$$

**证明**：
(1) 若 $\widehat Q'=\widehat Q+2^M\Delta$（$\Delta\in M_n(\mathcal O_L)$），因 $M\ge 2$ 故 $2M\ge M+2>M+1$，且 $\widehat Q\equiv I_n\pmod{2\mathcal O_L}$，于是
$$\widehat Q'^{\mathsf T}\widehat Q'=I_n+2^M(S+\widehat Q^{\mathsf T}\Delta+\Delta^{\mathsf T}\widehat Q)+2^{2M}\Delta^{\mathsf T}\Delta\equiv I_n+2^M(S+\Delta+\Delta^{\mathsf T})\pmod{2^{M+1}\mathcal O_L}.$$
在对角线上，$(\Delta+\Delta^{\mathsf T})_{kk}=2\Delta_{kk}\equiv 0\pmod{2\mathcal O_L}$，故 $(\widehat Q'^{\mathsf T}\widehat Q')_{kk}\equiv(\widehat Q^{\mathsf T}\widehat Q)_{kk}\pmod{2^{M+1}\mathcal O_L}$ 不依赖提升。且 $\widehat Q'\bmod 2^{M+1}\mathcal O_L\in\mathscr C_{L,M+1}^{(n)}\iff S+\Delta+\Delta^{\mathsf T}\equiv 0\pmod{2\mathcal O_L}$。在非对角线 $i<j$ 处，任取 $\Delta_{ij}\bmod 2\mathcal O_L$ 可唯一解出 $\Delta_{ji}\equiv -S_{ij}-\Delta_{ij}\pmod{2\mathcal O_L}$（因 $S$ 对称）；在对角线处，$(\Delta+\Delta^{\mathsf T})_{kk}\equiv 0\pmod{2\mathcal O_L}$ 恒成立。故可解当且仅当 $S_{kk}\equiv 0\pmod{2\mathcal O_L}$（$\forall k$）；此时可自由选取 $\Delta_{kk}\ (n$ 个）及 $\Delta_{ij}\ (i<j,\ \binom{n}{2}$ 个）模 $2\mathcal O_L$，共 $|\mathcal O_L/2\mathcal O_L|^{\binom{n+1}{2}}=2^{e_L\binom{n+1}{2}}$ 个提升。

(2) 显然 $\mathscr R_{L,M}^{(n)}\subseteq\operatorname{im}(\mathscr C_{L,M+1}^{(n)}\to\mathscr C_{L,M}^{(n)})$。反之，设 $Q\in\mathscr C_{L,M}^{(n)}$ 满足对某（从而任一）提升 $\widehat Q$ 有 $\widehat Q^{\mathsf T}\widehat Q=I_n+2^M S$ 且 $S_{kk}=2T_{kk}$（$T_{kk}\in\mathcal O_L$）。
- **情形 $M\ge 3$**：作提升 $\widehat Q'=\widehat Q+2^M\Delta$ 满足 $\Delta_{ij}+\Delta_{ji}\equiv -S_{ij}\pmod{2\mathcal O_L}$（$i<j$）与 $\Delta_{kk}\equiv -T_{kk}\pmod{2\mathcal O_L}$。此时 $\widehat Q'^{\mathsf T}\widehat Q'\equiv I_n\pmod{2^{M+1}\mathcal O_L}$。再计算对角元模 $2^{M+2}\mathcal O_L$：
  $$(\widehat Q'^{\mathsf T}\widehat Q')_{kk}=1+2^{M+1}T_{kk}+2^{M+1}\sum_{j=1}^n \widehat Q_{jk}\Delta_{jk}+2^{2M}\sum_{j=1}^n\Delta_{jk}^2.$$
  因 $\widehat Q_{kk}\equiv 1\pmod{2\mathcal O_L}$、$\widehat Q_{jk}\in 2\mathcal O_L$（$j\ne k$），且 $M\ge 3\implies 2M\ge M+3>M+2$，上式给出
  $$(\widehat Q'^{\mathsf T}\widehat Q')_{kk}\equiv 1+2^{M+1}(T_{kk}+\Delta_{kk})\pmod{2^{M+2}\mathcal O_L}.$$
  因此 $\widehat Q'\bmod 2^{M+1}\mathcal O_L\in\mathscr C_{L,M+1}^{(n)}$ 仍满足到 $M+2$ 的提升条件**当且仅当** $\Delta_{kk}\equiv -T_{kk}\pmod{2\mathcal O_L}$。固定 $\Delta_{kk}$ 而自由选取 $\Delta_{ij}\ (i<j)$ 恰有 $2^{e_L\binom{n}{2}}$ 种选法。由 $M\ge 3$ 起归纳逐层提升即得完备 $2$-进极限 $\widetilde Q\in\operatorname{O}_n^{(1)}(\mathcal O_L)$ 满足 $\widetilde Q\equiv Q\pmod{2^M\mathcal O_L}$，即 $Q\in\mathscr R_{L,M}^{(n)}$；同时也证明了当 $M\ge 3$ 时 $\mathscr R_{L,M+1}^{(n)}\to\mathscr R_{L,M}^{(n)}$ 是满射且纤维大小为 $2^{e_L\binom{n}{2}}$。
- **情形 $M=2$**：$Q=(I_n+2\bar X)\bmod 4\mathcal O_L$。因 $(I_n+2X)^{\mathsf T}(I_n+2X)=I_n+2(X+X^{\mathsf T})+4X^{\mathsf T}X$，故 $Q\in\mathscr C_{L,2}^{(n)}\iff \bar X+\bar X^{\mathsf T}=0$ 于 $M_n(\mathcal O_L/2\mathcal O_L)\iff \bar X^{\mathsf T}=\bar X$。取对称提升 $X\in M_n(\mathcal O_L)$ 令 $\widehat Q=I_n+2X$，则 $\widehat Q^{\mathsf T}\widehat Q=I_n+4S$（$S=X+X^2$）。若 $S_{kk}=2T_{kk}\in 2\mathcal O_L$，取 $\widehat Q'=\widehat Q+4\Delta$ 满足 $\Delta_{ij}+\Delta_{ji}\equiv -S_{ij}\pmod{2\mathcal O_L}$（$i<j$）。此时 $M=2$ 对应 $2^{2M}=16=2^{M+2}$，仍有 $16\sum_j\Delta_{jk}^2\equiv 0\pmod{16\mathcal O_L}$ 与 $8\widehat Q_{jk}\Delta_{jk}\equiv 0\pmod{16\mathcal O_L}$（$j\ne k$），故同样有
  $$(\widehat Q'^{\mathsf T}\widehat Q')_{kk}\equiv 1+8(T_{kk}+\Delta_{kk})\pmod{16\mathcal O_L}!$$
  从而当且仅当 $\Delta_{kk}\equiv -T_{kk}\pmod{2\mathcal O_L}$ 时 $\widehat Q'\bmod 8\mathcal O_L$ 可继续提升至 $M=4$（进而由 $M\ge 3$ 情形提升至 $\operatorname{O}_n^{(1)}(\mathcal O_L)$）。这表明 $Q\in\mathscr R_{L,2}^{(n)}$ 成立，且 $\mathscr R_{L,3}^{(n)}\to\mathscr R_{L,2}^{(n)}$ 同样是满射、纤维大小为 $2^{e_L\binom{n}{2}}$。

(3) 由 $\widehat Q=I_n+2X$（$X$ 对称），$S=X+X^2$ 的对角元模 $2\mathcal O_L$ 为 $\bar X_{kk}+\bar X_{kk}^2+\sum_{j\ne k}\bar X_{jk}^2=0$。考察 $R_1=\mathcal O_L/2\mathcal O_L$ 中两子集：
- 对 $L=F$（$R_1=\mathbb F_2$）：$x^2+x=0$ 恒成立，且 $x^2=x\in\mathbb F_2$。
- 对 $L=K_{-1}$（$R_1=\mathbb F_2[\theta_{-1}]/(\theta_{-1}^2-1)$）：写 $x=a+b\theta_{-1}$，则 $x^2=a+b\in\mathbb F_2$，而 $x^2+x=b(1+\theta_{-1})\in\{0,1+\theta_{-1}\}$。
- 对 $L=K_2$（$R_1=\mathbb F_2[\theta_2]/(\theta_2^2)$）：写 $x=a+b\theta_2$，则 $x^2=a\in\mathbb F_2$，而 $x^2+x=b\theta_2\in\{0,\theta_2\}$。
在三种域上，集合 $\{x^2+x:x\in R_1\}$ 与 $\mathbb F_2=\operatorname{span}_{\mathbb F_2}\{y^2:y\in R_1\}$ 之交均仅为 $\{0\}$！因此 $\bar X_{kk}^2+\bar X_{kk}=\sum_{j\ne k}\bar X_{jk}^2\iff \bar X_{kk}^2+\bar X_{kk}=0$（即 $\bar X_{kk}\in\mathbb F_2$）且 $\sum_{j\ne k}\bar X_{jk}^2=0$。$\square$

#### 定理 2（目标 1 的全部结论）
记 $S_{\mathrm{off}}:=\sum_{i=1}^r \binom{n_i}{2}$，$S_{\mathrm{sym}}:=\sum_{i=1}^r \binom{n_i+1}{2}=S_{\mathrm{off}}+d$，与 $e_L=[L:F]$。对任意合法 $A$、$L\in\{F,K_{-1},K_2\}$ 及 $M\ge 2$：
1. **$\bar U\in\mathscr C_{L,M}(A)$ 属于 $\mathscr R_{L,M}(A)$ 的可核验充要条件**：
   任取 $\bar U$ 的一个提升 $\widehat U\in M_d(\mathcal O_L/2^{M+1}\mathcal O_L)$（或 $M_d(\mathcal O_L)$），则
   $$\bar U\in\mathscr R_{L,M}(A)\iff (\widehat U^{\mathsf T}\widehat U)_{kk}\equiv 1\pmod{2^{M+1}\mathcal O_L}\quad(\forall k=1,\dots,d)$$
   （该条件与 $\widehat U$ 的选取无关，可有限验证，且等价于 $\bar U\in\operatorname{im}(\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A))$）。
   - *验证*：将 $\widehat U$ 换为 $\widehat U+2^M\Delta$ 时，对角线变化 $2^{M+1}(\widehat U^{\mathsf T}\Delta)_{kk}+2^{2M}(\Delta^{\mathsf T}\Delta)_{kk}\equiv 0\pmod{2^{M+1}\mathcal O_L}$。若 $A$ 可行，取 $W_0\in\mathscr S_F(A)$，置 $\widehat Q=W_0^{-1}\widehat U$（其块对角化模 $2^M\mathcal O_L$），有 $\widehat Q^{\mathsf T}\widehat Q=\widehat U^{\mathsf T}\widehat U$，由引理 3(2) 即得等价性。若 $A$ 不可行，设 $\bar U\in\mathscr C_{L,2}(A)$ 写为 $B\operatorname{diag}(\widehat C_1,\dots,\widehat C_r)\bmod 4$（此时 $H_i:=\widehat C_i^{\mathsf T}G_i\widehat C_i\equiv I_{n_i}\pmod{4\mathcal O_L}$），若所有对角元 $\equiv 1\pmod{8\mathcal O_L}$，因非对角元 $\in 4\mathcal O_L$，得 $\det(\widehat C_i)^2\det(G_i)=\det(H_i)\equiv \prod_{k\in I_i}(H_i)_{kk}\equiv 1\pmod{8\mathcal O_L}$，与定理 1 中 $s_i(A)=1$ 情形矛盾！故不可行时两边均不成立，等价性仍真。
2. **空集条件与闭式精确基数**：
   - **情形 I：$A$ 可行**（即 $\forall i,\ s_i(A)=0$）：$\mathscr R_{L,M}(A)$ 与 $\mathscr C_{L,M}(A)$ 对所有 $M\ge 2$ 均非空，且
     $$|\mathscr R_{L,M}(A)| = 2^{e_L(M-1)S_{\mathrm{off}}+r}\qquad(\forall M\ge 2),$$
     $$|\mathscr C_{L,2}(A)| = 2^{e_L S_{\mathrm{sym}}}=2^{e_L(S_{\mathrm{off}}+d)},$$
     $$|\mathscr C_{L,M}(A)| = 2^{e_L(M-1)S_{\mathrm{off}}+e_L d+r}\qquad(\forall M\ge 3).$$
   - **情形 II：$A$ 不可行**（即 $\exists i,\ s_i(A)=1$）：
     - 对所有 $M\ge 2$，$\mathscr R_{L,M}(A)=\emptyset$（基数为 $0$）；
     - 对所有 $M\ge 3$，$\mathscr C_{L,M}(A)=\emptyset$（基数为 $0$）；
     - 对 $M=2$，$\mathscr C_{L,2}(A)\ne\emptyset$，且 $|\mathscr C_{L,2}(A)|=2^{e_L S_{\mathrm{sym}}}$。
   （从而空集条件为：$\mathscr R_{L,M}(A)=\emptyset\iff \exists i,\ s_i(A)=1$；$\mathscr C_{L,2}(A)$ 永非空；对 $M\ge 3$，$\mathscr C_{L,M}(A)=\emptyset\iff \exists i,\ s_i(A)=1$。）

**基数公式证明**：按引理 2 只需对单块 $n\ge 1$ 计算 $|\mathscr C_{L,M}^{(n)}|$ 与 $|\mathscr R_{L,M}^{(n)}|$ 再连乘 $i=1,\dots,r$。
- $M=2$ 时，由引理 3(3)，$\mathscr C_{L,2}^{(n)}$ 与 $\operatorname{Sym}_n(\mathcal O_L/2\mathcal O_L)$ 双射，故 $|\mathscr C_{L,2}^{(n)}|=2^{e_L\binom{n+1}{2}}$。
  对 $|\mathscr R_{L,2}^{(n)}|$：各对角元 $\bar X_{kk}\in\mathbb F_2$ 有 $2^n$ 种取法。对非对角线 $i<j$，定义映射 $\varphi_L:\mathcal O_L/2\mathcal O_L\to\mathbb F_2$ 为 $x^2=\varphi_L(x)\cdot 1$（即 $\varphi_F(a)=a$，$\varphi_{K_{-1}}(a+b\theta_{-1})=a+b$，$\varphi_{K_2}(a+b\theta_2)=a$）。$\varphi_L$ 为满 $\mathbb F_2$-线性映射，核长为 $e_L-1$。条件 $\sum_{j\ne k}\varphi_L(\bar X_{jk})=0\ (\forall k)$ 即以 $(\varphi_L(\bar X_{jk}))_{j<k}$ 为边权的 $K_n$ 上各顶点度模 $2$ 为 $0$，这是 $\mathbb F_2^{\binom{n}{2}}\to\mathbb F_2^n$（像为偶数和向量，维数 $n-1$）的核（偶图圈空间），其 $\mathbb F_2$-维数为 $\binom{n}{2}-(n-1)=\binom{n-1}{2}$（对 $n=1$ 亦为 $0$）。再对每条边选定 $\ker(\varphi_L)$ 分量（共 $(e_L-1)\binom{n}{2}$ 比特），总 $\mathbb F_2$-维数为
  $$n+(e_L-1)\binom{n}{2}+\binom{n}{2}-(n-1)=e_L\binom{n}{2}+1,$$
  即 $|\mathscr R_{L,2}^{(n)}|=2^{e_L\binom{n}{2}+1}$。
- 由引理 3(2)，对一切 $M\ge 2$，$\mathscr R_{L,M+1}^{(n)}\to\mathscr R_{L,M}^{(n)}$ 满射且纤维长为 $2^{e_L\binom{n}{2}}$，归纳即得 $|\mathscr R_{L,M}^{(n)}|=2^{e_L(M-1)\binom{n}{2}+1}$。
- 对一切 $M\ge 3$，由引理 3(1)(2)，$\mathscr C_{L,M}^{(n)}\to\mathscr C_{L,M-1}^{(n)}$ 的像为 $\mathscr R_{L,M-1}^{(n)}$ 且非空纤维长为 $2^{e_L\binom{n+1}{2}}$，故
  $$|\mathscr C_{L,M}^{(n)}|=|\mathscr R_{L,M-1}^{(n)}|\cdot 2^{e_L\binom{n+1}{2}}=2^{e_L(M-2)\binom{n}{2}+1+e_L\binom{n}{2}+e_L n}=2^{e_L(M-1)\binom{n}{2}+e_L n+1}.$$
连乘 $i=1,\dots,r$ 即得定理 2。$\square$

- **具体反例**（验证上述包含严格性）：
  1. *不可行但 $M=2$ 非空*：取 $r=2,n_1=n_2=1$（或补以 $I_{n_1-1},I_{n_2-1}$ 及 $E_j$），令 $A_1$ 的左上 $2\times 2$ 块为 $\frac{1}{5}\begin{pmatrix}1&2\\2&4\end{pmatrix}$，$A_2$ 的左上 $2\times 2$ 块为 $\frac{1}{5}\begin{pmatrix}4&-2\\-2&1\end{pmatrix}$。此处 $s_1(A)=s_2(A)=1$，故 $\mathscr S_L(A)=\mathscr R_{L,M}(A)=\mathscr C_{L,3}(A)=\emptyset$，而 $\bar U_0=B\bmod 4\in\mathscr C_{F,2}(A)\subseteq\mathscr C_{L,2}(A)$。
  2. *$\mathscr C_{L,M}(A)\setminus\mathscr R_{L,M}(A)\ne\emptyset$*：取 $A_i=E_i$。当 $M\ge 3$ 时 $\operatorname{diag}(1+2^{M-1},1,\dots,1)\in\mathscr C_{F,M}(E)\setminus\mathscr R_{F,M}(E)$（其平方第一项为 $1+2^M\not\equiv 1\pmod{2^{M+1}}$）；当 $M=2,\ L=K_\mu$ 时 $\operatorname{diag}(1+2\theta_\mu,1,\dots,1)\in\mathscr C_{K_\mu,2}(E)\setminus\mathscr R_{K_\mu,2}(E)$；当 $M=2,\ L=F$ 且某 $n_i\ge 2$ 时，将块 $i$ 的前 $2\times 2$ 块取为 $\begin{pmatrix}1&2\\2&1\end{pmatrix}$ 得 $\mathscr C_{F,2}(E)\setminus\mathscr R_{F,2}(E)$ 中元素（第一列模长平方 $=5\not\equiv 1\pmod 8$）。

---

### 四、目标 2：Galois 固定点集、轨道数、逐层约化像与纤维及兼容序列刻画

记块对角对称矩阵的 $\mathbb F_2$-线性空间为
$$\mathcal L_{\mathrm{sym}}:=\{Y\in M_d(\mathbb F_2):Y^{\mathsf T}=Y,\ [Y,E_j]=0\ (\forall j)\}=\{\operatorname{diag}(Y_1,\dots,Y_r):Y_i\in\operatorname{Sym}_{n_i}(\mathbb F_2)\},$$
其零对角子空间与偶图圈子空间分别为
$$\mathcal L_{\mathrm{sym}}^0:=\{Y\in\mathcal L_{\mathrm{sym}}:Y_{kk}=0\ (\forall k=1,\dots,d)\},\qquad \mathcal L_{\mathrm{even}}^0:=\left\{Y\in\mathcal L_{\mathrm{sym}}^0:\sum_{j\in I_i\setminus\{k\}}Y_{jk}=0\ (\forall i,\forall k\in I_i)\right\}.$$
注意 $\dim_{\mathbb F_2}\mathcal L_{\mathrm{sym}}=S_{\mathrm{sym}}$，$\dim_{\mathbb F_2}\mathcal L_{\mathrm{sym}}^0=S_{\mathrm{off}}$，$\dim_{\mathbb F_2}\mathcal L_{\mathrm{even}}^0=\sum_{i=1}^r \binom{n_i-1}{2}=S_{\mathrm{off}}-\sum_{i=1}^r(n_i-1)=S_{\mathrm{off}}-d+r$。且对 $Y\in M_d(\mathbb F_2)$，$2^{M-1}\theta_\mu Y\bmod 2^M\mathcal O_\mu$ 是良定义的。

#### 定理 3（固定矩阵类的具体刻画及与基域集合的关系）
设 $\mu\in\{-1,2\}$，$M\ge 2$。

1. **$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 的刻画**：
   - 若 $A$ 不可行且 $M\ge 3$，则 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr C_{F,M}(A)=\emptyset$。
   - 其余情形（$A$ 可行且 $M\ge 2$，或 $A$ 不可行且 $M=2$）：
     $$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr C_{F,M}(A)\oplus 2^{M-1}\theta_\mu\mathcal L_{\mathrm{sym}}=\left\{\bar U_0+2^{M-1}\theta_\mu Y\bmod 2^M\mathcal O_\mu:\bar U_0\in\mathscr C_{F,M}(A),\ Y\in\mathcal L_{\mathrm{sym}}\right\}$$
     （直和意指分解 $\bar U=\bar U_0+2^{M-1}\theta_\mu Y$ 唯一）。特别地：
     - 当 $M=2$ 时，$\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}=\mathscr C_{K_\mu,2}(A)$；
     - 在任意情形下，$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z/2^M\mathbb Z)=\mathscr C_{F,M}(A)$（取 $Y=0$），且投影 $\pi_0(\bar U_0+2^{M-1}\theta_\mu Y):=\bar U_0$ 是到 $\mathscr C_{F,M}(A)$ 的满射，纤维均为 $2^{M-1}\theta_\mu\mathcal L_{\mathrm{sym}}$ 的陪集，大小为 $2^{S_{\mathrm{sym}}}$。

2. **$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 的刻画**：
   - 若 $A$ 不可行，则 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr R_{F,M}(A)=\emptyset$（$\forall M\ge 2$）。
   - 若 $A$ 可行：
     - **当 $M\ge 3$，或（$M=2$ 且 $\mu=2$）时**：
       $$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr R_{F,M}(A)\oplus 2^{M-1}\theta_\mu\mathcal L_{\mathrm{sym}}^0=\left\{\bar U_0+2^{M-1}\theta_\mu Y\bmod 2^M\mathcal O_\mu:\bar U_0\in\mathscr R_{F,M}(A),\ Y\in\mathcal L_{\mathrm{sym}}^0\right\}.$$
       此时 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z/2^M\mathbb Z)=\mathscr R_{F,M}(A)$，且 $\pi_0$ 将 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 满射到 $\mathscr R_{F,M}(A)$，纤维大小为 $2^{S_{\mathrm{off}}}$。
     - **当 $M=2$ 且 $\mu=-1$ 时**：
       $$\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}=\left\{\bar U_0+2\theta_{-1}Y\bmod 4\mathcal O_{-1}:\bar U_0\in\mathscr C_{F,2}(A),\ Y\in\mathcal L_{\mathrm{sym}}^0,\ (\widehat U_0^{\mathsf T}\widehat U_0)_{kk}+4\sum_{j\in I_i\setminus\{k\}}Y_{jk}\equiv 1\pmod 8\ (\forall i,\forall k\in I_i)\right\}$$
       （等价地，取定 $W_0\in\mathscr S_F(A)$ 并写 $\bar U_0=W_0(I_d+2X_0)\bmod 4$ 且 $X_0\in\mathcal L_{\mathrm{sym}}$，条件即为 $Y\in\mathcal L_{\mathrm{sym}}^0$ 且 $X_0^{\mathrm{off}}+Y\in\mathcal L_{\mathrm{even}}^0$，其中 $X_0^{\mathrm{off}}$ 为 $X_0$ 置零对角元所得）。此时：
       - $\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}\cap M_d(\mathbb Z/4\mathbb Z)=\mathscr R_{F,2}(A)$；
       - 但与 $\mu=2$ 迥异，投影 $\pi_0:\bar U_0+2\theta_{-1}Y\mapsto\bar U_0$ 将 $\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}$ **满射到整个 $\mathscr C_{F,2}(A)$**（当 $\max_i n_i\ge 2$ 时严格大于 $\mathscr R_{F,2}(A)$），且对每个 $\bar U_0\in\mathscr C_{F,2}(A)$，纤维是 $2\theta_{-1}\mathcal L_{\mathrm{even}}^0$ 的一个非空陪集，大小为 $2^{S_{\mathrm{off}}-d+r}$。

**证明**：
(1) 因 $\mathcal O_\mu/2^M\mathcal O_\mu=(\mathbb Z/2^M\mathbb Z)\oplus(\mathbb Z/2^M\mathbb Z)\theta_\mu$ 且 $\sigma_\mu(a+b\theta_\mu)=a-b\theta_\mu$，元素被 $\sigma_\mu$ 固定当且仅当 $2b\equiv 0\pmod{2^M}\iff b\in 2^{M-1}(\mathbb Z/2^M\mathbb Z)$。故 $\bar U\in M_d(\mathcal O_\mu/2^M\mathcal O_\mu)^{\sigma_\mu}$ 当且仅当 $\bar U=\bar U_0+2^{M-1}\theta_\mu Y\bmod 2^M\mathcal O_\mu$，其中 $\bar U_0\in M_d(\mathbb Z/2^M\mathbb Z)$ 与 $Y\in M_d(\mathbb F_2)$ 均唯一确定。

取基点 $W_0\in\mathscr S_F(A)$（可行时）或 $\bar U_0^{\mathrm{base}}=B\bmod 4\in\mathscr C_{F,2}(A)$（不可行 $M=2$ 时），记之为 $W$。因 $W\equiv I_d\pmod 2$，有 $W(2^{M-1}\theta_\mu Y')\equiv 2^{M-1}\theta_\mu Y'\pmod{2^M\mathcal O_\mu}$。故经引理 2 约化为单块情形：设 $\bar Q=Q_0+2^{M-1}\theta_\mu Y\bmod 2^M\mathcal O_\mu$（$Q_0\in M_n(\mathbb Z/2^M\mathbb Z),\ Y\in M_n(\mathbb F_2)$）。
- $\bar Q\equiv I_n\pmod{2\mathcal O_\mu}\iff Q_0\equiv I_n\pmod 2$（因 $M\ge 2\implies 2^{M-1}\theta_\mu Y\in 2\mathcal O_\mu$）。
- 计算 $\bar Q^{\mathsf T}\bar Q=(Q_0^{\mathsf T}Q_0+2^{2M-2}\mu Y^{\mathsf T}Y)+2^{M-1}\theta_\mu(Q_0^{\mathsf T}Y+Y^{\mathsf T}Q_0)$：
  因 $M\ge 2\implies 2M-2\ge M$，故 $2^{2M-2}\equiv 0\pmod{2^M}$；又因 $Q_0\equiv I_n\pmod 2$，有 $Q_0^{\mathsf T}Y+Y^{\mathsf T}Q_0\equiv Y+Y^{\mathsf T}\pmod 2$。因此
  $$\bar Q^{\mathsf T}\bar Q\equiv I_n\pmod{2^M\mathcal O_\mu}\iff Q_0^{\mathsf T}Q_0\equiv I_n\pmod{2^M}\ \text{且}\ Y^{\mathsf T}=Y.$$
这直接证明了 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr C_{F,M}(A)\oplus 2^{M-1}\theta_\mu\mathcal L_{\mathrm{sym}}$。

(2) 设 $A$ 可行，取 $\bar U=\bar U_0+2^{M-1}\theta_\mu Y\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$，取整数提升 $\widehat U=\widehat U_0+2^{M-1}\theta_\mu\widehat Y$（$\widehat U_0,\widehat Y\in M_d(\mathbb Z_2)$）。按定理 2(1)，$\bar U\in\mathscr R_{K_\mu,M}(A)$ 当且仅当对所有 $k=1,\dots,d$：
$$(\widehat U^{\mathsf T}\widehat U)_{kk}=(\widehat U_0^{\mathsf T}\widehat U_0)_{kk}+2^M\theta_\mu(\widehat U_0^{\mathsf T}\widehat Y)_{kk}+2^{2M-2}\mu(\widehat Y^{\mathsf T}\widehat Y)_{kk}\equiv 1\pmod{2^{M+1}\mathcal O_\mu}.$$
因 $\widehat U_0\equiv I_d\pmod 2$，$(\widehat U_0^{\mathsf T}\widehat Y)_{kk}\equiv Y_{kk}\pmod 2$，故比较 $\theta_\mu$ 分量模 $2^{M+1}$ 得必要条件 $Y_{kk}=0\ (\forall k)$，即 $Y\in\mathcal L_{\mathrm{sym}}^0$。再比较 $1$ 分量模 $2^{M+1}$：
- 若 $M\ge 3$：则 $2M-2\ge M+1$，故 $2^{2M-2}\mu(\widehat Y^{\mathsf T}\widehat Y)_{kk}\equiv 0\pmod{2^{M+1}}$，条件化为 $(\widehat U_0^{\mathsf T}\widehat U_0)_{kk}\equiv 1\pmod{2^{M+1}}$（$\forall k$），由定理 2(1) 此即 $\bar U_0\in\mathscr R_{F,M}(A)$。
- 若 $M=2$ 且 $\mu=2$：则 $2^{2M-2}\mu=4\cdot 2=8=2^{M+1}$，上项仍模 $8$ 为 $0$，故同样等价于 $\bar U_0\in\mathscr R_{F,2}(A)$ 与 $Y\in\mathcal L_{\mathrm{sym}}^0$。
- 若 $M=2$ 且 $\mu=-1$：则 $2^{2M-2}\mu=-4\equiv 4\pmod 8$，且对 $k\in I_i$，因 $Y_{kk}=0$ 与 $Y\in\mathcal L_{\mathrm{sym}}^0$，有 $(\widehat Y^{\mathsf T}\widehat Y)_{kk}=\sum_{j\in I_i\setminus\{k\}}Y_{jk}^2\equiv\sum_{j\in I_i\setminus\{k\}}Y_{jk}\pmod 2$。故条件化为
  $$(\widehat U_0^{\mathsf T}\widehat U_0)_{kk}+4\sum_{j\in I_i\setminus\{k\}}Y_{jk}\equiv 1\pmod 8\quad(\forall i,\ \forall k\in I_i).$$
  若写 $\bar U_0=W_0(I_d+2X_0)\bmod 4$（$W_0\in\mathscr S_F(A)$，$X_0\in\mathcal L_{\mathrm{sym}}$），可取 $\widehat U_0=W_0(I_d+2\widehat X_0)$（$\widehat X_0^{\mathsf T}=\widehat X_0$），则 $(\widehat U_0^{\mathsf T}\widehat U_0)_{kk}=((I_d+2\widehat X_0)^2)_{kk}\equiv 1+4\sum_{j\in I_i\setminus\{k\}}(X_0)_{jk}\pmod 8$。条件成为 $\sum_{j\in I_i\setminus\{k\}}(X_0^{\mathrm{off}}+Y)_{jk}\equiv 0\pmod 2$，即 $X_0^{\mathrm{off}}+Y\in\mathcal L_{\mathrm{even}}^0$。由于 $X_0^{\mathrm{off}}\in\mathcal L_{\mathrm{sym}}^0$，每块向量 $(\sum_{j\in I_i\setminus\{k\}}(X_0^{\mathrm{off}})_{jk})_{k\in I_i}$ 的分量之和在 $\mathbb F_2$ 中为 $0$，恒属于度映射 $Y_i\mapsto(\sum_{j\in I_i\setminus\{k\}}(Y_i)_{jk})_{k\in I_i}$ 的像！故对每个 $\bar U_0\in\mathscr C_{F,2}(A)$，满足条件的 $Y$ 恰好构成 $X_0^{\mathrm{off}}+\mathcal L_{\mathrm{even}}^0$，非空且基数为 $|\mathcal L_{\mathrm{even}}^0|=2^{S_{\mathrm{off}}-d+r}$。$\square$

#### 定理 4（固定点数与 $\langle\sigma_\mu\rangle$-轨道数）
由 $\langle\sigma_\mu\rangle\cong\mathbb Z/2\mathbb Z$ 作用下的 Burnside 引理，轨道数 $=\frac{|X|+|X^{\sigma_\mu}|}{2}$。
1. **当 $A$ 不可行时**：
   - $\mathscr R_{K_\mu,M}(A)$（$\forall M\ge 2$）与 $\mathscr C_{K_\mu,M}(A)$（$\forall M\ge 3$）固定点数与轨道数均为 $0$；
   - $\mathscr C_{K_\mu,2}(A)$ 全体固定，固定点数 $=|\mathscr C_{K_\mu,2}(A)|=2^{2S_{\mathrm{sym}}}$，轨道数 $=2^{2S_{\mathrm{sym}}}$。
2. **当 $A$ 可行时**（对 $\mu\in\{-1,2\}$ 均相同）：
   - 对 $\mathscr R_{K_\mu,M}(A)$（$\forall M\ge 2$）：
     $$|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}| = 2^{M S_{\mathrm{off}}+r},\qquad \text{轨道数}=2^{2(M-1)S_{\mathrm{off}}+r-1}+2^{M S_{\mathrm{off}}+r-1}.$$
     （验证 $M=2, \mu=-1$：$|\mathscr C_{F,2}(A)|\cdot|\mathcal L_{\mathrm{even}}^0|=2^{S_{\mathrm{off}}+d}\cdot 2^{S_{\mathrm{off}}-d+r}=2^{2S_{\mathrm{off}}+r}$，与上式在 $M=2$ 一致，且此时全部元素均固定，轨道数 $=2^{2S_{\mathrm{off}}+r}$。）
   - 对 $\mathscr C_{K_\mu,M}(A)$：
     - $M=2$：$|\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}|=2^{2S_{\mathrm{sym}}}=2^{2S_{\mathrm{off}}+2d}$，轨道数 $=2^{2S_{\mathrm{sym}}}$；
     - $M\ge 3$：
       $$|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}|=|\mathscr C_{F,M}(A)|\cdot|\mathcal L_{\mathrm{sym}}|=2^{M S_{\mathrm{off}}+2d+r},\qquad \text{轨道数}=2^{2(M-1)S_{\mathrm{off}}+2d+r-1}+2^{M S_{\mathrm{off}}+2d+r-1}.$$

#### 定理 5（从精度 $M+1$ 到 $M$ 的约化像、全部非空纤维大小与固定序列提升刻画）
设 $M\ge 2$。
1. **若 $A$ 不可行**：因 $\mathscr R_{L,M+1}(A)=\mathscr C_{L,M+1}(A)=\emptyset$（$M+1\ge 3$），四个约化映射的像均为空集，无非空纤维；没有固定矩阵类可提升为 $\sigma_\mu$-固定真正解或作为兼容固定序列的分量。
2. **若 $A$ 可行**：
   - **$\mathscr R_{L,M+1}(A)\to\mathscr R_{L,M}(A)$**（$L\in\{F,K_{-1},K_2\}$）：
     约化像为整个 **$\mathscr R_{L,M}(A)$**（满射），所有纤维均非空且大小恒为 **$2^{e_L S_{\mathrm{off}}}$**。（由引理 3(2) 对 $i=1,\dots,r$ 连乘即得。）
   - **$\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A)$**（$L\in\{F,K_{-1},K_2\}$）：
     约化像为 **$\mathscr R_{L,M}(A)$**，所有非空纤维大小恒为 **$2^{e_L S_{\mathrm{sym}}}=2^{e_L(S_{\mathrm{off}}+d)}$**。（由引理 3(1)(2) 连乘即得。）
   - **$\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$**（$\mu\in\{-1,2\}$）：
     约化像为 **$\mathscr R_{F,M}(A)$**，所有非空纤维大小恒为 **$2^{2S_{\mathrm{off}}}$**。
     *证明*：因 $M+1\ge 3$，由定理 3(2)，$\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}$ 中任一元素形如 $\bar U_0'+2^M\theta_\mu Y'$（$\bar U_0'\in\mathscr R_{F,M+1}(A),\ Y'\in\mathcal L_{\mathrm{sym}}^0$）。其模 $2^M\mathcal O_\mu$ 约化即为 $\bar U_0'\bmod 2^M$。当 $\bar U_0'$ 跑遍 $\mathscr R_{F,M+1}(A)$ 时，由 $\mathscr R_{F,M+1}(A)\to\mathscr R_{F,M}(A)$ 满射且纤维长为 $2^{S_{\mathrm{off}}}$，其像恰为 $\mathscr R_{F,M}(A)$；对固定 $\bar U_0\in\mathscr R_{F,M}(A)$，$\bar U_0'$ 有 $2^{S_{\mathrm{off}}}$ 种选法，$Y'\in\mathcal L_{\mathrm{sym}}^0$ 有 $2^{S_{\mathrm{off}}}$ 种选法，故纤维大小恒为 $2^{S_{\mathrm{off}}}\cdot 2^{S_{\mathrm{off}}}=2^{2S_{\mathrm{off}}}$。$\square$
   - **$\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$**（$\mu\in\{-1,2\}$）：
     约化像为 **$\mathscr R_{F,M}(A)$**，所有非空纤维大小恒为 **$2^{2S_{\mathrm{sym}}}=2^{2(S_{\mathrm{off}}+d)}$**。
     *证明*：由定理 3(1)，$\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$ 元素形如 $\bar U_0'+2^M\theta_\mu Y'$（$\bar U_0'\in\mathscr C_{F,M+1}(A),\ Y'\in\mathcal L_{\mathrm{sym}}$）。模 $2^M\mathcal O_\mu$ 后得 $\bar U_0'\bmod 2^M$，其像为 $\operatorname{im}(\mathscr C_{F,M+1}(A)\to\mathscr C_{F,M}(A))=\mathscr R_{F,M}(A)$；对每个 $\bar U_0\in\mathscr R_{F,M}(A)$，$\bar U_0'$ 有 $2^{S_{\mathrm{sym}}}$ 个提升，$Y'$ 有 $2^{S_{\mathrm{sym}}}$ 种选法，故非空纤维大小恒为 $2^{2S_{\mathrm{sym}}}$。$\square$

3. **固定矩阵类中的两类提升刻画**（对 $\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 与 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 均成立）：
   - **能提升为 $\sigma_\mu$-固定真正解的固定矩阵类**，恰为 **$\mathscr R_{F,M}(A)$**。
     （因为 $\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A)$，从而其模 $2^M\mathcal O_\mu$ 约化像正是 $\mathscr R_{F,M}(A)$。）
   - **能作为一条逐层相容的固定矩阵类序列 $(\bar U_m)_{m\ge 2}$（其中 $\bar U_m\in\mathscr C_{K_\mu,m}(A)^{\sigma_\mu}$ 或 $\mathscr R_{K_\mu,m}(A)^{\sigma_\mu}$，且 $\bar U_{m+1}\equiv\bar U_m\pmod{2^m\mathcal O_\mu}$）在精度 $M$ 的分量的固定矩阵类**，亦恰为 **$\mathscr R_{F,M}(A)$**。
     *证明*：若 $\bar U_M$ 是相容固定序列在精度 $M$ 的分量，则至少存在 $\bar U_{M+1}\in\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$ 约化为 $\bar U_M$，从而由上文第 2 部分 $\bar U_M\in\operatorname{im}(\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu})=\mathscr R_{F,M}(A)$（也可直接取 $2$-进极限 $U=\varprojlim_m \bar U_m\in\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A)$ 得到 $\bar U_M\in\mathscr R_{F,M}(A)$）。反之，若 $\bar U_M\in\mathscr R_{F,M}(A)$，取 $W\in\mathscr S_F(A)$ 使 $W\bmod 2^M=\bar U_M$，则 $(W\bmod 2^m)_{m\ge 2}$ 即为所求逐层相容固定序列（其每层均属 $\mathscr R_{F,m}(A)\subseteq\mathscr R_{K_\mu,m}(A)^{\sigma_\mu}\subseteq\mathscr C_{K_\mu,m}(A)^{\sigma_\mu}$）。$\square$

   - *具体反例*：只要 $\max_i n_i\ge 2$，由下文定理 6 的构造（或当 $M=2,\mu=-1$ 时还可取 $Q=\begin{pmatrix}\sqrt{1-8\theta_{-1}}&2+2\theta_{-1}\\-(2+2\theta_{-1})&\sqrt{1-8\theta_{-1}}\end{pmatrix}\bmod 4\mathcal O_{-1}$），就存在 $\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\setminus\mathscr R_{F,M}(A)$：它能提升至 $\mathscr S_{K_\mu}(A)$ 中的（非 $\sigma_\mu$-固定）真正解，甚至在 $M=2,\mu=-1$ 时其基域分量 $\begin{pmatrix}1&2\\2&1\end{pmatrix}$ 尚且不在 $\mathscr R_{F,2}(I_2)$ 中；而且它连精度 $M+1$ 的 $\sigma_\mu$-固定提升都不存在，更不能提升至 $\mathscr S_F(A)$ 或成为相容固定序列的分量。

---

### 五、目标 3：二次扩张上的下降精度界、精确下降与最优性构造

#### 定理 6（最大下降精度 $N$、精确下降块秩及 $N=M$ 充要条件）
固定块秩 $(n_1,\dots,n_r)$、$\mu\in\{-1,2\}$ 与整数 $M\ge 2$。
1. **允许精确下降的块秩与最大整数 $N$**：
   $$N_{\max}=
   \begin{cases}
   M, & \text{若 } n_1=n_2=\cdots=n_r=1\text{（精确下降）},\\[4pt]
   M-1, & \text{若 } \max_{1\le i\le r}n_i\ge 2.
   \end{cases}$$
   特别地，**精确下降**（即 $N_{\max}=M$）成立当且仅当全部块秩均为 $1$（$n_1=\cdots=n_r=1$，即 $d=r$）。
2. **给定 $(A,U)$ 时能取 $N=M$ 的必要充分条件**：
   设 $A$ 合法，$U\in\mathscr S_{K_\mu}(A)$ 且 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$。则存在 $W\in\mathscr S_F(A)$ 使 $U\equiv W\pmod{2^M\mathcal O_\mu}$ **当且仅当**
   $$\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$$
   （等价地：$U\bmod 2^M\mathcal O_\mu\in M_d(\mathbb Z/2^M\mathbb Z)$；或若按 $\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu$ 写作 $U=U_0+\theta_\mu U_1$（$U_0,U_1\in M_d(\mathbb Z_2)$），等价于 $U_1\equiv 0\pmod{2^M M_d(\mathbb Z_2)}$）。

**证明**：
1. **精确下降情形（$n_1=\cdots=n_r=1$）**：
   若 $U\in\mathscr S_{K_\mu}(A)$，则 $\mathscr S_{K_\mu}(A)\ne\emptyset$，由定理 1 知 $A$ 可行，取 $W_0\in\mathscr S_F(A)$。按引理 2，$U=W_0\operatorname{diag}(c_1,\dots,c_r)$，其中 $c_i\in\operatorname{O}_1^{(1)}(\mathcal O_\mu)=\{c\in\mathcal O_\mu:c^2=1,\ c\equiv 1\pmod{2\mathcal O_\mu}\}=\{\pm 1\}\subseteq\mathbb Z_2$（因 $\mathcal O_\mu$ 为整环，$c^2=1$ 仅有 $\pm 1$ 两解）。因此 $U\in\mathscr S_F(A)$ 恒成立，取 $W=U$ 即有 $U=W\equiv W\pmod{2^M\mathcal O_\mu}$，故 $N_{\max}=M$。

2. **存在块秩 $\ge 2$ 时的可达性（$N\ge M-1$）**：
   设 $A$ 合法，$U\in\mathscr S_{K_\mu}(A)$ 且 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$。由定理 1，$\mathscr S_F(A)\ne\emptyset$。
   - 若 $M=2$：需证 $N=1$ 可达。任取 $W\in\mathscr S_F(A)$，由定义 $U\equiv I_d\equiv W\pmod{2\mathcal O_\mu}$。
   - 若 $M\ge 3$：则 $\bar U:=U\bmod 2^M\mathcal O_\mu\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$。由定理 3(2)（因 $M\ge 3$），$\bar U=\bar U_0+2^{M-1}\theta_\mu Y$，其中 $\bar U_0\in\mathscr R_{F,M}(A)$，$Y\in\mathcal L_{\mathrm{sym}}^0$。再模 $2^{M-1}\mathcal O_\mu$ 约化，得
     $$U\bmod 2^{M-1}\mathcal O_\mu=\bar U_0\bmod 2^{M-1}\in\mathscr R_{F,M-1}(A).$$
     由 $\mathscr R_{F,M-1}(A)$ 的定义，存在 $W\in\mathscr S_F(A)$ 使 $W\bmod 2^{M-1}=U\bmod 2^{M-1}\mathcal O_\mu$，即 $U\equiv W\pmod{2^{M-1}\mathcal O_\mu}$。故 $N\ge M-1$ 恒成立。

3. **最优性（反证 $N=M$ 对所有 $\max_i n_i\ge 2$、$\mu\in\{-1,2\}$ 与 $M\ge 2$ 的统一构造及具体反例）**：
   固定任意块秩满足某 $n_i\ge 2$，取合法且可行的输入 $A_j=E_j$（$j=1,\dots,r$）。（若要对任一给定的可行 $A$ 构造反例，取定 $W_0\in\mathscr S_F(A)$ 并令 $U'=W_0 U$ 即可，因 $W_0\in\operatorname{GL}_d(\mathbb Z_2)$ 保持 $\sigma_\mu$-同余及到 $\mathscr S_F(A)$ 的模 $2^M\mathcal O_\mu$ 距离。）
   构造块对角矩阵 $U=\operatorname{diag}(I_{n_1},\dots,Q_i,\dots,I_{n_r})$，其中 $Q_i=\operatorname{diag}(Q_i^{(2)},I_{n_i-2})$（当 $n_i=2$ 时即 $Q_i=Q_i^{(2)}$）：
   - **统一构造（适用于一切 $M\ge 3$ 与 $\mu\in\{-1,2\}$，以及 $M=2$ 且 $\mu=2$）**：
     观察 $1-\mu 2^{2M-2}$：
     - 当 $M\ge 3$ 时，$2M-2\ge 4$，故 $1-\mu 2^{2M-2}\equiv 1\pmod{16}$；
     - 当 $M=2,\ \mu=2$ 时，$1-2\cdot 2^2=-7\equiv 1\pmod 8$。
     于是在所有上述情形中，由完备 DVR $\mathbb Z_2$ 上的 Hensel 引理（$f(X)=X^2-(1-\mu 2^{2M-2})$，$x_0=1$ 满足 $v_2(f(1))\ge 3>2=2v_2(f'(1))$），存在唯一 $a=\sqrt{1-\mu 2^{2M-2}}\in 1+4\mathbb Z_2$（$M\ge 3$ 时甚至在 $1+8\mathbb Z_2$）。取
     $$Q_i^{(2)}=\begin{pmatrix} a & 2^{M-1}\theta_\mu\\ -2^{M-1}\theta_\mu & a\end{pmatrix}\in M_2(\mathcal O_\mu).$$
     逐项验证：
     1. $(Q_i^{(2)})^{\mathsf T}Q_i^{(2)}=(a^2+\mu 2^{2M-2})I_2=I_2$，且 $U$ 分块对角，故 $U^{\mathsf T}U=I_d$ 且 $[U^{\mathsf T}E_j U,E_k]=0$；
     2. $a\equiv 1\pmod 4$，$2^{M-1}\theta_\mu\in 2\mathcal O_\mu$（因 $M\ge 2$），故 $U\equiv I_d\pmod{2\mathcal O_\mu}$，即 $U\in\mathscr S_{K_\mu}(E)$；
     3. $\sigma_\mu(U)-U$ 的非零元仅为 $\mp 2^M\theta_\mu\in 2^M\mathcal O_\mu$，故 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$；
     4. 然而 $U$ 有元素 $2^{M-1}\theta_\mu$。对任意 $W\in\mathscr S_F(E)\subseteq M_d(\mathbb Z_2)$，若 $U\equiv W\pmod{2^M\mathcal O_\mu}$，则对应位置 $2^{M-1}\theta_\mu-w\in 2^M\mathcal O_\mu=2^M\mathbb Z_2\oplus 2^M\theta_\mu\mathbb Z_2$（$w\in\mathbb Z_2$），比较 $\theta_\mu$ 系数得 $2^{M-1}\in 2^M\mathbb Z_2$，矛盾！故不存在这样的 $W$，$N=M$ 失败。
   - **情形 $M=2,\ \mu=-1$ 的具体构造**：
     由完备 DVR $\mathcal O_{-1}$ 上的 Hensel 引理（$f(X)=X^2-(1-8\theta_{-1})$，$x_0=1$ 满足 $v_{\pi_{-1}}(8\theta_{-1})=6>4=2v_{\pi_{-1}}(2)$），存在唯一 $a\in\mathcal O_{-1}$ 满足 $a^2=1-8\theta_{-1}$ 与 $a\equiv 1\pmod{4\mathcal O_{-1}}$（显式地，令 $a=1+4z$ 则 $z=-\theta_{-1}-2z^2$ 为 $2$-进压缩，迭代即收敛至唯一解 $z\in\mathcal O_{-1}$）。取
     $$Q_i^{(2)}=\begin{pmatrix} a & 2+2\theta_{-1}\\ -(2+2\theta_{-1}) & a\end{pmatrix}\in M_2(\mathcal O_{-1}).$$
     验证：
     1. $a^2+(2+2\theta_{-1})^2=(1-8\theta_{-1})+(4+8\theta_{-1}-4)=1$，故 $(Q_i^{(2)})^{\mathsf T}Q_i^{(2)}=I_2$，从而 $U^{\mathsf T}U=I_d$ 且 $[U^{\mathsf T}E_j U,E_k]=0$；
     2. $a\equiv 1\pmod{4\mathcal O_{-1}}$ 与 $2+2\theta_{-1}\in 2\mathcal O_{-1}$ 给出 $U\equiv I_d\pmod{2\mathcal O_{-1}}$，故 $U\in\mathscr S_{K_{-1}}(E)$；
     3. $\sigma_{-1}(a)\equiv 1\equiv a\pmod{4\mathcal O_{-1}}$，且 $\sigma_{-1}(2+2\theta_{-1})=2-2\theta_{-1}=(2+2\theta_{-1})-4\theta_{-1}\equiv 2+2\theta_{-1}\pmod{4\mathcal O_{-1}}$，故 $\sigma_{-1}(U)\equiv U\pmod{4\mathcal O_{-1}}$；
     4. 然而 $(Q_i^{(2)})_{1,2}=2+2\theta_{-1}$。对任意 $W\in\mathscr S_F(E)\subseteq M_d(\mathbb Z_2)$，其 $(1,2)$ 位 $w\in\mathbb Z_2$ 与之差 $(2-w)+2\theta_{-1}$ 的 $\theta_{-1}$ 系数 $2\notin 4\mathbb Z_2$，故 $U\not\equiv W\pmod{4\mathcal O_{-1}}$。
   综上，当 $\max_i n_i\ge 2$ 时，$N_{\max}=M-1$ 对一切 $\mu\in\{-1,2\}$ 与 $M\ge 2$ 最优。

4. **给定 $(A,U)$ 能取 $N=M$ 的充要条件证明**：
   写作 $U=U_0+\theta_\mu U_1$（$U_0,U_1\in M_d(\mathbb Z_2)$），则 $\sigma_\mu(U)-U=-2\theta_\mu U_1$。因 $2^{M+1}\mathcal O_\mu=2^{M+1}\mathbb Z_2\oplus 2^{M+1}\theta_\mu\mathbb Z_2$，有
   $$\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}\iff -2U_1\in 2^{M+1}M_d(\mathbb Z_2)\iff U_1\in 2^M M_d(\mathbb Z_2)\iff U\bmod 2^M\mathcal O_\mu\in M_d(\mathbb Z/2^M\mathbb Z).$$
   - **必要性**：若存在 $W\in\mathscr S_F(A)\subseteq M_d(\mathbb Z_2)$ 使 $U\equiv W\pmod{2^M\mathcal O_\mu}$，则 $U\bmod 2^M\mathcal O_\mu=W\bmod 2^M\in M_d(\mathbb Z/2^M\mathbb Z)$，从而 $\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$。
   - **充分性**：若 $\bar U:=U\bmod 2^M\mathcal O_\mu\in M_d(\mathbb Z/2^M\mathbb Z)$，取其整提升 $\widehat U\in M_d(\mathbb Z_2)$（例如 $\widehat U=U_0$）。由 $U\in\mathscr S_{K_\mu}(A)$ 得 $\bar U\in\mathscr R_{K_\mu,M}(A)\subseteq\mathscr C_{K_\mu,M}(A)$。因 $\mathbb Z/2^M\mathbb Z\hookrightarrow \mathcal O_\mu/2^M\mathcal O_\mu$ 为单同态，矩阵方程组表明 $\bar U\in\mathscr C_{F,M}(A)$；再由定理 2(1) 应用于 $K_\mu$ 得 $(\widehat U^{\mathsf T}\widehat U)_{kk}\equiv 1\pmod{2^{M+1}\mathcal O_\mu}$（$\forall k$）。又因 $\widehat U\in M_d(\mathbb Z_2)$ 且 $\mathbb Z_2\cap 2^{M+1}\mathcal O_\mu=2^{M+1}\mathbb Z_2$，故 $(\widehat U^{\mathsf T}\widehat U)_{kk}\equiv 1\pmod{2^{M+1}\mathbb Z_2}$（$\forall k$）。再将定理 2(1) 应用于 $F$，即得 $\bar U\in\mathscr R_{F,M}(A)$，从而存在 $W\in\mathscr S_F(A)$ 满足 $W\equiv U\pmod{2^M\mathcal O_\mu}$。$\square$
