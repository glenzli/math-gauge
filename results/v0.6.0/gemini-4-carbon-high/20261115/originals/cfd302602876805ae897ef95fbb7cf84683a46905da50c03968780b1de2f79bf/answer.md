下面给出三个目标的完整解答与严格证明。

---

## 零、记号约定与结构约化引理

对给定的块秩参数 \(r,n_1,\ldots,n_r\in\mathbb Z_{\ge 1}\)（其中 \(d=\sum_{i=1}^r n_i\)），记以下两个仅依赖块秩的非负整数：
\[
\alpha := \sum_{i=1}^r \binom{n_i}{2} = \sum_{i=1}^r \frac{n_i(n_i-1)}{2},\qquad
\beta := \sum_{i=1}^r \binom{n_i+1}{2} = d + \alpha.
\]
对每个 \(L\in\{F,K_{-1},K_2\}\)，记分歧指数（亦即扩张次数）\(e_L := [L:F]\in\{1,2\}\)，即 \(e_F=1\)，\(e_{K_{-1}}=e_{K_2}=2\)。对任意交换环 \(R\) 与正整数 \(n\)，记：
- \(\operatorname{O}_n(R):=\{X\in M_n(R):X^{\mathsf T}X=I_n\}\)（由于 \(\det(X^{\mathsf T}X)=(\det X)^2=1\)，必有 \(\det X\in R^\times\)，故 \(X\in\operatorname{GL}_n(R)\) 且 \(X^{-1}=X^{\mathsf T}\)，从而自动有 \(XX^{\mathsf T}=I_n\)）；
- \(\operatorname{O}_n^{(1)}(R):=\{X\in\operatorname{O}_n(R):X\equiv I_n\pmod{2R}\}\)；
- \(\operatorname{Sym}_n(R):=\{Z\in M_n(R):Z^{\mathsf T}=Z\}\)，以及零对角对称矩阵空间 \(\operatorname{Sym}_n^0(\mathbb F_2):=\{Z\in\operatorname{Sym}_n(\mathbb F_2):Z_{pp}=0\ (\forall 1\le p\le n)\}\)。注意 \(\dim_{\mathbb F_2}\operatorname{Sym}_n(\mathbb F_2)=\binom{n+1}{2}\)，\(\dim_{\mathbb F_2}\operatorname{Sym}_n^0(\mathbb F_2)=\binom{n}{2}\)。

---

### 引理 0.1（二次扩域的整数环、一致化子与 \(\sigma_\mu\) 作用）

对 \(\mu\in\{-1,2\}\)，置
\[
\pi_2 := \theta_2,\qquad \pi_{-1} := 1+\theta_{-1}.
\]
则：
1. \(K_\mu/\mathbb Q_2\) 是全分歧二次扩张（\(e(K_\mu/\mathbb Q_2)=2\)，剩余域同构于 \(\mathbb F_2\)），\(\pi_\mu\) 是 \(K_\mu\) 的一致化子，且 \(K_\mu\) 的完整整数环恰为 \(\mathcal O_{K_\mu}=\mathcal O_\mu=\mathbb Z_2[\theta_\mu]=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu\)，最大理想为 \(\mathfrak p_\mu=\pi_\mu\mathcal O_\mu\)，并有 \(\pi_2^2=2\)、\(\pi_{-1}^2=2\theta_{-1}\)，从而 \(2\mathcal O_\mu=\pi_\mu^2\mathcal O_\mu\)。
2. 对每个整数 \(M\ge 1\)，自然映射给出自由 \(\mathbb Z_2/2^M\mathbb Z_2\)-模分解与 \(\sigma_\mu\)-作用：
   \[
   \mathcal O_\mu/2^M\mathcal O_\mu = (\mathbb Z_2/2^M\mathbb Z_2)\oplus(\mathbb Z_2/2^M\mathbb Z_2)\theta_\mu,\qquad
   \sigma_\mu(\bar x+\bar y\theta_\mu)=\bar x-\bar y\theta_\mu.
   \]
   特别地，\(\bar x+\bar y\theta_\mu\in(\mathcal O_\mu/2^M\mathcal O_\mu)^{\sigma_\mu}\) 当且仅当 \(2\bar y\equiv 0\pmod{2^M}\)，即 \(\bar y\in 2^{M-1}\mathbb Z_2/2^M\mathbb Z_2\)；而在 \(\mathcal O_\mu\) 中，\(\mathcal O_\mu^{\sigma_\mu}=\mathbb Z_2\)。
3. 设 \(g\in\mathbb Z_2^\times\) 满足 \(g\equiv 5\pmod 8\)。则对任意 \(L\in\{F,K_{-1},K_2\}\)，\(g\notin(L^\times)^2\)；进一步，对每个 \(\mu\in\{-1,2\}\)，模 \(8\mathcal O_\mu\) 的同余方程 \(z^2\equiv g\pmod{8\mathcal O_\mu}\) 在 \(\mathcal O_\mu/8\mathcal O_\mu\) 中无解。

**证明**：
1. 局部域标准定理表明：完备离散赋值域 \((F,\mathcal O_F,(\pi_F))\) 上，若 \(\pi\in\mathcal O_L\) 的极小多项式在 \(\mathcal O_F[x]\) 中是 Eisenstein 多项式，则 \(L/F\) 全分歧，\(\pi\) 为 \(\mathcal O_L\) 的一致化子且 \(\mathcal O_L=\mathcal O_F[\pi]\)。
   - 当 \(\mu=2\) 时，\(\pi_2=\theta_2\) 的极小多项式为 \(x^2-2\)，在 \(\mathbb Z_2[x]\) 中为 Eisenstein 多项式，故 \(\mathcal O_{K_2}=\mathbb Z_2[\theta_2]=\mathcal O_2\)。
   - 当 \(\mu=-1\) 时，\(\pi_{-1}=1+\theta_{-1}\) 满足 \(\pi_{-1}^2-2\pi_{-1}+2=\theta_{-1}^2+1=0\)，故极小多项式 \(x^2-2x+2\) 在 \(\mathbb Z_2[x]\) 中亦为 Eisenstein 多项式，从而 \(\mathcal O_{K_{-1}}=\mathbb Z_2[1+\theta_{-1}]=\mathbb Z_2[\theta_{-1}]=\mathcal O_{-1}\)，且 \(\pi_{-1}^2=2\theta_{-1}\)（其中 \(\theta_{-1}\in\mathcal O_{-1}^\times\)，因 \(\theta_{-1}(-\theta_{-1})=1\)）。
   故 \(2\mathcal O_\mu=\pi_\mu^2\mathcal O_\mu\)，且 \(\{1,\theta_\mu\}\) 为 \(\mathcal O_\mu\) 的 \(\mathbb Z_2\)-自由基。
2. 由 \(\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu\) 对 \(\mathbb Z_2/2^M\mathbb Z_2\) 作张量积即得模 \(2^M\mathcal O_\mu\) 的直和分解。由 \(\sigma_\mu(\bar x+\bar y\theta_\mu)-(\bar x+\bar y\theta_\mu)=-2\bar y\theta_\mu\)，它在 \(\mathcal O_\mu/2^M\mathcal O_\mu\) 中为零当且仅当 \(2\bar y\equiv 0\pmod{2^M}\)，即 \(\bar y\in 2^{M-1}\mathbb Z_2/2^M\mathbb Z_2\)；在无挠模 \(\mathcal O_\mu\) 中 \(-2y=0\iff y=0\)。
3. 若 \(z=a+b\theta_\mu\in\mathcal O_\mu\)（\(a,b\in\mathbb Z_2\)）满足 \(z^2\equiv g\equiv 5\pmod{8\mathcal O_\mu}\)，展开得
   \[
   (a^2+\mu b^2)+2ab\theta_\mu \equiv 5+0\cdot\theta_\mu\pmod{8\mathcal O_\mu},
   \]
   故 \(a^2+\mu b^2\equiv 5\pmod 8\) 且 \(2ab\equiv 0\pmod 8\)（即 \(ab\equiv 0\pmod 4\)）。分三种情形：
   - 若 \(2\mid a\) 且 \(2\mid b\)，则 \(a^2+\mu b^2\equiv 0\pmod 4\)，不可能模 \(8\) 余 \(5\)；
   - 若 \(4\mid b\)，则 \(b^2\equiv 0\pmod{16}\)，故 \(a^2\equiv 5\pmod 8\)，但奇数平方模 \(8\) 恒余 \(1\)，矛盾；
   - 若 \(4\mid a\)，则 \(a^2\equiv 0\pmod{16}\)，故 \(\mu b^2\equiv 5\pmod 8\)：当 \(\mu=2\) 时左端为偶数，矛盾；当 \(\mu=-1\) 时 \(b^2\equiv -5\equiv 3\pmod 8\)，仍矛盾。
   因此 \(z^2\equiv g\pmod{8\mathcal O_\mu}\) 无解。由于若 \(g\) 在 \(K_\mu\)（或 \(F\)）中为平方，则其平方根属于整闭包 \(\mathcal O_\mu\)，模 \(8\mathcal O_\mu\) 亦必有解，故 \(g\notin(L^\times)^2\)。\(\square\)

---

### 引理 0.2（标准对称正交幂等元族与同时分块条件的等价化归）

设 \(A=(A_1,\ldots,A_r)\) 为任意允许输入，定义多项式 \(f(X):=3X^2-2X^3\in\mathbb Z[X]\)。则：
1. 对每个 \(1\le i\le r\)，迭代序列 \(f^{\circ m}(A_i)\) 在 \(M_d(\mathbb Z_2)\) 中 \(2\)-进收敛于矩阵 \(P_i:=\lim_{m\to\infty}f^{\circ m}(A_i)\in M_d(\mathbb Z_2)\)。
2. 矩阵族 \((P_1,\ldots,P_r)\) 满足：
   \[
   P_i^{\mathsf T}=P_i,\qquad P_iP_j=\delta_{ij}P_i,\qquad \sum_{i=1}^r P_i=I_d,\qquad P_i\equiv E_i\pmod 2,\qquad P_iA_j=A_jP_i\ (\forall i,j).
   \]
3. 设 \(R\in\{\mathcal O_L,\ \mathcal O_L/2^M\mathcal O_L\}\)（其中 \(L\in\{F,K_{-1},K_2\}\)，\(M\ge 2\)），并设 \(U\in\operatorname{O}_d^{(1)}(R)\)。则在 \(M_d(R)\) 中，以下三条互相等价：
   \[
   \text{(a) }[U^{\mathsf T}A_iU,E_j]=0\ (\forall i,j);\qquad
   \text{(b) }U^{\mathsf T}P_iU=E_i\ (\forall i);\qquad
   \text{(c) }P_iU=UE_i\ (\forall i).
   \]

**证明**：
1. 令 \(D_0:=A_i^2-A_i\)。因 \(A_i\equiv E_i\pmod 2\) 且 \(E_i^2=E_i\)，有 \(D_0\in 2M_d(\mathbb Z_2)\)。对任意矩阵 \(X\)，记 \(D=X^2-X\)，直接验证多项式恒等式：
   \[
   f(X)-X = -D(2X-I_d),\qquad f(X)^2-f(X) = (3X^2-2X^3)^2-(3X^2-2X^3) = D^2(4D-3I_d).
   \]
   归纳知 \(D_m:=f^{\circ m}(A_i)^2-f^{\circ m}(A_i)\in 2^{2^m}M_d(\mathbb Z_2)\)，且 \(f^{\circ(m+1)}(A_i)-f^{\circ m}(A_i)\in 2^{2^m}M_d(\mathbb Z_2)\)。因 \(M_d(\mathbb Z_2)\) 是 \(2\)-进完备环，极限 \(P_i=\lim_{m\to\infty}f^{\circ m}(A_i)\in M_d(\mathbb Z_2)\) 存在，且 \(P_i^2-P_i=\lim_{m\to\infty}D_m=0\)，\(P_i\equiv A_i\equiv E_i\pmod 2\)。
2. 因每个 \(f^{\circ m}(A_i)\in\mathbb Z[A_i]\)，而 \(A_i^{\mathsf T}=A_i\) 且 \(A_iA_j=A_jA_i\)，故 \(f^{\circ m}(A_i)\) 对称且与所有 \(A_j\) 及 \(f^{\circ m'}(A_j)\) 交换；取 \(2\)-进极限即得 \(P_i^{\mathsf T}=P_i\)，\(P_iA_j=A_jP_i\)，\(P_iP_j=P_jP_i\)。
   当 \(i\ne j\) 时，\((P_iP_j)^2=P_i^2P_j^2=P_iP_j\) 为幂等矩阵，且 \(P_iP_j\equiv E_iE_j=0\pmod 2\)。故 \(I_d-P_iP_j\equiv I_d\pmod 2\) 在 \(M_d(\mathbb Z_2)\) 中可逆（逆为几何级数 \(\sum_{k\ge 0}(P_iP_j)^k\)），由 \((P_iP_j)(I_d-P_iP_j)=0\) 得 \(P_iP_j=0\)。
   记 \(S:=\sum_{i=1}^r P_i\)，由 \(P_iP_j=\delta_{ij}P_i\) 知 \(S^2=S\)，于是 \(I_d-S\) 亦为幂等矩阵，且 \(I_d-S\equiv I_d-\sum_{i=1}^r E_i=0\pmod 2\)，同理由 \(S\equiv I_d\pmod 2\) 可逆及 \(S(I_d-S)=0\) 得 \(S=I_d\)。
3. 因 \(U\in\operatorname{O}_d^{(1)}(R)\)，有 \(U^{\mathsf T}U=UU^{\mathsf T}=I_d\)，故 (b)\(\iff\)(c) 显然。
   - (a)\(\implies\)(b)：若对所有 \(i,j\) 有 \([U^{\mathsf T}A_iU,E_j]=0\)，由于 \(U^{\mathsf T}f^{\circ m}(A_i)U=f^{\circ m}(U^{\mathsf T}A_iU)\) 是 \(U^{\mathsf T}A_iU\) 的整系数多项式，故与 \(E_i\) 交换。在 \(R=\mathcal O_L\) 中取极限（或在 \(R=\mathcal O_L/2^M\mathcal O_L\) 中取充分大的 \(m\) 使 \(2^{2^m}\ge 2^M\)）得 \(Q_i:=U^{\mathsf T}P_iU\) 满足 \(Q_iE_i=E_iQ_i\)。又 \(Q_i^2=U^{\mathsf T}P_i^2U=Q_i\)，\(E_i^2=E_i\)，且 \(Q_i\equiv I_d^{\mathsf T}E_iI_d=E_i\pmod{2R}\)。令 \(\Delta_i:=Q_i-E_i\in 2M_d(R)\)，因 \(Q_iE_i=E_iQ_i\)，计算得
     \[
     \Delta_i^3 = Q_i^3-3Q_i^2E_i+3Q_iE_i^2-E_i^3 = Q_i-3Q_iE_i+3Q_iE_i-E_i = \Delta_i,
     \]
     即 \(\Delta_i(I_d-\Delta_i^2)=0\)。因 \(\Delta_i^2\in 4M_d(R)\) 在 \(R\) 中拓扑幂零（或幂零），\(I_d-\Delta_i^2\in\operatorname{GL}_d(R)\)，从而 \(\Delta_i=0\)，即 \(U^{\mathsf T}P_iU=E_i\)。
   - (b)\(\implies\)(a)：若对所有 \(j\) 有 \(U^{\mathsf T}P_jU=E_j\)，由 \(A_iP_j=P_jA_i\) 及 \(UU^{\mathsf T}=I_d\) 得
     \[
     (U^{\mathsf T}A_iU)E_j = U^{\mathsf T}A_iUU^{\mathsf T}P_jU = U^{\mathsf T}A_iP_jU = U^{\mathsf T}P_jA_iU = U^{\mathsf T}P_jUU^{\mathsf T}A_iU = E_j(U^{\mathsf T}A_iU),
     \]
     故 \([U^{\mathsf T}A_iU,E_j]=0\) 对全体 \(i,j\) 成立。\(\square\)

---

### 引理 0.3（逐块等距分解与 Gram 矩阵模 \(8\) 公式）

对每个 \(1\le i\le r\)，令 \(\iota_i:\mathbb Z_2^{n_i}\hookrightarrow\mathbb Z_2^d\) 为标准嵌入到坐标区间 \(I_i\) 的列矩阵（故 \(\iota_i\iota_i^{\mathsf T}=E_i\)，\(\iota_i^{\mathsf T}\iota_i=I_{n_i}\)），定义
\[
W_i := P_i\iota_i \in M_{d\times n_i}(\mathbb Z_2),\qquad
G_i := W_i^{\mathsf T}W_i = \iota_i^{\mathsf T}P_i\iota_i \in M_{n_i}(\mathbb Z_2).
\]
记 \(B_i:=\frac{1}{2}(A_i-E_i)\in M_d(\mathbb Z_2)\)，以及非对角分块 \(B_{i,12}:=\iota_i^{\mathsf T}B_i(I_d-E_i)\in M_{n_i\times(d-n_i)}(\mathbb Z_2)\)（其模 \(2\) 约化仅由 \(A_i\bmod 4\) 决定）。则：
1. \(G_i^{\mathsf T}=G_i\)，且有模 \(8\) 精确同余式
   \[
   G_i \equiv I_{n_i} - 4 B_{i,12}B_{i,12}^{\mathsf T} \equiv I_{n_i} + 4 B_{i,12}B_{i,12}^{\mathsf T} \pmod{8M_{n_i}(\mathbb Z_2)}.
   \]
   特别地，\(G_i\equiv I_{n_i}\pmod 4\)，故 \(G_i\in\operatorname{GL}_{n_i}(\mathbb Z_2)\)，且在 \(M_d(\mathbb Z_2)\) 中成立精确矩阵恒等式 \(P_i=W_iG_i^{-1}W_i^{\mathsf T}\)。
2. 对每个对称矩阵 \(G\in M_n(\mathbb Z_2)\)（\(G\equiv I_n\pmod 4\)）、每个 \(L\in\{F,K_{-1},K_2\}\) 及 \(M\ge 2\)，定义
   \[
   \mathcal I_L(G):=\left\{X\in M_n(\mathcal O_L):X\equiv I_n\pmod{2\mathcal O_L},\ X^{\mathsf T}GX=I_n\right\},
   \]
   \[
   \mathcal I_{L,M}(G):=\left\{\bar X\in M_n(\mathcal O_L/2^M\mathcal O_L):\bar X\equiv I_n\pmod{2\mathcal O_L},\ \bar X^{\mathsf T}G\bar X\equiv I_n\pmod{2^M\mathcal O_L}\right\}.
   \]
   则映射 \((X_1,\ldots,X_r)\mapsto U:=\sum_{i=1}^r W_iX_i\iota_i^{\mathsf T}\)（即以 \(W_iX_i\) 为第 \(I_i\) 块列）给出保持模 \(2^N\) 同余关系且与 \(\sigma_\mu\) 作用等变的双射：
   \[
   \prod_{i=1}^r \mathcal I_L(G_i) \xrightarrow{\;\sim\;} \mathscr S_L(A),\qquad
   \prod_{i=1}^r \mathcal I_{L,M}(G_i) \xrightarrow{\;\sim\;} \mathscr C_{L,M}(A),
   \]
   其逆映射为 \(U\mapsto (G_1^{-1}\iota_1^{\mathsf T}U\iota_1,\ldots,G_r^{-1}\iota_r^{\mathsf T}U\iota_r)\)；进而 \(\mathscr R_{L,M}(A)\) 对应于 \(\prod_{i=1}^r \operatorname{im}(\mathcal I_L(G_i)\to\mathcal I_{L,M}(G_i))\)。

**证明**：
1. 在相对于 \(I_i\) 与 \([d]\setminus I_i\) 的分块下（不妨重排坐标仅作辅助记号），写 \(P_i=\begin{pmatrix}P_{11}&P_{12}\\ P_{12}^{\mathsf T}&P_{22}\end{pmatrix}\)，其中 \(P_{11}=G_i\equiv I_{n_i}\pmod 2\)，\(P_{12}\equiv 0\pmod 2\)，\(P_{22}\equiv 0\pmod 2\)。在引理 0.2 的第一步迭代中，将 \(A_i=E_i+2B_i\) 代入 \(f(X)=3X^2-2X^3\)：
   \[
   f(A_i) = E_i + 2(E_iB_i+B_iE_i-2E_iB_iE_i) + 4(3B_i^2-2E_iB_i^2-2B_iE_iB_i-2B_i^2E_i) - 16B_i^3 \equiv E_i + 2(E_iB_i(I_d-E_i)+(I_d-E_i)B_iE_i)\pmod 4.
   \]
   因 \(D_1=f(A_i)^2-f(A_i)=D_0^2(4D_0-3I_d)\in 4M_d(\mathbb Z_2)\)，故 \(P_i\equiv f(A_i)\pmod 4\)。由此知 \(P_{12}=2C_i\)，其中 \(C_i\in M_{n_i\times(d-n_i)}(\mathbb Z_2)\) 满足 \(C_i\equiv B_{i,12}\pmod 2\)。
   由 \(P_i^2=P_i\) 的左上块得 \(G_i^2+4C_iC_i^{\mathsf T}=G_i\)，即 \(G_i(I_{n_i}-G_i)=4C_iC_i^{\mathsf T}\)。因 \(G_i\equiv I_{n_i}\pmod 2\) 可逆，先由上式模 \(4\) 得 \(I_{n_i}-G_i\equiv 0\pmod 4\)，即 \(G_i\equiv I_{n_i}\pmod 4\)，从而 \(G_i^{-1}\equiv I_{n_i}\pmod 4\)；再模 \(16\) 得 \(I_{n_i}-G_i=G_i^{-1}(4C_iC_i^{\mathsf T})\equiv 4C_iC_i^{\mathsf T}\pmod{16}\)。写 \(C_i=B_{i,12}+2K\)，则
   \[
   4C_iC_i^{\mathsf T} = 4B_{i,12}B_{i,12}^{\mathsf T} + 8(B_{i,12}K^{\mathsf T}+KB_{i,12}^{\mathsf T}) + 16KK^{\mathsf T} \equiv 4B_{i,12}B_{i,12}^{\mathsf T}\pmod 8,
   \]
   故 \(G_i\equiv I_{n_i}-4B_{i,12}B_{i,12}^{\mathsf T}\equiv I_{n_i}+4B_{i,12}B_{i,12}^{\mathsf T}\pmod 8\)。
   进一步，幂等元 \(P_i\in M_d(\mathbb Z_2)\) 的像 \(\operatorname{im}(P_i)\) 是自由 \(\mathbb Z_2\)-模 \(\mathbb Z_2^d\) 的直和项，故自身为自由 \(\mathbb Z_2\)-模；模 \(2\) 张量 \(\mathbb F_2\) 后像为 \(\operatorname{im}(E_i)=\mathbb F_2^{I_i}\)，故 \(\operatorname{rk}_{\mathbb Z_2}\operatorname{im}(P_i)=n_i\)。算子 \(W_iG_i^{-1}W_i^{\mathsf T}\in M_d(\mathbb Z_2)\) 对称幂等（因 \((W_iG_i^{-1}W_i^{\mathsf T})^2=W_iG_i^{-1}(W_i^{\mathsf T}W_i)G_i^{-1}W_i^{\mathsf T}=W_iG_i^{-1}W_i^{\mathsf T}\)），其像包含于 \(\operatorname{im}(P_i)\)；而 \(\iota_i^{\mathsf T}W_i=G_i\in\operatorname{GL}_{n_i}(\mathbb Z_2)\) 说明 \(W_i:\mathbb Z_2^{n_i}\to\operatorname{im}(P_i)\) 是同秩自由 \(\mathbb Z_2\)-模间的满同态（因与 \(\iota_i^{\mathsf T}|_{\operatorname{im}(P_i)}\) 复合为同构），从而 \(W_i\) 是同构，\(\operatorname{im}(W_iG_i^{-1}W_i^{\mathsf T})=\operatorname{im}(W_i)=\operatorname{im}(P_i)\)。两个具有相同像的对称幂等阵必相等，故 \(P_i=W_iG_i^{-1}W_i^{\mathsf T}\)。
2. 设 \(R\in\{\mathcal O_L,\mathcal O_L/2^M\mathcal O_L\}\)。对 \(U\in M_d(R)\)，记第 \(i\) 块列 \(U_i:=U\iota_i\in M_{d\times n_i}(R)\)。由引理 0.2(3)，条件 \(P_iU=UE_i\ (\forall i)\) 等价于 \(P_iU_i=U_i\ (\forall i)\)（若 \(P_iU_i=U_i\)，则对 \(j\ne i\) 有 \(P_jU_i=P_jP_iU_i=0\)，故 \(P_jU=\sum_i P_jU_i\iota_i^{\mathsf T}=U_j\iota_j^{\mathsf T}=UE_j\)）。
   若 \(P_iU_i=U_i\)，令 \(X_i:=G_i^{-1}\iota_i^{\mathsf T}U_i\in M_{n_i}(R)\)；因 \(\iota_i^{\mathsf T}P_i=\iota_i^{\mathsf T}W_iG_i^{-1}W_i^{\mathsf T}=W_i^{\mathsf T}\)，有 \(W_iX_i=W_iG_i^{-1}W_i^{\mathsf T}U_i=P_iU_i=U_i\)。反之，对任意 \(X_i\in M_{n_i}(R)\)，置 \(U_i=W_iX_i\)，则 \(P_iU_i=P_i^2\iota_iX_i=U_i\) 且 \(G_i^{-1}\iota_i^{\mathsf T}U_i=G_i^{-1}G_iX_i=X_i\)。
   在此一一对应下：
   - 因 \(W_i=P_i\iota_i\equiv E_i\iota_i=\iota_i\pmod 2\)，有 \(U=\sum_i W_iX_i\iota_i^{\mathsf T}\equiv \sum_i \iota_iX_i\iota_i^{\mathsf T}\pmod{2R}\)，故 \(U\equiv I_d\pmod{2R}\iff X_i\equiv I_{n_i}\pmod{2R}\ (\forall i)\)；
   - \(U^{\mathsf T}U\) 的 \((i,j)\)-块为 \(U_i^{\mathsf T}U_j=X_i^{\mathsf T}W_i^{\mathsf T}W_jX_j\)：当 \(i\ne j\) 时 \(W_i^{\mathsf T}W_j=\iota_i^{\mathsf T}P_iP_j\iota_j=0\) 自动成立；当 \(i=j\) 时恰为 \(X_i^{\mathsf T}G_iX_i\)。故 \(U^{\mathsf T}U=I_d\iff X_i^{\mathsf T}G_iX_i=I_{n_i}\ (\forall i)\)。
   最后，因 \(W_i,G_i\) 的元素均属于 \(\mathbb Z_2\)（在 \(\sigma_\mu\) 下逐项不动），该双射及其逆映射与 \(\sigma_\mu\) 交换，且对任意 \(N\ge 0\) 有 \(U\equiv U'\pmod{2^N}\iff X_i\equiv X'_i\pmod{2^N}\ (\forall i)\)。\(\square\)

---

## 一、目标 1 的解答与证明

### 定理 1（可行性判准、精确基数与可提升性判准）

对每个 \(1\le i\le r\)，由 \(A_i\bmod 4\) 定义有限可计算的模 \(2\) 不变量：
\[
\tau_i(A) := \sum_{p\in I_i}\sum_{q\in [d]\setminus I_i} \left(\frac{A_i-E_i}{2}\right)_{pq} \bmod 2 \in \mathbb F_2
\]
（等价地，\(\tau_i(A)\) 是 \(A_i\bmod 4\) 在非对角矩形区域 \(I_i\times([d]\setminus I_i)\) 中取值为 \(2\bmod 4\) 的元素个数模 \(2\)；当 \(r=1\) 时空和约定为 \(\tau_1(A)=0\)）。记条件
\[
\Phi(A):\qquad \tau_1(A)=\tau_2(A)=\cdots=\tau_r(A)=0.
\]
对任意允许输入 \(A\)、任意 \(L\in\{F,K_{-1},K_2\}\)（记 \(e_L=[L:F]\in\{1,2\}\)）及任意整数 \(M\ge 2\)：

1. **\(\mathscr S_L(A)\) 的可行性判准**：
   \[
   \mathscr S_L(A)\ne\varnothing \iff \Phi(A)\text{ 成立（即 }\forall 1\le i\le r,\ \tau_i(A)=0\text{）}.
   \]
   特别地，三个域 \(F,K_{-1},K_2\) 上的非空性完全一致；当 \(r=1\) 时 \(\mathscr S_L(A)\) 恒非空，当 \(r\ge 2\) 时存在允许输入使 \(\mathscr S_L(A)=\varnothing\)。

2. **\(\mathscr R_{L,M}(A)\) 与 \(\mathscr C_{L,M}(A)\) 的空集条件与闭式精确基数**（其中 \(\alpha=\sum_{i=1}^r\binom{n_i}{2}\)，\(\beta=d+\alpha=\sum_{i=1}^r\binom{n_i+1}{2}\)）：
   - **对 \(\mathscr R_{L,M}(A)\)（任意 \(M\ge 2\)）**：\(\mathscr R_{L,M}(A)=\varnothing \iff \Phi(A)\) 不成立；基数为
     \[
     |\mathscr R_{L,M}(A)| = \begin{cases}
     2^{r + e_L(M-1)\alpha}, & \text{若 }\Phi(A)\text{ 成立},\\
     0, & \text{若 }\Phi(A)\text{ 不成立}.
     \end{cases}
     \]
   - **对 \(\mathscr C_{L,2}(A)\)（\(M=2\)）**：对**一切**允许输入 \(A\) 均非空（即使 \(\Phi(A)\) 不成立），且基数恒为
     \[
     |\mathscr C_{L,2}(A)| = 2^{e_L\beta} = 2^{e_L(d+\alpha)}.
     \]
   - **对 \(\mathscr C_{L,M}(A)\)（\(M\ge 3\)）**：\(\mathscr C_{L,M}(A)=\varnothing \iff \Phi(A)\) 不成立；基数为
     \[
     |\mathscr C_{L,M}(A)| = \begin{cases}
     2^{e_L d + r + e_L(M-1)\alpha}, & \text{若 }\Phi(A)\text{ 成立},\\
     0, & \text{若 }\Phi(A)\text{ 不成立}.
     \end{cases}
     \]

3. **\(\bar U\in\mathscr C_{L,M}(A)\) 属于 \(\mathscr R_{L,M}(A)\) 的可核验充要条件**：
   对给定的 \(\bar U\in\mathscr C_{L,M}(A)\)，任取其到 \(M_d(\mathcal O_L)\)（或仅到 \(M_d(\mathcal O_L/2^{M+1}\mathcal O_L)\)）的一个逐条目代表矩阵 \(\hat U\)。则同余条件
   \[
   (\hat U^{\mathsf T}\hat U - I_d)_{qq} \equiv 0 \pmod{2^{M+1}\mathcal O_L}\qquad (\forall 1\le q\le d)
   \]
   的真假与代表元 \(\hat U\) 的选取无关，且它是 \(\bar U\in\mathscr R_{L,M}(A)\) 的**必要充分条件**。

---

### 定理 1 的证明

#### 第一步：可行性判准与基点平移约化

记 \(S_i:=B_{i,12}B_{i,12}^{\mathsf T}\in M_{n_i}(\mathbb Z_2)\)。在模 \(2\) 下，
\[
\operatorname{tr}(S_i) = \sum_{p\in I_i}\sum_{q\notin I_i}(B_i)_{pq}^2 \equiv \sum_{p\in I_i}\sum_{q\notin I_i}(B_i)_{pq} = \tau_i(A)\pmod 2.
\]
对矩阵 \(G_i\equiv I_{n_i}+4S_i\pmod 8\) 展开行列式：对称群 \(S_{n_i}\) 中非恒等置换至少移动两个指标，故对应项至少含两个非对角因子 \(4(S_i)_{p,\pi(p)}\)，从而被 \(16\) 整除；主对角乘积为 \(\prod_{p=1}^{n_i}(1+4(S_i)_{pp})\equiv 1+4\operatorname{tr}(S_i)\pmod{16}\)。于是
\[
\det G_i \equiv 1 + 4\tau_i(A) \pmod 8.
\]

- **必要性（及 \(M\ge 3\) 时 \(\mathscr C_{L,M}(A)\) 的空集性）**：
  若存在 \(i\) 使 \(\tau_i(A)=1\)，则 \(\det G_i\equiv 5\pmod 8\)。若 \(\mathscr C_{L,M}(A)\ne\varnothing\)（\(M\ge 3\)），由引理 0.3(2) 知存在 \(\bar X_i\in\mathcal I_{L,M}(G_i)\)，模 \(8\mathcal O_L\) 约化后取行列式得 \((\det\bar X_i)^2\det G_i\equiv 1\pmod{8\mathcal O_L}\)。两边同乘 \(5\)（注意 \(\det G_i\cdot 5\equiv 25\equiv 1\pmod 8\)）得 \((5\det\bar X_i)^2\equiv 5\pmod{8\mathcal O_L}\)，与引理 0.1(3) 矛盾！故当 \(\Phi(A)\) 不成立时，对所有 \(M\ge 3\) 有 \(\mathscr C_{L,M}(A)=\varnothing\)，从而 \(\mathscr S_L(A)=\varnothing\) 且对所有 \(M\ge 2\) 有 \(\mathscr R_{L,M}(A)=\varnothing\)。

- **充分性（\(\Phi(A)\implies \mathscr S_F(A)\ne\varnothing\)）**：
  设对所有 \(1\le i\le r\) 有 \(\tau_i(A)=0\)。固定 \(i\)，记 \(n=n_i\)，我们来构造 \(X_{i,0}\in\mathcal I_F(G_i)\subseteq M_n(\mathbb Z_2)\)。
  因 \(\sum_{p=1}^n (S_i)_{pp}\equiv\tau_i(A)=0\pmod 2\)，集合 \(\{p\in\{1,\ldots,n\}:(S_i)_{pp}\equiv 1\pmod 2\}\) 具有偶数个元素，记为无交二元对的并 \(\{p_1,q_1\}\sqcup\cdots\sqcup\{p_k,q_k\}\)（\(0\le 2k\le n\)；特别地当 \(n=1\) 时 \(k=0\)）。
  取 \(Y_0\in\operatorname{Sym}_n(\mathbb Z_2)\)，使其在每个 \((p_t,q_t)\) 与 \((q_t,p_t)\) 处为 \(1\)，其余位置全为 \(0\)。则 \(Y_0^2\) 为对角阵，在 \(\{p_1,q_1,\ldots,p_k,q_k\}\) 的对角元上为 \(1\)，其余为 \(0\)，即对所有 \(p\) 有 \((Y_0^2)_{pp}\equiv (S_i)_{pp}\pmod 2\)。计算
  \[
  (I_n+2Y_0)^{\mathsf T}G_i(I_n+2Y_0) \equiv (I_n+2Y_0)(I_n+4S_i)(I_n+2Y_0) \equiv I_n + 4(Y_0+Y_0^2+S_i)\pmod 8.
  \]
  矩阵 \(T:=Y_0+Y_0^2+S_i\) 对称且对角元全为偶数，故模 \(8\) 可写为 \(I_n+4T'\)，其中 \(T'\in\operatorname{Sym}_n(\mathbb Z_2)\) 对角元全为 \(0\)。取严格上三角整数矩阵 \(Y_1\) 使 \(p<q\) 时 \((Y_1)_{pq}=T'_{pq}\)，则 \(Y_1+Y_1^{\mathsf T}=T'\)，于是令 \(X^{(1)}:=(I_n+2Y_0)(I_n+4Y_1)\equiv I_n\pmod 2\)，有
  \[
  G'_i := (X^{(1)})^{\mathsf T}G_iX^{(1)} \equiv (I_n+4Y_1^{\mathsf T})(I_n+4T')(I_n+4Y_1) \equiv I_n + 4(T'+Y_1+Y_1^{\mathsf T}) = I_n+8T' \equiv I_n\pmod 8.
  \]
  写 \(G'_i=I_n+8H\)（\(H\in\operatorname{Sym}_n(\mathbb Z_2)\)）。利用二项式级数系数恒等式 \(\binom{-1/2}{m}=\frac{(-1)^m}{4^m}\binom{2m}{m}\)，对每个 \(m\ge 1\) 有 \(v_2\bigl(\binom{-1/2}{m}8^m\bigr)=3m-2m+v_2\binom{2m}{m}\ge m\ge 1\)（且 \(m=1\) 时恰为 \(-4H\equiv 0\pmod 4\)），故级数
  \[
  (G'_i)^{-1/2} := \sum_{m=0}^\infty \binom{-1/2}{m} 8^m H^m
  \]
  在 \(M_n(\mathbb Z_2)\) 中收敛，对称，与 \(G'_i\) 交换，满足 \((G'_i)^{-1/2}\equiv I_n\pmod 4\) 且 \((G'_i)^{-1/2}G'_i(G'_i)^{-1/2}=I_n\)。令 \(X_{i,0}:=X^{(1)}(G'_i)^{-1/2}\in M_n(\mathbb Z_2)\)，则 \(X_{i,0}\equiv I_n\pmod 2\) 且 \(X_{i,0}^{\mathsf T}G_iX_{i,0}=I_n\)，即 \(X_{i,0}\in\mathcal I_F(G_i)\)。
  由引理 0.3(2)，\(U_0:=\sum_{i=1}^r W_iX_{i,0}\iota_i^{\mathsf T}\in\mathscr S_F(A)\subseteq\mathscr S_L(A)\)，故可行性判准得证。

- **可行情形下的主同余正交群同构**：
  当 \(\Phi(A)\) 成立时，固定上述 \(U_0\in\mathscr S_F(A)\)。对任意 \(R\in\{\mathcal O_L,\mathcal O_L/2^M\mathcal O_L\}\)，在引理 0.3(2) 中作左乘代换 \(X_i = X_{i,0}Q_i\)，因 \(X_{i,0}\in M_{n_i}(\mathbb Z_2)\) 满足 \(X_{i,0}\equiv I_{n_i}\pmod 2\) 且 \(X_{i,0}^{\mathsf T}G_iX_{i,0}=I_{n_i}\)，有 \(X_i\in\mathcal I_R(G_i)\iff Q_i\in\operatorname{O}_{n_i}^{(1)}(R)\)，且此时
  \[
  U = \sum_{i=1}^r W_iX_{i,0}Q_i\iota_i^{\mathsf T} = \left(\sum_{i=1}^r W_iX_{i,0}\iota_i^{\mathsf T}\right)\left(\sum_{j=1}^r \iota_jQ_j\iota_j^{\mathsf T}\right) = U_0\cdot\operatorname{diag}(Q_1,\ldots,Q_r).
  \]
  因 \(U_0\in\operatorname{O}_d^{(1)}(\mathbb Z_2)\) 在 \(\sigma_\mu\) 下不动，映射 \((Q_1,\ldots,Q_r)\mapsto U_0\operatorname{diag}(Q_1,\ldots,Q_r)\) 给出 \(\sigma_\mu\)-等变且保持一切模 \(2^N\) 同余的双射：
  \[
  \prod_{i=1}^r \operatorname{O}_{n_i}^{(1)}(\mathcal O_L) \xrightarrow{\;\sim\;} \mathscr S_L(A),\qquad
  \prod_{i=1}^r \operatorname{O}_{n_i}^{(1)}(\mathcal O_L/2^M\mathcal O_L) \xrightarrow{\;\sim\;} \mathscr C_{L,M}(A).
  \]

#### 第二步：主 Hensel 提升引理与可提升性判准（定理 1(3)）

我们先证明核心提升性质：对任意 \(L\in\{F,K_{-1},K_2\}\)、任意 \(M\ge 2\) 及任意允许输入 \(A\)，设 \(\bar U\in\mathscr C_{L,M}(A)\)。
1. **对角同余式对代表元选取的不变性**：
   设 \(\hat U,\hat U'\in M_d(\mathcal O_L)\) 均为 \(\bar U\) 的提升，则 \(\hat U'=\hat U+2^M\Psi\)（\(\Psi\in M_d(\mathcal O_L)\)）。展开得
   \[
   (\hat U')^{\mathsf T}\hat U'-I_d = (\hat U^{\mathsf T}\hat U-I_d) + 2^M(\hat U^{\mathsf T}\Psi+\Psi^{\mathsf T}\hat U) + 2^{2M}\Psi^{\mathsf T}\Psi.
   \]
   因 \(M\ge 2\implies 2M\ge M+2>M+1\)，且对每个对角指标 \(1\le q\le d\) 有 \((\hat U^{\mathsf T}\Psi+\Psi^{\mathsf T}\hat U)_{qq}=2(\hat U^{\mathsf T}\Psi)_{qq}\in 2\mathcal O_L\)，故 \(2^M(\hat U^{\mathsf T}\Psi+\Psi^{\mathsf T}\hat U)_{qq}\in 2^{M+1}\mathcal O_L\)。因此
   \[
   ((\hat U')^{\mathsf T}\hat U'-I_d)_{qq} \equiv (\hat U^{\mathsf T}\hat U-I_d)_{qq} \pmod{2^{M+1}\mathcal O_L}\qquad (\forall 1\le q\le d),
   \]
   与代表元选取完全无关。
2. **必要性**：
   若 \(\bar U\in\mathscr R_{L,M}(A)\)，则存在真正解 \(U\in\mathscr S_L(A)\) 作为 \(\bar U\) 的代表元；由 \(U^{\mathsf T}U=I_d\) 及上述不变性，对任意代表元 \(\hat U\) 均有 \((\hat U^{\mathsf T}\hat U-I_d)_{qq}\equiv (U^{\mathsf T}U-I_d)_{qq}=0\pmod{2^{M+1}\mathcal O_L}\)。
3. **充分性（及一步提升等价于无穷步提升）**：
   反之，设 \(\bar U\in\mathscr C_{L,M}(A)\) 对某（从而任意）代表元 \(\hat U\) 满足 \((\hat U^{\mathsf T}\hat U-I_d)_{qq}\equiv 0\pmod{2^{M+1}\mathcal O_L}\ (\forall q)\)（特别地，即便仅设 \(\bar U\) 可提升为 \(\bar U_1\in\mathscr C_{L,M+1}(A)\)，取 \(\bar U_1\) 的代表元作为 \(\hat U\) 亦满足该式）。
   由引理 0.3(2)，\(\bar U\) 对应于 \((\bar X_1,\ldots,\bar X_r)\in\prod_{i=1}^r\mathcal I_{L,M}(G_i)\)。取 \(\bar X_i\) 到 \(M_{n_i}(\mathcal O_L)\) 的提升 \(\tilde X_i\)，并置特定代表元 \(\tilde U:=\sum_{i=1}^r W_i\tilde X_i\iota_i^{\mathsf T}\in M_d(\mathcal O_L)\)。因 \(\tilde U^{\mathsf T}\tilde U-I_d\) 的第 \(I_i\times I_i\) 对角块恰为 \(\tilde X_i^{\mathsf T}G_i\tilde X_i-I_{n_i}\)，由代表元不变性知：对每个 \(i\)，对称矩阵
   \[
   H^{(0)}_i := \frac{\tilde X_i^{\mathsf T}G_i\tilde X_i - I_{n_i}}{2^M} \in \operatorname{Sym}_{n_i}(\mathcal O_L)
   \]
   的所有对角元均属于 \(2\mathcal O_L\)！
   我们对精度 \(m\ge M\) 归纳构造序列 \(X_i^{(m)}\in M_{n_i}(\mathcal O_L)\)（初值 \(X_i^{(M)}:=\tilde X_i\)），使其满足：
   - \(X_i^{(m)}\equiv I_{n_i}\pmod{2\mathcal O_L}\)，\(X_i^{(m+1)}\equiv X_i^{(m)}\pmod{2^m\mathcal O_L}\)；
   - \((X_i^{(m)})^{\mathsf T}G_iX_i^{(m)}=I_{n_i}+2^m H_i^{(m)}\)，其中 \(H_i^{(m)}\in\operatorname{Sym}_{n_i}(\mathcal O_L)\) 且对所有 \(1\le p\le n_i\) 有 \((H_i^{(m)})_{pp}\in 2\mathcal O_L\)。
   归纳步（\(m\ge M\ge 2\)）：写 \((H_i^{(m)})_{pp}=2h_p\)（\(h_p\in\mathcal O_L\)）。取矩阵 \(Z\in M_{n_i}(\mathcal O_L)\) 为：
   \[
   Z_{pp} := -h_p,\qquad Z_{pq} := -(H_i^{(m)})_{pq}\ (p<q),\qquad Z_{pq} := 0\ (p>q),
   \]
   并置 \(X_i^{(m+1)}:=X_i^{(m)}(I_{n_i}+2^m Z)\)。注意 \(Z+Z^{\mathsf T}\) 在非对角处等于 \(-H_i^{(m)}\)，在对角 \((p,p)\) 处等于 \(-2h_p=-(H_i^{(m)})_{pp}\)，即 \(H_i^{(m)}+Z+Z^{\mathsf T}=0\)！
   另一方面，因 \(X_i^{(m)}\equiv I_{n_i}\pmod{2\mathcal O_L}\) 且 \(G_i\equiv I_{n_i}\pmod 4\)，有 \((X_i^{(m)})^{\mathsf T}G_iX_i^{(m)}=I_{n_i}+2^m H_i^{(m)}\equiv I_{n_i}\pmod{4\mathcal O_L}\)。计算：
   \[
   (X_i^{(m+1)})^{\mathsf T}G_iX_i^{(m+1)} = (I_{n_i}+2^m Z^{\mathsf T})(I_{n_i}+2^m H_i^{(m)})(I_{n_i}+2^m Z)
   = I_{n_i} + 2^m(H_i^{(m)}+Z+Z^{\mathsf T}) + 2^{2m}(Z^{\mathsf T}H_i^{(m)}+H_i^{(m)}Z+Z^{\mathsf T}Z+2^m Z^{\mathsf T}H_i^{(m)}Z).
   \]
   因 \(H_i^{(m)}+Z+Z^{\mathsf T}=0\)，上式等于 \(I_{n_i}+2^{m+1}H_i^{(m+1)}\)，其中
   \[
   H_i^{(m+1)} := 2^{m-1}\bigl(Z^{\mathsf T}H_i^{(m)}+H_i^{(m)}Z+Z^{\mathsf T}Z+2^m Z^{\mathsf T}H_i^{(m)}Z\bigr).
   \]
   由于 \(m\ge M\ge 2\)，有 \(m-1\ge 1\)，故**整个矩阵** \(H_i^{(m+1)}\in 2^{m-1}M_{n_i}(\mathcal O_L)\subseteq 2M_{n_i}(\mathcal O_L)\)，其对角元自然属于 \(2\mathcal O_L\)！
   由 \(\mathcal O_L\) 的 \(2\)-进完备性，极限 \(X_i:=\lim_{m\to\infty}X_i^{(m)}\in\mathcal I_L(G_i)\) 存在且满足 \(X_i\equiv\tilde X_i\equiv\bar X_i\pmod{2^M\mathcal O_L}\)。令 \(U:=\sum_{i=1}^r W_iX_i\iota_i^{\mathsf T}\in\mathscr S_L(A)\)，即有 \(U\bmod 2^M\mathcal O_L=\bar U\in\mathscr R_{L,M}(A)\)。
   这也同时证明了对一切 \(M\ge 2\) 有 \(\operatorname{im}(\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A))=\mathscr R_{L,M}(A)\)。

#### 第三步：精确基数的计算（定理 1(2)）

注意到 \(|\mathcal O_L/2\mathcal O_L|=2^{e_L}\)（对 \(F\) 为 \(2\)，对 \(K_\mu\) 为 \(4\)）。

1. **\(M=2\) 时 \(|\mathscr C_{L,2}(A)|\) 与 \(|\mathscr R_{L,2}(A)|\)**：
   对任意允许输入 \(A\)，因 \(G_i\equiv I_{n_i}\pmod 4\)，在 \(\mathcal I_{L,2}(G_i)\) 中写 \(\bar X_i=I_{n_i}+2Y_i\)（\(Y_i\in M_{n_i}(\mathcal O_L/2\mathcal O_L)\)），则
   \[
   \bar X_i^{\mathsf T}G_i\bar X_i \equiv (I_{n_i}+2Y_i^{\mathsf T})(I_{n_i}+2Y_i) \equiv I_{n_i}+2(Y_i+Y_i^{\mathsf T})\pmod{4\mathcal O_L},
   \]
   该式模 \(4\mathcal O_L\) 为 \(I_{n_i}\) 当且仅当 \(Y_i\in\operatorname{Sym}_{n_i}(\mathcal O_L/2\mathcal O_L)\)。作为自由 \(\mathcal O_L/2\mathcal O_L\)-模，\(\operatorname{Sym}_{n_i}(\mathcal O_L/2\mathcal O_L)\) 的秩为 \(\binom{n_i+1}{2}\)，故 \(|\mathcal I_{L,2}(G_i)|=(2^{e_L})^{\binom{n_i+1}{2}}\)。连乘 \(1\le i\le r\) 即得：对一切允许输入 \(A\)，
   \[
   |\mathscr C_{L,2}(A)| = \prod_{i=1}^r 2^{e_L\binom{n_i+1}{2}} = 2^{e_L\beta}\ne 0.
   \]
   当 \(\Phi(A)\) 成立时，利用第一步的同构只需对 \(G_i=I_n\)（记 \(n=n_i\)）计算 \(|\operatorname{im}(\operatorname{O}_n^{(1)}(\mathcal O_L)\to\operatorname{O}_n^{(1)}(\mathcal O_L/4\mathcal O_L))|\)。对 \(\bar X=I_n+2Y\)（\(Y\in\operatorname{Sym}_n(\mathcal O_L/2\mathcal O_L)\)），取提升 \(\hat X=I_n+2\hat Y\)，模 \(8\mathcal O_L\) 展开：
   \[
   \hat X^{\mathsf T}\hat X - I_n \equiv 4(\hat Y + \hat Y^2)\pmod{8\mathcal O_L}.
   \]
   由第二步判准，\(\bar X\) 可提升当且仅当对所有 \(1\le p\le n\) 有 \((Y+Y^2)_{pp}\equiv 0\pmod{2\mathcal O_L}\)。
   - 当 \(L=F\) 时，\(Y\in\operatorname{Sym}_n(\mathbb F_2)\)，\((Y+Y^2)_{pp}=Y_{pp}+\sum_{q=1}^n Y_{pq}^2\equiv \sum_{q\ne p}Y_{pq}\pmod 2\)。这 \(n\) 个线性方程关于 \(\binom{n}{2}\) 个非对角自由元 \(\{Y_{pq}:p<q\}\) 的总和模 \(2\) 恒为 \(2\sum_{p<q}Y_{pq}\equiv 0\)，且任取前 \(n-1\) 个方程（第 \(p\) 个方程含独立变元 \(Y_{pn}\)，\(1\le p\le n-1\)）线性无关，故方程组秩为 \(n-1\)（当 \(n=1\) 时为空方程 \(0\equiv 0\)，秩亦为 \(0=n-1\)）。因此可提升元个数为 \(2^{\binom{n+1}{2}-(n-1)}=2^{1+\binom{n}{2}}\)。
   - 当 \(L=K_\mu\) 时，写 \(Y=Y_0+\theta_\mu Y_1\)（\(Y_0,Y_1\in\operatorname{Sym}_n(\mathbb F_2)\)），则模 \(2\mathcal O_\mu\) 有
     \[
     Y+Y^2 = (Y_0+Y_0^2+\mu Y_1^2) + \theta_\mu(Y_1+Y_0Y_1+Y_1Y_0).
     \]
     对角 \((p,p)\) 处的 \(\theta_\mu\)-系数为 \((Y_1)_{pp}+2(Y_0Y_1)_{pp}\equiv (Y_1)_{pp}\pmod 2\)，故先给出 \(n\) 个独立方程 \((Y_1)_{pp}=0\ (\forall p)\)。在此条件下，\(1\)-系数在对角 \((p,p)\) 处为 \(\sum_{q\ne p}(Y_0)_{pq}+\mu\sum_{q\ne p}(Y_1)_{pq}\equiv 0\pmod 2\)，同样是秩为 \(n-1\) 的齐次线性方程组。总秩为 \(n+(n-1)=2n-1\)，故可提升元个数为 \(2^{2\binom{n+1}{2}-(2n-1)}=2^{1+2\binom{n}{2}}\)。
   统一写作 \(2^{1+e_L\binom{n_i}{2}}\)，对 \(1\le i\le r\) 连乘得 \(|\mathscr R_{L,2}(A)|=2^{r+e_L\alpha}\)。

2. **\(M\ge 2\) 时提升纤维与 \(M\ge 3\) 的归纳计数**：
   设 \(\Phi(A)\) 成立，考虑归约映射 \(\operatorname{red}_M:\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A)\)，其像已证为 \(\mathscr R_{L,M}(A)\)。任取 \(\bar U\in\mathscr R_{L,M}(A)\)，选取一个真正解提升 \(U\in\mathscr S_L(A)\)。任意位于 \(\bar U\) 上方的 \(\bar U_1\in\mathscr C_{L,M+1}(A)\) 可唯一写作 \(\bar U_1=U(I_d+2^M Z)\bmod 2^{M+1}\mathcal O_L\)，其中 \(Z\in M_d(\mathcal O_L/2\mathcal O_L)\)。
   - 条件 \(\bar P_i\bar U_1\equiv\bar U_1 E_i\pmod{2^{M+1}\mathcal O_L}\)：因 \(P_iU=UE_i\) 且 \(2^M U\equiv 2^M I_d\pmod{2^{M+1}\mathcal O_L}\)，等价于 \(2^M UE_iZ\equiv 2^M UZE_i\pmod{2^{M+1}\mathcal O_L}\)，即 \(E_iZ=ZE_i\) 在 \(M_d(\mathcal O_L/2\mathcal O_L)\) 中对全体 \(i\) 成立，亦即 \(Z=\operatorname{diag}(Z_1,\ldots,Z_r)\)，\(Z_i\in M_{n_i}(\mathcal O_L/2\mathcal O_L)\)。
   - 条件 \(\bar U_1^{\mathsf T}\bar U_1\equiv I_d\pmod{2^{M+1}\mathcal O_L}\)：因 \(U^{\mathsf T}U=I_d\) 且 \(2M>M+1\)，展开为 \(I_d+2^M(Z+Z^{\mathsf T})\equiv I_d\pmod{2^{M+1}\mathcal O_L}\)，即每个 \(Z_i\in\operatorname{Sym}_{n_i}(\mathcal O_L/2\mathcal O_L)\)。
   因此，\(\mathscr C_{L,M+1}(A)\twoheadrightarrow\mathscr R_{L,M}(A)\) 的**每个非空纤维大小恒为** \(\prod_{i=1}^r |\operatorname{Sym}_{n_i}(\mathcal O_L/2\mathcal O_L)| = 2^{e_L\beta}\)，从而
   \[
   |\mathscr C_{L,M+1}(A)| = 2^{e_L\beta}\cdot |\mathscr R_{L,M}(A)|.
   \]
   再对任意 \(m\ge 3\) 比较 \(|\mathscr C_{L,m}(A)|\) 与 \(|\mathscr R_{L,m}(A)|\)：令对角群 \((\mathcal O_L/2\mathcal O_L)^d\) 通过 \(\bar U\mapsto \bar U(I_d+2^{m-1}D)\)（\(D=\operatorname{diag}(\delta_1,\ldots,\delta_d)\)）右乘作用于 \(\mathscr C_{L,m}(A)\)。因 \(m\ge 3\implies 2m-2\ge m+1\)，有：
   - \(D\) 与全体 \(E_j\) 交换，故保持同时分块条件；
   - \(\bigl(\hat U(I_d+2^{m-1}\hat D)\bigr)^{\mathsf T}\bigl(\hat U(I_d+2^{m-1}\hat D)\bigr) - I_d \equiv (\hat U^{\mathsf T}\hat U-I_d) + 2^m\hat D \pmod{2^{m+1}\mathcal O_L}\)。
   模 \(2^m\mathcal O_L\) 下这说明作用保持 \(\mathscr C_{L,m}(A)\) 且自由；模 \(2^{m+1}\mathcal O_L\) 下说明在对角模 \(2^{m+1}\mathcal O_L\) 阻碍向量上该作用单传递地平移 \(2^m(\mathcal O_L/2\mathcal O_L)^d\)。故每个大小为 \((2^{e_L})^d=2^{e_L d}\) 的轨道中**恰有唯一**一个元素满足第二步的对角消没判准（属于 \(\mathscr R_{L,m}(A)\)）！于是对一切 \(m\ge 3\) 有
   \[
   |\mathscr R_{L,m}(A)| = 2^{-e_L d}|\mathscr C_{L,m}(A)|.
   \]
   联立递推式 \(|\mathscr R_{L,m+1}(A)|=2^{-e_L d}\cdot 2^{e_L(d+\alpha)}|\mathscr R_{L,m}(A)|=2^{e_L\alpha}|\mathscr R_{L,m}(A)|\)（\(m\ge 2\)）及初值 \(|\mathscr R_{L,2}(A)|=2^{r+e_L\alpha}\)，归纳立得对所有 \(M\ge 2\) 有 \(|\mathscr R_{L,M}(A)|=2^{r+e_L(M-1)\alpha}\)，且对所有 \(M\ge 3\) 有 \(|\mathscr C_{L,M}(A)|=2^{e_L d+r+e_L(M-1)\alpha}\)。\(\square\)

---

### 关于目标 1 中否定情形的具体例子

1. **\(\mathscr S_L(A)=\varnothing\)（从而 \(\mathscr R_{L,M}(A)=\varnothing\)，且 \(M\ge 3\) 时 \(\mathscr C_{L,M}(A)=\varnothing\)）的允许输入实例**：
   只要 \(r\ge 2\)，任取 \(p_0\in I_1\)、\(q_0\in I_2\)，记 \(J:=E_{p_0q_0}+E_{q_0p_0}\in\operatorname{Sym}_d(\mathbb Z)\)（标准矩阵单位之和），令
   \[
   A_1 := E_1 + 2J,\qquad A_2 := E_2 - 2J,\qquad A_k := E_k\ (3\le k\le r).
   \]
   直接验证：各 \(A_i\) 对称，\(A_i\equiv E_i\pmod 2\)（且 \(A_1^2=E_1+2J+4(E_{p_0p_0}+E_{q_0q_0})\ne A_1\) 非幂等）；对 \(k\ge 3\) 有 \(A_kA_1=A_1A_k=0\)，\(A_kA_2=A_2A_k=0\)，而
   \[
   A_1A_2 = (E_1+2J)(E_2-2J) = 2(E_1(-J)+JE_2)-4J^2 = 2(-E_{p_0q_0}+E_{p_0q_0})-4(E_{p_0p_0}+E_{q_0q_0}) = -4(E_{p_0p_0}+E_{q_0q_0}) = A_2A_1,
   \]
   故 \(A\) 是合法输入。此时 \(\tau_1(A)=\tau_2(A)=1\ne 0\)，故对所有 \(L\in\{F,K_{-1},K_2\}\) 有 \(\mathscr S_L(A)=\varnothing\)，\(\mathscr R_{L,M}(A)=\varnothing\)（\(\forall M\ge 2\)），\(\mathscr C_{L,M}(A)=\varnothing\)（\(\forall M\ge 3\)），而 \(\mathscr C_{L,2}(A)\ne\varnothing\)（例如 \(\bar U=I_d+2J\bmod 4\mathcal O_L\in\mathscr C_{L,2}(A)\)，其对角阻碍 \(((\hat U^{\mathsf T}\hat U-I_d)_{p_0p_0})_{p_0}=4\not\equiv 0\pmod 8\)）。

2. **\(\Phi(A)\) 成立时 \(\mathscr R_{L,M}(A)\subsetneq\mathscr C_{L,M}(A)\) 的判别与实例**：
   比较定理 1 的基数可知，当 \(\Phi(A)\) 成立时，\(\mathscr R_{L,M}(A)=\mathscr C_{L,M}(A)\) **当且仅当** \(L=F\)、\(M=2\) 且 \(n_1=\cdots=n_r=1\)（此时 \(d=r,\alpha=0\)，两者基数均为 \(2^r\)）；其余一切情形均有真包含 \(\mathscr R_{L,M}(A)\subsetneq\mathscr C_{L,M}(A)\)，具体反例可取 \(A=(E_1,\ldots,E_r)\)：
   - 当 \(M\ge 3\)（任意 \(L\)、任意 \(d\ge 1\)）：取 \(\bar U = I_d + 2^{M-1}E_{11}\bmod 2^M\mathcal O_L\in\mathscr C_{L,M}(A)\)，有 \((\hat U^{\mathsf T}\hat U-I_d)_{11}=2^M+2^{2M-2}\equiv 2^M\not\equiv 0\pmod{2^{M+1}\mathcal O_L}\)，故 \(\bar U\notin\mathscr R_{L,M}(A)\)；
   - 当 \(M=2\) 且 \(L=K_\mu\)（任意 \(d\ge 1\)）：取 \(\bar U = I_d + 2\theta_\mu E_{11}\bmod 4\mathcal O_\mu\in\mathscr C_{K_\mu,2}(A)\)，有 \((\hat U^{\mathsf T}\hat U-I_d)_{11}=4\theta_\mu+4\mu\equiv 4\theta_\mu+4\mu\not\equiv 0\pmod{8\mathcal O_\mu}\)，故 \(\bar U\notin\mathscr R_{K_\mu,2}(A)\)；
   - 当 \(M=2\)、\(L=F\) 且存在 \(i_0\) 使 \(n_{i_0}\ge 2\)：取 \(p\ne q\in I_{i_0}\)，令 \(\bar U = I_d + 2(E_{pq}+E_{qp})\bmod 4\in\mathscr C_{F,2}(A)\)，有 \((\hat U^{\mathsf T}\hat U-I_d)_{pp}=4\not\equiv 0\pmod 8\)，故 \(\bar U\notin\mathscr R_{F,2}(A)\)。

---

## 二、目标 2 的解答与证明

为简洁书写分块对角扰动，引入分块对角嵌入记号：对 \(Z=(Z_1,\ldots,Z_r)\in\bigoplus_{i=1}^r M_{n_i}(\mathbb F_2)\)，将其等同于分块对角矩阵 \(\sum_{i=1}^r \iota_i Z_i\iota_i^{\mathsf T}\in M_d(\mathbb F_2)\)，从而将 \(\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\) 与 \(\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\) 视为 \(M_d(\mathbb F_2)\) 的分块对角对称矩阵子群（维数分别为 \(\beta\) 与 \(\alpha\)）。

### 定理 2（\(\sigma_\mu\)-固定集、轨道数、约化纤维与相容提升刻画）

固定 \(\mu\in\{-1,2\}\) 及 \(M\ge 2\)，记一致化子 \(\pi_2=\theta_2\)，\(\pi_{-1}=1+\theta_{-1}\)。

1. **具体矩阵类及与基域集合的精确关系**：
   - **对 \(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\)**（对一切允许输入 \(A\) 及 \(M\ge 2\)）：
     \[
     \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
     = \left\{\bar X + 2^{M-1}\theta_\mu \bar Z \bmod 2^M\mathcal O_\mu : \bar X\in\mathscr C_{F,M}(A),\ \bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\right\}
     = \left\{\bar X(I_d + 2^{M-1}\theta_\mu \bar Z) \bmod 2^M\mathcal O_\mu : \bar X\in\mathscr C_{F,M}(A),\ \bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\right\},
     \]
     且每个元素对应的 \((\bar X,\bar Z)\) 唯一。基域集合经自然包含恰为其中无 \(\theta_\mu\) 分量的子集：\(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z_2/2^M\mathbb Z_2)=\mathscr C_{F,M}(A)\)，而投射 \(\bar X+2^{M-1}\theta_\mu\bar Z\mapsto\bar X\) 使 \(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\) 成为 \(\mathscr C_{F,M}(A)\) 上以初等阿贝尔 \(2\)-群 \(2^{M-1}\theta_\mu\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\cong\mathbb F_2^\beta\) 为结构群的平凡主丛。特别当 \(M=2\) 时，\(\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}=\mathscr C_{K_\mu,2}(A)\)（\(\sigma_\mu\) 在精度 \(2\) 上恒平凡作用）。
   - **对 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)**：若 \(\Phi(A)\) 不成立，则 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr R_{F,M}(A)=\varnothing\)；若 \(\Phi(A)\) 成立，则对一切 \(M\ge 2\) 及 \(\mu\in\{-1,2\}\) 有统一刻画：
     \[
     \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
     = \left\{\bar X' + 2^{M-1}\pi_\mu \bar Z \bmod 2^M\mathcal O_\mu : \bar X'\in\mathscr R_{F,M}(A),\ \bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\right\}
     = \left\{\bar X'(I_d + 2^{M-1}\pi_\mu \bar Z) \bmod 2^M\mathcal O_\mu : \bar X'\in\mathscr R_{F,M}(A),\ \bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\right\},
     \]
     且每个元素对应的 \((\bar X',\bar Z)\) 唯一。按 \(\{1,\theta_\mu\}\)-基分解 \(\bar U=\bar X+2^{M-1}\theta_\mu\bar Z\) 写出时：
     - 当 **\(M\ge 3\)（任意 \(\mu\)）或 \(M=2,\mu=2\)** 时，\(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr R_{F,M}(A)+2^{M-1}\theta_\mu\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\)（即 \(\bar X\in\mathscr R_{F,M}(A)\)）；
     - 当 **\(M=2\) 且 \(\mu=-1\)** 时，\(\bar X+2\theta_{-1}\bar Z\in\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}\iff \bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\) 且 \(\bar X+2\bar Z\in\mathscr R_{F,2}(A)\)（此时若 \(\bar Z\) 存在某行元素和模 \(2\) 为 \(1\)，则 \(1\)-分量 \(\bar X\in\mathscr C_{F,2}(A)\setminus\mathscr R_{F,2}(A)\) 本身并不属于 \(\mathscr R_{F,2}(A)\)）。
     在一切情形下，\(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z_2/2^M\mathbb Z_2)=\mathscr R_{F,M}(A)\)（对应 \(\bar Z=0\)），且 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr R_{F,M}(A)\) 成立当且仅当 \(\Phi(A)\) 不成立或 \(n_1=\cdots=n_r=1\)（即 \(\alpha=0\)）；当 \(M=2\) 时亦有 \(\mathscr R_{K_\mu,2}(A)^{\sigma_\mu}=\mathscr R_{K_\mu,2}(A)\)。

2. **固定点数与 \(\langle\sigma_\mu\rangle\) 轨道数**：
   - **对 \(\mathscr C_{K_\mu,M}(A)\)**：
     - 当 \(M=2\) 时（对一切允许输入 \(A\)）：
       \[
       |\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}| = 2^{2\beta} = 2^{2(d+\alpha)},\qquad
       |\mathscr C_{K_\mu,2}(A)/\langle\sigma_\mu\rangle| = 2^{2\beta} = 2^{2(d+\alpha)}.
       \]
     - 当 \(M\ge 3\) 时：若 \(\Phi(A)\) 不成立，固定点数与轨道数均为 \(0\)；若 \(\Phi(A)\) 成立：
       \[
       |\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}| = 2^{2d + r + M\alpha},\qquad
       |\mathscr C_{K_\mu,M}(A)/\langle\sigma_\mu\rangle| = 2^{2d + r - 1 + 2(M-1)\alpha} + 2^{2d + r - 1 + M\alpha}.
       \]
   - **对 \(\mathscr R_{K_\mu,M}(A)\)（任意 \(M\ge 2\)）**：若 \(\Phi(A)\) 不成立，固定点数与轨道数均为 \(0\)；若 \(\Phi(A)\) 成立：
     \[
     |\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}| = 2^{r + M\alpha},\qquad
     |\mathscr R_{K_\mu,M}(A)/\langle\sigma_\mu\rangle| = 2^{r - 1 + 2(M-1)\alpha} + 2^{r - 1 + M\alpha}.
     \]

3. **从精度 \(M+1\) 到 \(M\)（\(M\ge 2\)）的约化像与全部非空纤维大小**：
   记模 \(2^M\mathcal O_L\) 约化映射为 \(\operatorname{red}_M\)。
   - 若 \(\Phi(A)\) 不成立：因 \(M+1\ge 3\)，精度 \(M+1\) 处的全部集合均为空集，故各约化像全为 \(\varnothing\)，不存在非空纤维。
   - 若 \(\Phi(A)\) 成立：以下全部映射的**所有非空纤维大小均整齐一致**（无大小差异）：
     1. \(\operatorname{red}_M:\mathscr R_{L,M+1}(A)\to\mathscr R_{L,M}(A)\)（\(L\in\{F,K_{-1},K_2\}\)）：约化像为全集 \(\mathscr R_{L,M}(A)\)，每个非空纤维大小为 \(2^{e_L\alpha}\)（即 \(L=F\) 时为 \(2^\alpha\)，\(L=K_\mu\) 时为 \(2^{2\alpha}=4^\alpha\)）。
     2. \(\operatorname{red}_M:\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A)\)（\(L\in\{F,K_{-1},K_2\}\)）：约化像为 \(\mathscr R_{L,M}(A)\)，每个非空纤维大小为 \(2^{e_L\beta}=2^{e_L(d+\alpha)}\)（即 \(L=F\) 时为 \(2^\beta\)，\(L=K_\mu\) 时为 \(2^{2\beta}=4^\beta\)）。
     3. \(\operatorname{red}_M:\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)：约化像恰为基域子集 \(\mathscr R_{F,M}(A)\)，每个非空纤维大小为 \(2^{2\alpha}=4^\alpha\)。
     4. \(\operatorname{red}_M:\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\)：约化像亦恰为基域子集 \(\mathscr R_{F,M}(A)\)，每个非空纤维大小为 \(2^{2\beta}=4^\beta\)。

4. **提升为 \(\sigma_\mu\)-固定真正解与逐层相容固定序列分量的刻画**：
   无论在 \(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\) 中还是在 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\) 中考察，以下四个子集**完全重合**，且皆等于自然嵌入下的基域集合 \(\mathscr R_{F,M}(A)\)：
   - 能提升为 \(\sigma_\mu\)-固定真正解 \(U\in\mathscr S_{K_\mu}(A)^{\sigma_\mu}\) 的矩阵类；
   - 能作为 \(\prod_{k\ge 2}\mathscr R_{K_\mu,k}(A)^{\sigma_\mu}\)（或 \(\prod_{k\ge M}\mathscr R_{K_\mu,k}(A)^{\sigma_\mu}\)）中逐层相容序列 \((\bar U_k)\)（\(\operatorname{red}_k(\bar U_{k+1})=\bar U_k\)）在精度 \(M\) 处分量 \(\bar U_M\) 的矩阵类；
   - 能作为 \(\prod_{k\ge 2}\mathscr C_{K_\mu,k}(A)^{\sigma_\mu}\)（或 \(\prod_{k\ge M}\mathscr C_{K_\mu,k}(A)^{\sigma_\mu}\)）中逐层相容序列在精度 \(M\) 处分量 \(\bar U_M\) 的矩阵类；
   - 仅向上相容一步（即属于 \(\operatorname{im}(\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu})\)）的矩阵类。
   具体核验判准为：
   - 对 \(\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)：\(\bar U\in\mathscr R_{F,M}(A)\iff \bar U\in M_d(\mathbb Z_2/2^M\mathbb Z_2)\)（即其 \(\theta_\mu\)-分量为 \(0\)）；
   - 对 \(\bar U\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\)：\(\bar U\in\mathscr R_{F,M}(A)\iff \bar U\in M_d(\mathbb Z_2/2^M\mathbb Z_2)\) 且任取代表元 \(\hat U\in M_d(\mathbb Z_2)\) 有 \((\hat U^{\mathsf T}\hat U-I_d)_{qq}\equiv 0\pmod{2^{M+1}\mathbb Z_2}\ (\forall 1\le q\le d)\)。

---

### 定理 2 的证明

1. **\(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\) 的矩阵类结构**：
   由引理 0.1(2)，\(\bar U\in M_d(\mathcal O_\mu/2^M\mathcal O_\mu)\) 被 \(\sigma_\mu\) 固定当且仅当可唯一写作 \(\bar U=\bar X+2^{M-1}\theta_\mu\bar Z\)，其中 \(\bar X\in M_d(\mathbb Z_2/2^M\mathbb Z_2)\)，\(\bar Z\in M_d(\mathbb F_2)\)。注意当 \(\bar X\equiv I_d\pmod 2\) 时，因 \(2^{M-1}\bar X\equiv 2^{M-1}I_d\pmod{2^M}\)，加法形式 \(\bar X+2^{M-1}\theta_\mu\bar Z\) 与右乘形式 \(\bar X(I_d+2^{M-1}\theta_\mu\bar Z)\) 模 \(2^M\mathcal O_\mu\) 完全相同。
   将 \(\bar U=\bar X+2^{M-1}\theta_\mu\bar Z\) 代入 \(\mathscr C_{K_\mu,M}(A)\) 的定义条件（结合引理 0.2(3)）：
   - 因 \(M\ge 2\implies 2^{M-1}\equiv 0\pmod 2\)，有 \(\bar U\equiv I_d\pmod{2\mathcal O_\mu}\iff \bar X\equiv I_d\pmod 2\)；
   - 因 \(P_i,E_i\) 系矩阵元在 \(\mathbb Z_2\) 中，\(\bar P_i\bar U\equiv\bar UE_i\pmod{2^M\mathcal O_\mu}\) 按 \(\{1,\theta_\mu\}\)-基分解等价于 \(\bar P_i\bar X\equiv\bar XE_i\pmod{2^M}\) 与 \(2^{M-1}P_i\bar Z\equiv 2^{M-1}\bar ZE_i\pmod{2^M}\)。由 \(P_i\equiv E_i\pmod 2\)，后者等价于 \(E_i\bar Z=\bar ZE_i\) 在 \(M_d(\mathbb F_2)\) 中对所有 \(i\) 成立，即 \(\bar Z\in\bigoplus_{i=1}^r M_{n_i}(\mathbb F_2)\) 分块对角；
   - 展开正交性（利用 \(M\ge 2\implies 2M-2\ge M\)，故 \(2^{2M-2}\mu\equiv 0\pmod{2^M}\)）：
     \[
     \bar U^{\mathsf T}\bar U = \bar X^{\mathsf T}\bar X + 2^{2M-2}\mu\bar Z^{\mathsf T}\bar Z + 2^{M-1}\theta_\mu(\bar X^{\mathsf T}\bar Z+\bar Z^{\mathsf T}\bar X)
     \equiv \bar X^{\mathsf T}\bar X + 2^{M-1}\theta_\mu(\bar Z+\bar Z^{\mathsf T})\pmod{2^M\mathcal O_\mu},
     \]
     其中用到了 \(\bar X\equiv I_d\pmod 2\)。按 \(\{1,\theta_\mu\}\)-基分离得 \(\bar X^{\mathsf T}\bar X\equiv I_d\pmod{2^M}\)（从而 \(\bar X\in\mathscr C_{F,M}(A)\)）且 \(\bar Z+\bar Z^{\mathsf T}=0\)（从而 \(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\)）。这证明了 \(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\) 的精确刻画及基数公式 \(|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}|=2^\beta|\mathscr C_{F,M}(A)|\)。

2. **\(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\) 的矩阵类结构**：
   设 \(\Phi(A)\) 成立。
   - 先证每个形如 \(\bar U=\bar X'+2^{M-1}\pi_\mu\bar Z\bmod 2^M\mathcal O_\mu\)（\(\bar X'\in\mathscr R_{F,M}(A)\)，\(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\)）的矩阵类属于 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)：
     因 \(\pi_2=\theta_2\)，\(\pi_{-1}=1+\theta_{-1}\)，无论哪种情形均有 \(2^{M-1}\pi_\mu\bar Z\in(\mathcal O_\mu/2^M\mathcal O_\mu)^{\sigma_\mu}\)，故 \(\sigma_\mu(\bar U)=\bar U\)。取 \(\bar X'\) 的真正解提升 \(U'\in\mathscr S_F(A)\) 及 \(\bar Z\) 的对称零对角提升 \(\hat Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb Z_2)\)（对所有 \(q\) 有 \(\hat Z_{qq}=0\)），令 \(\tilde U:=U'(I_d+2^{M-1}\pi_\mu\hat Z)\in M_d(\mathcal O_\mu)\)。因 \(U'\equiv I_d\pmod 2\)，有 \(\tilde U\equiv \bar X'+2^{M-1}\pi_\mu\bar Z=\bar U\pmod{2^M\mathcal O_\mu}\)。又因 \([\hat Z,E_i]=0\) 且 \(P_iU'=U'E_i\)，有 \(P_i\tilde U=\tilde UE_i\)。最后计算
     \[
     \tilde U^{\mathsf T}\tilde U - I_d = (I_d+2^{M-1}\pi_\mu\hat Z)(U')^{\mathsf T}U'(I_d+2^{M-1}\pi_\mu\hat Z) - I_d = 2^M\pi_\mu\hat Z + 2^{2M-2}\pi_\mu^2\hat Z^2.
     \]
     由 \(\hat Z_{qq}=0\) 知第一项对角元全为 \(0\)；由 \(\pi_\mu^2\in 2\mathcal O_\mu\)（引理 0.1(1)）及 \(M\ge 2\implies 2M-1\ge M+1\)，知 \(2^{2M-2}\pi_\mu^2\in 2^{2M-1}\mathcal O_\mu\subseteq 2^{M+1}\mathcal O_\mu\)，故 \(\tilde U\bmod 2^M\mathcal O_\mu\in\mathscr C_{K_\mu,M}(A)\) 且对所有 \(q\) 满足 \((\tilde U^{\mathsf T}\tilde U-I_d)_{qq}\equiv 0\pmod{2^{M+1}\mathcal O_\mu}\)。由定理 1(3) 得 \(\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)。
   - 再证单射性与满射性：
     在 \(\bar X'+2^{M-1}\pi_\mu\bar Z\) 中，其 \(\theta_\mu\)-系数恰为 \(2^{M-1}\bar Z\bmod 2^M\)（因 \(\pi_2\) 与 \(\pi_{-1}\) 的 \(\theta_\mu\)-系数皆为 \(1\)），故 \(\bar Z\in M_d(\mathbb F_2)\) 唯一确定，继而 \(\bar X'=\bar U-2^{M-1}\pi_\mu\bar Z\bmod 2^M\) 亦唯一确定，因此该映射单射，给出至少 \(2^\alpha|\mathscr R_{F,M}(A)|=2^{r+M\alpha}\) 个不同元素。
     反之，任取 \(\bar U=\bar X+2^{M-1}\theta_\mu\bar Z\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\subseteq\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\)，取代表元 \(\hat U=\hat X+2^{M-1}\theta_\mu\hat Z\)，展开
     \[
     (\hat U^{\mathsf T}\hat U-I_d)_{qq} = (\hat X^{\mathsf T}\hat X-I_d)_{qq} + 2^{2M-2}\mu(\hat Z^2)_{qq} + 2^M\theta_\mu(\hat X^{\mathsf T}\hat Z)_{qq}.
     \]
     模 \(2^{M+1}\mathcal O_\mu\) 令 \(\theta_\mu\)-部分消没，因 \(\hat X\equiv I_d\pmod 2\)，得 \(2^M\bar Z_{qq}\equiv 0\pmod{2^{M+1}}\)，故对一切 \(q\) 必有 \(\bar Z_{qq}=0\)，即 \(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\)。接着考察 \(1\)-部分：
     - 当 \(M\ge 3\) 或 \(M=2,\mu=2\) 时，\(2M-2+v_2(\mu)\ge M+1\)，故 \(2^{2M-2}\mu\equiv 0\pmod{2^{M+1}}\)，得 \((\hat X^{\mathsf T}\hat X-I_d)_{qq}\equiv 0\pmod{2^{M+1}}\)，即 \(\bar X\in\mathscr R_{F,M}(A)\)（且当 \(M\ge 3,\mu=-1\) 时，因 \(\bar Z\) 零对角且 \(2M-2\ge M+1\)，\(\bar X'=\bar X-2^{M-1}\bar Z\) 同样属于 \(\mathscr R_{F,M}(A)\)）；
     - 当 \(M=2,\mu=-1\) 时，令 \(\hat X':=\hat X+2\hat Z\)（代表 \(\bar X':=\bar X+2\bar Z\in\mathscr C_{F,2}(A)\)），因 \(\hat Z_{qq}=0\)，有 \(((\hat X')^{\mathsf T}\hat X'-I_d)_{qq}=(\hat X^{\mathsf T}\hat X-I_d)_{qq}+4(\hat X^{\mathsf T}\hat Z)_{qq}+4(\hat Z^2)_{qq}\equiv (\hat X^{\mathsf T}\hat X-I_d)_{qq}-4(\hat Z^2)_{qq}\equiv 0\pmod 8\)，故 \(\bar X'=\bar U-2\pi_{-1}\bar Z\in\mathscr R_{F,2}(A)\)。
     因此满射性亦成立，且 \(|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}|=2^\alpha|\mathscr R_{F,M}(A)|=2^{r+M\alpha}\)。

3. **\(\langle\sigma_\mu\rangle\) 轨道数**：
   因 \(\sigma_\mu\) 是对合（\(\sigma_\mu^2=\operatorname{id}\)），对任意有限 \(\langle\sigma_\mu\rangle\)-集 \(\mathcal X\)，轨道大小仅能为 \(1\)（固定点）或 \(2\)（非固定对），故由 Burnside 引理（或轨道计数）恒有
   \[
   |\mathcal X/\langle\sigma_\mu\rangle| = |\mathcal X^{\sigma_\mu}| + \frac{|\mathcal X|-|\mathcal X^{\sigma_\mu}|}{2} = \frac{|\mathcal X|+|\mathcal X^{\sigma_\mu}|}{2}.
   \]
   将定理 1(2) 的 \(|\mathscr C_{K_\mu,M}(A)|,|\mathscr R_{K_\mu,M}(A)|\) 与上已求得的固定点数代入即得定理 2(2) 的全部闭式公式。

4. **精度 \(M+1\to M\) 的约化像与非空纤维大小**：
   设 \(\Phi(A)\) 成立。
   - 对 \(\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A)\)，其像为 \(\mathscr R_{L,M}(A)\) 且每个非空纤维大小为 \(2^{e_L\beta}\) 已在定理 1 的第二步与第三步中严格证毕。
   - 对 \(\mathscr R_{L,M+1}(A)\to\mathscr R_{L,M}(A)\)，由定义 \(\mathscr R_{L,m}(A)=\operatorname{im}(\mathscr S_L(A)\to\mathscr C_{L,m}(A))\) 知必满射；经基点平移 \(U_0^{-1}(\cdot)\) 后，该映射等同于有限群满同态 \(\prod_{i=1}^r\operatorname{im}(\operatorname{O}_{n_i}^{(1)}(\mathcal O_L)\bmod 2^{M+1})\twoheadrightarrow\prod_{i=1}^r\operatorname{im}(\operatorname{O}_{n_i}^{(1)}(\mathcal O_L)\bmod 2^M)\)，故所有纤维均为核群的陪集，大小恒等于商值 \(|\mathscr R_{L,M+1}(A)|/|\mathscr R_{L,M}(A)|=2^{e_L\alpha}\)。
   - 对 \(\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\)：由第 1 条，任意 \(\bar U_{M+1}\in\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\) 唯一表为 \(\bar X_{M+1}+2^M\theta_\mu\bar Z\)（\(\bar X_{M+1}\in\mathscr C_{F,M+1}(A)\)，\(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\)）。模 \(2^M\mathcal O_\mu\) 约化时，\(2^M\theta_\mu\bar Z\equiv 0\pmod{2^M\mathcal O_\mu}\) 完全消去，故 \(\operatorname{red}_M(\bar U_{M+1})=\operatorname{red}_M(\bar X_{M+1})\)。当 \(\bar X_{M+1}\) 遍历 \(\mathscr C_{F,M+1}(A)\) 时，\(\operatorname{red}_M(\bar X_{M+1})\) 恰遍历 \(\operatorname{im}(\mathscr C_{F,M+1}(A)\to\mathscr C_{F,M}(A))=\mathscr R_{F,M}(A)\)！且对任意 \(\bar X_M\in\mathscr R_{F,M}(A)\)，其原像由 \(\bar X_{M+1}\in\operatorname{red}_M^{-1}(\bar X_M)\cap\mathscr C_{F,M+1}(A)\)（共 \(2^\beta\) 个）与任意 \(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}(\mathbb F_2)\)（共 \(2^\beta\) 个）独立配对而成，故每个非空纤维大小恒为 \(2^\beta\cdot 2^\beta=2^{2\beta}=4^\beta\)。
   - 对 \(\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)：因 \(M+1\ge 3\)，由第 2 条知任意 \(\bar U_{M+1}\in\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\) 唯一表为 \(\bar X_{M+1}+2^M\theta_\mu\bar Z\)（\(\bar X_{M+1}\in\mathscr R_{F,M+1}(A)\)，\(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\)）。模 \(2^M\mathcal O_\mu\) 约化同样消去 \(2^M\theta_\mu\bar Z\)，映射为 \(\operatorname{red}_M(\bar X_{M+1})\)，像恰为 \(\operatorname{im}(\mathscr R_{F,M+1}(A)\to\mathscr R_{F,M}(A))=\mathscr R_{F,M}(A)\)；且每个 \(\bar X_M\in\mathscr R_{F,M}(A)\) 上方的原像由 \(2^\alpha\) 个 \(\bar X_{M+1}\) 与 \(2^\alpha\) 个 \(\bar Z\) 独立配对而成，故每个非空纤维大小恒为 \(2^\alpha\cdot 2^\alpha=2^{2\alpha}=4^\alpha\)。

5. **\(\sigma_\mu\)-固定真正解提升与逐层相容固定序列分量的等价性**：
   由引理 0.1(2)，\(\mathcal O_\mu^{\sigma_\mu}=\mathbb Z_2\)，故 \(\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_{K_\mu}(A)\cap M_d(\mathbb Z_2)=\mathscr S_F(A)\)。
   - 若 \(\bar U\in\mathscr R_{F,M}(A)\)，则存在 \(U\in\mathscr S_F(A)=\mathscr S_{K_\mu}(A)^{\sigma_\mu}\) 使 \(U\bmod 2^M\mathcal O_\mu=\bar U\)；令 \(\bar U_k:=U\bmod 2^k\mathcal O_\mu\in\mathscr R_{F,k}(A)\subseteq\mathscr R_{K_\mu,k}(A)^{\sigma_\mu}\subseteq\mathscr C_{K_\mu,k}(A)^{\sigma_\mu}\)（\(\forall k\ge 2\)），即得整条逐层相容固定序列且其精度 \(M\) 分量为 \(\bar U\)。
   - 反之，若 \(\bar U\) 甚至仅能向上相容一步为某个 \(\bar U_{M+1}\in\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\) 的约化（特别地，若 \(\bar U\) 是任一条定义在 \(k\ge 2\) 或 \(k\ge M\) 上的逐层相容固定序列在精度 \(M\) 的分量），则由第 4 条已证的 \(\operatorname{im}(\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu})=\mathscr R_{F,M}(A)\) 立即推出 \(\bar U\in\mathscr R_{F,M}(A)\)！（亦可由投射极限 \(\varprojlim_k\mathscr C_{K_\mu,k}(A)^{\sigma_\mu}=\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A)\) 直接看出。）
   判准直接由第 1、2 条中 \(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z_2/2^M\mathbb Z_2)=\mathscr C_{F,M}(A)\) 与 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z_2/2^M\mathbb Z_2)=\mathscr R_{F,M}(A)\) 结合定理 1(3) 得出。
   *否定情形具体实例*：只要 \(\Phi(A)\) 成立且存在 \(i_0\) 使 \(n_{i_0}\ge 2\)（如 \(A=(E_1,\ldots,E_r)\)，取 \(p<q\in I_{i_0}\)），元素 \(\bar U:=I_d+2^{M-1}\pi_\mu(E_{pq}+E_{qp})\bmod 2^M\mathcal O_\mu\) 属于 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)，但因 \(\theta_\mu\)-分量为 \(2^{M-1}(E_{pq}+E_{qp})\not\equiv 0\pmod{2^M}\)，有 \(\bar U\notin\mathscr R_{F,M}(A)\)，故它既不能提升为 \(\sigma_\mu\)-固定的真正解，也不能作为逐层相容固定矩阵类序列在精度 \(M\) 的分量。\(\square\)

---

## 三、目标 3 的解答与证明

### 定理 3（下降精度的最优界、精确下降判准与统一反例构造）

固定块秩 \((n_1,\ldots,n_r)\)、\(\mu\in\{-1,2\}\) 及整数 \(M\ge 2\)。

1. **最大下降精度 \(N\) 与允许精确下降的块秩分类**：
   满足题目性质的最大整数 \(N\in\{0,\ldots,M\}\) 为：
   \[
   N_{\max}(n_1,\ldots,n_r;\,\mu,M) = \begin{cases}
   M, & \text{若 }n_1=n_2=\cdots=n_r=1\text{（即 }\max_{1\le i\le r} n_i = 1\text{）},\\[4pt]
   M-1, & \text{若存在 }i_0\in\{1,\ldots,r\}\text{ 使 }n_{i_0}\ge 2\text{（即 }\max_{1\le i\le r} n_i \ge 2\text{）}.
   \end{cases}
   \]
   特别地，允许对所有合法 \(A\) 和所有模 \(2^M\mathcal O_\mu\) 被 \(\sigma_\mu\) 固定的 \(U\in\mathscr S_{K_\mu}(A)\) 实现精确下降（\(N=M\)）的块秩，**当且仅当全部块秩均为 \(1\)**（\(n_1=\cdots=n_r=1\)）。

2. **给定 \((A,U)\) 时能取 \(N=M\) 的必要充分条件**：
   设 \(A\) 为合法输入，\(U\in\mathscr S_{K_\mu}(A)\) 满足 \(\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}\)。则存在 \(W\in\mathscr S_F(A)\) 使 \(U\equiv W\pmod{2^M\mathcal O_\mu}\) **当且仅当**以下三条等价条件中任一条成立：
   - (i) \(\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}\)（即 \(\sigma_\mu\)-不变性自动高出一阶 \(2\) 的幂次）；
   - (ii) 写 \(U=X+\theta_\mu Y\)（\(X,Y\in M_d(\mathbb Z_2)\)）时，有 \(Y\equiv 0\pmod{2^M M_d(\mathbb Z_2)}\)（亦即 \(U\bmod 2^M\mathcal O_\mu\in M_d(\mathbb Z_2/2^M\mathbb Z_2)\)）；
   - (iii) \(U\bmod 2^M\mathcal O_\mu\in\mathscr R_{F,M}(A)\)。

---

### 定理 3 的证明

#### 第一步：全 \(1\) 块秩的精确下降（\(N=M\)）与一般块秩的下界（\(N\ge M-1\)）

设 \(A\) 为合法输入且存在 \(U\in\mathscr S_{K_\mu}(A)\) 满足 \(\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}\)（若 \(\mathscr S_{K_\mu}(A)=\varnothing\)，命题对该 \(A\) 空真）。由 \(\mathscr S_{K_\mu}(A)\ne\varnothing\) 及定理 1(1)，必有 \(\Phi(A)\) 成立且 \(\mathscr S_F(A)\ne\varnothing\)。

- **当 \(n_1=\cdots=n_r=1\) 时**：
  此时 \(\alpha=\sum_{i=1}^r\binom{1}{2}=0\)。事实上，由定理 1 第一步的同构，取 \(U_0\in\mathscr S_F(A)\subseteq M_d(\mathbb Z_2)\)，任意 \(U\in\mathscr S_{K_\mu}(A)\) 形如 \(U=U_0\operatorname{diag}(q_1,\ldots,q_r)\)，其中 \(q_i\in\operatorname{O}_1^{(1)}(\mathcal O_\mu)=\{q\in\mathcal O_\mu:q\equiv 1\pmod{2\mathcal O_\mu},\ q^2=1\}\)。因 \(\mathcal O_\mu\) 是整环，\(q_i^2=1\implies q_i\in\{+1,-1\}\subseteq\mathbb Z_2\)，故 \(\mathscr S_{K_\mu}(A)=\mathscr S_F(A)\)！直接取 \(W:=U\in\mathscr S_F(A)\) 即有 \(U=W\)，从而 \(U\equiv W\pmod{2^M\mathcal O_\mu}\)，故 \(N=M\)。

- **对任意块秩证明 \(N\ge M-1\)**：
  设 \(U\in\mathscr S_{K_\mu}(A)\) 满足 \(\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}\)。则其模 \(2^M\mathcal O_\mu\) 剩余类 \(\bar U:=U\bmod 2^M\mathcal O_\mu\) 属于 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)。
  由定理 2(1) 对 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\) 的统一刻画，存在 \(\bar X'\in\mathscr R_{F,M}(A)\) 及 \(\bar Z\in\bigoplus_{i=1}^r\operatorname{Sym}_{n_i}^0(\mathbb F_2)\) 使得
  \[
  \bar U \equiv \bar X' + 2^{M-1}\pi_\mu\bar Z \pmod{2^M\mathcal O_\mu}.
  \]
  因 \(\bar X'\in\mathscr R_{F,M}(A)\)，按定义存在 \(W\in\mathscr S_F(A)\) 使 \(W\equiv\bar X'\pmod{2^M\mathbb Z_2}\)。将上式模 \(2^{M-1}\mathcal O_\mu\) 约化，注意到 \(2^{M-1}\pi_\mu\bar Z\equiv 0\pmod{2^{M-1}\mathcal O_\mu}\)，立即得到
  \[
  U \equiv \bar X' + 2^{M-1}\pi_\mu\bar Z \equiv \bar X' \equiv W \pmod{2^{M-1}\mathcal O_\mu}.
  \]
  故总可取 \(N=M-1\)。

#### 第二步：给定 \((A,U)\) 可取 \(N=M\) 的充要条件证明

对上述 \(U=X+\theta_\mu Y\in\mathscr S_{K_\mu}(A)\)（\(X,Y\in M_d(\mathbb Z_2)\)），条件 \(\exists W\in\mathscr S_F(A),\ U\equiv W\pmod{2^M\mathcal O_\mu}\) 按定义等价于 (iii) \(\bar U:=(U\bmod 2^M\mathcal O_\mu)\in\mathscr R_{F,M}(A)\)。
因已知 \(\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)，由定理 2(4) 知 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z_2/2^M\mathbb Z_2)=\mathscr R_{F,M}(A)\)，故 (iii) 等价于 (ii) \(\bar U\in M_d(\mathbb Z_2/2^M\mathbb Z_2)\)，即 \(Y\equiv 0\pmod{2^M M_d(\mathbb Z_2)}\)。
最后，在直和分解 \(\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu\) 中，\(\sigma_\mu(U)-U = -2Y\theta_\mu\)，故
\[
\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}
\iff -2Y\equiv 0\pmod{2^{M+1}M_d(\mathbb Z_2)}
\iff Y\equiv 0\pmod{2^M M_d(\mathbb Z_2)},
\]
此即 (i)\(\iff\)(ii)。故 (i)、(ii)、(iii) 三者互相等价，均为能取 \(N=M\) 的必要充分条件。

#### 第三步：当 \(\max_i n_i\ge 2\) 时 \(N=M-1\) 最优性的统一构造

设存在某个下标 \(i_0\in\{1,\ldots,r\}\) 使 \(n_{i_0}\ge 2\)。我们需要对任意固定的 \(\mu\in\{-1,2\}\) 和任意整数 \(M\ge 2\)，给出合法的 \(A\) 与 \(U^{(M,\mu)}\in\mathscr S_{K_\mu}(A)\) 的**统一显式构造**，使 \(\sigma_\mu(U^{(M,\mu)})\equiv U^{(M,\mu)}\pmod{2^M\mathcal O_\mu}\)，但对任何 \(W\in\mathscr S_F(A)\) 均有 \(U^{(M,\mu)}\not\equiv W\pmod{2^M\mathcal O_\mu}\)。

1. **取合法输入 \(A\)**：置 \(A_i := E_i\)（\(1\le i\le r\)）。显然 \(A_i\in M_d(\mathbb Z_2)\) 对称、两两交换且 \(A_i\equiv E_i\pmod 2\)。
2. **对任意 \(\mu\in\{-1,2\}\) 与任意 \(M\ge 2\) 统一构造 \(2\times 2\) 矩阵 \(V^{(M,\mu)}\in\operatorname{O}_2^{(1)}(\mathcal O_\mu)\)**：
   仍记一致化子 \(\pi_2=\theta_2\)，\(\pi_{-1}=1+\theta_{-1}\)，并记 \(\eta_\mu := \frac{\pi_\mu^2}{2}\in\mathcal O_\mu^\times\)（具体地，\(\eta_2=1\)，\(\eta_{-1}=\theta_{-1}\)）。令
   \[
   b_{M,\mu} := 2^{M-1}\pi_\mu \in \mathcal O_\mu,
   \]
   则 \(b_{M,\mu}^2 = 2^{2M-2}\pi_\mu^2 = 2^{2M-1}\eta_\mu\)。利用二项式系数与第 \(k-1\) 个 Catalan 数 \(C_{k-1}=\frac{1}{k}\binom{2k-2}{k-1}\in\mathbb Z\)（\(k\ge 1\)）的经典恒等式 \(\binom{1/2}{k}=\frac{(-1)^{k-1}}{2^{2k-1}}C_{k-1}\)，定义级数：
   \[
   a_{M,\mu} := \sum_{k=0}^\infty \binom{1/2}{k}(-b_{M,\mu}^2)^k = 1 - \sum_{k=1}^\infty C_{k-1}\, 2^{(2M-3)k + 1}\,\eta_\mu^k.
   \]
   - **收敛性与整性**：因 \(M\ge 2\)，有 \(2M-3\ge 1\)，故对每个 \(k\ge 1\)，指数 \((2M-3)k+1\ge k+1\to\infty\)（随 \(k\to\infty\)），且 \(C_{k-1}\in\mathbb Z\)、\(\eta_\mu\in\mathcal O_\mu\)。因此该级数在完备环 \(\mathcal O_\mu\) 中收敛，给出元素 \(a_{M,\mu}\in\mathcal O_\mu\)，且由形式幂级数恒等式 \(\bigl(\sum_{k\ge 0}\binom{1/2}{k}(-t)^k\bigr)^2=1-t\) 在 \(2\)-进收敛域上的求值（因 \(v_2(b_{M,\mu}^2)=2M-1\ge 3\)）精确满足 \(a_{M,\mu}^2 = 1 - b_{M,\mu}^2\)，即 \(a_{M,\mu}^2+b_{M,\mu}^2=1\)。
   - **模 \(2^M\mathcal O_\mu\) 同余估计**：对一切 \(k\ge 1\) 及 \(M\ge 2\)，有 \((2M-3)k+1 \ge (2M-3)\cdot 1+1 = 2M-2 \ge M\)！故级数中所有 \(k\ge 1\) 的项均属于 \(2^{2M-2}\mathcal O_\mu\subseteq 2^M\mathcal O_\mu\)，即
     \[
     a_{M,\mu} \equiv 1 \pmod{2^M\mathcal O_\mu}.
     \]
   定义二阶矩阵
   \[
   V^{(M,\mu)} := \begin{pmatrix} a_{M,\mu} & -b_{M,\mu} \\ b_{M,\mu} & a_{M,\mu} \end{pmatrix} \in M_2(\mathcal O_\mu).
   \]
   则 \((V^{(M,\mu)})^{\mathsf T}V^{(M,\mu)}=(a_{M,\mu}^2+b_{M,\mu}^2)I_2=I_2\)，且因 \(M\ge 2\implies b_{M,\mu}\in 2\mathcal O_\mu\)、\(a_{M,\mu}\equiv 1\pmod{4\mathcal O_\mu}\)，有 \(V^{(M,\mu)}\equiv I_2\pmod{2\mathcal O_\mu}\)。
3. **嵌入到 \(d\times d\) 矩阵并验证性质**：
   在区间 \(I_{i_0}\)（\(|I_{i_0}|=n_{i_0}\ge 2\)）中任取两个不同坐标 \(p<q\)，定义 \(U^{(M,\mu)}\in M_d(\mathcal O_\mu)\) 在行、列指标集 \(\{p,q\}\times\{p,q\}\) 上的二阶子矩阵为 \(V^{(M,\mu)}\)，在其余 \(d-2\) 个对角位置上为 \(1\)，其余非对角位置全为 \(0\)：
   \[
   U^{(M,\mu)} := I_d + (a_{M,\mu}-1)(E_{pp}+E_{qq}) + b_{M,\mu}(E_{qp}-E_{pq}).
   \]
   - **属于 \(\mathscr S_{K_\mu}(A)\)**：显然 \((U^{(M,\mu)})^{\mathsf T}U^{(M,\mu)}=I_d\)，\(U^{(M,\mu)}\equiv I_d\pmod{2\mathcal O_\mu}\)，且因 \(p,q\in I_{i_0}\) 同属一个坐标块，\(U^{(M,\mu)}\) 与每个 \(E_j\) 直接交换，故 \([(U^{(M,\mu)})^{\mathsf T}E_iU^{(M,\mu)},E_j]=[E_i,E_j]=0\)（\(\forall i,j\)），即 \(U^{(M,\mu)}\in\mathscr S_{K_\mu}(A)\)。
   - **满足 \(\sigma_\mu(U^{(M,\mu)})\equiv U^{(M,\mu)}\pmod{2^M\mathcal O_\mu}\)**：由 \(a_{M,\mu}\equiv 1\pmod{2^M\mathcal O_\mu}\) 得 \(\sigma_\mu(a_{M,\mu})\equiv 1\equiv a_{M,\mu}\pmod{2^M\mathcal O_\mu}\)；又对 \(b_{M,\mu}=2^{M-1}\pi_\mu\)，无论 \(\pi_2=\theta_2\) 还是 \(\pi_{-1}=1+\theta_{-1}\)，均有 \(\sigma_\mu(\pi_\mu)-\pi_\mu=-2\theta_\mu\)，故
     \[
     \sigma_\mu(b_{M,\mu}) - b_{M,\mu} = -2^M\theta_\mu \equiv 0 \pmod{2^M\mathcal O_\mu}.
     \]
     因此 \(\sigma_\mu(U^{(M,\mu)})\equiv U^{(M,\mu)}\pmod{2^M\mathcal O_\mu}\)。
   - **不可能取 \(N=M\)**：任取 \(W\in\mathscr S_F(A)\subseteq M_d(\mathbb Z_2)\)，考察 \((q,p)\) 位置的元素差：
     \[
     (U^{(M,\mu)} - W)_{qp} = b_{M,\mu} - W_{qp} = \begin{cases}
     -W_{qp} + 2^{M-1}\theta_2, & (\mu=2),\\
     (2^{M-1}-W_{qp}) + 2^{M-1}\theta_{-1}, & (\mu=-1).
     \end{cases}
     \]
     因 \(W_{qp}\in\mathbb Z_2\)，该差在自由 \(\mathbb Z_2\)-模 \(\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu\) 中的 \(\theta_\mu\)-坐标恒为 \(2^{M-1}\notin 2^M\mathbb Z_2\)！故 \((U^{(M,\mu)}-W)_{qp}\notin 2^M\mathcal O_\mu\)，即对一切 \(W\in\mathscr S_F(A)\) 均有 \(U^{(M,\mu)}\not\equiv W\pmod{2^M\mathcal O_\mu}\)。

综上，当 \(\max_{1\le i\le r}n_i\ge 2\) 时，对任意 \(\mu\in\{-1,2\}\) 及任意 \(M\ge 2\)，最大整数必为 \(N=M-1\)。全部目标证毕。\(\blacksquare\)
