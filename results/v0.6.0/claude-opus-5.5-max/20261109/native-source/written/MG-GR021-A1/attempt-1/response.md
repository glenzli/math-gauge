# 同时分块与二次扩张上的下降：完整解答

## 0. 记号与所用的标准事实

**记号。**
- \(M\ge 2\)。\(q_F=2\)，\(q_{K_\mu}=4\)，即 \(q_L=|\mathcal O_L/2\mathcal O_L|\)。
- \(D_n=\binom n2\)，\(D=\sum_iD_{n_i}\)。于是 \(\sum_i\binom{n_i+1}2=d+D\)。
- \(I_i^c\) 表示 \(I_i\) 的补集。
- \(\mathrm{Sym}_{bd}\)：\(\mathbb F_2\) 上按 \((n_1,\dots,n_r)\) 分块的块对角对称矩阵，共 \(2^{d+D}\) 个。
- \(\mathrm{Alt}_{bd}\subset\mathrm{Sym}_{bd}\)：其中对角线为零的那些，共 \(2^D\) 个。

**所用的标准事实。**
1. \(\mathbb Z_2\) 与 \(\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta\) 是完备的 Noether 局部环，Cauchy 列收敛。
2. \(2^M\mathcal O_\mu=2^M\mathbb Z_2\oplus2^M\mathbb Z_2\theta\)。因此每个 \(x\in\mathcal O_\mu/2^M\) 可唯一写成 \(a+b\theta\)（\(a,b\in\mathbb Z/2^M\)），且 \(\mathbb Z/2^M\hookrightarrow\mathcal O_\mu/2^M\) 是单射。
3. \(\mathcal O_\mu^{\sigma}=\mathbb Z_2\)。
4. Nakayama 引理（局部环上的有限生成模）。
5. 局部环上投射模是自由模。

设 \(k=\mathcal O_L/2\)。对 \(L=K_\mu\)，令 \(\varepsilon=\overline{\theta+\mu}\)，则 \(\varepsilon^2=\overline{\mu(\mu+1)}=0\)，\(k=\mathbb F_2\oplus\mathbb F_2\varepsilon\)。对 \(x=a+b\varepsilon\) 有
\[
x^2=a\in\mathbb F_2,\qquad x+x^2=b\varepsilon. \tag{0.1}
\]
对 \(L=F\)，\(k=\mathbb F_2\)，\(x^2=x\)。

---

## 1. 幂等元与分块化

**引理 1（幂等元提升）。** 设 \(A\in M_d(\mathbb Z_2)\)，\(A\equiv E \pmod 2\)，其中 \(E\) 幂等。令 \(f(x)=3x^2-2x^3\)，\(x_0=A\)，\(x_{n+1}=f(x_n)\)。

由恒等式
\[
f(x)-x=-(x^2-x)(2x-1),\qquad f(x)^2-f(x)=(x^2-x)^2(4x^2-4x-3)
\]
得 \(x_n^2-x_n\equiv0\) 及 \(x_{n+1}-x_n\equiv 0 \pmod{2^{2^n}}\)。所以 \(P=\lim x_n\) 存在，且：
- \(P\) 幂等，\(P\equiv A \pmod 2\)；
- \(P\) 属于 \(\mathbb Z_2[A]\) 的闭包；
- \(P\equiv x_1\pmod 4\)，\(P\equiv x_n\pmod{2^M}\)（当 \(2^n\ge M\)）。

另外，任一环 \(R=\mathcal O/2^M\) 或 \(\mathcal O\) 上，与 \(0\) 同余 mod 2 的幂等元为 \(0\)，因为 \(e=e^m\in 2^m\)。

**应用。** 对每个 \(A_i\) 得到 \(P_i\)，它们满足：
- \(P_i\) 对称（对称矩阵多项式的极限），且与所有 \(A_j\)、\(P_j\) 交换；
- \(i\ne j\) 时 \(P_iP_j\) 是 \(\equiv E_iE_j=0\) 的幂等元，故 \(P_iP_j=0\)；
- \(I-\sum P_i\) 是 \(\equiv0\) 的幂等元，故 \(\sum_iP_i=I\)。

记 \(A_i=E_i+2X_i\)，则 \(x_1=3A_i^2-2A_i^3\equiv E_i+2(E_iX_i+X_iE_i) \pmod 4\)。因此
\[
P_i[I_i,I_i]\equiv I \pmod 4,\qquad P_i[I_i^c,I_i]\equiv A_i[I_i^c,I_i] \pmod 4. \tag{1.1}
\]

**引理 2（关键等价）。** 设 \(R=\mathcal O_L/2^M\)（\(M\ge1\)）或 \(R=\mathcal O_L\)，\(\bar U\in GL_d(R)\)，\(\bar U\equiv I \pmod 2\)，\(\bar U^{\mathsf T}\bar U=I\)。则
\[
[\bar U^{\mathsf T}A_i\bar U,E_j]=0\ (\forall i,j)\iff P_i\bar U=\bar UE_i\ (\forall i)\iff \bar U\text{ 中下标属于 }I_i\text{ 的列都落在 }P_iR^d.
\]

*证明。* 注意 \(\bar U^{\mathsf T}=\bar U^{-1}\)。
- (⇒) \(Y_i=\bar U^{-1}A_i\bar U\) 是块对角的，所以 \(\bar U^{-1}P_i\bar U=x_n(Y_i)\) 是块对角幂等元，且 \(\equiv E_i\pmod 2\)。它的每个对角块都是与 \(0\) 或 \(I\) 同余 mod 2 的幂等元，由引理 1 末句得 \(\bar U^{-1}P_i\bar U=E_i\)。
- (⇐) \(P_j\equiv x_n(A_j)\) 与 \(A_i\) 交换，所以 \(\bar U^{-1}A_i\bar U\) 与 \(\bar U^{-1}P_j\bar U=E_j\) 交换。
- 第二个等价：若 \(P_i\) 在 \(I_i\) 列上取恒等，则对 \(k\in I_j\)（\(j\ne i\)）有 \(P_i\bar u_k=P_iP_j\bar u_k=0\)。∎

**格的图坐标。** 令 \(\Lambda_i=P_i\mathbb Z_2^d\)，它是正交直和项，秩为 \(n_i\)（因为 \(\Lambda_i/2\Lambda_i\cong\operatorname{Im}E_i\)）。向量 \(P_ie_k\)（\(k\in I_i\)）mod 2 为 \(e_k\)，由 Nakayama 引理它们构成 \(\Lambda_i\) 的基。由于 \(P_i[I_i,I_i]\) 可逆，可定义
\[
B_i=P_i[:,I_i]\,P_i[I_i,I_i]^{-1}=\begin{pmatrix}I\\ G_i\end{pmatrix}.
\]
由 (1.1)，\(G_i\equiv A_i[I_i^c,I_i]\pmod 4\)。写 \(G_i=2G_i'\)，并令
\[
H_i:=B_i^{\mathsf T}B_i=I+4Q_i,\qquad Q_i=G_i'^{\mathsf T}G_i'.
\]

**命题 3（分块化）。** 记 \(X(H;R)=\{T\in M_n(R):T\equiv I \pmod 2,\ T^{\mathsf T}HT=I\}\)。映射
\[
\bar U\mapsto(\bar U[I_i,I_i])_i
\]
是 \(C\)-型集合（\(R=\mathcal O_L/2^M\)）或 \(\mathscr S_L(A)\)（\(R=\mathcal O_L\)）到 \(\prod_iX(H_i;R)\) 的双射，逆映射为 \(\bar U[:,I_i]=B_iT_i\)。它与约化映射及 \(\sigma\) 相容，因为 \(B_i,H_i\) 都是有理的。

*证明。* 由引理 2，\(\bar U[:,I_i]\in P_iR^d=B_iR^{n_i}\)，又 \(B_i\) 在 \(I_i\) 行上是 \(I\)，所以 \(\bar U[:,I_i]=B_iT_i\) 且 \(T_i=\bar U[I_i,I_i]\)。由 \(\Lambda_i\perp\Lambda_j\) 得
\[
(B_iT_i)^{\mathsf T}B_jT_j=\delta_{ij}T_i^{\mathsf T}H_iT_i.
\]
\(\bar U\equiv I\iff T_i\equiv I\)。∎

---

## 2. 单块分析

固定一块：\(H=I+4Q\)，阶为 \(n\)，\(q=q_L\)。记 \(X_M=X(H;\mathcal O_L/2^M)\)，\(R_M\) 为真解集 \(X_\infty\) 的像。对 \(T\in X_M\)，定义
\[
\nu(T)_j=\overline{\big((\tilde T^{\mathsf T}H\tilde T)_{jj}-1\big)/2^M}\in k,
\]
其中 \(\tilde T\) 是任一提升。它良定：若 \(u'-u\in2^M\)，则 \(u+u'\in2\)，于是 \(u^{\mathsf T}Hu-u'^{\mathsf T}Hu'\in2^{M+1}\)。

**引理 4（提升）。** 设 \(M\ge2\)，\(T\in X_M\)。
1. \(T\) 能提升到 \(X_{M+1}\) 当且仅当 \(\nu(T)=0\)。
2. 若 \(\nu(T)=0\)，则 \(T\) 在 \(X_{M+1}\) 中恰有 \(q^{\binom{n+1}2}\) 个提升，其中恰有 \(q^{D_n}\) 个满足 \(\nu=0\)。

*证明。* 设 \(\tilde T^{\mathsf T}H\tilde T=I+2^M\Delta\)。\(T\) 的所有提升可唯一写成 \(\tilde T(I+2^MY)\)，且只依赖于 \(\bar Y\in M_n(k)\)。由
\[
(I+2^MY)^{\mathsf T}(I+2^M\Delta)(I+2^MY)=I+2^M(\Delta+Y+Y^{\mathsf T})+2^{2M}(\cdots)
\]
以及 \(2M\ge M+1\)，条件化为 \(\bar\Delta+\bar Y+\bar Y^{\mathsf T}=0\)。\(\bar Y+\bar Y^{\mathsf T}\) 的对角线为零，所以必要条件是 \(\bar\Delta_{jj}=0\)，即 \(\nu=0\)。此时每对 \(j<l\) 有 \(q\) 种选择，对角元自由，共 \(q^{D_n+n}\) 个解。

再写 \(\Delta+Y+Y^{\mathsf T}=2\Delta_1\)，则新的偏差 \(\Delta'\equiv\Delta_1\pmod 2\)（因 \(M\ge2\)），于是
\[
\nu_j=\overline{\Delta_{jj}/2}+\bar Y_{jj}.
\]
每个对角元恰有一个取值使 \(\nu_j=0\)。∎

**推论 5。** 对 \(M\ge2\)：
- \(\operatorname{Im}(X_{M+1}\to X_M)=\nu^{-1}(0)=R_M\)；
- \(R_{M+1}\to R_M\) 满射，每个纤维大小为 \(q^{D_n}\)；
- \(X_{M+1}\to X_M\) 的每个非空纤维大小为 \(q^{\binom{n+1}2}\)。

其中 \(\nu^{-1}(0)\subseteq R_M\) 的理由：逐层取 \(\nu=0\) 的提升，代表元构成 Cauchy 列，极限即为真解。

**引理 6（第 2 层）。** \(X_2=\{I+2Y:\bar Y\in\mathrm{Sym}_n(k)\}\)，因此 \(|X_2|=q^{\binom{n+1}2}\)，且恒非空。

对 \(T=I+2Y\)，写 \(\bar Y=Y^{(0)}+Y^{(1)}\varepsilon\)，其中 \(Y^{(0)},Y^{(1)}\) 是 \(\mathbb F_2\) 上的对称矩阵（\(F\) 情形 \(Y^{(1)}=0\)）。令 \(c_j=\sum_lG'_{lj}\bmod2\)（列和）。由
\[
T^{\mathsf T}HT\equiv I+4(Z+Y^{\mathsf T}Y+Q)\pmod 8,\qquad Z_{jj}=Y_{jj},
\]
并用 (0.1)，得
\[
\nu_j=\Big[c_j+\textstyle\sum_{l\neq j}Y^{(0)}_{lj}\Big]+Y^{(1)}_{jj}\,\varepsilon .
\]
\(\sum_{l\ne j}Y^{(0)}_{lj}\) 是以 \(Y^{(0)}\) 的非对角部分为邻接矩阵的图中顶点 \(j\) 的度的奇偶性。这些度奇偶向量恰好构成偶重量向量全体（由握手引理，且边 \(\{j,l\}\) 给出 \(e_j+e_l\)），并且这是一个线性映射，每个纤维含 \(2^{D_n-n+1}\) 个图。因此：

\[
R_2\neq\varnothing\iff\sum_jc_j\equiv0\iff\sum_{\text{全部元素}}G'\equiv 0 \pmod 2,
\]
此时 \(|R_2|=2^{D_n+1}\)（\(F\)），\(|R_2|=2^{2D_n+1}\)（\(K\)）。

---

## 3. 第 1 问

**可行性判准。** 令
\[
\epsilon_i(A)=\tfrac12\sum_{k\in I_i,\ l\notin I_i}(A_i)_{lk}\bmod 2 .
\]
它只依赖于 \(A_i\bmod 4\)。由 (1.1)，\(\epsilon_i(A)\) 等于 \(G_i'\) 全部元素之和 mod 2；等价地，\(\det(I+G_i^{\mathsf T}G_i)\equiv1\pmod 8\)。

\[
\mathscr S_L(A)\neq\varnothing\iff \epsilon_i(A)=0\ \ \forall i,
\]
且这一判准对 \(F,K_{-1},K_2\) 三者完全相同。

**结构。** 若 \(U_0\in\mathscr S_L(A)\)，则
\[
\mathscr S_L(A)=U_0\cdot\prod_i\Gamma_{n_i}(\mathcal O_L),\qquad \Gamma_n=\{V\in O_n:V\equiv I \pmod 2\}.
\]

**基数（\(M\ge2\)）。** 由命题 3 与推论 5、引理 6：

| 集合 | 条件 | \(L=F\) | \(L=K_\mu\) |
|---|---|---|---|
| \(\mathscr R_{L,M}(A)\) | 可行 | \(2^{\,r+(M-1)D}\) | \(2^{\,r+2(M-1)D}\) |
| \(\mathscr C_{L,2}(A)\) | 恒成立（与可行性无关） | \(2^{\,d+D}\) | \(2^{\,2(d+D)}\) |
| \(\mathscr C_{L,M}(A)\)，\(M\ge3\) | 可行 | \(2^{\,d+r+(M-1)D}\) | \(2^{\,2d+r+2(M-1)D}\) |

统一写法：\(|\mathscr R|=2^rq^{(M-1)D}\)，\(|\mathscr C_{M\ge3}|=2^rq^{d+(M-1)D}\)。

**空集条件。**
- \(\mathscr R_{L,M}(A)=\varnothing\iff\exists i:\ \epsilon_i(A)=1\)。
- \(\mathscr C_{L,M}(A)=\varnothing\iff M\ge3\) 且 \(\exists i:\ \epsilon_i(A)=1\)。

**属于 \(\mathscr R\) 的判准。** 对 \(\bar U\in\mathscr C_{L,M}(A)\)：
\[
\bar U\in\mathscr R_{L,M}(A)\iff \text{对每列 }k\text{ 及其任一提升 }\tilde u_k:\ \tilde u_k^{\mathsf T}\tilde u_k\equiv1 \pmod{2^{M+1}\mathcal O_L}\iff \bar U\text{ 能提升到 }\mathscr C_{L,M+1}(A).
\]
理由：取提升 \(B_i\tilde t_k\)，即得 \(\nu(T_i)=0\)。该判准无需事先假设可行性。

**例子（不可行）。** \(A_1=\begin{pmatrix}1&2\\2&0\end{pmatrix}\)，\(A_2=I-A_1\)。此时 \(\epsilon_1=1\)。

---

## 4. 第 2 问

\((\mathcal O_\mu/2^M)^\sigma=\{a+2^{M-1}b\theta:\ a\in\mathbb Z/2^M,\ b\in\mathbb F_2\}\)。

**\(\mathscr C\) 的固定点。** 由 \(2^{2M-2}\equiv0\) 及 \(V_0\equiv I\)，有
\[
\mathscr C_{K_\mu,M}(A)^{\sigma}=\{V_0+2^{M-1}\theta V_1:\ V_0\in\mathscr C_{F,M}(A),\ V_1\in\mathrm{Sym}_{bd}\},
\]
因此 \(|\mathscr C^\sigma|=2^{d+D}|\mathscr C_{F,M}(A)|\)。推导：\(V^{\mathsf T}V\equiv V_0^{\mathsf T}V_0+2^{M-1}\theta(V_1+V_1^{\mathsf T})\)，由坐标唯一性得 \(V_1\) 对称；\(P_iV=VE_i\) 给出 \(V_1E_i=E_iV_1\)，即 \(V_1\) 块对角。

**\(\mathscr R\) 的固定点。** 对列 \(v=v_0+2^{M-1}\theta v_1\)，
\[
v\cdot v\equiv v_0\cdot v_0+2^M\theta\,(v_1)_k+2^{2M-2}\mu\,v_1\cdot v_1 \pmod{2^{M+1}} .
\]
- 当 \(M\ge3\) 或 \(\mu=2\) 时：
  \[
  \mathscr R_{K,M}(A)^\sigma=\{V_0+2^{M-1}\theta V_1:\ V_0\in\mathscr R_{F,M}(A),\ V_1\in\mathrm{Alt}_{bd}\}.
  \]
- 当 \(\mu=-1,\ M=2\) 时：
  \[
  \mathscr R^\sigma=\mathscr R_{K,2}(A)=\{V_0+2iV_1:\ V_1\in\mathrm{Alt}_{bd},\ V_0\in\mathscr C_{F,2}(A),\ V_0\text{ 的第 }k\text{ 列范数}\equiv1+4w_k(V_1)\pmod 8\},
  \]
  其中 \(w_k(V_1)=\sum_l(V_1)_{lk}\)。这是一个"扭曲"集合，在 \(D>0\) 时不等于 \(\mathscr R_F+2i\,\mathrm{Alt}_{bd}\)。

**与基域集合的关系。**
- 所有情形下 \(|\mathscr R^\sigma|=2^D|\mathscr R_{F,M}(A)|=2^{r+MD}\)（可行时；不可行时为 0）。
- \(\mathscr R^\sigma\cap M_d(\mathbb Z/2^M)=\mathscr R_{F,M}(A)\)，\(\mathscr C^\sigma\cap M_d(\mathbb Z/2^M)=\mathscr C_{F,M}(A)\)。
- \(\mathscr R^\sigma=\mathscr R_F\iff D=0\)。
- 当 \(M=2\) 时，\(\sigma\) 在 \(\mathscr C_{K,2}\) 上平凡作用。

**\(\langle\sigma\rangle\) 轨道数**（由 Burnside 公式 \((|X|+|X^\sigma|)/2\)，可行时）：
- \(\mathscr R_{K,M}\)：\(2^{r-1}\big(2^{2(M-1)D}+2^{MD}\big)\)；
- \(\mathscr C_{K,2}\)：\(2^{2(d+D)}\)；
- \(\mathscr C_{K,M}\)（\(M\ge3\)）：\(2^{2d+r-1}\big(2^{2(M-1)D}+2^{MD}\big)\)。

**从精度 \(M+1\) 到 \(M\) 的约化。** 层 \(M+1\) 上的元素 \(V_0+2^M\theta V_1\) 约化为 \(V_0\bmod 2^M\)。

| 映射 | 像 | 每个非空纤维大小 |
|---|---|---|
| \(\mathscr R_{L,M+1}\to\mathscr R_{L,M}\) | 满射 | \(q^D\) |
| \(\mathscr C_{L,M+1}\to\mathscr C_{L,M}\) | \(\mathscr R_{L,M}(A)\) | \(q^{d+D}\) |
| \(\mathscr R^\sigma_{K,M+1}\to\mathscr R^\sigma_{K,M}\) | \(\mathscr R_{F,M}(A)\) | \(2^{2D}\) |
| \(\mathscr C^\sigma_{K,M+1}\to\mathscr C^\sigma_{K,M}\) | \(\mathscr R_{F,M}(A)\) | \(2^{2(d+D)}\) |

**哪些固定类能被提升。** 对 \(x\in\mathscr C^\sigma_{K,M}(A)\)，下列条件等价：
1. \(x\) 能提升为 \(\sigma\) 固定的真解；
2. \(x\in\mathscr R_{F,M}(A)\)，即 \(V_1=0\) 且各列范数 \(\equiv1\pmod{2^{M+1}}\)；
3. \(x\) 是某条逐层相容的固定类序列在精度 \(M\) 的分量；
4. \(x\) 在 \(\mathscr C^\sigma_{K,M+1}\) 中有原像。

证明链：(1)⇒(3) 取约化；(3)⇒(4) 显然；(4)⇒(2) 由上表的像；(2)⇒(1) 因为 \(\mathscr S_F\subset\mathscr S_K\)，且 \(\mathscr S_K(A)^\sigma=\mathscr S_F(A)\)（由 \(\mathcal O_\mu^\sigma=\mathbb Z_2\)）。

此外，\(\mathscr R^\sigma\setminus\mathscr R_F\) 中的类能提升为真解，但不能提升为固定真解；\(\mathscr C^\sigma\setminus\mathscr R^\sigma\) 中的类根本不能提升为真解。后者的例子：\(A=(E_i)\)，\(x=I+2^{M-1}\theta e_pe_p^{\mathsf T}\)（对角元 \((V_1)_{pp}=1\)，故 \(\nu\ne0\)）。

---

## 5. 第 3 问

**结论。**
\[
N_{\max}=\begin{cases}M-1,&\max_i n_i\ge2,\\ M,&\text{所有 }n_i=1,\end{cases}
\]
与 \(\mu\) 无关。当所有 \(n_i=1\) 时有精确下降：此时 \(\Gamma_1=\{\pm1\}\)，从而 \(\mathscr S_K(A)=\mathscr S_F(A)\)。

**下界 \(N\ge M-1\)。** 设 \(U\equiv V_0+2^{M-1}\theta V_1\pmod{2^M}\)。
- 若 \(M\ge3\)：\(V_0\in\mathscr C_{F,M}\)，其约化 \(\bar V_0\in\mathscr R_{F,M-1}\)，故存在 \(W\in\mathscr S_F(A)\) 使 \(W\equiv V_0\equiv U\pmod{2^{M-1}}\)。
- 若 \(M=2\)：可行性判准与域无关，故 \(\mathscr S_F(A)\ne\varnothing\)，任取 \(W\) 即有 \(W\equiv I\equiv U\pmod 2\)。

**对给定 \(A,U\) 能取 \(N=M\) 的充要条件。**
\[
\exists W:\ U\equiv W \pmod{2^M}\iff \sigma(U)\equiv U \pmod{2^{M+1}\mathcal O_\mu}\iff U\bmod 2^M\in M_d(\mathbb Z/2^M).
\]
- 必要性：写 \(U=U_0+\theta U_1\)，则 \(\sigma U-U=-2\theta U_1\)，而 \(W\) 是有理矩阵。
- 充分性：\(U\) 是真解，故 \(\nu_F(U_0\bmod 2^M)=\nu_K=0\)，于是 \(U_0\bmod 2^M\in\mathscr R_{F,M}(A)\)。

**最优性（对所有 \(M\ge2\) 和 \(\mu\) 的统一构造）。** 取 \(A_i=E_i\)，选一个 \(n_{i_0}\ge2\) 的块，以及其中的坐标 \(p,p+1\)。令
\[
s=2^{M-2}(\mu+\theta),\qquad \alpha=\frac{1-s^2}{1+s^2},\qquad \beta=\frac{2s}{1+s^2},
\]
并令 \(U\) 为在第 \(p,p+1\) 行列处为 \(\begin{pmatrix}\alpha&\beta\\-\beta&\alpha\end{pmatrix}\)、其余为单位阵的矩阵（Cayley 变换）。逐项验证：
- \(1+s^2\) 是单位：\(M=2\) 时 \(1+s^2=(1+\mu+\mu^2)+2\mu\theta\)，有理部分为奇数；\(M\ge3\) 时 \(s\in2\mathcal O\)。
- \(\alpha^2+\beta^2=1\)，\(U\equiv I\pmod 2\)，且 \(U\) 块对角，所以 \(U\in\mathscr S_K(A)\)。
- \(\sigma s-s=-2^{M-1}\theta\)，由此 \(\sigma\beta-\beta\) 与 \(\sigma\alpha-\alpha\) 都属于 \(2^M\mathcal O\)，即 \(\sigma(U)\equiv U\pmod{2^M}\)。
- \(\beta\equiv 2s=2^{M-1}(\mu+\theta)\pmod{2^M}\)，其 \(\theta\) 坐标为 \(2^{M-1}\not\equiv0\)，所以对任何 \(W\in M_d(\mathbb Z_2)\) 都有 \(U\not\equiv W\pmod{2^M}\)。

因此对该 \((A,U)\)，最佳精度恰为 \(M-1\)；同时 \(U\bmod 2^M\in\mathscr R^\sigma_{K,M}\setminus\mathscr R_{F,M}\)。

---

## 6. 验证

我在 Python 中按题目原始定义（直接检查交换子条件）做了穷举，与上述公式全部一致。覆盖范围：
- \(A=E\)，\(n\le3\)，\(M\le4\)（\(K\) 上 \(n=3\) 时 \(M\le3\)）：检查 \(|\mathscr C|\)、\(|\mathscr R|\)、"\(\mathscr C_{M+1}\) 的像 = \(\nu^{-1}(0)\)"、纤维大小，以及 \(|\mathscr C^\sigma|\)、\(|\mathscr R^\sigma|\)；
- 块秩 \((2,1)\)、取非平凡的 \(G\)，覆盖 \(F,K_{-1},K_2\) 与 \(M=2,3\)：检查各项基数、固定点数以及 \(\epsilon_i\) 判准（\(\epsilon_i=1\) 的情形 \(\mathscr R=\varnothing\)，且 \(M=3\) 时 \(\mathscr C=\varnothing\)）。

\((\mu,M)=(-1,2)\) 时扭曲集合的具体形状只在基数层面验证过，没有逐个元素比对；这一点由 §4 的列范数计算给出。