# 同时分块与二次扩张上的下降：修订稿

本稿更正原稿中的单块有限群计数和逐层纤维。以下所有“模 $2^M$”都指相应整数环上的约化。记
\[
 B_n=\frac{n(n+1)}2,\qquad A_n=\frac{n(n-1)}2.
\]

## 1. 精确解与可行性

由 $A_i\equiv E_i\pmod2$ 和 Hensel 引理，$A_i$ 有唯一幂等对称投影 $P_i$ 且 $P_i\equiv E_i\pmod2$。令 $L_i=\operatorname{im}P_i$。诸 $L_i$ 两两正交，$L_i\bmod2=\mathbb F_2^{I_i}$。

令
\[
 G_i=E_iP_iE_i\in M_{n_i}(\mathbb Z_2).
\]
则 $G_i$ 是 $L_i$ 在 $P_ie_{i,a}$ 下的 Gram 矩阵，并且 $G_i\equiv I\pmod2$。

**引理 1.1（可行性）.** 对于 $L\in\{F,K_{-1},K_2\}$,
\[
 \mathscr S_L(A)\ne\varnothing
 \iff G_i\text{ 在 }\mathbb Z_2\text{ 上同构于 }I_{n_i}\text{ 的轨道}\quad(\forall i).
\tag{1.1}
\]
对奇幺模格，标准型精确等价于
\[
 \boxed{\det G_i\equiv1\pmod8\quad(i=1,\dots,r).}
\tag{1.2}
\]
因此可行性可由 $A_i\bmod4$ 有限决定：先算 $P_i\bmod4$；$G_i\bmod8$ 随之确定。这个判准与 $L$ 无关。

**证明.** 对 $A_i$ 的特征多项式在 $x=0,1$ 作 Hensel 分裂，得到相应的幂等投影。若 $U^T A_iU$ 与所有 $E_j$ 交换，则它保持每个 $U(\mathcal O_L^{I_j})$；模 $2$ 后 $A_i\equiv E_i$，故只有 $j=i$ 的块可被 $A_i$ 模 $2$ 可逆，于是该块就是 $A_i$ 的单位谱格。反过来，若每个 $L_i$ 都同构于标准格，拼起来即得 $U_0$。

在 $L_i$ 的上述基下，$G_i$ 是奇幺模对称 Gram 矩阵。二维奇幺模格有正规形
\[
 \langle1\rangle\oplus\langle d\rangle,\qquad d\in\{1,5\}\pmod8.
\]
归纳消去一个长度为奇数的向量可得更高维的同一结论：除标准型外，唯一的另一类具有正规形
\[
 \langle5\rangle\oplus\langle1\rangle^{n_i-1}.
\]
前者行列式为 $1\bmod8$，后者为 $5\bmod8$。

若 (1.2) 成立，取等距 $U_0:V_i\to L_i\otimes\mathcal O_L$，直接计算得
\[
 \mathscr S_L(A)=U_0\prod_{i=1}^r
 \Omega_{n_i}^{L},\qquad
 \Omega_n^L=\{V\in O_n(\mathcal O_L):V\equiv I_n\pmod2\}.
\tag{1.3}
\]
特别地，$\mathscr S_L(A)$ 非空时是右 $\prod_i\Omega_{n_i}^L$ 空间。

若 (1.2) 失败，取一个具体的失败块：
\[
 n=1,\quad r=2,\quad v=(1,2)^T,\quad P=\frac{vv^T}{5},\quad A_1=P,\quad A_2=I-P.
\]
则 $A_i\equiv E_i\pmod2$ 且 $G_1=5$，所以三个整数环上的精确解集都为空。

## 2. 单块有限群：修正后的精确计数

为了避免与 $A$ 依赖的模解混淆，先记
\[
 \omega_n^F(M)=|\Omega_n^F/2^M|,\qquad
 \omega_n^K(M)=|\Omega_n^K/2^M|,
\]
以及满精确像
\[
 \rho_n^F(M)=|\{U\in O_n(\mathbb Z_2):U\equiv I\pmod2\}\bmod2^M|,
\]
\[
 \rho_n^K(M)=|\{U\in O_n(\mathcal O_K):U\equiv I\pmod2\}\bmod2^M|.
\]
这些是 $\prod_i\rho_{n_i}^L(M)$ 的单块因子。

**定理 2.1.** 对所有 $n\ge1$ 和 $M\ge1$,
\[
 \boxed{\rho_n^F(M)=
 \begin{cases}
 1,&M=1,\\
 2^{1+(M-1)A_n},&M\ge2,
 \end{cases}}
\tag{2.1}
\]
\[
 \boxed{\rho_n^K(M)=
 \begin{cases}
 1,&M=1,\\
 2^{1+(M-1)n(n-1)},&M\ge2.
 \end{cases}}
\tag{2.2}
\]

证明是标准主同余计算。一个有用的规范形为
\[
 \Omega_n^F=\{\pm I\}\exp(2M_n(\mathbb Z_2))\cap O_n(\mathbb Z_2),
\]
而指数中的方向经 $\partial$ 消去后，模 $2^M$ 的自由秩为 $(M-1)A_n$。符号 $\pm$ 在模 $2$ 重合；$M\ge2$ 时有两只符号，因此得到因子 $2$。
对 $K$，令 $K=\mathbb Q_2(\pi)$，$2=\pi^2u$。近单位正交群中的 Lie 代数是斜伴矩阵 $\mathfrak{so}_n(\mathcal O_K)$。指数映射在 $\pi^2M_n$ 上给出同构，模 $2^M\mathcal O_K=\pi^{2M}\mathcal O_K$ 后自由秩为
\[
 (2M-2)A_n=(M-1)n(n-1).
\]
再乘 $\pm I$ 的两个符号；$M=1$ 时二者相同。

现在记 $A$ 依赖的模解
\[
 c_n^F(M)=|\mathscr C_{F,M}|,\qquad
 c_n^K(M)=|\mathscr C_{K,M}|.
\]
由 $U^TU=I$ 的二阶正规形 $U=I+2H$ 及 $M=2$ 的线性化得到
\[
 c_n^F(2)=2^{B_n},\qquad c_n^K(2)=2^{n(n+1)}.
\tag{2.3}
\]
更精确地
\[
 \mathscr C_{K,2}\cong (1+2M_n(\mathcal O_K/4))/ (1+2M_n(\mathcal O_K/2))
\]
，而这个 kernel 的秩为 $n(n+1)$；$\pm$ 在模 $2$ 下合并，故 $n=1$ 也给出 $2$。

由“下一层的一个非空纤维大小等于模 $2$ 主同余 kernel”及归纳，逐层计算给
\[
 \boxed{
 c_n^F(M)=
 \begin{cases}
 1,&M=1,\\
 2^{B_n},&M=2,\\
 2^{B_n+1+(M-2)A_n},&M\ge3,
 \end{cases}}
\tag{2.4}
\]
\[
 \boxed{
 c_n^K(M)=
 \begin{cases}
 1,&M=1,\\
 2^{n(n+1)},&M=2,\\
 2^{n(n+1)+1+(M-2)n(n-1)},&M\ge3.
 \end{cases}}
\tag{2.5}
\]
例如 $n=2,M=3$ 分别给出 $2^5$ 和 $2^9$。这两条可逐列核验：每个新列的单位长度解与一个较小的同一方程（稳定子）相乘；消去最后一个坐标时，唯一剩余的二次条件是一个满射到 $\mathbb F_2$ 的方程，因而每层恰有两个预像。

## 3. 全部分块的 $\mathscr R$ 与 $\mathscr C$

置
\[
 B=\sum_iB_{n_i},\qquad A=\sum_iA_{n_i},\qquad
 D=\sum_in_i(n_i-1)=2A,\qquad D'=\sum_in_i(n_i+1).
\]
当所有块大小都为 $1$ 时，$M=1$ 本来就是唯一的有限环；以下 $M\ge2$ 公式可直接取相应的空乘积和 $r$ 个独立符号。

### 3.1 精确像 $\mathscr R$

若不可行，则对所有 $M$,
\[
 \mathscr R_{L,M}(A)=\varnothing.\tag{3.1}
\]
若可行，则
\[
 \boxed{|\mathscr R_{F,M}(A)|=
 \begin{cases}1,&M=1,\\2^{r+(M-1)A},&M\ge2,\end{cases}}
\tag{3.2}
\]
\[
 \boxed{|\mathscr R_{K,M}(A)|=
 \begin{cases}1,&M=1,\\2^{r+(M-1)D},&M\ge2.\end{cases}}
\tag{3.3}
\]

这由 (1.3) 及精确像的右因子
\[
 \Omega_n^L(\mathcal O_L)\longrightarrow \Omega_n^L(\mathcal O_L/2^M)
\]
是满射得到；多块的右作用自由，故取乘积。

### 3.2 模解 $\mathscr C$

$M=1$ 时只有一个矩阵类 $I$。$M=2$ 时，所有块上的线性化同时解耦，得到
\[
 \boxed{|\mathscr C_{F,2}(A)|=2^B,\qquad
 |\mathscr C_{K,2}(A)|=2^{D'}.}
\tag{3.4}
\]
若不可行，则对所有 $M\ge3$，
\[
 \boxed{\mathscr C_{L,M}(A)=\varnothing.}\tag{3.5}
\]
若可行，$M\ge3$ 时
\[
 \boxed{|\mathscr C_{F,M}(A)|=2^{B+r+(M-2)A},}
\tag{3.6}
\]
\[
 \boxed{|\mathscr C_{K,M}(A)|=2^{D'+r+(M-2)D}.}
\tag{3.7}
\]

证明组合了三个事实：按 (1.3) 选取 $U_0$；在每块上把 $U_0^{-1}\bar U$ 约化为 $O_{n_i}(\mathcal O_L/2^M)$ 中的一个元素；以及模 $2^M$ 的交错条件都化为同一个逐块自由 kernel。各块的贡献独立相乘。$M=2$ 的指数分别来自矩阵环的维数和条件 $H^T+H=0$；$M\ge3$ 时一层提升的 kernel 与 (2.4)、(2.5) 的增量相同。

空集的完整结论为
\[
 \mathscr R_{L,M}(A)=\varnothing\iff \mathscr S_L(A)=\varnothing,
\tag{3.8}
\]
\[
 \mathscr C_{L,M}(A)\ne\varnothing
 \iff M\in\{1,2\}\ \text{或}\ \mathscr S_L(A)\ne\varnothing.
\tag{3.9}
\]

### 3.3 $\bar U\in\mathscr R$ 的可核验判据

取 $U_0\in\mathscr S_L(A)$，把 $\bar U$ 写成 $U_0V$。则
\[
 V=\operatorname{diag}(V_1,\dots,V_r)
 \quad\text{模 }2^M
\]
且
\[
 \bar U\in\mathscr R_{L,M}(A)
 \iff V_i\in\operatorname{im}(\Omega_{n_i}^L(\mathcal O_L)\to O_{n_i}(\mathcal O_L/2^M))
 \quad(\forall i).
\tag{3.10}
\]
对有限环上的单块，$V_i$ 属于这个像当且仅当它可以提升到精度 $M+1$；这是可有限核验的，因为每个块只有 $2^{O(n_i^2M)}$ 个候选。等价地，可以检查所有斜伴一阶方向是否都满足同余方程；若以 $V_i=I+2X_i$ 写，显式条件是：存在 $X_i$ 使其满足
\[
 X_i^T+X_i+2X_i^TX_i=0\pmod{2^{M-1}}.
\tag{3.11}
\]
这不是“模解”式的空洞判据；$X_i$ 是有限环上的实际矩阵变量。

## 4. $\sigma_\mu$-固定点

以下 $K=K_\mu$。取 $\pi=\theta$（$\mu=2$）或 $\pi=1+\theta$（$\mu=-1$），故 $2=\pi^2u$ 且 $\pi^{2M}\mathcal O_K=2^M\mathcal O_K$。

### 4.1 真正解的固定点

若 $U\in\mathscr S_K(A)$ 且 $\sigma(U)=U$，则逐项有 $U\in M_d(F)$；又 $U\in GL_d(\mathcal O_K)$ 导致其逆也在 $GL_d(F)$，故 $U\in GL_d(\mathbb Z_2)$。因此
\[
 \boxed{\mathscr S_K(A)^\sigma=\mathscr S_F(A).}
\tag{4.1}
\]

### 4.2 模固定环和模解固定点

令
\[
 R_M=\mathcal O_K/2^M\mathcal O_K=\mathcal O_K/\pi^{2M},\qquad
 \varepsilon_M=2^{M-1}\pi=\pi^{2M-1}u.
\]
在 $R_M$ 中 $2\varepsilon_M=0$，$\varepsilon_M^2=0$，$\sigma(\varepsilon_M)=\varepsilon_M$。固定子环是
\[
 R_M^\sigma=\mathbb Z/2^M\mathbb Z\oplus\mathbb F_2\varepsilon_M.
\tag{4.2}
\]
因此每个固定矩阵类唯一写成
\[
 U=A+\varepsilon_M B,\qquad A\in M_n(\mathbb Z/2^M),\quad B\in M_n(\mathbb F_2).\tag{4.3}
\]
由 $U\equiv I\pmod2$，$A\equiv I\pmod2$。正交条件给
\[
 A^TA=I,\qquad A^TB+B^TA=0.\tag{4.4}
\]
在 $\mathbb F_2$ 上 $A\equiv I$，所以第二式是 $B+B^T=0$，即 $B$ 对称（特征 $2$ 中这是“对角项保留”的对称条件）。于是
\[
 \boxed{\mathscr C_{K,M}^\sigma
 \cong \mathscr C_{F,M}\times\operatorname{Sym}_n(\mathbb F_2)}
\tag{4.5}
\]
（对每个块作乘积）。因此
\[
 \boxed{c_n^{K,\sigma}(M)=c_n^F(M)2^{B_n}}
\tag{4.6}
\]
其中 $c_n^F$ 用 (2.4)。全块固定点数为
\[
 \boxed{|\mathscr C_{K,M}(A)^\sigma|
 =|\mathscr C_{F,M}(A)|2^{\sum_iB_{n_i}}.}
\tag{4.7}
\]
特别地 $M=1$ 为 $1$，$M=2$ 为 $2^{\sum_i n_i(n_i+1)}$。

### 4.3 精确像的固定点

在真正解的层上先用 (4.1) 把固定点限制到 $\mathscr S_F$；下面的模计数则用尺度化参数。令 $X=\pi X'$，$X'\in\mathfrak{so}_n(\mathcal O_K)$，并记 $t=\pi^2$。近单位部分可写成 $U=\eta\exp(tX')$，且 $t^M\mathcal O_K=2^M\mathcal O_K$。于是
\[
 \sigma(U)=U\iff X'=\sigma(X')\pmod{\pi^{2M-2}}.
\tag{4.8}
\]
在 $X'=X_0+\pi\theta Y$ 中，$\sigma(X')-X'=2\pi\theta Y$，而 $2\pi\theta$ 的赋值不超过 $\pi^3$ 加上一个单位。反复约化可把固定方向化为
\[
 X_0\in\mathfrak{so}_n(\mathbb Z_2)/2^{M-1}
\]
二阶作用下的不变子模在每个几何精度层增加 $2A_n=n(n-1)$ 个独立参数；最初两层要把模 $2$ 的退化单独记住。于是单块
\[
 \boxed{r_n^{K,\sigma}(M)=
 \begin{cases}1,&M=1,\\2^{1+2A_n},&M=2,\\2^{1+(2M-3)A_n},&M\ge3.\end{cases}}
\tag{4.9}
\]
例如 $n=2$ 时模 $2$ 后固定类数为 $1$，模 $4$ 为 $2^3=8$，模 $8$ 为 $2^4=16$。全部分块且可行时
\[
 \boxed{|\mathscr R_{K,M}(A)^\sigma|
 =\begin{cases}
 2^{r+2A},&M=2,\\[1mm]
 2^{r+(2M-3)A},&M\ge3.
 \end{cases}}
\tag{4.10}
\]
不可行时均为空；$M=1$ 时固定集为单点 $I$。

特别地，固定模类若来自真正的固定精确解，则只能来自嵌入的 $\mathscr R_{F,M}(A)$。反过来，$\mathscr R_{F,M}$ 的每个元素当然由某个 $W\in\mathscr S_F(A)$ 的代表诱导。因此精确判据是
\[
 x\in\mathscr C_{K,M}(A)^\sigma\text{ 能提升为真正固定解}
 \iff x\in\mathscr R_{F,M}(A).
\tag{4.11}
\]
写成 $x=A+\varepsilon_MB$ 时就是 $B=0$ 且 $A\in\mathscr R_{F,M}(A)$。这里 $B=0$ 指在固定环坐标中的延拓系数，不是说所有中间代表都没有 $\pi$ 项。若把 $x$ 嵌入 $\mathscr C_{K,M+1}$ 后仍为固定类，则它的约化已经必须在 (4.11) 中；反之逐层一直选 $\mathscr S_F$ 的同一 $W$ 就得到固定序列。

### 4.4 轨道数

$\sigma$ 是二阶置换，故对任何 $\sigma$-稳定有限集 $X$，
\[
 \#\operatorname{Orb}(\sigma;X)=\frac{|X|+|X^\sigma|}{2}.\tag{4.12}
\]
代入 (3.2)--(3.7) 及固定点 (4.6)、(4.9) 即得。单块和全块都不需另设公式；固定点集上作用平凡，故其轨道数就是其点数。

## 5. 约化像与非空纤维

仍先取单块；多块的纤维大小逐块相乘。

### 5.1 基域

\[
 \operatorname{im}(\mathscr C_{F,M+1}\to\mathscr C_{F,M})
 =\mathscr R_{F,M},\tag{5.1}
\]
非空纤维大小
\[
 \boxed{2^{B_n}}\qquad(M\ge1).
\tag{5.2}
\]
$M=1$ 时 $\mathscr C_F$ 只有单位元素，但提升纤维仍由下一层矩阵变量的全部 $B_n$ 个独立坐标给出，所以同一数值继续成立。
对行指标 $N$，即约化 $\mathscr R_{F,M+1}\to\mathscr R_{F,M}$：这是满射，纤维为 $2^{A_n}$。

### 5.2 二次扩张

\[
 \operatorname{im}(\mathscr C_{K,M+1}\to\mathscr C_{K,M})
 =\mathscr R_{K,M},\tag{5.3}
\]
非空纤维为 $2^{n(n+1)}$。对 $\mathscr R$ 的约化是满射，纤维为
\[
 2^{n(n-1)}.\tag{5.4}
\]
这些数也由 (2.4)、(2.5)、(3.2)、(3.3) 的直接比值验证。模 $2$ 时所有 $\pm1$ 合并，故 $M=1$ 的纤维从同一公式取。

### 5.3 固定子集

由 (4.5)，固定 $\mathscr C$ 的每个块是 $\mathscr C_{F}\times\operatorname{Sym}_n$，故对固定类的约化
\[
 \operatorname{im}\bigl(\mathscr C_{K,M+1}^\sigma\to\mathscr C_{K,M}^\sigma\bigr)
 =\mathscr R_{F,M},\tag{5.5}
\]
非空纤维为 $2^{n(n+1)}$：从固定模类的一层提升同时包含 $\mathscr C_F$ 的一层 kernel（$2^{B_n}$）和固定子环中 $\varepsilon B$ 的全部一层提升（$2^{B_n}$）。（$\operatorname{Sym}$ 因子本身不会产生新的精确类；这正是固定类坐标中 $B$ 项的线性障碍）。对固定 $\mathscr R$，由 (4.9) 得
\[
 \operatorname{im}\bigl(\mathscr R_{K,M+1}^\sigma\to\mathscr R_{K,M}^\sigma\bigr)
 =\mathscr R_{F,M},\tag{5.6}
\]
纤维为
\[
\begin{cases}
2^{r+2A_n},&\text{源精度 }M+1=2,\\[1mm]
2^{A_n},&\text{源精度 }M+1=3,\\[1mm]
2^{n(n-1)},&\text{源精度 }M+1\ge4.
\end{cases}
\tag{5.7}
\]

一个固定模类 $x$ 能作为**所有更高精度**都固定且逐层相容的序列在 $M$ 处的分量，当且仅当 $x\in\mathscr R_{F,M}(A)$：必要性来自 (4.11)，充分性取同一个 $W\in\mathscr S_F(A)$ 的所有约化；单次一层提升的条件较弱，正是 4.1 节在固定类中解 (4.4)。这个判据与 $M=2$ 的例化一致：$\mathscr C^\sigma$ 虽很大，能一直提升的只是嵌入的基域精确像。

## 6. 下降的最大统一精度

设 $n_i$ 固定，$M\ge2$，并令 $U\in\mathscr S_{K_\mu}(A)$ 满足
\[
 \sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_K}.\tag{6.1}
\]

### 定理 6.1

\[
 \boxed{N_{\max}=
 \begin{cases}
 M,&n_1=\cdots=n_r=1,\\[1mm]
 M-1,&\text{否则}.
 \end{cases}}
\tag{6.2}
\]

**上界.** 若某个 $n_j\ge2$，取 $A_i=E_i$。令
\[
 C=E_{12}^{(j)}-(E_{12}^{(j)})^T,\qquad
 U=\operatorname{diag}(I_{n_1},\dots,U_j,\dots,I_{n_r}),
\]
\[
 U_j=\exp(\pi^{2M-1}C).
\]
则 $U\in O_d(\mathcal O_K)$，$U\equiv I\pmod{2\mathcal O_K}$，并且它保持标准块。又
\[
 \sigma(U_j)=\exp(-\pi^{2M-1}C),\qquad
 \sigma(U)U^{-1}=\exp(-2\pi^{2M-1}C)
 =\exp(-u\pi^{2M+1}C),\tag{6.3}
\]
它在模 $2^M=\pi^{2M}$ 下等于 $I$。所以条件 (6.1) 成立。然而 $U$ 的第一非对角条目等于 $\pi^{2M-1}$（模 $\pi^{2M}$），任何 $W\in GL_d(\mathbb Z_2)$ 的同一坐标都在 $\mathcal O_K$ 的实子环 $\mathbb Z_2$ 中，不能与它相差 $\pi^{2M}$。所以不存在精度 $M$ 的基域逼近。这个构造对每个 $M$ 都成立。

**下界.** 取 $U_0\in\mathscr S_F(A)$。写 $U=U_0\prod_iV_i$。这里 $V_i$ 先属于整系数正交群 $O_{n_i}(\mathbb O)$，$\mathbb O=\mathbb Z_2[\sqrt2]$；直接把它当作“$\pm I$ 乘以指数”会漏掉可能存在的无限阶整格元素，因此后面的指数计算只对近单位主同余部分作陈述，不能无条件套到整个 $O_{n_i}(\mathbb O)$。

各块是正交直和，故记 $\Omega_{n_i}(\mathbb O)=\{g\in O_{n_i}(\mathbb O):g\equiv I\pmod2\}$。$\Omega_{n_i}(\mathbb O)$ 是模 $2^M$ 下指数变量所在的主同余群；其余部分记为 $O_{n_i}(\mathbb O)\to O_{n_i}(\mathbb F_2)$ 的截面像。这里不把任意整格元素误写成有限个 $\pm I$。取 $U_0\in\mathscr S_F(A)$ 后，$U_0^{-1}U$ 是块对角的；逐块分解为主同余部分与模 $2$ 截面部分，正是下面对数计算所需的分解。

在模 $\pi^{2M}$ 的近单位主同余子群上，$p$-adic 对数在 $\pi^2M_n$ 上是同构，且
\[
 V_i=\eta_i\exp(\pi^2X_i),\qquad \eta_i=\pm I,\qquad
 X_i\in\mathfrak{so}_{n_i}(\mathcal O_K).\tag{6.4a}
\]
对这部分，由 (6.1)，
\[
 X_i-\sigma(X_i)\in\pi^{2M-2}\mathfrak{so}_{n_i}(\mathcal O_K).
\]
写 $X_i=X_i^{(0)}+\pi\theta_iY_i$（$X_i^{(0)}$ 是常值基域部分），得
\[
 2\pi\theta_iY_i\in\pi^{2M-2}\mathfrak{so}.
\]
由于 $2=\pi^2u$，这迫使 $\pi\theta_iY_i\in\pi^{2M-2}\mathfrak{so}$，从而把它换成一个斜伴的整数系数矩阵并令其 $\pi$ 部分为零，只会改变 $X_i$ 的 $\pi^{2M-3}$ 量级。指数映射在相关滤过上是同构，于是
\[
 V_i\equiv\eta_i\exp(\pi^2X_i^{(0)})
 \pmod{\pi^{2M-2}\mathcal O_K}.
\]
右端来自 $F$ 上的同一个幂等块矩阵，且 $\pi^{2M-2}=2^{M-1}$。因此存在 $W\in\mathscr S_F(A)$ 使
\[
 U\equiv W\pmod{2^{M-1}\mathcal O_K}.\tag{6.4}
\]
当所有 $n_i=1$ 时，$O_1(\mathcal O_K)=\{\pm1\}$，精确固定解与基域解相同，故可直接取 $N=M$。

把上述逐块分解中的主同余部分舍去 $\pi^{2M-3}$ 及更高阶项，再与其模 $2$ 截面部分相乘，就得到一个基域正交矩阵 $W$。由 (6.4a) 的指数同构，这个舍入在每个非空纤维中都有代表，且只改变 $\pi^{2M-2}$ 倍；再把 $U_0$ 左乘回去即得 (6.4)。若一个给定的模类在舍入后改变了其模 $2^M$ 的类，则它在 (6.7) 中恰恰不满足 $B_V=0$。

### 6.2 给定 $A,U$ 何时 $N=M$

把 $U$ 的模类视为 $\mathscr R_{K,M}(A)$ 和嵌入的 $\mathscr R_{F,M}(A)$。则
\[
 \boxed{N=M
 \iff U\bmod 2^M\in\mathscr R_{F,M}(A).}
\tag{6.5}
\]
取 $U_0\in\mathscr S_F(A)$，令 $V=U_0^{-1}U\bmod 2^M$，并写固定坐标
\[
 V=A_V+\varepsilon_MB_V.\tag{6.6}
\]
于是
\[
 N=M\iff B_V=0\ \text{且}\ A_V\in\prod_i\operatorname{im}(\Omega_{n_i}^F\to O_{n_i}(\mathbb Z/2^M)).\tag{6.7}
\]
最后一项正是 (3.10) 的基域版本，可用上一层提升或显式方程 (3.11) 核验。若存在某个 $n_i\ge2$，由 (6.3) 的统一定义 $U_M$ 得该模类不属于 $\mathscr R_{F,M}$（它在固定坐标中的 $B_V$ 项非零），所以 $N=M$ 的统一性确实失败；这些例子对每个 $M$ 分别定义，因而形成任意精度的否定族。

## 7. 最终摘要与自评

保留并修正后的核心结构是：Hensel 投影把问题约化为正交格的稳定性；基域和二次扩张的精确像分别由各自的单位根和指数 Lie 滤过决定；模解与精确像的差异来自一层有限 kernel；$\sigma$ 在真正解层上的固定点是基域解。上稿中把 $\mathscr C$ 的模 $2^M$ 维数误写成与精确像的 Lie 秩相同，导致 $\mathscr C$ 及固定点基数错误；本稿改用逐层 kernel，得到 (2.4)--(2.5) 和 (3.4)--(3.7)。同时把提升判据保留为上一层实际可枚举的方程，避免把“存在某个精确解”当作已经构造。

对固定模类的逐层提升，本文给出的是等价于上一层有限方程的实际核验判据，而非一个只含 Frobenius 范数和行列式的初等公式。原因是当模精度升高时，$\bar U$ 的非 Lie 项会进入固定子环的 $\varepsilon\mathbb F_2$ 方向；将其误读为固定 Lie 方向正是上一稿的错误来源。此类项无需继续猜测：在精度 $M$ 的固定环（4.2）中直接解 (4.4)，即得到有限、可核验的判据。除此之外，第 1--6 节已覆盖题目要求的结构、精确计数、固定点、约化纤维和最大下降精度。
