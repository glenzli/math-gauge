三个域上的可行性判准完全相同。区别出现在有限精度：形式解可能不能提升，而扩域上的固定矩阵类也可能不能下降。

记
\[
D=\sum_{i=1}^r\binom{n_i}{2},\qquad s=D+d,\qquad
q_L=|\mathcal O_L/2\mathcal O_L|
=\begin{cases}2,&L=F,\\4,&L=K_\mu.\end{cases}
\]
定义可由 \(A_i\bmod4\) 直接计算的数
\[
\epsilon_i=
\sum_{\substack{a\in I_i\\b\notin I_i}}
\left(\frac{(A_i)_{ba}}2\right)^2\pmod2
\quad\in\mathbb F_2,
\]
以及
\[
\eta=\begin{cases}
1,&\epsilon_1=\cdots=\epsilon_r=0,\\
0,&\text{否则}.
\end{cases}
\]

对题中的每个 \(L\)，有
\[
\boxed{\mathscr S_L(A)\ne\varnothing\iff\eta=1.}
\]
全部基数为
\[
\boxed{|\mathscr R_{L,M}(A)|=\eta\,2^r q_L^{(M-1)D}}
\]
及
\[
\boxed{
|\mathscr C_{L,M}(A)|=
\begin{cases}
q_L^{D+d},&M=2,\\
\eta\,2^r q_L^{(M-1)D+d},&M\ge3.
\end{cases}}
\]
特别地，\(\mathscr C_{L,2}(A)\) 总非空；其他集合的空集条件由上述公式完全给出。

对任意 \(\bar U\in\mathscr C_{L,M}(A)\)，任取条目提升
\(\widetilde U\in M_d(\mathcal O_L)\)，则有可核验的提升判准
\[
\boxed{
\bar U\in\mathscr R_{L,M}(A)
\iff
\sum_{k=1}^d\widetilde u_{ka}^{\,2}
\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le a\le d). }\tag{1}
\]
这里的条件与提升的选择无关。也就是说，只须额外检查每一列范数的下一位。

为描述固定点，置
\[
\varpi_\mu=
\begin{cases}
1+\theta_{-1},&\mu=-1,\\
\theta_2,&\mu=2.
\end{cases}
\]
于是
\[
\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\varpi_\mu,\qquad
\varpi_{-1}^2=2\theta_{-1},\quad \varpi_2^2=2.
\]
令
\[
\operatorname{Sym}_{\mathcal I}
=\{\text{按 }I_1,\ldots,I_r\text{ 分块对角的对称 }\mathbb F_2\text{ 矩阵}\},
\]
\[
\operatorname{Alt}_{\mathcal I}
=\{Z\in\operatorname{Sym}_{\mathcal I}:\operatorname{diag}Z=0\}.
\]
它们的维数分别为 \(s=D+d\) 和 \(D\)。以下把这些矩阵任意提升为整数矩阵；所得模类不依赖提升选择。

所有精度 \(M\ge2\) 上均有统一的、表示唯一的公式
\[
\boxed{
\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
=
\left\{
V+2^{M-1}\varpi_\mu Z:
V\in\mathscr C_{F,M}(A),\
Z\in\operatorname{Sym}_{\mathcal I}
\right\}, }\tag{2}
\]
\[
\boxed{
\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
=
\left\{
V+2^{M-1}\varpi_\mu Z:
V\in\mathscr R_{F,M}(A),\
Z\in\operatorname{Alt}_{\mathcal I}
\right\}. }\tag{3}
\]
加法在模 \(2^M\mathcal O_\mu\) 的矩阵环中进行。这也给出了它们与基域集合的精确关系；尤其
\[
\mathscr R_{K_\mu,M}(A)\cap M_d(\mathbb Z_2/2^M)
=\mathscr R_{F,M}(A),
\]
\[
\mathscr C_{K_\mu,M}(A)\cap M_d(\mathbb Z_2/2^M)
=\mathscr C_{F,M}(A).
\]

固定点数为
\[
\boxed{
|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}|
=\eta\,2^{r+MD},}
\]
\[
\boxed{
|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}|
=
\begin{cases}
2^{2(D+d)},&M=2,\\
\eta\,2^{r+MD+2d},&M\ge3.
\end{cases}}
\]
相应的轨道数为
\[
\boxed{
\#\bigl(\mathscr R_{K_\mu,M}(A)/\langle\sigma_\mu\rangle\bigr)
=
\eta\,2^{r-1}
\left(2^{2D(M-1)}+2^{MD}\right),}
\]
以及
\[
\boxed{
\#\bigl(\mathscr C_{K_\mu,M}(A)/\langle\sigma_\mu\rangle\bigr)
=
\begin{cases}
2^{2(D+d)},&M=2,\\
\eta\,2^{r+2d-1}
\left(2^{2D(M-1)}+2^{MD}\right),&M\ge3.
\end{cases}}
\]
单点轨道数就是固定点数，其余轨道均含两个元素。特别地，在模 \(4\) 层，两种扩域集合上的作用都平凡。

从精度 \(M+1\) 到 \(M\) 的约化映射如下；表中列出全部非空纤维的大小，\(L\) 可为三个域中的任意一个。

| 约化映射 | 像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{L,M+1}\to\mathscr R_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^D\) |
| \(\mathscr C_{L,M+1}\to\mathscr C_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^{D+d}\) |
| \(\mathscr R_{K_\mu,M+1}^{\sigma_\mu}\to\mathscr R_{K_\mu,M}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(2^{2D}\) |
| \(\mathscr C_{K_\mu,M+1}^{\sigma_\mu}\to\mathscr C_{K_\mu,M}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(2^{2(D+d)}\) |

这里及下文省略的参数 \(A\) 均保持不变。如果像为空，就没有非空纤维。

对上述任一种固定矩阵类，以下条件等价：

- 它能提升为一个 \(\sigma_\mu\)-固定的真正解；
- 它能成为一条逐层相容的固定矩阵类序列在精度 \(M\) 的分量；
- 它能提升到下一精度的固定点集；
- 它属于嵌入的 \(\mathscr R_{F,M}(A)\)。

因此，在表示 (3) 中，条件就是 \(Z=0\)；在表示 (2) 中，条件是 \(Z=0\) 且 \(V\in\mathscr R_{F,M}(A)\)。

第三问的最大整数为
\[
\boxed{
N_{\max}=
\begin{cases}
M,&D=0\quad(\text{即所有 }n_i=1),\\
M-1,&D>0.
\end{cases}}\tag{4}
\]
事实上，所有块秩均为 \(1\) 时，有更强的等式
\[
\mathscr S_{K_\mu}(A)=\mathscr S_F(A).
\]

对给定的题设 \(A,U\)，逐条目唯一写成
\[
U=A_0+\theta_\mu B_0,\qquad A_0,B_0\in M_d(\mathbb Z_2).
\]
能取 \(N=M\) 的必要充分条件是
\[
\boxed{
B_0\equiv0\pmod{2^M}
\iff
\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}. }\tag{5}
\]

下面证明全部结论，并给出反例和最优性构造。

对每个 \(A_i\) 迭代多项式
\[
f(X)=3X^2-2X^3.
\]
由于 \(A_i^2-A_i\in2M_d(\mathbb Z_2)\)，且
\[
f(X)-X=-(2X-1)(X^2-X),
\]
\[
f(X)^2-f(X)=(X^2-X)^2(4X^2-4X-3),
\]
迭代在 \(2\)-进拓扑中收敛到一个对称幂等矩阵 \(P_i\)，满足
\[
P_i\equiv E_i\pmod2.
\]
这些矩阵彼此交换，也与全部 \(A_j\) 交换。

当 \(i\ne j\) 时，\(P_iP_j\) 是模 \(2\) 为零的幂等矩阵，因此为零：若 \(Q^2=Q\) 且 \(Q\in2M_d(\mathbb Z_2)\)，则 \(Q=Q^{2^k}\) 被任意高的 \(2\) 次幂整除。同理，
\[
P_iP_j=0\ (i\ne j),\qquad \sum_iP_i=I.
\]
所以它们给出一个正交直和分解。

每个 \(\operatorname{im}P_i\) 都有唯一的图形基矩阵 \(B_i\)：其在 \(I_i\) 上的行组成 \(I_{n_i}\)，其余行组成一个矩阵 \(Y_i\in2M_{d-n_i,n_i}(\mathbb Z_2)\)。令
\[
B=(B_1\ \cdots\ B_r).
\]
则
\[
B\equiv I\pmod2,\qquad
B^{\mathsf T}B=\operatorname{diag}(H_1,\ldots,H_r),
\]
其中
\[
H_i=I_{n_i}+Y_i^{\mathsf T}Y_i
=I_{n_i}+4C_i,\qquad
C_i=(Y_i/2)^{\mathsf T}(Y_i/2).\tag{6}
\]
而且每个 \(B^{\mathsf T}A_jB\) 都按给定块分块对角。

写 \(A_i=E_i+2D_i\)，在模 \(4\) 下计算一次 \(f\) 即得
\[
P_i\equiv E_i+2(E_iD_i+D_iE_i)\pmod4.
\]
因此
\[
Y_i\equiv (A_i)_{I_i^c,I_i}\pmod4,
\qquad
\operatorname{tr}C_i\equiv\epsilon_i\pmod2.\tag{7}
\]

这个分解也控制所有有限精度解。若 \(U\) 是真正解或模 \(2^M\) 的形式解，则 \(U^{\mathsf T}P_iU\) 是分块对角的幂等矩阵，并且模 \(2\) 等于 \(E_i\)。在每个块上，模 \(2\) 为零的幂等矩阵必为零，模 \(2\) 为单位阵的幂等矩阵必为单位阵。这个论证在有限商环中同样成立。因此
\[
U^{\mathsf T}P_iU=E_i.
\]
于是所有解都唯一写成
\[
U=B\,\operatorname{diag}(T_1,\ldots,T_r),\qquad T_i\equiv I\pmod2,
\]
相应的正交条件恰为
\[
T_i^{\mathsf T}H_iT_i=I,\tag{8}
\]
或者其模 \(2^M\) 版本。

以下使用一个初等的矩阵平方根事实。对题中的任一整数环，若对称矩阵
\[
G\equiv I\pmod{2^\ell},\qquad \ell\ge3,
\]
则二项式级数定义
\[
G^{-1/2}\in I+2^{\ell-1}M_n(\mathcal O_L).
\]
该矩阵对称、与 \(G\) 交换，并满足
\[
(G^{-1/2})^{\mathsf T}G\,G^{-1/2}=I.
\]
收敛性可直接由
\[
\binom{-1/2}{k}=(-1)^k\frac{\binom{2k}{k}}{4^k}
\]
验证：乘上 \(2^{\ell k}\) 后的系数整除性随 \(k\) 趋于无穷，且所有非常数项都被 \(2^{\ell-1}\) 整除。正平方根有相同的整除性结论。

现在证明可行性。考虑一个块
\[
H=I+4C,\qquad C\in M_n(\mathbb Z_2),\quad C^{\mathsf T}=C.
\]
若 \(T=I+2X\) 满足 \(T^{\mathsf T}HT=I\)，模 \(4\) 的条件首先给出
\[
X\equiv X^{\mathsf T}\pmod2.
\]
模 \(8\) 的对角条件是
\[
c_j+x_{jj}+\sum_kx_{kj}^2=0
\quad\text{于 }\mathcal O_L/2\mathcal O_L,\qquad
c_j=C_{jj}\bmod2.\tag{9}
\]

在基域上，平方映射是恒等映射。在两个扩域上，利用
\[
\mathcal O_\mu/2\mathcal O_\mu
=\mathbb F_2[\varpi_\mu]/(\varpi_\mu^2),
\]
写 \(x_{kj}=a_{kj}+b_{kj}\varpi_\mu\)，便有 \(x_{kj}^2=a_{kj}\)。所以 (9) 分别化为
\[
\sum_{k\ne j}a_{kj}=c_j,
\]
以及扩域情形额外的 \(b_{jj}=0\)。由于 \(a_{kj}=a_{jk}\)，对 \(j\) 求和得到必要条件
\[
\sum_jc_j=0.\tag{10}
\]

反过来，若 (10) 成立，可以在 \(\mathbb F_2\) 上选择对称零对角矩阵 \(X\)，使
\[
\sum_{k\ne j}X_{kj}=c_j.
\]
例如只使用连接第 \(n\) 个顶点的边即可；\(n=1\) 时取零矩阵。于是 \(T_0=I+2X\) 的 Gram 矩阵模 \(4\) 为单位阵，且对角误差被 \(8\) 整除。再右乘一个 \(I+4Y\)，可消去模 \(8\) 的全部非对角误差。最后应用上述逆平方根，得到一个真正的
\[
T\in I+2M_n(\mathbb Z_2),\qquad T^{\mathsf T}HT=I.
\]
结合 (6)、(7)，这证明了三个域上相同的可行性判准。

可行时，固定一个 \(W\in\mathscr S_F(A)\)。上述规范分解还给出
\[
\mathscr S_L(A)
=
W\prod_{i=1}^r
\{Q_i\in\operatorname O_{n_i}(\mathcal O_L):Q_i\equiv I\pmod2\},\tag{11}
\]
其中右边的乘积按块嵌入。

接着证明提升判准 (1)。若改变一列的提升 \(v\) 为 \(v+2^Mz\)，其范数变化为
\[
2^{M+1}v^{\mathsf T}z+2^{2M}z^{\mathsf T}z,
\]
故模 \(2^{M+1}\) 的范数不变，必要性也立即成立。

为证充分性，利用规范分解，把给定形式解提升成
\[
\widetilde U=B\operatorname{diag}(T_i).
\]
每块 Gram 矩阵可写为
\[
G_i=T_i^{\mathsf T}H_iT_i=I+2^MS_i,
\]
其中 \(S_i\) 对称，而条件 (1) 保证其对角被 \(2\) 整除。选择 \(Y_i\) 使
\[
Y_i+Y_i^{\mathsf T}\equiv-S_i\pmod2.
\]
右乘 \(I+2^MY_i\) 后，Gram 矩阵变为模 \(2^{M+1}\) 的单位阵。再应用逆平方根，修正矩阵属于 \(I+2^MM_{n_i}(\mathcal O_L)\)，所以不改变原来的模 \(2^M\) 类，却得到真正解。这证明 (1)。

它还立即证明
\[
\operatorname{im}\bigl(\mathscr C_{L,M+1}\to\mathscr C_{L,M}\bigr)
=\mathscr R_{L,M}.\tag{12}
\]
特别地，若 \(\eta=0\)，则所有 \(M\ge3\) 的形式解集均为空。

下面计算基数。对一个秩为 \(n\) 的块，记 \(k=\binom n2\)。模 \(4\) 的形式正交矩阵为
\[
I+2X,\qquad X\in M_n(\mathcal O_L/2\mathcal O_L),\quad X=X^{\mathsf T},
\]
所以共有 \(q_L^{k+n}\) 个。此计算也适用于 (6) 的 \(H\)，因为 \(H\equiv I\pmod4\)，故无论是否可行，所有块相乘都给出
\[
|\mathscr C_{L,2}|=q_L^{D+d}.
\]

对于真正正交矩阵的模 \(4\) 像，条件 (9) 中 \(c_j=0\)。对角有 \(2^n\) 种选择；非对角共有 \(q_L^k\) 种选择，而其标量部分的度数方程有 \(n-1\) 个独立条件。因而
\[
|\mathscr R_{n,L,2}|=2^n\frac{q_L^k}{2^{n-1}}=2q_L^k.\tag{13}
\]
这里度数映射的像正是坐标和为零的向量空间，前述星形构造也证明了其秩为 \(n-1\)。

对 \(M\ge2\)，真正解约化映射的核由
\[
I+2^MX\pmod{2^{M+1}}
\]
给出。正交条件和 (1) 分别要求
\[
X=X^{\mathsf T},\qquad \operatorname{diag}X=0
\quad\text{于 }\mathcal O_L/2\mathcal O_L.
\]
故每块核大小为 \(q_L^k\)。而形式解在一个可提升类上方的纤维只要求 \(X=X^{\mathsf T}\)，大小为 \(q_L^{k+n}\)。结合 (11)—(13)，即得全部基数公式及约化表的前两行。

再证明固定点公式。由于 \(\{1,\varpi_\mu\}\) 是整数基，标量模类固定当且仅当其 \(\varpi_\mu\) 系数被 \(2^{M-1}\) 整除。因此每个固定矩阵类唯一写成
\[
\bar U=V+2^{M-1}\varpi_\mu Z,\qquad
V\in M_d(\mathbb Z_2/2^M),\quad Z\in M_d(\mathbb F_2).\tag{14}
\]
展开正交方程，注意平方项
\[
2^{2M-2}\varpi_\mu^2 Z^{\mathsf T}Z
\]
被 \(2^M\) 整除。比较 \(\varpi_\mu\) 系数，得到 \(Z=Z^{\mathsf T}\)，随后得到 \(V^{\mathsf T}V=I\)。

同样展开分块条件，并使用 \(A_i\equiv E_i\)、\(V\equiv I\pmod2\)，其 \(\varpi_\mu\) 系数要求
\[
[E_iZ+ZE_i,E_j]=0\qquad(\forall i,j)
\]
于 \(\mathbb F_2\)。这恰好迫使 \(Z\) 按给定块分块对角；其余条件恰为 \(V\in\mathscr C_{F,M}(A)\)。这就证明 (2)。

由于
\[
2^{2M-2}\varpi_\mu^2\in2^{M+1}\mathcal O_\mu
\qquad(M\ge2),
\]
第 \(a\) 列在 (1) 中的下一位误差为
\[
\frac{(V^{\mathsf T}V-I)_{aa}}{2^M}
+\varpi_\mu Z_{aa}
\quad\text{于 }\mathcal O_\mu/2\mathcal O_\mu.
\]
因 \(1,\varpi_\mu\) 在该环上是 \(\mathbb F_2\)-基，此式为零当且仅当
\[
V\in\mathscr R_{F,M}(A),\qquad Z_{aa}=0\quad(\forall a).
\]
这证明 (3)。

固定点数现由唯一表示直接得到；轨道数则由二阶群的公式
\[
\#\text{轨道}=\frac{|\text{集合}|+|\text{固定点}|}{2}
\]
给出。

在下一精度的 (2)、(3) 中，附加项为 \(2^M\varpi_\mu Z\)，约化到模 \(2^M\) 后消失。因此固定点约化的像都是 \(\mathscr R_{F,M}\)。其纤维大小分别为
\[
2^D\cdot2^D=2^{2D},
\qquad
2^{D+d}\cdot2^{D+d}=2^{2(D+d)},
\]
证明约化表的后两行。

真正解逐条目固定恰好意味着它属于基域，因此
\[
\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A).
\]
结合固定点约化像，这也证明了关于固定真正提升及相容固定序列的全部等价条件。事实上，能多提升一层固定类，就已经能由一个基域真正解给出整个相容序列。

最后证明下降界及其最优性。给定第三问的 \(U\)，由 (3) 可写
\[
U\bmod2^M=V+2^{M-1}\varpi_\mu Z,
\qquad V\in\mathscr R_{F,M}(A).
\]
选择 \(W\in\mathscr S_F(A)\) 提升 \(V\)，便有
\[
U\equiv W\pmod{2^{M-1}\mathcal O_\mu}.
\]
能达到精度 \(M\) 当且仅当 \(Z=0\)，也就是 \(U\) 的所有 \(\theta_\mu\) 系数均被 \(2^M\) 整除。由
\[
\sigma_\mu(U)-U=-2\theta_\mu B_0
\]
并比较整数基系数，得到 (5)。

若 \(D=0\)，每块秩均为 \(1\)。在 (11) 中，一维正交群只有 \(\{\pm1\}\)，所以全部扩域真正解本来就在基域，证明此时的精确下降。

若 \(D>0\)，选取同一块内两个坐标，令 \(A_i=E_i\)。对任意 \(M\ge2\)，置
\[
b=2^{M-1}\varpi_\mu,\qquad a=(1-b^2)^{1/2},
\]
选择满足 \(a\equiv1\pmod4\) 的平方根。因为
\[
b^2\in2^{2M-1}\mathcal O_\mu,
\]
该平方根存在，且
\[
a-1\in2^{2M-2}\mathcal O_\mu\subseteq2^M\mathcal O_\mu.
\]
在选定二维坐标上放置
\[
U_M=
\begin{pmatrix}a&b\\-b&a\end{pmatrix},
\]
其余坐标取单位阵。则
\[
U_M^{\mathsf T}U_M=I,\qquad U_M\equiv I\pmod2,
\qquad \sigma_\mu(U_M)\equiv U_M\pmod{2^M}.
\]
但 \(b\) 的 \(\theta_\mu\) 系数恰为 \(2^{M-1}\)，故不可能模 \(2^M\) 同余于任何基域矩阵。这是适用于所有 \(M\) 的统一反例，证明 (4) 最优；它也给出了固定的真正解约化不能提升为固定真正解、不能进入相容固定序列的实际例子。把 \(U_2\) 约化到任意 \(M\ge3\)，又得到非固定元素及二元素轨道的例子。

其余可能的否定情形也都有直接例子：

- **形式解存在而真正解不存在。** 取 \(r=2,n_1=n_2=1\)，
  \[
  A_1=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix},
  \qquad
  A_2=I-A_1.
  \]
  它们满足全部题设，但 \(\epsilon_1=\epsilon_2=1\)，故三个域上的真正解集均为空。矩阵
  \[
  B=\begin{pmatrix}1&-2\\2&1\end{pmatrix}
  \]
  满足 \(B^{\mathsf T}B=5I\)，且同时分块，所以 \(B\bmod4\) 是形式解。任意给定的 \(r\ge2\) 和块秩，都可在两个不同块各选一个坐标嵌入此例。

- **任意精度上的扩域固定形式解不能提升。** 取 \(A_i=E_i\)，在任一对角位置放置
  \[
  c=1+2^{M-1}\varpi_\mu,
  \]
  其余对角位置放 \(1\)。所得类属于 \(\mathscr C_{K_\mu,M}^{\sigma_\mu}\)，但
  \[
  c^2-1\equiv2^M\varpi_\mu\not\equiv0
  \pmod{2^{M+1}\mathcal O_\mu}.
  \]
  故它不属于 \(\mathscr R_{K_\mu,M}\)，也不在下一层形式解或固定形式解的约化像中。这同时给出固定形式解严格多于基域形式解的例子。

- **基域形式解不能提升。** 对任意 \(M\ge3\)，在 \(A_i=E_i\) 的情形使用对角元素 \(1+2^{M-1}\)，其平方模 \(2^M\) 为 \(1\)，模 \(2^{M+1}\) 却不是 \(1\)。当 \(M=2\) 且有块秩至少为 \(2\) 时，在该块内取
  \[
  I+2(E_{ab}+E_{ba}).
  \]
  它模 \(4\) 正交，但第 \(a,b\) 列范数为 \(5\bmod8\)，所以不能提升。若所有块秩均为 \(1\) 且 \(\eta=1\)，则模 \(4\) 上确实有 \(\mathscr C_{F,2}=\mathscr R_{F,2}\)，与基数公式一致。