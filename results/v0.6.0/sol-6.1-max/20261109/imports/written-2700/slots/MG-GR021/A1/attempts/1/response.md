记
\[
k=\sum_{i=1}^r\binom{n_i}{2},\qquad
e_F=1,\quad e_{K_{-1}}=e_{K_2}=2.
\]
对每块定义
\[
\delta_i=
\sum_{\substack{a\notin I_i\\ b\in I_i}}
\frac{(A_i)_{ab}}2\pmod2\in\mathbb F_2,
\qquad
\chi=
\begin{cases}
1,&\delta_1=\cdots=\delta_r=0,\\
0,&\text{否则}.
\end{cases}                                                   \tag{1}
\]
这些商均有意义，且只用到 \(A_i\bmod4\)。

全部三个域上的可行性判准相同：
\[
\boxed{\quad \mathscr S_L(A)\ne\varnothing\iff\chi=1.\quad}       \tag{2}
\]
精确基数为
\[
\boxed{
\begin{aligned}
|\mathscr R_{L,M}(A)|
   &=\chi\,2^{\,e_Lk(M-1)+r} &&(M\ge2),\\
|\mathscr C_{L,2}(A)|
   &=2^{\,e_L(k+d)},\\
|\mathscr C_{L,M}(A)|
   &=\chi\,2^{\,e_Lk(M-1)+e_Ld+r} &&(M\ge3).
\end{aligned}}                                                \tag{3}
\]
因此 \(\mathscr C_{L,2}\) 总非空；其余各集合的空性由 \(\chi\) 完全决定。

对 \(\bar U\in\mathscr C_{L,M}(A)\)，任取逐条目提升 \(V\in M_d(\mathcal O_L)\)，则
\[
\boxed{\quad
\bar U\in\mathscr R_{L,M}(A)
\iff
(V^{\mathsf T}V)_{aa}\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le a\le d).
\quad}                                                        \tag{4}
\]
右边与提升的选择无关，故这是有限可核验条件。

为描述固定矩阵类，取
\[
\varpi_{-1}=1+\theta_{-1},\qquad \varpi_2=\theta_2.
\]
它们均为素元，并满足
\[
\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\varpi_\mu,\qquad
\varpi_\mu^2\in2\mathcal O_\mu,\qquad
\sigma_\mu(\varpi_\mu)-\varpi_\mu=-2\theta_\mu.
\]
设
\[
\begin{aligned}
\operatorname{Sym}_{\mathbf n}
 &=\{Y\in M_d(\mathbb F_2):[Y,E_i]=0,\ Y^{\mathsf T}=Y\},\\
\operatorname{Alt}_{\mathbf n}
 &=\{Y\in\operatorname{Sym}_{\mathbf n}:Y_{aa}=0\ \forall a\}.
\end{aligned}
\]
其维数分别为 \(k+d\) 和 \(k\)。这里特征 \(2\) 下的 \(\operatorname{Alt}\) 指对称且对角为零。

固定点的具体矩阵类为
\[
\boxed{
\begin{aligned}
\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
 &=\left\{X+2^{M-1}\varpi_\mu Y:
       X\in\mathscr R_{F,M}(A),\
       Y\in\operatorname{Alt}_{\mathbf n}\right\},\\
\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
 &=\left\{X+2^{M-1}\varpi_\mu Y:
       X\in\mathscr C_{F,M}(A),\
       Y\in\operatorname{Sym}_{\mathbf n}\right\}.
\end{aligned}}                                                \tag{5}
\]
加法在模 \(2^M\mathcal O_\mu\) 中进行，\(Y\) 任取 \(0,1\) 提升；两式中的参数表示都唯一。特别地，扩域集合中的基域矩阵类恰为基域相应集合：
\[
\begin{aligned}
\mathscr R_{K_\mu,M}(A)\cap M_d(\mathbb Z_2/2^M)
 &=\mathscr R_{F,M}(A),\\
\mathscr C_{K_\mu,M}(A)\cap M_d(\mathbb Z_2/2^M)
 &=\mathscr C_{F,M}(A).
\end{aligned}                                                 \tag{6}
\]

固定点数及轨道数如下：
\[
\begin{array}{c|c|c}
\text{集合}&\text{固定点数}&\langle\sigma_\mu\rangle\text{ 轨道数}\\ \hline
\mathscr R_{K_\mu,M}
&\chi\,2^{kM+r}
&\displaystyle\frac{\chi}{2}
 \left(2^{2k(M-1)+r}+2^{kM+r}\right)\\[2mm]
\mathscr C_{K_\mu,2}
&2^{2(k+d)}
&2^{2(k+d)}\\[1mm]
\mathscr C_{K_\mu,M},\ M\ge3
&\chi\,2^{kM+2d+r}
&\displaystyle\frac{\chi}{2}
 \left(2^{2k(M-1)+2d+r}+2^{kM+2d+r}\right)
\end{array}                                                   \tag{7}
\]
两种扩张的这些数字相同。精度 \(2\) 时作用均平凡；若 \(k=0\)，各精度上的作用都平凡。

对每个 \(M\ge2\)，约化像和非空纤维大小为
\[
\begin{array}{c|c|c}
\text{约化映射}&\text{像}&\text{每个非空纤维的大小}\\ \hline
\mathscr R_{L,M+1}\longrightarrow\mathscr R_{L,M}
&\mathscr R_{L,M}&2^{e_Lk}\\
\mathscr C_{L,M+1}\longrightarrow\mathscr C_{L,M}
&\mathscr R_{L,M}&2^{e_L(k+d)}\\
\mathscr R_{K_\mu,M+1}^{\sigma_\mu}
 \longrightarrow\mathscr R_{K_\mu,M}^{\sigma_\mu}
&\mathscr R_{F,M}&2^{2k}\\
\mathscr C_{K_\mu,M+1}^{\sigma_\mu}
 \longrightarrow\mathscr C_{K_\mu,M}^{\sigma_\mu}
&\mathscr R_{F,M}&2^{2(k+d)}
\end{array}                                                   \tag{8}
\]
像为空时，自然没有非空纤维。

在任一个固定点集中，下述两种要求都恰好选出子集 \(\mathscr R_{F,M}(A)\)：

- 能提升为一个 \(\sigma_\mu\)-固定的真正解；
- 能成为一条逐层相容的固定矩阵类序列的精度 \(M\) 分量。

在式 (5) 中，对 \(\mathscr R\) 这等价于 \(Y=0\)；对 \(\mathscr C\) 这等价于 \(Y=0\) 且 \(X\in\mathscr R_{F,M}\)。事实上
\[
\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A),\qquad
\varprojlim_M\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
=\varprojlim_M\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
=\mathscr S_F(A).                                             \tag{9}
\]

第 3 问的答案为
\[
\boxed{
N_{\max}=
\begin{cases}
M,&n_1=\cdots=n_r=1,\\
M-1,&\text{至少有一个 }n_i\ge2.
\end{cases}}                                                  \tag{10}
\]
对题设中给定的 \(A,U\)，写唯一的逐条目分解
\[
U=P+\varpi_\mu Q,\qquad P,Q\in M_d(\mathbb Z_2).
\]
则
\[
\boxed{\quad
\text{能取 }N=M
\iff Q\in2^M M_d(\mathbb Z_2)
\iff U\bmod2^M\mathcal O_\mu
      \text{ 是基域矩阵类}.
\quad}                                                       \tag{11}
\]
固定假设本身等价于 \(Q\in2^{M-1}M_d(\mathbb Z_2)\)。

下面证明所有断言。

先从 \(A_i\) 构造正交分块。对每个 \(i\)，从 \(A_i\) 出发迭代
\[
T\longmapsto3T^2-2T^3.
\]
因为 \(A_i^2-A_i\equiv0\pmod2\)，每次迭代把幂等误差的整除精度至少加倍，故收敛到对称幂等矩阵 \(P_i\)，满足
\[
P_i\equiv E_i\pmod2.
\]
所有 \(P_i\) 彼此交换，并与所有 \(A_j\) 交换。若 \(i\ne j\)，则 \(P_iP_j\) 是模 \(2\) 为零的幂等矩阵，因而为零；同理
\[
P_iP_j=0\quad(i\ne j),\qquad \sum_iP_i=I_d.                    \tag{12}
\]
这里用到的简单事实是：若幂等矩阵属于 \(2M_d(\mathbb Z_2)\)，反复取平方便知它属于任意 \(2^mM_d(\mathbb Z_2)\)。

令 \(V_i=\operatorname{im}P_i\)。坐标投影 \(V_i\to\mathbb Z_2^{I_i}\) 是同构，故可选唯一图基矩阵 \(B_i\)，使其 \(I_i\) 行块为单位矩阵。于是
\[
B=(B_1,\ldots,B_r)\equiv I_d\pmod2,\qquad
B^{\mathsf T}B=\operatorname{diag}(G_1,\ldots,G_r),
\]
且若
\[
Z_i=\frac12B_i[I_i^c,:],
\]
则
\[
G_i=I_{n_i}+4Z_i^{\mathsf T}Z_i.                              \tag{13}
\]

真正解和有限层解都必须沿这些 \(V_i\) 分块。具体地，在所考虑的整数环或其模 \(2^m\) 商环中，对满足 \(U\equiv I\pmod2\)、\(U^{\mathsf T}U=I\) 的 \(U\)，有
\[
[U^{\mathsf T}A_iU,E_j]=0\quad(\forall i,j)
\iff
P_iU=UE_i\quad(\forall i).                                   \tag{14}
\]
证明正向时，将幂等提升迭代施于 \(U^{-1}A_iU\)。它是块对角矩阵，其第 \(j\) 块模 \(2\) 为 \(\delta_{ij}I\)；相应幂等矩阵必为 \(\delta_{ij}I\)。反向由 \(A_i\) 与所有 \(P_j\) 交换立即得到。

因此，分块条件等价于
\[
U=B\operatorname{diag}(T_1,\ldots,T_r),\qquad T_i\equiv I\pmod2,
\]
而正交条件等价于
\[
T_i^{\mathsf T}G_iT_i=I_{n_i}.                                \tag{15}
\]
这些等价关系也全部适用于有限层。

需要一个保精度的提升事实。设 \(\mathcal O\) 为本题三个整数环之一，\(m\ge2\)，且对称矩阵 \(H\) 满足
\[
H\equiv I\pmod{2^m},\qquad H_{aa}\equiv1\pmod{2^{m+1}}.
\]
则存在 \(T\equiv I\pmod{2^m}\)，使
\[
T^{\mathsf T}HT=I.                                           \tag{16}
\]
确实，按顺序作 Gram–Schmidt 正交化，所有消元系数都属于 \(2^m\mathcal O\)，范数变化属于 \(2^{2m}\mathcal O\)。所得正交基的范数均在 \(1+2^{m+1}\mathcal O\) 中。每个这样的单位都有唯一的平方根属于 \(1+2^m\mathcal O\)：写平方根为 \(1+2^mx\)，只需解
\[
x+2^{m-1}x^2=a,
\]
而 \(x\mapsto a-2^{m-1}x^2\) 在完备环 \(\mathcal O\) 上为严格压缩映射。缩放各基向量即得 (16)。

由此可证明 (4)。首先，将提升 \(V\) 改为 \(V+2^MZ\)，第 \(a\) 列范数的变化为
\[
2^{M+1}\langle v_a,z_a\rangle+
2^{2M}\langle z_a,z_a\rangle,
\]
故模 \(2^{M+1}\) 不变，必要性也显然。反过来，由 (14) 选取形如 \(B\operatorname{diag}(T_i)\) 的提升。其 Gram 矩阵已经块对角；每块满足 (16) 的假设，故可在不改变模 \(2^M\) 类的前提下变为真正解。

现在验证有限可行性判准。写 \(A_i=E_i+2D_i\)。第一次幂等提升给出
\[
P_i\equiv E_i+2(E_iD_i+D_iE_i)\pmod4.
\]
因此，图基的非本块部分满足
\[
Z_i\equiv D_i[I_i^c,I_i]\pmod2.
\]
若记
\[
\gamma_{ia}=(Z_i^{\mathsf T}Z_i)_{aa}\pmod2
\quad(a\in I_i),
\]
便有
\[
\sum_{a\in I_i}\gamma_{ia}=\delta_i.                           \tag{17}
\]

考虑一块 \(G=I+4H\)，其中 \(H\) 在 \(\mathbb Z_2\) 上。令 \(T=I+2X\)。由 (16)，存在所需真正等距变换，当且仅当可选 \(X\bmod2\)，使
\[
X^{\mathsf T}=X,\qquad
H_{aa}+X_{aa}+\sum_bX_{ba}^2=0
\quad\text{于 }\mathcal O/2\mathcal O.                         \tag{18}
\]
第一条使 \(T^{\mathsf T}GT\equiv I\pmod4\)，第二条正是对角范数模 \(8\) 的条件。

在基域上，(18) 化为
\[
H_{aa}+\sum_{b\ne a}X_{ab}=0\pmod2.                           \tag{19}
\]
对称零对角矩阵的行和向量恰为总和为零的向量。因此可解当且仅当
\[
\sum_aH_{aa}=0\pmod2.
\]
这是完全显式的：若秩为 \(n\ge2\)，令
\[
X_{a,n}=X_{n,a}=H_{aa}\pmod2\quad(a<n),
\]
其余非对角位置取零，对角取零；总和条件保证最后一行也正确。秩为 \(1\) 时直接取 \(X=0\)。

在两个扩张上，
\[
\mathcal O_\mu/2\mathcal O_\mu
 \simeq\mathbb F_2[\bar\varpi_\mu]/(\bar\varpi_\mu^2).
\]
写 \(X=A+\bar\varpi_\mu B\)，则 (18) 化为
\[
H_{aa}+\sum_{b\ne a}A_{ab}+\bar\varpi_\mu B_{aa}=0.
\]
其常数项仍强制同一个总和条件。结合 (17)，便证明了 (2)，并给出了先求模 \(4\) 近似、再应用 (16) 的实际构造。

接下来计数。可行时固定 \(W\in\mathscr S_F(A)\)。由 (14)，所有真正解唯一写成
\[
W\operatorname{diag}(V_1,\ldots,V_r),\qquad
V_i^{\mathsf T}V_i=I,\quad V_i\equiv I\pmod2.                  \tag{20}
\]
有限层也相应归结为各块正交群。即使不可行，在精度 \(2\) 仍可用 \(B\bmod4\) 作同样归结，因为 \(G_i\equiv I\pmod4\)。

对秩 \(n\) 的单块，记 \(k_n=\binom n2\)、\(e=e_L\)。模 \(4\) 时写
\[
V=I+2X.
\]
有限层正交条件恰为 \(X\) 在 \(\mathcal O_L/2\) 上对称，故候选数为
\[
2^{e(k_n+n)}.                                                \tag{21}
\]
真正解的约化还须满足 (18) 中 \(H=0\) 的条件。在基域上，非对角部分的行和为零，约束秩为 \(n-1\)，对角部分自由，所以数目为
\[
2^{n+k_n-(n-1)}=2^{k_n+1}.
\]
扩域上写 \(X=A+\bar\varpi B\)，则 \(A\) 有同样条件，\(B\) 的对角为零、非对角自由，数目为
\[
2^{2k_n+1}.
\]
统一为
\[
2^{e k_n+1}.                                                 \tag{22}
\]

从精度 \(M+1\) 到 \(M\)，约化到单位矩阵的类写成
\[
I+2^MX,\qquad X\in M_n(\mathcal O_L/2).
\]
有限层正交只要求 \(X\) 对称，故核大小为 \(2^{e(k_n+n)}\)。真正解约化的额外范数条件为
\[
X_{aa}=0,
\]
故其核大小为 \(2^{e k_n}\)。

另外，\(\mathscr C_{L,M+1}\) 的约化像恰为 \(\mathscr R_{L,M}\)：源中的正交条件已经给出目标的额外一位对角范数条件，反向则由真正解直接提升。于是 (21)、(22) 和这些核大小给出 (3)，也证明 (8) 的前两行，包括不可行情形。

现在证明固定点公式。任意 \(\mathcal O_\mu/2^M\) 中的元素写成 \(a+b\varpi_\mu\) 后，固定条件为
\[
2b\theta_\mu\in2^M\mathcal O_\mu
\iff b\in2^{M-1}\mathbb Z_2.
\]
因此任意固定矩阵类唯一写为
\[
V=X+tY,\qquad t=2^{M-1}\varpi_\mu,
\]
其中 \(X\) 为基域矩阵类，\(Y\in M_d(\mathbb F_2)\)。注意对所有 \(M\ge2\)，
\[
t^2\in2^{2M-1}\mathcal O_\mu
   \subseteq2^{M+1}\mathcal O_\mu.                            \tag{23}
\]

将 \(V=X+tY\) 代入正交及分块条件。由常数部分得到
\(X\in\mathscr C_{F,M}(A)\)。由 \(\varpi_\mu\) 部分，并使用
\(X\equiv I\pmod2\)、\(A_i\equiv E_i\pmod2\)，得到
\[
Y^{\mathsf T}=Y,\qquad [Y,E_i]=0.
\]
反向展开也立即成立，所以得到 (5) 的 \(\mathscr C\) 公式。

对第 \(a\) 列范数，利用 (23)，额外一位条件为
\[
\frac{(X^{\mathsf T}X)_{aa}-1}{2^M}
  +\varpi_\mu Y_{aa}=0
\quad\text{于 }\mathcal O_\mu/2\mathcal O_\mu.
\]
由于 \(1,\bar\varpi_\mu\) 在 \(\mathbb F_2\) 上线性无关，这等价于
\[
X\in\mathscr R_{F,M}(A),\qquad Y_{aa}=0.
\]
从而得到 (5) 的 \(\mathscr R\) 公式。唯一性同时证明 (6)。固定点数由维数得到，轨道数由
\[
\#\text{轨道}=\frac{\#\text{元素}+\#\text{固定点}}2
\]
得到，故 (7) 成立。

固定点在精度 \(M+1\) 的表示为
\[
X+2^M\varpi_\mu Y,
\]
约化后是基域矩阵类。对 \(\mathscr R\)，它属于 \(\mathscr R_{F,M}\)；对 \(\mathscr C\)，由已证明的约化像结论，它仍属于 \(\mathscr R_{F,M}\)。反向每个基域真正解都提供固定提升。

而且，一个扩域矩阵类若约化到某个 \(W\in\mathscr S_F(A)\) 的模 \(2^M\) 类，它在精度 \(M+1\) 可写成
\[
W+2^MZ.
\]
因为 \(\sigma_\mu(Z)-Z\in2M_d(\mathcal O_\mu)\)，这样的类自动固定。因此这些固定纤维就是完整扩域纤维，得到 (8) 后两行。

真正固定解逐条目属于 \(\mathbb Z_2\)，所以正是 \(\mathscr S_F(A)\)。相容固定序列取完备极限后也是基域真正解；反向基域真正解给出相容序列。这证明 (9) 及其关于精度 \(M\) 分量的刻画。

对下降问题，给定 \(U\) 的模 \(2^M\) 类属于固定的 \(\mathscr R\)，故由 (5) 唯一写成
\[
U\bmod2^M=X+2^{M-1}\varpi_\mu Y,\qquad
X\in\mathscr R_{F,M}(A),\quad Y\in\operatorname{Alt}_{\mathbf n}.
\]
选 \(W\in\mathscr S_F(A)\) 提升 \(X\)，便有
\[
U\equiv W\pmod{2^{M-1}\mathcal O_\mu}.
\]
同精度下降当且仅当 \(Y=0\)，也即 (11)。

若每块秩均为 \(1\)，则 \(\operatorname{Alt}_{\mathbf n}=0\)。更强地，由 (20)，每块真正正交群只有 \(\{\pm1\}\)，故
\[
\mathscr S_{K_\mu}(A)=\mathscr S_F(A).
\]
这证明 (10) 中允许精确下降的情形。

只要有一块秩至少为 \(2\)，下面给出对两种扩张和所有 \(M\ge2\) 统一有效的最优性例子。取 \(A_i=E_i\)，在该块内选两个坐标，令
\[
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
a_M=2^{M-2}\varpi_\mu,
\]
并在这两个坐标上取
\[
T_M=(I+a_MJ)(I-a_MJ)^{-1}
=\frac1{1+a_M^2}
 \begin{pmatrix}1-a_M^2&2a_M\\-2a_M&1-a_M^2\end{pmatrix}.        \tag{24}
\]
其余坐标取单位矩阵。分母为单位，\(T_M\) 真正正交，且
\[
T_M\equiv I_2+2^{M-1}\varpi_\mu J
       \pmod{2^M\mathcal O_\mu}.                              \tag{25}
\]
所以它属于 \(\mathscr S_{K_\mu}(A)\)，其模 \(2^M\) 类固定，却不是基域矩阵类，无法同精度下降。这证明 \(M-1\) 的最优性。它也给出不能提升为固定真正解、不能成为相容固定序列分量的固定 \(\mathscr R\) 类。将参数改为 \(M-1\)，还得到精度 \(M\ge3\) 下的非固定真正解约化：其非对角位置的 \(\varpi_\mu\) 系数赋值恰为 \(M-2\)。

最后列出其余否定现象的实际例子。

若 \(r\ge2\)，选两个不同块中的坐标，在其二维子空间上取
\[
A_1=\begin{pmatrix}1&2\\2&0\end{pmatrix},\qquad
A_2=I_2-A_1,
\]
其余坐标按原投影补齐，其余 \(A_i\) 取相应标准投影。这是合法输入，且
\(\delta_1=\delta_2=1\)，故三个域上均无真正解。不过
\[
\bar U=\begin{pmatrix}1&2\\2&1\end{pmatrix}\pmod4
\]
补上其他单位坐标后属于 \(\mathscr C_{L,2}(A)\)；其列范数为 \(5\)，不能提升为真正解。

对任意块秩、任意 \(M\ge2\)，取 \(A_i=E_i\)，任选坐标 \(a\)，则
\[
D_M=I_d+2^{M-1}\varpi_\mu e_{aa}\pmod{2^M}
\]
属于 \(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\)，但
\[
(D_M^{\mathsf T}D_M)_{aa}-1
\equiv2^M\varpi_\mu\not\equiv0\pmod{2^{M+1}},
\]
故不属于 \(\mathscr R\)，不能提升为真正解，也不能进入相容固定序列。

基域上，对所有 \(M\ge3\)，
\[
I_d+2^{M-1}e_{aa}\pmod{2^M}
\]
同样属于 \(\mathscr C_{F,M}(E)\setminus\mathscr R_{F,M}(E)\)。精度 \(2\) 时，只要一块秩至少为 \(2\)，在该块取
\[
I_2+2\begin{pmatrix}0&1\\1&0\end{pmatrix}\pmod4
\]
也有同样性质，因为列范数为 \(5\)。这些构造分别实现了表 (8) 中相应约化映射不能覆盖整个目标集合的情形。