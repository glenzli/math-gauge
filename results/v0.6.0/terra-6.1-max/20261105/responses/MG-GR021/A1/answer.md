记
\[
Q=\sum_{i=1}^r\binom{n_i}{2},\qquad P=Q+d,
\qquad
s_L=\begin{cases}1,&L=F,\\2,&L=K_{-1}\text{ 或 }K_2.\end{cases}
\]
对每个 \(i\)，在 \(\mathbb F_2\) 中定义
\[
\kappa_i=
\sum_{\substack{a\in I_i\\ b\notin I_i}}
\frac{(A_i)_{ab}}2\pmod2,
\]
并令
\[
\eta=\begin{cases}1,&\kappa_i=0\quad(\forall i),\\
0,&\text{否则}.
\end{cases}                                                    \tag{1}
\]
这里除以 \(2\) 是有定义的，因为所用条目都是偶数。故 \(\eta\) 只依赖于 \(A_i\bmod4\)。

下面先给出解与计数，再给出固定点、约化和下降结论；证明随各部分给出。

## 一、可行性、精确基数与真正解的约化

对三个域同时有
\[
\boxed{\quad
\mathscr S_L(A)\ne\varnothing\iff \eta=1.
\quad}                                                        \tag{2}
\]
而且，只要任一扩域上有解，就有基域解。

对每个 \(M\ge2\)，精确基数为
\[
\boxed{\quad
|\mathscr R_{L,M}(A)|
=\eta\,2^{\,s_LQ(M-1)+r}.
\quad}                                                        \tag{3}
\]
以及
\[
\boxed{\quad
|\mathscr C_{L,2}(A)|=2^{s_LP},\qquad
|\mathscr C_{L,M}(A)|
=\eta\,2^{\,s_LQ(M-1)+r+s_Ld}\quad(M\ge3).
\quad}                                                        \tag{4}
\]
因此，\(\mathscr R_{L,M}\) 恰在 \(\eta=0\) 时为空；\(\mathscr C_{L,2}\) 总非空，而 \(M\ge3\) 时 \(\mathscr C_{L,M}\) 恰在 \(\eta=0\) 时为空。

对给定 \(\bar U\in\mathscr C_{L,M}(A)\)，任选其条目提升
\(\widetilde U\in M_d(\mathcal O_L)\)。其属于 \(\mathscr R_{L,M}(A)\) 的必要充分条件是
\[
\boxed{\quad
\eta=1,\qquad
(\widetilde U^{\mathsf T}\widetilde U)_{jj}
\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le j\le d).
\quad}                                                        \tag{5}
\]
这些对角同余与所选提升无关：改变提升 \(2^M Z\) 使对角范数的变化属于 \(2^{M+1}\mathcal O_L\)。

### 证明：同时正交分解与判准

在由所有 \(A_i\) 生成的交换的、\(2\)-进完备矩阵代数中，反复应用多项式
\[
x\longmapsto 3x^2-2x^3
\]
可把 \(A_i\bmod2=E_i\) 唯一提升为幂等元 \(P_i\)。这个迭代在每一有限精度处都是有限次多项式计算。所得矩阵满足
\[
P_i^{\mathsf T}=P_i,\quad P_i\equiv E_i\pmod2,\quad
P_iP_j=0\ (i\ne j),\quad \sum_iP_i=I.
\]
例如，\(P_iP_j\) 是属于 \(2M_d(\mathbb Z_2)\) 的幂等元，故它为零。每个 \(P_i\) 也与所有 \(A_j\) 交换。

对真正解和有限精度候选解，原来的分块条件等价于
\[
P_iU=UE_i\qquad(\forall i),                                  \tag{6}
\]
有限精度时取相应模数。事实上，正交性给出 \(U^{-1}=U^{\mathsf T}\)。若所有 \(U^{-1}A_iU\) 分块，则所有 \(U^{-1}P_iU\) 也分块；后者是模 \(2\) 等于 \(E_i\) 的幂等元，因此恰为 \(E_i\)。反向则由 \([A_j,P_i]=0\) 得到。

令 \(B_i\) 由 \(P_i\) 的第 \(I_i\) 列组成，置 \(B=[B_1\ \cdots\ B_r]\)。则
\[
B\equiv I\pmod2,\qquad
B^{\mathsf T}B=\operatorname{diag}(G_1,\ldots,G_r),\qquad
G_i=(P_i)_{I_i,I_i}.
\]
幂等关系给出 \(G_i\equiv I\pmod4\)。进一步，
\[
\det G_i\equiv1+4\kappa_i\pmod8.                             \tag{7}
\]
为验证此式，注意 \(P_i\) 的 \(I_i\times I_i^c\) 子块模 \(4\) 等于 \(A_i\) 的对应子块；这可由 \([P_i,A_i]=0\) 和两者模 \(2\) 的形式直接算出。若该子块为 \(2X\)，而 \(G_i=I+4C\)，则 \(P_i^2=P_i\) 蕴含
\(C\equiv-XX^{\mathsf T}\pmod2\)，从而得到 (7)。

当 \(\det G_i\equiv1\pmod8\) 时，存在
\(V_i\equiv I\pmod2\) 使 \(V_i^{\mathsf T}G_iV_i=I\)。具体地，写
\(G_i=I+4C\)。先选一个对称的零对角 \(0,1\) 矩阵 \(X\)，使其各行和模 \(2\) 分别等于 \(C\) 的对角元；这样的 \(X\) 存在，恰因为这些对角元之和为零。以 \(I+2X\) 变换后，对角元均为 \(1\bmod8\)，非对角元均为 \(0\bmod4\)。随后用系数属于 \(4\mathbb Z_2\) 的正交消元将其对角化；对角元仍为 \(1\bmod8\)，因而都是 \(\mathbb Z_2\) 中的平方。缩放这些对角元即得所需 \(V_i\)。

反之，即使只要求模 \(8\) 的扩域解，\(\det G_i\equiv5\bmod8\) 也不可能。确切地说，若
\(x=a+b\theta_\mu\equiv1\pmod{2\mathcal O_\mu}\) 且 \(x^2\) 模 \(8\) 为有理数，则 \(a\) 为奇数、\(b\) 为偶数；由 \(\theta_\mu\) 系数 \(2ab\equiv0\bmod8\) 得 \(b\equiv0\bmod4\)，于是 \(x^2\equiv1\bmod8\)，不可能为 \(5\bmod8\)。基域情形同样成立。

这证明了 (2)，也证明 \(\eta=0\) 时 \(\mathscr C_{L,M}=\varnothing\)（\(M\ge3\)）。当 \(\eta=1\) 时，上述构造给出一个
\(T\in\mathscr S_F(A)\)，并且
\[
\mathscr S_L(A)
=T\prod_{i=1}^r
\{V\in\operatorname{GL}_{n_i}(\mathcal O_L):
 V\equiv I\pmod2,\ V^{\mathsf T}V=I\},                       \tag{8}
\]
其中积理解为分块对角矩阵。若 \(\eta=0\)，\(B\bmod4\) 仍给出模 \(4\) 的正交分块标架；所以模 \(4\) 候选集总非空。

### 证明：有限计数与判据 (5)

对单块秩 \(n\)，写 \(q=\binom n2\)、\(U=I+2Y\)。正交方程等价于
\[
\begin{aligned}
g_{ij}(Y)&=Y_{ij}+Y_{ji}
            +2\sum_kY_{ki}Y_{kj}=0 &&(i<j),\\
f_i(Y)&=Y_{ii}+\sum_kY_{ki}^2=0. &&
\end{aligned}                                                \tag{9}
\]
在模 \(2^M\) 的候选集中，\(g_{ij}\) 要模 \(2^{M-1}\) 为零，而 \(f_i\) 只须模 \(2^{M-2}\) 为零。

对 \(F\)，\(\mathcal O_F/2=\mathbb F_2\)；对两个扩域，
\[
\mathcal O_\mu/2\mathcal O_\mu\simeq
\mathbb F_2[t]/(t^2).
\]
例如可分别取 \(t=1+\theta_{-1}\) 和 \(t=\theta_2\)。记到剩余域 \(\mathbb F_2\) 的映射为 \(\rho\)。方程 (9) 模 \(2\) 的条件是：

* \(Y_{ij}=Y_{ji}\)；
* 每个对角元 \(Y_{ii}\) 是 \(0\) 或 \(1\)；
* 每个顶点 \(i\) 满足 \(\sum_{j\ne i}\rho(Y_{ij})=0\)。

最后一组是完全图边变量的偶度条件，秩为 \(n-1\)。把下三角条目作为自由参数时，方程 (9) 对上三角及对角未知量的 Jacobian 模 \(2\) 为单位矩阵。因此，完备环上的 Hensel 提升表明：任何满足上述模 \(2\) 条件的选择，按精度唯一提升未知的上三角及对角条目。

于是单块真正解在模 \(2^M\) 的像有
\[
2^{\,s_Lq(M-1)+1}
\]
个。模 \(4\) 候选集只要求 \(Y\bmod2\) 对称，故有
\(2^{s_L(q+n)}\) 个；当 \(M\ge3\) 时，相对真正解像，每个对角未知量还多一个 \(\mathcal O_L/2\) 的自由层，故候选数为
\[
2^{\,s_Lq(M-1)+1+s_Ln}.
\]
对各块相乘即得 (3)、(4)。同一个 Hensel 提升论证也说明：候选类能提升为真正解，当且仅当 (9) 的 \(f_i\) 在多一层精度上为零；这正是 (5)。结合 \(\eta=1\) 得到所述全局判据。

## 二、Galois 固定类、轨道及逐层约化

以下固定一个 \(\mu\)，写
\[
\theta=\theta_\mu,\qquad \sigma=\sigma_\mu,\qquad
\epsilon_M=2^{M-1}\theta\pmod{2^M\mathcal O_\mu}.
\]
令
\[
\begin{aligned}
\operatorname{Sym}_{\rm bl}
 &=\{D\in M_d(\mathbb F_2):D\text{ 分块对角且 }D^{\mathsf T}=D\},\\
\operatorname{Alt}_{\rm bl}
 &=\{D\in\operatorname{Sym}_{\rm bl}:D_{jj}=0\quad\forall j\}.
\end{aligned}
\]
它们的 \(\mathbb F_2\)-维数分别为 \(P\) 和 \(Q\)。下式中的 \(D\) 可任取 \(0,1\) 整数提升；结果不依赖提升，因为 \(2\epsilon_M=0\)。

### 固定矩阵类的具体形式

对所有输入和 \(M\ge2\)，有不相交的唯一表示
\[
\boxed{\quad
\mathscr C_{K_\mu,M}(A)^\sigma
=
\mathscr C_{F,M}(A)+\epsilon_M\operatorname{Sym}_{\rm bl}.
\quad}                                                        \tag{10}
\]

若 \(\eta=0\)，所有 \(\mathscr R\) 都为空。以下假设 \(\eta=1\)。对 \(M\ge3\)，以及对 \((\mu,M)=(2,2)\)，有
\[
\boxed{\quad
\mathscr R_{K_\mu,M}(A)^\sigma
=
\mathscr R_{F,M}(A)+\epsilon_M\operatorname{Alt}_{\rm bl}.
\quad}                                                        \tag{11}
\]
唯一需要单独写出的情形是 \((\mu,M)=(-1,2)\)。对
\(U_0\in\mathscr C_{F,2}(A)\)，定义
\[
o_j(U_0)=
\frac{(\widetilde U_0^{\mathsf T}\widetilde U_0)_{jj}-1}{4}
\pmod2,
\]
其中 \(\widetilde U_0\) 是任意整数矩阵提升。则
\[
\boxed{\quad
\mathscr R_{K_{-1},2}(A)^\sigma
=
\left\{U_0+2\theta_{-1}D:
\begin{array}{l}
U_0\in\mathscr C_{F,2}(A),\
D\in\operatorname{Alt}_{\rm bl},\\[2pt]
o_j(U_0)=\displaystyle\sum_kD_{kj}\quad(\forall j)
\end{array}\right\}.
\quad}                                                        \tag{12}
\]
和在 \(\mathbb F_2\) 中计算。

特别地，所有模 \(4\) 候选类及真正解的模 \(4\) 类都由 \(\sigma\) 固定。并且，对于每个精度，
\[
\mathscr C_{K_\mu,M}\cap M_d(\mathbb Z_2/2^M)=\mathscr C_{F,M},
\qquad
\mathscr R_{K_\mu,M}\cap M_d(\mathbb Z_2/2^M)=\mathscr R_{F,M}.
                                                                    \tag{13}
\]

这些公式也给出固定点数：
\[
\boxed{\quad
|\mathscr R_{K_\mu,M}(A)^\sigma|
=2^Q|\mathscr R_{F,M}(A)|
=\eta\,2^{QM+r},
\quad}                                                        \tag{14}
\]
\[
\boxed{\quad
|\mathscr C_{K_\mu,M}(A)^\sigma|
=2^P|\mathscr C_{F,M}(A)|
=
\begin{cases}
2^{2P},&M=2,\\
\eta\,2^{QM+r+2d},&M\ge3.
\end{cases}
\quad}                                                        \tag{15}
\]
由两元素群的轨道计数公式，轨道数为
\[
\boxed{\quad
\#\bigl(\mathscr R_{K_\mu,M}(A)/\langle\sigma\rangle\bigr)
=\frac{\eta}{2}
 \left(2^{2Q(M-1)+r}+2^{QM+r}\right),
\quad}                                                        \tag{16}
\]
以及
\[
\boxed{\quad
\#\bigl(\mathscr C_{K_\mu,M}(A)/\langle\sigma\rangle\bigr)
=
\begin{cases}
2^{2P},&M=2,\\[2pt]
\displaystyle\frac{\eta}{2}
\left(2^{2Q(M-1)+r+2d}+2^{QM+r+2d}\right),&M\ge3.
\end{cases}
\quad}                                                        \tag{17}
\]

**证明。** 在 \(\mathcal O_\mu/2^M\) 中，\(\sigma\)-固定元唯一写成
\[
a+\epsilon_M b,\qquad a\in\mathbb Z_2/2^M,\quad b\in\mathbb F_2,
\]
且 \(\epsilon_M^2=0\)。将此写法逐条目代入 (6) 及正交方程：由于 \(P_i\bmod2=E_i\)、\(U\bmod2=I\)，\(\epsilon_M\) 的系数必须分块对角且对称，这证明 (10)。

再用 (5) 检查列范数。对于 \(U=U_0+\epsilon_MD\)，模 \(2^{M+1}\) 有
\[
(U^{\mathsf T}U)_{jj}
=(U_0^{\mathsf T}U_0)_{jj}
+2^M\theta\,(U_0^{\mathsf T}D)_{jj}
+2^{2M-2}\mu\sum_kD_{kj}^2.
\]
当 \(M\ge3\) 时最后一项消失；其余两项给出 \(D_{jj}=0\) 和 \(U_0\in\mathscr R_{F,M}\)，即 (11)。当 \(M=2\) 时，最后一项可能贡献 \(4\mu\sum_kD_{kj}\)，于是分别得到 (11) 的 \(\mu=2\) 情形和 (12)。模 \(4\) 的所有类固定，是因为 \(U\equiv I\bmod2\) 蕴含 \(\sigma(U)-U\equiv0\bmod4\)。计数和轨道公式随之得到。

### 从 \(M+1\) 到 \(M\) 的像与纤维

下面表中的最后一列是**每个非空纤维**的大小；当 \(\eta=0\) 时所有这些约化映射的像均为空，因此没有非空纤维。

\[
\begin{array}{c|c|c}
\text{约化映射}&\text{像}&\text{每个非空纤维的大小}\\ \hline
\mathscr R_{L,M+1}\to\mathscr R_{L,M}
 &\mathscr R_{L,M}&2^{s_LQ}\\
\mathscr C_{L,M+1}\to\mathscr C_{L,M}
 &\mathscr R_{L,M}&2^{s_LP}\\
\mathscr R_{K_\mu,M+1}^{\sigma}\to
  \mathscr R_{K_\mu,M}^{\sigma}
 &\mathscr R_{F,M}&2^{2Q}\\
\mathscr C_{K_\mu,M+1}^{\sigma}\to
  \mathscr C_{K_\mu,M}^{\sigma}
 &\mathscr R_{F,M}&2^{2P}
\end{array}                                                   \tag{18}
\]
这里基域集合按题意嵌入相应扩域集合。

前两行由 (5) 得到：精度 \(M+1\) 的候选类约化后满足精度 \(M\) 的真正提升判据；反之，真正解显然提供提升。后两行中，固定类的非有理部分在约化时消失，再用前两行的基域版本即可。用 (3)、(4)、(14)、(15) 取基数之比，或用所述群陪集结构，得到全部纤维大小。

固定类中，以下三个条件等价：

1. 它是某个 \(\sigma\)-固定真正解的模 \(2^M\) 类；
2. 它能作为一条逐层相容的固定类序列在精度 \(M\) 的分量；
3. 它属于嵌入的 \(\mathscr R_{F,M}(A)\)。

这里无论固定类最初属于 \(\mathscr R\) 还是 \(\mathscr C\)，结论相同。事实上，\(\sigma\)-固定真正解恰是 \(\mathscr S_F(A)\)，而表 (18) 已说明即使只向上提升一个固定层，像也恰为 \(\mathscr R_{F,M}(A)\)。

## 三、下降的最优精度

满足题目第三问的最大整数为
\[
\boxed{\quad
N_{\max}=
\begin{cases}
M,&Q=0\quad(\text{即所有 }n_i=1),\\
M-1,&Q>0.
\end{cases}
\quad}                                                        \tag{19}
\]

对给定的 \(A,U\)，唯一写
\[
U=a+\theta_\mu b,\qquad a,b\in M_d(\mathbb Z_2).
\]
题设的近似固定条件等价于
\[
b\in2^{M-1}M_d(\mathbb Z_2).                                \tag{20}
\]
对于这个给定的 \(U\)，能取 \(N=M\) 的必要充分条件是
\[
\boxed{\quad b\in2^MM_d(\mathbb Z_2).\quad}                  \tag{21}
\]
实际精确下降 \(U\in\mathscr S_F(A)\) 则等价于 \(b=0\)。

若所有 \(n_i=1\)，有更强结论：
\[
\boxed{\quad
\mathscr S_{K_\mu}(A)=\mathscr S_F(A)
\quad\text{作为矩阵集合}.
\quad}                                                        \tag{22}
\]
若有某个 \(n_i\ge2\)，则即使要求任意预定的有限精度近似固定，也不能保证精确下降。

### 证明及统一最优性构造

若给定的 \(U\) 存在，则 \(\eta=1\)，所以存在基域真正解。由正交性和 (6)，
\[
a^{\mathsf T}a+\mu b^{\mathsf T}b=I,\qquad
P_i a=aE_i.
\]
当 \(M\ge3\) 时，由 (20) 可知 \(a\bmod2^{M-1}\) 是基域候选类，而且其列范数模 \(2^M\) 为 \(1\)。由 (5)，它属于
\(\mathscr R_{F,M-1}(A)\)。当 \(M=2\) 时，任意基域真正解都与 \(U\) 模 \(2\) 同余。因此总可下降到精度 \(M-1\)。

若 \(b\) 可被 \(2^M\) 整除，同样的论证和 (5) 给出
\(a\bmod2^M\in\mathscr R_{F,M}(A)\)。反过来，若 \(U\) 模 \(2^M\) 同余于有理矩阵，则按 \(\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu\) 的唯一分解，\(b\) 必可被 \(2^M\) 整除。这证明 (21)。

若 \(Q=0\)，由 (8) 和域中的恒等式 \(v^2=1\Rightarrow v=\pm1\)，得到 (22)。

现在设 \(Q>0\)，在某块内选两个坐标，并取 \(A_i=E_i\)。对每个 \(M\ge2\)，统一定义
\[
\pi_\mu=\begin{cases}1+\theta_{-1},&\mu=-1,\\
\theta_2,&\mu=2,\end{cases}
\qquad
\lambda_\mu=\pi_\mu^2/2=
\begin{cases}\theta_{-1},&\mu=-1,\\1,&\mu=2.\end{cases}
\]
令
\[
b_M=2^{M-1}\pi_\mu.
\]
由 Hensel 引理，方程
\[
x+x^2=-2^{2M-3}\lambda_\mu
\]
有唯一满足 \(x\equiv0\bmod2\) 的解；令 \(a_M=1+2x\)。于是
\[
a_M^2+b_M^2=1,\qquad
a_M\equiv1\pmod{2^{2M-2}}.
\]
在所选两个坐标上放置
\[
\begin{pmatrix}a_M&-b_M\\ b_M&a_M\end{pmatrix},
\]
其余坐标放恒等矩阵，得到 \(U_M\in\mathscr S_{K_\mu}(A)\)。它满足
\[
\sigma(U_M)\equiv U_M\pmod{2^M},
\]
但 \(b_M\) 的 \(\theta_\mu\)-系数恰为 \(2^{M-1}\)，所以它不可能模 \(2^M\) 同余于任何基域矩阵。这对每个 \(M\) 都给出实际反例，证明 (19) 的最优性，也证明有非平凡块时不能保证精确下降。

## 四、其他否定情形的具体例子

* **合法输入可以不可行。** 取 \(r=2,n_1=n_2=1\)，令
  \[
  A_1=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix},
  \qquad
  A_2=\frac15\begin{pmatrix}4&-2\\-2&1\end{pmatrix}.
  \]
  它们是正交互补的对称幂等元，满足全部输入条件，但
  \(\kappa_1=\kappa_2=1\)。因此三个域上均无真正解，且精度 \(M\ge3\) 的候选集为空。不过
  \[
  \frac15\begin{pmatrix}1&-2\\2&1\end{pmatrix}\pmod4
  \]
  是模 \(4\) 候选类。这也给出模 \(4\) 候选类不能提升的例子。

* **可行输入上，固定候选类也可能没有真正提升。** 取 \(A_i=E_i\)。对任意 \(M\ge2\) 和任一坐标 \(j\)，
  \[
  I+2^{M-1}\theta_\mu E_{jj}\pmod{2^M}
  \]
  属于 \(\mathscr C_{K_\mu,M}^{\sigma}\)，但列范数不满足 (5)，故不属于 \(\mathscr R_{K_\mu,M}\)。对于 \(M\ge3\)，有理类
  \(I+2^{M-1}E_{jj}\) 也给出基域候选类不能提升的例子。若某块秩至少为 \(2\)，则模 \(4\) 的基域例子可取该块中的
  \(\begin{psmallmatrix}1&2\\2&1\end{psmallmatrix}\)。

* **固定真正解类未必来自固定真正解。** 当 \(Q>0\) 时，上述 \(U_M\bmod2^M\) 是固定的真正解类，却不属于 \(\mathscr R_{F,M}\)，所以不能提升为 \(\sigma\)-固定真正解，也不能继续作为固定类提升到下一层。对于 \(M\ge3\)，同一构造中的 \(U_{M-1}\bmod2^M\) 还给出不被 \(\sigma\) 固定的真正解类。特别地，在 \((\mu,M)=(-1,2)\) 时，该构造的有理部分模 \(4\) 为
  \(\begin{psmallmatrix}1&2\\2&1\end{psmallmatrix}\)，它不是基域真正解类；这具体展示了公式 (12) 中的扭曲项不可省去。