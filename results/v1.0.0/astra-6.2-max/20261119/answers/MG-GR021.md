## 1. 可行性、基数与提升判据

对每块定义奇偶数
\[
\eta_i=\sum_{p\in I_i}\sum_{b\notin I_i}\frac{(A_i)_{bp}}2\pmod 2,
\qquad
f=\mathbf 1_{\{\eta_i=0\ \text{对所有 }i\}}.
\]
这些非对角块的条目都是偶数，所以 \(A_i\bmod 4\) 就确定了 \(\eta_i\)。记
\[
a=\sum_{i=1}^r\binom{n_i}{2},\qquad s=a+d,\qquad
q_L=|\mathcal O_L/2\mathcal O_L|,
\]
其中 \(q_F=2\)，\(q_{K_{-1}}=q_{K_2}=4\)。以下在集合记号中省略 \(A\)。

**三个域的可行性判准相同**，均为 \(\mathscr S_L\ne\varnothing\iff f=1\)。精确基数为
\[
\boxed{\quad
|\mathscr R_{L,M}|=f\,2^r q_L^{(M-1)a},\qquad
|\mathscr C_{L,M}|=
\begin{cases}
q_L^s,&M=2,\\
f\,2^r q_L^{(M-1)a+d},&M\ge3 .
\end{cases}\quad}                                                    \tag{1}
\]
特别地，\(\mathscr C_{L,2}\) 总是非空。从 \(M=3\) 起，两个有限集合都恰在 \(f=0\) 时为空。

给定 \(\bar U\in\mathscr C_{L,M}\)，任取其列的整提升 \(u_1,\ldots,u_d\)。则
\[
\boxed{\quad
\bar U\in\mathscr R_{L,M}
\iff
u_j^{\mathsf T}u_j\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le j\le d).\quad}                                           \tag{2}
\]
更换整提升使平方范数改变 \(2^{M+1}\mathcal O_L\) 中的元素，因此可直接用给定矩阵类核验此判据。

### 共同投影与块上的 Gram 矩阵

令 \(P_i=\lim_{k\to\infty} A_i^{2^k}\)。为说明极限存在，注意每个迭代矩阵 \(X=A_i^{2^k}\) 都模 \(2\) 等于 \(E_i\)，因而 \(X^2+X\equiv0\pmod2\)。由
\[
X^4-X^2=(X^2-X)(X^2+X)
\]
可知第 \(k+1\) 次与第 \(k\) 次迭代之差被 \(2^{k+1}\) 整除。所得 \(P_i\) 对称、幂等、模 \(2\) 等于 \(E_i\)，并与所有 \(A_j,P_j\) 交换。当 \(i\ne j\) 时，\(P_iP_j\) 是模 \(2\) 为零的幂等矩阵，故为零，因为 \(I-P_iP_j\) 可逆。同理 \(\sum_iP_i=I\)。

在整数环及其模 \(2^m\) 商环上，对满足 \(U^{\mathsf T}U=I,\ U\equiv I\pmod2\) 的矩阵，题中的同时分块条件等价于
\[
P_iU=UE_i\qquad(1\le i\le r).                                       \tag{3}
\]
事实上，若 \(U^{-1}A_iU\) 分块，则 \(U^{-1}P_iU\) 也分块。在商环上，取足够高的一次迭代便得到 \(P_i\) 的约化。这个分块幂等矩阵模 \(2\) 为 \(E_i\)，故第 \(i\) 块是恒等矩阵，其余块全为零。反向由各 \(A_j\) 与 \(P_i\) 交换即得。

取列矩阵
\[
B_i=(P_i)_{\bullet,I_i}\bigl((P_i)_{I_i,I_i}\bigr)^{-1},
\qquad B=(B_1\ \cdots\ B_r).
\]
\(B_i\) 在 \(I_i\) 上的行组成恒等矩阵，其余行记为 \(2D_i\)。于是 \(B\equiv I\pmod2\)，且 \(P_iB=BE_i\)。不同 \(B_i\) 的列彼此正交，各块的 Gram 矩阵为
\[
G_i=B_i^{\mathsf T}B_i=I+4H_i,\qquad H_i=D_i^{\mathsf T}D_i.
\]
由于 \(A_iB_i=B_iT_i\) 且 \(T_i\equiv I\pmod2\)，取这个等式在 \(I_i\) 外的行，模 \(4\) 得
\[
2D_i\equiv(A_i)_{I_i^c,I_i}\pmod4,\qquad
\operatorname{tr}H_i\equiv\eta_i\pmod2.                              \tag{4}
\]
由 (3)，所有待求矩阵都唯一写成 \(U=B(\bigoplus_i V_i)\)。在各自的精度上，剩余条件就是各块独立满足
\[
V_i\equiv I\pmod2,\qquad V_i^{\mathsf T}G_iV_i=I.                   \tag{5}
\]

### 逐层提升

先看秩为 \(n\) 的一块，写 \(G=I+4H\)。设 \(V\) 代表一个模 \(2^m\) 的解，\(m\ge2\)。其下一层提升都写成 \(V+2^mD\)，其中 \(D\) 取模 \(2\)。模 \(2^{m+1}\) 的 Gram 矩阵增量为
\[
2^m(D+D^{\mathsf T})\pmod{2^{m+1}},
\]
因为 \(GV\equiv I\pmod2\)。因此，能提升一层的必要条件是当前每列的 \(G\)-平方范数已模 \(2^{m+1}\) 等于 \(1\)。满足此条件时，每对非对角位置只需指定 \(D_{jk}+D_{kj}\)，故共有 \(q_L^{\binom n2+n}\) 个下一层解。

在这些提升中，还能让每列的 \(G\)-平方范数模 \(2^{m+2}\) 等于 \(1\)。事实上，第 \(j\) 列平方范数的增量模 \(2^{m+2}\) 为
\[
2^{m+1}(V^{\mathsf T}GD)_{jj}\equiv 2^{m+1}D_{jj}\pmod{2^{m+2}},
\]
这里用到了 \(2m\ge m+2\)。故每个 \(D_{jj}\bmod2\) 都被唯一确定，余下 \(q_L^{\binom n2}\) 个选择。反复提升并用 \(\mathcal O_L\) 的 \(2\)-进完备性取极限，即得到真正解。这证明了 (2)，也给出了从任一满足 (2) 的类出发的逐层构造。

### 模 \(4\) 的起始计数

令 \(T=\mathcal O_L/2\mathcal O_L\)。统一写成 \(T=\mathbb F_2\oplus J\)。基域情形 \(J=0\)，两个扩域情形 \(J=\mathbb F_2\epsilon\)，其中 \(\epsilon^2=0\)，分别可取
\[
\epsilon=1+\bar\theta_{-1},\qquad \epsilon=\bar\theta_2 .
\]
因而对 \(u\in\mathbb F_2,\ v\in J\)，有 \((u+v)^2=u\)。

在一块上写 \(V=I+2X\bmod4\)，其中 \(X\) 取值于 \(T\)。模 \(4\) 的 Gram 方程恰为 \(X=X^{\mathsf T}\)。要使此类可提升，按 (2) 还需对每个 \(j\) 满足
\[
H_{jj}+X_{jj}+\sum_k X_{kj}^2=0\quad\text{于 }T.
\]
写 \(X_{kj}=u_{kj}+v_{kj}\)，其中 \(u_{kj}\in\mathbb F_2,\ v_{kj}\in J\)，再记 \(h_j=H_{jj}\bmod2\)。上式等价于
\[
v_{jj}=0,\qquad \sum_{k\ne j}u_{kj}=h_j.                            \tag{6}
\]
每个非对角变量 \(u_{kj}=u_{jk}\) 对右侧向量贡献 \(e_k+e_j\)。这些向量张成坐标和为零的子空间，维数为 \(n-1\)，对 \(n=1\) 也成立。因此 (6) 可解当且仅当 \(\sum_jh_j=0\)。可解时，令 \(b=\binom n2\)，非对角的 \(u\) 有 \(2^{b-(n-1)}\) 种选择，对角的 \(u\) 有 \(2^n\) 种，非对角的 \(v\) 有 \(|J|^b\) 种。乘积为 \(2q_L^b\)。

结合 (4)，各块同时可解恰为 \(f=1\)。将模 \(4\) 的计数与逐层提升数相乘，便得到 (1)。

空集情形可在任意两个不同块上实现。取 \(p\in I_i,\ q\in I_j,\ i\ne j\)，记 \(D_{pq}=e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T}\)，置
\[
A_i=E_i+2D_{pq},\qquad A_j=E_j-2D_{pq},\qquad A_k=E_k\quad(k\ne i,j).
\]
这些矩阵交换，因为 \(A_i+A_j=E_i+E_j\) 在这两个块上是恒等。此时 \(\eta_i=\eta_j=1\)，而 \(I+2D_{pq}\bmod4\) 是一个实际的模 \(4\) 解。

即使取可行输入 \(A_i=E_i\)，有限解也可能无法提升。对任意 \(M\ge3\)，矩阵 \(I+2^{M-1}e_pe_p^{\mathsf T}\) 给出基域上的例子，其第 \(p\) 列平方范数模 \(2^{M+1}\) 为 \(1+2^M\)。在 \(M=2\) 时，若同一块含两个位置 \(p,q\)，则 \(I+2D_{pq}\) 的相应列平方范数为 \(5\)，也无法提升。

## 2. 固定矩阵类、轨道与约化

固定 \(\mu\)，简写 \(K=K_\mu,\ \theta=\theta_\mu,\ \sigma=\sigma_\mu\)。令 \(\mathcal D\) 为 \(\mathbb F_2\) 上按给定块分块对角、每块对称的矩阵空间，令 \(\mathcal D_0\) 为其中对角线全零的子空间。二者维数分别是 \(s,a\)。令
\[
\lambda_{\mu,M}=
\begin{cases}
1+\theta,&\mu=-1,\ M=2,\\
\theta,&\text{其余情形}.
\end{cases}
\]
固定矩阵类在原标准坐标下有如下唯一表示，其中 \(Y\) 的条目可用 \(0,1\) 代表：
\[
\boxed{\begin{aligned}
\mathscr C_{K,M}^{\sigma}
 &=\{X+2^{M-1}\theta Y\mid X\in\mathscr C_{F,M},\ Y\in\mathcal D\},\\
\mathscr R_{K,M}^{\sigma}
 &=\{X+2^{M-1}\lambda_{\mu,M}Y\mid X\in\mathscr R_{F,M},\ Y\in\mathcal D_0\}.
\end{aligned}}                                                       \tag{7}
\]
基域上的相应集合恰为 \(Y=0\) 的部分。因此在非空时，\(\mathscr R_{K,M}^{\sigma}=\mathscr R_{F,M}\) 当且仅当 \(a=0\)，而 \(\mathscr C_{K,M}^{\sigma}\) 总严格包含 \(\mathscr C_{F,M}\)。

为证明 (7)，用整基 \(1,\theta\) 比较系数。模 \(2^M\) 固定的矩阵唯一写成 \(X+2^{M-1}\theta Y\)，其中 \(X\) 是实系数矩阵类，\(Y\) 取值于 \(\mathbb F_2\)。在 (3) 中比较两项，得到 \(P_iX=XE_i\) 以及 \(E_iY=YE_i\)。在模 \(2^M\) 的正交方程中，\(Y\) 的二次项消失，得到 \(X^{\mathsf T}X=I\) 以及 \(Y^{\mathsf T}=Y\)，后者用到了 \(X\equiv I\pmod2\)。这就证明了第一行。

取 \(X,Y\) 对应的第 \(j\) 列整提升 \(x,y\)。扩域列的平方范数为
\[
x^{\mathsf T}x+2^M\theta x^{\mathsf T}y
                  +2^{2M-2}\mu\,y^{\mathsf T}y.                     \tag{8}
\]
要通过 (2)，\(\theta\) 的系数要求 \(x^{\mathsf T}y\equiv0\pmod2\)，即 \(Y_{jj}=0\)。当 \(M\ge3\) 或 \(\mu=2\) 时，最后一项被 \(2^{M+1}\) 整除，于是实部条件恰为 \(X\in\mathscr R_{F,M}\)。

剩下 \(\mu=-1,M=2\)。在 \(Y_{jj}=0\) 时，
\[
x^{\mathsf T}x-4y^{\mathsf T}y
\equiv (x+2y)^{\mathsf T}(x+2y)\pmod8.
\]
而 \(Y\) 分块且对称，故 \(X+2Y\) 仍在 \(\mathscr C_{F,2}\) 中。于是 (2) 等价于 \(X+2Y\in\mathscr R_{F,2}\)。以 \(X+2Y\) 为基域参数重写原类，便得到 (7) 中的 \(1+\theta\)。

由 (1)、(7) 以及二阶群的轨道计数公式，得到下表。

| 集合 | 固定点数 | \(\langle\sigma\rangle\) 轨道数 |
|---|---:|---:|
| \(\mathscr R_{K,M}\)，\(M\ge2\) | \(f\,2^{r+Ma}\) | \(f\,2^{r-1}\bigl(2^{2(M-1)a}+2^{Ma}\bigr)\) |
| \(\mathscr C_{K,2}\) | \(4^s\) | \(4^s\) |
| \(\mathscr C_{K,M}\)，\(M\ge3\) | \(f\,2^{r+Ma+2d}\) | \(f\,2^{r-1+2d}\bigl(2^{2(M-1)a}+2^{Ma}\bigr)\) |

从 \(M+1\) 到 \(M\) 的约化具有如下像和纤维。固定点两行的像都按自然包含嵌入扩域矩阵环。

| 约化的源 | 精度 \(M\) 的像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{L,M+1}\) | \(\mathscr R_{L,M}\) | \(q_L^a\) |
| \(\mathscr C_{L,M+1}\) | \(\mathscr R_{L,M}\) | \(q_L^s\) |
| \(\mathscr R_{K,M+1}^{\sigma}\) | \(\mathscr R_{F,M}\) | \(4^a\) |
| \(\mathscr C_{K,M+1}^{\sigma}\) | \(\mathscr R_{F,M}\) | \(4^s\) |

前两行来自逐层提升计算。对后两行，(7) 在精度 \(M+1\) 的 \(Y\) 项约化后消失。可提升类的基域参数有 \(2^a\) 个提升，每个又有 \(2^a\) 个 \(Y\) 可选。有限方程解的相应两个因子均为 \(2^s\)。

**能提升为 \(\sigma\)-固定真正解的类，以及能出现在无限逐层相容固定序列中的类，两者都恰为 \(\mathscr R_{F,M}\)。** 事实上，\(\mathcal O_K^\sigma=\mathbb Z_2\)，所以 \(\mathscr S_K^\sigma=\mathscr S_F\)，其中每个解在所有精度给出相容固定序列。反过来，仅要求存在精度 \(M+1\) 的固定提升，就已由表中后两行强制当前类属于 \(\mathscr R_{F,M}\)。因此，对 (7) 中的固定 \(\mathscr R\) 类只须检验 \(Y=0\)，对固定 \(\mathscr C\) 类还须检验 (2)。

任意块秩和任意 \(M\ge2\) 都有非基域的固定 \(\mathscr C\) 类的实际例子。取 \(A_i=E_i\) 和
\[
I+2^{M-1}\theta e_pe_p^{\mathsf T}\pmod{2^M}.
\]
它满足有限方程，而第 \(p\) 列平方范数的 \(\theta\) 系数为 \(2^M\)，故连真正解的提升也不存在。固定 \(\mathscr R\) 类无法固定提升的例子由下面的正交矩阵给出。

## 3. 最优下降精度

所求最大整数为
\[
\boxed{\qquad
N_{\max}=
\begin{cases}
M,&\text{所有 }n_i=1,\\
M-1,&\text{至少一个 }n_i\ge2 .
\end{cases}\qquad}                                                   \tag{9}
\]
对给定的 \(A,U\)，按整基写 \(U=U_0+\theta U_1\)，其中 \(U_0,U_1\in M_d(\mathbb Z_2)\)。则还有可直接检验的判准
\[
\boxed{\quad
N=M\text{ 可取}
\iff U_1\equiv0\pmod{2^M}
\iff \sigma(U)\equiv U\pmod{2^{M+1}\mathcal O_K}.\quad}             \tag{10}
\]

事实上，\(U\bmod 2^M\) 在 (7) 的第二行中。取基域真正解 \(W\) 提升该行的参数 \(X\)，就有 \(U\equiv W\pmod{2^{M-1}}\)。同一公式表明，精度 \(M\) 可达恰当 \(Y=0\)，也即 \(U_1\equiv0\pmod{2^M}\)。再由 \(\sigma(U)-U=-2\theta U_1\) 比较整基系数，得 (10)。

当所有 \(n_i=1\) 时，甚至对每个输入都有 \(\mathscr S_K=\mathscr S_F\)。若有扩域解 \(U\)，由可行性判准取基域解 \(W\)。由 (3)，\(W^{-1}U\) 分块对角且正交。每块是平方为 \(1\) 的标量，只能取 \(\pm1\)，故 \(U\) 本身就在基域。

最后设某块含两个坐标，取 \(A_i=E_i\)。以下构造对两种扩张及所有 \(M\ge2\) 同时有效。置
\[
b_{-1}=1,\qquad b_2=0,\qquad t=2^{M-2}(b_\mu+\theta).
\]
在所选两坐标上取
\[
Q(t)=\frac{1}{1+t^2}
\begin{pmatrix}
1-t^2&-2t\\
2t&1-t^2
\end{pmatrix},
\]
其余坐标取恒等，得到 \(U\)。由于 \((1+\theta_{-1})^2=2\theta_{-1}\) 且 \(\theta_2^2=2\)，有 \(t^2\in 2^{2M-3}\mathcal O_K\)，故分母是单位。直接相乘得 \(Q(t)^{\mathsf T}Q(t)=I\)，且
\[
Q(t)\equiv I_2+
 2^{M-1}(b_\mu+\theta)
 \begin{pmatrix}0&1\\1&0\end{pmatrix}\pmod{2^M\mathcal O_K}.
\]
所以 \(U\in\mathscr S_K\)，其模 \(2^M\) 类固定，而非对角元的 \(\theta\) 系数模 \(2^M\) 为 \(2^{M-1}\)。这给出了每个精度上无法下降到 \(M\) 的真正解，证明了 (9) 的最优性。

在 \(\mu=-1,M=2\) 时，这个例子的实部为 \(I_2+2\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)\bmod4\)，列平方范数为 \(5\bmod8\)，具体展示了 (7) 中的例外。对任一 \(\mu\)，将构造中 \(M=2\) 的同一个真正解约化到任意精度 \(m\ge3\)，其非对角元的 \(\theta\) 系数仍为 \(2\bmod4\)，因而与其共轭构成一个二元轨道。