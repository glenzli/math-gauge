令
\[
t=\sum_{i=1}^r\binom{n_i}{2},\qquad
q_L=|\mathcal O_L/2\mathcal O_L|
=\begin{cases}2&L=F,\\4&L=K_\mu.\end{cases}
\]
对每个块计算一个奇偶量
\[
p_i=\sum_{\substack{a\in I_i\\ b\notin I_i}}
             \frac{(A_i)_{ba}}2\pmod 2,
\qquad
e=\begin{cases}1&\text{所有 }p_i=0,\\0&\text{其余情形}.\end{cases}
\]
这里参与求和的条目都是偶数，故 \(e\) 只依赖于 \(A_i\bmod 4\)。

## 1. 可行性、基数与提升判准

对三个域 \(L\)，**\(\mathscr S_L(A)\) 非空当且仅当 \(e=1\)**。有限精度的基数为
\[
\boxed{\begin{aligned}
|\mathscr R_{L,M}(A)|&=e\,2^r q_L^{(M-1)t},\\
|\mathscr C_{L,2}(A)|&=q_L^{d+t},\\
|\mathscr C_{L,M}(A)|&=e\,2^r q_L^{(M-1)t+d}\qquad(M\ge3).
\end{aligned}}
\]
特别地，\(\mathscr C_{L,2}(A)\) 总是非空。

给定 \(\bar U\in\mathscr C_{L,M}(A)\)，任取其整矩阵代表 \(U_*\)。提升判准是每一列的平方长度再多满足一位精度，即
\[
\boxed{\quad
\bar U\in\mathscr R_{L,M}(A)
\quad\Longleftrightarrow\quad
(U_*^{\mathsf T}U_*)_{aa}\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le a\le d).\quad}                                      \tag{1}
\]
将一列改动 \(2^M v\)，其平方长度的改变量属于 \(2^{M+1}\mathcal O_L\)，所以可以直接用任意代表检验。

### 同时分块的标准标架

取 \(h(x)=3x^2-2x^3\)，从每个 \(A_i\) 开始迭代 \(h\)。由于 \(h(x)-x\) 被 \(x^2-x\) 整除，且 \(h(x)^2-h(x)\) 被 \((x^2-x)^2\) 整除，而 \(A_i^2-A_i\equiv0\bmod2\)，迭代在 \(M_d(\mathbb Z_2)\) 中收敛到幂等矩阵 \(P_i\equiv E_i\bmod2\)。这些 \(P_i\) 对称、两两交换，且与所有 \(A_j\) 交换。对 \(i\ne j\)，\(P_iP_j\) 是被 \(2\) 整除的幂等矩阵，取任意高次幂即得 \(P_iP_j=0\)。同理 \(I-\sum_iP_i=0\)。

令 \(J_i\) 为第 \(i\) 块的标准坐标嵌入，定义
\[
B_i=P_iJ_i(J_i^{\mathsf T}P_iJ_i)^{-1},\qquad
B=(B_1\ \cdots\ B_r).
\]
逆矩阵存在，因为括号中的矩阵模 \(2\) 为单位阵。\(B_i\) 在 \(I_i\) 上的行组成单位阵，将其余各行写成 \(2X_i\)。于是 \(B\equiv I\bmod2\)，且
\[
P_iB=BE_i,\qquad
B^{\mathsf T}B=\operatorname{diag}(H_1,\ldots,H_r),\qquad
H_i=I_{n_i}+4D_i,\qquad D_i=X_i^{\mathsf T}X_i.                \tag{2}
\]
写 \(A_i=E_i+2Z_i,\ P_i=E_i+2Y_i\)。交换关系给出
\([E_i,Z_i-Y_i]\equiv0\bmod2\)，所以 \(X_i\bmod2\) 就是 \(Z_i\) 在行 \(I_i^c\)、列 \(I_i\) 上的子矩阵。因此
\[
\operatorname{tr}D_i\equiv p_i\pmod2.                           \tag{3}
\]

在整数环及其模 \(2^M\) 的商环上，对满足 \(U\equiv I\bmod2\)、\(U^{\mathsf T}U=I\) 的矩阵，原题的分块条件都等价于
\[
P_iU=UE_i\qquad(\forall i).                                    \tag{4}
\]
事实上，若 \(U^{\mathsf T}A_iU\) 分块，则由多项式迭代，\(U^{\mathsf T}P_iU\) 也分块。其第 \(j\) 块是模 \(2\) 等于 \(\delta_{ij}I\) 的幂等矩阵，故等于 \(\delta_{ij}I\)。反过来，(4) 与 \([A_j,P_i]=0\) 给出所需的分块条件。

由 (2)、(4)，所有问题都化为独立地取
\[
U=B\,\operatorname{diag}(V_1,\ldots,V_r),\qquad V_i\equiv I\bmod2,
\]
并在相应精度上解 \(V_i^{\mathsf T}H_iV_i=I\)。

### 模 \(4\) 的起点与逐层提升

先看一块，省略下标，记块秩为 \(n\)，\(t_n=\binom n2\)，\(H=I+4D\)，\(k=\mathcal O_L/2\mathcal O_L\)。模 \(4\) 写 \(V=I+2X\)，此时 \(X\) 取值于 \(M_n(k)\)。正交方程模 \(4\) 恰好要求 \(X=X^{\mathsf T}\)，故有 \(q_L^{n+t_n}\) 个解。要使各列平方长度模 \(8\) 也正确，展开对角元，得到在 \(k\) 中的方程
\[
x_{aa}+x_{aa}^2+\sum_{b\ne a}x_{ba}^2+D_{aa}=0
\qquad(1\le a\le n).                                           \tag{5}
\]

对两个扩域统一取
\[
\eta=\begin{cases}
1+\theta_{-1}&\mu=-1,\\
\theta_2&\mu=2.
\end{cases}
\]
则 \(1,\eta\) 是整基，\(\eta^2\in2\mathcal O_\mu\)，且
\(k=\mathbb F_2[\bar\eta]/(\bar\eta^2)\)。因而 \(u+v\bar\eta\) 的平方等于 \(u\)。基域的 \(k=\mathbb F_2\) 只需保留常数部分。由 (5)，对角元 \(x_{aa}\) 可各取 \(0,1\)，扩域情形下其 \(\bar\eta\) 系数必须为零。对每条无向边 \(\{a,b\}\)，令 \(u_{ab}\) 为 \(x_{ab}=x_{ba}\) 的常数部分，余下的条件为
\[
\sum_{b\ne a}u_{ab}=D_{aa}\pmod2.
\]
每条边贡献向量 \(e_a+e_b\)，它们张成坐标和为零的子空间，维数为 \(n-1\)，这也包括 \(n=1\)。故可解条件为 \(\operatorname{tr}D\equiv0\bmod2\)。可解时，边的常数部分有 \(2^{t_n-(n-1)}\) 种选法，每条边还有 \(q_L/2\) 种选取其余部分的方式。计入对角元，满足额外一位精度的模 \(4\) 解共有
\[
2^n\,2^{t_n-(n-1)}(q_L/2)^{t_n}=2q_L^{t_n}.                  \tag{6}
\]

现在设 \(m\ge2\)。给定模 \(2^m\) 的块解，选取代表 \(V\)，其模 \(2^{m+1}\) 的候选提升为 \(V+2^mY\)，其中 \(Y\bmod2\) 任意。记 \(G=V^{\mathsf T}HV\)。修正后的 Gram 矩阵为
\[
G+2^m(V^{\mathsf T}HY+Y^{\mathsf T}HV)+2^{2m}Y^{\mathsf T}HY.
\]
对每个 \(a<b\)，要使非对角元在模 \(2^{m+1}\) 正确，恰好规定了 \(Y_{ab}+Y_{ba}\bmod2\)。对角元模 \(2^{m+1}\) 已由原解决定。因此，存在下一层解当且仅当原解的对角元已经模 \(2^{m+1}\) 正确，此时有 \(q_L^{n+t_n}\) 个下一层解。

若还要求下一层解的对角元模 \(2^{m+2}\) 正确，则每个 \(Y_{aa}\bmod2\) 也被唯一确定。这是因为对角改变量除以 \(2^{m+1}\) 后模 \(2\) 等于 \(Y_{aa}\)，其中用到了 \(m\ge2\) 及 \(V,H\equiv I\bmod2\)。故满足这一额外要求的提升有 \(q_L^{t_n}\) 个。如此逐层选取并取极限，就得到真正解。利用标架 \(B\) 选取分块代表，再用平方长度对代表的独立性，即得 (1)。将 (3)、(6) 与逐层计数按块相乘，得到第 1 节的全部公式。

## 2. 固定矩阵类、轨道与约化纤维

记 \(\operatorname{Sym}_{\rm bl}\) 为 \(\mathbb F_2\) 上按给定分块的块对角对称矩阵空间，\(\operatorname{Alt}_{\rm bl}\) 为其中对角元全零的子空间。两者维数分别为 \(d+t\) 和 \(t\)。置 \(h_M=2^{M-1}\)，用上面选定的 \(\eta\)。固定矩阵类有如下**唯一表示**，其中 \(T\) 的条目可用 \(0,1\) 代表：
\[
\boxed{\begin{aligned}
\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
 &=\{\,W_0+h_M\eta T:
       W_0\in\mathscr R_{F,M}(A),\ T\in\operatorname{Alt}_{\rm bl}\,\},\\
\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
 &=\{\,W_0+h_M\eta T:
       W_0\in\mathscr C_{F,M}(A),\ T\in\operatorname{Sym}_{\rm bl}\,\}.
\end{aligned}}                                                   \tag{7}
\]
在这两个表示中，基域的相应集合都恰是 \(T=0\) 的部分。

为证 (7)，将一个条目写成 \(a+b\eta\)。其共轭与自身之差为 \(-2b\theta_\mu\)，由整基 \(1,\theta_\mu\) 可知，该条目模 \(2^M\) 固定当且仅当 \(b\in 2^{M-1}\mathbb Z_2\)。这给出了 \(W_0+h_M\eta T\) 的唯一分解。代入 (4)，基域部分须满足 \(P_iW_0=W_0E_i\)，而 \(T\) 须满足 \(E_iT=TE_i\)，即 \(T\) 块对角。

又因 \(h_M^2\eta^2\in2^{M+1}\mathcal O_\mu\)，正交方程模 \(2^M\) 分解为 \(W_0^{\mathsf T}W_0=I\bmod2^M\) 及 \(T+T^{\mathsf T}=0\bmod2\)。在 (1) 所需的对角精度上，每个平方长度还产生交叉项
\[
2^M\eta\,(W_0^{\mathsf T}T)_{aa}
\equiv 2^M\eta\,T_{aa}\pmod{2^{M+1}\mathcal O_\mu}.
\]
由 \(1,\eta\) 的线性独立性，(1) 等价于 \(W_0\) 自身通过基域的提升检验，且 \(T_{aa}=0\) 对每个 \(a\) 成立。这里 \(\eta^2\in2\mathcal O_\mu\) 保证了公式在 \(M=2\) 也适用。

固定点数因而为
\[
\begin{aligned}
|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}|
 &=2^t|\mathscr R_{F,M}(A)|=e\,2^{r+Mt},\\
|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}|
 &=2^{d+t}|\mathscr C_{F,M}(A)|
 =\begin{cases}4^{d+t}&M=2,\\ e\,2^{r+Mt+2d}&M\ge3.\end{cases}
\end{aligned}
\]
对一个对合，轨道数是总点数与固定点数之和的一半。因此 \(\mathscr R,\mathscr C\) 在扩域上的轨道数分别为
\[
o_R=e\,2^{r-1}\bigl(4^{(M-1)t}+2^{Mt}\bigr),\qquad
o_C=\begin{cases}4^{d+t}&M=2,\\4^d o_R&M\ge3.\end{cases}
\]

**从 \(M+1\) 到 \(M\) 的约化**如下，表中各集合均取同一输入 \(A\)。

| 精度 \(M+1\) 的定义域 | 在精度 \(M\) 的像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{L,M+1}\) | \(\mathscr R_{L,M}\) | \(q_L^t\) |
| \(\mathscr C_{L,M+1}\) | \(\mathscr R_{L,M}\) | \(q_L^{d+t}\) |
| \(\mathscr R_{K_\mu,M+1}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(4^t\) |
| \(\mathscr C_{K_\mu,M+1}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(4^{d+t}\) |

前两行来自逐层提升计算。后两行中，(7) 在精度 \(M+1\) 的附加项为 \(2^M\eta T\)，约化时消失。每个可取的基域提升都可独立配上任意相应的 \(T\)，从而得到表中的纤维数。

对两种固定点集，**能提升为 \(\sigma_\mu\)-固定真正解的类，以及能出现在无限逐层相容固定序列中的类，均恰为 \(\mathscr R_{F,M}(A)\)**。事实上，固定的真正解逐条目属于 \(\mathbb Z_2\)，正是 \(\mathscr S_F(A)\) 的元素。相容序列的必要条件仅用其第 \(M+1\) 层和上表便可得到。反过来，每个基域真正解的各层约化给出所需的相容序列。

## 3. 最优下降精度

对两种 \(\mu\)，答案相同：
\[
\boxed{\quad
N_{\max}=
\begin{cases}
M&\text{所有 }n_i=1,\\
M-1&\text{至少一个 }n_i\ge2.
\end{cases}\quad}                                                \tag{8}
\]

事实上，给定题中的 \(A,U\)，将 \(U\bmod2^M\) 按 (7) 的第一行写成 \(W_0+2^{M-1}\eta T\)。取 \(W_0\) 的一个基域真正提升 \(W\)，便有 \(U\equiv W\bmod2^{M-1}\mathcal O_\mu\)。对这个给定的 \(A,U\)，能取 \(N=M\) 的必要充分条件是 **\(T=0\)**。等价地，将 \(U=X+\eta Y\) 写成两个基域整矩阵的组合，判准可写为
\[
Y\equiv0\pmod{2^M}
\quad\Longleftrightarrow\quad
\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}.
\]

当所有 \(n_i=1\) 时，\(t=0\)。此时甚至有真正解集合的等式 \(\mathscr S_{K_\mu}(A)=\mathscr S_F(A)\)。若扩域上有解，由可行性判准可取一个基域解 \(W\)。由 (4)，对任意扩域解 \(U\)，\(W^{-1}U\) 都是块对角正交矩阵，每个一维块只能为 \(1\) 或 \(-1\)，故 \(U\) 本身属于基域。

当某块含有两个坐标 \(a,b\) 时，取 \(A_i=E_i\)。对任意 \(M\ge2\)，令 \(s=2^{M-2}\eta\)，在这两个坐标上取矩阵
\[
\frac{1}{1+s^2}
\begin{pmatrix}1-s^2&-2s\\2s&1-s^2\end{pmatrix},
\]
其余坐标上取单位阵，得到 \(U\)。由于 \(s^2\in2\mathcal O_\mu\)，分母是单位，且此矩阵直接满足正交方程。用 \(e_{ab}\) 表示矩阵单位，模 \(2^M\) 有
\[
U\equiv I+2^{M-1}\eta(e_{ab}+e_{ba}).
\]
这里对角改变量属于 \(2s^2\mathcal O_\mu\subseteq2^M\mathcal O_\mu\)。所以 \(U\) 是真正解，其模 \(2^M\) 类固定，并且 (7) 中的 \(T\ne0\)。这对每个 \(M\) 都给出无法匹配到精度 \(M\) 的实例，同时给出了固定的 \(\mathscr R\) 类无法向上一层固定提升的实例。取此构造的 \(M=2\) 后保留同一个真正解，其非对角条目的 \(\eta\) 系数恰被 \(2\) 整除一次，故它在每个精度 \(m\ge3\) 又都给出长度为二的轨道。

最后，以下矩阵具体实现了有限方程中其余的提升障碍。

- **可行性失败。** 从两个不同块 \(p,q\) 各取坐标 \(a,b\)，令 \(S=e_{ab}+e_{ba}\)。取 \(A_p=E_p+2S,\ A_q=E_q-2S\)，其余 \(A_i=E_i\)。这些矩阵交换，因为 \(A_p+A_q=E_p+E_q\) 与二者均交换。此时 \(p_p=p_q=1\)，而 \(I+2S\bmod4\) 是一个有限解。它在三个域上都无法提升到模 \(8\)。
- **基域上可行但有限解无法提升。** 取 \(A_i=E_i\)。对每个 \(M\ge3\)，\(I+2^{M-1}e_{aa}\) 满足模 \(2^M\) 的方程，其第 \(a\) 列平方长度模 \(2^{M+1}\) 为 \(1+2^M\)。在 \(M=2\) 且某块含 \(a,b\) 两个坐标时，\(I+2(e_{ab}+e_{ba})\) 的第 \(a\) 列平方长度为 \(5\)，同样无法提升。若所有块均为一维且输入可行，则基数公式给出 \(\mathscr C_{F,2}=\mathscr R_{F,2}\)。
- **扩域上的固定有限解无法提升。** 仍取 \(A_i=E_i\)。对任意块秩和每个 \(M\ge2\)，\(I+2^{M-1}\eta e_{aa}\) 属于 \(\mathscr C_{K_\mu,M}^{\sigma_\mu}\)。其第 \(a\) 列平方长度模 \(2^{M+1}\) 为 \(1+2^M\eta\)，故它连扩域上的真正提升也没有。