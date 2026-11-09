记
\[
T=\sum_{i=1}^r\binom{n_i}{2},\qquad h=T+d,\qquad
q_F=2,\quad q_{K_{-1}}=q_{K_2}=4.
\]
这里 \(q_L=|\mathcal O_L/2\mathcal O_L|\)，不是剩余域的大小。

对每个块定义
\[
\kappa_i(A)=
\sum_{\substack{a\in I_i\\ b\notin I_i}}
\frac{(A_i)_{ba}}2\pmod2\in\mathbb F_2,
\qquad
\eta(A)=
\begin{cases}
1,&\kappa_i(A)=0\quad(\forall i),\\
0,&\text{否则}.
\end{cases}
\tag{1}
\]
这些量只需 \(A_i\bmod4\) 即可计算。

三个域上的可行性判准完全相同：
\[
\boxed{\mathscr S_L(A)\ne\varnothing\iff\eta(A)=1.}
\tag{2}
\]
全部基数如下，其中 \(M\ge2\)：
\[
\boxed{|\mathscr R_{L,M}(A)|=\eta(A)\,2^r q_L^{(M-1)T}.}
\tag{3}
\]
\[
\boxed{
|\mathscr C_{L,M}(A)|=
\begin{cases}
q_L^{h},&M=2,\\
\eta(A)\,2^r q_L^{(M-1)T+d},&M\ge3.
\end{cases}}
\tag{4}
\]
因此 \(\mathscr C_{L,2}(A)\) 总非空；其余集合的非空条件就是 (2)。

还有一个直接可核验的提升判准。给定
\(\bar U\in\mathscr C_{L,M}(A)\)，任取其整系数提升
\(\widetilde U=(\widetilde u_1,\ldots,\widetilde u_d)\)，则
\[
\boxed{
\bar U\in\mathscr R_{L,M}(A)
\iff
\widetilde u_a^{\mathsf T}\widetilde u_a
\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le a\le d).
}
\tag{5}
\]
右侧与所选提升无关：改变一列 \(2^M v\)，其范数改变
\(2^{M+1}\widetilde u_a^{\mathsf T}v+2^{2M}v^{\mathsf T}v\)。

先证明这些结论，并计算一般约化映射的纤维。

对矩阵迭代多项式 \(f(x)=3x^2-2x^3\)。因为
\[
f(x)-x=-(2x-1)(x^2-x),\qquad
f(x)^2-f(x)=-(x^2-x)^2(3-2x)(2x+1),
\]
从 \(A_i\) 出发的迭代收敛到一个对称幂等矩阵 \(P_i\)，满足
\[
P_i\equiv E_i\pmod2.
\]
所有 \(P_i,A_j\) 彼此交换。对 \(i\ne j\)，\(P_iP_j\) 是模 \(2\) 为零的幂等矩阵，故为零；同理
\[
P_iP_j=0\ (i\ne j),\qquad \sum_iP_i=I.
\tag{6}
\]
这里用了简单事实：若幂等矩阵属于 \(2M_d(\mathbb Z_2)\)，则反复平方表明它属于每个 \(2^mM_d(\mathbb Z_2)\)，因而为零。

取 \(\operatorname{im}P_i\) 的图形基 \(B_i\)，使其在 \(I_i\) 行上的子矩阵为 \(I_{n_i}\)。于是
\[
B_i=
\begin{pmatrix}
I_{n_i}\\ 2S_i
\end{pmatrix},
\qquad
G_i:=B_i^{\mathsf T}B_i=I_{n_i}+4S_i^{\mathsf T}S_i,
\tag{7}
\]
其中行的排列按 \(I_i\) 与其补集理解。令 \(B=(B_1,\ldots,B_r)\)，则
\[
B\equiv I\pmod2,\qquad
B^{\mathsf T}B=\operatorname{diag}(G_1,\ldots,G_r).
\tag{8}
\]

由 \(P_i^2=P_i\) 可知 \((P_i)_{I_i,I_i}\equiv I\pmod4\)。再将
\([A_i,P_i]=0\) 模 \(4\) 展开，得到
\[
(S_i)_{ba}\equiv \frac{(A_i)_{ba}}2\pmod2
\quad(a\in I_i,\ b\notin I_i).
\]
从而
\[
\operatorname{tr}(S_i^{\mathsf T}S_i)\equiv\kappa_i(A)\pmod2.
\tag{9}
\]

这个分解也适用于有限精度。若 \(U\) 满足题中的正交与同时分块条件，则
\(U^{-1}A_iU\) 块对角，因此 \(U^{-1}P_iU\) 也块对角。后者是模 \(2\) 等于 \(E_i\) 的幂等矩阵，只能等于 \(E_i\)。在有限商环中，同一论证使用 \(2\) 的幂零性成立。因此，真解及形式解都分别对应于
\[
U=B\,\operatorname{diag}(Q_1,\ldots,Q_r),\qquad
Q_i\equiv I\pmod2,\qquad
Q_i^{\mathsf T}G_iQ_i=I,
\tag{10}
\]
最后一个等式按相应精度理解。

下面使用一个提升引理。设 \(G\) 对称，\(m\ge2\)，且
\(Q^{\mathsf T}GQ\) 的非对角元属于 \(2^m\mathcal O_L\)，对角元模
\(2^{m+1}\) 等于 \(1\)。则存在
\[
Q_\infty\equiv Q\pmod{2^m},\qquad Q_\infty^{\mathsf T}GQ_\infty=I.
\tag{11}
\]
事实上，右乘 \(I+2^mZ\) 后，下一位非对角误差由
\(Z_{ab}+Z_{ba}\) 控制，下一位对角误差由 \(Z_{aa}\) 控制，均在
\(\mathcal O_L/2\mathcal O_L\) 中独立可解。具体地，若当前 Gram 矩阵为 \(H\)，则
\[
\begin{aligned}
(H_{\rm new})_{ab}
&\equiv H_{ab}+2^m(Z_{ab}+Z_{ba})\pmod{2^{m+1}}
&& (a\ne b),\\
(H_{\rm new})_{aa}
&\equiv H_{aa}+2^{m+1}Z_{aa}\pmod{2^{m+2}}.
\end{aligned}
\]
逐层进行并利用完备性，即得 (11)。结合 (10)，这也证明了 (5)。

现在考虑一个块 \(G=I+4D\)，其中 \(D=S^{\mathsf T}S\)。若
\(Q\equiv I\pmod2\) 且 \(Q^{\mathsf T}GQ=I\)，写
\(\det Q=1+2z\)，取行列式并模 \(8\)，得
\[
\operatorname{tr}D+z+z^2=0
\quad\text{于 }\mathcal O_L/2\mathcal O_L.
\tag{12}
\]
三个环的剩余域都是 \(\mathbb F_2\)，而 \(z+z^2\) 在剩余域中为零，故
\(\operatorname{tr}D\) 必须为偶数。

反过来，若 \(\operatorname{tr}D\) 为偶数，则存在一个对称零对角矩阵
\(X\in M_n(\mathbb F_2)\)，使
\[
\sum_{b\ne a}X_{ba}=D_{aa}\pmod2.
\tag{13}
\]
这是因为完全图的边界映射的像恰为坐标和为零的向量空间；也可直接用以第 \(n\) 个顶点为中心的星形图构造。取 \(X\) 的整数提升，令 \(Q_0=I+2X\)。则
\(Q_0^{\mathsf T}GQ_0\) 的非对角元被 \(4\) 整除，对角元模 \(8\) 等于 \(1\)。由 (11)，它可在 \(\mathbb Z_2\) 上提升为真正的等距矩阵。

这证明了 (2)，并给出构造基域真解 \(U_0\) 的方法。一旦可行，
\[
\mathscr S_L(A)=
U_0\prod_{i=1}^r
\{g\in O_{n_i}(\mathcal O_L):g\equiv I\pmod2\}.
\tag{14}
\]

为计数，先看一个秩 \(n\) 的标准块，记 \(t=\binom n2\)。
模 \(4\) 的形式解是 \(I+2X\)，其中
\[
X\in\operatorname{Sym}_n(\mathcal O_L/2\mathcal O_L).
\]
它可真正提升，当且仅当
\[
X_{aa}+\sum_bX_{ba}^2=0
\quad(\forall a).
\tag{15}
\]
在基域上，这要求非对角部分的每个顶点度数为偶数，对角元任意，故共有
\(2^{t+1}\) 个。

在两个扩域上，
\[
\mathcal O_\mu/2\mathcal O_\mu
\simeq\mathbb F_2[\epsilon]/(\epsilon^2),
\]
其中 \(\mu=2\) 时可取 \(\epsilon=\theta_2\)，\(\mu=-1\) 时可取
\(\epsilon=1+\theta_{-1}\)。写 \(X=A+\epsilon B\)，则 (15) 等价于
\[
B_{aa}=0,\qquad \sum_{b\ne a}A_{ba}=0.
\]
因此共有 \(2^{2t+1}\) 个。两种情形统一写成 \(2q_L^t\)。

从精度 \(m\) 提升到 \(m+1\)，取一个真正代表 \(g\)，其上方的矩阵写为
\[
g(I+2^mX)\pmod{2^{m+1}}.
\]
成为形式解等价于 \(X\) 对称；成为真正解的约化类还要求
\(\operatorname{diag}X=0\)。故每块的两种纤维大小分别为
\(q_L^{t+n}\) 和 \(q_L^t\)。同时，(5) 表明下一层形式解必落入当前层真正可提升的集合。于是，对所有 \(M\ge2\)，有下表：

| 约化映射 | 约化像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{L,M+1}\to\mathscr R_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^T\) |
| \(\mathscr C_{L,M+1}\to\mathscr C_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^h\) |

若该像为空，则源也为空。模 \(4\) 时，(8) 给出
\(|\mathscr C_{L,2}|=q_L^h\)；结合上述首层真解计数与纤维计算，即得 (3)、(4)。

现在讨论伽罗瓦固定点。令
\[
\mathfrak s=\prod_i\operatorname{Sym}_{n_i}(\mathbb F_2),\qquad
\mathfrak a=\{B\in\mathfrak s:\operatorname{diag}B=0\}.
\]
把它们视为 \(d\times d\) 块对角矩阵空间，则
\[
\dim\mathfrak s=h,\qquad \dim\mathfrak a=T.
\]
以下相加都在模 \(2^M\) 的矩阵环中进行。

对所有 \(M\ge2\)，形式解的固定类都有唯一表达
\[
\boxed{
\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
=
\{V+2^{M-1}\theta_\mu B:
V\in\mathscr C_{F,M}(A),\ B\in\mathfrak s\}.
}
\tag{16}
\]
对真正解的约化类，当 \(M\ge3\) 时，
\[
\boxed{
\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
=
\{V+2^{M-1}\theta_\mu B:
V\in\mathscr R_{F,M}(A),\ B\in\mathfrak a\}.
}
\tag{17}
\]

模 \(4\) 的答案需要单独写出。对 \(V\in\mathscr C_{F,2}(A)\)，定义
\[
c_a(V)=\frac{\widetilde v_a^{\mathsf T}\widetilde v_a-1}{4}\pmod2,
\tag{18}
\]
其中 \(\widetilde V\) 是任意整数提升。对 \(B\in\mathfrak a\)，定义
\[
(\partial B)_a=\sum_{\substack{b\in I_i\\b\ne a}}B_{ba},
\qquad a\in I_i.
\]
则
\[
\boxed{
\mathscr R_{K_\mu,2}(A)^{\sigma_\mu}
=
\{V+2\theta_\mu B:
V\in\mathscr C_{F,2}(A),\
B\in\mathfrak a,\
c(V)=\bar\mu\,\partial B\}.
}
\tag{19}
\]
这里 \(\bar\mu\) 是 \(\mu\bmod2\)。特别地：

- 对 \(\mu=2\)，(17) 在 \(M=2\) 时也成立。
- 对 \(\mu=-1\)，条件是 \(c(V)=\partial B\)，其中 \(V\) 未必属于
  \(\mathscr R_{F,2}(A)\)。
- 两个扩域上都有
  \(\mathscr R_{K_\mu,2}^{\sigma_\mu}=\mathscr R_{K_\mu,2}\)、
  \(\mathscr C_{K_\mu,2}^{\sigma_\mu}=\mathscr C_{K_\mu,2}\)。

证明这些公式只需展开。固定标量类恰为
\[
a+2^{M-1}\theta_\mu b,
\qquad a\in\mathbb Z/2^M,\quad b\in\mathbb F_2.
\]
因此固定矩阵类唯一写作 \(V+2^{M-1}\theta_\mu B\)。将正交条件模
\(2^M\) 展开，得到 \(V\) 正交且 \(B\) 对称；将同时分块条件展开，利用
\(A_i\equiv E_i\)、\(V\equiv I\pmod2\)，得到 \(B\) 必须块对角。这证明 (16)。

对一列，令 \(\delta=2^{M-1}\)，则
\[
(v+\delta\theta_\mu b)^{\mathsf T}(v+\delta\theta_\mu b)-1
=
v^{\mathsf T}v-1
+2^M\theta_\mu v^{\mathsf T}b
+2^{2M-2}\mu\,b^{\mathsf T}b.
\tag{20}
\]
当 \(M\ge3\) 时，最后一项模 \(2^{M+1}\) 消失。由 (5)，其余两项分别给出
\(V\in\mathscr R_{F,M}\) 和 \(\operatorname{diag}B=0\)，即 (17)。
当 \(M=2\) 时，(20) 则给出
\[
B_{aa}=0,\qquad c_a(V)=\bar\mu\sum_bB_{ba},
\]
即 (19)。

特别地，扩域不会产生新的、条目全在基域商环中的真正可提升类：
\[
\boxed{
\mathscr R_{K_\mu,M}(A)\cap
M_d(\mathbb Z_2/2^M\mathbb Z_2)
=\mathscr R_{F,M}(A).
}
\tag{21}
\]
形式解也有对应的交集等式。对真正解本身则有
\[
\boxed{\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A).}
\tag{22}
\]

固定点数为
\[
\boxed{
|\mathscr R_{K_\mu,M}^{\sigma_\mu}|
=\eta(A)\,2^{r+MT}\qquad(M\ge2),
}
\tag{23}
\]
\[
\boxed{
|\mathscr C_{K_\mu,M}^{\sigma_\mu}|
=
\begin{cases}
2^{2h},&M=2,\\
\eta(A)\,2^{r+MT+2d},&M\ge3.
\end{cases}}
\tag{24}
\]
式 (23) 在 \(M=2\) 时由所有类均固定得到，在其余精度由 (17) 得到。

当集合非空时，固定真解类与基域真解类的数量比为 \(2^T\)；固定形式解类与基域形式解类的数量比为 \(2^h\)。因此前者在 \(T=0\) 时相等，在 \(T>0\) 时严格扩大；后者只要非空，就严格扩大。

由二阶群作用的 Burnside 公式，轨道数为
\[
\boxed{
\#\bigl(\mathscr R_{K_\mu,M}/\langle\sigma_\mu\rangle\bigr)
=
\eta(A)\,2^{r-1}
\left(2^{2(M-1)T}+2^{MT}\right).
}
\tag{25}
\]
\[
\boxed{
\#\bigl(\mathscr C_{K_\mu,M}/\langle\sigma_\mu\rangle\bigr)
=
\begin{cases}
2^{2h},&M=2,\\
\eta(A)\,2^{r+2d-1}
\left(2^{2(M-1)T}+2^{MT}\right),&M\ge3.
\end{cases}}
\tag{26}
\]

固定点集之间的约化映射如下，对所有 \(M\ge2\) 均成立：

| 约化映射 | 约化像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{K_\mu,M+1}^{\sigma_\mu}\to\mathscr R_{K_\mu,M}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(4^T\) |
| \(\mathscr C_{K_\mu,M+1}^{\sigma_\mu}\to\mathscr C_{K_\mu,M}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(4^h\) |

因为源精度 \(M+1\ge3\)，可以使用 (16)、(17)：其中的
\(2^M\theta_\mu B\) 项约化后消失，而基域部分的约化像由前一张表给出。
两种纤维大小分别是
\[
2^T\cdot2^T=4^T,\qquad 2^h\cdot2^h=4^h.
\]

这也完全回答了固定类的提升与相容性问题。对任一固定矩阵类，以下条件等价：

1. 它可提升为一个 \(\sigma_\mu\)-固定的真正解；
2. 它可成为一条在所有更高精度上逐层相容的固定 \(\mathscr R\)-类序列的分量；
3. 它可成为一条在所有更高精度上逐层相容的固定 \(\mathscr C\)-类序列的分量；
4. 它属于嵌入的 \(\mathscr R_{F,M}(A)\)。

事实上，连“存在下一层固定类提升”就已等价于这些条件。具体而言：

- 对固定的 \(\mathscr R\)-类，条件就是其条目均来自
  \(\mathbb Z_2/2^M\mathbb Z_2\)，即上述唯一表达中的 \(B=0\)。
- 对固定的 \(\mathscr C\)-类，还需其基域部分满足 (5)。

最后，第三问中的最大整数为
\[
\boxed{
N_{\max}=
\begin{cases}
M,&T=0\quad\text{即所有 }n_i=1,\\
M-1,&T>0.
\end{cases}}
\tag{27}
\]

先证明下界。给定题设中的 \(U\)，其模 \(2^M\) 类是固定的
\(\mathscr R\)-类。若 \(M\ge3\)，由固定点约化像的结论，它模
\(2^{M-1}\) 落在 \(\mathscr R_{F,M-1}(A)\)，故存在所需的
\(W\in\mathscr S_F(A)\)。若 \(M=2\)，由可行性等价知基域真解存在，且
\(U,W\) 均模 \(2\) 等于 \(I\)，所以仍能取 \(N=M-1=1\)。

若所有块秩均为 \(1\)，则 (14) 中每个正交群只有 \(\{1,-1\}\)，所以更强地有
\[
\boxed{\mathscr S_{K_\mu}(A)=\mathscr S_F(A).}
\tag{28}
\]
这给出精确下降。

对给定的 \(A,U\)，写其唯一展开为
\[
U=X+\theta_\mu Y,\qquad X,Y\in M_d(\mathbb Z_2).
\]
能够取 \(N=M\) 的必要充分条件是
\[
\boxed{
Y\equiv0\pmod{2^M}
\iff
\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}.
}
\tag{29}
\]
必要性显然；充分性由 (21) 得到。第二个等价关系来自
\(\sigma_\mu(U)-U=-2\theta_\mu Y\) 以及 \(\{1,\theta_\mu\}\) 的
\(\mathbb Z_2\)-基性质。

下面给出反例和统一构造，验证所有上述严格性及界的最优性。

首先，只要 \(r\ge2\)，选不同块中的坐标 \(p\in I_i,q\in I_j\)，令
\[
J=e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T},\qquad
A_i=E_i+2J,\quad A_j=E_j-2J,\quad A_k=E_k\ (k\ne i,j).
\tag{30}
\]
这些矩阵对称且交换：在所选二维空间上，后两个非平凡矩阵互为
\(I\) 减去对方。此时
\[
\kappa_i=\kappa_j=1.
\]
故三个域上均无真解，精度至少为 \(3\) 时也无形式解。但是
\[
I+2J\pmod4\in\mathscr C_{L,2}(A).
\]
这给出了模 \(4\) 可解而实际不可解的例子，也说明两个二次扩张都不能消除可行性障碍。

其次，取 \(A_i=E_i\)。对任意 \(M\ge3\)，把某个对角元改为
\(1+2^{M-1}\)、其余保持为 \(I\)，得到基域形式解，但
\[
(1+2^{M-1})^2\not\equiv1\pmod{2^{M+1}},
\]
故它不属于 \(\mathscr R_{F,M}\)。在 \(M=2\) 时，只要某块秩至少为
\(2\)，块内矩阵 \(I+2J\) 也给出这样的例子，其相应列范数为 \(5\bmod8\)。
若所有块秩均为 \(1\)，则确实有
\(\mathscr C_{F,2}=\mathscr R_{F,2}\)。

在扩域上，对任意 \(M\ge2\)，把某个对角元改为
\[
1+2^{M-1}\theta_\mu
\tag{31}
\]
即可得到固定的形式解。其范数误差为
\[
2^M\theta_\mu+2^{2M-2}\mu,
\]
不被 \(2^{M+1}\) 整除。因此它不是可提升真解类，也不能处于无限相容的固定类序列中。这是适用于任意精度、任意块秩的统一例子。

最后，设某块秩至少为 \(2\)，仍取 \(A_i=E_i\)，在该块选取二维平面。令
\[
\tau_2=\theta_2,\qquad \tau_{-1}=1+\theta_{-1},\qquad
z=2^{M-2}\tau_\mu,
\]
并在该平面上置
\[
R(z)=
\begin{pmatrix}
c&s\\-s&c
\end{pmatrix},
\qquad
c=\frac{1-z^2}{1+z^2},\quad
s=\frac{2z}{1+z^2}.
\tag{32}
\]
在其余坐标上取恒等矩阵。

因为 \(z^2\in2\mathcal O_\mu\)，分母为单位；又
\(c^2+s^2=1\)，且 \(R(z)\equiv I\pmod2\)，故得到真正的扩域解。

当 \(\mu=2\) 时，
\[
s=\frac{2^{M-1}\theta_2}{1+2^{2M-3}},
\]
其 \(\theta_2\) 系数恰有 \(2\)-进赋值 \(M-1\)，而 \(c\) 在基域中。

当 \(\mu=-1\) 时，令 \(\lambda=2^{2M-3}\)，则
\[
c=\frac{1-\lambda^2-2\lambda\theta_{-1}}{1+\lambda^2},
\qquad
s=
\frac{2^{M-1}\bigl((1+\lambda)+(1-\lambda)\theta_{-1}\bigr)}
{1+\lambda^2}.
\]
这里 \(s\) 的 \(\theta_{-1}\) 系数也恰有赋值 \(M-1\)，而 \(c\) 的该系数赋值为 \(2M-2\ge M\)。因此，两个扩域上都满足
\[
\sigma_\mu(R(z))\equiv R(z)\pmod{2^M},
\qquad
\sigma_\mu(R(z))\not\equiv R(z)\pmod{2^{M+1}}.
\tag{33}
\]
由 (29)，不存在基域真解与它模 \(2^M\) 相同。这统一证明了所有
\(M\ge2\) 上 \(M-1\) 界的最优性；这些类也都是不能提升为固定真解、不能继续提升为下一层固定类的固定 \(\mathscr R\)-类。

在特殊的 \(\mu=-1,M=2\) 情形，(32) 给出
\[
c=\frac{-3-4\theta_{-1}}5,\qquad
s=\frac{6-2\theta_{-1}}5,
\]
其模 \(4\) 类为
\[
\begin{pmatrix}
1&2+2\theta_{-1}\\
2+2\theta_{-1}&1
\end{pmatrix}.
\]
它的基域部分
\(\begin{psmallmatrix}1&2\\2&1\end{psmallmatrix}\)
列范数为 \(5\bmod8\)，不属于 \(\mathscr R_{F,2}\)。这具体展示了 (19) 中必须保留的例外。

对任意其他可行输入，把这些块内例子左乘基域真解 \(U_0\)，即可得到对应输入上的同类例子。整个证明只使用了所给整数环的结构与完备性，无需援引二次型分类定理。