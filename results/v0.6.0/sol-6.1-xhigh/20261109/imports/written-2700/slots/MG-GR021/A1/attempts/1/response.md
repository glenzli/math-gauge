记
\[
m=\sum_{i=1}^r\binom{n_i}{2},\qquad s=m+d=\sum_{i=1}^r\frac{n_i(n_i+1)}2,
\qquad q_F=2,\quad q_{K_\mu}=4.
\]
对每个块定义
\[
\varepsilon_i(A)=
\sum_{\substack{a\in I_i\\ b\notin I_i}}
\frac{(A_i)_{ba}}2\pmod2\in\mathbb F_2,
\qquad
\chi_A=
\begin{cases}
1,&\varepsilon_1(A)=\cdots=\varepsilon_r(A)=0,\\
0,&\text{否则}.
\end{cases}
\tag{1}
\]
求和中的条目均属于 \(2\mathbb Z_2\)，故此定义只使用 \(A_i\bmod4\)。

三个域上的可行性完全相同：
\[
\boxed{\ \mathscr S_L(A)\ne\varnothing\iff\chi_A=1.\ }
\tag{2}
\]
全部有限集合的基数为
\[
\boxed{\ |\mathscr R_{L,M}(A)|=\chi_A\,2^r q_L^{(M-1)m}\quad(M\ge2),\ }
\tag{3}
\]
以及
\[
\boxed{
|\mathscr C_{L,M}(A)|=
\begin{cases}
q_L^s,&M=2,\\
\chi_A\,2^r q_L^{(M-1)m+d},&M\ge3.
\end{cases}}
\tag{4}
\]
因此，\(\mathscr R_{L,M}\) 为空当且仅当 \(\chi_A=0\)；\(\mathscr C_{L,2}\) 总不为空，而 \(M\ge3\) 时 \(\mathscr C_{L,M}\) 为空当且仅当 \(\chi_A=0\)。

还有一个统一的、可直接核验的提升判准。给定
\(\bar U\in\mathscr C_{L,M}(A)\)，任取其条目提升 \(u\in M_d(\mathcal O_L)\)，则
\[
\boxed{
\bar U\in\mathscr R_{L,M}(A)
\iff
\sum_{k=1}^d u_{ka}^2\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le a\le d).
}
\tag{5}
\]
右端与提升的选择无关：改变一列中的条目 \(2^M z\)，其范数改变一个 \(2^{M+1}\mathcal O_L\) 中的量。

下面先证明这些公式，再给出固定点、约化映射与下降结论。

---

由每个 \(A_i\) 可以构造一个规范投影 \(P_i\)。从 \(B_0=A_i\) 开始迭代
\[
B_{t+1}=B_t-(B_t^2-B_t)(2B_t-I)^{-1}.
\tag{6}
\]
因为 \(B_t^2-B_t\equiv0\pmod2\)，而 \(2B_t-I\) 可逆，迭代收敛到对称幂等矩阵 \(P_i\)，且
\[
P_i\equiv E_i\pmod2.
\]
所有迭代项都是相应 \(A_i\) 的收敛函数，所以 \(P_i\) 两两交换，并与全部 \(A_j\) 交换。

交换幂等矩阵 \(P_iP_j\) 在 \(i\ne j\) 时模 \(2\) 为零，因而为零。这里使用的简单事实是：若幂等矩阵 \(T\in2M_d(\mathcal O_L)\)，则
\(T=T^k\in2^kM_d(\mathcal O_L)\) 对所有 \(k\) 成立，故 \(T=0\)。同理，
\[
P_iP_j=0\ (i\ne j),\qquad \sum_iP_i=I.
\tag{7}
\]

令 \(X_i\) 为 \(\operatorname{im}P_i\) 的图形基，其 \(I_i\)-坐标块恰为 \(I_{n_i}\)；具体可取
\[
X_i=P_i[:,I_i]\bigl(P_i[I_i,I_i]\bigr)^{-1}.
\]
把这些列依次拼成 \(X\)。则
\[
X\equiv I\pmod2,\qquad
P_iX=XE_i,\qquad
X^{\mathsf T}X=\operatorname{diag}(G_1,\ldots,G_r),
\tag{8}
\]
其中
\[
G_i=X_i^{\mathsf T}X_i=I_{n_i}+4B_i,\qquad
B_i=\sum_{j\ne i}(X_{ji}/2)^{\mathsf T}(X_{ji}/2).
\tag{9}
\]
并且
\[
X_{ji}\equiv A_i[I_j,I_i]\pmod4\quad(j\ne i).
\tag{10}
\]
例如，由 \(P_i^2=P_i\) 可先得 \(P_i[I_i,I_i]\equiv I\pmod4\)，再由
\([P_i,A_i]=0\) 得到 (10)。于是
\[
\operatorname{tr}B_i\equiv\varepsilon_i(A)\pmod2.
\tag{11}
\]

这个分解对有限精度的解也具有唯一性。事实上，若 \(U\) 是真正解，或是模 \(2^M\) 的解，置
\[
Q_i=UE_iU^{\mathsf T}.
\]
则 \(Q_i\) 是与全部 \(A_j\)、因而与全部 \(P_j\) 交换的幂等矩阵，且
\(Q_i\equiv E_i\pmod2\)。对 \(i\ne j\)，幂等矩阵 \(P_iQ_j\) 模 \(2\) 为零，所以为零；在有限商环上，同一论证使用 \(2\) 的幂零性。因此 \(Q_i=P_i\)。

所以，在真正解和有限精度解两种情况下，分块条件都等价于
\[
U=X\operatorname{diag}(V_1,\ldots,V_r),\qquad V_i\equiv I\pmod2,
\tag{12}
\]
而正交条件分别成为
\[
V_i^{\mathsf T}G_iV_i=I
\quad\text{或}\quad
V_i^{\mathsf T}G_iV_i\equiv I\pmod{2^M}.
\tag{13}
\]

我们将反复使用以下提升事实：

> 若 \(H\) 是 \(\mathcal O_L\) 上的对称矩阵，\(M\ge2\)，并且
> \[
> H\equiv I\pmod{2^M},\qquad H_{aa}\equiv1\pmod{2^{M+1}},
> \]
> 则存在 \(Z\equiv I\pmod{2^M}\)，使 \(Z^{\mathsf T}HZ=I\)。

证明如下。使用单位主元作 Gram–Schmidt 消元，可用一个模 \(2^M\) 为 \(I\) 的矩阵把 \(H\) 化成对角阵
\(\operatorname{diag}(h_a)\)。消元对对角条目的改变属于 \(2^{2M}\mathcal O_L\)，所以
\(h_a\in1+2^{M+1}\mathcal O_L\)。每个 \(h_a\) 都有平方根
\(z_a\in1+2^M\mathcal O_L\)，再作对角缩放即可。

这里使用的 Hensel 引理形式是：在完备离散赋值域上，若
\[
v(f(a))>2v(f'(a)),
\]
则存在根 \(b\)，且
\(v(b-a)\ge v(f(a))-v(f'(a))\)。取 \(f(T)=T^2-h_a\)、\(a=1\)。若
\(e=v(2)\)，则
\[
v(1-h_a)\ge(M+1)e>2e,
\]
故上述结论适用于三个域，并给出 \(z_a-1\in2^M\mathcal O_L\)。

先证明可行性的必要性；事实上，存在模 \(8\) 的解已足够。对一块写
\(V=I+2T\)，并在 \(\mathcal O_L/2\mathcal O_L\) 中记其像为 \(t\)。由 (13) 模 \(4\) 得
\(t^{\mathsf T}=t\)，由对角范数模 \(8\) 得
\[
(B_i)_{aa}+t_{aa}+\sum_k t_{ka}^2=0.
\tag{14}
\]
对 \(a\) 求和，得到
\[
\operatorname{tr}B_i+\sum_a(t_{aa}+t_{aa}^2)=0.
\tag{15}
\]
在基域上，\(t_{aa}+t_{aa}^2=0\)。在两个扩域上，
\[
\mathcal O_\mu/2\mathcal O_\mu
=\mathbb F_2[\epsilon]/(\epsilon^2),\qquad
\epsilon=
\begin{cases}
1+\theta_{-1},&\mu=-1,\\
\theta_2,&\mu=2.
\end{cases}
\tag{16}
\]
若 \(t=x+\epsilon y\)，则 \(t+t^2=\epsilon y\)。所以 (15) 的常数项仍强制
\(\operatorname{tr}B_i=0\) 于 \(\mathbb F_2\) 中。结合 (11)，得到必要性。

反过来，假设每个 \(\operatorname{tr}B_i\) 都为偶数。完全图的边到顶点次数的映射
\[
\mathbb F_2^{\binom n2}\longrightarrow\mathbb F_2^n
\]
的像恰为坐标和为零的向量。因此，可选一个对称的整数矩阵 \(T_i\)，使
\[
\sum_{k\ne a}(T_i)_{ka}\equiv(B_i)_{aa}\pmod2.
\]
令 \(V_i=I+2T_i\)。则
\(V_i^{\mathsf T}G_iV_i\equiv I\pmod4\)，且其对角条目模 \(8\) 为 \(1\)。应用上述提升事实，得到有理整数环上的真正解 \(U_0\in\mathscr S_F(A)\)。这证明 (2)，并给出构造 \(U_0\) 的收敛算法。

可行时，所有真正解具体为
\[
\boxed{
\mathscr S_L(A)=
U_0\left\{
\operatorname{diag}(V_i):
V_i^{\mathsf T}V_i=I,\quad V_i\equiv I\pmod2
\right\}.
}
\tag{17}
\]

同一个提升事实证明 (5)。必要性已显然。若右端成立，由规范分块可先把 \(u\) 改成
\[
u'=X\operatorname{diag}(V_i)\equiv u\pmod{2^M}.
\]
其各块 Gram 矩阵模 \(2^M\) 为 \(I\)，对角条目模 \(2^{M+1}\) 为 \(1\)。逐块应用提升事实，便得到与 \(u\) 同类的真正解。

为计算基数，只须在 (17) 中计算每块的正交群。模 \(4\) 写
\[
V=I+2T.
\]
有限正交条件恰为 \(t^{\mathsf T}=t\)，故有限解数为
\(q_L^{n(n+1)/2}\)。真正解的模 \(4\) 像还须满足
\[
t_{aa}+\sum_k t_{ka}^2=0.
\tag{18}
\]
在 \(\mathbb F_2\) 上，对角有 \(n\) 个自由变量，非对角变量的次数须全为零；后者有 \(n-1\) 个独立条件。因此解数为
\[
2^{n+\binom n2-(n-1)}=2^{\binom n2+1}.
\]
在 (16) 的环上，写 \(t=x+\epsilon y\)。条件变为：
\(x\) 的非对角次数为零，且 \(y_{aa}=0\)。于是解数为
\[
2^{2\binom n2+1}=2q_L^{\binom n2}.
\]
两种情形统一为：每块的真正模 \(4\) 像有 \(2q_L^{\binom n2}\) 个元素。

对 \(M\ge2\)，精确正交群中模 \(2^M\) 为 \(I\) 的部分由 Cayley 变换
\[
V=(I-H)(I+H)^{-1},\qquad
H^{\mathsf T}=-H,\quad H\in2^{M-1}M_n(\mathcal O_L)
\tag{19}
\]
参数化。模 \(2^{M+1}\) 有 \(V\equiv I-2H\)，故每升一层，真正约化像增加因子
\(q_L^{\binom n2}\)。这证明 (3)。

最后，对模 \(2^M\) 的有限正交群定义范数缺陷
\[
\nu_M(V)=
\left(\frac{(V^{\mathsf T}V-I)_{aa}}{2^M}\pmod2\right)_a.
\tag{20}
\]
这是到 \((\mathcal O_L/2)^n\) 的群同态，核由 (5) 给出。对 \(M\ge3\)，对角矩阵
\[
\operatorname{diag}(1+2^{M-1}a_1,\ldots,1+2^{M-1}a_n)
\]
的缺陷为 \((a_1,\ldots,a_n)\bmod2\)，所以 (20) 满射。这给出因子 \(q_L^n\)，证明 (4)。

---

现在描述伽罗瓦固定点。以下把 \(\mathbb F_2\) 矩阵按标准块嵌入，记
\[
\mathcal T=\bigoplus_i\operatorname{Sym}_{n_i}(\mathbb F_2),\qquad
\mathcal A=\bigoplus_i\operatorname{Alt}_{n_i}(\mathbb F_2).
\]
这里 \(\operatorname{Alt}\) 表示对称且对角为零的矩阵；因此
\[
\dim\mathcal T=s,\qquad \dim\mathcal A=m.
\]
对 \(B\in\mathcal A\)，定义
\[
(\deg B)_a=\sum_k B_{ka}\in\mathbb F_2.
\tag{21}
\]

固定环中的矩阵有唯一表示
\[
\bar U=V+2^{M-1}\theta_\mu B,
\tag{22}
\]
其中 \(V\) 是模 \(2^M\) 的有理矩阵，\(B\in M_d(\mathbb F_2)\)。因为对一个条目
\(a+b\theta_\mu\)，固定条件正是 \(2b\equiv0\pmod{2^M}\)。

有限解的固定点始终有如下描述：
\[
\boxed{
\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
=
\left\{
V+2^{M-1}\theta_\mu B:
V\in\mathscr C_{F,M}(A),\ B\in\mathcal T
\right\}.
}
\tag{23}
\]
真正解约化像的固定点，在 \(M\ge3\)，以及在 \((\mu,M)=(2,2)\) 时，为
\[
\boxed{
\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
=
\left\{
V+2^{M-1}\theta_\mu B:
V\in\mathscr R_{F,M}(A),\ B\in\mathcal A
\right\}.
}
\tag{24}
\]

唯一的例外是 \(K_{-1}\)、\(M=2\)。对
\(V\in\mathscr C_{F,2}(A)\)，定义可核验的向量
\[
\eta(V)_a=\frac{\sum_kV_{ka}^2-1}{4}\pmod2.
\tag{25}
\]
则
\[
\boxed{
\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}
=
\left\{
V+2\theta_{-1}B:
V\in\mathscr C_{F,2}(A),\
B\in\mathcal A,\
\eta(V)=\deg B
\right\}.
}
\tag{26}
\]
所以在这个例外中，固定矩阵类的有理部分 \(V\) 本身可能不属于
\(\mathscr R_{F,2}(A)\)。

这些公式也精确说明了与基域集合的关系：取 \(B=0\) 就分别得到基域上的
\(\mathscr C_{F,M}\)、\(\mathscr R_{F,M}\)，并且它们正是固定点集中所有有理矩阵类。

证明 (23)—(26) 只需展开 (22)。其正交条件强制 \(B^{\mathsf T}=B\)；分块条件的最高位只涉及 \(A_i\bmod2=E_i\)，从而强制 \(B\) 块对角。这给出 (23)。进一步，令
\[
\eta_M(V)_a=\frac{\sum_kV_{ka}^2-1}{2^M}\pmod2.
\]
由 (5)，属于真正约化像的条件恰为
\[
\eta_M(V)_a+\theta_\mu B_{aa}
+2^{M-2}\mu\sum_k B_{ka}=0
\quad\text{于 }\mathcal O_\mu/2\mathcal O_\mu.
\tag{27}
\]
当 \(M\ge3\) 或 \(\mu=2\) 时，最后一项为零，故 \(B_{aa}=0\)、\(\eta_M(V)=0\)，得到 (24)。当 \(M=2,\mu=-1\) 时，得到 \(B_{aa}=0\) 和
\(\eta(V)=\deg B\)，即 (26)。

固定点数如下：
\[
\boxed{
|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}|
=\chi_A\,2^{Mm+r}\qquad(M\ge2),
}
\tag{28}
\]
\[
\boxed{
|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}|=
\begin{cases}
2^{2s},&M=2,\\
\chi_A\,2^{Mm+2d+r},&M\ge3.
\end{cases}}
\tag{29}
\]
在 \(M=2\) 时，所有模 \(4\) 为 \(I\) 的矩阵类都被 \(\sigma_\mu\) 固定，因此两个集合的伽罗瓦作用都平凡；这也验证了 (28) 在例外情形中的计数。

所有轨道的长度为 \(1\) 或 \(2\)，单点轨道就是上述固定点。轨道总数为
\[
\boxed{
\#\bigl(\mathscr R_{K_\mu,M}/\langle\sigma_\mu\rangle\bigr)
=
\chi_A\,2^{r-1}
\left(2^{2(M-1)m}+2^{Mm}\right),
}
\tag{30}
\]
以及
\[
\boxed{
\#\bigl(\mathscr C_{K_\mu,M}/\langle\sigma_\mu\rangle\bigr)
=
\begin{cases}
2^{2s},&M=2,\\
\chi_A\,2^{r+2d-1}
\left(2^{2(M-1)m}+2^{Mm}\right),&M\ge3.
\end{cases}}
\tag{31}
\]
双点轨道数相应为“总点数减固定点数”除以 \(2\)。

---

精度约化的全部信息可以列在一个表中。表中的基域集合均按题意自然嵌入扩域集合。

| 约化映射，\(M\ge2\) | 约化像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{L,M+1}\to\mathscr R_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^m\) |
| \(\mathscr C_{L,M+1}\to\mathscr C_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^s\) |
| \(\mathscr R_{K_\mu,M+1}^{\sigma_\mu}\to\mathscr R_{K_\mu,M}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(4^m\) |
| \(\mathscr C_{K_\mu,M+1}^{\sigma_\mu}\to\mathscr C_{K_\mu,M}^{\sigma_\mu}\) | \(\mathscr R_{F,M}\) | \(4^s\) |

若 \(\chi_A=0\)，这些映射的定义域全部为空，因而没有非空纤维。

第一行由真正解的定义及 (19) 得到。第二行由 (5) 得到：多一层有限正交性正好提供所需的对角范数精度。对于后两行，下一层固定点的最高位项是
\(2^M\theta_\mu B\)，约化后消失；下一层精度至少为 \(3\)，所以 (24)、(23) 及第二行分别给出像
\(\mathscr R_{F,M}\)。反向包含可用基域上的真正解提升实现。

可行时，选定有理 \(U_0\) 后，这些集合都是相应群的陪集，约化映射成为群同态。因此所有非空纤维等大；将 (3)、(4)、(28)、(29) 相除，恰得表中的大小。

真正解的固定点满足
\[
\boxed{\ \mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A).\ }
\tag{32}
\]
这是因为 \(\mathcal O_\mu^{\sigma_\mu}=\mathbb Z_2\)，且
\(2\mathcal O_\mu\cap\mathbb Z_2=2\mathbb Z_2\)。

因而，对固定矩阵类 (22)：

- 若它属于 \(\mathscr R_{K_\mu,M}^{\sigma_\mu}\)，则它能提升为一个真正的 \(\sigma_\mu\)-固定解，当且仅当 \(B=0\)。
- 若它属于 \(\mathscr C_{K_\mu,M}^{\sigma_\mu}\)，则它能如此提升，当且仅当
  \(B=0\) 且 \(V\in\mathscr R_{F,M}\)；后一个条件由 (5) 核验。

这也恰好刻画了哪些固定类能成为一条无限逐层相容的固定类序列在精度 \(M\) 的分量。事实上，表中说明：有一个下一层固定提升，已经等价于属于
\(\mathscr R_{F,M}\)；而基域真正解提供全部更高层。因此有自然双射
\[
\varprojlim_{M\ge2}\mathscr R_{K_\mu,M}^{\sigma_\mu}
\;\cong\;
\varprojlim_{M\ge2}\mathscr C_{K_\mu,M}^{\sigma_\mu}
\;\cong\;\mathscr S_F(A).
\tag{33}
\]

---

第 3 问的最优统一答案为
\[
\boxed{
N_{\max}=
\begin{cases}
M,&n_1=\cdots=n_r=1,\\
M-1,&\max_i n_i\ge2.
\end{cases}}
\tag{34}
\]
它与 \(\mu\) 无关。

对给定的 \(A,U\)，把真正解唯一写成
\[
U=P+\theta_\mu Q,\qquad P,Q\in M_d(\mathbb Z_2).
\]
题设的有限固定条件等价于 \(Q\in2^{M-1}M_d(\mathbb Z_2)\)。能取满精度
\(N=M\) 的必要充分条件为
\[
\boxed{
Q\in2^M M_d(\mathbb Z_2)
\iff
\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}.
}
\tag{35}
\]
确实，若能与有理 \(W\) 模 \(2^M\) 相同，显然其 \(\theta_\mu\)-系数须被 \(2^M\) 整除。反之，若该系数消失，则 \(U\bmod2^M\) 是一个有理的真正约化类，故由前述交集关系属于
\(\mathscr R_{F,M}\)。

证明统一下界：当 \(M\ge3\)，由 (24)，固定的真正约化类为
\[
V+2^{M-1}\theta_\mu B,\qquad V\in\mathscr R_{F,M}.
\]
取提升 \(V\) 的有理真正解即可得到精度 \(M-1\)。当 \(M=2\) 时，扩域真正解的存在保证 \(\chi_A=1\)，故有理真正解存在；两者均模 \(2\) 为 \(I\)，得到精度 \(1=M-1\)。

如果全部 \(n_i=1\)，由 (17)，每块的精确正交群只有 \(\{1,-1\}\)。因此实际上
\[
\mathscr S_{K_\mu}(A)=\mathscr S_F(A),
\tag{36}
\]
所以能精确下降。

只要某块秩至少为 \(2\)，下面的统一构造就在任意 \(M\ge2\) 给出最优性反例。取
\[
A_i=E_i,
\]
并在该块的一个二维坐标平面上放置矩阵
\[
R(h)=\frac1{1+h^2}
\begin{pmatrix}
1-h^2&-2h\\
2h&1-h^2
\end{pmatrix},
\tag{37}
\]
其余坐标取恒等。令
\[
\rho_\mu=
\begin{cases}
1+\theta_{-1},&\mu=-1,\\
\theta_2,&\mu=2,
\end{cases}
\qquad h=2^{M-2}\rho_\mu.
\tag{38}
\]
在两种情况下，\(h^2\in2\mathcal O_\mu\)，所以分母是单位，
\(R(h)^{\mathsf T}R(h)=I\)，且 \(R(h)\equiv I\pmod2\)。

令
\[
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]
则 \(R(h)=(I-hJ)(I+hJ)^{-1}\)。两个 Cayley 变换之差是
\(2(h-k)\) 乘以一个整矩阵，而
\[
\sigma_\mu(h)-h=-2^{M-1}\theta_\mu.
\]
故
\[
\sigma_\mu(R(h))\equiv R(h)\pmod{2^M\mathcal O_\mu}.
\]
另一方面，
\[
\frac{2h/(1+h^2)}{2^{M-1}}\equiv\rho_\mu\pmod{2\mathcal O_\mu}.
\]
右端的 \(\theta_\mu\)-系数为 \(1\)，所以某个非对角条目的
\(\theta_\mu\)-系数恰被 \(2^{M-1}\)、而不被 \(2^M\) 整除。这个真正解不能与任何有理矩阵模 \(2^M\) 相同。构造 (37)—(38) 同时适用于两种扩张和全部精度，证明了 (34) 的最优性。

最后列出其余提升失败现象的实际例子。

取 \(r=2,n_1=n_2=1\)，
\[
A_1=\begin{pmatrix}1&2\\2&0\end{pmatrix},
\qquad
A_2=I-A_1.
\tag{39}
\]
它们满足全部输入条件，且 \(\varepsilon_1=\varepsilon_2=1\)。所以三个域上的真正解均不存在，模 \(8\) 的有限解也不存在。但
\[
\bar U=\begin{pmatrix}1&2\\2&1\end{pmatrix}\pmod4
\tag{40}
\]
属于三个域的 \(\mathscr C_{L,2}\)：其 Gram 矩阵为
\(\begin{psmallmatrix}5&4\\4&5\end{psmallmatrix}\)，且共轭后的两矩阵模 \(4\) 都是对角阵。它的列范数为 \(5\)，故不属于任何 \(\mathscr R_{L,2}\)。该例可嵌入任意两个不同的块，表明 \(r\ge2\) 时可行性确实可能失败；\(r=1\) 时判准自动成立。

在可行输入 \(A_i=E_i\) 下，若某块至少二维，(40) 放在该块内便给出
\(\mathscr C_{F,2}\setminus\mathscr R_{F,2}\)。对任意块秩、任意 \(M\ge3\)，
\[
\operatorname{diag}(1+2^{M-1},1,\ldots,1)\pmod{2^M}
\tag{41}
\]
属于每个 \(\mathscr C_{L,M}\)，但其首列范数缺陷除以 \(2^M\) 为奇数，所以不属于
\(\mathscr R_{L,M}\)。

对任意块秩、任意 \(\mu\)、任意 \(M\ge2\)，
\[
\operatorname{diag}(1+2^{M-1}\theta_\mu,1,\ldots,1)\pmod{2^M}
\tag{42}
\]
属于 \(\mathscr C_{K_\mu,M}^{\sigma_\mu}\)，却既不是有理矩阵类，也不属于
\(\mathscr R_{K_\mu,M}\)。其范数缺陷除以 \(2^M\) 模 \(2\) 为
\(\theta_\mu+2^{M-2}\mu\ne0\)。这给出了固定有限解不能提升为真正解、不能进入相容固定序列的统一例子。

构造 (37)—(38) 则给出固定的真正约化类不能提升为下一层固定类的统一例子。特别地，在 \(\mu=-1,M=2\) 时，取 \(h=1+\theta_{-1}\)，得到
\[
R(h)\equiv
\begin{pmatrix}
1&2+2\theta_{-1}\\
2+2\theta_{-1}&1
\end{pmatrix}\pmod4.
\]
它的有理部分正是 (40)，列范数为 \(5\bmod8\)，故不属于
\(\mathscr R_{F,2}\)；而取
\(B=\begin{psmallmatrix}0&1\\1&0\end{psmallmatrix}\)，恰有
\(\eta(V)=(1,1)=\deg B\)，实际实现了 (26) 中的特殊现象。