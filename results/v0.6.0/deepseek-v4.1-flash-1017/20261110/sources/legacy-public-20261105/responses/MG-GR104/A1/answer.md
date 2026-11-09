以下均按“环同态保 \(1\)”理解；零环中 \(0=1\)。

---

## S1　单层提升

**结论：** 对每个幂等元 \(e\in S\)，存在唯一的幂等元 \(\widetilde e\in R\) 使 \(q(\widetilde e)=e\)。构造不使用 \(2^{-1}\)，也不需要核有统一的幂零指数。

设
\[
I=\ker q.
\]
任取 \(x\in R\) 使 \(q(x)=e\)。则
\[
q(x^2-x)=e^2-e=0,
\]
故
\[
a=x^2-x\in I
\]
是幂零元。设 \(a^N=0\)。

### 存在性

令
\[
x_0=x,\qquad x_{m+1}=3x_m^2-2x_m^3.
\]
再令
\[
a_m=x_m^2-x_m.
\]
直接展开可得恒等式
\[
a_{m+1}=a_m^2(4a_m-3).
\]
因此若 \(a_m^{M}=0\)，则
\[
a_{m+1}^{\lceil M/2\rceil}
=\bigl(a_m^2(4a_m-3)\bigr)^{\lceil M/2\rceil}=0.
\]
于是每迭代一次，幂零指数的上界至少减半；有限步后得到某个 \(a_m=0\)。此时 \(x_m^2=x_m\)，即为幂等元。

另一方面，由 \(q(x)=e\) 且 \(e^2=e\)，有
\[
q(x_{m+1})=3e^2-2e^3=e,
\]
故所有 \(x_m\) 都是 \(e\) 的提升。取最终的幂等元
\[
\widetilde e=x_m
\]
即可。

上述迭代只使用整数系数 \(3,-2\)，所以不需要 \(2\) 可逆；消去过程只依赖所选元素 \(a\) 自己的幂零指数，不要求 \(\ker q\) 有统一幂零指数。

### 唯一性

若 \(u,v\in R\) 都是幂等元且 \(q(u)=q(v)=e\)，令
\[
d=u-v\in I.
\]
于是 \(d\) 幂零。由于 \(R\) 交换且 \(u,v\) 幂等，
\[
d^3=(u-v)^3=u-v=d.
\]
若 \(d^N=0\)，则 \(d=d^{3^k}\)。取 \(k\) 足够大使得 \(3^k\ge N\)，便得
\[
d=d^{3^k}=0.
\]
故 \(u=v\)。唯一性得证。

---

## S2　任意有向逆系

采用如下逆系约定：若 \(i\ge j\)，则过渡映射为
\[
\rho_{ij}:R_i\to R_j,
\]
且
\[
p_i\rho_{ij}=p_j.
\]
极限为
\[
L=\left\{(r_i)\in\prod_{i\in I}R_i:\ \rho_{ij}(r_i)=r_j\quad(i\ge j)\right\}.
\]
由于所有同态保 \(1\)，\((1_{R_i})_i\in L\)，故 \(L\) 是含幺子环。

### 1. 构造 \(p:L\to S\)

对 \(r=(r_i)\in L\)，定义
\[
p(r)=p_i(r_i).
\]
需验证与 \(i\) 无关。若 \(i,j\in I\)，由 \(I\) 有向，取 \(k\ge i,j\)。则
\[
p_i(r_i)=p_i\rho_{ki}(r_k)=p_k(r_k),
\]
同理 \(p_j(r_j)=p_k(r_k)\)。故定义良好，且
\[
p(r)=p_i(r_i)
\]
对任意 \(i\) 都相同。

它显然保加法、乘法与 \(1\)，故 \(p:L\to S\) 是含幺环同态。

---

### 2. 有限族幂等元的提升与双射

先用 S1 得一个关键事实。

**引理.** 对每个幂等元 \(e\in S\)，存在唯一的相容幂等族
\[
\widetilde e=(\widetilde e_i)_{i\in I}\in L
\]
使得
\[
p_i(\widetilde e_i)=e\quad(\forall i\in I).
\]

**证明.** 对每个 \(i\)，由 S1，\(R_i\) 中存在唯一的幂等提升 \(\widetilde e_i\in R_i\) 满足 \(p_i(\widetilde e_i)=e\)。

若 \(i\ge j\)，则 \(\rho_{ij}(\widetilde e_i)\) 是 \(R_j\) 中的幂等元，并且
\[
p_j\bigl(\rho_{ij}(\widetilde e_i)\bigr)
=p_i(\widetilde e_i)=e.
\]
由 \(R_j\) 中幂等提升的唯一性，
\[
\rho_{ij}(\widetilde e_i)=\widetilde e_j.
\]
故 \((\widetilde e_i)\) 相容，属于 \(L\)。唯一性由逐分量的唯一性直接得到。∎

现在证明
\[
D_J(p):D_J(L)\longrightarrow D_J(S)
\]
是双射。

先处理一个边界情形。

- 若 \(J=\varnothing\)，按题中定义，
  \[
  D_\varnothing(R)\ne\varnothing
  \iff R=0.
  \]
  若 \(S=0\)，因为 \(p_i:R_i\to 0\) 保 \(1\)，有 \(1_{R_i}\in\ker p_i\)。但 \(\ker p_i\) 逐元幂零，故 \(1_{R_i}\) 幂零，从而 \(R_i=0\)。所以此时所有 \(R_i=0\)，进而 \(L=0\)，双方均为单点集。
  
  若 \(S\ne0\)，则 \(L\ne0\)，因为 \(1_L\) 满足 \(p(1_L)=1_S\ne0\)。于是
  \[
  D_\varnothing(L)=D_\varnothing(S)=\varnothing,
  \]
  仍为双射。

以下设 \(J\ne\varnothing\)。

给定
\[
(e_j)_{j\in J}\in D_J(S).
\]
由引理，对每个 \(j\) 取唯一的相容幂等提升
\[
\widetilde e_j\in L,\qquad p(\widetilde e_j)=e_j.
\]
需证 \((\widetilde e_j)_{j\in J}\in D_J(L)\)。

逐层看。对固定 \(i\)，各 \(\widetilde e_{j,i}\in R_i\) 幂等。若 \(j\ne k\)，则
\[
\widetilde e_{j,i}\widetilde e_{k,i}
\]
仍幂等，因为 \(R_i\) 交换；并且
\[
p_i(\widetilde e_{j,i}\widetilde e_{k,i})
=e_j e_k=0.
\]
而 \(0\) 的唯一幂等提升是 \(0\)，故
\[
\widetilde e_{j,i}\widetilde e_{k,i}=0.
\]
同理
\[
s_i=\sum_{j\in J}\widetilde e_{j,i}
\]
是幂等元，且由正交性，
\[
p_i(s_i)=\sum_j e_j=1.
\]
故 \(s_i\) 是 \(1\in S\) 的幂等提升；而 \(1_{R_i}\) 本身就是一个提升，故唯一性给出 \(s_i=1_{R_i}\)。因此
\[
\sum_j\widetilde e_j=1_L.
\]
于是
\[
(\widetilde e_j)_{j\in J}\in D_J(L).
\]

反之，若
\[
(E_j)_{j\in J}\in D_J(L),
\]
则逐分量 \(E_{j,i}\) 都是 \(e_j=p(E_j)\) 在 \(R_i\) 中的幂等提升，由 S1 的唯一性，\(E_{j,i}=\widetilde e_{j,i}\)。故 \(E_j=\widetilde e_j\)。因此
\[
D_J(p):D_J(L)\to D_J(S)
\]
既满又单，从而是双射。

特别地，取 \(J=\{1,2\}\) 即知：\(S\) 中每个幂等元在 \(L\) 中有唯一的幂等提升。

---

### 3. 分解 \(L\cong\prod_{j\in J}L/(1-\widetilde e_j)L\)

设 \((e_j)_{j\in J}\in D_J(S)\)，对应提升为 \((\widetilde e_j)_{j\in J}\in D_J(L)\)。

先设 \(J\ne\varnothing\)。对每个 \(j\)，置
\[
I_j=(1-\widetilde e_j)L.
\]
定义
\[
\Phi:L\longrightarrow\prod_{j\in J}L/I_j,
\qquad
\Phi(x)=(x+I_j)_{j\in J}.
\]
再定义
\[
\Psi:\prod_{j\in J}L/I_j\longrightarrow L,
\qquad
\Psi\bigl((y_j+I_j)_{j\in J}\bigr)
=\sum_{j\in J}\widetilde e_j y_j.
\]
这个定义与代表元选取无关，因为
\[
\widetilde e_j I_j
=\widetilde e_j(1-\widetilde e_j)L=0.
\]

若 \(i\ne j\)，由于 \(\sum_k\widetilde e_k=1\)，
\[
1-\widetilde e_j=\sum_{k\ne j}\widetilde e_k,
\]
故 \(\widetilde e_i\in I_j\)。于是
\[
\Phi\Psi((y_j+I_j)_j)
=\left(\sum_i \widetilde e_i y_i+I_k\right)_k
=(y_k+I_k)_k,
\]
其中最后一步用到：若 \(i\ne k\)，则 \(\widetilde e_i y_i\in I_k\)，而
\[
\widetilde e_k y_k\equiv y_k\pmod{I_k}.
\]
另一方面，
\[
\Psi\Phi(x)=\sum_j\widetilde e_j x
=x\sum_j\widetilde e_j=x.
\]
故 \(\Phi\) 与 \(\Psi\) 互逆，得到环同构
\[
L\cong\prod_{j\in J}\frac{L}{(1-\widetilde e_j)L}.
\]

若 \(J=\varnothing\)，如上面所述，只有 \(S=0\) 时才存在空提升；此时 \(L=0\)，而空积也是零环，公式同样成立。

---

### 4. 自然性

设有另一同指标逆系
\[
(R'_i,\rho'_{ij},p'_i:S')
\]
以及相容环同态 \(u_i:R_i\to R'_i\)、\(u:S\to S'\)，满足
\[
u_i\rho_{ij}=\rho'_{ij}u_j,
\qquad
p'_i u_i=u p_i.
\]
定义
\[
u_L:L\to L',\qquad
u_L((r_i))=(u_i(r_i)).
\]
若 \(r=(r_i)\in L\)，则
\[
\rho'_{ij}(u_i(r_i))
=u_j(\rho_{ij}(r_i))
=u_j(r_j),
\]
故 \(u_L(r)\in L'\)。且
\[
p'(u_L(r))
=p'_i(u_i(r_i))
=u(p_i(r_i))
=u(p(r)).
\]
所以
\[
u\circ p=p'\circ u_L.
\]

再验证幂等族双射的自然性。若 \(e\in D_J(S)\)，其唯一提升为 \(\widetilde e\in D_J(L)\)，则 \(u_L(\widetilde e)\in D_J(L')\) 是 \(u(e)\in D_J(S')\) 的幂等提升。由唯一性，
\[
u_L(\widetilde e)=\widetilde{u(e)}.
\]
因此下述图表交换：
\[
\begin{array}{ccc}
D_J(L) & \xrightarrow{p_J} & D_J(S)\\[2mm]
{\scriptstyle u_L}\downarrow & & \downarrow{\scriptstyle D_J(u)}\\[2mm]
D_J(L') & \xrightarrow{p'_J} & D_J(S')
\end{array}
\]
其中 \(D_J(u)((e_j))=(u(e_j))\)。

最后看分解的自然性。令
\[
\widetilde e'_j=u_L(\widetilde e_j),
\qquad
I_j=(1-\widetilde e_j)L,\quad
I'_j=(1-\widetilde e'_j)L'.
\]
由于
\[
u_L(1-\widetilde e_j)=1-\widetilde e'_j,
\]
有 \(u_L(I_j)\subseteq I'_j\)，故诱导出
\[
\overline u_j:L/I_j\to L'/I'_j,
\qquad
\overline u_j(x+I_j)=u_L(x)+I'_j.
\]
于是由分解映射 \(\Phi_{\widetilde e}\)、\(\Phi_{\widetilde e'}\) 的定义，
\[
\Phi_{\widetilde e'}\circ u_L
=
\left(\prod_j\overline u_j\right)\circ \Phi_{\widetilde e}.
\]
即分解同构在相容映射下自然。

> 注意：S2 并没有断言 \(p:L\to S\) 满射，也没有断言 \(\ker p\) 逐元幂零。前者见 S5，后者见 S3；二者均不与上面的幂等提升结论矛盾。

---

## S3　极限核

这里
\[
R_n=k[t]/(t^{n+1}),\qquad S=k,
\]
过渡为自然约化，\(p_n\) 取常数项。相容元组 \((f_n)_{n\ge1}\) 的下标与截断相容，故可等价地写成一列系数
\[
(a_0,a_1,a_2,\dots)\in k^{\mathbb N}.
\]
因此
\[
L\cong k[[t]],
\]
并且
\[
p:L\to k
\]
就是常数项映射：
\[
p\left(\sum_{r\ge0}a_r t^r\right)=a_0.
\]

于是
\[
\ker(p:L\to k)=t\,k[[t]].
\]
元素 \(t\in\ker p\) 不幂零，因为
\[
t^m\ne0\qquad(\forall m\ge1).
\]
更一般地，\(k[[t]]\) 是整环，故其中非零元都不幂零；所以 \(\ker p\) 中只有 \(0\) 幂零。因此答案是：

\[
\boxed{\ker(p:L\to k)\text{ 并非每个元素都幂零。}}
\]

这与 S2 的结论一致。原因有两层：

1. S2 的前提只要求每个有限层核
   \[
   \ker p_n=(t)\subset k[t]/(t^{n+1})
   \]
   中元素逐个幂零。事实上在该层中
   \[
   t^{n+1}=0,
   \]
   所以该条件成立。
2. S2 的结论是极限上的幂等提升及 \(D_J\) 双射，从未断言极限核
   \[
   \ker(p:L\to k)
   \]
   幂零。

此外，这里 S2 的结论确实成立：\(k[[t]]\) 是局部环，幂等元只有 \(0,1\)，故对每个非空有限 \(J\)，
\[
D_J(k[[t]])\cong D_J(k),
\]
两者都是由“恰好一个分量为 \(1\)，其余为 \(0\)”给出的 \(|J|\) 个元组。因此 S3 正好说明：**有限层核幂零不能推出极限核幂零，但这不影响 S2 的幂等提升结论。**

---

## S4　相容元素的满射性

设
\[
\rho_n:R_{n+1}\to R_n
\]
均满射，且
\[
p_n\rho_n=p_{n+1}.
\]
极限为
\[
L=\left\{(r_n)_{n\ge1}:\rho_n(r_{n+1})=r_n\right\}.
\]

任取 \(s\in S\)。由于 \(p_1\) 满射，可取
\[
r_1\in R_1,\qquad p_1(r_1)=s.
\]
假设已选好 \(r_n\in R_n\)。由于 \(\rho_n:R_{n+1}\to R_n\) 满射，可取
\[
r_{n+1}\in R_{n+1},\qquad
\rho_n(r_{n+1})=r_n.
\]
于是
\[
p_{n+1}(r_{n+1})
=p_n(\rho_n(r_{n+1}))
=p_n(r_n)
=s.
\]
归纳地得到序列 \((r_n)_{n\ge1}\)，满足
\[
\rho_n(r_{n+1})=r_n\quad(\forall n),
\]
故 \((r_n)\in L\)，且
\[
p((r_n))=p_n(r_n)=s.
\]
所以 \(p:L\to S\) 满射。

这里不需要交换性，也不需要核幂零；只用了所有 \(\rho_n,p_n\) 的满射性以及可数递归选择（ZFC 足够）。

---

## S5　逐层增广

**结论：不必满射。**

反例如下。取特征 \(0\) 的域 \(K\)，例如 \(K=\mathbb Q\)，令
\[
S=K[X].
\]
对 \(n\ge1\)，令
\[
R_n=S[\varepsilon_n]/(\varepsilon_n^2)
=K[X,\varepsilon_n]/(\varepsilon_n^2),
\]
并定义
\[
p_n:R_n\to S,\qquad
p_n(f+g\varepsilon_n)=f.
\]
于是
\[
\ker p_n=(\varepsilon_n),\qquad \varepsilon_n^2=0,
\]
故每层核中元素逐个幂零。

定义过渡映射
\[
\rho_n:R_{n+1}\to R_n,
\qquad
\rho_n(f+g\varepsilon_{n+1})
=
f+(Xg+f')\varepsilon_n,
\]
其中 \(f'\) 表示 \(\frac{d}{dX}f\)。

先验证 \(\rho_n\) 是含幺环同态。对 \(f,g,h,k\in S\)，在 \(R_{n+1}\) 中
\[
(f+g\varepsilon)(h+k\varepsilon)
=fh+(fk+gh)\varepsilon,
\]
其中 \(\varepsilon=\varepsilon_{n+1}\)。于是
\[
\begin{aligned}
\rho_n\bigl((f+g\varepsilon)(h+k\varepsilon)\bigr)
&=fh+\bigl[X(fk+gh)+(fh)'\bigr]\varepsilon_n\\
&=fh+\bigl[Xfk+Xgh+f'h+fh'\bigr]\varepsilon_n.
\end{aligned}
\]
另一方面，
\[
\rho_n(f+g\varepsilon)=f+(Xg+f')\varepsilon_n,
\]
\[
\rho_n(h+k\varepsilon)=h+(Xk+h')\varepsilon_n,
\]
二者相乘得
\[
fh+\bigl[f(Xk+h')+(Xg+f')h\bigr]\varepsilon_n,
\]
即
\[
fh+\bigl[Xfk+fh'+Xgh+f'h\bigr]\varepsilon_n,
\]
二者相等。且 \(\rho_n(1)=1\)。故 \(\rho_n\) 是含幺环同态。

同时
\[
p_n\rho_n(f+g\varepsilon_{n+1})
=p_n\bigl(f+(Xg+f')\varepsilon_n\bigr)
=f
=p_{n+1}(f+g\varepsilon_{n+1}),
\]
故与增广相容。对 \(i>j\) 用相邻过渡复合定义 \(\rho_{ij}\)，便得到完整的逆系。

下面证明 \(p:L\to S\) 不满。

假设元素 \(X\in S=K[X]\) 有相容提升
\[
(r_n)_{n\ge1}\in L,\qquad p(r_n)=X\quad(\forall n).
\]
写成
\[
r_n=f_n+g_n\varepsilon_n.
\]
由相容性，
\[
f_n=f_{n+1}
\]
且
\[
g_n=Xg_{n+1}+f_n'.
\]
由于 \(p(r_n)=f_n=X\)，得到
\[
g_n=Xg_{n+1}+1\qquad(\forall n\ge1).
\]
反复迭代：
\[
g_1
=1+X+\cdots+X^{n-1}+X^n g_{n+1}
\qquad(\forall n\ge1).
\]
设 \(d=\deg g_1\)（若 \(g_1=0\)，则第一条方程 \(0=1+Xg_2\) 已经矛盾）。取 \(n>d+1\)。则左边 \(g_1\) 中 \(X^{n-1}\) 的系数为 \(0\)；右边和式
\[
1+X+\cdots+X^{n-1}
\]
中 \(X^{n-1}\) 的系数为 \(1\)，而 \(X^n g_{n+1}\) 的次数至少为 \(n\)，不可能贡献次数 \(n-1\)。矛盾。

故 \(X\) 不属于 \(p(L)\)，所以
\[
\boxed{p:L\to S\text{ 不必满射。}}
\]

事实上，本例中 \(\ker p=0\)：若 \(f=0\)，则 \(g_n=Xg_{n+1}\)。于是 \(g_1=X^n g_{n+1}\) 对所有 \(n\) 成立，故 \(g_1=0\)，再逐次得所有 \(g_n=0\)。所以这个反例连“极限核逐元幂零”都满足，却仍然不能保证 \(p\) 满射。

---

## S6　乘法结构与唯一性

### 1. 核平方零时，非交换情形下幂等提升不唯一

取域 \(F\)（例如 \(F=\mathbb F_2\)），令
\[
R=T_2(F)
=\left\{
\begin{pmatrix}
a&b\\
0&c
\end{pmatrix}:a,b,c\in F
\right\},
\]
\[
S=F\times F,
\]
并定义
\[
q:R\to S,
\qquad
q\begin{pmatrix}
a&b\\
0&c
\end{pmatrix}=(a,c).
\]
则 \(q\) 是含幺环满射，且
\[
\ker q
=
\left\{
\begin{pmatrix}
0&b\\
0&0
\end{pmatrix}:b\in F
\right\}.
\]
若 \(N_1,N_2\in\ker q\)，则 \(N_1N_2=0\)，故
\[
(\ker q)^2=0.
\]

考虑幂等元
\[
\overline e=(1,0)\in S.
\]
它在 \(R\) 中的提升为
\[
E_b=
\begin{pmatrix}
1&b\\
0&0
\end{pmatrix},
\qquad b\in F.
\]
直接计算：
\[
E_b^2=
\begin{pmatrix}
1&b\\
0&0
\end{pmatrix}^2
=
\begin{pmatrix}
1&b\\
0&0
\end{pmatrix}
=E_b,
\]
且
\[
q(E_b)=(1,0)=\overline e.
\]
当 \(b\) 取不同值时得到不同提升。例如在 \(F=\mathbb F_2\) 中，\(E_0\ne E_1\)。

因此：

\[
\boxed{\text{若环不交换，即使 }\ker q\text{ 平方零，幂等提升也不必唯一。}}
\]

S1 中交换性对唯一性是实质性的。

---

### 2. S1–S5 中诸性质之间的关系

为便于表述，记：

- \(E\)：元素提升，即增广 \(q\) 或 \(p\) 满射；
- \(I\)：幂等提升，即 \(S\) 中每个幂等元至少有一个幂等提升；
- \(U\)：幂等提升唯一，即每个幂等元至多有一个幂等提升；
- \(N\)：核逐元幂零，即核中每个元素都幂零，指数可随元素变化；
- \(N_i\)：第 \(i\) 层 \(\ker p_i\) 逐元幂零。

#### 已证明的蕴含

1. **S1：** 若 \(R\) 交换、\(q:R\to S\) 满射且 \(N\) 成立，则  
   \[
   E+N+\text{交换性}\Longrightarrow I+U.
   \]
   更准确地说，\(E\) 由 \(q\) 满射已经成立；S1 证明的是局部幂零核上的幂等提升存在且唯一。

2. **S2：** 在交换逆系中，若每层
   \[
   \ker p_i
   \]
   逐元幂零，则极限增广 \(p:L\to S\) 上每个有限幂等分解都唯一提升；特别地
   \[
   \text{每层 }N_i+\text{相容性}\Longrightarrow I+U.
   \]
   而且对所有有限 \(J\)，
   \[
   D_J(L)\cong D_J(S).
   \]
   注意这个结论不需要 \(\ker p\) 幂零，也不需要 \(p\) 满射。

3. **S4：** 若可数塔中所有过渡 \(\rho_n\) 和所有 \(p_n\) 都满射，则
   \[
   \rho_n,p_n\text{ 全满}\Longrightarrow E.
   \]
   这里不需要交换性，也不需要 \(N\)。S4 只证明元素提升，不证明幂等提升或唯一性。

#### 不能从现有条件推出的蕴含

1. **\(E\not\Rightarrow I\).**  
   取
   \[
   q:\mathbb Z\to \mathbb Z/6\mathbb Z
   \]
   为自然商映射。\(q\) 满射，故 \(E\) 成立。但 \(3\in\mathbb Z/6\mathbb Z\) 是幂等元，而 \(\mathbb Z\) 的幂等元只有 \(0,1\)，故 \(3,4\) 都不能提升为幂等元。因此 \(E\) 不推出幂等提升。

2. **\(E+N+I\not\Rightarrow U\)（若无交换性）。**  
   这就是 S6 上半部分的例子：\(q:T_2(F)\to F\times F\)，
   \[
   \ker q
   \]
   平方零，\((1,0)\) 有多个幂等提升。取常值塔
   \[
   R_n=R,\qquad \rho_n=\mathrm{id},\qquad p_n=q,
   \]
   则它也落在 S4 的“所有 \(\rho_n,p_n\) 满射”假设下，仍有 \(E+N+I\) 真而 \(U\) 假。这说明 S1 中的交换性不能去掉。

3. **\(I+U\not\Rightarrow E\).**  
   S5 的反例中，每层核平方零，S2 保证 \(I+U\)，但 \(p:L\to K[X]\) 不满射。事实上该例还有 \(\ker p=0\)，所以甚至
   \[
   I+U+N\not\Rightarrow E.
   \]

4. **\(E+I+U\not\Rightarrow N\).**  
   S3 中 \(p:k[[t]]\to k\) 满射，幂等元只有 \(0,1\) 且唯一提升，但
   \[
   t\in\ker p
   \]
   不幂零。故元素提升、幂等提升、幂等提升唯一都不能推出极限核逐元幂零。

5. **每层 \(N_i\) 不推出极限 \(N\).**  
   同样由 S3：每层
   \[
   \ker p_n=(t)\subset k[t]/(t^{n+1})
   \]
   是幂零理想，但极限核
   \[
   t k[[t]]
   \]
   不是逐元幂零的。

6. **若 \(U\) 只理解为“至多一个提升”，则 \(U\not\Rightarrow I\).**  
   仍取 \(q:\mathbb Z\to\mathbb Z/6\mathbb Z\)。幂等元 \(0,1\) 各有唯一提升；幂等元 \(3,4\) 没有提升。于是“至多一个”成立，但“存在”失败。

总结成一句话：

\[
\boxed{
\begin{gathered}
\text{交换性加逐层局部幂零核足以保证幂等提升的存在与唯一（S1、S2）；}\\
\text{但它既不保证极限增广满射（S5），也不保证极限核幂零（S3）；}\\
\text{去掉交换性后，即使核平方零，幂等提升也不唯一（S6）。}
\end{gathered}}
\]