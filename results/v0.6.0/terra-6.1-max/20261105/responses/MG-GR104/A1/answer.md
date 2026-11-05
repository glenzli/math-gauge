## S1　单层提升

取 \(e\in S\) 满足 \(e^2=e\)。由满射性取 \(x\in R\) 使 \(q(x)=e\)。则
\[
a=x^2-x\in\ker q,
\]
故对某个依赖于 \(x\) 的 \(N\ge1\)，有 \(a^N=0\)。

定义整数多项式
\[
P_N(X)=\sum_{r=N}^{2N-1}\binom{2N-1}{r}X^r(1-X)^{2N-1-r}.
\]
由二项式定理，\(P_N(X)\) 可被 \(X^N\) 整除，而 \(1-P_N(X)\) 可被 \((1-X)^N\) 整除。因此
\[
P_N(x)(1-P_N(x))=0,
\]
因为
\[
x^N(1-x)^N=(-1)^N(x^2-x)^N=0.
\]
于是 \(\widetilde e=P_N(x)\) 是幂等元。又由于 \(P_N(0)=0,\ P_N(1)=1\)，对任意幂等元 \(e\) 有 \(P_N(e)=e\)，故
\[
q(\widetilde e)=e.
\]

唯一性：若 \(f,g\in R\) 都是 \(e\) 的幂等提升，则 \(d=f-g\in\ker q\) 幂零。利用交换性及 \(f^2=f,\ g^2=g\)，得
\[
d^3=d.
\]
所以对所有 \(m\ge0\)，\(d^{2m+1}=d\)。取足够大的 \(m\)，由 \(d\) 幂零得到 \(d=0\)，即 \(f=g\)。

此构造既未除以 \(2\)，也未要求核有统一幂零指数。

---

## S2　任意有向逆系

### 极限增广

对 \(x=(x_i)\in L\)，定义
\[
p(x)=p_i(x_i),
\]
其中 \(i\) 任取。若 \(i,j\in I\)，取共同上界 \(h\)，则
\[
p_i(x_i)=p_i\rho_{ih}(x_h)=p_h(x_h)
=p_j\rho_{jh}(x_h)=p_j(x_j).
\]
故定义与指标无关，且 \(p\) 是含幺环同态。

### 有限分解的双射

先在每一层应用 S1：\(p_i\) 是交换环满射，且其核逐元素幂零，所以 \(S\) 的每个幂等元在 \(R_i\) 中恰有一个幂等提升。

给定 \((e_j)_{j\in J}\in D_J(S)\)，令 \(f_{i,j}\) 为 \(e_j\) 在 \(R_i\) 中的唯一幂等提升。若 \(i\le h\)，则 \(\rho_{ih}(f_{h,j})\) 也是 \(e_j\) 在 \(R_i\) 中的幂等提升，因此
\[
\rho_{ih}(f_{h,j})=f_{i,j}.
\]
于是 \(\widetilde e_j=(f_{i,j})_i\in L\)。

当 \(j\ne k\) 时，交换性保证 \(f_{i,j}f_{i,k}\) 是幂等元；它在 \(S\) 中的像为零，故由唯一性它等于零。于是各层的有限和 \(\sum_j f_{i,j}\) 是映到 \(1\) 的幂等元，故等于 \(1\)。所以
\[
(\widetilde e_j)_{j\in J}\in D_J(L),
\qquad p(\widetilde e_j)=e_j.
\]

反过来，若 \(D_J(L)\) 中两个元有相同的像，则它们每个坐标、每个指标处都是同一个 \(S\)-幂等元的提升；由 S1 的唯一性，所有坐标都相等。因此
\[
\boxed{D_J(L)\xrightarrow{\ \sim\ }D_J(S)}.
\]

上述论证也包含 \(J=\varnothing\)。此时 \(D_\varnothing(A)\) 非空当且仅当 \(A\) 是零环；若 \(S\) 是零环，则每个 \(R_i=\ker p_i\) 的 \(1\) 都幂零，因而每个 \(R_i\) 及 \(L\) 也是零环。

### 环分解

对对应的 \((\widetilde e_j)\in D_J(L)\)，定义
\[
\Phi:L\longrightarrow\prod_{j\in J}L/(1-\widetilde e_j)L,
\qquad
x\longmapsto\bigl(x\bmod(1-\widetilde e_j)L\bigr)_j.
\]
其逆映射为
\[
\bigl([x_j]\bigr)_j\longmapsto\sum_{j\in J}\widetilde e_jx_j.
\]
它良定义，因为 \(\widetilde e_j(1-\widetilde e_j)=0\)；互为逆则由
\[
\sum_j\widetilde e_j=1,\qquad
\widetilde e_j\widetilde e_k=0\quad(j\ne k)
\]
直接得到。因此
\[
\boxed{L\cong\prod_{j\in J}L/(1-\widetilde e_j)L}.
\]
空乘积按零环理解；此时 \(L\) 也确为零环。

### 自然性

令另一系统为 \((R_i',p_i')\)，其极限为 \(L'\)。相容的 \(u_i\) 诱导
\[
U:L\to L',\qquad (x_i)_i\mapsto(u_i(x_i))_i,
\]
并满足 \(p'U=up\)。

若 \((\widetilde e_j)\) 是 \((e_j)\) 的提升，则 \(U(\widetilde e_j)\) 是 \(u(e_j)\) 的幂等提升，故由唯一性等于后者在 \(L'\) 中的指定提升。于是
\[
D_J(U)\circ\operatorname{lift}
=\operatorname{lift}'\circ D_J(u),
\]
即分解双射自然。

此外，\(U\) 对每个因子诱导
\[
\overline U_j:L/(1-\widetilde e_j)L
\longrightarrow L'/(1-\widetilde e_j')L',
\]
其中 \(\widetilde e_j'=U(\widetilde e_j)\)。上述环分解同构与 \(U\) 及 \(\prod_j\overline U_j\) 交换。

---

## S3　极限核

相容截断唯一确定一个形式幂级数，因此
\[
L\cong k[[t]],
\]
而 \(p\) 是取常数项，故
\[
\ker p=t\,k[[t]].
\]
其中 \(t\) 不是幂零元，因为每个 \(t^m\ne0\)。所以 **极限核并非逐元素幂零**。

这不与 S2 矛盾：S2 的证明只对每层满射 \(p_n\) 使用幂零核，并不声称极限核幂零。事实上，\(k[[t]]\) 是整环，其幂等元与域 \(k\) 的幂等元一样，只有 \(0,1\)。

---

## S4　相容元素的满射性

给定 \(s\in S\)，由 \(p_1\) 满射取 \(r_1\in R_1\) 使 \(p_1(r_1)=s\)。递归地，由 \(\rho_n\) 满射，选取
\[
r_{n+1}\in R_{n+1},\qquad \rho_n(r_{n+1})=r_n.
\]
因此 \((r_n)\in L\)。并且
\[
p_{n+1}(r_{n+1})
=p_n\rho_n(r_{n+1})
=p_n(r_n)=s.
\]
故 \(p((r_n))=s\)，所以 **\(p:L\to S\) 满射**。论证不需要交换性或幂零核。

---

## S5　逐层增广

**不必满射**；即使每层核平方为零、极限核为零，也可能失败。

令 \(k=\mathbb Q\)，并设
\[
R=k[x,\varepsilon_1,\varepsilon_2,\ldots]/
(\varepsilon_i\varepsilon_j:i,j\ge1),\qquad S=k[x].
\]
令 \(p_0:R\to S\) 把所有 \(\varepsilon_i\) 送至零。其核
\[
M=\bigoplus_{i\ge1}k[x]\varepsilon_i
\]
满足 \(M^2=0\)，而 \(p_0\) 满射。

定义环自同态
\[
\alpha(x)=x+\varepsilon_1,\qquad
\alpha(\varepsilon_i)=\varepsilon_{i+1},\qquad
\alpha|_k=\mathrm{id}.
\]
这里是“环到自身的同态”，不要求它是同构。关系 \(\varepsilon_i\varepsilon_j=0\) 在像中仍成立，且 \(p_0\alpha=p_0\)。取每个 \(R_n=R\)、每个 \(p_n=p_0\)，相邻过渡映射均为 \(\alpha\)。这满足共同逆系的所有条件。

下面计算其极限。若 \((r_n)\in L\)，令其共同像为 \(f(x)\in k[x]\)。每个 \(r_n\) 唯一写成
\[
r_n=f(x)+\sum_i a_{n,i}(x)\varepsilon_i,
\]
其中和只有有限项。对任意 \(N\ge1\)，由 \(r_n=\alpha^N(r_{n+N})\) 及 \(M^2=0\)，得到
\[
r_n
=f(x)+f'(x)\sum_{j=1}^{N}\varepsilon_j
+\sum_i a_{n+N,i}(x)\varepsilon_{i+N}.
\]
固定 \(n\)。由于 \(N\) 任意，\(r_n\) 中每个 \(\varepsilon_j\) 的系数都必须是 \(f'(x)\)。但 \(r_n\) 只有有限多个非零的 \(\varepsilon_j\) 项，故 \(f'(x)=0\)。因为 \(k=\mathbb Q\)，所以 \(f\in k\)。

再看上式：此时对每个 \(N\)，\(r_n\) 的前 \(N\) 个 \(\varepsilon_j\) 系数均为零，故 \(r_n=f\)。因此
\[
L\cong k,\qquad p:L\to k[x]\text{ 是常数多项式的嵌入}.
\]
特别地，\(x\) 没有提升，\(p\) 不满射，而 \(\ker p=0\)。

这也不违反 S4：此处的过渡映射 \(\alpha\) 不满射，例如 \(x\notin\alpha(R)\)。

---

## S6　乘法结构与唯一性

### 平方零核：存在，但不必唯一

设 \(q:R\to S\) 为任意含幺环满射，\(I=\ker q\) 满足 \(I^2=0\)。先说明幂等提升仍存在。给定 \(\bar e^2=\bar e\)，任取 \(a\in R\) 提升它，令
\[
d=a^2-a\in I,\qquad e=3a^2-2a^3=a+(1-2a)d.
\]
这里 \(a,d\) 可交换，因为 \(d\) 是 \(a\) 的多项式。故多项式恒等式
\[
e^2-e=d^2(4d-3)
\]
在 \(R\) 中成立，而 \(d^2=0\)。所以 \(e^2=e\)，且 \(q(e)=\bar e\)。

但提升 **不必唯一**。取域 \(k\)，令
\[
R=\left\{\begin{pmatrix}a&b\\0&c\end{pmatrix}:a,b,c\in k\right\},
\qquad S=k\times k,
\]
\(q\) 为取对角元。其核是严格上三角矩阵，平方为零。可是
\[
\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
\begin{pmatrix}1&1\\0&0\end{pmatrix}
\]
是两个不同的幂等元，且都映到 \((1,0)\)。

### 各种性质的关系

以下对所考虑的映射记：

- \(A\)：每个元素都有原像；
- \(H\)：每个幂等元都有幂等提升；
- \(U\)：每个幂等元至多有一个幂等提升；
- \(N\)：核中每个元素幂零。对极限增广，这正是题目所问的极限核性质。

“每个幂等元有唯一提升”是 \(H+U\)。下表中“可变”表示该阶段条件下既有成立例子，也有不成立例子。

| 阶段 | \(A\) | \(H\) | \(U\) | \(N\) |
|---|---|---|---|---|
| S1 | 是 | 是 | 是 | 是 |
| S2 | 可变 | 是 | 是 | 可变 |
| S3 | 是 | 是 | 是 | 否 |
| S4 | 是 | 可变 | 可变 | 可变 |
| S5 | 可变 | 是 | 是 | 可变 |
| S6 的平方零核情形 | 是 | 是 | 可变 | 是 |

主要蕴含与反例如下。

1. 对**交换环**同态，\(N\Rightarrow U\)，其证明就是 S1 的唯一性证明，并不需要满射。若再有 \(A\)，则 S1 给出 \(H\)，所以 \(A+N\Rightarrow H+U\)。
2. 在 S2 的共同逆系中，即使不知道极限映射有 \(A\) 或 \(N\)，仍有 \(H+U\)。S5 给出 \(H+U+N\) 但无 \(A\)；S3 给出 \(A+H+U\) 但无 \(N\)。因此这两个条件均不能从 S2 或 S5 推出。
3. S2/S5 中的 \(A,N\) 甚至可同时失败：将 S5 的系统与 S3 中取 \(k=\mathbb Q\) 的系统逐层取直积。每层核仍逐元素幂零；其极限及增广为
   \[
   \mathbb Q\times\mathbb Q[[t]]
   \longrightarrow \mathbb Q[x]\times\mathbb Q,\quad
   (c,F)\longmapsto(c,F(0)).
   \]
   它不满射，且核含非幂零元 \((0,t)\)。恒等系统则同时满足 \(A,N\)。
4. \(A\) 本身不推出 \(H\)，即使在交换环中也是如此：\(\mathbb Z\to\mathbb Z/6\mathbb Z\) 是满射，而 \(3\bmod6\) 是幂等元，却不是 \(\mathbb Z\) 中幂等元 \(0,1\) 的像。将它作为常值塔，也说明 S4 不保证 \(H\)。
5. \(A+H\) 不推出 \(U\)，即使在交换环中也是如此：投影 \(k\times k\to k\) 满射且幂等元都可提升，但例如 \(0\) 有不同提升 \((0,0)\) 和 \((0,1)\)。它也可作为 S4 的常值塔。
6. 对一般交换环同态，单有 \(N\) 不推出 \(H\) 或 \(A\)：对角嵌入 \(k\to k\times k\) 的核为零，但幂等元 \((1,0)\) 不在其像中。此例不属于 S2 的共同逆系结论所限制的极限增广。
7. 去掉交换性后，甚至 \(A+H+N\) 也不推出 \(U\)：本阶段的上三角矩阵反例满足这三项，却没有唯一性。S4 亦不保证 \(N\)，因为 S3 的塔本身满足 S4 条件。