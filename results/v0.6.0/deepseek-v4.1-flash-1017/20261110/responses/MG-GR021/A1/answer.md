下面给出完整结论。为避免记号混乱，先约定：

- \(D_n=\binom n2=\frac{n(n-1)}2\)。
- 对单个块（即 \(r=1,n_1=n\)）的集合记作
  \[
  \mathscr C^L_{n,M},\qquad \mathscr R^L_{n,M},
  \]
  其中 \(L\in\{F,K_\mu\}\)。
- 记
  \[
  \operatorname{Feas}(A)=1
  \]
  表示 \(\mathscr S_L(A)\ne\varnothing\)。下面将证明这个条件与 \(L\) 无关。
- 对 \(K_\mu\)，取一致化元 \(\pi=\pi_\mu\)，使 \(2\in \pi^2\mathcal O_\mu^\times\)，且
  \[
  \sigma_\mu(\pi)\equiv-\pi\pmod{\pi^{2M}}\quad(M\ge2).
  \]
  例如 \(K_2\) 取 \(\pi=\theta\)；\(K_{-1}\) 取 \(\pi=1+\theta\) 即可。

---

# 1. 基本结构：谱投影、可行性与单块计数

## 1.1 谱投影分解

因为 \(A_i\equiv E_i\pmod 2\)，所以 \(A_i\) 的特征多项式模 \(2\) 为
\[
x^{d-n_i}(x-1)^{n_i},
\]
两个因子互素。由 Hensel 引理，存在唯一的幂等对称矩阵
\[
P_i\in M_d(\mathbb Z_2),\qquad 
P_i^2=P_i,\quad P_i^{\mathsf T}=P_i,\quad
P_i\equiv E_i\pmod 2,
\]
并且 \(P_i\) 是 \(A_i\) 的多项式，因此与所有 \(A_j\) 交换。于是
\[
P_iP_j=0\ (i\ne j),\qquad \sum_{i=1}^rP_i=I_d.
\]
事实上 \(P_iP_j\) 仍幂等且模 \(2\) 为零，故必为零；同理 \(\sum P_i\) 幂等且模 \(2\) 为 \(I\)，故等于 \(I\)。

令
\[
L_i=\operatorname{im}P_i\subset \mathbb Z_2^d.
\]
则
\[
\mathbb Z_2^d=\bigoplus_{i=1}^r L_i
\]
是相互正交的直和，且每个 \(L_i\) 是无幺模格（unimodular lattice），并且
\[
L_i\bmod 2=\mathbb F_2^{I_i}.
\]

### 引理 1.1（\(\mathscr S_L(A)\) 的精确描述）

设 \(V_i=\mathcal O_L^{I_i}\) 是标准坐标块。若 \(U\in\mathscr S_L(A)\)，则
\[
U V_i=L_i\otimes_{\mathbb Z_2}\mathcal O_L
\qquad(1\le i\le r).
\]
因此
\[
\mathscr S_L(A)\ne\varnothing
\]
当且仅当每个 \(L_i\) 在 \(\mathcal O_L\) 上等距同构于标准格 \(\mathcal O_L^{n_i}\)。

若此条件成立，取任意一组等距
\[
U_0:V_i\longrightarrow L_i\otimes\mathcal O_L,
\]
则 \(U_0\in\mathscr S_L(A)\)，并且
\[
\mathscr S_L(A)
=
U_0\cdot \prod_{i=1}^r
\{V\in O_{n_i}(\mathcal O_L):V\equiv I_{n_i}\!\!\pmod{2\mathcal O_L}\}.
\tag{1.1}
\]
特别地，只要非空，\(\mathscr S_L(A)\) 就是一个主齐性空间，其结构只由块大小 \(n_i\) 决定。

**证明要点.**  
由 \(U^{\mathsf T}A_iU\) 关于标准块分解为块对角，知 \(A_i\) 保持每个 \(U V_j\)。模 \(2\) 时 \(A_i\equiv E_i\)，所以 \(A_i\) 在 \(UV_j\) 上模 \(2\) 可逆当且仅当 \(i=j\)。于是 \(UV_j\) 必等于 \(A_i\) 的单位谱子空间，即 \(L_j\)。反过来同理。其余部分是标准的稳定子计算。\(\square\)

---

## 1.2 可行性判准

在块 \(I_i\) 的坐标中定义
\[
G_i:=E_iP_iE_i\in M_{n_i}(\mathbb Z_2).
\]
这是 \(L_i\) 在基
\[
P_ie_{i,1},\dots,P_ie_{i,n_i}
\]
下的 Gram 矩阵。

### 定理 1.2（可行性判准）

对每个 \(i\)，\(L_i\) 等距同构于标准格
\[
(\mathbb Z_2^{n_i},\,\langle\,,\,\rangle)
\]
当且仅当
\[
\boxed{\ \det G_i\equiv 1\pmod 8.\ }
\tag{1.2}
\]
因此
\[
\boxed{
\operatorname{Feas}(A)=1
\iff
\det(E_iP_iE_i)\equiv1\pmod 8
\quad(\forall i).
}
\tag{1.3}
\]
这个条件与 \(L=F,K_{-1},K_2\) 无关。

此外，\(P_i\bmod4\) 由 \(A_i\bmod4\) 唯一决定，\(G_i\bmod8\) 由 \(P_i\bmod4\) 决定，所以 (1.3) 确实可由所有 \(A_i\bmod4\) 有限计算。

**证明.**  
由于 \(P_i\) 是自伴幂等矩阵，
\[
(P_ie_{i,a})\cdot(P_ie_{i,b})
=e_{i,a}^{\mathsf T}P_i^{\mathsf T}P_ie_{i,b}
=e_{i,a}^{\mathsf T}P_ie_{i,b}
=(G_i)_{ab}.
\]
又 \(P_ie_{i,a}\equiv e_{i,a}\pmod2\)，故
\[
(G_i)_{aa}\equiv1\pmod4,\qquad
(G_i)_{ab}\equiv0\pmod2\ (a\ne b).
\]
于是对应的二次型
\[
q_i(x)=x^{\mathsf T}G_ix
\]
满足
\[
q_i(x)\equiv\sum_{a=1}^{n_i}x_a^2\pmod4.
\tag{1.4}
\]
因此 \(q_i\) 的模 \(4\) Gauss 和与标准型相同。对 \(\mathbb Z_2\) 上的奇幺模二次型，等距类由“模 \(4\) 二次型”和“行列式模 \(8\)”决定。由 (1.4) 知唯一的剩余不变量是 \(\det G_i\pmod8\)。因为 \(\det G_i\equiv1\pmod4\)，只有两种可能：
\[
\det G_i\equiv1\pmod8
\quad\text{或}\quad
\det G_i\equiv5\pmod8.
\]
第一种就是标准型；第二种是非标准型
\[
\langle 5\rangle\oplus \langle 1\rangle^{n_i-1}.
\]
证毕。\(\square\)

在 \(K_\mu\) 上，若
\[
\langle 5\rangle\oplus \langle 1\rangle^{n_i-1}
\]
变成标准型，则必须有 \(5\) 在 \(K_\mu\) 中为平方。但
\[
5\notin (K_{-1}^\times)^2,\qquad
5\notin (K_2^\times)^2.
\]
例如 \(K_2=\mathbb Q_2(\sqrt2)\) 中，若 \(5=(a+b\sqrt2)^2\)，则 \(ab=0\)，分别化为 \(a^2=5\) 或 \(2b^2=5\)，均不可能；\(K_{-1}=\mathbb Q_2(i)\) 中同理化为 \(a^2=5\) 或 \(-b^2=5\)，也不可能。因此可行性确实与 \(L\) 无关。

**非空反例（可实际计算）：** 取
\[
r=2,\quad n_1=n_2=1,\quad
v=\binom12,\quad
P=\frac{vv^{\mathsf T}}{5}
=\begin{pmatrix}1/5&2/5\\2/5&4/5\end{pmatrix},
\]
\[
A_1=P,\qquad A_2=I-P.
\]
则 \(A_1,A_2\) 对称、交换、分别 \(\equiv E_1,E_2\pmod2\)，但
\[
G_1=5,\qquad \det G_1\equiv5\pmod8.
\]
所以对全部三个域 \(F,K_{-1},K_2\)，\(\mathscr S_L(A)=\varnothing\)。此时
\[
\mathscr C_{L,1}(A)=\{I\},\qquad
\mathscr C_{L,2}(A)\ne\varnothing,
\]
但当 \(M\ge3\) 时 \(\mathscr C_{L,M}(A)=\varnothing\)。

---

# 2. 单块精确基数

以下对单个块 \(n\) 给出。所有结果与 \(\mu\in\{-1,2\}\) 无关。

## 2.1 基域 \(F=\mathbb Q_2\)

定义
\[
c^F_n(M)=|\mathscr C^F_{n,M}|,\qquad
r^F_n(M)=|\mathscr R^F_{n,M}|.
\]

则
\[
\boxed{
c^F_n(M)=
\begin{cases}
1,&M=1,\\[2mm]
2^{n(n+1)/2},&M=2,\\[2mm]
2^{(M-1)\binom n2+n+1},&M\ge3,
\end{cases}}
\tag{2.1}
\]
以及
\[
\boxed{
r^F_n(M)=
\begin{cases}
1,&M=1,\\[2mm]
2^{(M-1)\binom n2+1},&M\ge2.
\end{cases}}
\tag{2.2}
\]

**证明要点.**  
计数 \(\mathscr C^F_{n,M}\) 可按第一列做归纳。令 \(a_n(M)\) 为向量
\[
u\equiv e_1\pmod2,\qquad u^{\mathsf T}u\equiv1\pmod{2^M}
\]
的个数。\(\mathscr C^F_{n,M}\) 在全体这样的向量上传递作用，稳定子同构于 \(\mathscr C^F_{n-1,M}\)。于是
\[
c^F_n(M)=\prod_{k=1}^n a_k(M).
\]
直接计算得
\[
a_1(1)=1,\quad a_1(2)=2,\quad a_1(M)=4\ (M\ge3),
\]
\[
a_k(2)=2^k,\qquad
a_k(M)=2^{(k-1)(M-1)+1}
\quad(k\ge2,\ M\ge3).
\]
相乘即得 (2.1)。

对 \(\mathscr R^F_{n,M}\)，利用标准事实
\[
\{U\in O_n(\mathbb Z_2):U\equiv I\pmod2\}
=\{\pm I\}\exp\bigl(2\mathfrak{so}_n(\mathbb Z_2)\bigr),
\]
且 \(p\)-adic 对数在 \(I+4M_n(\mathbb Z_2)\) 上给出标准同构。由此
\[
r^F_n(M)=2\cdot 2^{(M-1)\binom n2}.
\]
当 \(M=1\) 时 \(\pm I\) 在模 \(2\) 下相同，故为 \(1\)。\(\square\)

---

## 2.2 二次扩张 \(K_\mu\)

定义
\[
c^K_n(M)=|\mathscr C^K_{n,M}|,\qquad
r^K_n(M)=|\mathscr R^K_{n,M}|.
\]

则
\[
\boxed{
c^K_n(M)=
\begin{cases}
1,&M=1,\\[2mm]
2^{n(n+1)},&M=2,\\[2mm]
2^{(M-1)n(n-1)+2n+1},&M\ge3,
\end{cases}}
\tag{2.3}
\]
以及
\[
\boxed{
r^K_n(M)=
\begin{cases}
1,&M=1,\\[2mm]
2^{(M-1)n(n-1)+1},&M\ge2.
\end{cases}}
\tag{2.4}
\]

**证明要点.**  
同样按第一列归纳。在 \(\mathcal O_K\) 中 \(2=\pi^2u\)，直接计数给
\[
a_1(1)=1,\quad a_1(2)=4,\quad a_1(M)=8\ (M\ge3),
\]
\[
a_k(2)=4^k,\qquad
a_k(M)=2^{(k-1)(2M-2)+2}
\quad(k\ge2,\ M\ge3).
\]
相乘即得 (2.3)。

对 \(\mathscr R^K_{n,M}\)，标准 \(p\)-adic 对数给出
\[
\{U\in O_n(\mathcal O_K):U\equiv I\pmod{2\mathcal O_K}\}
=\{\pm I\}\exp\bigl(\pi^2\mathfrak{so}_n(\mathcal O_K)\bigr).
\]
商去模 \(2^M\mathcal O_K=\pi^{2M}\) 后，对数部分的秩为
\[
[\mathcal O_K/\pi^{2M-2}:\mathcal O_K]^{\binom n2}
=\bigl(2^{2M-2}\bigr)^{\binom n2}.
\]
故
\[
r^K_n(M)=2\cdot 2^{(2M-2)\binom n2}
=2^{(M-1)n(n-1)+1}.
\]
\(M=1\) 时 \(\pm I\) 在模 \(2\) 下相同。\(\square\)

---

# 3. 全部分块：基数、空集条件与 \(\mathscr R\subseteq\mathscr C\) 的判准

## 3.1 空集条件

设
\[
\operatorname{Feas}(A)=1
\]
如定理 1.2 所定义。

则对任意 \(L\in\{F,K_{-1},K_2\}\)：

\[
\boxed{
\mathscr R_{L,M}(A)=\varnothing
\iff
\operatorname{Feas}(A)=0
\qquad(\text{对一切 }M).
}
\tag{3.1}
\]

并且
\[
\boxed{
\mathscr C_{L,M}(A)\ne\varnothing
\iff
\begin{cases}
M=1\text{ 或 }M=2,& \text{总成立};\\[1mm]
M\ge3,& \operatorname{Feas}(A)=1.
\end{cases}}
\tag{3.2}
\]
也就是说：无论 \(A\) 如何，\(M=1,2\) 时模 \(2^M\) 总有解；但若精确格 \(L_i\) 非标准，则从 \(M=3\) 起没有解。

## 3.2 精确基数

若 \(\operatorname{Feas}(A)=1\)，则
\[
\boxed{
|\mathscr R_{L,M}(A)|
=
\prod_{i=1}^r r^L_{n_i}(M).
}
\tag{3.3}
\]

对 \(\mathscr C\)：
\[
\boxed{
|\mathscr C_{L,M}(A)|=
\begin{cases}
1,&M=1,\\[2mm]
\displaystyle\prod_{i=1}^r c^L_{n_i}(2),&M=2,\\[4mm]
0,&M\ge3,\ \operatorname{Feas}(A)=0,\\[2mm]
\displaystyle\prod_{i=1}^r c^L_{n_i}(M),
&M\ge3,\ \operatorname{Feas}(A)=1.
\end{cases}}
\tag{3.4}
\]
其中 \(c^L_n(M)\) 由 (2.1)、(2.3) 给出，\(r^L_n(M)\) 由 (2.2)、(2.4) 给出。

显式写出总量：
\[
|\mathscr C_{F,M}(A)|
=
\prod_i 2^{(M-1)\binom{n_i}2+n_i+1}
\quad(M\ge3,\ \operatorname{Feas}=1),
\]
\[
|\mathscr C_{K,M}(A)|
=
\prod_i 2^{(M-1)n_i(n_i-1)+2n_i+1}
\quad(M\ge3,\ \operatorname{Feas}=1),
\]
\[
|\mathscr R_{F,M}(A)|
=
\prod_i 2^{(M-1)\binom{n_i}2+1}
\quad(M\ge2,\ \operatorname{Feas}=1),
\]
\[
|\mathscr R_{K,M}(A)|
=
\prod_i 2^{(M-1)n_i(n_i-1)+1}
\quad(M\ge2,\ \operatorname{Feas}=1).
\]

## 3.3 \(\mathscr R\subseteq\mathscr C\) 的可核验判准

对单个块，约化映射
\[
\mathscr C^L_{n,M+1}\longrightarrow \mathscr C^L_{n,M}
\]
的像恰为
\[
\operatorname{im}\bigl(\mathscr C^L_{n,M+1}\to\mathscr C^L_{n,M}\bigr)
=
\mathscr R^L_{n,M}.
\tag{3.5}
\]
于是对全部分块，在 \(\operatorname{Feas}(A)=1\) 时
\[
\operatorname{im}\bigl(\mathscr C_{L,M+1}(A)\to\mathscr C_{L,M}(A)\bigr)
=
\mathscr R_{L,M}(A).
\tag{3.6}
\]

因此有非常简洁的判准：

\[
\boxed{
\bar U\in\mathscr C_{L,M}(A)
\text{ 属于 }\mathscr R_{L,M}(A)
\iff
\bar U\text{ 可提升为某个 }
\widetilde U\in\mathscr C_{L,M+1}(A).
}
\tag{3.7}
\]
当 \(M\ge2\) 时此判准对全部合法 \(A\) 都成立；当 \(M=1\) 时，若 \(\operatorname{Feas}(A)=1\) 则
\(\mathscr R_{L,1}(A)=\{I\}\)，否则为空。

等价地，若先构造 \(U_0\in\mathscr S_L(A)\)，令
\[
V=U_0^{-1}\bar U\pmod{2^M\mathcal O_L}.
\]
则 \(V\) 必为关于标准分块的块对角矩阵，并且
\[
\bar U\in\mathscr R_{L,M}(A)
\iff
V_i\in\mathscr R^L_{n_i,M}\quad(1\le i\le r).
\]
而单块成员 \(V_i\in\mathscr C^L_{n_i,M}\) 是否属于 \(\mathscr R^L_{n_i,M}\)，可由“是否可提升一层到 \(\mathscr C^L_{n_i,M+1}\)”直接检验。

---

# 4. \(\sigma_\mu\)-固定点

以下只讨论 \(K_\mu\)。结论与 \(\mu=-1,2\) 无关。

## 4.1 固定环的显式描述

令
\[
R_M=\mathcal O_\mu/2^M\mathcal O_\mu.
\]
取 \(\pi=\pi_\mu\)，并令
\[
\varepsilon_M=2^{M-1}\pi.
\]
则在 \(R_M\) 中
\[
2\varepsilon_M=0,\qquad \varepsilon_M^2=0,
\qquad \sigma_\mu(\varepsilon_M)\equiv\varepsilon_M
\pmod{2^M}.
\]
并且
\[
\boxed{
R_M^{\sigma_\mu}
=
\mathbb Z/2^M\mathbb Z
\oplus
\mathbb F_2\varepsilon_M
\cong
\mathbb Z/2^M[\varepsilon]/(2\varepsilon,\varepsilon^2).
}
\tag{4.1}
\]
于是任何 \(\sigma_\mu\)-固定矩阵类可唯一写成
\[
U=A+\varepsilon_M B,
\qquad
A\in M_n(\mathbb Z/2^M),\quad
B\in M_n(\mathbb F_2).
\tag{4.2}
\]

由
\[
U^{\mathsf T}U=I,\qquad
U\equiv I\pmod2
\]
得到，对 \(M\ge2\)，
\[
A^{\mathsf T}A=I\pmod{2^M},\qquad
A\equiv I\pmod2,
\]
以及
\[
A^{\mathsf T}B+B^{\mathsf T}A=0
\quad\text{in }M_n(\mathbb F_2).
\]
因为 \(A\equiv I\pmod2\)，第二式等价于
\[
B^{\mathsf T}+B=0
\quad\Longleftrightarrow\quad
B=B^{\mathsf T}.
\]
因此有精确的集合分解
\[
\boxed{
\mathscr C_{K,M}^{\sigma_\mu}
\cong
\mathscr C_{F,M}\times \operatorname{Sym}_n(\mathbb F_2)
\qquad(M\ge2),
}
\tag{4.3}
\]
其中 \(\operatorname{Sym}_n(\mathbb F_2)\) 是 \(n\times n\) 对称矩阵的加法群。

对多个块取乘积即可。

---

## 4.2 固定点数

对单个块 \(n\)，记
\[
c^{K,\sigma}_n(M)
=
|\mathscr C^K_{n,M}{}^{\sigma_\mu}|,
\qquad
r^{K,\sigma}_n(M)
=
|\mathscr R^K_{n,M}{}^{\sigma_\mu}|.
\]

由 (4.3)：
\[
\boxed{
c^{K,\sigma}_n(M)=
\begin{cases}
1,&M=1,\\[2mm]
2^{n(n+1)},&M=2,\\[2mm]
2^{(M-1)\binom n2+\frac{(n+1)(n+2)}2},&M\ge3.
\end{cases}}
\tag{4.4}
\]
其中 \(M=2\) 时恰有
\[
\mathscr C^K_{n,2}{}^{\sigma_\mu}
=
\mathscr C^K_{n,2}.
\]

对 \(\mathscr R\)，利用
\[
\mathscr R^K_{n,M}
\cong
\{\pm I\}\times
\mathfrak{so}_n(\mathcal O_\mu)/\pi^{2M-2}\mathfrak{so}_n(\mathcal O_\mu)
\qquad(M\ge2),
\]
并在固定环 (4.1) 中数斜对称矩阵。模 \(\pi^{2M-2}\) 下，每个非对角独立分量有 \(2^M\) 个固定值，对角为 \(0\)。故
\[
\boxed{
r^{K,\sigma}_n(M)=
\begin{cases}
1,&M=1,\\[2mm]
2^{M\binom n2+1},&M\ge2.
\end{cases}}
\tag{4.5}
\]
特别地，当 \(M=2\) 时
\[
\mathscr R^K_{n,2}{}^{\sigma_\mu}
=
\mathscr R^K_{n,2}.
\]

对全部分块，若 \(\operatorname{Feas}(A)=1\)，则
\[
\boxed{
|\mathscr R_{K,M}(A)^{\sigma_\mu}|
=
\prod_{i=1}^r r^{K,\sigma}_{n_i}(M)
\qquad(M\ge2),
}
\tag{4.6}
\]
以及
\[
\boxed{
|\mathscr C_{K,M}(A)^{\sigma_\mu}|
=
\begin{cases}
1,&M=1,\\[2mm]
\displaystyle\prod_{i=1}^r c^{K}_{n_i}(2),&M=2,\\[4mm]
\displaystyle\prod_{i=1}^r c^{K,\sigma}_{n_i}(M),
&M\ge3.
\end{cases}}
\tag{4.7}
\]
若 \(\operatorname{Feas}(A)=0\)，则 \(M\ge3\) 时固定集为空；\(M=1,2\) 的公式仍成立。

---

## 4.3 与基域集合的精确关系

由 (4.3) 直接得到
\[
\boxed{
\mathscr C_{K,M}^{\sigma_\mu}
\supset \mathscr C_{F,M},
\qquad
\mathscr C_{K,M}^{\sigma_\mu}
=
\{A+\varepsilon_M B:A\in\mathscr C_{F,M},\ 
B=B^{\mathsf T}\in M_n(\mathbb F_2)\}.
}
\tag{4.8}
\]
因此嵌入商为
\[
\bigl[\mathscr C_{K,M}^{\sigma_\mu}:\mathscr C_{F,M}\bigr]
=
2^{n(n+1)/2}
\qquad(M\ge2).
\]

类似地，
\[
\boxed{
\mathscr R_{F,M}\subsetneq \mathscr R_{K,M}^{\sigma_\mu}
}
\]
一般真正包含，且当 \(M\ge2\) 时
\[
\bigl[\mathscr R_{K,M}^{\sigma_\mu}:\mathscr R_{F,M}\bigr]
=
2^{\binom n2}.
\tag{4.9}
\]
对多个块，指数分别为
\[
2^{\sum_i n_i(n_i+1)/2}
\quad\text{和}\quad
2^{\sum_i\binom{n_i}2}.
\]

---

## 4.4 哪些固定类能提升为真正的 \(\sigma_\mu\)-固定解？

若 \(U\in\mathscr S_K(A)\) 且 \(\sigma_\mu(U)=U\)，则由固定性
\[
U\in GL_d(\mathcal O_K)\cap GL_d(F)=GL_d(\mathbb Z_2).
\]
因此
\[
\boxed{
\mathscr S_K(A)^{\sigma_\mu}
=
\mathscr S_F(A).
}
\tag{4.10}
\]

于是对固定矩阵类 \(x\in\mathscr C_{K,M}(A)^{\sigma_\mu}\)：

\[
\boxed{
x\text{ 可提升为某个真正的 }\sigma_\mu\text{-固定解}
\iff
x\in \mathscr R_{F,M}(A)
\subset \mathscr R_{K,M}(A)^{\sigma_\mu}.
}
\tag{4.11}
\]
在 (4.2) 的坐标下等价于
\[
B=0
\quad\text{且}\quad
A\in\mathscr R_{F,M}.
\tag{4.12}
\]

同样地，\(x\) 能作为一条逐层相容的固定矩阵类序列在精度 \(M\) 处的分量，也当且仅当
\[
x\in\mathscr R_{F,M}(A).
\]
原因是：在单块情形下，固定类约化映射
\[
\mathscr C_{K,M+1}^{\sigma_\mu}\longrightarrow
\mathscr C_{K,M}^{\sigma_\mu}
\]
的像恰为嵌入的 \(\mathscr R_{F,M}\)；而对 \(\mathscr R\) 也有
\[
\operatorname{im}\bigl(
\mathscr R_{K,M+1}^{\sigma_\mu}\to
\mathscr R_{K,M}^{\sigma_\mu}
\bigr)
=
\mathscr R_{F,M}.
\tag{4.13}
\]
因此，一个固定类只要能在固定类中提升一层，就已经必须是基域上的真正解类。

---

## 4.5 \(\langle\sigma_\mu\rangle\)-轨道数

因为 \(\sigma_\mu\) 是二阶置换，轨道长只能为 \(1\) 或 \(2\)。故对任何 \(\sigma_\mu\)-稳定集合 \(X\)，
\[
\#\{\langle\sigma_\mu\rangle\text{-轨道}\}
=
\frac{|X|+|X^{\sigma_\mu}|}{2}.
\]

因此对单个块：

- \(\mathscr C^K_{n,M}\) 的轨道数为
  \[
  \frac{c^K_n(M)+c^{K,\sigma}_n(M)}2.
  \]
- \(\mathscr R^K_{n,M}\) 的轨道数为
  \[
  \frac{r^K_n(M)+r^{K,\sigma}_n(M)}2.
  \]
  对 \(M=1\) 为 \(1\)。

对多个块，把 \(c^K_n\) 等换成乘积即可：
\[
\boxed{
\#\operatorname{Orb}\bigl(\sigma_\mu;
\mathscr C_{K,M}(A)\bigr)
=
\frac{
\prod_i c^K_{n_i}(M)
+
\prod_i c^{K,\sigma}_{n_i}(M)
}{2},
}
\tag{4.14}
\]
（若 \(M\ge3\) 且 \(\operatorname{Feas}(A)=0\)，则为 \(0\)；\(M=1\) 为 \(1\)；\(M=2\) 时固定集等于全空间，故轨道数为 \(\prod_i c^K_{n_i}(2)\)），以及
\[
\boxed{
\#\operatorname{Orb}\bigl(\sigma_\mu;
\mathscr R_{K,M}(A)\bigr)
=
\frac{
\prod_i r^K_{n_i}(M)
+
\prod_i r^{K,\sigma}_{n_i}(M)
}{2}.
}
\tag{4.15}
\]
若 \(\operatorname{Feas}(A)=0\)，则为 \(0\)。

在固定点集上，\(\sigma_\mu\) 作用为恒等，所以每个点本身就是一个轨道，轨道数就是固定点数：
\[
\boxed{
\#\operatorname{Orb}
\bigl(\sigma_\mu;\mathscr C_{K,M}^{\sigma_\mu}\bigr)
=
|\mathscr C_{K,M}^{\sigma_\mu}|,
\qquad
\#\operatorname{Orb}
\bigl(\sigma_\mu;\mathscr R_{K,M}^{\sigma_\mu}\bigr)
=
|\mathscr R_{K,M}^{\sigma_\mu}|.
}
\tag{4.16}
\]

---

# 5. 精度约化像与非空纤维

仍先对单个块 \(n\)。

## 5.1 基域 \(F\)

1. 对
   \[
   \mathscr C^F_{n,M+1}\longrightarrow \mathscr C^F_{n,M},
   \]
   有
   \[
   \operatorname{im}= \mathscr R^F_{n,M}.
   \]
   每个非空纤维大小恒为
   \[
   \boxed{2^{n(n+1)/2}.}
   \tag{5.1}
   \]

2. 对
   \[
   \mathscr R^F_{n,M+1}\longrightarrow \mathscr R^F_{n,M},
   \]
   映射满射；纤维大小
   \[
   \boxed{
   \begin{cases}
   2^{\binom n2+1},&M=1,\\[2mm]
   2^{\binom n2},&M\ge2.
   \end{cases}}
   \tag{5.2}
   \]

## 5.2 二次扩张 \(K_\mu\)

1. 对
   \[
   \mathscr C^K_{n,M+1}\longrightarrow \mathscr C^K_{n,M},
   \]
   有
   \[
   \operatorname{im}= \mathscr R^K_{n,M}.
   \]
   每个非空纤维大小恒为
   \[
   \boxed{2^{n(n+1)}.}
   \tag{5.3}
   \]

2. 对
   \[
   \mathscr R^K_{n,M+1}\longrightarrow \mathscr R^K_{n,M},
   \]
   映射满射；纤维大小
   \[
   \boxed{
   \begin{cases}
   2^{n(n-1)+1},&M=1,\\[2mm]
   2^{n(n-1)},&M\ge2.
   \end{cases}}
   \tag{5.4}
   \]

## 5.3 固定点集

对
\[
\mathscr C^{K,\sigma}_{n,M+1}\longrightarrow
\mathscr C^{K,\sigma}_{n,M},
\]
有
\[
\boxed{
\operatorname{im}
=
\mathscr R^F_{n,M}\quad(\text{嵌入的基域集合}),
}
\tag{5.5}
\]
且每个非空纤维大小恒为
\[
\boxed{2^{n(n+1)}.}
\tag{5.6}
\]

对
\[
\mathscr R^{K,\sigma}_{n,M+1}\longrightarrow
\mathscr R^{K,\sigma}_{n,M},
\]
有
\[
\boxed{
\operatorname{im}
=
\mathscr R^F_{n,M}
\quad(\text{嵌入的基域集合}),
}
\tag{5.7}
\]
且纤维大小
\[
\boxed{
\begin{cases}
2^{n(n-1)+1},&M=1,\\[2mm]
2^{n(n-1)},&M\ge2.
\end{cases}}
\tag{5.8}
\]

对多个块，以上纤维大小分别取乘积；例如
\[
\prod_i 2^{n_i(n_i+1)}
=
2^{\sum_i n_i(n_i+1)}
\]
等。

---

# 6. 下降精度：最大统一整数 \(N\)

设
\[
U\in\mathscr S_{K_\mu}(A),\qquad
\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}.
\]
我们要找
\[
W\in\mathscr S_F(A),\qquad
U\equiv W\pmod{2^N\mathcal O_\mu}.
\]

先注意：由 (4.10)，
\[
\mathscr S_{K_\mu}(A)^{\sigma_\mu}
=
\mathscr S_F(A).
\]

## 6.1 统一下降界

### 定理 6.1

固定块秩 \(n_1,\dots,n_r\) 与 \(M\ge2\)。

1. 若
   \[
   n_1=\cdots=n_r=1,
   \]
   则对一切合法 \(A\) 与满足 \(\sigma_\mu(U)\equiv U\pmod{2^M}\) 的 \(U\)，都有
   \[
   U\in\mathscr S_F(A).
   \]
   因此可取
   \[
   \boxed{N=M.}
   \]

2. 若至少有一个 \(i\) 满足 \(n_i\ge2\)，则最大的统一整数是
   \[
   \boxed{N=M-1.}
   \]
   即：对一切合法 \(A,U\)，总存在 \(W\in\mathscr S_F(A)\) 使得
   \[
   U\equiv W\pmod{2^{M-1}\mathcal O_\mu},
   \]
   但一般不能做到 \(N=M\)。

**证明.**  
当所有 \(n_i=1\) 时，
\[
O_1(\mathcal O_K)=\{\pm1\}=\mathcal O_F^\times,
\]
故 \(\mathscr S_K(A)=\mathscr S_F(A)\)，断言显然。

现设某个 \(n_j\ge2\)。先证明上界 \(N\le M-1\)。取
\[
A_i=E_i\qquad(1\le i\le r),
\]
即 \(A\) 已经是标准块投影。取非零斜对称矩阵
\[
C=E_{12}-E_{21}\in\mathfrak{so}_{n_j}(\mathbb Z_2),
\]
把 \(C\) 只放在第 \(j\) 块，其它块取 \(0\)。令
\[
z=\pi_\mu^{2M-1},\qquad
U_j=\exp(zC),
\]
并令整个矩阵为
\[
U=\operatorname{diag}(I_{n_1},\dots,U_j,\dots,I_{n_r}).
\]
则：
\[
U\equiv I\pmod{\pi_\mu^2}
\]
（因为 \(2M-1\ge3\)），且 \(U\) 关于标准块对角，故
\[
U\in\mathscr S_{K_\mu}(E).
\]
又
\[
\sigma_\mu(U)\equiv \exp(-zC)\pmod{\pi_\mu^{2M}},
\]
于是
\[
U-\sigma_\mu(U)
\equiv 2zC
\equiv 0\pmod{\pi_\mu^{2M}}.
\]
所以
\[
U\equiv\sigma_\mu(U)\pmod{2^M\mathcal O_\mu}.
\]
但
\[
U_{12}=\pi_\mu^{2M-1}
\]
（模 \(\pi_\mu^{2M}\)），而任何基域矩阵 \(W\in GL_d(\mathbb Z_2)\) 的 \((\mathbb Z_2)\)-元素在 \(\mathcal O_K\) 中只含 \(\pi_\mu\) 的偶次项。因此 \(U\not\equiv W\pmod{\pi_\mu^{2M}}\) 对任意 \(W\in\mathscr S_F(E)\) 成立。故 \(N=M\) 不可能，统一上界至多 \(M-1\)。

再证明 \(N=M-1\) 总能达到。由 (1.1)，取 \(U_0\in\mathscr S_F(A)\)（可行性与 \(L\) 无关，故存在）。写
\[
U=U_0V,\qquad
V=\prod_{i=1}^rV_i,
\]
其中 \(V_i\in O_{n_i}(\mathcal O_K)\)，且 \(V_i\equiv I\pmod{\pi^2}\)。对每个 \(i\)，由 p-adic 对数分解
\[
V_i=\eta_i\exp(\pi^2X_i),
\qquad
\eta_i=\pm I_{n_i},
\quad
X_i\in\mathfrak{so}_{n_i}(\mathcal O_K).
\]
条件 \(\sigma_\mu(V_i)\equiv V_i\pmod{\pi^{2M}}\) 给出
\[
X_i\equiv\sigma_\mu(X_i)\pmod{\pi^{2M-2}}.
\]
写
\[
X_i=A_i+\pi_\mu B_i,
\qquad
A_i\in M_{n_i}(\mathbb Z_2),
\]
其中 \(A_i\) 为常数项。因为
\[
X_i-\sigma_\mu(X_i)=-2\pi_\mu B_i,
\]
而 \(2\in\pi_\mu^2\mathcal O_K^\times\)，所以
\[
\pi_\mu^3B_i\in\pi_\mu^{2M-2}M_{n_i}(\mathcal O_K),
\]
从而
\[
B_i\in\pi_\mu^{2M-5}M_{n_i}(\mathcal O_K),
\]
所以
\[
X_i\equiv A_i\pmod{\pi_\mu^{2M-4}}.
\]
由 \(X_i^{\mathsf T}=-X_i\) 得
\[
A_i^{\mathsf T}=-A_i.
\]
令
\[
V_i':=\eta_i\exp(\pi^2A_i)\in O_{n_i}(\mathbb Z_2),
\qquad
V':=\prod_iV_i',
\]
并令
\[
W:=U_0V'\in\mathscr S_F(A).
\]
指数映射在 \(I+\pi^2M_n\) 上是等距同构，故
\[
V_i\equiv V_i'\pmod{\pi_\mu^{2M-2}},
\]
于是
\[
U\equiv W\pmod{\pi_\mu^{2M-2}}
=
\pmod{2^{M-1}\mathcal O_\mu}.
\]
即 \(N=M-1\) 总可以达到。结合上界，得到最大统一值 \(M-1\)。\(\square\)

---

## 6.2 对给定 \(A,U\) 何时可取 \(N=M\)

由 (4.10)，能做到 \(N=M\) 当且仅当
\[
U\bmod 2^M\mathcal O_\mu
\in
\mathscr R_{F,M}(A)
\quad
(\text{视 }\mathscr R_{F,M}(A)\text{ 通过自然嵌入为 }\mathscr R_{K,M}(A)^{\sigma_\mu}\text{ 的子集}).
\]
等价地，取 \(U_0\in\mathscr S_F(A)\)，令
\[
V=U_0^{-1}U\pmod{2^M\mathcal O_\mu}.
\]
因为 \(U\) 近似固定，\(V\) 在固定环中可唯一写成
\[
V=A+\varepsilon_M B,
\qquad
A\in M_d(\mathbb Z/2^M),\quad
B\in M_d(\mathbb F_2),
\]
并按块分解。则
\[
\boxed{
N=M
\iff
B=0
\quad\text{且}\quad
A\in\prod_{i=1}^r\mathscr R^F_{n_i,M}.
}
\tag{6.1}
\]
这里 \(A\in\prod_i\mathscr R^F_{n_i,M}\) 可用第 3.3 节的“一层提升”判准直接检验：每个块类必须属于模 \(2^M\) 的基域精确解像。

在块秩全部为 \(1\) 时，(6.1) 自动成立，因此统一地有 \(N=M\)。若某个 \(n_i\ge2\)，(6.1) 不再自动成立；第 6.1 节中的统一构造说明它可以被破坏到任意精度。

---

# 7. 结论汇总

- **可行性**：
  \[
  \operatorname{Feas}(A)
  \iff
  \det(E_iP_iE_i)\equiv1\pmod8\quad(\forall i),
  \]
  其中 \(P_i\) 是 \(A_i\equiv E_i\pmod2\) 的 Hensel 谱投影。此判准只依赖 \(A_i\bmod4\)，且与 \(F,K_{-1},K_2\) 无关。

- 若可行，则
  \[
  \mathscr S_L(A)
  =
  U_0\prod_{i=1}^r
  \{V\in O_{n_i}(\mathcal O_L):V\equiv I\pmod{2\mathcal O_L}\}.
  \]
  因此 \(\mathscr R_{L,M}(A)\)、\(\mathscr C_{L,M}(A)\) 的基数分别等于各块基数的乘积，单块公式为上面的表 (2.1)–(2.4)。

- 空集：
  \[
  \mathscr R_{L,M}(A)=\varnothing
  \iff \neg\operatorname{Feas}(A),
  \]
  \[
  \mathscr C_{L,M}(A)\ne\varnothing
  \iff
  M\in\{1,2\}\ \text{或}\ \operatorname{Feas}(A).
  \]

- 对 \(\bar U\in\mathscr C_{L,M}(A)\)，当 \(M\ge2\) 时，
  \[
  \bar U\in\mathscr R_{L,M}(A)
  \iff
  \bar U\text{ 可提升为 }\mathscr C_{L,M+1}(A)\text{ 中元素}.
  \]

- 固定环：
  \[
  (\mathcal O_{K_\mu}/2^M)^{\sigma_\mu}
  \cong
  \mathbb Z/2^M[\varepsilon]/(2\varepsilon,\varepsilon^2),
  \]
  故
  \[
  \mathscr C_{K,M}^{\sigma_\mu}
  \cong
  \mathscr C_{F,M}\times\operatorname{Sym}_n(\mathbb F_2)
  \quad(M\ge2).
  \]
  固定点数由 (4.4)、(4.5) 给出，轨道数由 (4.14)–(4.16) 给出。

- 固定类可提升为真正 \(\sigma_\mu\)-固定解，或可作为逐层相容固定类序列的分量，当且仅当它属于嵌入的基域精确解像
  \[
  \mathscr R_{F,M}(A)
  \subset
  \mathscr R_{K,M}(A)^{\sigma_\mu}.
  \]

- 约化像：
  \[
  \operatorname{im}(\mathscr C_{L,M+1}\to\mathscr C_{L,M})
  =
  \mathscr R_{L,M},
  \]
  \[
  \operatorname{im}(\mathscr C_{K,M+1}^{\sigma_\mu}\to\mathscr C_{K,M}^{\sigma_\mu})
  =
  \operatorname{im}(\mathscr R_{K,M+1}^{\sigma_\mu}\to\mathscr R_{K,M}^{\sigma_\mu})
  =
  \mathscr R_{F,M},
  \]
  非空纤维大小见 (5.1)–(5.8)。

- 统一下降：
  \[
  N_{\max}=
  \begin{cases}
  M,&n_1=\cdots=n_r=1,\\[2mm]
  M-1,&\text{若存在 }n_i\ge2.
  \end{cases}
  \]
  给定的 \(A,U\) 能达到 \(N=M\) 的充要条件为
  \[
  U\bmod 2^M\in\mathscr R_{F,M}(A),
  \]
  等价于 (6.1)。若存在 \(n_i\ge2\)，则第 6.1 节中的
  \[
  U=\exp(\pi_\mu^{2M-1}(E_{12}-E_{21}))
  \]
  （置于该块，其余块取单位阵）给出对任意 \(M\ge2\) 都成立的统一反例，证明 \(M\) 位精度不能统一达到。