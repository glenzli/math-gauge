## S1 可缩子复形的商

**结论：商映射 \(q:Y\to Y/A\) 是同伦等价。**

因为 \((Y,A)\) 是 CW 对，包含 \(A\hookrightarrow Y\) 具有同伦延拓性质。取 \(A\) 的收缩
\[
c_t:A\to A,\qquad c_0=\operatorname{id}_A,\qquad c_1(a)=a_0,
\]
并把它延拓为
\[
F_t:Y\to Y,\qquad F_0=\operatorname{id}_Y,\qquad F_t|_A=c_t.
\]
特别地，\(F_t(A)\subseteq A\)，且 \(F_1(A)=\{a_0\}\)。

于是 \(F_1\) 在商空间上定义了连续映射
\[
g:Y/A\longrightarrow Y,\qquad g([y])=F_1(y).
\]
显然 \(gq=F_1\)，所以 \(F_t\) 给出
\[
\operatorname{id}_Y\simeq gq.
\]

另一方面，对每个 \(t\)，映射 \(qF_t:Y\to Y/A\) 都把 \(A\) 映到同一个点 \([A]\)，因而下降为
\[
\overline F_t:Y/A\longrightarrow Y/A,\qquad \overline F_t([y])=[F_t(y)].
\]
这里 \(\overline F_0=\operatorname{id}_{Y/A}\)，而 \(\overline F_1=qg\)，故
\[
\operatorname{id}_{Y/A}\simeq qg.
\]
下降后的同伦连续，是因为 \(q\times\operatorname{id}_{[0,1]}\) 是商映射（区间是局部紧致空间）。因此 \(g\) 是 \(q\) 的同伦逆。

---

## S2 非可缩底空间上的锥附着

记映射 \(f:L\to D\) 的非约化映射锥为
\[
C(f)=D\cup_f CL.
\]
我们用以下标准事实：对于 CW 空间 \(L\)，若 \(f_0\simeq f_1:L\to D\)，则
\[
C(f_0)\simeq C(f_1).
\]
这是映射锥作为同伦推出
\[
D\longleftarrow L\longrightarrow *
\]
的同伦不变性；此处 \(L\hookrightarrow CL\) 是余纤维，故普通推出就是相应的同伦推出。

也可以直接写出映射：若 \(H:f_0\simeq f_1\)，定义 \(F:C(f_0)\to C(f_1)\) 在 \(D\) 上为恒等，在锥上为
\[
F(x,t)=
\begin{cases}
H(x,2t)\in D,&0\le t\le \frac12,\\[2mm]
(x,2t-1)\in CL,&\frac12\le t\le1 .
\end{cases}
\]
用 \(H\) 的反向同伦类似构造反向映射；拼接 \(H\) 与其反向同伦并重新参数化锥坐标，可得两个复合均同伦于恒等。

现在题设给出包含映射 \(i:L\hookrightarrow D\) 零伦。取同伦
\[
i\simeq c_{d_0}:L\to D,\qquad c_{d_0}(x)=d_0.
\]
因此
\[
Y=C(i)\simeq C(c_{d_0}).
\]
而常值映射的映射锥为
\[
C(c_{d_0})
 =D\cup_{L\to\{d_0\}}CL
 \cong D\vee (CL/L),
\]
其中 \(CL/L\) 是把锥底 \(L\) 缩成一点。它正是非约化悬挂 \(\Sigma L\)：锥顶和锥底分别给出两个悬挂极点。因此
\[
\boxed{Y\simeq D\vee\Sigma L.}
\]

楔点取为：

- 在 \(D\) 中取零伦终点 \(d_0\)；
- 在 \(\Sigma L\) 中取由锥底 \(L\) 缩成的那个极点。

若已另给 \(D\) 的基点，利用 \(D\) 路径连通，可沿路径把 \(d_0\) 移到该基点；相应的常值映射也同伦。

---

## S3 整数扭结的实例

设 \(L\) 是 \(\mathbb{RP}^2\) 的任一有限单纯三角剖分。取两个新顶点 \(u,v\)，构造双锥
\[
K=(u*L)\cup_L(v*L).
\]
其几何实现就是
\[
X=|K|\cong\Sigma|L|\cong\Sigma\mathbb{RP}^2,
\]
其中 \(u,v\) 是两个悬挂极点。

任取 \(L\) 的一个顶点 \(w\)，令 \(B\) 为由边 \(\{v,w\}\) 及其两个端点组成的子复形。

### 验证原条件

把每个含 \(v\) 的单形中 \(v\) 的重心坐标线性推到 \(0\)，得到强形变收缩
\[
X\setminus\{v\}\ \searrow\ |u*L|.
\]
后者是一个锥，因而可缩；同时 \(X\setminus\{v\}\) 非空。

另一方面，
\[
C=|B|\cong[0,1],\qquad C\setminus\{v\}\cong(0,1].
\]
二者均可缩，所以包含
\[
O\cap C=C\setminus\{v\}\hookrightarrow C
\]
是同伦等价。

### 同调与不可缩性

非约化悬挂满足
\[
\widetilde H_{n+1}(\Sigma Z;R)\cong\widetilde H_n(Z;R).
\]
由于
\[
\widetilde H_*(\mathbb{RP}^2;\mathbb Q)=0,
\]
得到
\[
\boxed{\widetilde H_*(X;\mathbb Q)=0.}
\]
但
\[
H_2(X;\mathbb Z)
 \cong H_1(\mathbb{RP}^2;\mathbb Z)
 \cong\mathbb Z/2,
\]
所以 \(X\) 不可缩。这样便得到满足全部要求的 \((K,v,B)\)。

---

## S4 整体对象与全部恢复目标

### 1. 由 \(v\) 的局部数据分解 \(X\)

定义
\[
K_0=\{\sigma\in K:v\notin\sigma\},
\]
以及 \(v\) 的链环
\[
\operatorname{lk}_K(v)
 =\{\tau\in K_0:\tau\cup\{v\}\in K\}.
\]
记
\[
Q=|K_0|,\qquad \Lambda=|\operatorname{lk}_K(v)|.
\]
\(v\) 的闭星形就是抽象锥 \(v*\operatorname{lk}_K(v)\)，所以
\[
K=K_0\cup(v*\operatorname{lk}_K(v)),\qquad
K_0\cap(v*\operatorname{lk}_K(v))=\operatorname{lk}_K(v).
\]
当链环非空时，这在几何实现上给出
\[
X=Q\cup_\Lambda C\Lambda. \tag{1}
\]

还有一个关键的强形变收缩
\[
O=X\setminus\{v\}\ \searrow\ Q. \tag{2}
\]
具体地，若 \(x\) 位于单形 \(v*\tau\) 中，写成
\[
x=\lambda v+(1-\lambda)y,\qquad y\in|\tau|,\quad \lambda<1,
\]
则令
\[
R_s(x)=(1-s)\lambda v+\bigl(1-(1-s)\lambda\bigr)y.
\]
在不含 \(v\) 的单形上令 \(R_s=\operatorname{id}\)。该公式在面上相容，且 \(R_1(O)\subseteq Q\)，故证明 (2)。

因为 \(O\) 非空可缩，所以 \(Q\) 也是非空可缩有限 CW 复形。

### 2. \(X\) 的所有可能同伦类型

若 \(\operatorname{lk}_K(v)\neq\varnothing\)，则在 (1) 中，\(\Lambda\) 到可缩空间 \(Q\) 的包含必零伦。S2 的条件全部满足，因此
\[
X\simeq Q\vee\Sigma\Lambda.
\]
再把可缩子复形 \(Q\) 用 S1 缩商，得到
\[
\boxed{X\simeq\Sigma\Lambda
 =\Sigma|\operatorname{lk}_K(v)|.}
\]

题设中的 \(B\) 还排除了链环为空的情形。事实上，若链环为空，则 \(v\) 是 \(K\) 的孤立顶点。任何含 \(v\) 的子复形 \(B\) 都满足
\[
C=\{v\}\sqcup C',\qquad C\setminus\{v\}=C',
\]
其中 \(C'\) 可能为空。包含 \(C'\hookrightarrow\{v\}\sqcup C'\) 不可能在路径分支集合上诱导双射，因而不可能是同伦等价。

故在原假设下，必有 \(\operatorname{lk}_K(v)\neq\varnothing\)，并且
\[
\boxed{\text{\(X\) 的可能同伦类型恰为非空有限单纯复形的非约化悬挂。}}
\]

### 3. 所有类型的实现

任给非空有限单纯复形 \(L\)，取双锥
\[
K=(u*L)\cup_L(v*L).
\]
则 \(X\cong\Sigma|L|\)，且如 S3 所述，
\[
X\setminus\{v\}\ \searrow\ |u*L|
\]
故 \(X\setminus\{v\}\) 非空可缩。

取 \(L\) 的任一顶点 \(w\)，令 \(B\) 为边 \(\{v,w\}\) 及其面。则
\[
C\cong[0,1],\qquad C\setminus\{v\}\cong(0,1],
\]
所以 \(O\cap C\hookrightarrow C\) 是同伦等价。这样，每一个非空有限单纯复形 \(L\) 的悬挂类型都能实现。

### 4. 可缩性的有限局部判据

**判据：**
\[
\boxed{
X\text{ 可缩}
\iff
\operatorname{lk}_K(v)\neq\varnothing
\ \text{且}\
\widetilde H_j(\operatorname{lk}_K(v);\mathbb Z)=0
\quad\text{对所有 }j\ge0.
}
\]
也就是说，链环必须是**非空、连通且整数无环的**；其中连通性已包含在 \(\widetilde H_0=0\) 中。

证明如下。记 \(\Lambda=|\operatorname{lk}_K(v)|\)。由 \(X\simeq\Sigma\Lambda\) 及悬挂同调公式，若 \(X\) 可缩，则
\[
\widetilde H_j(\Lambda;\mathbb Z)
\cong\widetilde H_{j+1}(X;\mathbb Z)=0
\]
对所有 \(j\ge0\) 成立。

反之，若这些群全为零，则 \(\widetilde H_0(\Lambda)=0\)，故有限 CW 复形 \(\Lambda\) 路径连通。非约化悬挂可用两个可缩的开锥邻域覆盖，其交同伦等价于路径连通的 \(\Lambda\)；由 Seifert–van Kampen 定理，\(\Sigma\Lambda\) 单连通。同时悬挂公式表明它整数无环。

单连通 CW 复形若所有约化整数同调均为零，则由 Hurewicz 定理逐次得到所有同伦群为零，再由 Whitehead 定理知其可缩。因此 \(X\simeq\Sigma\Lambda\) 可缩。

最后，\(\operatorname{lk}_K(v)\) 完全由含 \(v\) 的单形及其面确定；其整数单纯同调可由有限个整数边界矩阵及其 Smith 标准形计算。因此这确实是一个只使用所要求局部有限关联数据的判据。**必须取整数系数；有理无环并不足够，S3 就是反例。**

---

## S5 不提供子复形 \(B\)

**结论：不必同伦等价于非空有限复形的悬挂。**

最简单的反例是令 \(K\) 只含两个孤立顶点 \(v,w\)。则
\[
|K|\setminus\{v\}=\{w\}
\]
非空可缩，但 \(|K|\) 是两点离散空间 \(S^0\)。任何非空空间的非约化悬挂都路径连通，所以不可能同伦等价于 \(S^0\)。

完整分类仍由 S4 的分解得到：

1. 若 \(\operatorname{lk}_K(v)\neq\varnothing\)，不需要任何 \(B\)，仍有
   \[
   |K|\simeq\Sigma|\operatorname{lk}_K(v)|.
   \]

2. 若 \(\operatorname{lk}_K(v)=\varnothing\)，则 \(v\) 孤立，并且
   \[
   |K|=Q\sqcup\{v\},
   \]
   其中 \(Q\) 非空可缩。因此
   \[
   |K|\simeq *\sqcup *\cong S^0.
   \]

反之，任取非空有限可缩单纯复形 \(Z\)，令 \(K=Z\sqcup\{v\}\)，即可实现第二类情形。

所以没有 \(B\) 时，**只新增一个同伦类型，即两点离散空间 \(S^0\)**；它恰好对应于 \(v\) 为孤立顶点。

---

## S6 悬挂信息的逆向恢复

**结论：不能推出。**

取 \(L_1\) 为单顶点复形，所以 \(\Sigma|L_1|\) 是一个区间，因而可缩。

再取 \(\mathscr P\) 为 Poincaré 同调 \(3\)-球面，去掉一个开 \(3\)-球，得到带边界的紧致流形
\[
N=\mathscr P\setminus\operatorname{int}D^3.
\]
取 \(N\) 的任一有限单纯三角剖分作为 \(L_2\)。

\(N\) 具有以下性质：

- 由 \(\mathscr P=N\cup D^3\)、\(N\cap D^3=S^2\) 和 van Kampen 定理，
  \[
  \pi_1(N)\cong\pi_1(\mathscr P),
  \]
  后者是非平凡的二元二十面体群，所以 \(N\) 不可缩。
- \(N\) 整数无环。事实上，\(H_3(N)=0\)，因为 \(N\) 有非空边界；同一拼接的 Mayer–Vietoris 序列给出
  \[
  H_3(\mathscr P)\xrightarrow{\ \cong\ }H_2(S^2)
  \longrightarrow H_2(N)\longrightarrow H_2(\mathscr P)=0,
  \]
  其中连接映射把基本类送到边界球面的基本类，故 \(H_2(N)=0\)。又有 \(H_1(N)=H_1(\mathscr P)=0\)，且 \(N\) 连通。

于是 \(L_2\) 路径连通且整数无环。由 S4 中同样的 Hurewicz–Whitehead 论证，\(\Sigma|L_2|\) 单连通且无环，所以可缩。因此
\[
\Sigma|L_1|\simeq *\simeq\Sigma|L_2|.
\]
但是
\[
|L_1|\simeq *,\qquad |L_2|\simeq N\not\simeq *,
\]
因为二者基本群不同。故
\[
\boxed{\Sigma|L_1|\simeq\Sigma|L_2|\ \not\Rightarrow\ |L_1|\simeq|L_2|.}
\]