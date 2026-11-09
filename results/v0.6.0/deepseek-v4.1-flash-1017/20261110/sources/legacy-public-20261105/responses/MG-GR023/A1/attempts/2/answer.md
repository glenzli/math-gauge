下面始终使用选择公理（ZFC），并反复使用两条标准事实：每个具有有限交性质的集族可扩张为超滤子；\(\beta X\) 在 Stone 拓扑下紧 Hausdorff。记
\[
X^g=\{x\in X:gx=x\},\qquad X^G=\bigcap_{g\in G}X^g.
\]
对 \(A\subseteq X\)，记 \(f_A:X\to[2]\) 为
\[
f_A(x)=
\begin{cases}
0,&x\in A,\\
1,&x\notin A.
\end{cases}
\]
若 \(X\ne\varnothing\)，记 \(\beta X\) 为 \(X\) 上超滤子的集合；对 \(h:X\to Y\)，记
\[
h_*U=\{B\subseteq Y:h^{-1}B\in U\}.
\]

---

# 一、截断及其相容关系

## 1.1 \(R_m(X)\) 的完全分类

### 命题 1.1
对任意集合 \(X\)：

1. 对一切允许的 \(m\)，若 \(X=\varnothing\)，则
   \[
   R_m(\varnothing)=\varnothing.
   \]
2. 若 \(X\ne\varnothing\)，则
   \[
   |R_1(X)|=1.
   \]
3. 若 \(X\ne\varnothing\)，则 \(R_2(X)\) 与下述集合双射：
   \[
   \mathcal C_2(X)
   :=\left\{c:\mathcal P(X)\to\{0,1\}:
   \begin{array}{l}
   c(A^c)=1-c(A)\quad(\forall A\subseteq X),\\
   c(X)=0
   \end{array}
   \right\}.
   \]
   双射为
   \[
   r\longmapsto \bigl(A\mapsto r_2(f_A)\bigr).
   \]
   等价地，\(c(\varnothing)=1\)，且每一对 \(\{A,A^c\}\) 中恰取一个值为 \(0\) 的元素。
4. 若 \(X\ne\varnothing\) 且 \(m\ge 3\)（包括 \(m=\infty\)），则
   \[
   R_m(X)\cong \beta X.
   \]
   具体双射为
   \[
   U\longmapsto r_U,\qquad
   r_{U,n}(f)=\text{唯一的 }j\in[n]\text{ 使得 }f^{-1}(j)\in U,
   \]
   其中 \(n\ge1\)，并令 \(r_{U,0}\) 为唯一的空映射。其逆为
   \[
   r\longmapsto U_r
   :=\{A\subseteq X:r_2(f_A)=0\}.
   \]

特别地，若 \(X\) 有限且非空，则对 \(m\ge3\)，
\[
R_m(X)\cong X
\]
（每个超滤子都是主超滤子）。

### 证明

若 \(X=\varnothing\)，则
\[
\operatorname{Map}(\varnothing,[0])=\{\varnothing\},
\]
但 \([0]=\varnothing\)，故不存在函数
\[
r_0:\operatorname{Map}(\varnothing,[0])\to[0].
\]
所以 \(R_m(\varnothing)=\varnothing\)。

以下设 \(X\ne\varnothing\)。

**\(m=1\)。**  
此时
\[
\operatorname{Map}(X,[0])=\varnothing,\qquad
\operatorname{Map}(X,[1])=\{\text{常值 }0\}.
\]
故 \(r_0\) 是唯一空映射，\(r_1\) 只能取常值 \(0\)。自然性条件唯一满足。

**\(m=2\)。**  
令
\[
c(A)=r_2(f_A).
\]
全体映射 \(X\to[2]\) 都形如 \(f_A\)，所以 \(c\) 决定 \(r_2\)。

对换 \(\sigma:[2]\to[2]\) 给出
\[
c(A^c)=r_2(f_{A^c})
=r_2(\sigma\circ f_A)
=\sigma(r_2(f_A))
=1-c(A).
\]
对常值映射 \(a_0,a_1:[2]\to[2]\)，取 \(f_X\)（常值 \(0\)）：
\[
0=a_0(r_2(f_X))=r_2(a_0\circ f_X)=r_2(f_X)=c(X),
\]
\[
1=a_1(r_2(f_X))=r_2(a_1\circ f_X)=r_2(f_{\varnothing})=c(\varnothing).
\]
所以 \(c(X)=0\)，等价地 \(c(\varnothing)=1\)。

反之，给定满足
\[
c(A^c)=1-c(A),\qquad c(X)=0
\]
的 \(c\)，定义
\[
r_2(f)=c(f^{-1}(0)),\qquad r_1\equiv0,\qquad r_0=\varnothing.
\]
检查 \([2]\to[2]\) 的四个映射以及到 \([1]\) 的映射，即得自然性。因此分类成立。

**\(m\ge3\)。**  
给定 \(r\)，定义
\[
U:=\{A\subseteq X:r_2(f_A)=0\}.
\]
由上一段知 \(X\in U\)，\(\varnothing\notin U\)，且对每个 \(A\)，\(A,A^c\) 中恰有一个属于 \(U\)。

证明 \(U\) 对交封闭。取 \(f:X\to[3]\)，其纤维为
\[
A_0,A_1,A_2.
\]
对任意 \(S\subseteq[3]\)，令 \(a_S:[3]\to[2]\) 为
\[
a_S(j)=
\begin{cases}
0,&j\in S,\\
1,&j\notin S.
\end{cases}
\]
由于
\[
a_S\circ f=f_{\bigcup_{j\in S}A_j},
\]
自然性给出
\[
r_3(f)\in S
\iff
a_S(r_3(f))=0
\iff
r_2(f_{\bigcup_{j\in S}A_j})=0
\iff
\bigcup_{j\in S}A_j\in U.
\tag{1.1}
\]
取 \(S=\{j\}\)，得到
\[
A_j\in U\iff r_3(f)=j.
\]
因此任意三块分割中恰有一块属于 \(U\)。

现在若 \(A,B\in U\)，由 \(\{B,A\setminus B,X\setminus B\}\) 恰有一块属于 \(U\)，知
\[
A\setminus B\notin U,\qquad X\setminus B\notin U.
\]
又由 \(\{A,X\setminus A\}\) 知 \(X\setminus A\notin U\)。于是分割
\[
A\cap B,\quad A\setminus B,\quad X\setminus A
\]
中恰有一块属于 \(U\)，前两块之外的两块都不属于 \(U\)，故
\[
A\cap B\in U.
\]
若 \(A\in U\)，\(A\subseteq B\)，而 \(B\notin U\)，则 \(X\setminus B\in U\)。但 \(A\cap(X\setminus B)=\varnothing\)，与交封闭矛盾。因此 \(B\in U\)。于是 \(U\) 是滤子；结合互补性，\(U\) 是超滤子。

对任意 \(f:X\to[n]\)，\(n\ge2\)，由 (1.1)（用 \(a_S:[n]\to[2]\)）知
\[
f^{-1}(j)\in U\iff r_n(f)=j.
\]
而 \(U\) 是超滤子，故恰有一个 \(j\) 使 \(f^{-1}(j)\in U\)。于是
\[
r_n(f)=\text{唯一满足 }f^{-1}(j)\in U\text{ 的 }j.
\]
所以 \(r=r_U\)。反之，给定超滤子 \(U\)，按此式定义 \(r_U\)，直接检查：
若 \(r_U(f)=j\)，则对任意 \(a:[n]\to[k]\)，
\[
(a\circ f)^{-1}(a(j))
=\bigcup_{i:a(i)=a(j)}f^{-1}(i)\in U,
\]
而其他纤维的并属于 \(U^c\)，故
\[
r_U(a\circ f)=a(j)=a(r_U(f)).
\]
自然性成立。命题得证。

### 有限情形的基数
若 \(X\) 有限且 \(|X|=n\ge1\)，则
\[
|R_2(X)|=2^{n-1}.
\]
事实上，\(\mathcal P(X)\) 中有 \(2^{n-1}\) 对互补子集，而值在每一对上恰由一端决定，\(\varnothing\) 与 \(X\) 那一对由 \(c(X)=0\) 固定方向。

---

## 1.2 遗忘映射 \(q_{m,k}\) 的像与纤维

以下设 \(m\ge k\ge1\)，且 \(m\) 可为 \(\infty\)。

若 \(X=\varnothing\)，则 \(R_m(X)=R_k(X)=\varnothing\)，故 \(q_{m,k}\) 是空映射，像为 \(\varnothing\)，没有纤维。

设 \(X\ne\varnothing\)。

### (a) \(k=1\)
\(R_1(X)\) 是单点集。于是 \(q_{m,1}\) 是到单点集的满射，像是该单点，唯一的非空纤维是 \(R_m(X)\)。

### (b) \(k=2\)
- 若 \(m=2\)，则 \(q_{2,2}\) 是恒等映射，像是 \(R_2(X)\)，各纤维为单点。
- 若 \(m\ge3\)，定义
\[
\theta_2:R_m(X)\longrightarrow R_2(X),\qquad
\theta_2(U)=c_U,\quad
c_U(A)=
\begin{cases}
0,&A\in U,\\
1,&A\notin U.
\end{cases}
\]
则
\[
q_{m,2}(r_U)=c_U.
\]
其像为
\[
\operatorname{Ev}_2(X)
:=\{c_U:U\in\beta X\}.
\]
这恰是那些 \(c\in\mathcal C_2(X)\)，其零族
\[
\mathcal F_c:=\{A\subseteq X:c(A)=0\}
\]
对交封闭的 \(c\)。等价地，\(\mathcal F_c\) 是超滤子。

若 \(c\in\operatorname{Ev}_2(X)\)，则 \(q_{m,2}^{-1}(c)\) 是单点集 \(\{r_U\}\)，其中
\[
U=\mathcal F_c.
\]
若 \(c\notin\operatorname{Ev}_2(X)\)，则纤维为空。

当 \(X\) 有限时，
\[
\operatorname{Ev}_2(X)=\{c_x:x\in X\},
\qquad
c_x(A)=
\begin{cases}
0,&x\in A,\\
1,&x\notin A.
\end{cases}
\]

### (c) \(k\ge3\)
此时 \(m\ge3\)。在同一双射 \(R_m(X)\cong\beta X\)、\(R_k(X)\cong\beta X\) 下，\(q_{m,k}\) 就是恒等映射：
\[
q_{m,k}(r_U)=r_U.
\]
所以它是双射，像为整个 \(R_k(X)\)，每个纤维都是单点。

---

## 1.3 与集合映射 \(h:X\to Y\) 的相容性

直接由定义
\[
(R_m(h)r)_n(f)=r_n(f\circ h)
\]
可得：

1. \(R_m(\mathrm{id}_X)=\mathrm{id}_{R_m(X)}\)。
2. 若 \(h:X\to Y\)，\(k:Y\to Z\)，则
   \[
   R_m(k\circ h)=R_m(k)\circ R_m(h).
   \]
3. 遗忘映射自然：
   \[
   q_{m,k}^{Y}\circ R_m(h)
   =
   R_k(h)\circ q_{m,k}^{X}.
   \]
4. 点值记录自然：
   \[
   R_m(h)(\eta_{m,X}(x))
   =
   \eta_{m,Y}(h(x)).
   \]

在分类下：
- \(m=1\)：所有非空底集都送到唯一点。
- \(m=2\)：
  \[
  (R_2(h)c)(B)=c(h^{-1}B)\qquad(B\subseteq Y).
  \]
  验证：
  \[
  c(h^{-1}B^c)=c(X\setminus h^{-1}B)=1-c(h^{-1}B),
  \]
  且 \(c(h^{-1}Y)=c(X)=0\)。
- \(m\ge3\)：
  \[
  R_m(h)(r_U)=r_{h_*U}.
  \]
  因为
  \[
  (f\circ h)^{-1}(j)=h^{-1}(f^{-1}(j)),
  \]
  所以 \(f^{-1}(j)\in h_*U\iff (f\circ h)^{-1}(j)\in U\)。

---

## 1.4 有限 \(G\)-集合的固定记录

设 \(X\) 是有限 \(G\)-集合。

若 \(X=\varnothing\)，则对所有 \(m\)，
\[
R_m(X)^G=\varnothing.
\]

以下设 \(X\ne\varnothing\)。

### (a) 存在判准与基数

- **\(m=1\)：**
  \[
  |R_1(X)^G|=1.
  \]
  因为 \(G\) 在单点集 \(R_1(X)\) 上作用平凡。

- **\(m=2\)：**
  令 \(H=G\times C_2\)，其中 \(C_2\) 由补集运算
  \[
  \iota(A)=X\setminus A
  \]
  给出。于是 \(H\) 作用在 \(\mathcal P(X)\) 上。

  一个 \(G\)-不动记录 \(c\) 满足
  \[
  c(gA)=c(A),\qquad c(A^c)=1-c(A).
  \]
  若某个非空真子集的 \(G\)-轨道 \(\mathcal O\) 满足
  \[
  \mathcal O^c:=\{A^c:A\in\mathcal O\}=\mathcal O,
  \]
  则不存在这样的 \(c\)，因为 \(c\) 在 \(\mathcal O\) 上为常数，而 \(c(A^c)=1-c(A)\)。

  若不存在这种“自补”的 \(G\)-轨道，则每个 \(H\)-轨道由两个互补的 \(G\)-轨道组成，并且在该 \(H\)-轨道上可以独立选择 \(c\) 为 \(0\) 或 \(1\)（另一端自动相反）。\(H\)-轨道 \(\{\varnothing,X\}\) 的值被 \(c(\varnothing)=1,c(X)=0\) 固定，不贡献因子 \(2\)。

  因此：
  \[
  \boxed{
  R_2(X)^G=\varnothing
  \iff
  \exists A\subseteq X\ \exists g\in G
  \ \bigl(\varnothing\ne A\ne X,\quad gA=X\setminus A\bigr).
  }
  \]
  若上述自补轨道不存在，令 \(N\) 为 \(H\) 在
  \[
  \mathcal P(X)\setminus\{\varnothing,X\}
  \]
  上的轨道数，则
  \[
  |R_2(X)^G|=2^N.
  \]

- **\(m\ge3\)（包括 \(m=\infty\)）：**
  因 \(X\) 有限，
  \[
  R_m(X)\cong\beta X\cong X.
  \]
  主超滤子 \(U_x\) 被 \(G\) 固定当且仅当对一切 \(g\in G\)，\(gx=x\)。因此
  \[
  \boxed{|R_m(X)^G|=|X^G|.}
  \]
  特别地，
  \[
  R_m(X)^G\ne\varnothing\iff X^G\ne\varnothing.
  \]

### (b) 固定集合之间的限制映射

设 \(X\ne\varnothing\)。对 \(m\ge3\)，用
\[
\iota_m:R_m(X)^G\xrightarrow{\ \cong\ }X^G,
\qquad
r_{U_x}\mapsto x
\]
作标准识别。对 \(x\in X^G\)，定义
\[
c_x(A)=
\begin{cases}
0,&x\in A,\\
1,&x\notin A.
\end{cases}
\]

限制映射如下：

\[
\begin{array}{c|c|c|c}
(m,k)&\text{映射}&\text{像}&\text{纤维}\\ \hline
(1,1)&\mathrm{id}_{R_1(X)^G}&\text{单点}&\text{单点}\\
(2,1)&R_2(X)^G\to R_1(X)^G
&\text{若 }R_2(X)^G\ne\varnothing\text{ 则单点，否则 }\varnothing
&\text{若非空则一个纤维}\\
(2,2)&\mathrm{id}_{R_2(X)^G}&R_2(X)^G&\text{单点}\\
(m\ge3,1)&X^G\to R_1(X)^G
&\text{若 }X^G\ne\varnothing\text{ 则单点，否则 }\varnothing
&\text{若非空则 }X^G\\
(m\ge3,2)&X^G\to R_2(X)^G,\ x\mapsto c_x
&\{c_x:x\in X^G\}
&\text{像上单点，像外空}\\
(m\ge k\ge3)&X^G\to X^G,\ x\mapsto x
&X^G&\text{单点}
\end{array}
\]
其中 \(m=\infty\) 归入 \(m\ge3\) 的行。

### (c) 有限层不动记录延拓为完整不动记录的准确范围

由于 \(X\) 有限，
\[
R_\infty(X)^G\cong X^G.
\]
因此 \(q_{\infty,m}\) 的像就是可延拓到完整不动记录的全部有限层记录。

- \(m=1\)：
  \[
  q_{\infty,1}(R_\infty(X)^G)=
  \begin{cases}
  R_1(X)^G,&X^G\ne\varnothing,\\
  \varnothing,&X^G=\varnothing.
  \end{cases}
  \]
  所以唯一的 \(1\)-层不动记录可延拓当且仅当 \(X^G\ne\varnothing\)。

- \(m=2\)：
  \[
  q_{\infty,2}(R_\infty(X)^G)
  =\{c_x:x\in X^G\}.
  \]
  所以一个 \(2\)-层不动记录 \(c\) 可延拓为完整不动记录当且仅当存在 \(x\in X^G\) 使得
  \[
  c(A)=0\iff x\in A\qquad(\forall A\subseteq X).
  \]
  若 \(X^G=\varnothing\)，则 \(R_2(X)^G\) 即使非空，也没有任何记录能延拓到完整层。

- \(m\ge3\)：
  \[
  q_{\infty,m}:R_\infty(X)^G\longrightarrow R_m(X)^G
  \]
  是双射。因此每个 \(m\)-层不动记录都唯一延拓为完整不动记录，且延拓后的完整记录由 \(m\)-层记录对应的那个 \(x\in X^G\) 唯一确定。

特别地，对有限 \(X\)，完整不动记录实际上由任意一个 \(\ge3\) 的有限层记录完全决定；层 \(2\) 只在它恰为某个固定点 \(x\in X^G\) 的点值记录时才延拓；层 \(1\) 唯一记录没有携带固定点信息，因此当且仅当 \(X^G\ne\varnothing\) 时才有某个完整延拓存在。

---

# 二、完整不动记录的空间

## 2.1 内在分类与拓扑

若 \(X=\varnothing\)，则
\[
R_\infty(X)=\varnothing,\qquad R_\infty(X)^G=\varnothing.
\]
以下设 \(X\ne\varnothing\)。

由命题 1.1，
\[
\Phi:\beta X\longrightarrow R_\infty(X),\qquad
U\mapsto r_U
\]
是双射。并且
\[
(g\cdot r_U)=r_{g_*U},\qquad
g_*U=\{gA:A\in U\}.
\]
因此
\[
\boxed{
R_\infty(X)^G
\cong
\{U\in\beta X:g_*U=U\ \forall g\in G\}.
}
\]
这就是由 \(X\) 及其作用直接给出的内在分类：不动记录就是 \(G\)-不变超滤子。

**拓扑相容性。**  
对 \(A\subseteq X\)，令
\[
\widehat A=\{U\in\beta X:A\in U\}.
\]
在 \(R_\infty(X)\) 上，\(\widehat A\) 是观察
\[
r\mapsto r_2(f_A)
\]
取值为 \(0\) 的原像，故是开闭集。反过来，任意观察
\[
r\mapsto r_n(f)
\]
的纤维
\[
\{r:r_n(f)=j\}
=
\{r_U:f^{-1}(j)\in U\}
=
\widehat{f^{-1}(j)}
\]
也是这样的开闭集。因此 \(R_\infty(X)\) 上的观察拓扑正好是 \(\beta X\) 的 Stone 拓扑。限制到不动记录集合后，也就是 \(G\)-不变超滤子上的子空间拓扑。

---

## 2.2 \(R_\infty(X)^G\) 非空的充要条件

先证明一个关键引理。

### 引理 2.1
设 \(T\) 是集合 \(Y\) 上的一个置换，\(V\) 是 \(Y\) 上的 \(T\)-不变超滤子，即 \(T_*V=V\)。则
\[
Y^T\in V.
\]

### 证明
反设 \(Y^T\notin V\)。令
\[
Z=Y\setminus Y^T\in V.
\]
则 \(Z\) 是 \(T\)-不变的，且 \(T|_Z\) 没有不动点。令
\[
V_Z=\{A\subseteq Z:A\in V\}.
\]
这是 \(Z\) 上被 \(T\) 固定的超滤子。我们证明不存在这样的超滤子。

把 \(Z\) 分解为 \(T\)-轨道。对每个轨道 \(O\)，选择一个二染色
\[
a_O:O\to\{0,1\}
\]
如下：
- 若 \(O\) 无限（此时同构于 \(\mathbb Z\)），沿 \(T\)-方向交错染色；
- 若 \(|O|\) 为偶数，沿循环交错染色；
- 若 \(|O|\) 为奇数 \(r\ge3\)，按循环次序染成
  \[
  0,0,1,0,1,\ldots,0,1.
  \]
  这个循环序列没有连续三个同色。

令
\[
A=\{y\in Z:a_O(y)=0\text{ 对 }y\text{ 所在的轨道 }O\}.
\]
则在每个 \(y\in Z\) 处，\(a(y),a(Ty),a(T^2y)\) 不全相同。因此
\[
Z=(A\triangle TA)\cup(A\triangle T^2A).
\tag{2.1}
\]
由于 \(V_Z\) 被 \(T\) 固定，\(A\in V_Z\) 当且仅当 \(TA\in V_Z\)，也当且仅当 \(T^2A\in V_Z\)。于是
\[
A\triangle TA\notin V_Z,\qquad
A\triangle T^2A\notin V_Z.
\]
但两个都不属于超滤子的集合的并不能属于超滤子；而 (2.1) 说其并是 \(Z\in V_Z\)，矛盾。因此 \(Z\notin V\)，从而 \(Y^T\in V\)。引理得证。

### 定理 2.2
对任意 \(G\)-集合 \(X\)，任意超滤子 \(U\in\beta X\)，下列等价：
\[
U\text{ 是 }G\text{-不变的}
\iff
X^g\in U\quad(\forall g\in G).
\]

### 证明
必要性由引理 2.1 直接得到。

反之，若 \(X^g\in U\) 对一切 \(g\in G\)，则对任意 \(A\in U\) 和 \(g\in G\)，
\[
A\cap X^g\in U,
\]
并且
\[
g(A\cap X^g)=gA\cap X^g.
\]
故 \(gA\cap X^g\in U\)，从而 \(gA\in U\)。于是 \(U\subseteq g_*U\)。对 \(g^{-1}\) 使用同一结论得反向包含，故 \(g_*U=U\)。定理得证。

### 推论 2.3
\[
R_\infty(X)^G\ne\varnothing
\]
当且仅当集族
\[
\{X^g:g\in G\}
\]
具有有限交性质；等价地，对每个有限子集 \(F\subseteq G\)，
\[
\bigcap_{g\in F}X^g\ne\varnothing.
\]
又因为
\[
\bigcap_{g\in F}X^g=X^{\langle F\rangle},
\]
所以等价于：
\[
\boxed{
R_\infty(X)^G\ne\varnothing
\iff
X^H\ne\varnothing
\text{ 对每个有限生成子群 }H\le G.
}
\]
特别地，对 \(X=\varnothing\)，条件失败，结论为空。

### 证明
若 \(U\) 是 \(G\)-不变超滤子，则由定理 \(X^g\in U\) 对一切 \(g\) 成立，故任意有限交非空。

反之，若集族 \(\{X^g\}\) 具有有限交性质，它生成一个真滤子，扩张为超滤子 \(U\)。则 \(X^g\in U\) 对一切 \(g\)，由定理 \(U\) 是 \(G\)-不变的。

---

## 2.3 \(\eta_{\infty,X}(X^G)\) 的闭包

对 \(x\in X\)，令
\[
U_x=\{A\subseteq X:x\in A\}
\]
为主超滤子。则
\[
\eta_{\infty,X}(x)=r_{U_x}.
\]
因此 \(\eta_{\infty,X}(X^G)\) 对应
\[
\{U_x:x\in X^G\}.
\]

令
\[
F=X^G.
\]
在 \(\beta X\) 中，\(\{U_x:x\in F\}\) 的闭包是
\[
\widehat F
=
\{U\in\beta X:F\in U\}.
\tag{2.2}
\]
事实上，基本开闭集 \(\widehat A\) 与 \(\{U_x:x\in F\}\) 相交当且仅当 \(A\cap F\ne\varnothing\)。一个超滤子 \(U\) 属于闭包当且仅当它的每个成员都与 \(F\) 相交；这等价于 \(F\in U\)，因为若 \(F\notin U\)，则 \(X\setminus F\in U\)，它与 \(F\) 不交。

所以
\[
\boxed{
\overline{\eta_{\infty,X}(X^G)}
=
\{r_U:F\in U\}.
}
\]
这是 \(R_\infty(X)\) 中的开闭集。

### 推论 2.4
\[
\overline{\eta_{\infty,X}(X^G)}
=
R_\infty(X)^G
\]
当且仅当每个 \(G\)-不变超滤子都含 \(X^G\)。

等价地，当且仅当
\[
\boxed{
\exists\text{ 有限生成子群 }H\le G
\quad\text{使得}\quad
X^H=X^G.
}
\tag{2.3}
\]

### 证明
由 (2.2)，左端是包含 \(X^G\) 的超滤子，右端是包含所有 \(X^g\) 的超滤子。所以等式成立当且仅当由 \(\{X^g:g\in G\}\) 生成的滤子已经含有 \(X^G\)。

一个集合 \(F\) 属于由 \(\{X^g\}\) 生成的滤子，当且仅当存在有限多个 \(g_1,\ldots,g_r\) 使得
\[
X^{g_1}\cap\cdots\cap X^{g_r}\subseteq F.
\]
而
\[
X^{g_1}\cap\cdots\cap X^{g_r}
=
X^{\langle g_1,\ldots,g_r\rangle}.
\]
令 \(H=\langle g_1,\ldots,g_r\rangle\)，则条件就是 \(X^H\subseteq X^G\)。由于总有 \(X^G\subseteq X^H\)，这等价于 \(X^H=X^G\)。

反过来，若 \(X^G\) 不属于该滤子，则由 \(\{X^g\}\cup\{X\setminus X^G\}\) 具有有限交性质，可扩张为超滤子 \(U\)。于是 \(U\) 包含所有 \(X^g\)，故 \(U\in R_\infty(X)^G\)，但 \(X^G\notin U\)，故 \(U\) 不在闭包中。因此 (2.3) 是充要条件。

---

## 2.4 哪些群对每个 \(G\)-集合都满足等式

### 定理 2.5
群 \(G\) 满足
\[
\overline{\eta_{\infty,X}(X^G)}
=
R_\infty(X)^G
\qquad
\text{对每个 }G\text{-集合 }X
\]
当且仅当 \(G\) 是有限生成群。

### 证明
若 \(G\) 有限生成，则对任意 \(X\)，在 (2.3) 中取 \(H=G\) 即可，故等式成立。

反之，设 \(G\) 不是有限生成群。令
\[
\mathcal H
=
\{H\le G:H\text{ 有限生成},\ H\ne G\}.
\]
考虑 \(G\)-集合
\[
X=\coprod_{H\in\mathcal H}G/H,
\]
其中 \(G\) 按左平移作用在每个陪集空间上。

首先，
\[
X^G=\varnothing.
\]
事实上，若 \(x=gH\) 被 \(G\) 固定，则对一切 \(a\in G\)，
\[
agH=gH,
\]
即 \(g^{-1}Gg\subseteq H\)，从而 \(G\subseteq gHg^{-1}=H\)，于是 \(H=G\)，与 \(H\in\mathcal H\) 矛盾。

另一方面，任取有限生成子群 \(K\le G\)，因 \(G\) 不是有限生成群，故 \(K\ne G\)，所以 \(K\in\mathcal H\)。在分量 \(G/K\) 中，陪集 \(K\) 被 \(K\) 逐点固定，故
\[
X^K\ne\varnothing.
\]
由推论 2.3，
\[
R_\infty(X)^G\ne\varnothing.
\]
但 \(X^G=\varnothing\)，故
\[
\overline{\eta_{\infty,X}(X^G)}
=
\overline{\eta_{\infty,X}(\varnothing)}
=
\varnothing
\ne
R_\infty(X)^G.
\]
所以该群不满足全称等式。定理得证。

---

## 2.5 一个可数群、可数底集的具体例子

取
\[
G=\operatorname{FSym}(\omega),
\]
即 \(\omega\) 上具有有限支撑的全体置换；这是可数群。令 \(X\) 为 \(\omega\) 上全体换位（二元子集）的集合：
\[
X=\bigl\{\{a,b\}:a,b\in\omega,\ a\ne b\bigr\}.
\]
\(X\) 可数。令 \(G\) 通过共轭作用在 \(X\) 上：
\[
g\cdot\{a,b\}=\{ga,gb\}.
\]
由于每个 \(g\in G\) 只移动有限多个点，这个作用良定义。

显然
\[
X^G=\varnothing,
\]
因为不存在被所有有限支撑置换固定的换位。

对有限子集 \(S\subset\omega\)，定义
\[
F_S=\{\tau\in X:\operatorname{supp}\tau\cap S=\varnothing\}.
\]
即 \(F_S\) 由支撑完全避开 \(S\) 的换位组成。令 \(\mathcal F\) 为集族 \(\{F_S:S\subset\omega\text{ 有限}\}\) 生成的滤子。由于
\[
F_S\cap F_T=F_{S\cup T}\ne\varnothing,
\]
\(\mathcal F\) 是真自由滤子。

**断言：**
\[
\boxed{
R_\infty(X)^G
=
\left\{
r_U:
U\in\beta X,\quad
F_S\in U\text{ 对每个有限 }S\subset\omega
\right\}.
}
\tag{2.4}
\]

**证明。**  
先设 \(U\) 是扩张 \(\mathcal F\) 的超滤子。对任意 \(g\in G\)，令 \(S=\operatorname{supp}g\)。任何 \(\tau\in F_S\) 的支撑与 \(S\) 不交，故 \(g\tau g^{-1}=\tau\)。于是
\[
F_S\subseteq X^g.
\]
因 \(F_S\in U\)，得 \(X^g\in U\)。由定理 2.2，\(U\) 是 \(G\)-不变的。

反之，设 \(U\) 是 \(G\)-不变超滤子。任取有限 \(S\subset\omega\)，选取有限 \(T\supset S\) 且 \(|T|\ge3\)，并令 \(g\) 为在 \(T\) 上的一个循环置换。则一个换位与 \(g\) 交换当且仅当其支撑与 \(T\) 不交，故
\[
X^g=F_T\subseteq F_S.
\]
由定理 2.2，\(F_T=X^g\in U\)，于是 \(F_S\in U\)。因此 \(U\) 扩张 \(\mathcal F\)。断言得证。

特别地，这个例子满足
\[
X^G=\varnothing,
\qquad
R_\infty(X)^G\ne\varnothing.
\]

（确实非空：例如令
\[
A=\{\{a,b\}:\min(a,b)\text{ 为偶数}\}.
\]
对每个有限 \(S\)，\(A\cap F_S\) 与 \(A^c\cap F_S\) 都非空，因此 \(\mathcal F\cup\{A\}\) 和 \(\mathcal F\cup\{A^c\}\) 都具有有限交性质，可分别扩张为 \(G\)-不变超滤子。于是不动记录不止一个。）

---

# 三、乘积比较

设 \((X_i)_{i\in I}\) 是一族 \(G\)-集合，乘积取对角作用：
\[
g\cdot(x_i)_{i\in I}=(gx_i)_{i\in I}.
\]
记
\[
X=\prod_{i\in I}X_i,\qquad p_i:X\to X_i
\]
为投影。

---

## 3.1 良定义与连续性

映射
\[
\Pi_{(X_i)}:R_\infty(X)^G
\longrightarrow
\prod_{i\in I}R_\infty(X_i)^G,
\qquad
r\longmapsto(R_\infty(p_i)r)_{i\in I}
\]
是良定义的。事实上，若 \(r\) 被 \(G\) 固定，则
\[
R_\infty(g_{X_i})R_\infty(p_i)r
=
R_\infty(g_{X_i}\circ p_i)r
=
R_\infty(p_i\circ g_X)r
=
R_\infty(p_i)R_\infty(g_X)r
=
R_\infty(p_i)r.
\]
故每个分量都是 \(G\)-不变的。

连续性：每个
\[
R_\infty(p_i):R_\infty(X)\to R_\infty(X_i)
\]
在观察拓扑下连续，因为基本观察
\[
R_\infty(X_i)\ni s\mapsto s_n(f)\in[n]
\]
拉回为
\[
R_\infty(X)\ni r\mapsto r_n(f\circ p_i)\in[n],
\]
仍是基本观察。目标取乘积拓扑，故 \(\Pi_{(X_i)}\) 连续。

若空指标族 \(I=\varnothing\)，则 \(\prod_{i\in I}X_i\) 是单点集，\(R_\infty(\text{单点})^G\) 是单点集，目标也是单点集，映射是双射。

---

## 3.2 满射性

### 定理 3.1
对任意群 \(G\)、任意集合指标族 \((X_i)_{i\in I}\)，比较映射
\[
\Pi_{(X_i)}:R_\infty(X)^G
\longrightarrow
\prod_{i\in I}R_\infty(X_i)^G
\]
总是满射。

特别地，它不要求指标族有限，也不要求各 \(X_i\) 非空；空底集和空指标族的情形按上面的约定处理。

### 证明
若 \(I=\varnothing\)，已见是双射。

若某个 \(X_i=\varnothing\)，则 \(X=\prod X_i=\varnothing\)，且目标中因子
\[
R_\infty(X_i)^G=R_\infty(\varnothing)^G=\varnothing,
\]
故目标为空，定义域也为空，空映射是满射。

以下设所有 \(X_i\ne\varnothing\)。任取目标元素
\[
(r_i)_{i\in I}\in\prod_i R_\infty(X_i)^G.
\]
由分类，存在超滤子 \(U_i\in\beta X_i\)，使得 \(r_i=r_{U_i}\)。每个 \(U_i\) 都是 \(G\)-不变的。

令
\[
\mathcal C
=
\left\{
\bigcap_{j\in J}p_j^{-1}(A_j):
J\subseteq I\text{ 有限},\ A_j\in U_j
\right\}.
\]
这是 \(X\) 上的真滤子：有限交仍是这种形式，且非空，因为每个 \(A_j\ne\varnothing\)，其余坐标的集合也非空。

令
\[
L=\{U\in\beta X:(p_i)_*U=U_i\ \forall i\in I\}.
\]
则 \(L\ne\varnothing\)，且是 \(\beta X\) 中的非空紧致闭子集；\(G\) 在 \(L\) 上作用，因为所有的 \(U_i\) 都是 \(G\)-不变的。

我们证明对每个有限生成子群 \(H\le G\)，\(L^H\ne\varnothing\)。设 \(H\) 由 \(h_1,\ldots,h_s\) 生成。因 \(U_i\) 被 \(G\) 固定，由定理 2.2，
\[
X_i^{h_1},\ldots,X_i^{h_s}\in U_i,
\]
故
\[
F_i:=X_i^H\in U_i.
\]
令 \(U_i^H\) 为 \(U_i\) 在 \(F_i\) 上的迹：
\[
U_i^H=\{A\subseteq F_i:A\in U_i\}.
\]
这是 \(F_i\) 上的超滤子。对所有 \(i\)，取 \(\prod_i F_i\) 上的一个超滤子 \(W_H\)，使得
\[
(p_i)_*W_H=U_i^H\qquad(\forall i).
\]
这样的 \(W_H\) 存在：由所有有限柱形
\[
\bigcap_{j\in J}p_j^{-1}(A_j),
\qquad A_j\in U_j^H
\]
生成的滤子具有有限交性质，扩张为超滤子即可。

把 \(W_H\) 扩张为 \(X=\prod_iX_i\) 上的超滤子，仍记为 \(W_H\)，使其含有 \(\prod_iF_i\)。则 \(W_H\) 的每个投影是 \(U_i\)，故 \(W_H\in L\)。又因 \(H\) 在 \(\prod_iF_i\) 上逐点作用平凡，故 \(W_H\) 被 \(H\) 固定。因此 \(L^H\ne\varnothing\)。

于是 \(\{L^H:H\le G\text{ 有限生成}\}\) 是一族非空紧致闭集。若 \(H_1,\ldots,H_r\) 有限生成，则
\[
\langle H_1,\ldots,H_r\rangle
\]
仍有限生成，且
\[
L^{\langle H_1,\ldots,H_r\rangle}
\subseteq
\bigcap_{j=1}^rL^{H_j}.
\]
故该族具有有限交性质。由 \(L\) 的紧致性，
\[
\bigcap_{H\text{ 有限生成}}L^H\ne\varnothing.
\]
取其中的 \(U\)。对任意 \(g\in G\)，\(\langle g\rangle\) 有限生成，故 \(U\) 被 \(g\) 固定。于是 \(U\in L^G\)，且
\[
(p_i)_*U=U_i\qquad(\forall i).
\]
所以
\[
\Pi_{(X_i)}(r_U)=(r_{U_i})_{i\in I}=(r_i)_{i\in I}.
\]
满射性得证。

---

## 3.3 平凡群时两因子比较映射的单射性

取 \(G\) 为平凡群。此时固定记录就是全部记录，
\[
\Pi:R_\infty(X\times Y)\to R_\infty(X)\times R_\infty(Y)
\]
在超滤子语言下就是标准映射
\[
\Pi:\beta(X\times Y)\to\beta X\times\beta Y,
\qquad
U\mapsto((p_X)_*U,(p_Y)_*U).
\]

### 定理 3.2
对平凡群，\(\Pi\) 是单射当且仅当
\[
\boxed{X\text{ 或 }Y\text{ 有限}.}
\]
（空集按有限集处理。）

### 证明
若 \(X=\varnothing\) 或 \(Y=\varnothing\)，定义域和目标都为空，空映射是单射。

以下设 \(X,Y\ne\varnothing\)。

若 \(X\) 有限，则
\[
X\times Y=\coprod_{x\in X}\bigl(\{x\}\times Y\bigr).
\]
有限不交并的 Stone–Čech 紧化就是各块紧化的不交并：
\[
\beta(X\times Y)
\cong
\coprod_{x\in X}\beta(\{x\}\times Y)
\cong
\coprod_{x\in X}\beta Y.
\]
而
\[
\beta X\times\beta Y
\cong
X\times\beta Y
\cong
\coprod_{x\in X}\beta Y,
\]
标准映射在每个块上是恒等。因此它是双射，特别地是单射。\(Y\) 有限时同理。

反之，设 \(X,Y\) 都无限。取可数无限子集
\[
X_0=\{x_n:n<\omega\}\subseteq X,\qquad
Y_0=\{y_n:n<\omega\}\subseteq Y.
\]
取 \(\omega\) 上的非主超滤子 \(p_0,q_0\)，并定义
\[
p=\{A\subseteq X:\{n:x_n\in A\}\in p_0\},
\]
\[
q=\{B\subseteq Y:\{n:y_n\in B\}\in q_0\}.
\]
则 \(p,q\) 分别是 \(X,Y\) 上的非主超滤子。

令
\[
\Delta=\{(x_n,y_n):n<\omega\}\subseteq X\times Y.
\]
考虑柱形滤子
\[
\mathcal C=\{A\times B:A\in p,\ B\in q\}.
\]
它具有有限交性质，因为 \(A,B\) 都无限，\(A\cap X_0\) 与 \(B\cap Y_0\) 无限，故存在 \(n\) 使 \(x_n\in A\)、\(y_n\in B\)。

并且 \(\mathcal C\cup\{\Delta\}\) 与 \(\mathcal C\cup\{(X\times Y)\setminus\Delta\}\) 都具有有限交性质：
- 对 \(A\times B\)，
  \[
  (A\times B)\cap\Delta\ne\varnothing
  \]
  因为可取同一个 \(n\) 使 \(x_n\in A\)、\(y_n\in B\)；
- 同时 \(A\times B\not\subseteq\Delta\)，故
  \[
  (A\times B)\cap\bigl((X\times Y)\setminus\Delta\bigr)\ne\varnothing.
  \]

分别扩张为超滤子 \(U_+,U_-\)。二者都包含 \(\mathcal C\)，故在 \(X\) 与 \(Y\) 上的投影都是 \(p,q\)。但
\[
\Delta\in U_+,\qquad
\Delta\notin U_-,
\]
所以 \(U_+\ne U_-\)。在平凡群下，二者都是记录，故 \(\Pi\) 不是单射。

---

## 3.4 两个全称命题的判定

### 命题 3.3
**命题 (i)：若 \(X,Y\) 中至少一个有限，则两因子比较映射为双射。**

这个命题对任意群作用都为真。

**证明。**  
满射性由定理 3.1。

单射性：无群作用时，底层集合映射
\[
\beta(X\times Y)\to\beta X\times\beta Y
\]
在 \(X\) 或 \(Y\) 有限时是单射（定理 3.2 的证明）。带群作用时，比较映射
\[
R_\infty(X\times Y)^G
\to
R_\infty(X)^G\times R_\infty(Y)^G
\]
正是上述无群作用映射限制在固定点子空间上。由于大映射已经是单射，其限制也单射。

若 \(X\) 或 \(Y\) 为空，则两边都为空，空映射是双射。

因此 (i) 成立。

---

### 命题 3.4
**命题 (ii)：若 \(X^G=Y^G=\varnothing\)，则两因子比较映射为单射。**

这个命题对任意群作用 **不真**。

**反例。**  
取 2.5 中的例子：
\[
G=\operatorname{FSym}(\omega),
\qquad
X=\{\text{\(\omega\) 上的换位}\},
\]
\(G\) 按共轭作用在 \(X\) 上。我们已经知道
\[
X^G=\varnothing,
\qquad
R_\infty(X)^G\ne\varnothing.
\]
取定一个 \(G\)-不变超滤子 \(U\in\beta X\)，即 \(r_U\in R_\infty(X)^G\)。并且由 2.5 知道 \(U\) 非主：若 \(U\) 含有有限集，则含有某个单点 \(\{\tau\}\)，即 \(U\) 是主超滤子，而主超滤子不可能在 \(X^G=\varnothing\) 时被 \(G\) 固定。

令 \(Y=X\)，乘积取对角作用。设
\[
\Delta=\{(\tau,\tau):\tau\in X\}\subseteq X\times X.
\]
注意 \(\Delta\) 是 \(G\)-不变的。

令 \(\mathcal C\) 为由
\[
A\times B,\qquad A,B\in U
\]
生成的柱形滤子。它非空、真，并且 \(G\)-不变。令
\[
L=\{W\in\beta(X\times X):(p_1)_*W=U,\ (p_2)_*W=U\}.
\]
这是非空紧致 \(G\)-不变集合。

对每个有限生成子群 \(H\le G\)，令
\[
F=X^H.
\]
因 \(U\) 是 \(G\)-不变的，由定理 2.2，\(F\in U\)。迹
\[
U_F=\{A\subseteq F:A\in U\}
\]
是 \(F\) 上的非主超滤子。于是 \(F\) 无限。

在 \(F\times F\) 上取乘积超滤子
\[
V_H=U_F\otimes U_F,
\]
即
\[
V_H=\left\{C\subseteq F^2:\{x\in F:C_x\in U_F\}\in U_F\right\},
\]
其中 \(C_x=\{y\in F:(x,y)\in C\}\)。它满足两个投影都是 \(U_F\)，并且因 \(H\) 在 \(F\) 上逐点作用平凡，\(V_H\) 被 \(H\) 固定。

并且 \(V_H\cup\{\Delta\cap(F\times F)\}\) 具有有限交性质：对 \(A,B\in U_F\)，因二者都无限，
\[
(A\times B)\cap(\Delta\cap(F\times F))
=
\{(x,x):x\in A\cap B\}
\]
非空。类似地，\(V_H\cup\{((F\times F)\setminus\Delta)\}\) 也具有有限交性质，因为 \(A,B\) 无限保证 \(A\times B\) 中有对角线以外的点。

把相应的超滤子由 \(F\times F\) 扩张到 \(X\times X\)，使其含有 \(F\times F\)。这样得到 \(L\) 中的 \(H\)-不动点，一个含 \(\Delta\)，一个含 \(\Delta^c\)。

于是对每个有限生成 \(H\)，\(L^H\) 与“含 \(\Delta\) 的 \(L^H\)”及“含 \(\Delta^c\) 的 \(L^H\)”都非空。由与定理 3.1 相同的紧致性/有限交性质论证，存在 \(G\)-不变超滤子
\[
W_+,\ W_-\in\beta(X\times X)
\]
使得
\[
(p_1)_*W_\pm=(p_2)_*W_\pm=U,
\]
但
\[
\Delta\in W_+,\qquad
\Delta^c\in W_-.
\]
因此 \(W_+\ne W_-\)，然而
\[
\Pi(r_{W_+})=(r_U,r_U)=\Pi(r_{W_-}).
\]
所以两因子比较映射不是单射。

---

# 结论汇总

1. **截断分类：**
   \[
   R_m(\varnothing)=\varnothing;
   \]
   对 \(X\ne\varnothing\)，
   \[
   R_1(X)\cong 1,\qquad
   R_2(X)\cong \mathcal C_2(X),\qquad
   R_m(X)\cong\beta X\quad(m\ge3,\ m=\infty).
   \]
   \(q_{m,k}\) 的像和纤维由三层次分类直接给出：到 \(1\)-层的所有纤维是全集；到 \(2\)-层在 \(m\ge3\) 时像为超滤子限制，纤维至多单点；到 \(k\ge3\) 层是双射。有限 \(G\)-集的 \(R_m(X)^G\) 的基数分别为 \(1\)、由互补轨道计数给出的 \(2^N\) 或 \(0\)、以及 \(|X^G|\)。有限层延拓到完整层的精确范围由 \(q_{\infty,m}\) 的像给出：\(m=1\) 需 \(X^G\ne\varnothing\)，\(m=2\) 需记录为某个 \(x\in X^G\) 的点值记录，\(m\ge3\) 时全部唯一延拓。

2. **完整层：**
   \[
   R_\infty(X)^G\cong \{U\in\beta X:U\text{ 是 }G\text{-不变超滤子}\}.
   \]
   非空当且仅当每个有限生成子群都有不动点。且
   \[
   \overline{\eta_{\infty,X}(X^G)}
   =
   \{U:X^G\in U\},
   \]
   等于 \(R_\infty(X)^G\) 当且仅当存在有限生成 \(H\le G\) 使 \(X^H=X^G\)。所有 \(G\)-集合都满足该等式的群恰好是有限生成群。可数反例为 \(G=\operatorname{FSym}(\omega)\) 共轭作用在全体换位集合上，其全部不动记录由 (2.4) 精确描述。

3. **乘积比较：**
   映射 \(\Pi_{(X_i)}\) 对任意群和任意指标族都良定义、连续，并且总是满射。对平凡群，两因子映射为单射当且仅当至少一个底集有限。命题 (i) 对任意群作用为真；命题 (ii) 为假，上述共轭换位例子给出了两个不同的不变记录具有相同两个投影的明确构造。