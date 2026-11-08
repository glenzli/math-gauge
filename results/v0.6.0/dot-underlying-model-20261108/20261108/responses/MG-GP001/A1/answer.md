# S1 可缩子复形的商

设 (q:Y\to Y/A) 为商映射，取 (a_0\in A)，以及收缩
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
CW 子复形的包含 (A\hookrightarrow Y) 是 cofibration，具有同伦延拓性质。因此 (h) 与 (\operatorname{id}_Y\) 可延拓为
\[
H:Y\times I\longrightarrow Y,\qquad H(y,0)=y,\quad H|_{A\times I}=h.
\]
因为 (H_1) 在 (A) 上恒为 (a_0)，它唯一地通过商空间分解为连续映射
\[
f:Y/A\longrightarrow Y,\qquad fq=H_1.
\]
故 (fq\simeq\operatorname{id}_Y)。

还须检查另一侧的同伦确实能下降。对每个 (t)，有 (H(A,t)\subseteq A)，因而 (qH(a,t)=*) 与 (a\in A) 无关。所以
\[
\overline H([y],t)=qH(y,t)
\]
定义良好且连续。连续性可由 (q\times\operatorname{id}_I) 是商映射得到：这里 (Y) 是紧 Hausdorff 空间，(A) 是闭子复形，(Y/A) 是 Hausdorff 空间，故该乘积映射是紧空间到 Hausdorff 空间的连续满射，因而是商映射。于是
\[
\overline H_0=\operatorname{id}_{Y/A},\qquad \overline H_1=qf.
\]
这证明 (q) 是同伦等价。关键不是任意同伦都能下降，而是所构造的同伦始终把整个 (A) 映入 (A)。

# S2 非可缩底空间上的锥附着

记包含映射为 (i:L\to D)。选取它的零伦
\[
F:L\times I\longrightarrow D,\qquad F(l,0)=i(l),\quad F(l,1)=d_0.
\]
令 (c:L\to D) 为常值映射 (d_0)。空间 (Y) 就是映射锥 (C_i)。同伦的附着映射有同伦等价的映射锥，且可使等价在 (D) 上为恒等，因此
\[
Y=C_i\simeq C_c.
\]
这里使用的是映射锥的同伦不变性，适用于本题的 CW 空间及连续映射。具体地，把映射锥的坐标写成 ([l,t])，其中 (t=0) 为附着端、(t=1) 为锥顶，映射 (C_i\to C_c) 在 (D) 上取恒等，在锥上取
\[
[l,t]\longmapsto
\begin{cases}
F(l,2t),&0\le t\le\tfrac12,\\
[l,2t-1],&\tfrac12\le t\le1.
\end{cases}
\]
反向映射用逆向同伦 (F(l,1-t)) 同样构造。两个复合分别对应于先走 (F) 再原路返回，或先逆向走再返回，并附带锥坐标的重参数化。这些往返同伦相对两端收缩为常同伦，锥坐标也可重参数化回恒等，故两个复合均同伦于恒等。

在 (C_c) 中，锥的整个底面 (L\times\{0\}) 被识别到 (d_0)，而锥顶是另一个点。因此
\[
C_c\cong D\vee_{d_0,s}\Sigma L,
\]
其中
\[
\Sigma L=(L\times I)/(L\times\{0\}\text{ 合为一点 }s,\ L\times\{1\}\text{ 合为另一点 }n)
\]
是非约化悬挂，楔点是其南极 (s) 与 (D) 中的 (d_0)。于是 (Y\simeq D\vee\Sigma L)。

由于 (D) 路径连通，可以在零伦末尾接上一条从 (d_0) 到任意指定点 (d\in D) 的路径，使零伦终点改为 (d)。特别可以选择 (D) 的一个顶点为楔点。以上论证并不要求 (L) 连通，但其零伦必须终止于一个共同的常值点，这正是题设的零伦条件。

# S3 整数扭结的实例

给定题中的有限三角剖分 (L)，加入两个新顶点 (v,w)，令
\[
K=L*\{v,w\}=(v*L)\cup_L(w*L),
\]
其中 ({v,w}) 表示只有两个顶点而没有边的复形。取 (L) 的任一顶点 (a)，令 (B) 是边 ({v,a}) 及其所有面的子复形。

删除顶点 (v) 后的诱导子复形是 (w*L)。几何空间 (|K|\setminus\{v\}) 强形变收缩到 (|w*L|)：对重心坐标为 ((t_u)) 的点，把 (v) 的坐标归零，再把其余坐标除以 (1-t_v)，并在原点与所得点之间作直线同伦。这里 (t_v<1)，同伦始终留在原单形且不经过 (v)。故穿孔空间非空可缩。

另一方面，(|B|) 是闭区间，而 (|B|\setminus\{v\}) 是半开区间，二者都非空可缩。因此其包含映射是同伦等价。

最后，(|K|\cong\Sigma|L|\cong\Sigma\mathbb{RP}^2)。整数约化同调为
\[
\widetilde H_j(|K|;\mathbb Z)\cong
\begin{cases}
\mathbb Z/2,&j=2,\\
0,&j\ne2.
\end{cases}
\]
这是由悬挂同构和 (\widetilde H_1(\mathbb{RP}^2;\mathbb Z)=\mathbb Z/2) 得到的。故所有约化有理同调均为零，但 (|K|) 不可缩。

# S4 整体对象与全部恢复目标

所有目标均成立。精确分类为：

**可能的 (X) 的同伦类型，恰好是所有非空有限单纯复形的非约化悬挂的同伦类型。**

只用题目允许的局部关联数据的可缩性判据是：

**顶点链接 (\operatorname{lk}_K(v)) 的所有约化整数同调群均为零。**

下面证明分类、全部实现以及判据。

## 1. 从穿孔空间到删除复形

定义删除复形与链接
\[
D=\{\sigma\in K:v\notin\sigma\},\qquad
L=\operatorname{lk}_K(v)
 =\{\tau\in D:\tau\cup\{v\}\in K\}.
\]
有复形分解
\[
K=D\cup(v*L),\qquad D\cap(v*L)=L.
\]

如 S3 的重心坐标构造所示，(O) 强形变收缩到 (|D|)。更明确地，令
\[
r(x)_v=0,\qquad r(x)_u=\frac{t_u(x)}{1-t_v(x)}\quad(u\ne v),
\]
以及 (R_s(x)=(1-s)x+sr(x))。它连续、固定 (|D|)，且在 (O) 中给出所需强形变收缩。因此 (|D|) 非空可缩。

## 2. (B) 的假设排除了空链接

如果 (|L|=\varnothing)，则没有任何正维单形包含 (v)，所以 (v) 是 (X) 的孤立点。由于 (B) 含 (v)，({v}) 也是 (C) 的一个路径分支，而 (O\cap C\to C) 的像遗漏这一分支。它不可能诱导路径分支集合上的双射，故不可能是同伦等价。

因此原假设保证 (|L|\ne\varnothing)。

## 3. 分类的必要性

对可缩非空子复形 (|D|\subseteq X) 应用 S1，得
\[
X\simeq X/|D|.
\]
由上述锥分解以及 (L) 非空，商空间恰为
\[
X/|D|\cong |v*L|/|L|\cong\Sigma|L|.
\]
这里 (|D|) 被压成悬挂的一个极点，(v) 是另一个极点。这证明了分类的必要性。也可以对 (|D|\cup_{|L|}C|L|) 应用 S2，因为 (|D|) 可缩，包含 (|L|\to|D|) 自动零伦。

## 4. 每一种类型的实现

反过来，给定任意非空有限单纯复形 (M)，取新顶点 (v,w)，置
\[
K=M*\{v,w\}.
\]
选择 (M) 的一个顶点 (a)，取 (B) 为边 ({v,a}) 及其面。则：

- (|K|\cong\Sigma|M|)；
- (|K|\setminus\{v\}) 强形变收缩到非空可缩的锥 (|w*M|)；
- (|B|\setminus\{v\}\hookrightarrow|B|) 是两个非空可缩空间之间的映射，因而是同伦等价。

故分类列出的每种类型都满足原条件。特别地，(B) 的存在并未进一步限制非空链接能具有的同伦型：对任何包含 (v) 的边，把该边取为 (B) 就满足有关 (B) 的条件。

## 5. 局部整数同调判据

对非空有限复形 (L)，悬挂同构给出
\[
\widetilde H_{n+1}(\Sigma|L|;\mathbb Z)
\cong\widetilde H_n(|L|;\mathbb Z)\qquad(n\ge0).
\]
若 (X) 可缩，由 (X\simeq\Sigma|L|) 立即得出 (|L|) 的所有约化整数同调群均为零。

反之，假设这些群都为零。由 (\widetilde H_0(|L|;\mathbb Z)=0) 及非空性，有限复形 (|L|) 路径连通。因此其悬挂单连通：用删除北极与删除南极所得的两个开集覆盖悬挂，它们均可缩，交集同伦等价于路径连通的 (|L|)，van Kampen 定理给出平凡基本群。悬挂同构又说明该悬挂整数无环。

一个单连通、整数无环的 CW 复形必可缩。事实上，若有非零高阶同伦群，取最小的 (n\ge2)，Hurewicz 定理给出
\[
\pi_n\cong H_n=0,
\]
矛盾。因此所有同伦群为零，映射到一点是弱同伦等价，Whitehead 定理将其提升为同伦等价。故 (\Sigma|L|)，进而 (X)，可缩。

最后说明判据确实只用指定的局部数据。每个包含 (v) 的单形 (sigma
e\{v\}) 对应链接单形 (sigma\setminus\{v\})，它们的面关联也由这些单形及其面的关联数据确定。于是可恢复 (L) 的有限增广单纯链复形
\[
\cdots\longrightarrow C_1(L;\mathbb Z)
\longrightarrow C_0(L;\mathbb Z)
\xrightarrow{\varepsilon}\mathbb Z\longrightarrow0.
\]
任选顶点次序写出整数边界矩阵，用整数矩阵算法（例如 Smith 标准形及整数核、像计算）检验该有限链复形是否正合，即可判定所有约化整数同调是否为零。这是有限且可检验的充要条件，不使用 (K) 远离 (v) 的任何单形。S3 同时说明不能把“整数同调”换成“有理同调”。

# S5 不提供子复形 (B)

**不必。新增的可能类型恰好只有离散两点空间 (S^0) 的同伦类型。**

仍令 (D) 为删除复形、(L) 为链接。穿孔空间强形变收缩到非空可缩的 (|D|)，这不使用 (B)。

- 若 (|L|\ne\varnothing)，S4 中压缩 (|D|) 的论证照样成立，故 (X\simeq\Sigma|L|)。这些类型均已由 S4 的构造实现。
- 若 (|L|=\varnothing)，则 (v) 是孤立点，且
  \[
  X=|D|\amalg\{v\}\simeq\{*,v\}=S^0.
  \]

后一类型确实出现：令 (K) 只有两个孤立顶点 (v,w)，则 (X\setminus\{v\}=\{w\}) 非空可缩，而 (X=S^0)。任何非空空间的非约化悬挂都是路径连通的，因此 (S^0) 不可能同伦等价于题目所说的非空有限复形的悬挂。这也证明没有其他新增类型。

# S6 悬挂信息的逆向恢复

**不能推出。** 取有限单纯复形 (L_1,L_2) 分别实现
\[
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
二者都有有限三角剖分：环面是紧多面体；第二个空间可把三个分别三角剖分的空间在一个顶点处粘合。

下面证明它们的非约化悬挂同伦等价。先用约化悬挂 (Sigma_r) 计算。环面有基于顶点的 CW 表示
\[
T^2=(S^1\vee S^1)\cup_f e^2,
\]
其中 (f:S^1\to S^1\vee S^1) 为交换子附着映射，代表 (aba^{-1}b^{-1})。约化悬挂保持同伦余纤维，因此 (Sigma_rT^2) 同伦等价于
\[
\Sigma_rf:S^2\longrightarrow S^2\vee S^2
\]
的映射锥。此处所有空间都是以零胞腔为基点的 CW 复形，故可使用通常的基点映射锥及悬挂的同伦余纤维性质。

交换子的指数和均为零，所以 (f) 在 (H_1) 上诱导零映射。由悬挂同构的自然性，(Sigma_rf) 在 (H_2) 上也诱导零映射。而 (S^2\vee S^2) 单连通，Hurewicz 同构为
\[
\pi_2(S^2\vee S^2)\xrightarrow{\cong}H_2(S^2\vee S^2;\mathbb Z).
\]
故 (Sigma_rf) 零伦。常值映射的映射锥给出
\[
\Sigma_rT^2\simeq S^2\vee S^2\vee S^3.
\]
另一方面，约化悬挂与有限楔和交换，所以
\[
\Sigma_r(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]

这些计算同样适用于题目中的非约化悬挂：选基点为一个顶点，则在非约化悬挂中，该基点的悬挂弧是非空可缩子复形。将这条弧压成一点得到约化悬挂，由 S1 此商映射是同伦等价。因此
\[
\Sigma|L_1|\simeq S^2\vee S^2\vee S^3\simeq\Sigma|L_2|.
\]
但
\[
\pi_1(|L_1|)\cong\mathbb Z^2,\qquad
\pi_1(|L_2|)\cong F_2,
\]
前者交换而后者不交换，二者不同构，所以 (|L_1|\not\simeq|L_2|)。这给出了满足全部前提的反例。
