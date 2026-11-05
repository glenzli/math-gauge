FULL

以下用“几何非空”表示单纯复形至少有一个顶点。这样即使采用包含空面的约定，仅含空面的复形也不会被误认为有非空几何实现。悬挂 \(\Sigma Z\) 均指非约化悬挂。

## S1 可缩子复形的商

设 \(q:Y\to Y/A\) 是商映射，取 \(A\) 的收缩
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
因为 \((Y,A)\) 是 CW 对，包含 \(A\hookrightarrow Y\) 具有同伦延拓性质。故 \(h\) 可延拓为
\[
G:Y\times I\longrightarrow Y,\qquad
G(y,0)=y,\quad G(a,t)=h(a,t).
\]
于是每个 \(G_t\) 都把 \(A\) 映入 \(A\)，且 \(G_1(A)=\{a_0\}\)。因此 \(G_1\) 通过 \(q\) 分解为连续映射
\[
r:Y/A\longrightarrow Y,\qquad r([y])=G_1(y).
\]
这给出 \(rq=G_1\simeq\operatorname{id}_Y\)。

同伦 \(G\) 也能下降到商：定义
\[
\overline G([y],t)=[G(y,t)].
\]
由于 \(G_t(A)\subseteq A\)，此式良定义。有限 CW 复形 \(Y\) 紧 Hausdorff，子复形 \(A\) 闭，故 \(Y/A\) 也是紧 Hausdorff 空间。因此
\[
q\times\operatorname{id}_I:Y\times I\to(Y/A)\times I
\]
是闭满射，从而是商映射；这证明 \(\overline G\) 连续。它给出
\[
\operatorname{id}_{Y/A}\simeq qr.
\]
所以 \(q\) 是同伦等价。

## S2 非可缩底空间上的锥附着

先证明所需的映射锥同伦不变性。对映射 \(f:L\to D\)，写
\[
C_f=\bigl(D\sqcup(L\times I)\bigr)/
\bigl((x,0)\sim f(x),\ L\times\{1\}\text{ 压为一点}\bigr).
\]
若 \(H:L\times I\to D\) 是从 \(f\) 到 \(g\) 的同伦，定义 \(F_H:C_f\to C_g\) 在 \(D\) 上为恒等，并在锥上令
\[
F_H([x,t])=
\begin{cases}
H(x,2t),&0\le t\le \frac12,\\
[x,2t-1]_g,&\frac12\le t\le1.
\end{cases}
\]
两式在 \(t=\frac12\) 处均等于 \(g(x)\)，所以映射连续。反向同伦 \(\bar H(x,t)=H(x,1-t)\) 给出 \(F_{\bar H}:C_g\to C_f\)。

这两个映射互为同伦逆。例如，\(F_{\bar H}F_H\) 在锥上先沿 \(H\) 前进、再沿 \(H\) 返回，最后进入原锥。把前进和返回所经过的 \(H\)-参数同时缩至零，就得到在锥的初始一段恒为 \(f(x)\)、其余一段进入原锥的映射；再线性调整锥参数，即得到恒等映射。这些同伦均固定 \(D\)，且在锥顶良定义。另一复合同理。

现在取 \(d_0\in D\)，例如取一个顶点。题设给出包含映射 \(L\hookrightarrow D\) 到某常值映射的同伦；由于 \(D\) 路径连通，再接上一条路径，可将常值点改为 \(d_0\)。所以
\[
Y\simeq C_{c_{d_0}}.
\]
后者正是把 \(\Sigma L\) 的一个悬挂极点与 \(D\) 中的 \(d_0\) 粘合所得空间。因此
\[
\boxed{Y\simeq D\vee\Sigma L.}
\]
楔点在 \(D\) 中选为 \(d_0\)，在 \(\Sigma L\) 中选为被粘到 \(d_0\) 的悬挂极点。

## S3 整数扭结的实例

先给出一个变形收缩，供本题及后面使用。对有限单纯复形 \(K\) 和顶点 \(v\)，令
\[
K-v=\{\sigma\in K:v\notin\sigma\}.
\]
则 \(|K|\setminus\{v\}\) 强变形收缩到 \(|K-v|\)。确切地，若
\[
x=\sum_w t_w w\ne v,
\]
定义
\[
r(x)=\sum_{w\ne v}\frac{t_w}{1-t_v}w,\qquad
H(x,s)=(1-s)x+s\,r(x).
\]
同伦始终留在含 \(x\) 的单形内，也始终避开 \(v\)，并固定 \(|K-v|\)。若 \(x\) 在含 \(v\) 的子复形 \(|B|\) 中，此同伦也留在 \(|B|\) 中。

现在取题给的 \(\mathbb{RP}^2\) 的有限单纯三角剖分 \(L\)，另取新顶点 \(u,v\)，令
\[
K=(u*L)\cup(v*L).
\]
选 \(L\) 的一个顶点 \(w\)，令 \(B\) 为边 \(\{v,w\}\) 及其所有面的子复形。

- \(K-v=u*L\) 是非空锥，故 \(|K|\setminus\{v\}\) 非空可缩。
- \(|B|\) 和 \(|B|\setminus\{v\}\) 都沿边线性收缩到 \(w\)。因此包含 \(|B|\setminus\{v\}\to|B|\) 是同伦等价；其同伦逆可取为到 \(w\) 的常值映射。
- 两个锥沿公共底 \(L\) 粘合，故
  \[
  |K|\cong\Sigma|L|\cong\Sigma\mathbb{RP}^2.
  \]

\(\mathbb{RP}^2\) 的标准胞腔链复形在正维的非零边界为
\[
\mathbb Z\xrightarrow{\;2\;}\mathbb Z.
\]
因此 \(\widetilde H_*(\mathbb{RP}^2;\mathbb Q)=0\)，而
\[
H_1(\mathbb{RP}^2;\mathbb Z)\cong\mathbb Z/2.
\]
由悬挂同调公式，
\[
\widetilde H_*(|K|;\mathbb Q)=0,\qquad
\widetilde H_2(|K|;\mathbb Z)\cong\mathbb Z/2.
\]
所以 \(|K|\) 不可缩。

## S4 整体对象与全部恢复目标

### 同伦类型的刻画

**全部可能类型恰好是**
\[
\boxed{\bigl\{\Sigma|L|\text{ 的同伦类型}:
L\text{ 是几何非空的有限单纯复形}\bigr\}.}
\]

先证必要性。令
\[
D=K-v,\qquad
L=\operatorname{lk}_K(v)
=\{\sigma\in K:v\notin\sigma,\ \sigma\cup\{v\}\in K\}.
\]
由 S3 的变形收缩，\(O\) 强变形收缩到 \(|D|\)，故 \(|D|\) 非空可缩。

**\(L\) 至少有一个顶点。** 实际上，若 \(B\) 中没有含 \(v\) 的边，则 \(v\) 是 \(C=|B|\) 的一个孤立路径分支。但
\[
O\cap C=C\setminus\{v\}
\]
不与该分支相交，因此包含 \(O\cap C\to C\) 不可能在路径分支上满射，更不可能是同伦等价。故 \(B\) 含某条边 \(\{v,w\}\)，于是 \(w\) 是 \(L\) 的顶点。

由单纯复形的分解，
\[
K=D\cup(v*L),\qquad D\cap(v*L)=L.
\]
由于 \(|L|\ne\varnothing\)，把 \(|D|\) 压为一点后得到
\[
X/|D|\cong |v*L|/|L|\cong\Sigma|L|.
\]
\(|D|\) 是有限 CW 复形 \(X\) 的非空可缩子复形，故由 S1，
\[
X\simeq X/|D|\cong\Sigma|L|.
\]

反过来，对任意几何非空的有限单纯复形 \(L\)，取两个新顶点 \(u,v\)，令
\[
K=(u*L)\cup(v*L).
\]
选 \(L\) 的顶点 \(w\)，令 \(B\) 为边 \(\{v,w\}\) 及其所有面。S3 中的论证表明：

1. \(|K|\setminus\{v\}\) 强变形收缩到非空可缩的 \(|u*L|\)；
2. \(|B|\setminus\{v\}\to|B|\) 是同伦等价；
3. \(|K|\cong\Sigma|L|\)。

故刻画中的每一种类型都由满足全部原条件的三元组实现。

### 仅用 \(v\) 的局部关联数据的可缩判据

令 \(L=\operatorname{lk}_K(v)\)。在题设下 \(|L|\ne\varnothing\)。所求判据为
\[
\boxed{X\text{ 可缩}
\quad\Longleftrightarrow\quad
\widetilde H_*(|L|;\mathbb Z)=0.}
\]

此条件可由指定的有限数据检验：\(L\) 的每个单形 \(\sigma\) 恰对应 \(K\) 中含 \(v\) 的单形 \(\sigma\cup\{v\}\)。给这些单形任意定向，写出整数边界矩阵，检查增广链复形
\[
0\longrightarrow C_d(L;\mathbb Z)\longrightarrow\cdots
\longrightarrow C_1(L;\mathbb Z)\longrightarrow
C_0(L;\mathbb Z)\xrightarrow{\ \varepsilon\ }\mathbb Z
\longrightarrow0
\]
是否处处正合即可。这可用整数矩阵运算、例如 Smith 标准形完成。

证明判据。上面已知 \(X\simeq\Sigma|L|\)。悬挂同调公式给出
\[
\widetilde H_{n+1}(\Sigma|L|;\mathbb Z)
\cong\widetilde H_n(|L|;\mathbb Z)\qquad(n\ge0),
\]
所以必要性成立。

反之，设 \(\widetilde H_*(|L|;\mathbb Z)=0\)。由 \(\widetilde H_0=0\)，\(|L|\) 路径连通。用悬挂的两个开锥覆盖 \(\Sigma|L|\)：它们均可缩，交集同伦等价于路径连通的 \(|L|\)。由 van Kampen 定理，\(\Sigma|L|\) 单连通；由悬挂同调公式，它的所有约化整数同调均为零。

若该空间有非零同伦群，取最小的 \(n\ge2\) 使 \(\pi_n\ne0\)。Hurewicz 定理将给出 \(H_n\ne0\)，矛盾。故它所有同伦群均为零。它是有限 CW 复形，由 Whitehead 定理可缩，因此 \(X\) 可缩。

## S5 不提供子复形 \(B\)

**不必是几何非空有限复形的悬挂。** 全部可能类型恰好是
\[
\boxed{\{S^0\}\ \cup\
\{\Sigma|L|:L\text{ 是几何非空的有限单纯复形}\}
\quad\text{的同伦类型}.}
\]

令 \(D=K-v\)、\(L=\operatorname{lk}_K(v)\)。由 S3，\(|D|\) 非空可缩。

- 若 \(L\) 有顶点，S4 的商空间论证不依赖 \(B\)，给出
  \[
  |K|\simeq\Sigma|L|.
  \]
- 若 \(L\) 没有顶点，则 \(v\) 是孤立顶点，
  \[
  |K|=|D|\sqcup\{v\}\simeq S^0.
  \]

前一类全部由 S4 的双锥构造实现；后一类可取 \(K\) 为两个孤立顶点，\(v\) 为其中一个。非空空间的非约化悬挂总是路径连通，而 \(S^0\) 不连通，所以 \(S^0\) 确实是新增类型。

## S6 悬挂信息的逆向恢复

**不必推出。** 取有限单纯模型
\[
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
例如，可将两个三角形边界的乘积作有限三角剖分得到 \(L_1\)；将两个三角形边界和一个四面体边界各选一个顶点粘合得到 \(L_2\)。

首先，
\[
\pi_1(|L_1|)\cong\mathbb Z^2,\qquad
\pi_1(|L_2|)\cong F_2.
\]
前者交换，后者不交换，因此 \(|L_1|\not\simeq|L_2|\)。

下面证明它们的悬挂同伦等价。对选定顶点的有限单纯复形，非约化悬挂中穿过该顶点、连接两个悬挂极点的路径，是双锥三角剖分中的可缩子复形。将其压为一点得到约化悬挂；由 S1，压缩映射是同伦等价。因此可计算约化悬挂。

环面的标准 CW 分解为
\[
T^2=(S^1\vee S^1)\cup_f e^2,
\]
其中 \(f:S^1\to S^1\vee S^1\) 表示两个圆生成元的交换子。对这个以 \(0\)-胞腔为基点的 CW 附着取约化悬挂，得到
\[
\widetilde\Sigma T^2\simeq
(S^2\vee S^2)\cup_{\widetilde\Sigma f}e^3.
\]
交换子在一维同调中为零，故 \(f_*\) 在 \(H_1\) 上为零；由悬挂同调的自然性，\((\widetilde\Sigma f)_*\) 在 \(H_2\) 上也为零。\(S^2\vee S^2\) 单连通，Hurewicz 定理给出
\[
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z),
\]
所以 \(\widetilde\Sigma f\) 零伦。由 S2 证明中的映射锥同伦不变性，
\[
\widetilde\Sigma T^2\simeq S^2\vee S^2\vee S^3.
\]
另一方面，约化悬挂保持楔和，故
\[
\widetilde\Sigma(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]
于是
\[
\Sigma|L_1|\simeq\Sigma|L_2|,
\qquad\text{但}\qquad
|L_1|\not\simeq|L_2|.
\]