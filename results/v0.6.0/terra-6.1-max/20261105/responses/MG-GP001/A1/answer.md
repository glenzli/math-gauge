记非约化悬挂为
\[
\Sigma Z=(Z\times I)/(Z\times\{0\},\,Z\times\{1\}),
\]
其中两端分别压成两个点。

## S1 可缩子复形的商

设 \(q:Y\to Y/A\) 为商映射。取 \(A\) 的收缩
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
因为 \((Y,A)\) 是 CW 对，所以包含 \(A\hookrightarrow Y\) 具有同伦延拓性质。将 \(h\) 看作取值于 \(Y\) 的同伦，可延拓为
\[
G:Y\times I\longrightarrow Y,\qquad G(y,0)=y,\quad G(a,t)=h(a,t).
\]
特别地，对每个 \(t\)，都有 \(G_t(A)\subseteq A\)，而 \(G_1(A)=\{a_0\}\)。

因此 \(G_1\) 通过 \(q\) 分解为连续映射
\[
r:Y/A\longrightarrow Y,\qquad r([y])=G_1(y).
\]
于是 \(rq=G_1\simeq\operatorname{id}_Y\)。

还需证明此同伦在商上成立。由于每个 \(G_t\) 都把 \(A\) 映入 \(A\)，公式
\[
\overline G([y],t)=[G(y,t)]
\]
良定义。有限 CW 复形 \(Y\) 是紧 Hausdorff 空间，\(A\) 是闭集，所以 \(Y/A\) 也是紧 Hausdorff 空间；因而
\[
q\times\operatorname{id}_I:Y\times I\longrightarrow (Y/A)\times I
\]
是闭的满射，故为商映射。这说明 \(\overline G\) 连续。它给出
\[
\operatorname{id}_{Y/A}\simeq qr.
\]
所以 \(q\) 是同伦等价，同伦逆为 \(r\)。

## S2 非可缩底空间上的锥附着

先说明所用的映射锥同伦不变性。对映射 \(f:L\to D\)，记
\[
C_f=\bigl(D\sqcup(L\times I)\bigr)/
\bigl((x,0)\sim f(x),\ L\times\{1\}\text{ 压为一点}\bigr).
\]
若 \(H:L\times I\to D\) 是从 \(f\) 到 \(g\) 的同伦，定义 \(F_H:C_f\to C_g\) 在 \(D\) 上为恒等，并令
\[
F_H([x,t])=
\begin{cases}
H(x,2t),&0\le t\le \frac12,\\
[x,2t-1]_g,&\frac12\le t\le1.
\end{cases}
\]
粘合处两式均为 \(g(x)\)，所以映射连续。反向同伦 \(\bar H(x,t)=H(x,1-t)\) 给出 \(F_{\bar H}:C_g\to C_f\)。

这两个映射互为同伦逆，且同伦可相对于 \(D\) 取定。事实上，\(F_{\bar H}F_H\) 在锥的初始部分先沿 \(H\) 前进、再沿 \(H\) 返回，然后进入原来的锥。将这段往返路径同时缩短至其起点，再把剩余锥参数线性拉直，就得到恒等映射；另一复合同理。故同伦的附着映射有同伦等价的映射锥。

现在取 \(D\) 的一个顶点 \(d_0\)。给定的零伦终止于 \(D\) 中某个常值点；由于 \(D\) 路径连通，可接上一条路径，将终点改为 \(d_0\)。因此包含映射 \(L\hookrightarrow D\) 与常值映射 \(c_{d_0}\) 同伦，故
\[
Y\simeq C_{c_{d_0}}.
\]
后者就是把 \(\Sigma L\) 的 \(L\times\{0\}\) 所代表的悬挂极点与 \(d_0\) 粘合所得空间。因此
\[
\boxed{Y\simeq D\vee\Sigma L.}
\]
这里楔点在 \(D\) 一侧选为 \(d_0\)，在悬挂一侧选为上述极点。由于 \(D\) 路径连通，可任选其顶点作为 \(d_0\)。

## S3 整数扭结的实例

先记录一个后面也要使用的事实。对有限单纯复形 \(K\) 和顶点 \(v\)，令
\[
K-v=\{\sigma\in K:v\notin\sigma\}.
\]
则 \(|K|\setminus\{v\}\) 强变形收缩到 \(|K-v|\)。具体地，若 \(x=\sum_w t_w w\ne v\)，令
\[
r(x)=\sum_{w\ne v}\frac{t_w}{1-t_v}\,w,\qquad
H(x,s)=(1-s)x+s\,r(x).
\]
这些点始终留在含 \(x\) 的单形内，且 \(H(x,s)\ne v\)。若 \(x\) 原来属于某个含 \(v\) 的子复形，此同伦也始终留在该子复形中。

现在取题给的 \(\mathbb{RP}^2\) 的有限单纯三角剖分 \(L\)，另取两个新顶点 \(u,v\)，令
\[
K=(u*L)\cup(v*L).
\]
选 \(L\) 的任一顶点 \(w\)，令 \(B\) 为边 \(\{v,w\}\) 及其所有面的子复形。

这里 \(K-v=u*L\) 是非空锥，因此上面的变形收缩表明 \(|K|\setminus\{v\}\) 非空可缩。而 \(|B|\setminus\{v\}\) 和 \(|B|\) 都可沿边线性收缩到 \(w\)；故包含
\[
|B|\setminus\{v\}\longrightarrow |B|
\]
是同伦等价。

两个锥沿其公共底 \(L\) 粘合，所以
\[
|K|\cong\Sigma|L|\cong\Sigma\mathbb{RP}^2.
\]
\(\mathbb{RP}^2\) 的标准胞腔链复形在正维为
\[
0\longrightarrow\mathbb Z\xrightarrow{\;2\;}\mathbb Z\longrightarrow 0.
\]
因此其约化有理同调全为零，而
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

**所有可能类型恰好是**
\[
\boxed{\bigl\{\text{\(\Sigma|L|\) 的同伦类型}:
L\text{ 是非空有限单纯复形}\bigr\}.}
\]

先证必要性。令
\[
D=K-v,\qquad
L=\operatorname{lk}_K(v)
 =\{\sigma\in K:v\notin\sigma,\ \sigma\cup\{v\}\in K\}.
\]
由 S3 的变形收缩，\(O\) 强变形收缩到 \(|D|\)。因此 \(|D|\) 非空可缩。

\(L\) 必须非空。否则 \(K\) 中没有任何连接 \(v\) 与另一顶点的边，故 \(\{v\}\) 是 \(|K|\) 的一个路径分支，也是 \(C=|B|\) 的一个路径分支。但 \(O\cap C=C\setminus\{v\}\) 的像不与这个分支相交，故包含 \(O\cap C\to C\) 不可能在路径分支上满射，更不可能是同伦等价，矛盾。

由于
\[
K=D\cup(v*L),\qquad D\cap(v*L)=L,
\]
将可缩子复形 \(|D|\) 压为一点后，剩下的是以 \(|L|\) 为底的锥，其底也被压为一点。因此
\[
X/|D|\cong\Sigma|L|.
\]
S1 适用于有限 CW 对 \((X,|D|)\)，故 \(X\to X/|D|\) 是同伦等价，从而
\[
X\simeq\Sigma|L|.
\]

反过来，对任意非空有限单纯复形 \(L\)，取两个新顶点 \(u,v\)，令
\[
K=(u*L)\cup(v*L),
\]
再取 \(L\) 的一个顶点 \(w\)，令 \(B\) 为边 \(\{v,w\}\) 及其面。S3 中的同一论证表明：

- \(|K|\setminus\{v\}\) 强变形收缩到非空可缩的 \(|u*L|\)；
- \(|B|\setminus\{v\}\to|B|\) 是同伦等价；
- \(|K|\cong\Sigma|L|\)。

这实现了刻画中的每一种类型。

### 只使用 \(v\) 附近有限关联数据的可缩判据

令 \(L=\operatorname{lk}_K(v)\)。题设保证 \(L\) 非空。所求判据为
\[
\boxed{X\text{ 可缩}\quad\Longleftrightarrow\quad
\widetilde H_*(|L|;\mathbb Z)=0.}
\]

这是有限可检验条件：\(L\) 的单形恰好由 \(K\) 中含 \(v\) 的单形删去 \(v\) 得到。给这些单形定向，写出整数边界矩阵，检查增广链复形
\[
0\longrightarrow C_d(L;\mathbb Z)\longrightarrow\cdots
\longrightarrow C_1(L;\mathbb Z)\longrightarrow
C_0(L;\mathbb Z)\xrightarrow{\ \varepsilon\ }\mathbb Z
\longrightarrow0
\]
是否处处正合即可；例如可用整数矩阵的 Smith 标准形计算。只检验有理同调不够，S3 给出了反例。

证明判据。由上面的刻画，\(X\simeq\Sigma|L|\)。非空空间的悬挂同调公式给出
\[
\widetilde H_{n+1}(\Sigma|L|;\mathbb Z)
\cong\widetilde H_n(|L|;\mathbb Z)\qquad(n\ge0).
\]
所以 \(X\) 可缩时，\(L\) 的整数约化同调必全为零。

反之，若这些同调全为零，则 \(\widetilde H_0(|L|;\mathbb Z)=0\)，故有限单纯复形 \(|L|\) 路径连通。用悬挂的两个开锥覆盖 \(\Sigma|L|\)：两个开锥均可缩，其交同伦等价于路径连通的 \(|L|\)。由 van Kampen 定理，\(\Sigma|L|\) 单连通；由悬挂同调公式，它又是整数非循环的，即所有约化整数同调为零。

若该单连通 CW 复形存在非零同伦群，取最小的 \(n\ge2\) 使 \(\pi_n\ne0\)，Hurewicz 定理便给出 \(H_n\ne0\)，矛盾。因此它的所有同伦群均为零。由适用于 CW 复形的 Whitehead 定理，\(\Sigma|L|\) 可缩，故 \(X\) 可缩。

## S5 不提供子复形 \(B\)

**不必是非空有限复形的悬挂。** 全部可能类型恰好是
\[
\boxed{\{S^0\}\ \cup\
\{\Sigma|L|:L\text{ 为非空有限单纯复形}\}
\quad\text{的同伦类型}.}
\]

事实上，仍令 \(D=K-v\)、\(L=\operatorname{lk}_K(v)\)。由 S3，\(|D|\) 非空可缩。

- 若 \(L\ne\varnothing\)，S4 的商空间论证不依赖 \(B\)，给出 \(X\simeq\Sigma|L|\)。
- 若 \(L=\varnothing\)，则 \(v\) 是孤立顶点，且
  \[
  X=|D|\sqcup\{v\}\simeq S^0.
  \]

前一类全部由 S4 构造实现；后一类可取 \(K\) 为两个孤立顶点，\(v\) 为其中一个。非空空间的非约化悬挂总是路径连通，而 \(S^0\) 不连通，所以 \(S^0\) 确实是去掉 \(B\) 后新增的类型。

## S6 悬挂信息的逆向恢复

**不必推出。** 可取
\[
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
二者都有有限单纯模型：对两个三角形边界的乘积作有限乘积三角剖分得到 \(L_1\)；将两个三角形边界和一个四面体边界各选一个顶点粘合得到 \(L_2\)。

首先，
\[
\pi_1(|L_1|)\cong\mathbb Z^2,\qquad
\pi_1(|L_2|)\cong F_2.
\]
前者交换，后者不交换，因此 \(|L_1|\not\simeq|L_2|\)。

证明其悬挂同伦等价。对以顶点为基点的有限单纯复形，将非约化悬挂中通过该顶点连接两个悬挂极点的路径压为一点，得到约化悬挂。该路径是可缩子复形，故由 S1，压缩映射是同伦等价。因此下面可计算约化悬挂。

环面有一个 CW 分解
\[
T^2=(S^1\vee S^1)\cup_f e^2,
\]
其中附着映射 \(f:S^1\to S^1\vee S^1\) 表示两个圆生成元的交换子。对这个基点为 \(0\)-胞腔的 CW 附着取约化悬挂，得到相应的同伦余纤维：
\[
\widetilde\Sigma T^2\simeq
(S^2\vee S^2)\cup_{\widetilde\Sigma f} e^3.
\]
由于交换子在一维同调中为零，\(f_*\) 在 \(H_1\) 上为零；由悬挂同调的自然性，\((\widetilde\Sigma f)_*\) 在 \(H_2\) 上也为零。空间 \(S^2\vee S^2\) 单连通，Hurewicz 定理给出
\[
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z),
\]
所以 \(\widetilde\Sigma f\) 零伦。由 S2 证明中使用的映射锥同伦不变性，
\[
\widetilde\Sigma T^2\simeq S^2\vee S^2\vee S^3.
\]
另一方面，约化悬挂保持楔和，故
\[
\widetilde\Sigma(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]
于是 \(\Sigma|L_1|\simeq\Sigma|L_2|\)，尽管 \(|L_1|\not\simeq|L_2|\)。