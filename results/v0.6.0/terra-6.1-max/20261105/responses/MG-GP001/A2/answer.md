## S1 可缩子复形的商

令 \(q:Y\to Y/A\) 为商映射。取 \(A\) 的收缩
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0,
\]
其中 \(a_0\in A\)。

由于 \(A\) 是 CW 复形 \(Y\) 的子复形，\((Y,A)\) 具有同伦扩张性质。因此可将 \(h\) 扩张为
\[
F:Y\times I\longrightarrow Y,\qquad F(y,0)=y,\quad F(a,t)=h(a,t).
\]
特别地，对所有 \(t\)，有 \(F(A,t)\subseteq A\)，而 \(F(A,1)=\{a_0\}\)。

于是 \(F_1=F(-,1)\) 在 \(A\) 上为常值，故通过商映射唯一分解为连续映射
\[
g:Y/A\longrightarrow Y,\qquad gq=F_1.
\]
因此 \(gq\simeq\operatorname{id}_Y\)。

另一方面，\(qF(y,t)\) 在每个固定的 \(t\) 下对 \(q\) 的纤维为常值，故诱导
\[
\overline F:(Y/A)\times I\longrightarrow Y/A,\qquad
\overline F(q(y),t)=qF(y,t).
\]
这里同伦确实连续地下降到商：\(Y/A\) 是有限 CW 复形，故为 Hausdorff 空间；\(Y\times I\) 紧，因而连续满射
\[
q\times\operatorname{id}_I:Y\times I\longrightarrow (Y/A)\times I
\]
是闭商映射。故上述分解连续。它满足
\[
\overline F(-,0)=\operatorname{id}_{Y/A},\qquad
\overline F(-,1)=qg.
\]
所以 \(qg\simeq\operatorname{id}_{Y/A}\)，即 \(q\) 是同伦等价。

## S2 非可缩底空间上的锥附着

先说明所用的锥附着同伦不变性。设 \(f,g:L\to D\) 由同伦 \(H:L\times I\to D\) 连接，其中 \(H(-,0)=f\)、\(H(-,1)=g\)。记
\[
C_f=D\cup_f CL,\qquad C_g=D\cup_g CL,
\]
并取 \(CL=(L\times I)/(L\times\{1\})\)，其底为 \(L\times\{0\}\)。

定义 \(F_H:C_f\to C_g\) 在 \(D\) 上为恒等，在锥上为
\[
F_H([l,t])=
\begin{cases}
H(l,2t),&0\le t\le \tfrac12,\\[2mm]
[l,2t-1]_{C_g},&\tfrac12\le t\le1.
\end{cases}
\]
两段在 \(t=\tfrac12\) 处相接，因为 \(H(l,1)=g(l)=[l,0]_{C_g}\)。反向同伦 \(\bar H(l,s)=H(l,1-s)\) 同样给出 \(F_{\bar H}:C_g\to C_f\)。

两个复合都相对于 \(D\) 同伦于恒等。例如，\(F_{\bar H}F_H\) 在锥上的效果是先沿 \(H\) 往返一次，再进入原来的锥；将往返的 \(H\)-参数收缩到 \(0\)，再将被延迟的锥参数线性改回 \(t\)，即得到恒等。因此 \(C_f\simeq C_g\)。

现在取 \(f\) 为包含 \(L\hookrightarrow D\)。它零伦，故同伦于某个常值映射。由于 \(D\) 路径连通，可在该同伦后接一条路径，使常值成为任意预选的 \(d_0\in D\)。于是
\[
Y=D\cup_f CL\simeq D\cup_{\mathrm{const}_{d_0}}CL.
\]
后一空间中，锥底 \(L\) 全部与 \(d_0\) 相粘。因为 \(L\ne\varnothing\)，有
\[
(CL)/L\cong\Sigma L,
\]
所以
\[
\boxed{Y\simeq D\vee\Sigma L.}
\]
楔点取为 \(D\) 中的 \(d_0\) 与非约化悬挂中由锥底 \(L\) 压成的那个极点。上述路径连通性说明 \(d_0\) 可以任意选择；若希望楔和带有明显的 CW 结构，也可选 \(D\) 的一个 \(0\)-胞腔。

## S3 整数扭结的实例

先记录一个后面也会使用的事实。若 \(P\) 是非空有限复形，则其非约化悬挂可由去掉两个极点所得的两个开集覆盖；这两个开集各自可缩，交集同伦等价于 \(P\)。约化 Mayer–Vietoris 序列因此给出自然同构
\[
\widetilde H_n(\Sigma P;R)\cong
\widetilde H_{n-1}(P;R)\qquad(n\ge1),
\tag{1}
\]
其中 \(R=\mathbb Z\) 或 \(\mathbb Q\)。此外，\(\Sigma P\) 路径连通；若 \(P\) 路径连通，则由同一开覆盖和 van Kampen 定理知 \(\Sigma P\) 单连通。

现在令给定的 \(L\) 是 \(\mathbb{RP}^2\) 的有限单纯三角剖分。取不在 \(L\) 中的两个顶点 \(v,w\)，令
\[
K=L*S^0,\qquad S^0=\{\{v\},\{w\},\varnothing\}.
\]
再取 \(L\) 的任一顶点 \(a\)，令 \(B\) 为边 \(\{v,a\}\) 及其所有面。

这里 \(|K|\cong\Sigma|L|\)，其中 \(v,w\) 是两个极点。去掉 \(v\) 后，空间可表示为
\[
\bigl(|L|\times[0,1)\bigr)\big/\bigl(|L|\times\{0\}\bigr),
\]
它通过把第二坐标压向 \(0\) 而收缩到 \(w\)。因此 \(|K|\setminus\{v\}\) 非空可缩。

另一方面，\(|B|\) 是闭区间，而 \(|B|\setminus\{v\}\) 是含端点 \(a\) 的半开区间；二者均可缩，且包含映射是同伦等价。例如，可取从闭区间到半开区间的常值映射 \(x\mapsto a\) 为同伦逆。

由 \(\mathbb{RP}^2\) 的标准 CW 胞腔链复形
\[
0\longrightarrow\mathbb Z\xrightarrow{\;2\;}\mathbb Z
\xrightarrow{\;0\;}\mathbb Z\longrightarrow0
\]
可知
\[
\widetilde H_*(|L|;\mathbb Q)=0,\qquad
\widetilde H_1(|L|;\mathbb Z)\cong\mathbb Z/2.
\]
由式 (1)，
\[
\widetilde H_*(|K|;\mathbb Q)=0,\qquad
\widetilde H_2(|K|;\mathbb Z)\cong\mathbb Z/2.
\]
故该例满足全部条件，且 \(|K|\) 虽有理约化同调全零，却不可缩。

## S4 整体对象与全部恢复目标

### 1. 同伦类型的刻画

**结论：**恰好得到所有
\[
\boxed{\Sigma|L|\quad\text{的同伦类型，其中 }L\text{ 是非空有限单纯复形}.}
\tag{2}
\]
这里不同的 \(L\) 可以产生相同的悬挂同伦类型。

为证明必要性，令
\[
K-v=\{\sigma\in K:v\notin\sigma\},\qquad
L=\operatorname{lk}_K(v)
=\{\sigma\in K:v\notin\sigma,\ \sigma\cup\{v\}\in K\},
\]
并记 \(D=|K-v|\)。

首先，\(O=|K|\setminus\{v\}\) 强变形收缩到 \(D\)。具体地，设 \(x\in O\) 的重心坐标为 \(\lambda_u(x)\)，令
\[
r(x)=\sum_{u\ne v}
\frac{\lambda_u(x)}{1-\lambda_v(x)}\,u.
\]
由于 \(x\ne v\)，分母非零；\(r(x)\) 属于包含 \(x\) 的单形中去掉 \(v\) 后的面。因此
\[
H_s(x)=(1-s)x+s\,r(x)
\]
始终留在原单形及 \(O\) 中，并且固定 \(D\)。由假设，\(D\) 非空可缩。

其次，\(L\) 必非空。事实上，若 \(v\) 在 \(B\) 中不属于任何边，则 \(\{v\}\) 是 \(|B|\) 的一个独立路径分支，而
\[
O\cap C=C\setminus\{v\}
\]
不包含该分支。其包含到 \(C\) 不可能在路径分支上满射，更不可能是同伦等价。这与假设矛盾。所以 \(B\)，从而 \(K\)，含有某条以 \(v\) 为端点的边，故 \(|L|\ne\varnothing\)。

单纯复形分解为
\[
K=(K-v)\cup(v*L),\qquad (K-v)\cap(v*L)=L.
\]
因此压缩 \(D\) 后，
\[
X/D\cong |v*L|/|L|\cong\Sigma|L|.
\]
这里 \(D\) 是 \(X\) 的非空可缩子复形；由 S1，\(X\to X/D\) 是同伦等价，故
\[
X\simeq\Sigma|L|.
\]

### 2. 全部类型的实现

反过来，给定任意非空有限单纯复形 \(L\)，取新顶点 \(v,w\)，令
\[
K=L*\{\varnothing,\{v\},\{w\}\}.
\]
取 \(L\) 的任意顶点 \(a\)，令 \(B\) 为边 \(\{v,a\}\) 及其所有面。

则 \(K-v=w*L\) 是锥，故其实现可缩；由上面的强变形收缩，\(|K|\setminus\{v\}\) 非空可缩。又 \(|B|\setminus\{v\}\to|B|\) 是半开区间到闭区间的包含，按 S3 的论证是同伦等价。最后
\[
|K|\cong\Sigma|L|.
\]
这实现了式 (2) 中的每一种类型，也完成了分类。

### 3. 只用 \(v\) 的局部关联数据的可缩判据

**判据：**
\[
\boxed{X\text{ 可缩}\quad\Longleftrightarrow\quad
\widetilde H_j(|\operatorname{lk}_K(v)|;\mathbb Z)=0
\text{ 对所有 }j\ge0.}
\tag{3}
\]

该条件可以完全由包含 \(v\) 的单形及其面之间的有限关联数据检验。具体地，固定顶点顺序，对 \(q\ge0\) 定义自由阿贝尔群
\[
C_q=\mathbb Z\langle [u_0,\ldots,u_q]:
u_0<\cdots<u_q,\ 
\{v,u_0,\ldots,u_q\}\in K\rangle.
\]
令 \(C_{-1}=\mathbb Z\)，边界为
\[
\partial_q[u_0,\ldots,u_q]
=\sum_{i=0}^q(-1)^i[u_0,\ldots,\widehat{u_i},\ldots,u_q]
\quad(q\ge1),
\qquad
\partial_0[u]=1.
\]
这些正是链接 \(L\) 的增广单纯链复形的边界。令最高维为 \(m\)，则判据等价于有限整数链复形
\[
0\longrightarrow C_m\longrightarrow\cdots\longrightarrow C_0
\xrightarrow{\partial_0}\mathbb Z\longrightarrow0
\tag{4}
\]
处处正合。每个矩阵条目只由含 \(v\) 的单形及删去一个非 \(v\) 顶点所得的面决定；可用整数 Smith 标准形及核、像的格点计算检验正合性。

证明式 (3)。由上文 \(X\simeq\Sigma|L|\)。若 \(X\) 可缩，式 (1) 立即给出 \(L\) 的全部整数约化同调为零。

反过来，若这些群全为零，则 \(\widetilde H_0(|L|;\mathbb Z)=0\)，故 \(|L|\) 路径连通。由 S3 中的 van Kampen 论证，\(\Sigma|L|\) 单连通；由式 (1)，它的全部整数约化同调也为零。它是有限 CW 复形。若其某个同伦群非零，取最小的非零维数 \(n\ge2\)，Hurewicz 定理将该 \(\pi_n\) 同构到 \(H_n\)，产生矛盾。因此它弱可缩，再由适用于 CW 复形的 Whitehead 定理知它可缩。由此得到式 (3)，而式 (4) 的正合性正是这些约化同调消失。

这里必须使用**整数**链复形：仅检查有理正合性不够，S3 中的 \(\mathbb Z/2\) 正是障碍。

## S5 不提供子复形 \(B\)

不一定。例如令 \(K\) 只有两个孤立顶点 \(v,w\)。则
\[
|K|\setminus\{v\}=\{w\}
\]
非空可缩，但 \(|K|\cong S^0\)。非空空间的非约化悬挂总是路径连通，所以 \(S^0\) 不可能同伦等价于非空有限复形的悬挂。

事实上，新增的可能同伦类型**恰好只有 \(S^0\)**。沿用 S4 的 \(D\) 和链接 \(L\)：

- 若 \(|L|\ne\varnothing\)，S4 中压缩 \(D\) 的论证不需要 \(B\)，仍给出 \(X\simeq\Sigma|L|\)。
- 若 \(|L|=\varnothing\)，则 \(v\) 是孤立顶点，
  \[
  X=D\sqcup\{v\}\simeq S^0,
  \]
  因为 \(D\) 非空可缩。

所有非空有限复形的悬挂已由 S4 的构造实现；上面的两孤立顶点实现新增类型 \(S^0\)。

## S6 悬挂信息的逆向恢复

**不必推出。**取有限单纯复形 \(L_1,L_2\)，使
\[
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
这些都可有限三角剖分：例如 \(T^2\) 可将两个三边圈的乘积的每个方格沿一致的对角线剖分；另一空间可将两个三角形边界和一个四面体边界在选定顶点处相粘。

原空间不同伦等价，因为
\[
\pi_1(T^2)\cong\mathbb Z^2,\qquad
\pi_1(S^1\vee S^1\vee S^2)\cong F_2,
\]
前者交换，后者为非交换自由群。

但它们的悬挂同伦等价。为便于计算，先改用约化悬挂。对带基点的有限单纯复形，非约化悬挂中由基点连接两个极点的弧是可缩子复形；将它压成一点得到约化悬挂。因此由 S1，两种悬挂同伦等价。

令 \(W=S^1\vee S^1\)。环面有标准 CW 分解
\[
T^2=W\cup_c e^2,
\]
其中 \(c:S^1\to W\) 表示交换子 \([a,b]\)。在这些带基点 CW 复形上，约化悬挂保持同伦余纤，故
\[
\widetilde\Sigma T^2
\simeq (\widetilde\Sigma W)\cup_{\widetilde\Sigma c}e^3.
\]
这里 \(\widetilde\Sigma W\cong S^2\vee S^2\)。交换子在一维同调的阿贝尔化中为零，所以
\[
c_*:H_1(S^1;\mathbb Z)\longrightarrow H_1(W;\mathbb Z)
\]
为零。由悬挂同调同构的自然性，\((\widetilde\Sigma c)_*\) 在二阶同调上也为零。目标 \(S^2\vee S^2\) 是单连通 CW 复形，Hurewicz 同构
\[
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z)
\]
遂表明 \(\widetilde\Sigma c:S^2\to S^2\vee S^2\) 零伦。因此锥附着的同伦不变性给出
\[
\widetilde\Sigma T^2\simeq S^2\vee S^2\vee S^3.
\]
另一方面，约化悬挂与有限楔和相容，所以
\[
\widetilde\Sigma(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]
换回非约化悬挂即得
\[
\Sigma|L_1|\simeq\Sigma|L_2|,
\qquad |L_1|\not\simeq|L_2|.
\]