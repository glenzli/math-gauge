**S1.** 记商映射为 \(q:Y\to Y/A\)。取收缩
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
因为 \(A\subseteq Y\) 是 CW 子复形，包含映射具有同伦延拓性质。因此 \(h\) 可延拓为
\[
F:Y\times I\longrightarrow Y,\qquad F(y,0)=y,\quad F|_{A\times I}=h.
\]
特别地，\(F_1\) 在 \(A\) 上恒为 \(a_0\)，故存在连续映射
\[
g:Y/A\longrightarrow Y,\qquad gq=F_1.
\]
于是 \(gq\simeq\operatorname{id}_Y\)。

另一方面，对每个 \(t\)，都有 \(F_t(A)\subseteq A\)，所以
\[
\overline F(q(y),t)=q(F(y,t))
\]
定义良好。这也是连续的联合同伦：有限 CW 复形 \(Y\) 紧致 Hausdorff，\(A\) 闭，故 \(Y/A\) 是 Hausdorff；连续满射
\[
q\times\operatorname{id}_I:Y\times I\longrightarrow (Y/A)\times I
\]
是紧空间到 Hausdorff 空间的闭映射，因而是商映射。因此 \(qF\) 确实连续地下降到商。

该同伦满足
\[
\overline F_0=\operatorname{id}_{Y/A},\qquad \overline F_1=qg.
\]
故 \(q\) 是同伦等价。下降的关键是构造保证了整个同伦过程中 \(F_t(A)\subseteq A\)。

**S2.** 先证明一个后面也会使用的映射锥事实。对映射 \(f:L\to D\)，记
\[
C(f)=\bigl(D\amalg(L\times I)\bigr)/
\bigl((x,0)\sim f(x),\ L\times\{1\}\text{ 压为一点}\bigr).
\]
若 \(H:f\simeq g\)，则定义
\[
\Phi_H:C(f)\longrightarrow C(g)
\]
在 \(D\) 上为恒等，并在锥上定义为
\[
\Phi_H([x,t])=
\begin{cases}
H(x,2t),&0\le t\le \tfrac12,\\
[x,2t-1],&\tfrac12\le t\le1.
\end{cases}
\]
两段在 \(t=\tfrac12\) 处一致，也尊重底部和锥顶的识别，故给出连续映射。

反向同伦 \(\overline H(x,s)=H(x,1-s)\) 给出反向映射。两种复合都是先沿同伦往返，再进入原锥，仅各段参数长度有所改变。线性调整这些长度后，往返部分可连续缩为常值：例如令
\[
\rho(u)=
\begin{cases}
2u,&u\le\tfrac12,\\
2-2u,&u\ge\tfrac12,
\end{cases}
\]
则
\[
H(x,(1-s)\rho(u))
\]
在端点不动下把 \(H\) 后接其逆的路径缩为常值路径。最后把剩余常值领圈的长度缩为零，即得到恒等映射。另一复合同理。因此
\[
f\simeq g\quad\Longrightarrow\quad C(f)\simeq C(g),
\]
而且这些同伦在 \(D\) 上保持不动。

现在令 \(i:L\hookrightarrow D\)。题设给出 \(i\simeq c_{d_0}\)。因为 \(D\) 路径连通，可将零伦接上一条路径，使 \(d_0\) 是任意指定的 \(0\) 胞腔。于是
\[
Y=C(i)\simeq C(c_{d_0}).
\]
对常值映射，整个锥底被粘到 \(d_0\)，所以
\[
C(c_{d_0})
\cong D\vee\bigl(CL/L\bigr)
= D\vee\Sigma L.
\]

楔点在 \(D\) 中取 \(d_0\)，在非约化悬挂中取“锥底压缩所得”的悬点。两个悬点可由悬挂反射交换；不同的 \(d_0\) 可由 \(D\) 中的路径连接，相应常值映射同伦，故所得同伦类型不变。这里没有要求 \(L\) 连通。

**S3.** 先记录一个删去顶点的事实。对有限单纯复形 \(K\)，令
\[
D=\{\sigma\in K:v\notin\sigma\}.
\]
在通常的重心坐标中，对 \(x\ne v\) 定义
\[
r(x)=\sum_{u\ne v}\frac{t_u(x)}{1-t_v(x)}\,u.
\]
它落在 \(|D|\) 中。直线同伦
\[
R_s(x)=(1-s)x+s\,r(x)
\]
始终位于承载 \(x\) 的单形内，且不会经过 \(v\)，并逐点固定 \(|D|\)。因此
\[
|K|\setminus\{v\}\ \searrow\ |D|
\]
是强形变收缩。

现取题给的 \(L\)，添加两个新顶点 \(v,w\)，令
\[
K=L*\{v,w\}=(v*L)\cup_L(w*L),
\]
其中 \(\{v,w\}\) 是没有边的两点复形。选择 \(L\) 的任一顶点 \(a\)，令 \(B\) 为边 \([v,a]\) 及其所有面。

此时 \(|K|\cong\Sigma|L|\)，而删除子复形为 \(w*L\)，是非空可缩的锥。因此上述形变收缩说明
\[
|K|\setminus\{v\}
\]
非空且可缩。

又有 \(|B|\cong[0,1]\)，其中 \(v\) 对应 \(0\)，所以 \(|B|\setminus\{v\}\cong(0,1]\)。包含映射的同伦逆可取到端点 \(1\) 的常值映射；同伦
\[
h_s(t)=(1-s)t+s
\]
在这两个区间上均适用，故该包含确为同伦等价。

对非空空间，两个开锥邻域的 Mayer–Vietoris 序列给出悬挂同构
\[
\widetilde H_n(\Sigma|L|;R)
\cong \widetilde H_{n-1}(|L|;R),\qquad n\ge1.
\]
\(\mathbb{RP}^2\) 的标准胞腔链复形中 \(\partial_2\) 是乘以 \(2\)，故
\[
\widetilde H_1(\mathbb{RP}^2;\mathbb Z)=\mathbb Z/2,
\qquad
\widetilde H_n(\mathbb{RP}^2;\mathbb Q)=0\quad\text{对所有 }n.
\]
悬挂又是连通的，因而
\[
\widetilde H_*(|K|;\mathbb Q)=0,
\qquad
\widetilde H_2(|K|;\mathbb Z)=\mathbb Z/2\ne0.
\]
所以 \(|K|\) 不可缩，全部要求均满足。

**S4.** 可能的同伦类型恰好是
\[
\boxed{\ \Sigma|M|\quad\text{其中 }M\text{ 为任意非空有限单纯复形。}\ }
\]

先证明必要性。仍记删除子复形为 \(D\)，并记链环为
\[
\Lambda=\operatorname{lk}_K(v)
=\{\tau\in K:v\notin\tau,\ \tau\cup\{v\}\in K\}.
\]
由 S3 的形变收缩，\(|D|\simeq O\)，所以 \(|D|\) 非空且可缩。

此外，\(v\) 必须属于 \(B\) 的某条边。否则 \(v\) 是 \(|B|\) 的孤立分支，而
\[
|B|\setminus\{v\}\longrightarrow |B|
\]
在路径分支上不满射，不可能是同伦等价。因此 \(\Lambda\) 非空。

单纯复形的分解给出
\[
K=D\cup(v*\Lambda),\qquad D\cap(v*\Lambda)=\Lambda.
\]
对有限 CW 对 \((|K|,|D|)\) 应用 S1，得到
\[
X\simeq X/|D|
\cong (C|\Lambda|)/|\Lambda|
=\Sigma|\Lambda|.
\]
这里商空间的识别使用了 \(\Lambda\ne\varnothing\)：被压缩的 \(|D|\) 正对应于锥底压缩所得的悬点。

反过来，给定任意非空有限复形 \(M\)，取
\[
K=M*\{v,w\},\qquad B=[v,a]
\]
，其中 \(a\) 是 \(M\) 的任一顶点。与 S3 完全相同，删除子复形是可缩锥 \(w*M\)，而边去掉 \(v\) 后包含到整条边是同伦等价。因此每个 \(\Sigma|M|\) 都满足原条件得到实现。

可缩的局部判据为
\[
\boxed{\quad
X\text{ 可缩}
\iff
\widetilde H_q(\operatorname{lk}_K(v);\mathbb Z)=0
\quad\text{对所有 }q\ge0.
\quad}
\]

必要性来自 \(X\simeq\Sigma|\Lambda|\) 和悬挂同调同构。

证明充分性。若右边成立，则 \(\widetilde H_0(\Lambda;\mathbb Z)=0\)。由于 \(\Lambda\) 是非空有限复形，\(|\Lambda|\) 路径连通。悬挂的两个开锥邻域均可缩，其交集同伦等价于 \(|\Lambda|\)，故 van Kampen 定理说明 \(\Sigma|\Lambda|\) 单连通。悬挂同构又说明它的约化整数同调全零。

单连通且整数同调平凡的 CW 复形可缩：从 \(\pi_1=0\) 开始，逐次应用 Hurewicz 定理得到所有高阶同伦群为零，再对它到一点的映射应用 Whitehead 定理。因此 \(\Sigma|\Lambda|\)，从而 \(X\)，可缩。

最后说明如何只用题目要求的有限关联数据检验此判据。链环中的每个 \(q\) 单形
\[
\{u_0,\ldots,u_q\}
\]
恰对应于 \(K\) 中含 \(v\) 的 \((q+1)\) 单形
\[
\{v,u_0,\ldots,u_q\}.
\]
链环中的面关系，也恰对应于这些单形之间保留 \(v\) 的面关系。任意排列邻接顶点后，即可由这些关联写出增广整数链复形
\[
0\longrightarrow C_m(\Lambda;\mathbb Z)
\longrightarrow\cdots\longrightarrow
C_0(\Lambda;\mathbb Z)
\xrightarrow{\epsilon}\mathbb Z
\longrightarrow0,
\]
其中
\[
\partial[u_0,\ldots,u_q]
=\sum_{i=0}^q(-1)^i
[u_0,\ldots,\widehat u_i,\ldots,u_q],
\qquad \epsilon([u])=1.
\]
所求条件就是这个有限链复形处处正合，可通过整数矩阵计算，例如 Smith 标准形检验。整个计算只使用含 \(v\) 的单形及其面关联。必须使用整数系数；S3 表明有理系数会漏掉挠性障碍。

**S5.** 不一定；新增的可能类型恰好只有
\[
\boxed{S^0.}
\]

事实上，不需要 \(B\)，S3 的形变收缩仍说明删除子复形 \(D\) 非空可缩。

若链环 \(\Lambda\) 非空，S4 的商空间证明仍然适用，得到
\[
|K|\simeq\Sigma|\Lambda|.
\]
若链环没有顶点，则 \(v\) 是孤立顶点，从而
\[
|K|=|D|\amalg\{v\}\simeq\{\ast\}\amalg\{\ast\}=S^0.
\]

任何非空空间的非约化悬挂都路径连通，故 \(S^0\) 不可能同伦等价于题目要求的悬挂。它可由只有两个孤立顶点 \(v,w\) 的复形实现，此时删去 \(v\) 后只剩一点。原来的全部悬挂类型仍由 S4 的构造实现，故分类完整。

**S6.** 不必。取有限单纯复形 \(L_1,L_2\)，分别实现
\[
|L_1|\cong T^2,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
前者可取环面的有限三角剖分；后者可将两个多边形圆和一个三角剖分的球面在一个顶点处粘合，得到有限单纯复形。

它们不同伦等价，因为
\[
\pi_1(T^2)=\mathbb Z^2,\qquad
\pi_1(S^1\vee S^1\vee S^2)=F_2,
\]
前者交换，后者不交换。

下面证明它们的悬挂同伦等价。对基点为顶点的有限 CW 复形 \(Z\)，非约化悬挂中的基点经线是一条可缩子复形。由 S1，压缩这条经线得到的约化悬挂 \(\Sigma_r Z\) 满足
\[
\Sigma Z\simeq\Sigma_r Z.
\]

环面有一个 \(0\) 胞腔、两个 \(1\) 胞腔和一个 \(2\) 胞腔。以其 \(0\) 胞腔为基点，约化悬挂将非基点胞腔的维数增加一，故
\[
\Sigma_r T^2=(S^2\vee S^2)\cup_\alpha D^3
\]
，其中 \(\alpha:S^2\to S^2\vee S^2\)。

悬挂同构给出
\[
H_3(\Sigma_r T^2;\mathbb Z)
\cong H_2(T^2;\mathbb Z)=\mathbb Z.
\]
因此其胞腔边界
\[
\partial_3:\mathbb Z\longrightarrow\mathbb Z^2
\]
必须为零；它的两个坐标正是 \(\alpha\) 对两个球面的度数。于是 \(\alpha\) 的 Hurewicz 像为零。由于 \(S^2\vee S^2\) 是单连通 CW 复形，Hurewicz 同构
\[
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z)
\]
说明 \(\alpha\) 零伦。应用 S2 证明中的映射锥引理，得到
\[
\Sigma_r T^2\simeq S^2\vee S^2\vee S^3.
\]

另一方面，约化悬挂与有限楔和交换，所以
\[
\Sigma_r(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]
结合约化与非约化悬挂的比较，最终得到
\[
\Sigma|L_1|\simeq\Sigma|L_2|,
\qquad
|L_1|\not\simeq|L_2|.
\]