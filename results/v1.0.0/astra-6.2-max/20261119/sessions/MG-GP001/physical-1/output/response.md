## S1 可缩子复形的商

记商映射为 \(q:Y\to Y/A\)。取 \(A\) 到一点 \(a_0\in A\) 的收缩 \(h:A\times I\to A\)。由于 \(A\) 是 CW 子复形，包含 \(A\hookrightarrow Y\) 具有同伦延拓性质。因此存在 \(H:Y\times I\to Y\)，满足
\[
H(y,0)=y,\qquad H(a,t)=h(a,t)\quad(a\in A).
\]
末端映射 \(H_1\) 在 \(A\) 上恒等于 \(a_0\)，故可分解为 \(H_1=rq\)，其中 \(r:Y/A\to Y\) 连续。于是 \(rq\simeq\mathrm{id}_Y\)。

对每个 \(t\)，有 \(H_t(A)\subseteq A\)，所以 \(qH_t\) 在 \(A\) 上为常值。这使得
\[
\overline H(q(y),t)=q(H(y,t))
\]
良定义。它也连续，因为 \(Y\) 是紧 Hausdorff 空间，\(A\) 闭，故 \(Y/A\) 也是紧 Hausdorff 空间，从而 \(q\times\mathrm{id}_I\) 是闭满射，因而是商映射。这样得到的 \(\overline H\) 从 \(\mathrm{id}_{Y/A}\) 连到 \(qr\)。故 \(r\) 是 \(q\) 的同伦逆。

## S2 非可缩底空间上的锥附着

把 \(CL\) 的底置于高度 \(0\)，锥顶置于高度 \(1\)。对映射 \(f:L\to D\)，记 \(C_f=D\cup_f CL\)。若 \(H:L\times I\to D\) 是从 \(f\) 到 \(g\) 的同伦，则有映射 \(F_H:C_f\to C_g\)，它在 \(D\) 上取恒等，在锥上取
\[
F_H([z,t])=
\begin{cases}
H(z,2t),&0\le t\le \tfrac12,\\
[z,2t-1],&\tfrac12\le t\le 1.
\end{cases}
\]
两段在 \(t=\tfrac12\) 处都给出 \(g(z)\)，且公式符合底部和锥顶的粘合关系。反向同伦给出反向映射。两映射的复合在锥的下部沿同一条同伦路径往返一次，然后走完原锥。将往返路径的折返点连续退回起点，再把底部常值段的长度缩为零，即得相对于 \(D\) 的恒等同伦。反序复合同理，故 \(C_f\simeq C_g\)。

现在取 \(f\) 为题中的包含，\(g\) 为常值 \(p\in D\)。在 \(C_g\) 中，锥底 \(L\times\{0\}\) 全部粘到 \(p\)，所以
\[
Y=C_f\simeq C_g\cong D\vee\Sigma L.
\]
楔点把 \(D\) 中的 \(p\) 与 \(\Sigma L\) 的高度 \(0\) 极点相认。由于 \(D\) 路径连通，可在给定零伦末端接一条路径，使 \(p\) 成为任意指定的点。悬挂的两个极点则可由反转高度互换。

## S3 整数扭结的实例

对给定的三角剖分 \(L\)，取两个新顶点 \(v,w\)，令
\[
K=(v*L)\cup_L(w*L).
\]
从 \(L\) 中任选顶点 \(u\)，取 \(B\) 为边 \([u,v]\) 及其所有面。于是 \(|K|\cong\Sigma|L|\)。以 \(w\) 为高度 \(0\) 的极点、\(v\) 为高度 \(1\) 的极点，去掉 \(v\) 后的空间非空，并由
\[
[z,t]\longmapsto [z,(1-s)t],\qquad 0\le s\le1,
\]
收缩到 \(w\)。闭边 \([u,v]\) 及半开边 \([u,v)\) 都可沿边收缩到 \(u\)，所以题中的包含 \([u,v)\hookrightarrow[u,v]\) 是同伦等价。

对任一非空有限复形的实现 \(T\)，用分别删去一个极点得到的两个开集覆盖 \(\Sigma T\)。两开集都可缩，交集为 \(T\times(0,1)\)。约化 Mayer–Vietoris 正合列因此给出
\[
\widetilde H_{i+1}(\Sigma T;R)\cong \widetilde H_i(T;R)
\qquad(i\ge0),
\]
且 \(\Sigma T\) 路径连通。

\(\mathbb{RP}^2\) 的标准 CW 分解在维数 \(0,1,2\) 各有一个胞腔，二维胞腔的附着映射次数为 \(2\)，故其整系数胞腔边界为 \(\partial_2=2,\ \partial_1=0\)。于是 \(\mathbb{RP}^2\) 的约化有理同调全零，而 \(H_1(\mathbb{RP}^2;\mathbb Z)=\mathbb Z/2\)。由悬挂同构，
\[
\widetilde H_*(|K|;\mathbb Q)=0,\qquad
H_2(|K|;\mathbb Z)\cong\mathbb Z/2.
\]
后一个群说明 \(|K|\) 不可缩。

## S4 整体同伦类型、实现与可缩判据

**可能的同伦类型恰为 \(\Sigma|L|\)，其中 \(L\) 取遍至少有一个顶点的有限单纯复形。** 对给定的三元组，可以直接取 \(L=\operatorname{lk}_K(v)\)。

令
\[
K_0=\{\sigma\in K:v\notin\sigma\},\qquad
L_v=\operatorname{lk}_K(v)
=\{\tau\in K_0:\tau\cup\{v\}\in K\},
\qquad D=|K_0|,\quad T=|L_v|.
\]
先证 \(D\) 是 \(O\) 的强形变收缩核。若 \(x\in O\) 的重心坐标为 \((t_u)_u\)，则 \(t_v<1\)。定义
\[
r(x)_v=0,\qquad r(x)_u=\frac{t_u}{1-t_v}\quad(u\ne v).
\]
点 \(r(x)\) 位于 \(x\) 所在单形删去 \(v\) 后的面中，因而属于 \(D\)。直线同伦 \((1-s)x+s\,r(x)\) 留在原单形中，其 \(v\) 坐标始终小于 \(1\)，且它逐点固定 \(D\)。因此 \(D\) 非空可缩。

若 \(B\) 中没有以 \(v\) 为端点的边，则 \(\{v\}\) 是 \(C\) 的一个路径分支，而 \(O\cap C\hookrightarrow C\) 遗漏这个分支，与同伦等价在路径分支上诱导双射矛盾。因此 \(B\) 中存在这样的边，特别地 \(T\ne\varnothing\)。

每个含 \(v\) 的单形都属于锥 \(v*L_v\)，且该锥与 \(K_0\) 的交为 \(L_v\)。由于 \(D\) 是 \(X\) 的非空可缩子复形，S1 给出
\[
X\simeq X/D\cong |v*L_v|/T\cong\Sigma T.
\]
反过来，给定任意至少有一个顶点的有限 \(L\)，取 S3 的双锥 \(K=(v*L)\cup_L(w*L)\) 和边子复形 \(B=[u,v]\)。S3 中收缩到 \(w\) 和收缩到 \(u\) 的两个构造对这个 \(L\) 同样适用，故实现了所列的每一种类型。

**可缩的充要条件为**
\[
\boxed{\quad \widetilde H_i(L_v;\mathbb Z)=0\quad\text{对所有 }i\ge0.\quad}
\]
必要性来自 \(X\simeq\Sigma T\) 和 S3 的悬挂同构。反之，若这些群全零，则由 \(T\ne\varnothing\) 和 \(\widetilde H_0(T;\mathbb Z)=0\) 知 \(T\) 路径连通。S3 所用的两个可缩开集此时也有路径连通的交集，故由 van Kampen 定理，\(\Sigma T\) 单连通。其约化整系数同调又由悬挂同构全为零。若它有非零同伦群，取最小的此种维数 \(n\ge2\)，则 Hurewicz 定理给出 \(\pi_n(\Sigma T)\cong H_n(\Sigma T;\mathbb Z)=0\)，矛盾。因此 \(\Sigma T\to *\) 是 CW 复形之间的弱同伦等价，由 Whitehead 定理即为同伦等价。

这个判据可以只用指定的关联数据检验。将每个含 \(v\) 的单形删去 \(v\)，其面包含关系正好给出 \(L_v\) 的面包含关系。给以 \(v\) 为端点的边任选一个全序，就给链环顶点排了序，可据此写出带符号的整系数单纯边界矩阵。检验增广链复形
\[
\cdots\longrightarrow C_1(L_v;\mathbb Z)
\longrightarrow C_0(L_v;\mathbb Z)
\xrightarrow{\epsilon}\mathbb Z\longrightarrow0
\]
是否正合即可，其中 \(\epsilon\) 将每个顶点送到 \(1\)。这些矩阵都是有限的，可用 Smith 标准形计算其整系数同调。

## S5 不提供子复形 \(B\)

**不一定是非空有限复形的悬挂，唯一新增的同伦类型是 \(S^0\)。**

S4 中 \(O\) 到 \(D\) 的强形变收缩只用到 \(K,v\)，所以 \(D\) 仍然非空可缩。若 \(T=|\operatorname{lk}_K(v)|\ne\varnothing\)，同一个商构造给出 \(X\simeq\Sigma T\)。若 \(T=\varnothing\)，则 \(v\) 是孤立顶点，从而
\[
X=D\sqcup\{v\}\simeq S^0.
\]
取 \(K\) 为两个孤立顶点即可实现后一情形，去掉 \(v\) 后只剩一点。每个非空空间的非约化悬挂都是路径连通的，因为其中的点可沿悬挂线连到极点。因此 \(S^0\) 确实是新增类型。

## S6 悬挂信息的逆向恢复

**不能推出，甚至两个底空间都路径连通时也不能。** 取 \(L_1\) 为环面 \(T^2\) 的有限三角剖分，取 \(L_2\) 为两个三角形边界和一个四面体边界在一个公共顶点处的楔和。于是
\[
|L_1|=T^2,\qquad |L_2|\cong S^1\vee S^1\vee S^2.
\]
两者的基本群分别为 \(\mathbb Z^2\) 和二生成元自由群，故不同伦等价。

为计算悬挂，两空间都可取一个顶点、两个一维胞腔和一个二维胞腔的 CW 分解。环面的二维附着词为交换子 \(aba^{-1}b^{-1}\)，另一空间的二维附着映射为常值。因此二者的二维胞腔边界均为零，均有 \(H_2\cong\mathbb Z\)。

记其中任一空间为 \(Z\)。在 \(\Sigma Z\) 中，原顶点扫出的极点连线是可缩子复形，由 S1 可将它压为一点而保持同伦型。每个其余开胞腔 \(e^k\) 扫出一个开胞腔 \(e^k\times(0,1)\)，故所得商具有形式
\[
Q=(S^2\vee S^2)\cup_\alpha D^3.
\]
由 S3，\(H_3(Q;\mathbb Z)\cong H_2(Z;\mathbb Z)\cong\mathbb Z\)。因此胞腔边界 \(\partial_3:\mathbb Z\to\mathbb Z^2\) 有非零核，只能是零映射。它将三维胞腔的生成元送到 \(\alpha_*[S^2]\)，故该同调类为零。由于 \(S^2\vee S^2\) 单连通，Hurewicz 映射 \(\pi_2\to H_2\) 是同构，故 \(\alpha\) 零伦。现在 \(D^3=CS^2\)，由 S2 中对零伦映射的锥附着计算，
\[
\Sigma|L_1|\simeq S^2\vee S^2\vee S^3\simeq\Sigma|L_2|.
\]