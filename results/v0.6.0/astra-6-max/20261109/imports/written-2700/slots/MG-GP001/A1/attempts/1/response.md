**S1**

记商映射为 \(q:Y\to Y/A\)。选取 \(a_0\in A\) 及收缩
\[
h:A\times I\to A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
因为 \(A\subseteq Y\) 是 CW 子复形，包含映射具有同伦延拓性质，所以 \(h\) 可延拓为
\[
H:Y\times I\to Y,\qquad H(y,0)=y,\quad H|_{A\times I}=h.
\]
于是 \(H_1\) 在 \(A\) 上恒等于 \(a_0\)，故存在连续映射
\[
g:Y/A\to Y,\qquad gq=H_1.
\]
因此 \(gq\simeq\operatorname{id}_Y\)。

另一方面，对每个 \(t\)，都有 \(H_t(A)\subseteq A\)，所以 \(qH_t\) 在 \(A\) 上为常值。这使 \(qH\) 下降为
\[
\overline H:(Y/A)\times I\to Y/A.
\]
下降后的映射确实连续：有限 CW 复形 \(Y\) 紧且 Hausdorff，子复形 \(A\) 闭，故 \(Y/A\) 为 Hausdorff；因此连续满射
\[
q\times\operatorname{id}_I:Y\times I\to(Y/A)\times I
\]
是从紧空间到 Hausdorff 空间的商映射。由商拓扑的性质，\(\overline H\) 连续。

现在
\[
\overline H_0=\operatorname{id}_{Y/A},\qquad
\overline H_1=qg.
\]
故 \(qg\simeq\operatorname{id}_{Y/A}\)，证明 \(q\) 是同伦等价。这里下降的是 **\(qH\)**；关键条件是 \(H_t(A)\subseteq A\)，并不要求 \(H_t\) 逐点固定 \(A\)。

---

**S2**

成立。选定 \(D\) 的一个 \(0\)-胞腔 \(d_0\)。包含映射 \(i:L\to D\) 零伦，而 \(D\) 路径连通，因此可选零伦
\[
F:L\times I\to D,\qquad F(x,0)=i(x),\quad F(x,1)=d_0.
\]

使用如下映射锥事实：同伦的映射 \(f,g:L\to D\) 具有同伦等价的映射锥，而且该同伦等价可在 \(D\) 上取恒等。具体地，记
\[
M_f=\bigl(D\amalg(L\times I)\bigr)/
\bigl((x,0)\sim f(x),\ L\times\{1\}\text{ 压成一点}\bigr).
\]
若 \(F:f\simeq g\)，则定义 \(\Phi:M_f\to M_g\) 在 \(D\) 上为恒等，在锥上为
\[
\Phi([x,t])=
\begin{cases}
F(x,2t),&0\le t\le \tfrac12,\\
[x,2t-1],&\tfrac12\le t\le1.
\end{cases}
\]
两段在 \(t=\tfrac12\) 处相容，并满足商空间的识别关系，故连续。反向同伦给出反向映射。两者的复合在锥上先沿 \(F\) 往返，再进入锥；将往返同伦收缩为常值同伦，并重参数化锥坐标，就得到相对于 \(D\) 的恒等同伦。这证明了所述事实。

本题中 \(Y=M_i\)，故
\[
Y\simeq M_{\mathrm{const}_{d_0}}.
\]
常值映射的映射锥把锥的整个底面 \(L\) 接到 \(d_0\)，因而
\[
M_{\mathrm{const}_{d_0}}
\cong D\vee(CL/L)
\cong D\vee\Sigma L.
\]

这里 \(\Sigma L\) 是非约化悬挂；楔点取为 \(D\) 中的 \(d_0\) 与悬挂中由锥底面压缩得到的那个极点。由于 \(D\) 路径连通，\(d_0\) 可以预先选为任意 \(0\)-胞腔，再相应调整零伦。整个论证不要求 \(L\) 连通。

---

**S3**

取两个不属于 \(L\) 的新顶点 \(v,w\)，令
\[
K=(v*L)\cup(w*L),
\]
即 \(L\) 的单纯悬挂，其中没有同时包含 \(v,w\) 的单形。选取 \(L\) 的任一顶点 \(a\)，令 \(B\) 为边 \(\{v,a\}\) 及其全部面的子复形。

这是有限单纯复形，且
\[
|K|\cong\Sigma|L|\cong\Sigma\mathbb{RP}^{2}.
\]

验证删点条件。把悬挂写成高度参数 \(t\in[-1,1]\)，令 \(w\) 为下极点、\(v\) 为上极点。在删去 \(v\) 后，公式
\[
H_s([x,t])=[x,(1-s)t-s],\qquad -1\le t<1,
\]
给出到 \(w\) 的收缩。因此 \(|K|\setminus\{v\}\) 非空且可缩。

此外，\(|B|\) 是闭区间，\(|B|\setminus\{v\}\) 是包含另一端点 \(a\) 的半开区间。两者都沿区间收缩到 \(a\)，所以包含映射是同伦等价。

最后，\(\mathbb{RP}^{2}\) 的整数约化同调为
\[
\widetilde H_j(\mathbb{RP}^{2};\mathbb Z)=
\begin{cases}
\mathbb Z/2,&j=1,\\
0,&j\ne1.
\end{cases}
\]
对非空空间的悬挂，覆盖两个极点的可缩开锥邻域给出约化 Mayer–Vietoris 同构
\[
\widetilde H_n(\Sigma|L|;R)
\cong\widetilde H_{n-1}(|L|;R),\qquad n\ge1.
\]
因此
\[
\widetilde H_*(|K|;\mathbb Q)=0,
\qquad
\widetilde H_2(|K|;\mathbb Z)\cong\mathbb Z/2.
\]
后者说明 \(|K|\) 不可缩，所有要求均满足。

---

**S4**

全部可能同伦类型恰好是
\[
\boxed{\ \Sigma|L|,\qquad L\text{ 为几何实现非空的有限单纯复形}\ }.
\]
相应的局部判据是
\[
\boxed{\ X\text{ 可缩}
\iff
\widetilde H_j(\operatorname{lk}_K(v);\mathbb Z)=0
\quad\text{对所有 }j\ge0.\ }
\]

下面证明分类、实现及判据。

令
\[
K_0=\{\sigma\in K:v\notin\sigma\},\qquad
L_v=\operatorname{lk}_K(v)
=\{\sigma\in K_0:\sigma\cup\{v\}\in K\},
\]
并记 \(D=|K_0|\)。

首先，\(O\) 强形变收缩到 \(D\)。事实上，若 \(x\in O\) 的重心坐标为 \((\lambda_u)\)，则 \(\lambda_v<1\)，可以定义
\[
r(x)=\sum_{u\ne v}\frac{\lambda_u}{1-\lambda_v}\,u.
\]
它位于 \(x\) 所在单形的不含 \(v\) 的面中。直线同伦
\[
F_s(x)=(1-s)x+sr(x)
\]
始终留在该单形内且避开 \(v\)，并逐点固定 \(D\)。因此 \(D\) 非空且可缩。

其次，题设关于 \(B\) 的条件保证 \(L_v\) 非空。若 \(B\) 中没有以 \(v\) 为端点的边，那么 \(v\) 是 \(|B|\) 的一个孤立路径分支，而 \(O\cap C\) 完全缺少这个分支。这与同伦等价必须诱导路径分支集合的双射矛盾。因此 \(B\) 中存在某条边 \(\{v,a\}\)，特别地 \(L_v\) 有顶点。

现在有锥附着分解
\[
X=D\cup_{|L_v|}C|L_v|.
\]
其中 \(D\) 是 \(X\) 的非空可缩子复形。S1 的条件全部满足，故
\[
X\simeq X/D
\cong C|L_v|/|L_v|
\cong\Sigma|L_v|.
\]
这证明每个满足题设的 \(X\) 都属于所列类型。

反过来，给定任意非空有限单纯复形 \(L\)，取
\[
K=(v*L)\cup(w*L),\qquad B=\text{边 }\{v,a\}\text{ 及其面},
\]
其中 \(a\) 是 \(L\) 的一个顶点。此时 \(|K|\cong\Sigma|L|\)，删除复形为 \(w*L\)，其实现是非空可缩锥。由上面的强形变收缩，\(|K|\setminus\{v\}\) 可缩；边 \(B\) 的条件则由 S3 中的区间收缩验证。这实现了列表中的全部类型。

因此，在已满足删点可缩条件的 \((K,v)\) 中，**存在符合条件的 \(B\)，恰好等价于 \(v\) 不是孤立顶点**：必要性已经证明，充分性只需取一条以 \(v\) 为端点的边。

下面证明局部可缩判据。由悬挂同调同构，
\[
\widetilde H_{j+1}(X;\mathbb Z)
\cong\widetilde H_j(|L_v|;\mathbb Z),\qquad j\ge0.
\]
所以 \(X\) 可缩必然推出链接的整数约化同调全零。

反之，假设链接的整数约化同调全零。因为 \(L_v\) 非空且是有限复形，
\[
\widetilde H_0(|L_v|;\mathbb Z)=0
\]
说明 \(|L_v|\) 路径连通。悬挂的两个可缩开锥邻域之交同伦等价于 \(|L_v|\)，故 van Kampen 定理给出
\[
\pi_1(\Sigma|L_v|)=0.
\]
悬挂同调同构又说明它的整数约化同调全零。

单连通、整数约化同调全零的 CW 复形可缩：若有非零同伦群，取最小的 \(n\ge2\) 使 \(\pi_n\ne0\)，Hurewicz 定理将给出
\[
\pi_n\cong H_n\ne0,
\]
产生矛盾。因此所有同伦群均为零，再由 Whitehead 定理得其同伦等价于一点。应用于有限 CW 复形 \(\Sigma|L_v|\)，即得 \(X\) 可缩。

最后，这确实是只依赖所要求的有限局部数据的判据。每个含 \(v\) 的单形删除 \(v\) 后，恰好给出 \(L_v\) 的一个单形；它们之间的面关系给出整个链接。给链接顶点任取全序，就能写出有限增广整数单纯链复形
\[
0\longrightarrow C_d(L_v;\mathbb Z)
\xrightarrow{\partial_d}\cdots
\xrightarrow{\partial_1}C_0(L_v;\mathbb Z)
\xrightarrow{\varepsilon}\mathbb Z
\longrightarrow0,
\qquad \varepsilon(a)=1.
\]
所需判据就是这个链复形正合，可用整数矩阵的 Smith 标准形逐维计算核商像来检验。整个检验不需要闭星以外的单形数据。

---

**S5**

不必。新增的可能同伦类型恰好只有
\[
\boxed{S^0}.
\]

S4 中删点空间强形变收缩到删除复形 \(D=|K_0|\) 的证明不使用 \(B\)，故这里 \(D\) 仍然非空可缩。

分两种情况：

- 若 \(L_v\) 的几何实现非空，则仍由 S1 得
  \[
  |K|\simeq |K|/D\cong\Sigma|L_v|.
  \]
- 若 \(L_v\) 没有顶点，则 \(v\) 是孤立顶点，因而
  \[
  |K|=D\amalg\{v\}\simeq S^0.
  \]

非空空间的非约化悬挂总是路径连通，而 \(S^0\) 有两个路径分支，所以 \(S^0\) 不可能同伦等价于非空有限复形的悬挂。

取 \(K\) 为两个孤立顶点即可实现这一例外：删去其中一个顶点后只剩一点。其余全部类型已由 S4 的双锥构造实现。

---

**S6**

不必。取
\[
|L_1|=T^2=S^1\times S^1,\qquad
|L_2|=S^1\vee S^1\vee S^2.
\]
两者都具有非空有限单纯三角剖分；后者可由两个三角形边界和一个四面体边界，在各选一个顶点后识别这些顶点而得到。

我们证明
\[
\Sigma T^2\simeq S^2\vee S^2\vee S^3
\simeq\Sigma(S^1\vee S^1\vee S^2).
\]

以 \(0\)-胞腔为基点时，非约化悬挂中的基点悬挂线是一条可缩子复形。将其压缩便得到约化悬挂，因此由 S1，二者同伦等价。以下可使用约化悬挂 \(\Sigma_{\mathrm r}\)。

记两个投影为
\[
p_1,p_2:T^2\to S^1,
\]
并令
\[
\rho:T^2\to T^2/(S^1\vee S^1)\cong S^2
\]
为压缩标准 CW 分解中一维骨架的商映射。利用悬挂的三重捏合映射，构造
\[
\Sigma_{\mathrm r}T^2
\longrightarrow
\bigvee_{k=1}^{3}\Sigma_{\mathrm r}T^2
\xrightarrow{\ \Sigma p_1\vee\Sigma p_2\vee\Sigma\rho\ }
S^2\vee S^2\vee S^3.
\]
此映射在整数同调上是同构：

- 在二维悬挂同调上，两个投影给出
  \[
  H_1(T^2;\mathbb Z)\xrightarrow{\cong}
  H_1(S^1;\mathbb Z)\oplus H_1(S^1;\mathbb Z).
  \]
- 在三维悬挂同调上，\(\rho\) 给出
  \[
  H_2(T^2;\mathbb Z)\xrightarrow{\cong}H_2(S^2;\mathbb Z).
  \]
  这也直接来自环面的标准胞腔链复形：唯一二维胞腔的边界为零，而压缩一维骨架保留了这个二维生成元。
- 其余约化同调均为零。

源和目标都是单连通 CW 复形，因此适用同调版 Whitehead 定理，此映射为同伦等价。另一方面，约化悬挂保持有限楔和，故
\[
\Sigma_{\mathrm r}(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]
于是两者的非约化悬挂同伦等价。

但
\[
\pi_1(T^2)\cong\mathbb Z^2,\qquad
\pi_1(S^1\vee S^1\vee S^2)\cong F_2.
\]
前者交换，后者不交换，故原来的两个空间不同伦等价。