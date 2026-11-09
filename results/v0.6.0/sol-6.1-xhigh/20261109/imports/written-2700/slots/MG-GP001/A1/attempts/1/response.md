**S1**

记 \(q:Y\to Y/A\)。取 \(A\) 的收缩
\[
h:A\times I\to A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
由于子复形包含 \(A\hookrightarrow Y\) 是上纤维化，具有同伦延拓性质，故 \(h\) 与 \(\operatorname{id}_Y\) 延拓为
\[
H:Y\times I\to Y,\qquad H_0=\operatorname{id}_Y,\quad H|_{A\times I}=h.
\]
因为 \(H_1(A)=\{a_0\}\)，\(H_1\) 唯一分解为
\[
H_1=fq,\qquad f:Y/A\to Y.
\]
于是 \(fq\simeq\operatorname{id}_Y\)。

另一方面，对每个 \(t\)，都有 \(H_t(A)\subseteq A\)，所以 \(qH_t\) 在整个 \(A\) 上取同一值。因此 \(qH\) 下降为同伦
\[
\overline H:(Y/A)\times I\to Y/A.
\]
这里联合连续性也有保证：有限 CW 复形 \(Y\) 紧且 Hausdorff，\(A\) 闭，故 \(Y/A\) 是紧 Hausdorff 空间；于是连续满射
\[
q\times\operatorname{id}_I:Y\times I\longrightarrow (Y/A)\times I
\]
是商映射。因而上述下降映射连续。

其两端满足
\[
\overline H_0=\operatorname{id}_{Y/A},\qquad \overline H_1=qf.
\]
故 \(q\) 与 \(f\) 互为同伦逆。关键在于延拓时指定了 \(H|_{A\times I}=h\)，保证整个同伦都把 \(A\) 映入 \(A\)。

---

**S2**

先说明所用的映射锥事实。对于同伦映射 \(f,g:L\to D\)，其映射锥
\[
C_f=D\cup_f CL,\qquad C_g=D\cup_g CL
\]
同伦等价。

事实上，设 \(F:L\times I\to D\) 从 \(f\) 同伦到 \(g\)，以 \(t=0\) 表示锥底、\(t=1\) 表示锥尖。定义 \(T_F:C_f\to C_g\)，在 \(D\) 上为恒等，在锥上为
\[
T_F([\ell,t])=
\begin{cases}
F(\ell,2t),&0\le t\le \frac12,\\
[\ell,2t-1],&\frac12\le t\le1.
\end{cases}
\]
各拼接处相容，故这是连续映射。反向同伦给出反向映射。两个复合在锥坐标上都表现为：先沿同伦往返一次，再进入原锥。往返段经重新参数化后，可用
\[
F\bigl(\ell,r\min\{2s,2-2s\}\bigr),\qquad r:1\longrightarrow0,
\]
缩成常值段，再缩短这一常值段，便得到恒等映射。这些同伦均固定 \(D\)，证明了该事实。

现在令 \(i:L\hookrightarrow D\)。按假设，\(i\) 同伦于常值映射 \(c_{d_0}\)，于是
\[
Y=C_i\simeq C_{c_{d_0}}
\cong D\vee_{d_0}(CL/L).
\]
而
\[
CL/L\cong \Sigma L,
\]
因为锥底被压成一个悬挂极点，锥尖是另一个极点。因此
\[
\boxed{Y\simeq D\vee\Sigma L.}
\]

楔点在 \(D\) 中取零伦的常值点 \(d_0\)，在 \(\Sigma L\) 中取由锥底压成的极点。由于 \(D\) 路径连通，可以在零伦后接上一条路径，把 \(d_0\) 改为任意指定点；特别可以选一个 \(0\)-胞腔，使楔和具有通常的 CW 结构。

---

**S3**

先记录一个也用于后文的删点事实。对有限单纯复形 \(K\) 的顶点 \(v\)，令
\[
D=\{\sigma\in K:v\notin\sigma\}
\]
为删点子复形。若 \(x\ne v\) 的重心坐标为 \((t_u)\)，则 \(t_v<1\)，可定义
\[
r(x)=\sum_{u\ne v}\frac{t_u}{1-t_v}\,u.
\]
它落在包含 \(x\) 的单形去掉 \(v\) 所得的面内。直线同伦
\[
R_s(x)=(1-s)x+sr(x)
\]
始终留在同一单形内且不经过 \(v\)，并固定 \(|D|\)。所以
\[
|K|\setminus\{v\}\ \text{强形变收缩到}\ |D|.
\tag{1}
\]

现在取两个新顶点 \(v,w\)，定义
\[
K=(v*L)\cup_L(w*L).
\]
即取 \(L\) 的单纯悬挂，因此
\[
|K|\cong\Sigma|L|.
\]
任选 \(L\) 的顶点 \(a\)，令 \(B\) 为边 \(\{v,a\}\) 及其所有面。

删点子复形为 \(D=w*L\)，它非空且可缩。由 (1)，\(|K|\setminus\{v\}\) 非空可缩。另一方面，\(|B|\) 和 \(|B|\setminus\{v\}\) 都可沿该边收缩到 \(a\)，所以
\[
|B|\setminus\{v\}\hookrightarrow |B|
\]
是同伦等价。

由于 \(|L|\cong\mathbb {RP}^2\)，其约化有理同调全零。悬挂同调移位给出
\[
\widetilde H_n(|K|;\mathbb Q)=0\qquad\text{对所有 }n.
\]
但整数系数下
\[
\widetilde H_2(|K|;\mathbb Z)
\cong \widetilde H_1(\mathbb {RP}^2;\mathbb Z)
\cong\mathbb Z/2.
\]
故 \(|K|\) 不可缩，满足全部要求。

---

**S4**

结论是：
\[
\boxed{\text{可能的同伦类型，恰为所有非空有限单纯复形的非约化悬挂。}}
\tag{2}
\]

令 \(D\) 为上述删点子复形，令
\[
L=\operatorname{lk}_K(v)
=\{\tau\in K:v\notin\tau,\ \tau\cup\{v\}\in K\}.
\]
以下说链结非空，均指 \(|L|\ne\varnothing\)，即链结含有顶点。单纯复形有分解
\[
K=D\cup_L(v*L).
\tag{3}
\]

由 (1)，\(O\) 强形变收缩到 \(|D|\)。所以 \(|D|\) 非空可缩。

条件 \(B\) 保证 \(|L|\ne\varnothing\)。否则 \(v\) 不属于任何边，是 \(X\) 的孤立点，因而也是 \(C\) 的一个单独分支。映射
\[
O\cap C=C\setminus\{v\}\longrightarrow C
\]
便遗漏了该分支，不可能在路径分支集合上诱导双射，与其为同伦等价矛盾。

由 S1，可缩子复形 \(|D|\) 的商映射是同伦等价。再由 (3)，
\[
X\simeq X/|D|
\cong |v*L|/|L|
\cong\Sigma|L|.
\tag{4}
\]
这里商空间的同胚来自两个闭子复形的拼接；锥底压成一个极点，\(v\) 是另一个极点。这证明所有满足条件的 \(X\) 都在 (2) 中。

反过来，给定任意非空有限单纯复形 \(M\)，取
\[
K=(v*M)\cup_M(w*M),
\]
并取 \(M\) 的任一顶点 \(a\)，令 \(B\) 为边 \(\{v,a\}\) 及其面。S3 的验证原样适用：删点空间强形变收缩到锥 \(w*M\)，而边及其删去端点后的空间均收缩到 \(a\)。故全部原条件成立，且
\[
|K|\cong\Sigma|M|.
\]
因此 (2) 中每一种类型均有实现。

可缩性的局部判据为
\[
\boxed{
X\text{ 可缩}
\quad\Longleftrightarrow\quad
\widetilde H_j(\operatorname{lk}_K(v);\mathbb Z)=0
\quad\text{对所有 }j\ge0.
}
\tag{5}
\]

必要性由 (4) 和悬挂同调移位立即得到。证明充分性时，链结的约化整数同调全零，特别是 \(\widetilde H_0(L;\mathbb Z)=0\)，故有限复形 \(|L|\) 路径连通。悬挂可由两个可缩的开锥邻域覆盖，其交集同伦等价于 \(|L|\)。因此 van Kampen 定理适用，给出
\[
\pi_1(\Sigma|L|)=0.
\]
悬挂同调移位又说明 \(\Sigma|L|\) 的约化整数同调全零。

单连通、整数无约化同调的 CW 复形可缩：若存在非零同伦群，取最小的相应次数，Hurewicz 定理将其同构到同次数的非零同调群，矛盾；于是到一点的映射是弱同伦等价，再由 Whitehead 定理是同伦等价。这里 \(\Sigma|L|\) 是有限 CW 复形，满足适用条件。这证明了 (5)。

最后，(5) 确实只需题目指定的有限局部数据即可检验。对每个含 \(v\) 的单形删去 \(v\)，便得到链结的全部单形及面关联。给其他顶点排序，构造增广整数单纯链复形
\[
\cdots\longrightarrow C_1(L;\mathbb Z)
\longrightarrow C_0(L;\mathbb Z)
\xrightarrow{\epsilon}\mathbb Z\longrightarrow0,
\qquad \epsilon([a])=1.
\]
其中 \(C_q(L;\mathbb Z)\) 的基与含 \(v\) 的 \((q+1)\)-单形对应，边界仅涉及删去非 \(v\) 顶点的面。判据就是此增广链复形处处正合。利用整数矩阵的 Smith 标准形计算核、像并检验相等，是有限算法，无须读取 \(K\) 的其他单形。

---

**S5**

不一定。去掉 \(B\) 后，恰好新增一种同伦类型：
\[
\boxed{S^0.}
\]

仍用删点子复形 \(D\) 和链结 \(L\)。由 (1)，\(|D|\) 非空可缩。

- 若 \(|L|\ne\varnothing\)，S4 中的商论证仍适用，得到
  \[
  |K|\simeq\Sigma|L|.
  \]
  此时也总能补选一条以 \(v\) 为端点的边作为 \(B\)。
- 若 \(|L|=\varnothing\)，则 \(v\) 孤立，
  \[
  |K|=|D|\sqcup\{v\}\simeq S^0.
  \]

取只有两个孤立顶点 \(v,w\) 的有限复形即可实现后一种情况：删去 \(v\) 后是单点，但整体为 \(S^0\)。非空空间的非约化悬挂总是路径连通，所以 \(S^0\) 不可能同伦等价于题目所说的悬挂。

---

**S6**

不必。取有限单纯复形 \(L_1,L_2\)，分别实现
\[
T^2,\qquad W=S^1\vee S^1\vee S^2.
\]
二环面具有有限三角剖分；\(W\) 可由两个三角形边界和一个四面体边界，在各自一个顶点处相交构造为有限单纯复形。

它们不同伦等价，因为
\[
\pi_1(T^2)\cong\mathbb Z^2,\qquad
\pi_1(W)\cong F_2,
\]
前者交换，后者不交换。下面验证它们的悬挂同伦等价。

记约化悬挂为 \(\Sigma_r\)。对带 \(0\)-胞腔基点的有限 CW 复形 \(Z\)，非约化悬挂中基点扫出的弧是可缩子复形，压掉此弧得到 \(\Sigma_r Z\)。由 S1，
\[
\Sigma Z\simeq\Sigma_r Z.
\tag{6}
\]

二环面的通常 CW 分解为
\[
T^2=(S^1\vee S^1)\cup_f D^2,
\]
其中 \(f:S^1\to S^1\vee S^1\) 代表交换子 \([a,b]\)。约化悬挂保持带基点 CW 映射的同伦余纤维，因此
\[
\Sigma_r T^2\simeq C_{\Sigma_r f},
\qquad
\Sigma_r f:S^2\longrightarrow S^2\vee S^2.
\]
这里所有基点都是 \(0\)-胞腔，附着给出 CW 同伦余纤维，故该性质适用。

交换子在一维同调中为零。由悬挂同调移位的自然性，\(\Sigma_r f\) 在二维同调中也为零。而 \(S^2\vee S^2\) 单连通，Hurewicz 定理给出
\[
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z).
\]
因此 \(\Sigma_r f\) 零伦。应用 S2 证明中的映射锥引理，
\[
\Sigma_r T^2\simeq S^2\vee S^2\vee S^3.
\]
另一方面，约化悬挂保持楔和，故
\[
\Sigma_r W\cong S^2\vee S^2\vee S^3.
\]
结合 (6)，得到
\[
\boxed{\Sigma|L_1|\simeq\Sigma|L_2|,
\qquad |L_1|\not\simeq|L_2|.}
\]