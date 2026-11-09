**S1．结论成立。**

取 \(a_0\in A\)，以及收缩
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0.
\]
子复形包含 \(A\hookrightarrow Y\) 是上纤维化，因而具有同伦延拓性质。将 \(h\) 与 \(\operatorname{id}_Y\) 延拓为
\[
H:Y\times I\longrightarrow Y,\qquad H_0=\operatorname{id}_Y,\quad H|_{A\times I}=h.
\]
由于 \(H_1\) 在 \(A\) 上恒等于 \(a_0\)，它经商映射 \(q:Y\to Y/A\) 分解为
\[
H_1=gq,\qquad g:Y/A\longrightarrow Y.
\]
所以 \(gq\simeq\operatorname{id}_Y\)。

还需验证另一侧，并解释同伦为何下降。对每个 \(t\)，有
\[
H(A,t)\subseteq A,
\]
因此 \(qH(-,t)\) 在 \(A\) 上取同一个值。故公式
\[
\overline H([y],t)=q(H(y,t))
\]
良定义。其连续性来自 \(q\times\operatorname{id}_I\) 是商映射：有限 CW 复形 \(Y\) 紧致，闭子复形 \(A\) 的商 \(Y/A\) 为 Hausdorff 空间，所以这是从紧空间到 Hausdorff 空间的连续满射。于是
\[
\overline H_0=\operatorname{id}_{Y/A},\qquad \overline H_1=qg.
\]
因此 \(q\) 与 \(g\) 互为同伦逆。

注意，下降的是 \(qH\)；关键条件是整个同伦始终将 \(A\) 映入 \(A\)。

---

**S2．结论成立，楔点可取 \(D\) 的任一选定 \(0\)-胞腔与悬挂的一个悬挂点。**

先说明所用的映射锥事实。记
\[
C_f=D\cup_f CL.
\]
若 \(f,g:L\to D\) 经 \(F:L\times I\to D\) 同伦，则 \(C_f\simeq C_g\)。具体地，令锥坐标 \(t=0\) 为底面、\(t=1\) 为锥顶，定义一个在 \(D\) 上为恒等的映射
\[
\Phi_F:C_f\longrightarrow C_g,\qquad
[x,t]\longmapsto
\begin{cases}
F(x,2t),&0\le t\le \tfrac12,\\
[x,2t-1],&\tfrac12\le t\le1.
\end{cases}
\]
两段在接合处相容，也与底面的粘合相容。

反向同伦给出反向映射。两个复合在每条锥线上都先沿同伦路径往返，再沿原锥线前进。将往返路径的行进长度连续缩至零，再重参数化锥线，便得到到恒等映射的同伦；这些同伦在 \(D\) 上固定。因此上述映射确为同伦等价。

现在选定 \(D\) 的一个 \(0\)-胞腔 \(d_0\)。包含 \(i:L\hookrightarrow D\) 零伦；由于 \(D\) 路径连通，可在原零伦后接一条路径，使终点为常值映射 \(c_{d_0}\)。于是
\[
Y=C_i\simeq C_{c_{d_0}}
=D\vee_{d_0=s_-}(CL/L)
=D\vee\Sigma L.
\]
这里 \(s_-\) 是把锥底 \(L\) 压成的悬挂点，另一个悬挂点来自锥顶。因此使用的是**非约化悬挂**，不需要为 \(L\) 选择基点。

更换 \(D\) 中所选的 \(0\)-胞腔时，两常值映射由路径给出同伦，上述映射锥论证仍适用。两个悬挂点则可由悬挂坐标反向的同胚交换。

---

**S3．取 \(\mathbb{RP}^2\) 的双锥，即可得到所需实例。**

先记录供 S3–S5 使用的删点事实。对有限单纯复形 \(K\) 的顶点 \(v\)，定义删点子复形
\[
D_v=\{\sigma\in K:v\notin\sigma\}.
\]
则
\[
|K|\setminus\{v\}\ \searrow\ |D_v|.
\]
事实上，若 \(x\ne v\) 的重心坐标为 \((\lambda_w)\)，则 \(\lambda_v<1\)，可以定义
\[
r(x)_v=0,\qquad
r(x)_w=\frac{\lambda_w}{1-\lambda_v}\quad(w\ne v).
\]
线性同伦 \((1-t)x+tr(x)\) 始终位于包含 \(x\) 的原单形内，不经过 \(v\)，并固定 \(|D_v|\)，故是强形变收缩。

现在取题给的三角剖分 \(L\)，添加两个新顶点 \(a,v\)，令
\[
K=(a*L)\cup_L(v*L).
\]
于是
\[
|K|\cong\Sigma|L|\cong\Sigma\mathbb{RP}^2.
\]
任取 \(L\) 的顶点 \(w\)，令 \(B\) 为边 \(\{v,w\}\) 及其全部面组成的子复形。

逐项验证：

- \(D_v=a*L\)，其实现是非空可缩的锥。因此 \(|K|\setminus\{v\}\) 非空可缩。
- \(|B|\) 是闭区间，\(|B|\setminus\{v\}\) 是含端点 \(w\) 的半开区间。两者均可沿区间收缩到 \(w\)，故包含映射是同伦等价。
- 对非空空间 \(Z\)，悬挂的两个加厚锥给出的约化 Mayer–Vietoris 序列给出
  \[
  \widetilde H_{q+1}(\Sigma Z;\mathbb Z)
  \cong \widetilde H_q(Z;\mathbb Z),\qquad q\ge0.
  \]
  而 \(\mathbb{RP}^2\) 的胞腔链复形中，二维边界为乘以 \(2\)，一维边界为零。因此
  \[
  \widetilde H_q(|K|;\mathbb Z)=
  \begin{cases}
  \mathbb Z/2,&q=2,\\
  0,&q\ne2.
  \end{cases}
  \]

所以 \(|K|\) 的约化有理同调全零，但其二阶整数同调非零，故不可缩。

---

**S4．全部目标成立。可能的同伦类型恰为非空有限单纯复形的非约化悬挂；可缩的充要条件是顶点 link 的约化整数同调全零。**

令
\[
D=D_v,\qquad
\Lambda=\operatorname{lk}_K(v)
=\{\tau\in D:\tau\cup\{v\}\in K\}.
\]

**先证明分类。** 由 S3 的形变收缩，\(|D|\simeq O\)，所以 \(|D|\) 非空可缩。

此外，\(|\Lambda|\ne\varnothing\)。否则没有边连接 \(v\) 与其他顶点，\(v\) 就是 \(X\) 的孤立点，也是 \(C\) 的独立路径分支。但
\[
O\cap C=C\setminus\{v\}\longrightarrow C
\]
遗漏这个路径分支，不可能在路径分支集合上诱导双射，因而不可能是同伦等价。

现在有单纯复形分解
\[
K=D\cup_\Lambda(v*\Lambda).
\]
应用 S1：\(|D|\) 是有限 CW 复形 \(X\) 的非空可缩子复形，故
\[
X\simeq X/|D|
\cong C|\Lambda|/|\Lambda|
\cong\Sigma|\Lambda|.
\]
这证明了必要方向。

**实现全部类型。** 对任意非空有限单纯复形 \(L\)，取
\[
K=(a*L)\cup_L(v*L),\qquad B=\{v,w\}\text{ 及其全部面},
\]
其中 \(a,v\) 是新顶点，\(w\) 是 \(L\) 的任一顶点。S3 对删点空间及 \(B\) 的验证完全不依赖于 \(L=\mathbb{RP}^2\)，所以这个构造满足全部原条件，并且
\[
|K|\cong\Sigma|L|.
\]
因此可能同伦类型的集合准确地是
\[
\boxed{\{[\Sigma|L|]:L\text{ 为非空有限单纯复形}\}.}
\]
这里并不声称不同 \(L\) 一定给出不同同伦类型；S6 将说明这种唯一性不成立。

**给出仅依赖局部关联数据的判据。** 任意排列 \(v\) 以外的顶点。对 \(q\ge0\)，令
\[
\mathcal C_q=
\bigoplus_{\{v,w_0,\ldots,w_q\}\in K}
\mathbb Z[w_0,\ldots,w_q],
\qquad w_0<\cdots<w_q.
\]
定义
\[
\partial_q[w_0,\ldots,w_q]
=\sum_{i=0}^q(-1)^i[w_0,\ldots,\widehat w_i,\ldots,w_q]
\quad(q\ge1),
\]
并定义增广
\[
\varepsilon:\mathcal C_0\to\mathbb Z,\qquad [w]\mapsto1.
\]
这是 \(\Lambda\) 的增广单纯链复形。每个生成元及其边界关联，都由包含 \(v\) 的单形之间的面关系确定。

所求判据为
\[
\boxed{
X\text{ 可缩}
\iff
0\longrightarrow\mathcal C_d\longrightarrow\cdots
\longrightarrow\mathcal C_0
\xrightarrow{\varepsilon}\mathbb Z\longrightarrow0
\text{ 正合}.
}
\]
这里 \(d=\dim\Lambda\)。这是有限整数矩阵的正合性问题，可以通过整数线性代数及 Smith 标准形检验。

证明如下：

- 若 \(X\) 可缩，则 \(X\simeq\Sigma|\Lambda|\) 以及悬挂同调同构给出
  \[
  \widetilde H_q(|\Lambda|;\mathbb Z)=0\qquad(q\ge0),
  \]
  所以上述增广链复形正合。
- 反之，正合性说明 \(|\Lambda|\) 非空、连通且约化整数同调全零。有限单纯复形的连通性蕴含路径连通性。悬挂的两个加厚锥均可缩，交集同伦等价于路径连通的 \(|\Lambda|\)，故 van Kampen 定理给出
  \[
  \pi_1(\Sigma|\Lambda|)=0.
  \]
  悬挂同调同构又说明其约化整数同调全零。

最后，单连通且整数同调平凡的 CW 复形可缩：若存在非零高阶同伦群，取最小的这样的次数 \(n\)，Hurewicz 定理将给出非零 \(H_n\)，矛盾。因此所有同伦群均为零，再由 CW 复形的 Whitehead 定理得到它与一点同伦等价。应用于 \(\Sigma|\Lambda|\)，即可得 \(X\) 可缩。

---

**S5．不一定。去掉 \(B\) 后，只新增 \(S^0\) 这一种同伦类型。**

仍令 \(D=D_v\)、\(\Lambda=\operatorname{lk}_K(v)\)。删点形变收缩说明 \(|D|\) 非空可缩。

若 \(|\Lambda|\ne\varnothing\)，S4 的商空间论证仍然适用，得到
\[
|K|\simeq\Sigma|\Lambda|.
\]
这部分不需要 \(B\)。

若 \(|\Lambda|=\varnothing\)，则 \(v\) 孤立，因而
\[
|K|=|D|\amalg\{v\}\simeq\{\ast\}\amalg\{v\}=S^0.
\]
这个类型确实可以实现：取 \(K\) 仅由两个孤立顶点 \(v,w\) 组成。删去 \(v\) 后只剩一点，满足题设。

非空空间的非约化悬挂总是路径连通，而 \(S^0\) 有两个路径分支。因此它不可能同伦等价于任何非空有限复形的悬挂。

---

**S6．不成立。环面与 \(S^1\vee S^1\vee S^2\) 给出反例。**

取有限三角剖分使
\[
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
第二个有限单纯复形可具体构造为：取两个三角形的边界和一个四面体的边界，将它们各自的一个顶点识别，其他顶点保持不同。

二者不同伦等价，因为
\[
\pi_1(|L_1|)\cong\mathbb Z^2,\qquad
\pi_1(|L_2|)\cong F_2;
\]
前者交换，后者不交换。

下面验证它们的悬挂同伦等价。记约化悬挂为 \(\Sigma_r\)。对以顶点为基点的非空有限复形 \(Z\)，非约化悬挂中经过该基点、连接两个悬挂点的弧是可缩子复形。将它压成一点得到 \(\Sigma_r Z\)，所以由 S1，
\[
\Sigma Z\simeq\Sigma_r Z.
\]
又因约化悬挂保持有限楔和，
\[
\Sigma_r(S^1\vee S^1\vee S^2)
\cong S^2\vee S^2\vee S^3.
\]

为验证环面的分裂，令
\[
p_1,p_2:T^2\to S^1
\]
为两个投影，令
\[
q:T^2\longrightarrow T^2/(S^1\vee S^1)\cong S^2
\]
压缩标准 CW 结构的一维骨架。把悬挂坐标分成三段并压缩分界面，得到悬挂的标准挤压映射
\[
\Delta:\Sigma_rT^2\longrightarrow
\Sigma_rT^2\vee\Sigma_rT^2\vee\Sigma_rT^2.
\]
定义
\[
F=(\Sigma_rp_1\vee\Sigma_rp_2\vee\Sigma_rq)\circ\Delta:
\Sigma_rT^2\longrightarrow S^2\vee S^2\vee S^3.
\]
由悬挂同调同构：

- 在二阶同调上，\(F_*\) 对应
  \[
  (p_{1*},p_{2*}):H_1(T^2;\mathbb Z)\xrightarrow{\cong}\mathbb Z^2.
  \]
- 在三阶同调上，\(F_*\) 对应
  \[
  q_*:H_2(T^2;\mathbb Z)\xrightarrow{\cong}H_2(S^2;\mathbb Z).
  \]
  这个同构也可直接由胞腔链复形看出：商映射保留唯一的二维胞腔。
- 其余约化同调群均为零。

因此 \(F\) 是整数同调等价。源与靶都是单连通 CW 复形，满足同调版 Whitehead 定理的适用条件，故 \(F\) 是同伦等价。于是
\[
\boxed{
\Sigma|L_1|
\simeq S^2\vee S^2\vee S^3
\simeq\Sigma|L_2|,
\qquad |L_1|\not\simeq|L_2|.
}
\]