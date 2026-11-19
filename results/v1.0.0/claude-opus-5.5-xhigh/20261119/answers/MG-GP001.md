# 局部单形、锥附着与整体同伦型：S1–S6 解答

**主要结论：**
- S4 所列目标全部成立，并且有 $X\simeq\Sigma|\mathrm{lk}_K(v)|$，其中 $\mathrm{lk}_K(v)\neq\varnothing$。
- $X$ 的可能同伦型恰好是"非空有限复形的非约化悬挂"。
- $X$ 可缩当且仅当 $\mathrm{lk}_K(v)$ 整系数无环。这个条件可以用含 $v$ 的单形之间的关联矩阵，通过 Smith 标准形来检验。
- 关于 $B$ 的条件，在其余假设下只起一个作用：排除 $v$ 是孤立点。若去掉 $B$（S5），只新增一种类型 $S^0$。
- 由悬挂的同伦型不能反推出原复形的同伦型（S6 的答案是否定的）。

---

## 0. 约定与引用的标准定理

**记号。**
- 有限单纯复形的实现和有限 CW 复形都是紧 Hausdorff 空间。
- $CP=P\times[0,1]/P\times\{1\}$，底为 $P\times\{0\}$。
- 对 $P\neq\varnothing$，非约化悬挂 $\Sigma P=P\times[0,1]/(P\times\{0\},\ P\times\{1\}$ 各自塌缩为一点$)$；约定 $\Sigma\varnothing=S^0$。
- 对顶点 $v$，记
  - 闭星形 $\mathrm{st}(v)=\{\sigma:\sigma\cup\{v\}\in K\}$，
  - 链环 $\mathrm{lk}(v)=\{\sigma\in K:v\notin\sigma,\ \sigma\cup\{v\}\in K\}$，
  - 删除 $\mathrm{dl}(v)=\{\sigma\in K: v\notin\sigma\}$。
- 于是 $K=\mathrm{dl}(v)\cup\mathrm{st}(v)$，$\mathrm{dl}(v)\cap\mathrm{st}(v)=\mathrm{lk}(v)$，且 $\mathrm{st}(v)=v*\mathrm{lk}(v)$。

**引用的标准定理及适用条件。**
- **(T1) HEP。** 若 $(P,Q)$ 是 CW 对，则 $P\times I$ 形变收缩到 $P\times\{0\}\cup Q\times I$（Hatcher 0.16）。
- **(T2) Whitehead + Hurewicz。** 单连通 CW 复形之间诱导整同调同构的映射是同伦等价。特别地，单连通且约化整同调为零的 CW 复形可缩。
- **(T3)** 每个有限 CW 复形同伦等价于一个有限单纯复形（Hatcher 2C.5）。
- **(T4)** 从紧空间到 Hausdorff 空间的连续满射是闭映射，因而是商映射；连续双射是同胚。

---

## S1 可缩子复形的商

**命题。** $Y$ 是有限 CW 复形，$\varnothing\neq A\subset Y$ 是可缩子复形，则 $q:Y\to Y/A$ 是同伦等价。

**证明。**
1. **取收缩同伦。** 由于 $A$ 可缩，有 $h:A\times I\to A$，$h_0=\mathrm{id}_A$，$h_1\equiv a_0$。
2. **用 HEP 扩张（T1，适用于 CW 对 $(Y,A)$）。**
   - 在 $Y\times\{0\}$ 上令 $(y,0)\mapsto y$，在 $A\times I$ 上令 $(a,t)\mapsto h_t(a)$。两者是闭集，在 $A\times\{0\}$ 上一致。
   - 把它扩张为 $f:Y\times I\to Y$。于是 $f_0=\mathrm{id}_Y$，$f_t(A)=h_t(A)\subset A$，$f_1(A)=\{a_0\}$。
3. **同伦为何能下降到商。**
   - $q$ 的纤维是 $A$ 和单点 $\{y\}$（$y\notin A$）。因为 $f_t(A)\subset A$，所以 $q f_t$ 在每个纤维上取常值。
   - 因此存在唯一的 $\bar f_t$ 使 $\bar f_t q=q f_t$，即 $\bar f\circ(q\times\mathrm{id}_I)=q\circ f$。
   - $q\times\mathrm{id}_I$ 是商映射：$Y\times I$ 紧，$Y/A\times I$ Hausdorff（$Y/A$ 是 CW 复形，$A$ 塌成一个 0-胞腔），由 T4 得出。所以 $\bar f$ 连续，是从 $\bar f_0=\mathrm{id}$ 到 $\bar f_1$ 的同伦。
   - 关键有两点：
     - 同伦在每个时刻都把 $A$ 映入 $A$。这是 HEP 带来的；任意给一个同伦一般不满足。
     - 对 $I$ 取积后，商映射仍是商映射。
4. **构造同伦逆。**
   - $f_1$ 在 $A$ 上取常值，由泛性质得到连续的 $g:Y/A\to Y$，满足 $gq=f_1$。
   - 于是 $gq=f_1\simeq f_0=\mathrm{id}_Y$。
   - 又 $qgq=qf_1=\bar f_1q$，而 $q$ 是满射，所以 $qg=\bar f_1\simeq\mathrm{id}_{Y/A}$。

因此 $q$ 是同伦等价。 ∎

---

## S2 非可缩底空间上的锥附着

**引理 2.1（附着映射的同伦不变性，Hatcher 0.18）。**
设 $(P,Q)$ 是有限 CW 对，$D$ 是紧 Hausdorff 空间，$f_0\simeq f_1:Q\to D$。则
$$D\cup_{f_0}P\simeq D\cup_{f_1}P\quad\text{rel }D.$$

**证明。**
- 设 $F:Q\times I\to D$ 是从 $f_0$ 到 $f_1$ 的同伦，令 $W=D\cup_F(P\times I)$。$W$ 是紧 Hausdorff 空间。
- 由 T1，$P\times I$ 形变收缩到 $P\times\{0\}\cup Q\times I$，并且这个形变在 $Q\times I$ 上保持不动。所以它与粘合相容，并下降到 $W$（理由同 S1 第 3 步，用 T4）。
- 下降后，$W$ 形变收缩到 $D\cup_F(P\times 0\cup Q\times I)=D\cup_{f_0}P$。这里 $Q\times I$ 整体被粘进了 $D$。
- 对称地，$W$ 也形变收缩到 $D\cup_{f_1}P$。两者都同伦等价于 $W$（rel $D$）。 ∎

**定理。** 在题设下，$Y=D\cup_L CL\simeq D\vee\Sigma L$（rel $D$）。

**证明。**
1. 取 $P=CL$，并取单纯锥 $|w*L|$ 作为它的模型，$Q=L$ 是底。这是 CW 对。
2. 取 $f_0=i$ 为包含映射。由 $i$ 零伦，$i\simeq f_1\equiv d_0$。
3. 由引理，$Y\simeq D\cup_{f_1}CL=(D\sqcup CL)/(L\times0\sim d_0)$。
4. 这个空间就是 $D\vee(CL/L)$，而 $CL/L\cong\Sigma L$：底塌缩为一个极点 $s$，锥顶是另一个极点。 ∎

**楔点的选择。**
- **$D$ 侧。** 楔点是零伦的终点 $d_0$。由于 $D$ 道路连通，任意两个常值映射都同伦，所以由引理 2.1，$d_0$ 可以任取，结果都同伦等价（rel $D$）。
- **$\Sigma L$ 侧。** 楔点按构造是对应锥底的极点 $s$。由于 $L\neq\varnothing$，$\Sigma L$ 道路连通。$X\vee_{x=y}Z=Z\cup_g X$，其中 $g:\{x\}\mapsto y$，$(X,\{x\})$ 是 CW 对。沿道路移动 $y$，再用引理，可知把楔点换到 $\Sigma L$ 的任一点都得到同一同伦型。
- **前提的作用。**
  - 若 $D$ 不道路连通，$d_0$ 必须落在零伦所指定的那个分支里。
  - 若 $L=\varnothing$，则 $\Sigma\varnothing=S^0$ 不连通，楔积不再适用。

**推论 2.2。** 若 $D$ 还是可缩的，取 $d_0$ 为顶点，则 $D$ 是 $D\vee\Sigma L$ 的非空可缩子复形。由 S1 得 $Y\simeq\Sigma L$。

---

## S3 整数扭结的实例

**构造。**
- 设 $L$ 是 $\mathbb RP^2$ 的任一有限三角剖分。例如 6 顶点剖分，三角形为：123, 134, 145, 156, 162, 235, 346, 452, 563, 624。我已用计算机验证：每条边恰在 2 个三角形中，并且 $H_1=\mathbb Z/2$，$H_2=0$。
- 令 $K=L*\{v,w\}$（单纯悬挂）。它的单形为 $\sigma,\ \sigma\cup\{v\},\ \sigma\cup\{w\}$，其中 $\sigma\in L$ 或 $\sigma=\varnothing$。
- 令 $B=\overline{\{v,u\}}$，其中 $u$ 是 $L$ 的一个顶点。

**验证。**
- **$O$ 非空可缩。** $\mathrm{dl}(v)=w*L$ 是锥。由 S4 引理 A，$O=|K|\setminus v$ 形变收缩到 $|w*L|$，所以 $O$ 非空且可缩。
- **$B$ 的条件。** $|B|$ 是线段，$|B|\setminus v$ 是半开线段，两者都可缩。可缩空间之间的映射是同伦等价。
- **同调。** $\mathrm{lk}_K(v)=L$，由 S4 得 $|K|\simeq\Sigma\mathbb RP^2$。由悬挂同构，$\tilde H_n(|K|;\mathbb Z)\cong\tilde H_{n-1}(\mathbb RP^2;\mathbb Z)$，所以
  - $\tilde H_2=\mathbb Z/2$，其余为 $0$（计算机复核 $K$：$H_2=\mathbb Z/2$）。
- **有理同调全零。** $\mathbb Q$ 是平坦模，所以 $\tilde H_*(\,\cdot\,;\mathbb Q)=\tilde H_*(\,\cdot\,;\mathbb Z)\otimes\mathbb Q=0$。
- **不可缩。** $H_2(|K|;\mathbb Z)\neq0$，所以 $|K|$ 不可缩。（$|K|$ 单连通，由 Hurewicz 还有 $\pi_2=\mathbb Z/2$。）

这个例子说明：可缩性判据必须用整系数，不能用有理系数。

---

## S4 整体对象与全部恢复目标

**判定：全部目标成立。**

### 引理 A（径向形变收缩）

$O$ 强形变收缩到 $D:=|\mathrm{dl}(v)|$。

**证明。** 对 $x\in O$（即重心坐标 $x_v<1$），定义 $r_t(x)$ 如下：
- 把 $x_v$ 换成 $(1-t)x_v$；
- 把其余坐标乘以 $\dfrac{1-(1-t)x_v}{1-x_v}$。

验证：
- 支撑集不变大，所以 $r_t(x)$ 留在 $x$ 所在的闭单形中。
- $r_0=\mathrm{id}$，$r_1(x)$ 的 $v$ 坐标为 $0$，所以 $r_1(O)\subset D$。$D$ 上的点在整个过程中不动。
- 在每个"闭单形去掉 $v$"上公式连续。这些集合构成 $O$ 的有限闭覆盖，由粘接引理，$r$ 在 $O$ 上连续。 ∎

因此 $O$ 非空可缩 ⟺ $D$ 非空可缩。

### 引理 B（商就是悬挂）

设 $L:=|\mathrm{lk}(v)|\neq\varnothing$，$S:=|\mathrm{st}(v)|$。则 $X/D\cong\Sigma L$。

**证明。**
- $(y,t)\mapsto(1-t)y+tv$ 诱导 $CL\cong S$：它是从紧空间到 Hausdorff 空间的连续双射（T4）。
- $X=D\cup S$，$D\cap S=L$，且 $X\setminus D=S\setminus L$。
- 因此 $S/L\to X/D$ 是连续双射，由 T4 是同胚。
- 而 $S/L\cong CL/L\cong\Sigma L$。 ∎

### 命题 C

若 $O$ 非空可缩且 $\mathrm{lk}(v)\neq\varnothing$，则 $X\simeq\Sigma|\mathrm{lk}(v)|$。

**证明。** $D$ 是有限 CW 复形 $X$ 的非空可缩子复形（引理 A），满足 S1 的条件。所以 $X\simeq X/D\cong\Sigma|\mathrm{lk}(v)|$（引理 B）。

另一种证法：$X=D\cup_L CL$，其中 $D$ 可缩（因而道路连通），包含映射 $L\to D$ 零伦，满足 S2 的条件。由推论 2.2 得同一结论。 ∎

### 引理 D（$B$ 条件的实际内容）

1. 题设条件蕴含 $\mathrm{lk}_K(v)\neq\varnothing$。
2. 反之，若 $\mathrm{lk}_K(v)\neq\varnothing$，取 $B=\overline{\{v,u\}}$ 即可满足条件。

**证明。**
1. 若 $\mathrm{lk}_K(v)=\varnothing$，则 $\mathrm{lk}_B(v)=\varnothing$。于是 $C=|\mathrm{dl}_B(v)|\sqcup\{v\}$，两部分都是闭集，所以 $\{v\}$ 是 $C$ 的一个道路分支。包含映射 $C\setminus v\to C$ 在 $\pi_0$ 上不满射，因而不是同伦等价，与假设矛盾。
2. 这是 S3 中线段的论证：$|B|$ 与 $|B|\setminus v$ 都可缩。 ∎

所以，在其余假设下，$B$ 条件只起"排除 $v$ 孤立"的作用，不提供关于 $X$ 的其他信息。

### 刻画定理

满足条件的三元组中，$X$ 的同伦类型恰好是
$$\{\Sigma|L|:L \text{ 是非空有限单纯复形}\}=\{\Sigma P: P\text{ 是非空有限 CW 复形}\},$$
并且具体地 $X\simeq\Sigma|\mathrm{lk}_K(v)|$。

**证明。**
- **"⊂"：** 由引理 D 的第 1 条和命题 C。
- **两个集合相等：** 由 T3，$P\simeq|L|$；悬挂保持同伦，所以 $\Sigma P\simeq\Sigma|L|$。
- **实现构造：** 对任意非空 $L$，令 $K=L*\{v,w\}$，$B=\overline{\{v,u\}}$（$u\in L$ 是顶点）。
  - $\mathrm{lk}_K(v)=L$；
  - $\mathrm{dl}(v)=w*L$ 可缩，所以 $O$ 非空可缩；
  - $B$ 满足条件（引理 D 第 2 条）；
  - $X\cong\Sigma|L|$。 ∎

**附注（推论）。**
- $X$ 道路连通，且 $\tilde H_n(X)\cong\tilde H_{n-1}(\mathrm{lk}\,v)$。
- 若 $\mathrm{lk}(v)$ 的连通分支为 $L_0,\dots,L_m$，则 $X\simeq\bigvee_i\Sigma L_i\vee\bigvee^m S^1$，所以 $\pi_1(X)$ 是秩 $m$ 的自由群。证法：$\Sigma L_i$ 沿两极粘到 $\Sigma L_0$ 上；对这两点的附着映射反复用引理 2.1，把它同伦到常值映射。
- 例如 $\mathrm{lk}(v)=S^0$ 时 $X\simeq S^1$（$K$ 取三角形的边界）。可见 $X$ 一般不可缩。

### 可缩判据（只用含 $v$ 的单形及其面关系）

**数据。**
- 把 $v$ 排为最小顶点。令 $S_k$ 为含 $v$ 的 $k$-单形的集合，$S_0=\{v\}$。
- 定义
$$D_k[v,a_1,\dots,a_k]=\sum_{i=1}^k(-1)^i[v,a_1,..,\hat a_i,..,a_k].$$
- 所需信息只有：含 $v$ 的单形、它们之间余维 1 的包含关系、由顶点顺序决定的符号。

**判据。** $X$ 可缩 ⟺ 有限自由链复形 $(\mathbb Z[S_*],D_*)$ 正合。具体检验办法：对每个 $k$，
- $\operatorname{rank}D_k+\operatorname{rank}D_{k+1}=|S_k|$，并且
- 每个 $D_k$ 的 Smith 标准形中，非零不变因子全为 $\pm1$。

这两条合起来等价于 $\tilde H_*(\mathrm{lk}_K(v);\mathbb Z)=0$。

**证明。**
1. **与链环同调的关系。**
   - $(\mathbb Z[S_*],D)=C_*(K)/C_*(\mathrm{dl}\,v)$，即相对链复形。
   - 映射 $[v,a_1..a_k]\mapsto[a_1..a_k]$（其中 $[v]\mapsto[\varnothing]$）把 $D_k$ 变成 $-\tilde\partial_{k-1}$，即 $\mathrm{lk}(v)$ 的增广边缘的负号。
   - 所以 $H_k\cong\tilde H_{k-1}(\mathrm{lk}\,v)\cong H_k(X,D)\cong\tilde H_k(X)$。最后一步用到 $D$ 非空可缩和长正合列。
2. **正合性的矩阵刻画。**
   - 由 Smith 标准形，$\operatorname{tors}H_{k-1}=\operatorname{tors}\operatorname{coker}D_k=\bigoplus\mathbb Z/d_i$。
   - 理由：若 $mx\in\operatorname{im}D_k$，则 $mD_{k-1}x=0$；由于模是自由的，$D_{k-1}x=0$。
   - 因此"秩条件 + 不变因子全为 $\pm1$"等价于各阶同调为零。
3. **(⇒)** $X$ 可缩，则 $\tilde H_*(X)=0$，由第 1 步链复形正合。
4. **(⇐)**
   - 在 $k=0$ 处正合，说明 $D_1$ 满射，所以 $\mathrm{lk}\neq\varnothing$。
   - 在 $k=1$ 处正合，说明 $\tilde H_0(\mathrm{lk})=0$，即 $\mathrm{lk}$ 连通。
   - 于是 $\Sigma|\mathrm{lk}|$ 单连通：用 van Kampen，取两个开锥（可缩），交集 $\simeq|\mathrm{lk}|$ 道路连通。
   - 又 $\tilde H_*(X)=0$，由 T2，$X\simeq\Sigma|\mathrm{lk}|$ 可缩。 ∎

**两点说明。**
- 有理系数版本的判据是错的：S3 中有理同调全零但 $X$ 不可缩。
- "链环可缩"只是充分条件，不是必要条件（见 S6 例 2）。

---

## S5 不提供子复形 B

**结论：不必。** 恰好新增一种同伦型 $S^0$（若约定 $\Sigma\varnothing=S^0$，则它就是 $\Sigma\varnothing$）。

**证明。**
- 若 $\mathrm{lk}(v)\neq\varnothing$，命题 C 的证明没有用到 $B$，所以 $X\simeq\Sigma|\mathrm{lk}\,v|$。
- 若 $\mathrm{lk}(v)=\varnothing$，则 $X=O\sqcup\{v\}$，且 $O$ 可缩，所以 $X\simeq S^0$。
- $S^0$ 不道路连通，而非空复形的悬挂都道路连通，所以 $S^0$ 不在 S4 的类型里。
- 实现：$K=\{\varnothing,\{v\},\{w\}\}$。

**分类：** $\{\Sigma P: P\text{ 是非空有限 CW 复形}\}\sqcup\{S^0\}$。

S4 的判据在这里自动适用：$v$ 孤立时 $S_1=\varnothing$，链复形在 $k=0$ 处不正合，判据正确给出"不可缩"。

---

## S6 悬挂信息的逆向恢复

**结论：不能。** $\Sigma|L_1|\simeq\Sigma|L_2|$ 不蕴含 $|L_1|\simeq|L_2|$。

### 例 1：$L_1=T^2$，$L_2=S^1\vee S^1\vee S^2$

两者都取三角剖分，例如 7 顶点环面，以及两个三角形边界与一个四面体边界在一个顶点处粘合。

1. **非约化悬挂与约化悬挂。** 对连通 CW 复形 $P$ 和 0-胞腔 $p$，$\{p\}\times I$ 是可缩子复形。由 S1，非约化悬挂 $\Sigma P\simeq$ 约化悬挂 $SP$。
2. **$L_2$ 的悬挂。** 约化悬挂与楔积交换，所以 $S L_2\cong S^2\vee S^2\vee S^3$。
3. **构造 $\varphi$。** 设 $p_1,p_2:T\to S^1$ 是两个投影，$q:T\to T/(S^1\vee S^1)\cong S^2$。用余 H 结构的捏合映射 $\nu$ 定义
$$\varphi=(Sp_1\vee Sp_2\vee Sq)\circ\nu:\ ST\to S^2\vee S^2\vee S^3.$$
   在约化同调上，$\nu_*x=(x,x,x)$，所以 $\varphi_*=(Sp_1)_*+(Sp_2)_*+(Sq)_*$。
4. **$\varphi_*$ 是同构。** 利用悬挂同构的自然性：
   - 2 维：$H_1(T)=\mathbb Z a\oplus\mathbb Z b$，其中 $a\mapsto(1,0,0)$，$b\mapsto(0,1,0)$；$q$ 在 $H_1$ 上为零。所以是同构。
   - 3 维：$p_i$ 经过 $S^1$ 分解，在 $H_2$ 上为零；而 $q_*:H_2(T)\to H_2(S^2)$ 是同构（2-胞腔以度 1 映到 2-胞腔）。所以是同构。
5. **结论。** 两边都单连通，由 T2，$\varphi$ 是同伦等价，即 $\Sigma L_1\simeq\Sigma L_2$。
6. **$L_1\not\simeq L_2$。** $\pi_1(T^2)=\mathbb Z^2$ 是交换群，而 $\pi_1(S^1\vee S^1\vee S^2)=\mathbb Z*\mathbb Z$ 不交换。

### 例 2：无环但不可缩的复形，对比单点（呼应 S4 判据）

- **复形。** 取群表示 $\langle s,t\mid s^3t^{-5},\ s^3(st)^{-2}\rangle$ 的表示复形，并由 T3 换成同伦等价的有限单纯复形 $L_1$。
- **无环。** 指数和矩阵为 $\begin{pmatrix}3&1\\-5&-2\end{pmatrix}$，行列式为 $-1$。所以胞腔 $\partial_2$ 是同构，$H_1=H_2=0$，$L_1$ 整系数无环。
- **不可缩。** 令 $s\mapsto(3\,4\,5)$，$t\mapsto(1\,3\,5\,2\,4)$。则 $st=(1\,3)(2\,4)$，并且 $s^3=t^5=(st)^2=1$（我已用计算机验证）。这给出 $\pi_1(L_1)$ 到 $A_5$ 的非平凡同态，所以 $\pi_1(L_1)\neq1$，$L_1$ 不可缩。
- **悬挂相同。** 由 S4 判据的证明，非空 $\mathbb Z$-无环复形的悬挂可缩，所以 $\Sigma L_1\simeq\mathrm{pt}\simeq\Sigma(\mathrm{pt})$。
- **对 S4 的含义。** 取 $K=L_1*\{v,w\}$，则 $X$ 可缩，但 $\mathrm{lk}(v)=L_1$ 不可缩。

### 悬挂能保留的信息

$\tilde H_*(L)$（平移一维后）和 $L$ 的连通分支数（等于 $\pi_1(\Sigma L)$ 的自由秩加 1）仍由 $\Sigma L$ 决定。因此在 S4 中，$X$ 只决定 $\mathrm{lk}(v)$ 的这些不变量，不决定它的同伦型。