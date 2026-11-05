以下对有限支撑向量 \(v\) 和赋值 \(x\) 记
\[
\langle v,x\rangle=\sum_i v(i)x_i,
\]
其中求和总是有限的。

## S1 有限系统的坐标纤维

记
\[
n=|I|,\qquad r=\dim W,\qquad s=\dim(W+U_A).
\]
取一个已知存在的解 \(x^0\)。令
\[
W^\perp=\{z\in k^I:\langle w,z\rangle=0\ \text{对所有 }w\in W\}.
\]
则
\[
\mathcal S=x^0+W^\perp,\qquad \dim_{\rm aff}\mathcal S=n-r.
\]

对于给定的 \(y\in k^A\)，它可延拓为全解的充要条件是：
\[
\boxed{\quad
\sum_{j\in J}c_j a_j\in U_A
\ \Longrightarrow\
\sum_{j\in J}c_jb_j
=
\sum_{i\in A}\left(\sum_{j\in J}c_ja_j(i)\right)y_i
\quad\text{对所有 }(c_j)\in k^J.
\quad} \tag{1}
\]
若 \(y\) 可延拓，取任一延拓 \(x^y\)，则纤维为
\[
\pi_A^{-1}(y)=x^y+(W+U_A)^\perp,
\qquad
\boxed{\dim_{\rm aff}\pi_A^{-1}(y)=n-s.}
\]
此外，像是维数为
\[
\boxed{\dim_{\rm aff}\pi_A(\mathcal S)=s-r}
\]
的仿射子空间。

**证明。** 解的差恰好属于 \(W^\perp\)，而有限维空间中
\(\dim W^\perp=n-r\)，得到解集公式。

条件 (1) 的必要性来自对全解 \(x\) 将各行乘以 \(c_j\) 后相加。为证充分性，条件 (1) 表示：对每个 \(w\in W\cap U_A\)，
\[
\langle w,x^0\rangle=\langle w,y\rangle.
\]
因此
\[
g(w+u)=\langle w,x^0\rangle+\langle u,y\rangle
\qquad(w\in W,\ u\in U_A)
\]
在 \(W+U_A\) 上良定义。将 \(g\) 以基扩张延拓到 \(k^I\) 上的线性泛函，再令 \(x_i=g(e_i)\)，便得到坐标为 \(y\) 的全解。

固定坐标后的齐次条件是同时湮灭 \(W\) 和 \(U_A\)，即属于 \((W+U_A)^\perp\)，故纤维维数为 \(n-s\)。限制映射在 \(W^\perp\) 上的核正是 \((W+U_A)^\perp\)，由秩—零度定理，像的维数为
\[
(n-r)-(n-s)=s-r.
\]

## S2 有限域下的精确计数

沿用 S1 的 \(n,r,s\)，若 \(|k|=q\)，则
\[
\boxed{
|\mathcal S|=q^{n-r},\qquad
|\pi_A(\mathcal S)|=q^{s-r},\qquad
|\pi_A^{-1}(y)|=q^{n-s}\quad(y\in\pi_A(\mathcal S)).
}
\]
这是因为有限域上维数为 \(d\) 的非空仿射空间有 \(q^d\) 个点。上述公式只使用了指定的量。

## S3 有限域的无限坐标拓扑

对每行定义
\[
C_j=\{x\in k^I:\langle a_j,x\rangle=b_j\}.
\]
每个 \(a_j\) 有限支撑，所以 \(C_j\) 是乘积拓扑中的闭集，实际上也是开集。

有限离散空间 \(k\) 紧且 Hausdorff。由 Tychonoff 定理，\(k^I\) 紧 Hausdorff。有限子系统可解说明闭集族 \((C_j)_{j\in J}\) 具有有限交性质，故
\[
\mathcal S=\bigcap_{j\in J}C_j
\]
非空；它又是紧空间的闭子集，因而紧。

若 \(x,x'\in\mathcal S\) 不同，存在坐标 \(i\) 使 \(x_i\ne x'_i\)。集合
\[
\{z\in\mathcal S:z_i=x_i\}
\]
在 \(\mathcal S\) 中既开又闭，包含 \(x\) 而不包含 \(x'\)。因此 \(\mathcal S\) 的任何含两个不同点的子集都不连通，故 \(\mathcal S\) 全不连通。

对任意 \(A\subseteq I\)，\(\pi_A\) 连续，故 \(\pi_A(\mathcal S)\) 紧；\(k^A\) Hausdorff，所以此像闭。

具体地，对 \(y\in k^A\)，
\[
\boxed{
y\in\pi_A(\mathcal S)
\iff
\begin{array}{l}
\text{对每个有限 }F\subseteq J\text{ 和有限 }B\subseteq A，\\
\text{存在 }x\in k^I\text{ 同时满足 }
\langle a_j,x\rangle=b_j\ (j\in F),\quad x|_B=y|_B.
\end{array}}
\tag{2}
\]
必要性显然。反之，右侧恰表示闭集族
\[
\{C_j:j\in J\}\cup\{\{x:x_i=y_i\}:i\in A\}
\]
具有有限交性质；由 \(k^I\) 的紧性，其总交非空，即得到所需延拓。

## S4 整体对象与全部恢复目标

**结论：所有目标成立。** 下述数据、分类和构造对任意域及任意指标集合都适用。

### 1. 由原系统确定的代数数据与整体解

令
\[
V=k^{(I)},\qquad W=\operatorname{span}\{a_j:j\in J\}.
\]
有限可解性给出良定义的线性泛函
\[
\ell:W\longrightarrow k,\qquad
\ell\!\left(\sum_{j\in F}c_ja_j\right)=\sum_{j\in F}c_jb_j,
\quad F\subseteq J\text{ 有限}. \tag{3}
\]
确实，若一个有限行组合为零，取该有限子系统的解，将方程作同样的线性组合，就知右侧也为零。

赋值空间与代数对偶自然同构：
\[
k^I\cong V^*=\operatorname{Hom}_k(V,k),\qquad
x\longleftrightarrow[v\mapsto\langle v,x\rangle].
\]
反过来，泛函 \(\varphi\in V^*\) 对应 \(x_i=\varphi(e_i)\)；这可行是因为 \(V\) 的每个向量都是有限个 \(e_i\) 的线性组合。

在 ZFC 中可取 \(W\) 的 Hamel 基并将其扩为 \(V\) 的基。令新加入基向量上的值为零，即将 \(\ell\) 延拓为 \(\varphi_0\in V^*\)。于是
\[
x_i^0=\varphi_0(e_i)
\]
构造出整体解。全部解恰为
\[
\boxed{
\mathcal S
=\{x\in k^I:\langle w,x\rangle=\ell(w)\ \forall w\in W\}
=x^0+W^\perp.}
\tag{4}
\]
这里 \(W^\perp\subseteq V^*\cong k^I\)，且自然同构于 \((V/W)^*\)。

### 2. 按方程系的结果分类

相容系统的解集由且仅由代数对 \((W,\ell)\) 决定。更精确地，若两个相容系统有相同解集，则它们的 \(W\) 和 \(\ell\) 均相同。

证明：在解集上取 \(x^0\)。若 \(v\in W\)，则 \(\langle v,x\rangle=\ell(v)\) 对所有解恒定。若 \(v\notin W\)，可用基扩张构造 \(h\in V^*\)，使 \(h|_W=0\) 而 \(h(v)=1\)。于是 \(x^0+h\) 仍是解，但其 \(v\)-取值不同。所以
\[
W=\{v\in V:\langle v,x\rangle\text{ 在 }\mathcal S\text{ 上恒定}\},
\]
而 \(\ell(v)\) 就是该恒定值。

反之，任意子空间 \(W\le V\) 和任意 \(\ell\in W^*\) 都可由有限支撑行实现：取 \(W\) 的一个基作为行，常数取对应的 \(\ell\)-值；上面的基扩张构造给出解。若行指标集合 \(J\) 预先固定，则恰好要求
\[
\dim W\le |J|.
\]
必要性来自 \(W\) 由 \(|J|\) 个行生成；充分性是把一个基注入 \(J\)，其余行及常数取零。

### 3. 所有坐标像及纤维

固定 \(A\subseteq I\)，令
\[
U_A=k^{(A)}\subseteq V,\qquad W_A=W\cap U_A,\qquad T_A=W+U_A.
\]
则
\[
\boxed{
\pi_A(\mathcal S)
=
\{y\in k^A:\langle w,y\rangle=\ell(w)\ \text{对所有 }w\in W_A\}.
}
\tag{5}
\]
这里每个 \(w\in W_A\) 有限支撑，故左侧求和有限。于是像由 \((W_A,\ell|_{W_A})\) 完全确定；应用上一节的同一分离论证可知，这对数据也由像唯一确定。

证明 (5)：必要性显然。若 \(y\) 满足右侧，在 \(T_A\) 上定义
\[
g_y(w+u)=\ell(w)+\langle u,y\rangle
\qquad(w\in W,\ u\in U_A). \tag{6}
\]
两个分解之差属于 \(W_A\)，故 (5) 保证 \(g_y\) 良定义。将 \(g_y\) 以基扩张延拓到 \(V\)，便构造出一个坐标为 \(y\) 的全解。

若 \(y\) 不满足 (5)，纤维为空。若满足，取上述任一延拓对应的 \(x^y\)，则
\[
\boxed{
\pi_A^{-1}(y)=x^y+T_A^\perp,
\qquad T_A^\perp\cong (V/T_A)^*.
}
\tag{7}
\]
更具体地，非空纤维与满足 \(g|_W=\ell\) 的 \(g\in T_A^*\) 一一对应：从 \(y\) 得到 (6) 中的 \(g_y\)；反之令 \(y_i=g(e_i)\) 即可。该纤维正是 \(g\) 到 \(V\) 的所有线性延拓。

### 4. 显式参数化、维数与基数

选取补空间
\[
U_A=W_A\oplus C,\qquad V=(W\oplus C)\oplus D.
\]
第一式给出 \(W+U_A=W\oplus C\)，第二式由基扩张得到。对任意
\[
t\in C^*,\qquad h\in D^*,
\]
定义
\[
\varphi_{t,h}(w+c+d)=\ell(w)+t(c)+h(d).
\]
令 \(x_i=\varphi_{t,h}(e_i)\)，就得到全解；每个全解恰由一对 \((t,h)\) 得到。其 \(A\)-坐标只由 \(t\) 决定，不同 \(t\) 给出不同 \(A\)-坐标；固定 \(t\) 后，整个纤维由任意 \(h\in D^*\) 参数化。泛函 \(t,h\) 可分别通过在所选基上任意赋值来构造。

因此，仿射方向空间分别为
\[
\operatorname{dir}\mathcal S\cong(V/W)^*,\qquad
\operatorname{dir}\pi_A(\mathcal S)\cong(U_A/W_A)^*,\qquad
\operatorname{dir}\pi_A^{-1}(y)\cong(V/T_A)^*.
\tag{8}
\]
这些同构也给出相应的任意基数仿射维数。

若记
\[
\alpha=\dim(V/W),\quad
\beta=\dim(U_A/W_A),\quad
\gamma=\dim(V/T_A),
\]
其中维数允许是无限基数，则由对偶空间在一组基上的任意赋值，
\[
\boxed{
|\mathcal S|=|k|^\alpha,\qquad
|\pi_A(\mathcal S)|=|k|^\beta,\qquad
|\pi_A^{-1}(y)|=|k|^\gamma
\quad(y\in\pi_A(\mathcal S)).
}
\tag{9}
\]
这些是基数幂；无限维时不把商空间维数误当作其对偶空间的代数维数。

### 5. 恢复与唯一性判据

对可实现的 \(y\) 和任意有限支撑线性观测 \(v\in V\)，其在纤维上恒定的充要条件是
\[
v\in T_A=W+U_A.
\]
若 \(v=w+u\in W+U_A\)，其值为
\[
\langle v,x\rangle=\ell(w)+\langle u,y\rangle.
\tag{10}
\]
若 \(v\notin T_A\)，则对任意 \(c\in k\)，可先在 \(T_A\oplus kv\) 上令 \(g_y(v)=c\)，再延拓到 \(V\)；因此该观测在纤维上可取遍 \(k\)。

特别地，以下判据全部成立：
\[
\begin{array}{c|c}
\text{性质}&\text{充要条件}\\ \hline
\pi_A\text{ 满射到 }k^A&W\cap U_A=\{0\}\\
\pi_A\text{ 单射}&W+U_A=V\\
\pi_A\text{ 为常映射}&U_A\subseteq W\\
\mathcal S\text{ 恰有一个元素}&W=V
\end{array}
\]
其中，满射判据来自 (5) 和有限支撑向量与 \(k^A\) 的配对可分离非零向量；其余判据来自 (7)–(8) 及基扩张。故 \(\pi_A\) 双射当且仅当
\[
V=W\oplus U_A.
\]

单个坐标 \(i\) 在给定 \(y\) 后可唯一恢复，当且仅当 \(e_i\in W+U_A\)；此时将 \(e_i=w+u\) 代入 (10)，就得到只涉及有限个 \(A\)-坐标的恢复公式。否则该坐标在纤维上可取遍 \(k\)。不预先给定坐标时，坐标 \(i\) 被整个系统强制当且仅当 \(e_i\in W\)，其值为 \(\ell(e_i)\)。

## S5 赋值空间的支持

结论不成立。对每个 \(n\in\mathbb N\)，取
\[
a_n=e_n,\qquad b_n=1.
\]
即方程为 \(x_n=1\)。

每个有限子系统都有有限支撑解：在涉及的有限个坐标取 \(1\)，其余取 \(0\)。但全系统唯一的全赋值解是 \(x_n=1\) 对所有 \(n\) 成立，它具有无限支撑，因此不属于 \(k^{(\mathbb N)}\)。

## S6 无限域的坐标像

**仍然闭**，即使 \(k\) 无限。由 S4，像由下列只涉及有限坐标的方程完整描述：
\[
\boxed{
\sum_{i\in A}\left(\sum_{j\in F}c_ja_j(i)\right)y_i
=
\sum_{j\in F}c_jb_j
}
\tag{11}
\]
其中遍历所有有限 \(F\subseteq J\) 及 \(c_j\in k\)，并要求
\[
\operatorname{supp}\left(\sum_{j\in F}c_ja_j\right)\subseteq A.
\]
每个这样的行组合仍有限支撑，所以 (11) 只涉及有限个 \(y_i\)。离散域的乘积拓扑中，每个方程的解集都是闭集，故它们的交 \(\pi_A(\mathcal S)\) 闭。这里用的是 S4 的线性泛函延拓，而不是无限离散域的乘积紧性。

此外，S3 的有限测试 (2) 对任意域仍等价于可延拓性：若有限测试成立，对 (11) 所对应的有限行集 \(F\) 和有限坐标集
\[
B=\operatorname{supp}\left(\sum_{j\in F}c_ja_j\right)
\]
应用测试，即得 (11)；反向则由整体延拓显然成立。

作为集合分类的补充，允许任意行指标集合时，有限支撑线性方程系的非空解集**恰是** \(k^I\) 中的非空闭仿射子空间。正向由各行方程闭得到。反向，设闭仿射子空间为 \(x^0+L\)，其中 \(L\) 是闭线性子空间。若 \(z\notin L\)，由乘积拓扑存在有限 \(F\subseteq I\)，使 \(z|_F\notin\pi_F(L)\)。有限维线性代数给出 \(k^F\) 上一个线性泛函，在 \(\pi_F(L)\) 上为零而在 \(z|_F\) 上非零；把它扩成 \(I\) 上有限支撑的行，即得到一个排除 \(z\) 而在 \(L\) 上为零的方程。所有这些方程的交恰为 \(L\)，平移常数后得到 \(x^0+L\)。