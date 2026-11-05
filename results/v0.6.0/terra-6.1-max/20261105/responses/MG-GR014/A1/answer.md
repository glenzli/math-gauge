## S1 有限系统的坐标纤维

记
\[
n=|I|,\qquad w=\dim W,\qquad r=\dim(W+U_A).
\]
由相容性选一个解 \(x^0\)。在 \(W\) 上定义线性泛函
\[
\lambda(v)=v\cdot x^0.
\]
它满足 \(\lambda(a_j)=b_j\)，且与所选解无关。

解集为
\[
\mathcal S=x^0+W^\perp,\qquad
W^\perp=\{z\in k^I:v\cdot z=0\ \text{对所有 }v\in W\}.
\]
由于有限维标准配对非退化，
\[
\boxed{\dim\mathcal S=n-w.}
\]

对给定的 \(y\in k^A\)，令 \(\widehat y\in U_A^*\) 由
\[
\widehat y(u)=\sum_{i\in A}u(i)y_i
\]
定义。则 \(y\) 可延拓为系统的解，当且仅当
\[
\boxed{\widehat y(v)=\lambda(v)\quad(v\in W\cap U_A).}\tag{1}
\]

证明：若 \(y=x|_A\) 且 \(x\in\mathcal S\)，条件显然成立。反之，在 (1) 下，
\[
W+U_A\longrightarrow k,\qquad w_0+u\longmapsto \lambda(w_0)+\widehat y(u)
\]
是良定义的线性泛函。将它延拓到 \(k^I\) 的线性泛函；由标准配对，该延拓对应一个 \(x\in k^I\)，它满足原方程和 \(x|_A=y\)。

直接用给定行表示，(1) 等价于：对每一组 \(t_j\in k\)，只要
\[
c=\sum_{j\in J}t_ja_j\in U_A,
\]
就有
\[
\sum_{j\in J}t_jb_j=\sum_{i\in A}c(i)y_i.
\]

若纤维非空，取其中一点 \(x^y\)，则
\[
\pi_A^{-1}(y)=x^y+(W+U_A)^\perp.
\]
因此每个非空纤维的仿射维数为
\[
\boxed{n-r.}
\]
由秩—零度定理，坐标像的仿射维数为
\[
\boxed{\dim\pi_A(\mathcal S)=(n-w)-(n-r)=r-w.}
\]

## S2 有限域下的精确计数

沿用 S1 的记号，若 \(|k|=q\)，则有限维仿射空间的点数等于 \(q\) 的维数次幂。所以
\[
\boxed{|\mathcal S|=q^{\,|I|-\dim W},}
\]
\[
\boxed{|\pi_A(\mathcal S)|=q^{\,\dim(W+U_A)-\dim W},}
\]
且每个可实现的 \(A\) 坐标有
\[
\boxed{q^{\,|I|-\dim(W+U_A)}}
\]
个完成。特别地，这些公式也适用于 \(A=\varnothing\) 或 \(A=I\)。

## S3 有限域的无限坐标拓扑

有限离散空间 \(k\) 紧且 Hausdorff。由 Tychonoff 定理，\(k^I\) 紧且 Hausdorff。

每一行有限支撑，所以其方程定义 \(k^I\) 中的闭集，实际上是开闭集。有限子系统可解意味着这些闭集具有有限交性质。因此其交集 \(\mathcal S\) 非空；它也是 \(k^I\) 的闭子集，故紧。

若 \(x,x'\in\mathcal S\) 不同，存在坐标 \(i\) 使 \(x_i\ne x'_i\)。相对开闭集
\[
\{z\in\mathcal S:z_i=x_i\}
\]
及其补集将二者分开。所以 \(\mathcal S\) 的每个连通子集至多含一点，即 \(\mathcal S\) 全不连通。

对于任意 \(A\subseteq I\)，投影连续，而 \(k^A\) 是 Hausdorff 空间。因此紧集 \(\pi_A(\mathcal S)\) 在 \(k^A\) 中闭。

最后，\(y\in k^A\) 属于该像，当且仅当满足以下有限可实现条件：
\[
\boxed{\begin{gathered}
\text{对每个有限 }F\subseteq J\text{ 和有限 }B\subseteq A,\\
\text{存在 }x\in k^I\text{，满足 }a_j\cdot x=b_j\ (j\in F)
\text{ 且 }x_i=y_i\ (i\in B).
\end{gathered}}\tag{2}
\]
必要性显然。若 (2) 成立，则所有原方程的闭集和所有坐标条件 \(x_i=y_i\)（\(i\in A\)）的闭集共同具有有限交性质；紧性给出它们的公共点，从而得到所需整体解。

## S4 整体对象与全部恢复目标

这些目标**成立**。以下只使用由系数和常数确定的代数数据，并给出整体及各坐标问题的构造和分类。

### 1. 一致性数据与整体解

令
\[
V=k^{(I)},\qquad W=\operatorname{span}\{a_j:j\in J\}.
\]
每个赋值 \(x\in k^I\) 唯一对应一个代数线性泛函
\[
\phi_x\in V^*,\qquad \phi_x(v)=\sum_{i\in I}v(i)x_i.
\]
反之，\(\phi\in V^*\) 对应赋值 \(x_i=\phi(e_i)\)。因此可将 \(k^I\) 与 \(V^*\) 等同。

有限可解性蕴含：对任何有限线性关系
\[
\sum_{j\in F}t_ja_j=0,
\]
取解 \(F\) 中各行的赋值，可得
\[
\sum_{j\in F}t_jb_j=0.
\]
所以
\[
\lambda:W\to k,\qquad
\lambda\!\left(\sum_{j\in F}t_ja_j\right)=\sum_{j\in F}t_jb_j
\]
是良定义的线性泛函。这一对数据 \((W,\lambda)\) 完全由给定系数和常数确定。

在 ZFC 中，取 \(W\) 的一个基并将其扩充为 \(V\) 的基；在新增基向量上赋值 \(0\)，即可把 \(\lambda\) 延拓为 \(\phi_0\in V^*\)。令
\[
x_i^0=\phi_0(e_i),
\]
便得到整体解。因此
\[
\boxed{\mathcal S=\{\phi\in V^*:\phi|_W=\lambda\}
       =\phi_0+(V/W)^*.}\tag{3}
\]
这里将 \((V/W)^*\) 通过商映射拉回，视为 \(V^*\) 中在 \(W\) 上为零的泛函。

上述论证也证明：**有限可解性等价于所有有限行线性关系都满足相应的常数关系**。满足该条件时，基延拓给出整体解。

### 2. 整体解集的分类

固定 \(k,I\) 后，满足题设的系统，其非空解集由 \((W,\lambda)\) 完全且唯一地分类。

唯一性可直接从解集恢复：
\[
W=\{v\in V:\phi_x(v)\text{ 在 }x\in\mathcal S\text{ 上为常数}\}.
\]
确实，\(v\in W\) 时常数为 \(\lambda(v)\)。若 \(v\notin W\)，可先在 \(W+kv\) 上定义在 \(W\) 为零、在 \(v\) 取 \(1\) 的泛函，再延拓到 \(V\)。将其加到一个解上，便得到在 \(v\) 处取值不同的另一个解。因此也可从该常数恢复 \(\lambda(v)\)。

反过来，任给子空间 \(W\le V\) 和 \(\lambda\in W^*\)，可用 \(W\) 本身作行指标，令每行分别为 \(w\in W\)，右端为 \(\lambda(w)\)。其解集正是 (3)，且由延拓定理非空。因此，允许任意行指标集时，这些对 \((W,\lambda)\) 恰好分类了所有此类非空解集。

### 3. 任意坐标像和全部纤维

固定 \(A\subseteq I\)，令
\[
U_A=\operatorname{span}\{e_i:i\in A\},\qquad L_A=W\cap U_A.
\]
对 \(y\in k^A\)，仍记对应泛函为
\[
\widehat y(u)=\sum_{i\in A}u(i)y_i\quad(u\in U_A).
\]
则
\[
\boxed{\pi_A(\mathcal S)
=\{y\in k^A:\widehat y|_{L_A}=\lambda|_{L_A}\}.}\tag{4}
\]

证明与 S1 相同，但此处使用任意维线性泛函的基延拓：条件 (4) 恰使
\[
\lambda_y:W+U_A\to k,\qquad
\lambda_y(w+u)=\lambda(w)+\widehat y(u) \tag{5}
\]
良定义。把 \(\lambda_y\) 延拓到 \(V\)，就构造出一个满足 \(\pi_A(x)=y\) 的整体解。反向蕴含显然。

因此，若 \(y\) 可实现，任选一个按上述方法构造的解 \(x^y\)，则
\[
\boxed{\pi_A^{-1}(y)=x^y+\bigl(V/(W+U_A)\bigr)^*.}\tag{6}
\]
若 (4) 不成立，纤维为空。坐标像本身则是以
\[
\bigl(U_A/(W\cap U_A)\bigr)^*
\]
为平移空间的非空仿射空间。

这些空间之间还有自然的短正合列
\[
0\longrightarrow \bigl(V/(W+U_A)\bigr)^*
\longrightarrow (V/W)^*
\longrightarrow \bigl(U_A/(W\cap U_A)\bigr)^*
\longrightarrow 0. \tag{7}
\]
最后一个映射是限制映射；它满射，因为交集上为零的泛函可先与 \(W\) 上的零泛函拼接，再延拓到 \(V\)。

更一般地，固定一个可实现的 \(y\)，并令 \(T_A=W+U_A\)。对于任意另一坐标集 \(B\subseteq I\)，无须假定 \(A\subseteq B\)，有
\[
\pi_B\bigl(\pi_A^{-1}(y)\bigr)
=
\{z\in k^B:\widehat z|_{T_A\cap U_B}
                 =\lambda_y|_{T_A\cap U_B}\}. \tag{8}
\]
每个非空的进一步纤维都是
\[
\bigl(V/(W+U_A+U_B)\bigr)^*
\]
的仿射空间。这由将 \(\lambda_y\) 与 \(\widehat z\) 在交集上拼接，再作基延拓得到。

### 4. 可恢复性的判据

由上述描述，得到以下完全判据：

- \(\pi_A\) 满射，当且仅当 \(W\cap U_A=0\)。
- \(\pi_A(\mathcal S)\) 是单点，当且仅当 \(U_A\subseteq W\)。
- \(\pi_A\) 单射，也就是 \(A\) 坐标确定整个解，当且仅当
  \[
  W+U_A=V.
  \]

例如，第一条的必要性中，若 \(0\ne v\in W\cap U_A\)，可在 \(U_A\) 上取一个在 \(v\) 处不同于 \(\lambda(v)\) 的泛函，得到不满足 (4) 的 \(y\)。

更具体地，给定任意可实现的 \(y\)，坐标 \(x_i\) 被 \(y\) 唯一确定，当且仅当
\[
\boxed{e_i\in W+U_A.}\tag{9}
\]
若 \(e_i=w+u\)，其中 \(w\in W,u\in U_A\)，则恢复公式为
\[
x_i=\lambda(w)+\sum_{a\in A}u(a)y_a.
\]
其中只涉及有限多个 \(A\) 坐标；若 \(w=\sum_jt_ja_j\)，常数项就是 \(\sum_jt_jb_j\)。

反之，若 \(e_i\notin W+U_A\)，可构造在 \(W+U_A\) 上为零、在 \(e_i\) 上为 \(1\) 的泛函并延拓到 \(V\)。把它的任意标量倍数加到纤维中的解上，保持 \(A\) 坐标不变，而 \(i\) 坐标遍历整个 \(k\)。

因此，\(A\) 坐标唯一恢复全部 \(B\) 坐标，当且仅当
\[
\boxed{U_B\subseteq W+U_A.}
\]

### 5. 任意基数下的大小和仿射维数

令
\[
\kappa=\dim(V/W),\quad
\alpha_A=\dim\bigl(U_A/(W\cap U_A)\bigr),\quad
\delta_A=\dim\bigl(V/(W+U_A)\bigr),\quad
\mu=|k|.
\]
由基扩充，\(\kappa=\alpha_A+\delta_A\)，右侧为基数加法。取相应商空间的基并使用 (3)、(4)、(6)，得到
\[
\boxed{|\mathcal S|=\mu^\kappa,\qquad
|\pi_A(\mathcal S)|=\mu^{\alpha_A},\qquad
|\pi_A^{-1}(y)|=\mu^{\delta_A}\quad(y\text{ 可实现}).}\tag{10}
\]

其仿射维数分别是对应商空间的**代数对偶空间**的维数；无限维时不能直接将它们写成 \(\kappa,\alpha_A,\delta_A\)。精确地，定义
\[
D_\mu(\rho)=
\begin{cases}
\rho,&\rho\text{ 为有限基数},\\
\mu^\rho,&\rho\text{ 为无限基数}.
\end{cases}
\]
则三者的仿射维数分别为
\[
\boxed{D_\mu(\kappa),\qquad D_\mu(\alpha_A),\qquad
D_\mu(\delta_A).}\tag{11}
\]

证明 (11)：若一个向量空间有基 \(D\)，则其对偶可等同于所有函数构成的 \(k^D\)，所以大小为 \(\mu^{|D|}\)。有限维情形显然。设 \(|D|=\rho\) 无限，其对偶维数记为 \(d\)。若 \(k\) 有限，\(d\) 无限，而无限维有限域向量空间的点数等于其维数，故 \(d=\mu^\rho\)。若 \(k\) 无限，则 \(|k^D|=\max(\mu,d)\)。当 \(\mu^\rho>\mu\) 时立即得到 \(d=\mu^\rho\)；当 \(\mu^\rho=\mu\) 时，取 \(D\) 中可数多个坐标，对每个 \(t\in k\) 构造在这些坐标上依次取 \(1,t,t^2,\ldots\)、在其他坐标取零的函数。Vandermonde 行列式表明这 \(\mu\) 个函数线性无关，因此仍有 \(d=\mu^\rho\)。

## S5 赋值空间的支持

**不成立。** 对任意域 \(k\)，取方程
\[
x_j=1\qquad(j\in\mathbb N).
\]
每行只有一个非零系数。任给有限行集 \(F\)，令
\[
x_j=\begin{cases}1,&j\in F,\\0,&j\notin F,\end{cases}
\]
便得到 \(k^{(\mathbb N)}\) 中的解。

但全系统唯一要求的赋值是所有坐标均为 \(1\)；由于 \(1\ne0\)，它有无限支撑，不属于 \(k^{(\mathbb N)}\)。这不与 S4 矛盾：它仍是全赋值空间 \(k^{\mathbb N}\) 中的解。

## S6 无限域的坐标像

**仍然闭。** 对任意离散域 \(k\)，S4 的 (4) 给出仅涉及有限坐标的闭方程描述：
\[
\boxed{
\pi_A(\mathcal S)
=
\bigcap_{\substack{F\subseteq J\text{ 有限},\ t\in k^F\\
c=\sum_{j\in F}t_ja_j\in U_A}}
\left\{
y\in k^A:
\sum_{i\in A}c(i)y_i=\sum_{j\in F}t_jb_j
\right\}.}\tag{12}
\]
每个 \(c\) 都有限支撑，所以每个方程只涉及有限多个 \(A\) 坐标。在离散域的乘积拓扑中，每个这样的方程集都是开闭集，故其交集闭。

另外，S3 的有限可实现刻画 (2) 对无限域也成立：把坐标条件 \(x_i=y_i\) 加入原方程系。若所有有限行与有限坐标条件同时可解，则增广系统的每个有限子系统可解，S4 的代数延拓构造给出整体解。这里使用的是线性泛函延拓，而非紧性；无限离散域本身一般不紧。