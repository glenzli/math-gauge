## 审阅结论

原答卷 S1–S6 的数学结论、构造与主要论证正确，没有发现满足题设的反例或影响结论实质缺口。因此 `current-check` 中的 `KEEP` 可以维持。

`current-check` 用“扩充方程组”再次证明 S6，也是成立的；其中的线性紧性论证属于冗余的第三种论证。需要区分普通紧性与线性紧性，并应把“Hahn–Banach”改称“线性泛函的基延拓”，但这些表述问题不影响任何结论。

## S1：有限系统

令

\[
V=k^I,\qquad W=\operatorname{span}\{a_j:j\in J\},\qquad
U_A=\operatorname{span}\{e_i:i\in A\}.
\]

相容时，取任意特解 \(x_0\)，解集和齐次方向分别为

\[
\mathcal S=x_0+W^\perp,\qquad
\dim\mathcal S=|I|-\dim W.
\]

对于 \(y\in\pi_A(\mathcal S)\)，其纤维方向为

\[
W^\perp\cap U_A^\perp=(W+U_A)^\perp,
\]

所以

\[
\dim\mathcal F_y
=|I|-\dim(W+U_A).
\]

延拓条件也正确。因为 \(a_j\) 只依赖有限个坐标，存在与全部方程相容的线性泛函

\[
\beta:W\to k,\qquad
\beta\left(\sum_jc_ja_j\right)=\sum_jc_jb_j.
\]

原答案中的必要性核对如下：若 \(x|_A=y\)，则对 \(w\in W\cap U_A\)，

\[
\sum_{i\in A}w_iy_i
=\langle w,x\rangle
=\beta(w).
\]

充分性可以直接构造：定义

\[
\gamma_y:U_A\to k,\qquad
\gamma_y(u)=\sum_{i\in A}u_iy_i.
\]

上述条件恰好说明 \(\beta\) 与 \(\gamma_y\) 在 \(W\cap U_A\) 上一致，所以

\[
\psi(w+u)=\beta(w)+\gamma_y(u)
\]

是 \(W+U_A\) 上良定义的线性泛函。将它延拓到 \(V\)，令 \(x_i=\psi(e_i)\)，就有 \(x\in\mathcal S\) 且 \(x|_A=y\)。

因此，延拓的充要条件应为

\[
\boxed{
\forall w\in W\cap U_A,\qquad
\sum_{i\in A}w_iy_i=\beta(w).
}
\]

原答案的结论与有限维伴随映射论证均正确。

## S2：有限域计数

由 S1，

\[
|\mathcal S|=q^{|I|-\dim W}.
\]

所有非空纤维大小相同：

\[
|\mathcal F_y|
=q^{|I|-\dim(W+U_A)|}.
\]

因此可实现的 \(A\)-坐标数为

\[
|\pi_A(\mathcal S)|
=\frac{|\mathcal S|}{|\mathcal F_y|}
=q^{\dim(W+U_A)-\dim W}.
\]

三个公式只使用题面指定参数，且均正确。

## S3：有限域的无限坐标系统

有限域 \(k\) 是紧 Hausdorff 全不连通空间，因此 \(k^I\) 具有这些性质。每行 \(a_j\) 有限支撑，所以

\[
f_j(x)=\sum_i a_j(i)x_i
\]

是连续函数；单方程解集

\[
\mathcal S_j=f_j^{-1}(\{b_j\})
\]

闭，并且题设保证它满足有限交性质。由 \(k^I\) 的紧性，

\[
\mathcal S=\bigcap_{j\in J}\mathcal S_j
\]

非空、紧且闭。闭子空间继承全不连通性。

坐标像 \(\pi_A(\mathcal S)\) 是紧集 \(\mathcal S\) 的连续像，因而紧；\(k^A\) 是 Hausdorff 空间，所以它闭。其有限可实现性刻画同样由有限交性质和紧性给出：

\[
\begin{aligned}
y\in\pi_A(\mathcal S)
\Longleftrightarrow\;&
\forall\text{ finite }F\subseteq J,\ 
\forall\text{ finite }B\subseteq A,\\
&\exists x\in k^I:
\quad f_j(x)=b_j\ (j\in F),
\quad x|_B=y|_B.
\end{aligned}
\]

该命题及证明完整正确。

## S4：整体解、像与纤维

答卷的核心结论均正确。

首先，对任意有限关系

\[
\sum_{j\in F}c_ja_j=0,
\]

任取 \(F\) 的一个解 \(x\)，得到

\[
\sum_{j\in F}c_jb_j
=\left\langle\sum_{j\in F}c_ja_j,x\right\rangle
=0.
\]

因此

\[
\beta\left(\sum_{j\in F}c_ja_j\right)
=\sum_{j\in F}c_jb_j
\]

在 \(W\) 上良定义，并且是线性泛函。

利用基扩充得到 \(\widetilde\beta:k^{(I)}\to k\)，再令 \(x_i^*=\widetilde\beta(e_i)\)。于是

\[
\sum_i a_j(i)x_i^*=\beta(a_j)=b_j.
\]

所以整体解存在，并且

\[
\mathcal S=x^*+W^\circ
=
\{x\in k^I:\langle w,x\rangle=\beta(w)\ \forall w\in W\}.
\]

对任意 \(A\subseteq I\)，有

\[
\boxed{
\pi_A(\mathcal S)
=
\left\{
y\in k^A:
\forall w\in W\cap U_A,\ 
\sum_{i\in A}w_iy_i=\beta(w)
\right\}.
}
\]

原答案的反向包含证明正确：条件允许把 \(\beta\) 和

\[
\gamma_y(u)=\sum_{i\in A}u_iy_i
\]

拼接为 \(W+U_A\) 上的线性泛函，再延拓到 \(k^{(I)}\)。得到的代数对偶元素正好满足原系统且限制为 \(y\)。

对 \(y\in\pi_A(\mathcal S)\) 和 \(x\in\mathcal S\cap\pi_A^{-1}(y)\)，

\[
\pi_A^{-1}(y)\cap\mathcal S
=x+(W+U_A)^\circ.
\]

分类表也正确。具体可写为：

- \(\pi_A|_{\mathcal S}\) 单射，当且仅当
  \[
  (W+U_A)^\circ=\{0\}
  \iff W+U_A=k^{(I)}.
  \]
- 满射，当且仅当
  \[
  W\cap U_A=\{0\}.
  \]
  因为交集中的一个非零 \(w\) 总会在 \(k^A\) 上产生一个非平凡的仿射约束；反之交集为零时没有约束。
- 双射，当且仅当
  \[
  W\oplus U_A=k^{(I)}.
  \]

原答卷没有展开这些从核空间和像公式直接读出的细节，但属于普通的定义性代数推导，不构成数学缺口。

## S5：有限支撑解空间中的反例

原答卷的反例正确：

\[
x_1=1,\qquad x_{j-1}-x_j=0\quad(j\ge2).
\]

对任意有限 \(F\subseteq\mathbb N\)，取 \(M=\max F\)，并令

\[
x_i=
\begin{cases}
1,&i\le M,\\
0,&i>M,
\end{cases}
\]

就得到该子系统在 \(k^{(\mathbb N)}\) 中的解。

但全系统的唯一解为

\[
x=(1,1,1,\ldots),
\]

其支撑是无限的，所以全系统在 \(k^{(\mathbb N)}\) 中无解。结论和反例均完整。

## S6：无限域下的坐标像

S6 的肯定判断正确。由 S4，

\[
\pi_A(\mathcal S)
=
\bigcap_{w\in W\cap U_A}C_w,
\qquad
C_w=
\left\{
y\in k^A:
\sum_{i\in A}w_iy_i=\beta(w)
\right\}.
\]

对于每个 \(w\in W\cap U_A\)，其支撑有限。因此 \(C_w\) 是有限个坐标的等值约束。在离散域 \(k\) 的乘积空间中，有限坐标上的加法与投影都是连续的，所以每个 \(C_w\) 都是闭集，事实上是 clopen 的柱状集。任意多个闭集之交仍闭，故

\[
\pi_A(\mathcal S)
\]

在 \(k^A\) 中闭。该证明与 \(k\) 是有限域还是无限域无关。

`current-check` 的第一种证明也成立：若 \(y^*\in\overline{\pi_A(\mathcal S)}\)，则对每个有限 \(B\subseteq A\)，存在 \(x\in\mathcal S\) 使 \(x|_B=y^*|_B\)。于是加入约束 \(x_i=y_i^*\) 后，扩充系统仍满足 S4 的有限相容性条件，因而有整体解。该解属于 \(\mathcal S\) 且限制为 \(y^*\)，所以 \(y^*\in\pi_A(\mathcal S)\)。

## 对 `current-check` 的具体评价

`current-check` 的 `KEEP` 结论正确，前两项论证完整。第三项线性紧性论证属于冗余内容；若保留，应明确说明这里讨论的是线性紧性而非通常的紧致性。将线性泛函延拓称为“Hahn–Banach”也略显宽泛，准确说法是任意域上的基扩充或线性泛函延拓。这两种表述均不影响原证明的正确性。

## 保留、修正与自评

- **保留：** S1–S6 的全部最终判断、主要构造、计数公式、拓扑论证及 S5 反例。
- **新增/修正：** 补写了 S4 分类表的几个直接等价推导；明确了 S6 的有限支撑闭方程证明；将线性紧性引用标为冗余，并收紧泛函延拓的术语。
- **仍未完成或不确定：** 核心要求没有未完成部分；未发现需要撤回的数学断言，也没有依赖不确定的额外假设。

原答卷满足原题的全部数学要求；`current-check` 的 `KEEP` 判断有充分依据。