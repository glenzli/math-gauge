下面统一记号：  
\[
\ell_a(x)=\sum_{i\in I}a_i x_i\qquad (a\in k^{(I)},\ x\in k^I),
\]
\[
W=\operatorname{span}_k\{a_j:j\in J\}\subseteq k^{(I)},\qquad 
U_A=\operatorname{span}_k\{e_i:i\in A\}\subseteq k^{(I)}.
\]
对子空间 \(F\subseteq k^{(I)}\)，记
\[
F^\perp=\{x\in k^I:\ell_f(x)=0\ \forall f\in F\}.
\]
若 \(F\subseteq U_A\)，则在 \(k^A\) 中记
\[
F^\circ=\{y\in k^A:\textstyle\sum_{i\in A}f_i y_i=0\ \forall f\in F\}.
\]

---

# S1 有限系统的坐标纤维

设 \(n=|I|\)，\(r=\dim W\)，\(s=\dim(W+U_A)\)。系统相容，取一个解 \(x^0\)。则
\[
\mathcal S=x^0+W^\perp,
\]
所以
\[
\boxed{\dim \mathcal S=n-r=n-\dim W.}
\]

对坐标投影 \(\pi_A(x)=x|_A\)，有
\[
\pi_A(\mathcal S)=x^0|_A+\pi_A(W^\perp).
\]
在有限维空间中有
\[
\pi_A(W^\perp)=(W\cap U_A)^\circ,
\]
因为 \(\pi_A(W^\perp)\) 在 \(k^A\) 中的零化子正是 \(W\cap U_A\)。因此
\[
\boxed{\pi_A(\mathcal S)
=x^0|_A+(W\cap U_A)^\circ,}
\]
并且
\[
\dim \pi_A(\mathcal S)
=|A|-\dim(W\cap U_A)
=\dim(W+U_A)-\dim W
=s-r.
\]

若 \(y\in\pi_A(\mathcal S)\)，任取 \(x_y\in\mathcal S\) 使 \(x_y|_A=y\)。则非空纤维为
\[
\boxed{
\pi_A^{-1}(y)\cap\mathcal S
=x_y+(W+U_A)^\perp,}
\]
因此其仿射维数为
\[
\boxed{
\dim\bigl(\pi_A^{-1}(y)\cap\mathcal S\bigr)
=n-s=n-\dim(W+U_A).}
\]
特别地，所有非空纤维彼此平行，公共方向为 \((W+U_A)^\perp\)。

**可延拓的充要条件。**  
给定 \(y\in k^A\)，它属于 \(\pi_A(\mathcal S)\) 当且仅当
\[
\boxed{
y-x^0|_A\in (W\cap U_A)^\circ.}
\]
等价地，对每个 \(\lambda\in W\cap U_A\)，有
\[
\boxed{
\sum_{i\in A}\lambda_i y_i=\lambda\cdot x^0.}
\]
由于 \(\lambda\in W\)，可写成 \(\lambda=\sum_j c_j a_j\) 的有限线性组合，而 \(\lambda\cdot x^0=\sum_j c_j b_j\)。因此也可写成系数关系形式：
\[
\boxed{
\sum_{j\in J}c_j a_j\in U_A
\Longrightarrow
\sum_{j\in J}c_j b_j
=
\sum_{i\in A}\Bigl(\sum_{j\in J}c_j a_j(i)\Bigr)y_i.}
\]
这里的 \(c_j\) 为任意有限支撑系数族；在 S1 中 \(J\) 有限，所以就是任意 \(c\in k^J\)。

这是充分的：上述条件恰好保证把 \(y\) 固定后，关于剩余变量 \(x_{I\setminus A}\) 的有限线性系统满足所有线性关系，因此可解。必要性由将方程线性组合并限制到 \(A\) 直接得到。

---

# S2 有限域下的精确计数

设 \(|k|=q\)，仍记
\[
n=|I|,\qquad r=\dim W,\qquad s=\dim(W+U_A).
\]
由 S1，解集是仿射空间，方向为 \(W^\perp\)，故
\[
\boxed{|\mathcal S|=q^{\,n-r}=q^{\,|I|-\dim W}.}
\]

坐标像的仿射维数为
\[
\dim\pi_A(\mathcal S)=s-r
=\dim(W+U_A)-\dim W,
\]
故可实现 \(A\)-坐标的总数为
\[
\boxed{
|\pi_A(\mathcal S)|
=q^{\,s-r}
=q^{\,\dim(W+U_A)-\dim W}
=q^{\,|A|-\dim(W\cap U_A)}.}
\]

每个可实现坐标 \(y\in\pi_A(\mathcal S)\) 的完成数为每个非空纤维的大小。纤维方向维数为 \(n-s\)，所以
\[
\boxed{
\left|\pi_A^{-1}(y)\cap\mathcal S\right|
=q^{\,n-s}
=q^{\,|I|-\dim(W+U_A)}.}
\]
这两个数相乘正好给出
\[
q^{s-r}q^{n-s}=q^{n-r}=|\mathcal S|.
\]

---

# S3 有限域的无限坐标拓扑

设 \(k\) 有限离散。于是 \(k^I\) 是有限离散空间的乘积，故由 Tychonoff 定理紧、Hausdorff；其由有限坐标柱集
\[
C_{B,\eta}=\{x\in k^I:x|_B=\eta\}\qquad(B\subseteq I\ \text{有限})
\]
给出闭开基，因此 \(k^I\) 全不连通。

对每个 \(j\in J\)，因为 \(a_j\) 有限支撑，函数
\[
x\longmapsto \ell_{a_j}(x)=\sum_i a_j(i)x_i
\]
只依赖有限个坐标，故连续。于是
\[
C_j=\{x\in k^I:\ell_{a_j}(x)=b_j\}
\]
是闭集，且
\[
\mathcal S=\bigcap_{j\in J}C_j.
\]

**非空。**  
任取有限 \(F\subseteq J\)，由假设 \(\bigcap_{j\in F}C_j\neq\varnothing\)。故闭集族 \(\{C_j:j\in J\}\) 具有有限交性质。由 \(k^I\) 紧，得
\[
\mathcal S\neq\varnothing.
\]

**紧且全不连通。**  
\(\mathcal S\) 是紧空间 \(k^I\) 的闭子集，故紧。全不连通性由 \(k^I\) 全不连通且为遗传性质得到；也可直接使用 \(\mathcal S\cap C_{B,\eta}\) 作为闭开基。因此
\[
\boxed{\mathcal S\text{ 非空、紧且全不连通。}}
\]

**坐标像闭。**  
投影 \(\pi_A:\mathcal S\to k^A\) 连续；\(\mathcal S\) 紧，\(k^A\) Hausdorff，故 \(\pi_A(\mathcal S)\) 紧，从而是闭集：
\[
\boxed{\pi_A(\mathcal S)\subseteq k^A\text{ 闭}.}
\]

**像的刻画。**  
断言：
\[
\boxed{
y\in\pi_A(\mathcal S)
\iff
\begin{array}{l}
\text{对每个有限 }F\subseteq J\text{ 和每个有限 }B\subseteq A,\\
\text{存在 }x\in k^I\text{ 使 }\ell_{a_j}(x)=b_j\ (j\in F)
\text{ 且 }x|_B=y|_B.
\end{array}}
\]

必要性显然：取 \(x\in\mathcal S\) 且 \(x|_A=y\)，则对任意有限 \(F,B\)，同一个 \(x\) 满足全部条件。

反之，假设上述有限相容条件成立。考虑闭集族
\[
\{C_j:j\in J\}\cup
\{\{x:x_i=y_i\}:i\in A\}.
\]
任一有限交只涉及有限个 \(j\) 和有限个 \(A\)-坐标，因此由假设非空。由 \(k^I\) 紧，整个族有交。取交中一点 \(x\)，则 \(x\in\mathcal S\) 且 \(x|_A=y\)。故 \(y\in\pi_A(\mathcal S)\)。

---

# S4 整体对象与全部恢复目标

**结论：在 ZFC 下，题目所列目标全部成立。**  
关键点是每个 \(a_j\) 只有有限支撑，因此 \(a_j\) 可视为 \(k^{(I)}\) 中的有限坐标线性泛函；有限相容性只给出 \(W\) 上一个良定义的线性泛函 \(\beta\)，再用基延拓即可得到整体解。

## S4.1 基本代数数据

令
\[
E=k^{(I)},\qquad V=k^I.
\]
把 \(E\) 嵌入 \(V^*\)：每个 \(a\in E\) 对应有限坐标线性泛函
\[
\ell_a(x)=\sum_i a_i x_i.
\]
令
\[
W=\operatorname{span}_k\{a_j:j\in J\}\subseteq E.
\]

定义
\[
\boxed{\beta:W\to k,\qquad \beta(a_j)=b_j.}
\]
它良定义。事实上，若
\[
\sum_{t=1}^m c_t a_{j_t}=0,
\]
取有限子系统 \(\{j_1,\dots,j_m\}\) 的一个解 \(x\)，则
\[
0=\sum_{t=1}^m c_t\ell_{a_{j_t}}(x)
=\sum_{t=1}^m c_t b_t.
\]
故 \(\sum c_t b_t\) 只依赖于 \(\sum c_t a_{j_t}\)，不依赖于表示。

反过来，若 \(\beta\) 良定义，则由有限线性代数，每个有限子系统相容；故题设有限相容性等价于 \(\beta\) 良定义。

## S4.2 整体解的构造

取 \(E\) 的一组基，使其包含 \(W\) 的一组基；在 \(W\) 上按 \(\beta\) 定义线性泛函，在其余基向量上任意取值，例如取 \(0\)。这样得到线性延拓
\[
L:E\to k,\qquad L|_W=\beta.
\]
令
\[
\boxed{x^0_i=L(e_i)\qquad(i\in I).}
\]
对任意 \(j\in J\)，由于 \(a_j\) 有限支撑，
\[
a_j=\sum_{i\in I}a_j(i)e_i
\]
是有限线性组合，因此
\[
\ell_{a_j}(x^0)
=\sum_i a_j(i)L(e_i)
=L(a_j)
=\beta(a_j)
=b_j.
\]
所以 \(x^0\in\mathcal S\)。特别地，
\[
\boxed{\mathcal S\neq\varnothing.}
\]

更一般地，所有整体解与 \(\beta\) 到 \(E\) 的所有线性延拓一一对应：
\[
\boxed{
\mathcal S
\longleftrightarrow
\{L\in E^*:L|_W=\beta\},
\qquad
x\longleftrightarrow L_x,\quad L_x(a)=\ell_a(x).}
\]
其逆为
\[
L\longmapsto x^L=(L(e_i))_{i\in I}.
\]
这个对应说明：不同的基延拓选择正好对应不同的解，而不是不同的解集。

## S4.3 \(\mathcal S\) 的描述与分类

由定义，
\[
\boxed{
\mathcal S
=\{x\in k^I:\ell_w(x)=\beta(w)\ \forall w\in W\}
=x^0+W^\perp.}
\]
因此 \(\mathcal S\) 是非空仿射空间，方向为 \(W^\perp\)。它是闭的，因为 \(W^\perp\) 是有限坐标超平面的交。

**解集的分类。**  
考虑所有有序对
\[
(W,\beta),\qquad W\subseteq k^{(I)}\text{ 为线性子空间},\quad
\beta\in\operatorname{Hom}_k(W,k).
\]
每个这样的对定义一个解集
\[
\mathcal S(W,\beta)
=\{x\in k^I:\ell_w(x)=\beta(w)\ \forall w\in W\}.
\]
由上面的构造，\(\mathcal S(W,\beta)\neq\varnothing\)。反之，任一有限支撑行系统都给出这样的对。

而且这个对应是单射。设 \(\mathcal S=\mathcal S(W,\beta)\neq\varnothing\)。定义
\[
\widetilde W
=\{w\in E:\ell_w|_{\mathcal S}\text{ 在 }\mathcal S\text{ 上是常值函数}\}.
\]
显然 \(W\subseteq\widetilde W\)。若 \(w\in E\setminus W\)，考虑辅助系统（变量为 \(d\in k^I\)）
\[
\ell_u(d)=0\quad(u\in W),\qquad
\ell_w(d)=1.
\]
它的任一有限子系统都相容：若有限线性关系
\[
\sum_t c_tu_t+cw=0
\]
成立，且 \(c\neq0\)，则 \(w\in W\)，矛盾；故 \(c=0\)，右端关系也自动为 \(0\)。由已证的整体存在性定理，存在 \(d\in k^I\) 满足上述辅助系统。于是 \(d\in W^\perp\)，从而对任意 \(x\in\mathcal S\)，
\[
x+d\in\mathcal S,\qquad
\ell_w(x+d)=\ell_w(x)+1,
\]
故 \(\ell_w\) 在 \(\mathcal S\) 上不是常值。矛盾。所以
\[
\widetilde W=W.
\]
一旦 \(W\) 恢复，\(\beta(w)\) 就是在 \(\mathcal S\) 上的常值，故 \(\beta\) 也恢复。因此
\[
\boxed{
(W,\beta)\longleftrightarrow \mathcal S(W,\beta)
}
\]
是非空解集与代数数据对的一一对应。

换言之，两个有限支撑行系统有相同的解集，当且仅当它们给出同一个 \(W\) 和同一个 \(\beta:W\to k\)。

## S4.4 每个坐标像的完整描述

令
\[
W_A=W\cap U_A
=\{w\in W:\operatorname{supp}w\subseteq A\},
\qquad
\beta_A=\beta|_{W_A}.
\]
由 \(W_A\subseteq U_A\)，可把 \(W_A\) 自然视为 \(k^{(A)}\) 的子空间。

断言：
\[
\boxed{
\pi_A(\mathcal S)
=\mathcal S(W_A,\beta_A)
=\left\{y\in k^A:
\ell_\lambda(y)=\beta(\lambda)
\ \forall\lambda\in W_A\right\}.}
\]
更明确地，
\[
\boxed{
\pi_A(\mathcal S)
=\left\{y\in k^A:
\sum_{i\in A}\lambda_i y_i=\beta(\lambda)
\ \forall\lambda\in W_A\right\}.}
\]

**证明。**  
若 \(y=x|_A\)，\(x\in\mathcal S\)，且 \(\lambda\in W_A\subseteq W\)，则 \(\lambda\) 只在 \(A\) 上有非零坐标，故
\[
\ell_\lambda(y)=\ell_\lambda(x)=\beta(\lambda).
\]
所以 \(\pi_A(\mathcal S)\subseteq\mathcal S(W_A,\beta_A)\)。

反之，设 \(y\in k^A\) 满足上述所有限制方程。令 \(B=I\setminus A\)，考虑未知量 \(z\in k^B\) 的系统
\[
\boxed{
\ell_{w|_B}(z)
=
\beta(w)-\ell_{w|_A}(y)
\qquad(w\in W).}
\]
每个 \(w|_B\) 仍有限支撑。我们验证该系统每个有限子系统都相容。取 \(w_1,\dots,w_m\in W\)，并设
\[
\sum_{t=1}^m c_t w_t|_B=0.
\]
令 \(w=\sum_t c_tw_t\in W\)。则 \(w|_B=0\)，即 \(w\in W_A\)。由 \(y\) 满足限制方程，
\[
\ell_w(y)=\beta(w).
\]
于是
\[
\sum_{t=1}^m c_t
\bigl(\beta(w_t)-\ell_{w_t|_A}(y)\bigr)
=
\beta(w)-\ell_w(y)
=0.
\]
故该有限线性系统满足全部线性关系，有限相容。由 S4.2 的整体存在性定理，存在 \(z\in k^B\) 解整个系统。令 \(x\in k^I\) 满足 \(x|_A=y,\ x|_B=z\)。则对每个 \(w\in W\)，
\[
\ell_w(x)
=\ell_{w|_A}(y)+\ell_{w|_B}(z)
=\beta(w).
\]
特别地对所有 \(a_j\) 成立，故 \(x\in\mathcal S\) 且 \(x|_A=y\)。因此 \(y\in\pi_A(\mathcal S)\)。证毕。

因此坐标像自动是
\[
\boxed{
\pi_A(\mathcal S)
=x^0|_A+(W_A)^\circ,}
\]
其中
\[
(W_A)^\circ
=\{y\in k^A:\ell_\lambda(y)=0\ \forall\lambda\in W_A\}
\]
是闭子空间。

## S4.5 所有非空纤维

对 \(y\in\pi_A(\mathcal S)\)，纤维为
\[
\mathcal S_y
=\{x\in\mathcal S:x|_A=y\}.
\]
任取 \(x_y\in\mathcal S\) 使 \(x_y|_A=y\)。令
\[
K_A=(W+U_A)^\perp
=W^\perp\cap U_A^\perp.
\]
显式地，
\[
K_A
=\left\{d\in k^I:
d_i=0\ (i\in A),\quad
\ell_w(d)=0\ (w\in W)
\right\}.
\]
断言：
\[
\boxed{
\mathcal S_y
=x_y+K_A.}
\]
事实上，若 \(d\in K_A\)，则 \(d\in W^\perp\) 且 \(d|_A=0\)，故 \(x_y+d\in\mathcal S\) 且仍限制为 \(y\)。反之，若 \(x\in\mathcal S_y\)，则
\[
d=x-x_y\in W^\perp,\qquad d|_A=0.
\]
于是 \(d\) 同时零化 \(W\) 和 \(U_A\)，故 \(d\in(W+U_A)^\perp=K_A\)。

因此：
\[
\boxed{
\text{所有非空纤维恰为 }
x+K_A\quad(x\in\mathcal S),
}
\]
它们彼此平行、两两不交，公共方向为 \(K_A\)。等价地，坐标投影给出仿射同构
\[
\boxed{
\mathcal S/K_A\;\cong\;\pi_A(\mathcal S),
\qquad
[x]\longmapsto x|_A.}
\]
并且
\[
\boxed{
\mathcal S_y\neq\varnothing
\iff
y\in\pi_A(\mathcal S)
=\mathcal S(W_A,\beta_A).}
\]
每个非空纤维的仿射维数为
\[
\boxed{\dim_k K_A=\dim_k (W+U_A)^\perp.}
\]

## S4.6 维数与“恢复”判据

有仿射维数公式
\[
\boxed{
\dim\mathcal S=\dim_k W^\perp,}
\]
\[
\boxed{
\dim\pi_A(\mathcal S)=\dim_k (W_A)^\circ,}
\]
\[
\boxed{
\dim(\text{非空纤维})=\dim_k (W+U_A)^\perp.}
\]
若 \(I\) 有限，则化为 S1 中的整数公式：
\[
\dim\mathcal S=|I|-\dim W,
\]
\[
\dim\pi_A(\mathcal S)
=|A|-\dim(W\cap U_A)
=\dim(W+U_A)-\dim W,
\]
\[
\dim(\text{纤维})
=|I|-\dim(W+U_A).
\]

由此还可读出全部坐标恢复判据：

1. \(\pi_A\) 是单射，即 \(A\)-坐标完全决定整体解，当且仅当
   \[
   \boxed{K_A=0\iff W+U_A=E=k^{(I)}.}
   \]
   因为 \(K_A\) 正是投影在 \(\mathcal S\) 上的核；而 \((W+U_A)^\perp=0\) 当且仅当 \(W+U_A\) 在整个 \(E\) 中稠密，但 \(E\) 为离散直和，故等价于 \(W+U_A=E\)。

2. \(\pi_A\) 是满射，即任意 \(A\)-坐标都可延拓，当且仅当
   \[
   \boxed{W_A=W\cap U_A=0.}
   \]

3. \(\pi_A\) 是双射，当且仅当
   \[
   \boxed{W_A=0\quad\text{且}\quad W+U_A=E.}
   \]

这样，\(\mathcal S\)、所有坐标像、所有非空纤维以及全部恢复问题都由 \((W,\beta)\) 这一仅由系数 \(a_j\) 和常数 \(b_j\) 决定的代数数据完整描述。

---

# S5 赋值空间的支持

**结论：不成立。**  
即使每个有限子系统在 \(k^{(\mathbb N)}\) 中有解，全系统也未必在 \(k^{(\mathbb N)}\) 中有解。

取 \(I=J=\mathbb N=\{0,1,2,\dots\}\)，方程如下：
\[
x_0=1,
\]
以及
\[
x_{n-1}-x_n=0\qquad(n\ge1).
\]
即
\[
a_0=e_0,\quad b_0=1;\qquad
a_n=e_{n-1}-e_n,\quad b_n=0\quad(n\ge1).
\]
每行均有限支撑。

任取有限个方程，令其中出现的最大指标为 \(N\)。定义
\[
x_i=
\begin{cases}
1,&0\le i\le N,\\
0,&i>N.
\end{cases}
\]
则 \(x\in k^{(\mathbb N)}\)，并且满足所选方程：\(x_0=1\)，且对所选的所有 \(n\le N\) 有 \(x_{n-1}=x_n=1\)。所以每个有限子系统在 \(k^{(\mathbb N)}\) 中有解。

但整个系统强制
\[
x_0=x_1=x_2=\cdots=1,
\]
即唯一的 \(k^{\mathbb N}\)-解为常值 \(1\) 序列，它不具有有限支撑。因此全系统在 \(k^{(\mathbb N)}\) 中无解。

所以：
\[
\boxed{\text{有限子系统的有限支撑可解性不蕴含全系统的有限支撑可解性。}}
\]
注意全系统在 \(k^{\mathbb N}\) 中确有解；S3 的紧性只能保证这种“全赋值”解，不能保证有限支撑解。

---

# S6 无限域的坐标像

**结论：成立。**  
即使 \(k\) 无限，每个
\[
\pi_A(\mathcal S)\subseteq k^A
\]
在乘积拓扑中仍然闭，而且可以由只涉及有限个坐标的闭方程精确描述。

沿用 S4 的 \(W,\beta,W_A,\beta_A\)。由 S4.4，
\[
\boxed{
\pi_A(\mathcal S)
=
\left\{
y\in k^A:
\sum_{i\in A}\lambda_i y_i=\beta(\lambda)
\quad\forall\lambda\in W_A
\right\},}
\]
其中
\[
W_A=W\cap U_A
=\{\lambda\in W:\operatorname{supp}\lambda\subseteq A\}.
\]
对每个固定的 \(\lambda\in W_A\)，因为 \(\lambda\) 有限支撑，方程
\[
\sum_{i\in A}\lambda_i y_i=\beta(\lambda)
\]
只涉及 \(y\) 的有限个坐标。定义闭集
\[
C_\lambda
=
\left\{y\in k^A:
\sum_{i\in A}\lambda_i y_i=\beta(\lambda)
\right\}.
\]
由于 \(k\) 离散，坐标投影连续，故每个 \(C_\lambda\) 在 \(k^A\) 中既闭又开。于是
\[
\boxed{
\pi_A(\mathcal S)
=
\bigcap_{\lambda\in W_A}C_\lambda}
\]
是闭集的交，从而闭。

若 \(W_A=0\)，则约定该交集为全空间 \(k^A\)，此时投影是满射。

因此：
\[
\boxed{
\pi_A(\mathcal S)\text{ 在 }k^A\text{ 的乘积拓扑中闭，且其闭方程描述为 }
\sum_{i\in A}\lambda_i y_i=\beta(\lambda)
\quad(\lambda\in W_A).
}
\]
这些方程每个只涉及有限多个坐标；即使 \(W_A\) 是无限维、\(A\) 无限、\(k\) 无限，也不出现任何无限和或极限条件。