# 参考论证：无限方程系的坐标恢复

主目标成立。下述分类允许任意集合指标和任意域；所有线性组合均为有限和，所有对偶均为代数对偶。

## 由输入得到的对象和分类

置 $V=k^{(I)}$、$E=k^{(J)}$，定义线性映射

$$T:E\longrightarrow V,\qquad T\lambda=\sum_j\lambda_j a_j,
\qquad B:E\longrightarrow k,\qquad B\lambda=\sum_j\lambda_j b_j.$$

记 $W=\operatorname{im}T$。对于 $A\subseteq I$，令 $V_A=k^{(A)}$，$\iota_A:V_A\to V$ 为延零包含，$U_A=\operatorname{im}\iota_A=\operatorname{span}\{e_i:i\in A\}$。若 $y\in k^A$，记

$$g_y(z)=\sum_{i\in A}z_i y_i\qquad(z\in V_A).$$

分类如下。

1. $\mathcal S$ 非空。选择任一 $x^0\in\mathcal S$ 后，存在双射
   $$ (V/W)^*\longrightarrow\mathcal S,\qquad
      \ell\longmapsto\bigl(x_i^0+\ell(e_i+W)\bigr)_{i\in I}. \tag{1}$$
   此公式也给出解空间的仿射结构：平移空间为 $(V/W)^*$，并未选出不依赖选择的原点。
2. $y\in\pi_A(\mathcal S)$ 的充要条件是
   $$T\lambda=\iota_Az\quad\Longrightarrow\quad B\lambda=g_y(z)
   \qquad(\lambda\in E,\ z\in V_A). \tag{2}$$
   这是只含输入行、常数和 $y$ 的有限线性组合判据。
3. 若 (2) 成立，选择任一 $x^0\in\pi_A^{-1}(y)$ 后，存在双射
   $$ (V/(W+U_A))^*\longrightarrow\pi_A^{-1}(y),\qquad
      \ell\longmapsto\bigl(x_i^0+\ell(e_i+W+U_A)\bigr)_{i\in I}. \tag{3}$$
   因而每个非空纤维的全部自由度由这个商空间的代数对偶给出。

这些公式也适用于空指标集和空坐标集，所出现的零空间与空有限和按通常约定解释。

## 有限相容性产生整体解

先证明 $\ker T\subseteq\ker B$。设 $T\lambda=0$。取有限集合 $F=\operatorname{supp}\lambda$，由题设选择满足 $F$ 中全部方程的 $x$。配对后有

$$0=\sum_i(T\lambda)_i x_i
=\sum_{j\in F}\lambda_j\sum_i a_j(i)x_i
=\sum_{j\in F}\lambda_j b_j=B\lambda.$$

有限和的交换合法，因为 $F$ 及每个 $a_j$ 的支撑均有限。因此

$$\beta:W\to k,\qquad\beta(T\lambda)=B\lambda$$

定义良好且线性：两个原像之差在 $\ker T$ 中，其 $B$ 值之差为零。

在 ZFC 中，将 $W$ 的一组基扩充为 $V$ 的一组基，在新基向量上任意指定值，便把 $\beta$ 扩张为线性泛函 $f_0:V\to k$。置 $x_i^0=f_0(e_i)$。每个 $a_j$ 是有限线性组合，故

$$\sum_i a_j(i)x_i^0=f_0(a_j)=\beta(a_j)=b_j.$$

这构造了整体解。反向地，任一整体解通过 $v\mapsto\sum_i v_i x_i$ 给出延拓 $\beta$ 的线性泛函。此对应与取基向量上的值互逆。

## 全部整体解

设 $f,f_0$ 为两个这样的延拓。差 $f-f_0$ 在 $W$ 上为零，故唯一下降为 $\ell:V/W\to k$。反过来，任一 $\ell$ 给出 $f=f_0+\ell\circ q_W$，它仍在 $W$ 上等于 $\beta$。两步互逆，取各 $e_i$ 的值即得 (1)。加上任意两个商泛函与逐次平移一致，减去两个解得到唯一的商泛函，这验证了所述仿射结构和自由度。

## 坐标像的充分性与必要性

若 $x\in\mathcal S$ 且 $x|_A=y$，对 $T\lambda=\iota_A z$ 与 $x$ 配对，左侧得到 $B\lambda$，右侧得到 $g_y(z)$，故 (2) 必要。

反之，假设 (2)。在 $E\oplus V_A$ 上定义

$$L(\lambda,z)=T\lambda+\iota_Az,
\qquad D(\lambda,z)=B\lambda+g_y(z).$$

若 $L(\lambda,z)=0$，则 $T\lambda=\iota_A(-z)$。由 (2)，$B\lambda=g_y(-z)$，故 $D(\lambda,z)=0$。于是 $\ker L\subseteq\ker D$，从而 $D$ 唯一下降为 $\operatorname{im}L=W+U_A$ 上的线性泛函。按前述基扩充方法把它扩张到 $V$，得到 $f$。由于

$$f(a_j)=D(e_j,0)=b_j,
\qquad f(e_i)=D(0,e_i)=y_i\quad(i\in A),$$

$x_i=f(e_i)$ 是所需整体解，且 $x|_A=y$。这证明 (2) 的充分性。

## 每个非空纤维

同一纤维中两个解对应的泛函之差既在 $W$ 上为零，又在全部 $e_i$（$i\in A$）上为零，因而恰好在 $W+U_A$ 上为零。它唯一下降为 $V/(W+U_A)$ 上的泛函。反过来，把任意这样的商泛函拉回并加到一个已选纤维点上，同时保持原方程和 $A$ 上全部坐标。与前面的整体分类一样，这两步互逆，得到 (3)。

## 同一构造给出的有限关系结论

作为分类的另一种检验，给定 $v\in V,c\in k$，有

$$\bigl(\forall x\in\mathcal S,\ \sum_i v_i x_i=c\bigr)
\quad\Longleftrightarrow\quad
\exists\lambda\in E,\quad T\lambda=v,\quad B\lambda=c. \tag{4}$$

右向左由有限线性组合立即成立。对左向右，先取 $x^0\in\mathcal S$。若 $v\notin W$，在 $W+kv$ 上把 $W$ 送到零、把 $v$ 送到一，再扩张到 $V$，得到在 $W$ 上为零但在 $v$ 上非零的泛函。把它加到 $x^0$ 对应的泛函上会改变 $v$ 的值而仍满足全部原方程，矛盾。因此 $v=T\lambda$；再与 $x^0$ 配对便得 $B\lambda=c$。式 (4) 是已证明的附加结论，不增加题面的最低完成义务。

## 来源和验证范围

基扩充与线性泛函延拓的标准背景见 [Mathlib 的向量空间基文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/VectorSpace.html)，相应实际依赖为固定 Mathlib 版本中的 `LinearMap.exists_extend` 和 `Submodule.exists_le_ker_of_notMem`。其余相容性、参数化、坐标像和纤维论证均在本文给出。没有引用未公开 OET 材料。

Lean 对原有限支撑行、完整赋值空间、所有坐标子集和实际商空间构造上述映射，并检查双射及像判据。具体覆盖见 formal/COVERAGE.md。独立 AI 审核、隔离编译与人工审定分别记录；human 状态仍为 pending。
