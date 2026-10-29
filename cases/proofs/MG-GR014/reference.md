# 线性关系、坐标纤维与无限赋值：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 有限系统的坐标纤维

判定：construction。

令 β(Σλ_ja_j)=Σλ_jb_j；相容解保证它良定义。解是 V=k^I 上延拓 β 的泛函，选一个延拓后差空间为 (V/W)*，维数 |I|−dim W。给 y∈k^A，延拓存在当且仅当 β 与 g_y 在 W∩U_A 上相等；这时二者拼成 W+U_A 上的泛函，再补基延到 V。非空纤维差空间是 (V/(W+U_A))*，维数 |I|−dim(W+U_A)。此处任意有限基补充均有效。

判准：维数与实际双向延拓判据；非空纤维平移空间。

## S2 有限域下的精确计数

判定：true。

解数为 q^{|I|−dim W}。每个非空纤维为同维仿射空间，故完成数 q^{|I|−dim(W+U_A)}。相除给坐标像大小 q^{dim(W+U_A)−dim W}，指数亦为 |A|−dim(W∩U_A)。S1 的拼接判据保证这不是仅上界而是实际像，所有纤维平移同一个核，空 A 时像只有空记录。

判准：三个计数；零维和空坐标。

## S3 有限域的无限坐标拓扑

判定：true。

有限离散 k 紧 Hausdorff，Tychonoff 给 k^I 紧，有限支撑使每个方程的零集闭；有限可解给有限交性质，故全解非空紧。坐标柱状开闭集（如 x_i=c 与其补集）分离点，子空间全不连通。坐标像是紧到 Hausdorff 的像所以闭。给 y，加入 x_i=y_i(i∈A) 的闭约束；所述有限同时实现正是这族闭集的有限交性质，紧性给共同解。必要性由全解限制直接得。

判准：真正紧性及有限交性质；坐标像精确有限可实现判据。

## S4 整体对象与全部恢复目标

判定：true。

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

判准：Prove an actual global solution for arbitrary sets I and J and an arbitrary field under the given finite-subsystem solvability assumption.；Give a noncircular algebraic classification of every global solution using data determined by the supplied rows and constants.；For every coordinate subset A, give and prove an exact description of the image of the original restriction map and all its nonempty fibers, with actual corresponding constructions.。

## S5 赋值空间的支持

判定：false。

否。取第 j 行 x_j=1。任意有限 F 用其特征向量得到有限支撑解；全解只能是恒 1 序列，因 1≠0 而无限支撑。它是 k^N 的合法解，故并不反驳 S4；结论失效源于目标赋值空间已改变。

判准：全部有限子系统；原范围 k^I 与新范围 k^(I) 区分。

## S6 无限域的坐标像

判定：true。

成立。用 S4 的 T、B、V_A 记号，像恰由全部关系 Tλ=ι_Az 所给方程 Σ_{i∈A}z_i y_i=Bλ 定义；z 有限支撑，每个等式是有限坐标连续映射到离散 k 的一个闭纤维，任意交闭。这里不需要 k^I 紧；有限域的紧像论证不适用于无限域，但代数消元判据仍给同一闭性。

判准：有限坐标闭方程；充分性依靠真实代数延拓。
