记 \(b=\sum_{i=1}^r\binom{n_i}{2}\)，并令 \(q_F=2\)、\(q_{K_{-1}}=q_{K_2}=4\)。对 \(a\in I_i\)，定义
\[
h_a=\sum_{c\notin I_i}\frac{(A_i)_{ca}}2\pmod 2.
\]
这些条目都能由 \(A_i\bmod4\) 算出。令 \(\chi=1\) 当且仅当
\[
\boxed{\quad \sum_{a\in I_i}h_a=0\quad\text{于 }\mathbb F_2,\qquad 1\le i\le r.\quad} \tag{1}
\]
其余情形令 \(\chi=0\)。

## 1. 可行性、基数与真解提升

对三个 \(L\)，均有 \(\mathscr S_L(A)\ne\varnothing\) 当且仅当 \(\chi=1\)。有限集合的基数为
\[
\boxed{
\begin{aligned}
|\mathscr R_{L,M}(A)|&=\chi\,2^r q_L^{(M-1)b},\\
|\mathscr C_{L,2}(A)|&=q_L^{b+d},\\
|\mathscr C_{L,M}(A)|&=\chi\,2^r q_L^{(M-1)b+d}\qquad(M\ge3).
\end{aligned}} \tag{2}
\]
特别地，\(\mathscr C_{L,2}(A)\) 总是非空。

对任意 \(\bar U\in\mathscr C_{L,M}(A)\)，取任意整数环矩阵提升 \(\widetilde U\)，定义
\[
\Delta_{L,M}(\bar U)
=\frac{\operatorname{diag}(\widetilde U^{\mathsf T}\widetilde U-I_d)}{2^M}
 \pmod{2\mathcal O_L}.
\]
这里 \(\operatorname{diag}\) 取对角向量。改变提升时，每列平方和的变化均被 \(2^{M+1}\) 整除，因此 \(\Delta_{L,M}\) 定义良好。提升判准是
\[
\boxed{\quad \bar U\in\mathscr R_{L,M}(A)
\quad\Longleftrightarrow\quad \Delta_{L,M}(\bar U)=0.\quad} \tag{3}
\]
也就是用任意提升检查每列平方和是否模 \(2^{M+1}\) 等于 \(1\)。

### 分块化简

令 \(f(x)=3x^2-2x^3\)。多项式 \(f(x)-x\) 被 \(x^2-x\) 整除，且 \(f(x)^2-f(x)\) 被 \((x^2-x)^2\) 整除。因此迭代 \(f\) 得到极限
\[
P_i=\lim_{m\to\infty} f^{\circ m}(A_i),\qquad
P_i^2=P_i,\qquad P_i\equiv E_i\pmod2.
\]
这些矩阵对称，彼此交换，并与每个 \(A_j\) 交换。对 \(i\ne j\)，\(P_iP_j\) 是模 \(2\) 为零的幂等矩阵，故为零。事实上，幂等矩阵若被 \(2^k\) 整除，也被 \(2^{2k}\) 整除。同理，\(\sum_iP_i\) 是模 \(2\) 为 \(I_d\) 的幂等矩阵，故等于 \(I_d\)。

令 \(B\) 的第 \(a\) 列为 \(P_i e_a\)，其中 \(a\in I_i\)。则
\[
B\equiv I_d\pmod2,\qquad P_iB=BE_i,\qquad
G=B^{\mathsf T}B=\bigoplus_i G_i,\qquad G_i=(P_i)_{I_i,I_i}.
\]
记 \(D_i=(P_i)_{I_i^c,I_i}\)。由 \(P_i^2=P_i\) 得
\[
G_i^2+D_i^{\mathsf T}D_i=G_i.
\]
由于 \(G_i\equiv I_{n_i}\pmod2\) 且 \(D_i\equiv0\pmod2\)，有 \(G_i\equiv I_{n_i}\pmod4\)，并且
\[
\frac{G_i-I_{n_i}}4\equiv -(D_i/2)^{\mathsf T}(D_i/2)\pmod2.
\]
另一方面，\(P_i\equiv f(A_i)\equiv A_i^2\pmod4\)。将 \(A_i=E_i+2Z\) 代入 \(A_i^2\)，可见 \(A_i^2\) 与 \(A_i\) 在 \(I_i^c\times I_i\) 上模 \(4\) 相等。因此 \((G-I_d)/4\) 的对角向量模 \(2\) 正是 \(h=(h_a)_a\)。

在整数环上和每个有限商环上，若 \(U\equiv I_d\pmod2\) 且 \(U^{\mathsf T}U=I_d\)，则原题的分块方程等价于
\[
P_iU=UE_i\qquad(\forall i). \tag{4}
\]
事实上，若 \(U^{-1}A_iU\) 分块对角，则由多项式迭代，\(U^{-1}P_iU\) 也分块对角。它的各块都是模 \(2\) 为 \(0\) 或 \(I\) 的幂等矩阵，故 \(U^{-1}P_iU=E_i\)。逆向由 \(A_i\) 与所有 \(P_j\) 交换得到。于是令 \(U=BT\)，原条件就化为
\[
T\ \text{分块对角},\qquad T\equiv I_d\pmod2,\qquad T^{\mathsf T}GT=I_d. \tag{5}
\]

### 提升与计数

设 \(k\ge2\)，取 \(T\) 的分块对角提升，并记 \(Q=T^{\mathsf T}GT\equiv I_d\pmod{2^k}\)。它在下一层的所有分块对角提升可唯一写成
\(T(I_d+2^k Z)\bmod2^{k+1}\)，其中 \(Z\bmod2\) 分块对角。新 Gram 矩阵为
\[
Q+2^k(Z^{\mathsf T}Q+QZ)+2^{2k}Z^{\mathsf T}QZ.
\]
其对角模 \(2^{k+1}\) 不变，所以能升到 \(\mathscr C_{L,k+1}\) 必须有 \(\Delta_{L,k}=0\)。在这个条件下，达到 \(\mathscr C_{L,k+1}\) 只需对同一块的每对 \(a<c\) 解
\[
Z_{ac}+Z_{ca}\equiv -Q_{ac}/2^k\pmod2.
\]
每对有 \(q_L\) 种选择，对角条目各有 \(q_L\) 种选择。若再要求新对角模 \(2^{k+2}\) 等于 \(1\)，则每个对角条目由
\[
Z_{aa}\equiv -(Q_{aa}-1)/2^{k+1}\pmod2
\]
唯一确定。这里 \(2k\ge k+2\)，所以二次项在该对角条件中消失。逐层选取满足这两组条件的提升，由完备性得到满足 (5) 的真正解。这证明了 (3)，也证明了普通约化的像与纤维大小。

在精度 \(2\)，写 \(T=I_d+2Z\bmod4\)。因为 \(G\equiv I_d\pmod4\)，条件恰为 \(Z\bmod2\) 分块对角且对称，所以 \(|\mathscr C_{L,2}|=q_L^{b+d}\)。此时
\[
\Delta_{L,2}(BT)_a=h_a+Z_{aa}+\sum_c Z_{ca}^2
\quad\text{于 }\mathcal O_L/2\mathcal O_L. \tag{6}
\]
设 \(\mathcal Y\) 为分块对角的对称二元矩阵空间，\(\mathcal Y_0\) 为其对角为零的子空间。定义 \(\partial Y\) 为 \(Y\) 的列和向量，其中 \(Y\in\mathcal Y_0\)。块内每个非对角位置对 \(\partial\) 贡献一个 \(e_a+e_c\)，这些向量张成该块坐标和为零的空间。因此 \(\partial\) 的秩为 \(d-r\)。

基域上，(6) 等于 \(h\) 加上 \(Z\) 去掉对角后的列和。扩域上，置
\[
\pi_{-1}=1+\theta_{-1},\qquad \pi_2=\theta_2.
\]
有 \(\mathcal O_\mu/2\mathcal O_\mu=\mathbb F_2[\varepsilon]/(\varepsilon^2)\)，其中 \(\varepsilon\) 是 \(\pi_\mu\) 的像。写 \(Z=Z_0+\varepsilon Z_1\)，则 (6) 的常数项仍是 \(h\) 加上 \(Z_0\) 去掉对角后的列和，\(\varepsilon\) 项是 \(Z_1\) 的对角。因此三个域上有解的条件都是 (1)。可行时 \(Z_0\) 有 \(2^{b-d+r}\) 种非对角选择和 \(2^d\) 种对角选择，扩域上的 \(Z_1\) 另有 \(2^b\) 种选择。由 (3) 得 \(|\mathscr R_{L,2}|=2^r q_L^b\)。此后每个 \(\mathscr R_{L,k}\) 类有 \(q_L^b\) 个 \(\mathscr R_{L,k+1}\) 提升和 \(q_L^{b+d}\) 个 \(\mathscr C_{L,k+1}\) 提升，得到 (2)。

## 2. 固定矩阵类、轨道与约化

固定 \(\mu\)，写 \(\theta=\theta_\mu\)、\(\sigma=\sigma_\mu\)。由于 \(1,\theta\) 是整数环的 \(\mathbb Z_2\)-基，任意固定矩阵类唯一写成
\[
X+2^{M-1}\theta Y,\qquad
X\in M_d(\mathbb Z_2/2^M\mathbb Z_2),\quad Y\in M_d(\mathbb F_2). \tag{7}
\]
事实上，\(\sigma-1\) 将 \(\theta\) 的系数乘以 \(-2\theta\)，所以固定恰好要求该系数被 \(2^{M-1}\) 整除。

固定的方程解为
\[
\boxed{\displaystyle
\mathscr C_{K_\mu,M}(A)^\sigma
=\{X+2^{M-1}\theta Y:X\in\mathscr C_{F,M}(A),\ Y\in\mathcal Y\}.} \tag{8}
\]
证明时，将 (7) 代入 (4)，比较系数得到 \(P_iX=XE_i\bmod2^M\) 和 \(E_iY=YE_i\bmod2\)。再展开正交方程。二次项被 \(2^{2M-2}\) 整除，故模 \(2^M\) 消失。由 \(X\equiv I_d\pmod2\)，\(\theta\) 项要求 \(Y+Y^{\mathsf T}=0\bmod2\)，常数项要求 \(X^{\mathsf T}X=I_d\bmod2^M\)。这些条件正好给出 (8)。

令 \(\kappa_{\mu,M}=1\) 当 \((\mu,M)=(-1,2)\)，其余情形为 \(0\)。固定的真解约化类为
\[
\boxed{\displaystyle
\mathscr R_{K_\mu,M}(A)^\sigma
=\{X+2^{M-1}\theta Y:X\in\mathscr C_{F,M}(A),\
Y\in\mathcal Y_0,\ \Delta_{F,M}(X)=\kappa_{\mu,M}\partial Y\}.} \tag{9}
\]
为证此式，把 (7) 的每列平方和展开到模 \(2^{M+1}\)。除以 \(2^M\) 后，第 \(a\) 个对角缺陷为
\[
\Delta_{F,M}(X)_a+\theta Y_{aa}
       +\kappa_{\mu,M}\sum_cY_{ca}
       \pmod{2\mathcal O_\mu}.
\]
二次项在除法后带有因子 \(2^{M-2}\mu\)，恰在 \((\mu,M)=(-1,2)\) 时保留。比较 \(1,\theta\) 的系数，再用 (3)，即得 (9)。

因此，(8) 和 (9) 中 \(Y=0\) 的类分别恰是 \(\mathscr C_{F,M}(A)\) 和 \(\mathscr R_{F,M}(A)\)。当 \(\mathscr C_{F,M}(A)\) 非空时，它在 (8) 中是真子集。当 \(\chi=1\) 时，\(\mathscr R_{F,M}(A)\) 在 (9) 中是真子集当且仅当 \(b>0\)。除 \((-1,2)\) 外，(9) 的常数项恰遍历 \(\mathscr R_{F,M}(A)\)。在 \((-1,2)\) 且 \(\chi=1\) 时，由 (6)，每个 \(X\in\mathscr C_{F,2}(A)\) 的缺陷都在 \(\partial\) 的像中，所以每个这样的 \(X\) 都出现，且恰配有 \(2^{b-d+r}\) 个 \(Y\)。

固定点数和作用在整个相应集合上的轨道数如下。每个非固定点与其共轭组成一个二元轨道。
\[
\begin{array}{c|c|c}
\text{集合}&\text{固定点数}&\langle\sigma\rangle\text{ 的轨道数}\\ \hline
\mathscr R_{K_\mu,M}
 &\chi\,2^{r+Mb}
 &\dfrac{\chi}{2}\bigl(2^{r+2(M-1)b}+2^{r+Mb}\bigr)\\[2pt]
\mathscr C_{K_\mu,2}
 &2^{2(b+d)}
 &2^{2(b+d)}\\[2pt]
\mathscr C_{K_\mu,M},\ M\ge3
 &\chi\,2^{r+Mb+2d}
 &\dfrac{\chi}{2}\bigl(2^{r+2(M-1)b+2d}+2^{r+Mb+2d}\bigr)
\end{array} \tag{10}
\]
其中 (8) 的每个 \(X\) 配有 \(2^{b+d}\) 个 \(Y\)。对于 (9)，可行时每个 \(Y\in\mathcal Y_0\) 都配有 \(|\mathscr R_{F,M}|\) 个 \(X\)。在例外情形，这个计数由 (6) 给出，因为把 \(h\) 改成 \(h+\partial Y\) 后，列和方程的解数相同。

### 约化的像和纤维

下表中每行的目标都是同一族在精度 \(M\) 的集合。像外的纤维全为空。
\[
\begin{array}{c|c|c}
\text{精度 }M+1\text{ 的来源}&\text{约化像}&\text{每个非空纤维的大小}\\ \hline
\mathscr R_{L,M+1}(A)&\mathscr R_{L,M}(A)&q_L^b\\
\mathscr C_{L,M+1}(A)&\mathscr R_{L,M}(A)&q_L^{b+d}\\
\mathscr R_{K_\mu,M+1}(A)^\sigma&\mathscr R_{F,M}(A)&2^{2b}\\
\mathscr C_{K_\mu,M+1}(A)^\sigma&\mathscr R_{F,M}(A)&2^{2(b+d)}
\end{array} \tag{11}
\]
前两行已由 (5) 的逐层校正证明。对后两行，精度 \(M+1\) 的固定类在约化时丢掉 \(2^M\theta Y\) 项，其常数项属于 \(\mathscr C_{F,M+1}(A)\)，故约化属于 \(\mathscr R_{F,M}(A)\)。反之，任何 \(\mathscr R_{F,M}(A)\) 类都来自基域真解，所以在下一层有固定提升。事实上，在 \(K_\mu\) 上，基域矩阵类的任何下一层提升都固定，因为其 \(\theta\) 系数被 \(2^M\) 整除。故后两行的纤维大小直接由前两行取 \(q_L=4\) 得到。

一个固定矩阵类能提升为 \(\sigma\)-固定真解，当且仅当它属于 \(\mathscr R_{F,M}(A)\)。用 (7) 表示，这要求 \(Y=0\) 且 \(\Delta_{F,M}(X)=0\)。若该类已在 \(\mathscr R_{K_\mu,M}(A)^\sigma\) 中，只需检查 \(Y=0\)。这也是它能作为一条逐层相容的固定 \(\mathscr R\) 序列或固定 \(\mathscr C\) 序列的精度 \(M\) 分量的充要条件。必要性由下一层和 (11) 得到，充分性由基域真解在各层的约化得到。每条这样的无限相容序列也唯一确定一个基域真解，因为各层都是基域矩阵类，且其极限满足所有方程。

## 3. 最佳下降精度与实例

所求最大整数为
\[
\boxed{\displaystyle
N_{\max}=
\begin{cases}
M,& n_1=\cdots=n_r=1,\\
M-1,& \text{至少一块的秩大于 }1.
\end{cases}} \tag{12}
\]
对给定的 \(A,U\)，将 \(U=X+\theta Z\) 写成 \(X,Z\in M_d(\mathbb Z_2)\)。达到 \(N=M\) 的充要条件为
\[
\boxed{\displaystyle
Z\equiv0\pmod{2^M}
\quad\Longleftrightarrow\quad
\sigma(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}.} \tag{13}
\]
事实上，给定的近似固定条件保证 \(U\bmod2^M\) 属于固定的 \(\mathscr R\)。由 (9)，这个类来自基域真解当且仅当它的 \(Y=0\)，即 \(2^M\mid Z\)。右侧等价式直接由 \(\sigma(U)-U=-2\theta Z\) 比较基底系数得到。

当 \(M\ge3\)，用 (11) 将 \(U\bmod2^M\) 约化一层，即得基域真解在精度 \(M-1\) 的类。当 \(M=2\)，扩域真解的存在保证基域可行，且任取基域真解都与 \(U\) 模 \(2\) 相等。若所有块秩都是 \(1\)，还有真正的等式 \(\mathscr S_{K_\mu}(A)=\mathscr S_F(A)\)。可行时取 \(W_0\in\mathscr S_F(A)\)。由 (4)，任一扩域真解 \(U\) 的 \(W_0^{-1}U\) 分块对角且正交，每个一维块只能取 \(1\) 或 \(-1\)，故 \(U\) 本身就在基域上。不可行时两集合皆空。

### 任意精度的最优性实例

取 \(A_i=E_i\)，并在同一块内选取两个坐标。对每个 \(m\ge2\)，令
\[
t=2^{m-2}\pi_\mu,\qquad
Q_m=\frac1{1+t^2}
\begin{pmatrix}1-t^2&2t\\-2t&1-t^2\end{pmatrix},
\]
在所选两坐标上用 \(Q_m\)，其余坐标用恒等，得到 \(U_m\)。因为 \(\pi_\mu^2\in2\mathcal O_\mu\)，分母可逆，且直接计算得 \(Q_m^{\mathsf T}Q_m=I_2\)。又因为 \(t^2\in2^{2m-3}\mathcal O_\mu\)，
\[
Q_m\equiv I_2+2^{m-1}\pi_\mu
\begin{pmatrix}0&1\\1&0\end{pmatrix}
\pmod{2^m\mathcal O_\mu}.
\]
所以 \(U_m\) 是扩域真解，模 \(2^m\) 固定，而非对角条目的 \(\theta_\mu\) 系数恰被 \(2^{m-1}\) 整除。取 \(m=M\)，由 (13) 排除精度 \(M\) 的下降，证明 (12) 最优。这个固定类也没有下一层固定提升。对于 \(M\ge3\)，取 \(m=M-1\) 并约化到精度 \(M\)，则得到一个二元轨道。在 \(K_{-1}\) 的精度 \(2\)，\(U_2\) 的常数项在所选平面上是 \(\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)\bmod4\)，两列平方和均为 \(5\bmod8\)。这实际实现了 (9) 中常数项属于 \(\mathscr C_{F,2}\) 而无法提升成基域真解的情形。

### 空集和不可提升的实例

- 若 \(r\ge2\)，在两个不同块内各取一个坐标。在这两个坐标张成的平面上令
  \[
  A_1=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix},\qquad
  A_2=I_2-A_1,
  \]
  其中所选坐标分别属于 \(I_1,I_2\)，其余 \(A_i\) 在此平面上为零。在补空间上仍取 \(A_i=E_i\)。这些矩阵是合法的交换对称投影，两个所选块在 (1) 中的和均为 \(1\)。此时三个域都不可行。矩阵 \(B\bmod4\) 仍给出一个固定的 \(\mathscr C_{K_\mu,2}\) 类和一个 \(\mathscr C_{F,2}\) 类。它在该平面上的 Gram 矩阵是 \(I_2/5\)，所以连模 \(8\) 的方程解也无法提升到。

- 取 \(A_i=E_i\)。对每个 \(M\ge3\)，把恒等矩阵的一个对角元改成 \(1+2^{M-1}\)，得到基域上的 \(\mathscr C_{F,M}\) 类。该列平方和模 \(2^{M+1}\) 为 \(1+2^M\)，故此类在三个域上都没有下一层提升。在 \(M=2\) 且 \(b>0\) 时，可改取同一块内 \(I_2+2\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)\) 并在其余坐标用恒等。它模 \(4\) 满足方程，两列平方和均为 \(5\bmod8\)，也没有下一层提升。

- 取 \(A_i=E_i\)。在任一扩域和任意 \(M\ge2\)，把恒等矩阵的一个对角元改成 \(1+2^{M-1}\theta_\mu\)。所得类属于 \(\mathscr C_{K_\mu,M}^\sigma\)，且其 \(Y\) 非零，所以它在基域矩阵类之外。该列平方和的缺陷在除以 \(2^M\) 后仍有非零的 \(\theta_\mu\) 系数，故它没有真解提升，也没有下一层方程解提升。