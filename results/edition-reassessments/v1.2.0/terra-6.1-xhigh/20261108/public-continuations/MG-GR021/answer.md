令
\[
t=\sum_{i=1}^r\binom{n_i}{2},\qquad
s=\sum_{i=1}^r\frac{n_i(n_i+1)}2=t+d,
\]
并定义
\[
\varepsilon_i=
\sum_{\substack{a\in I_i\\ b\notin I_i}}
\frac{(A_i)_{ba}}2\pmod2,\qquad
\delta=
\begin{cases}
1,&\varepsilon_i=0\quad(\forall i),\\
0,&\text{否则}.
\end{cases}
\]
以下所有公式均适用于题目给定的全部输入。特别地，\(\delta\) 由 \(A_i\bmod4\) 有限计算。

记
\[
q_F=2,\qquad q_{K_{-1}}=q_{K_2}=4.
\]
另外，把 \(\mathbb F_2\) 上按指定块分块的对称矩阵和交错矩阵空间分别记为
\[
\operatorname{Sym}_{\rm bl},\qquad \operatorname{Alt}_{\rm bl}.
\]
这里交错矩阵指对称且对角线为零的矩阵；它们的维数分别为 \(s,t\)。

## 一、可行性、计数和真正可提升性

三个域上的真正解同时存在或同时不存在：
\[
\boxed{\mathscr S_L(A)\ne\varnothing\iff\delta=1.}
\]

真正解的约化像和有限精度解的基数为
\[
\boxed{\displaystyle
|\mathscr R_{L,M}(A)|
=\delta\,2^r q_L^{\,t(M-1)}}
\]
以及
\[
\boxed{\displaystyle
|\mathscr C_{L,M}(A)|=
\begin{cases}
q_L^s,&M=2,\\[1mm]
\delta\,2^r q_L^{\,s+t(M-2)},&M\ge3.
\end{cases}}
\]
因此 \(\mathscr C_{L,2}(A)\) 总非空；当 \(M\ge3\) 时，它在且仅在 \(\delta=1\) 时非空。

给定 \(\bar U\in\mathscr C_{L,M}(A)\)，任选其整数环矩阵提升 \(\widetilde U\)。则
\[
\boxed{\displaystyle
\bar U\in\mathscr R_{L,M}(A)
\iff
\sum_{a=1}^d \widetilde U_{aj}^{\,2}
\equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(j=1,\ldots,d).}
\tag{1}
\]
此条件与提升的选择无关，因而可直接有限计算。它不仅必要，而且包括了所有更高精度的提升障碍。

## 二、固定矩阵类、轨道和逐层约化

将 \(K_\mu\) 省记为 \(K\)。每个 \(\sigma_\mu\)-固定的矩阵类都唯一写成
\[
B+2^{M-1}\theta_\mu C,
\]
其中 \(B\) 的条目在 \(\mathbb Z_2/2^M\)，而 \(C\) 的条目在 \(\mathbb F_2\)。具体地，
\[
\boxed{\displaystyle
\mathscr C_{K,M}(A)^{\sigma_\mu}
=
\left\{B+2^{M-1}\theta_\mu C:
B\in\mathscr C_{F,M}(A),\
C\in\operatorname{Sym}_{\rm bl}\right\}.}
\tag{2}
\]
这个公式也适用于 \(\delta=0,M=2\)。

当 \(M\ge3\) 时，真正解约化像的固定点为
\[
\boxed{\displaystyle
\mathscr R_{K,M}(A)^{\sigma_\mu}
=
\left\{B+2^{M-1}\theta_\mu C:
B\in\mathscr R_{F,M}(A),\
C\in\operatorname{Alt}_{\rm bl}\right\}.}
\tag{3}
\]

精度 \(M=2\) 时，整个 \(\mathscr R_{K,2}(A)\) 都被固定；其具体描述如下。若 \(\delta=1\)，取下文构造的 \(T\in\mathscr S_F(A)\)。对于式 (2) 中的矩阵，唯一写
\[
T^{-1}B=\operatorname{diag}(I_{n_i}+2x_i)\pmod4,
\qquad C=\operatorname{diag}(y_i),
\]
其中 \(x_i,y_i\) 是 \(\mathbb F_2\) 上的对称矩阵。那么它属于 \(\mathscr R_{K_\mu,2}(A)\) 当且仅当每个 \(y_i\) 的对角线为零，且对每个块及其每个顶点 \(a\)，有
\[
\begin{cases}
\displaystyle\sum_{b\ne a}(x_i)_{ba}=0,&\mu=2,\\[2mm]
\displaystyle\sum_{b\ne a}\bigl((x_i)_{ba}+(y_i)_{ba}\bigr)=0,
&\mu=-1.
\end{cases}
\tag{4}
\]
若 \(\delta=0\)，则 \(\mathscr R_{K,2}(A)=\varnothing\)。

固定点数因而为
\[
\boxed{\begin{aligned}
|\mathscr C_{K,M}(A)^{\sigma_\mu}|
 &=2^s|\mathscr C_{F,M}(A)|,\\
|\mathscr R_{K,M}(A)^{\sigma_\mu}|
 &=\delta\,2^{r+tM}.
\end{aligned}}
\tag{5}
\]
每个集合的 \(\langle\sigma_\mu\rangle\) 轨道数由 Burnside 公式明确给出：
\[
\boxed{\displaystyle
\#(\mathscr X/\langle\sigma_\mu\rangle)
=\frac{|\mathscr X|+|\mathscr X^{\sigma_\mu}|}{2},
\quad \mathscr X=\mathscr R_{K,M}(A)\ \text{或}\ \mathscr C_{K,M}(A),}
\tag{6}
\]
其中代入前述闭式即可。

基域集合与扩域集合的关系还有
\[
\mathscr C_{K,M}(A)\cap M_d(\mathbb Z_2/2^M)
=\mathscr C_{F,M}(A),
\qquad
\mathscr R_{K,M}(A)\cap M_d(\mathbb Z_2/2^M)
=\mathscr R_{F,M}(A).
\tag{7}
\]

假设 \(\delta=1\)。从 \(M+1\) 到 \(M\) 的约化像及每个非空纤维大小如下：
\[
\begin{array}{c|c|c}
\text{集合}&\text{约化像}&\text{每个非空纤维大小}\\ \hline
\mathscr R_{L,M+1}(A)&\mathscr R_{L,M}(A)&q_L^t\\
\mathscr C_{L,M+1}(A)&\mathscr R_{L,M}(A)&q_L^s\\
\mathscr R_{K,M+1}(A)^{\sigma_\mu}
 &\mathscr R_{F,M}(A)&2^{2t}\\
\mathscr C_{K,M+1}(A)^{\sigma_\mu}
 &\mathscr R_{F,M}(A)&2^{2s}
\end{array}
\tag{8}
\]
表中基域集合均经自然包含视为扩域上的矩阵类。

若 \(\delta=0\)，所有 \(\mathscr R\) 以及 \(M\ge3\) 的所有 \(\mathscr C\) 均为空；唯一非空的 \(\mathscr C_{L,2}\) 和其固定点集从精度 \(3\) 得到的约化像为空。

对于任一个固定的矩阵类，无论它属于 \(\mathscr R_{K,M}^{\sigma_\mu}\) 还是 \(\mathscr C_{K,M}^{\sigma_\mu}\)，以下条件等价：

1. 它能提升为一个 \(\sigma_\mu\)-固定的真正解；
2. 它能作为一条从精度 \(M\) 起逐层相容的固定矩阵类序列的第 \(M\) 项；
3. 它属于自然嵌入的 \(\mathscr R_{F,M}(A)\)。

## 三、最优下降精度

题目第 3 问的最大整数为
\[
\boxed{\displaystyle
N=
\begin{cases}
M,&n_i=1\quad(\forall i),\\
M-1,&\text{至少一个 }n_i\ge2.
\end{cases}}
\tag{9}
\]
若所有块秩均为 1，则事实上每个扩域真正解都在基域上，可以精确下降。

对于给定的满足固定模 \(2^M\) 条件的 \(U\)，唯一写
\[
U=X+\theta_\mu Y,\qquad X,Y\in M_d(\mathbb Z_2).
\]
存在 \(W\in\mathscr S_F(A)\) 满足 \(U\equiv W\pmod{2^M\mathcal O_\mu}\) 的充要条件为
\[
\boxed{Y\equiv0\pmod{2^M}.}
\tag{10}
\]

## 四、证明：谱分解与可行性

由特征多项式的 Hensel 分解，\(A_i\) 有对应模 2 特征值 1 的谱投影 \(P_i\)，满足
\[
P_i^2=P_i,\qquad P_i^{\mathsf T}=P_i,\qquad P_i\equiv E_i\pmod2.
\]
这些投影可取为相应 \(A_i\) 的多项式，所以彼此可交换。对 \(i\ne j\)，\(P_iP_j\) 是模 2 为零的幂等矩阵，故为零；同理 \(\sum_iP_i=I_d\)。于是
\[
\mathbb Z_2^d=\bigoplus_i H_i,\qquad H_i=P_i\mathbb Z_2^d,
\]
是正交直和，各 \(H_i\) 对全部 \(A_j\) 不变。

把 \(H_i\) 表为从第 \(i\) 坐标块到其余坐标的图，图矩阵为 \(D_i\)。由谱投影方程计算非对角块，得到
\[
D_i\equiv (A_i)_{I_i^c,I_i}\pmod4.
\]
图基的 Gram 矩阵
\[
G_i=I_{n_i}+D_i^{\mathsf T}D_i
\]
因而满足
\[
\det G_i\equiv1+4\varepsilon_i\pmod8.
\tag{11}
\]

若存在模 2 为标准基的正交归一基，其块内变换矩阵 \(C_i\equiv I\pmod2\)，且
\(C_i^{\mathsf T}G_iC_i=I\)。写 \(\det C_i=1+2x\)，由行列式模 8 得
\[
\varepsilon_i+x+x^2\equiv0\pmod{2\mathcal O_L}.
\]
题中三个整数环的剩余域均为 \(\mathbb F_2\)，所以把上式再约化到剩余域得到 \(\varepsilon_i=0\)。

反之，若 \(\varepsilon_i=0\)，则 \(G_i\) 的对角元中模 8 等于 5 的位置有偶数个。将它们配对，对每对用 \(I+2S\) 换基，其中 \(S\) 的该对对称非对角元为 1，其余为零。所得 Gram 矩阵的对角元均为 \(1\bmod8\)，非对角元均被 4 整除。随后进行 Gram–Schmidt 正交化；对角元仍为 \(1\bmod8\)，而每个这样的 \(\mathbb Z_2\) 单位均为平方。将各块合并，得到
\[
T\in\mathscr S_F(A).
\]

任何真正解必须把第 \(i\) 标准块送入 \(H_i\)：分块条件使全部谱投影在变换后分块，而这些幂等块模 2 分别为零或单位矩阵，故只能是相应标准投影。因此
\[
\mathscr S_L(A)
=T\prod_{i=1}^r
\left\{V_i\in\operatorname{GL}_{n_i}(\mathcal O_L):
V_i^{\mathsf T}V_i=I,\ V_i\equiv I\pmod2\right\}.
\tag{12}
\]

## 五、证明：有限精度提升与计数

先说明一个提升引理。设 \(V\equiv I\pmod2\) 的列已落在相应 \(H_i\) 中，且
\[
V^{\mathsf T}V\equiv I\pmod{2^m},\qquad
(V^{\mathsf T}V)_{jj}\equiv1\pmod{2^{m+1}},
\quad m\ge2.
\]
可取分块矩阵 \(H\)，令
\[
V'=V(I+2^mH),
\]
使同样两式的精度均提高一位。事实上，模 \(2^{m+1}\) 时，非对角误差可用 \(H+H^{\mathsf T}\) 消去；对角误差已为零。然后利用 \(H\) 的自由对角元，使列范数模 \(2^{m+2}\) 也正确。二次项 \(2^{2m}H^{\mathsf T}V^{\mathsf T}VH\) 被 \(2^{m+2}\) 整除。迭代并取完备极限，就得到真正解。

若 \(\bar U\in\mathscr C_{L,M}(A)\)，谱投影的唯一性允许先选取一个列严格落在各 \(H_i\) 中的整数提升。应用上述引理，便证明了判准 (1)。它也表明 \(\mathscr C_{L,M+1}\) 的约化像恰为 \(\mathscr R_{L,M}\)，并由真正解的存在性推出所有 \(M\ge3\) 的有限精度非空条件。

当 \(M=2\) 时，不要求 \(\delta=1\)。令 \(T_0\) 的第 \(a\in I_i\) 列为 \(P_i e_a\)。则
\[
T_0\equiv I\pmod2,\qquad T_0^{\mathsf T}T_0\equiv I\pmod4,
\]
且其列已按 \(H_i\) 分块。故
\[
\mathscr C_{L,2}(A)
=T_0\operatorname{diag}(I+2X_i)\pmod4,
\qquad X_i^{\mathsf T}=X_i\quad\text{在 }\mathcal O_L/2.
\]
这给出 \(|\mathscr C_{L,2}|=q_L^s\)。

为计算 \(\mathscr R_{L,2}\)，假设 \(\delta=1\)，并用 \(T\) 化到块内。对单个秩 \(n\) 块写 \(V=I+2X\)。除了 \(X\) 对称，式 (1) 给出
\[
X_{jj}+\sum_k X_{kj}^2=0
\quad\text{在 }\mathcal O_L/2.
\tag{13}
\]
对于 \(F\)，这些条件说非对角元构成的完全图中每个顶点度数为偶数；独立条件有 \(n-1\) 个，对角元有 \(n\) 个自由位。故该块有
\(2^{1+\binom n2}\) 个类。

对于两个二次扩域，\(\mathcal O_K/2\) 是四元环
\(\mathbb F_2[\epsilon]/(\epsilon^2)\)。式 (13) 要求每个对角元的 \(\epsilon\) 系数为零，并要求非对角元的剩余域部分构成偶度图；非对角元的 \(\epsilon\) 系数自由。因此该块有
\(2^{1+2\binom n2}\) 个类。统一写作 \(2q_L^{\binom n2}\)，各块相乘得到
\[
|\mathscr R_{L,2}|=\delta\,2^r q_L^t.
\]

提升引理还给出每个真正解类向上一层的 \(q_L^t\) 个选择：新一层修正矩阵的非对角部分可任意取对称值，对角部分由下一位的列范数唯一决定。有限精度解向上一层的非空纤维则有 \(q_L^s\) 个选择，因为修正矩阵可以是任意对称矩阵。这证明第一节的全部计数及表 (8) 的前两行。

## 六、证明：固定点和下降

由于 \(\mathcal O_K=\mathbb Z_2\oplus\theta_\mu\mathbb Z_2\)，矩阵类被共轭固定当且仅当其 \(\theta_\mu\) 系数被 \(2^{M-1}\) 整除。将
\[
B+2^{M-1}\theta_\mu C
\]
代入正交与分块方程，可见 \(B\) 必须是基域有限精度解，\(C\) 必须按指定块分块且对称；反之这些条件充分。这证明 (2)。

对真正解约化像再使用式 (1)。当 \(M\ge3\)，\(\theta_\mu^2C^{\mathsf T}C\) 项在所需精度下消失，而混合项要求 \(C\) 对角线为零；基域部分则必须属于 \(\mathscr R_{F,M}\)。这得到 (3)。

当 \(M=2\)，把 \(T^{-1}B=I+2x\) 和 \(C=y\) 代入式 (13)。在 \(\mu=2\) 时，\(\theta_2^2=0\) 于模 2 环中；在 \(\mu=-1\) 时，\(\theta_{-1}^2=1\) 于模 2 环中。分别比较 \(1,\theta_\mu\) 系数，恰得到式 (4)。其计数与 \(\mathscr R_{K,2}\) 的计数相同，故该层全部真正解类均被固定。由此得到式 (5)，式 (6) 是二元群的轨道计数公式。

固定类从精度 \(M+1\) 约化到 \(M\) 时，其 \(\theta_\mu\) 项消失。结合 (2)、(3)、(4) 和基域的提升引理，约化像恰为 \(\mathscr R_{F,M}\)。按式 (5) 和基域计数取商，得到表 (8) 的后两行。一个固定类若有更高一层的固定提升，就已在 \(\mathscr R_{F,M}\)；反过来，基域真正解提供全部更高层及固定的真正提升。这也证明了第二节末尾的三个条件等价。

现在证明下降精度。若存在给定的扩域真正解，则 \(\delta=1\)，可用 \(T\) 化为块对角正交矩阵。写
\[
T^{-1}U=X+\theta_\mu Y.
\]
固定模 \(2^M\) 等价于 \(Y\equiv0\pmod{2^{M-1}}\)，正交关系的有理部分为
\[
X^{\mathsf T}X=I-\mu Y^{\mathsf T}Y.
\]
当 \(M\ge3\)，二项级数收敛，令
\[
W_0=X(X^{\mathsf T}X)^{-1/2}.
\]
则 \(W_0\) 是基域块对角正交矩阵，且
\[
W_0\equiv X\pmod{2^{2M-3}}.
\]
故 \(TW_0\) 给出模 \(2^{M-1}\) 的下降。当 \(M=2\)，直接取 \(T\) 得到模 2 下降。若 \(Y\equiv0\pmod{2^M}\)，同一构造给出模 \(2^M\) 下降；必要性由基 \(1,\theta_\mu\) 的唯一表示立即得到。这证明 (10)。

若所有块秩为 1，式 (12) 中每个块满足 \(v^2=1\)，所以 \(v=\pm1\)，真正解本身即在基域上。

## 七、例子与最优性

取 \(n_1=n_2=1\) 及
\[
A_1=\begin{pmatrix}1&2\\2&4\end{pmatrix},
\qquad A_2=I-A_1.
\]
这里 \(\varepsilon_1=\varepsilon_2=1\)，所以真正解均不存在，但
\[
\begin{pmatrix}1&2\\2&1\end{pmatrix}\pmod4
\]
是有限精度解。这同时说明不能把模 4 可解等同于真正可解。

有限精度的额外解也可在可行输入上出现。取 \(A_i=E_i\)，在一个一维坐标上放 \(1+2^{M-1}\)，其余位置取 1。对每个 \(M\ge3\)，它属于 \(\mathscr C_{F,M}\)，但列范数未通过式 (1)，所以不属于 \(\mathscr R_{F,M}\)。在扩域的 \(M=2\) 层，将该坐标改为 \(1+2\theta_\mu\) 也给出有限精度解而非真正解的约化。

任意块秩下，
\[
I+2^{M-1}\theta_\mu E_{11}
\]
是 \(A_i=E_i\) 时的固定有限精度解类，但不是基域矩阵类，说明式 (2) 中的额外固定点确实存在。

最后证明式 (9) 的界在每个精度都最优。若某块秩至少为 2，取 \(A_i=E_i\)，在该块放置
\[
\begin{pmatrix}
\dfrac{1-z^2}{1+z^2}&\dfrac{2z}{1+z^2}\\[2mm]
-\dfrac{2z}{1+z^2}&\dfrac{1-z^2}{1+z^2}
\end{pmatrix},
\]
其他位置取单位矩阵，其中
\[
z=
\begin{cases}
2^{M-2}(1+\theta_{-1}),&\mu=-1,\\
2^{M-2}\theta_2,&\mu=2.
\end{cases}
\]
分母是单位，矩阵正交且模 2 为单位矩阵。其 \(\theta_\mu\) 系数均被 \(2^{M-1}\) 整除，故模 \(2^M\) 被固定；但一个非对角元的 \(\theta_\mu\) 系数恰有 2-adic 赋值 \(M-1\)。因此它不能模 \(2^M\) 与任何基域矩阵同余。该构造对所有 \(M\ge2\) 同时有效。

## 八、进一步结果：任意有限二进局部扩域上的完整有限层演化

上述有限层机制不依赖题目中两个特定二次扩域。设 \(K/\mathbb Q_2\) 是任意有限扩域，整数环为 \(\mathcal O\)，剩余域为 \(\mathbb F_{2^f}\)，并令
\[
q=|\mathcal O/2\mathcal O|.
\]
对任意秩 \(n\)，令 \(G_M\) 是
\[
\{V\in\operatorname{GL}_n(\mathcal O):V\equiv I\pmod2,\ V^{\mathsf T}V=I\}
\]
模 \(2^M\) 的像，令 \(D_M\) 是对应的全部模 \(2^M\) 方程解。则对每个 \(M\ge2\)，
\[
|G_M|=2q^{\binom n2(M-1)},\qquad
|D_2|=q^{n(n+1)/2},\qquad
|D_{M+1}|=q^{n(n+1)/2}|G_M|.
\tag{14}
\]
而且
\[
D_{M+1}\longrightarrow D_M\text{ 的像为 }G_M,
\]
每个非空纤维大小为 \(q^{n(n+1)/2}\)；并有精确序列
\[
1\longrightarrow
\operatorname{Alt}_n(\mathcal O/2)
\longrightarrow G_{M+1}
\longrightarrow G_M
\longrightarrow1.
\tag{15}
\]
这里核中的 \(H\) 对应 \(I+2^M H\)。式 (1) 的列范数判准和上述逐位构造在此一般性下同样成立。

为核实初始层计数，令 \(B=\mathcal O/2\mathcal O\)。它是特征 2 的有限局部环，剩余域为 \(\mathbb F_{2^f}\)。映射
\[
\wp:B\to B,\qquad x\mapsto x+x^2
\]
的核恰为 \(\{0,1\}\)：其核元是局部环的幂等元。在 \(B\) 的幂零理想上，\(x\mapsto x+x^2\) 是双射，因为 Frobenius 在该理想上迭代后为零。因此 \(\wp(x)=a\) 可解，当且仅当 \(a\) 在剩余域中的像具有零绝对迹。

对式 (13) 的每一列，这给出非对角元剩余域值的迹之和为零。完全图的这些偶度条件有 \(n-1\) 个独立的二元条件；每个对角方程恰有两个解。于是
\[
|G_2|
=2^n\frac{q^{\binom n2}}{2^{n-1}}
=2q^{\binom n2}.
\]
提升引理和核的交错矩阵描述随即给出 (14)、(15)。这对任意有限 \(2\)-进扩域、任意秩及所有精度，完整确定了这些正交同余层的初始约束和逐层演化。

保留并核实了原答的谱分解、可行性判准和最优下降界；新增了全部有限层计数、固定点矩阵描述、提升判准、纤维及任意有限扩域上的演化定理。上述证明没有留下已知未完成项。按题给尺度自评为 **B2**；第八节把有限层结构推广到任意有限二进局部扩域，并确定全部精度的初始约束、核和演化，属于有完整证明的广泛自然延伸，自评 **R3**。