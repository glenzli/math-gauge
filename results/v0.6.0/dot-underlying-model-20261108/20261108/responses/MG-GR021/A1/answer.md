# 解答

以下所有同余均按题中的理想 (2^m\mathcal O_L) 理解，而不是按扩域的极大理想的 (m) 次幂理解。这个区别在固定点问题中很重要。

记
\[
t_i=\frac{n_i(n_i-1)}2,\qquad s_i=\frac{n_i(n_i+1)}2,
\qquad t=\sum_i t_i,\quad s=\sum_i s_i=t+d,
\]
并记
\[
q_F=2,\qquad q_{K_{-1}}=q_{K_2}=4.
\]

## 一、可行性判准与全部基数

### 1. 只需模 (4) 的判准

对 (k\ne i)，定义二元矩阵
\[
B_{ki}=\left(\frac{A_i[I_k,I_i]}2\right)\bmod2
       \in M_{n_k,n_i}(\mathbb F_2).
\]
定义
\[
e_i=\sum_{k\ne i}\sum_{a\in I_k,\ b\in I_i}(B_{ki})_{ab}
       \in\mathbb F_2.                                      \tag{1}
\]
这里也可以将每个被加的元素换成其平方。称条件
\[
\boxed{e_i=0\quad(1\le i\le r)}                            \tag{F}
\]
为可行条件。

对于三个域 (L)，都有
\[
\boxed{\mathscr S_L(A)\ne\varnothing\iff\text{(F)}.}       \tag{2}
\]
特别地，两个二次扩张都不会使原来不可行的输入变得可行。判准 (1) 确实只用 (A_i\bmod4)。

### 2. 基数和空集条件

若 (F) 不成立，则对于所有 (L,M\ge2)，
\[
\mathscr R_{L,M}(A)=\varnothing;
\]
此外，
\[
|\mathscr C_{L,2}(A)|=q_L^s,
\qquad
\mathscr C_{L,M}(A)=\varnothing\quad(M\ge3).               \tag{3}
\]
因此模 (4) 的近似解总存在。

若 (F) 成立，则
\[
\boxed{|\mathscr R_{L,M}(A)|=2^r q_L^{(M-1)t}\quad(M\ge2),} \tag{4}
\]
以及
\[
\boxed{
|\mathscr C_{L,M}(A)|=
\begin{cases}
q_L^s,&M=2,\\
2^r q_L^{(M-1)t+d},&M\ge3.
\end{cases}}                                               \tag{5}
\]
这些集合在此情形都非空。

### 3. 可核验的真正可提升性判准

给定 \(\bar U\in\mathscr C_{L,M}(A)\)，任取其整系数矩阵提升 \(\widetilde U\)。则
\[
\boxed{
\bar U\in\mathscr R_{L,M}(A)
\iff
(\widetilde U^{\mathsf T}\widetilde U)_{aa}
       \equiv1\pmod{2^{M+1}\mathcal O_L}
\quad(1\le a\le d).
}                                                          \tag{6}
\]
右侧与所取提升无关。因而只需再检验各列平方长度的一位精度，不必先找出一个真正解。

## 二、固定矩阵类、轨道与约化

以下令 (K=K_\mu,\theta=\theta_\mu,\sigma=\sigma_\mu)。将二元矩阵的元素用 (0,1) 提升。

令
\[
\operatorname{Sym}_{\rm bl}=\bigoplus_i\operatorname{Sym}_{n_i}(\mathbb F_2),
\qquad
\operatorname{Alt}_{\rm bl}
 =\{Y\in\operatorname{Sym}_{\rm bl}:Y_{aa}=0\ (\forall a)\}.
\]
它们的维数分别是 (s,t)。这里“交替”指特征 (2) 下对称且对角为零。

### 1. \(\mathscr C\) 的固定矩阵类

对每个 (M\ge2)，都有如下不交且唯一的表示：
\[
\boxed{
\mathscr C_{K,M}(A)^\sigma
 =\left\{X+2^{M-1}\theta Y:
       X\in\mathscr C_{F,M}(A),\quad
       Y\in\operatorname{Sym}_{\rm bl}\right\}.
}                                                          \tag{7}
\]
因此
\[
|\mathscr C_{K,M}(A)^\sigma|
 =2^s|\mathscr C_{F,M}(A)|.                                \tag{8}
\]
具体而言，在 (M=2) 时，整个 \(\mathscr C_{K,2}\) 都固定，基数为 (2^{2s})。在 (M\ge3) 且 (F) 成立时，固定点数为
\[
\boxed{2^{r+Mt+2d}.}                                      \tag{9}
\]
若 (M\ge3) 且 (F) 不成立，则没有固定点。

### 2. \(\mathscr R\) 的固定矩阵类

若 (F) 不成立，以下 \(\mathscr R\) 集合全空。若 (F) 成立，则对 (M\ge3)，
\[
\boxed{
\mathscr R_{K,M}(A)^\sigma
 =\left\{X+2^{M-1}\theta Y:
       X\in\mathscr R_{F,M}(A),\quad
       Y\in\operatorname{Alt}_{\rm bl}\right\}.
}                                                          \tag{10}
\]

在 (M=2) 时要区分两个扩张。对 (X\in\mathscr C_{F,2}(A))，定义
\[
\delta_a(X)=
\frac{(\widetilde X^{\mathsf T}\widetilde X)_{aa}-1}{4}
\bmod2.                                                   \tag{11}
\]
该定义与整数提升无关。对二元矩阵 (Y)，记
\[
\rho_a(Y)=\sum_bY_{ba}\in\mathbb F_2.
\]
则
\[
\boxed{
\mathscr R_{K_2,2}(A)^\sigma
 =\{X+2\theta_2Y:X\in\mathscr R_{F,2}(A),\
                         Y\in\operatorname{Alt}_{\rm bl}\},
}                                                          \tag{12}
\]
而
\[
\boxed{
\mathscr R_{K_{-1},2}(A)^\sigma
 =\{X+2\theta_{-1}Y:X\in\mathscr C_{F,2}(A),\
             Y\in\operatorname{Alt}_{\rm bl},\
             \rho(Y)=\delta(X)\}.
}                                                          \tag{13}
\]
特别是，(13) 中的实系数部分 (X) 不一定本身属于 \(\mathscr R_{F,2}\)。

对于两个扩张和所有 (M\ge2)，固定点数统一为
\[
\boxed{|\mathscr R_{K,M}(A)^\sigma|=2^{r+Mt}}               \tag{14}
\]
（以 (F) 成立为前提）。在 (M=2) 时，整个 \(\mathscr R_{K,2}\) 都固定。

基域集合在这些描述中就是 (Y=0) 的部分，且始终有
\[
\begin{aligned}
\mathscr R_{K,M}(A)\cap M_d(\mathbb Z_2/2^M)
 &=\mathscr R_{F,M}(A),\\
\mathscr C_{K,M}(A)\cap M_d(\mathbb Z_2/2^M)
 &=\mathscr C_{F,M}(A).                                   \tag{15}
\end{aligned}
\]
因此，在可行情形下，\(\mathscr R_{K,M}^\sigma=\mathscr R_{F,M}\) 当且仅当 (t=0)，即所有块秩均为 (1)。\(\mathscr C_{K,M}^\sigma\) 只要非空，就严格包含 \(\mathscr C_{F,M}\)。

### 3. 轨道数

对作用在有限集上的对合，轨道数为“总数加固定点数，再除以 (2)”。从而，在 (F) 成立时，
\[
\boxed{
\#\bigl(\mathscr R_{K,M}(A)/\langle\sigma\rangle\bigr)
 =2^{r-1}\left(2^{2(M-1)t}+2^{Mt}\right).
}                                                          \tag{16}
\]
若 (F) 不成立，该轨道数为零。

对于 \(\mathscr C\)，无论是否可行，精度 (2) 的轨道数均为
\[
\boxed{2^{2s}.}                                           \tag{17}
\]
在 (M\ge3) 且 (F) 成立时，其轨道数为
\[
\boxed{
2^{r+2d-1}\left(2^{2(M-1)t}+2^{Mt}\right).
}                                                          \tag{18}
\]
在 (M\ge3) 且 (F) 不成立时为零。

### 4. 所有约化像和非空纤维

以下均指 (M+1\longrightarrow M)，其中 (M\ge2)。在 (F) 成立时：

| 约化映射 | 在目标中的像 | 每个非空纤维的大小 |
|---|---|---:|
| \(\mathscr R_{L,M+1}\to\mathscr R_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^t\) |
| \(\mathscr C_{L,M+1}\to\mathscr C_{L,M}\) | \(\mathscr R_{L,M}\) | \(q_L^s\) |
| \(\mathscr R_{K,M+1}^{\sigma}\to\mathscr R_{K,M}^{\sigma}\) | \(\mathscr R_{F,M}\) | \(2^{2t}\) |
| \(\mathscr C_{K,M+1}^{\sigma}\to\mathscr C_{K,M}^{\sigma}\) | \(\mathscr R_{F,M}\) | \(2^{2s}\) |

未列在像中的目标元素的纤维均为空。若 (F) 不成立，上述四种约化的源均为空，因此像为空，没有非空纤维。基域上“固定点”的约化当然就是前两行取 (L=F)。

注意：固定点的约化像通常比“先约化再取固定点”的结果小得多。

### 5. 固定类的两种无限提升问题

令 (\bar U) 属于 \(\mathscr R_{K,M}^\sigma\) 或 \(\mathscr C_{K,M}^\sigma\)。下列三件事等价：

1. (\bar U) 能提升为一个真正的 \(\sigma\)-固定解；
2. (\bar U) 能作为一条逐层相容的固定矩阵类序列的精度 (M) 分量，无论该序列要求在各层属于 \(\mathscr R^\sigma\) 还是 \(\mathscr C^\sigma\)；
3. \(\bar U\in\mathscr R_{F,M}(A)\)。

在上述唯一表示中，第三项即 (Y=0)，并要求 (X\in\mathscr R_{F,M}\)。对于已经在 \(\mathscr R^\sigma\) 中的类，(Y=0) 自动蕴含后一个要求。

## 三、最佳统一下降精度

对题目第三部分的量，答案为
\[
\boxed{
N_{\max}=
\begin{cases}
M,&n_1=\cdots=n_r=1,\\
M-1,&\text{至少一个 }n_i\ge2.
\end{cases}}                                               \tag{19}
\]
这个答案与 \(\mu\) 无关。

更精确地，将给定真正解唯一写成
\[
U=P+\theta_\mu Q,\qquad P,Q\in M_d(\mathbb Z_2).
\]
题中的近似固定条件等价于 (Q\in2^{M-1}M_d(\mathbb Z_2))。对这样的 (A,U)，能取 (N=M) 的必要充分条件为
\[
\boxed{Q\in2^M M_d(\mathbb Z_2).}                         \tag{20}
\]
也就是说，精度 (M) 的矩阵类本身必须来自基域；没有额外隐藏的下降障碍。

若所有块秩均为 (1)，实际上有更强的结论：
\[
\boxed{\mathscr S_{K_\mu}(A)=\mathscr S_F(A)}              \tag{21}
\]
（用自然包含来理解），并非仅有有限精度的下降。

## 四、证明

### 1. 规范的正交不变分解

设 (p(x)=3x^2-2x^3)。从 (A_i\) 开始反复施加 (p)，得到收敛的幂等矩阵 (P_i\)。这是幂等元提升的一个直接构造：(p(x)-x) 是 (x^2-x) 的倍数，而 (p(x)^2-p(x)) 是 \((x^2-x)^2\) 的倍数。因此幂等误差的 (2)-进阶数至少逐次加倍。

于是
\[
P_i^2=P_i,\quad P_i^{\mathsf T}=P_i,\quad P_i\equiv E_i\pmod2.
\]
各 (P_i) 相互交换，并与所有 (A_j) 交换。若 (i\ne j)，则 (P_iP_j) 是模 (2) 为零的幂等元，因此为零。相同理由给出
\[
\sum_iP_i=I.
\]
这里所用的简单事实是：在 (2)-进完备环或其模 (2^M) 商中，落在理想 (2) 内的幂等元只能是零。

而且，若某个幂等元 (Q\equiv E_i\pmod2) 与所有 (A_j) 交换，则它与各 (P_j) 交换。对 (j\ne i)，幂等元 (QP_j\equiv0\pmod2)，故为零；对 \((I-Q)P_i\) 同理。因此 (Q=P_i)。这个论证也适用于模 (2^M) 的矩阵。

令 (T_i) 为 \(\operatorname{im}P_i\) 的图基：其 (I_i\) 行组成单位矩阵，其余行记为 (2D_{ki})，其中 (D_{ki}\in M_{n_k,n_i}(\mathbb Z_2))。令
\[
T=(T_1,\ldots,T_r).
\]
则
\[
T\equiv I\pmod2,\qquad
T^{\mathsf T}T=\operatorname{diag}(H_1,\ldots,H_r),
\]
其中
\[
H_i=I_{n_i}+4D_i,\qquad D_i=\sum_{k\ne i}D_{ki}^{\mathsf T}D_{ki}.       \tag{22}
\]
由于 (P_i[I_i,I_i]\) 是单位矩阵模 (2)，图基可直接由 (P_i) 的对应列右乘该主块的逆得到。

幂等提升模 (4) 的非对角块与 (A_i) 相同，故
\[
D_{ki}\bmod2=B_{ki}.                                      \tag{23}
\]
例如将 (A_i=E_i+2C\) 代入 (p(A_i)\bmod4\) 即得此结论；后续迭代不再改变模 (4) 的结果。由 (22)、(23)，
\[
\operatorname{tr}(D_i)\bmod2=e_i.                         \tag{24}
\]

若 (U) 是一个精确或模 (2^M) 的题设解，则 (UE_iU^{\mathsf T}\) 是与所有 (A_j\) 交换、模 (2) 为 (E_i\) 的幂等元，故等于相应的 (P_i\)。所以其第 (i\) 组列恰好属于上述规范子模，且唯一地写为
\[
U=T\operatorname{diag}(V_1,\ldots,V_r),\qquad V_i\equiv I\pmod2,
\]
并满足
\[
V_i^{\mathsf T}H_iV_i=I.                                  \tag{25}
\]
反过来，(25) 也充分，因为各子模相互正交且被所有 (A_j\) 保持。这个描述同时适用于整数环和有限商。

### 2. 一个保精度的正规化引理

**引理。** 设 \(\mathcal O\) 是本文的任一整数环，(m\ge2)，(H\) 对称，并且
\[
H\equiv I\pmod{2^m},\qquad H_{aa}\equiv1\pmod{2^{m+1}}.
\]
则存在 (B\equiv I\pmod{2^m}\) 使 (B^{\mathsf T}HB=I\)。

**证明。** 可取矩阵 (Q\in2^mM_n(\mathcal O)\) 使
\[
Q+Q^{\mathsf T}=-(H-I).
\]
具体取对角元为 \(-(H_{aa}-1)/2\)，上三角元为 \(-H_{ab}\)，下三角元为零即可。令 (B_0=I+Q\)。则
\[
B_0^{\mathsf T}HB_0-I\in2^{2m}M_n(\mathcal O).
\]
由于 (2m\ge m+2\)，新的误差满足以 (m+1\) 代替 (m\) 的假设。依次重复，所得矩阵乘积收敛，且保持模 (2^m\) 为单位矩阵。这给出所求 (B\)。证毕。

这个引理只用了整数环的 (2)-进完备性，不需要关于分歧域二次型分类的额外定理。

### 3. 可行性的证明及基域解的构造

考虑一个块 (H=I+4D\)，并写 (V=I+2X\)。模 (4\) 的非对角正交条件给出
\[
X=X^{\mathsf T}\pmod2.
\]
模 (8\) 的对角条件给出
\[
D_{aa}+X_{aa}+\sum_kX_{ka}^2=0\quad\text{在 }\mathcal O/2\mathcal O\text{ 中}. \tag{26}
\]
在基域中，(26) 化为
\[
\sum_{k\ne a}X_{ka}=D_{aa}\quad\text{在 }\mathbb F_2\text{ 中}.             \tag{27}
\]
对称矩阵的非对角元素在所有行和之和中出现两次，所以必要条件是 \(\sum_aD_{aa}=0\)。它也充分：完全图的边到顶点的关联映射
\[
\mathbb F_2^{\binom n2}\longrightarrow\mathbb F_2^n
\]
的像恰是坐标和为零的子空间，秩为 (n-1\)，包括 (n=1\) 时秩为零的情形。

对两个扩张都有
\[
\mathcal O_K/2\mathcal O_K\simeq\mathbb F_2[\varepsilon]/(\varepsilon^2),
\]
其中 (K_2\) 取 \(\varepsilon=\theta_2\)，(K_{-1}\) 取 \(\varepsilon=1+\theta_{-1}\)。写 (X=A+\varepsilon B\)。由于 (D\) 来自基域，(26) 的常数部分仍是 (27)，而其 \(\varepsilon\) 部分要求 (B_{aa}=0\)。所以扩域中的必要条件完全相同。

当该必要条件成立时，直接在 \(\mathbb F_2\) 中选取一个满足 (27) 的对称 (X\)，提升到整数矩阵。(V_0=I+2X\) 使 (V_0^{\mathsf T}HV_0\) 的非对角误差被 (4\) 整除、对角误差被 (8\) 整除。应用引理，得到 (V=V_0B\) 的真正解，而且在 \(\mathbb Z_2\) 上就能完成。

结合 (24)，这证明了 (2)，也构造了一个可行情形下的
\[
U_0\in\mathscr S_F(A).                                    \tag{28}
\]
此时所有解都有唯一表达
\[
\mathscr S_L(A)
=U_0\prod_iG_{n_i}(\mathcal O_L),\qquad
G_n(\mathcal O)=\{g:g^{\mathsf T}g=I,\ g\equiv I\pmod2\}, \tag{29}
\]
右侧的乘积按标准块对角嵌入。有限精度的 \(\mathscr C\) 亦由 (U_0\) 给出相应的扭子描述。

### 4. 判准 (6) 的证明

若改变提升 \(\widetilde U\mapsto\widetilde U+2^MZ\)，第 (a\) 列平方长度改变
\[
2^{M+1}\langle\widetilde U_a,Z_a\rangle+2^{2M}\langle Z_a,Z_a\rangle,
\]
故模 (2^{M+1}\) 不变。必要性显然。

反之，将每组列用对应 (P_i\) 投影，得到矩阵 (V\)。上一节的唯一性说明
\[
V\equiv\widetilde U\pmod{2^M}.
\]
不同列组已精确正交，各组 Gram 矩阵模 (2^M\) 为单位矩阵；按假设，其对角还多消失一位。逐块应用正规化引理，得到一个与 \(\widetilde U\) 模 (2^M\) 相同的真正正交矩阵。它的列仍在规范不变子模中，因此满足全部分块要求。这证明 (6)。

### 5. 计数和普通约化纤维

先处理一个标准块，记 (t_n=n(n-1)/2\)、(s_n=n(n+1)/2\)。模 (4\) 时，矩阵写成 (I+2X\)，正交条件恰是 (X\) 在 \(\mathcal O/2\) 上对称。所以近似解数为 (q^{s_n}\)。对一般输入，(22) 中 (H\equiv I\pmod4\)，故此计数不变。

对真正可提升的模 (4\) 类，还须满足 (26) 取 (D=0\)。在基域，对角有 (2^n\) 个选择，非对角有 (2^{t_n-n+1}\) 个选择，故总数为 (2^{t_n+1}\)。在扩域，写成 (A+\varepsilon B\) 后，(A\) 有上述选择，而 (B\) 是任意零对角对称矩阵，有 (2^{t_n}\) 个选择。故统一写为
\[
|R_{n,2}|=2q^{t_n}.                                      \tag{30}
\]
判准 (6) 保证这些类全部可提升。

给定真正解在精度 (M\) 的类，其精度 (M+1\) 的真正解提升可写成
\[
g(I+2^MX)\pmod{2^{M+1}}.
\]
正交模 (2^{M+1}\) 要求 (X\) 模 (2\) 对称，而 (6) 再要求其对角为零。因此纤维大小为 (q^{t_n}\)。由 (30) 得到 (4)。

同样，精度 (M+1\) 的近似解约化到精度 (M\)，必满足 (6)，故其像正是 (R_{n,M}\)。在一个真正提升周围，所有近似提升的参数是模 (2\) 的任意对称矩阵，故纤维大小为 (q^{s_n}\)。相乘即得到 (5) 以及约化表的前两行。

若不可行，模 (8\) 解会由 (26) 强制推出 (F)，矛盾。这也证明了全部空集断言。

### 6. 固定点的证明

由于 \(\mathcal O_K=\mathbb Z_2\oplus\theta\mathbb Z_2\)，有
\[
\sigma(a+b\theta)\equiv a+b\theta\pmod{2^M\mathcal O_K}
\iff b\in2^{M-1}\mathbb Z_2.
\]
因此任一固定矩阵类唯一写为
\[
X+2^{M-1}\theta Y,
\quad X\in M_d(\mathbb Z_2/2^M),\quad Y\in M_d(\mathbb F_2).             \tag{31}
\]
对正交条件展开，因为 (X\equiv I\pmod2\)，模 (2^M\) 的虚系数条件就是 (Y^{\mathsf T}=Y\)。二次项含 (2^{2M-2}\)，模 (2^M\) 消失。

再由规范分块描述，或将 (31) 左乘 (T^{-1}\)，可知 (Y\) 的非对角块必须为零，而 (X\) 自身满足基域的全部近似方程。注意 (T^{-1}\equiv I\pmod2\)，故这一最高位系数的块位置不变。由此得到 (7)。

为了判断它是否在 \(\mathscr R\) 中，使用 (6)。第 (a\) 列平方长度的额外项是
\[
2^M\theta\sum_kX_{ka}Y_{ka}
 +2^{2M-2}\mu\sum_kY_{ka}^2.                              \tag{32}
\]
模 (2^{M+1}\) 的虚系数要求 (Y_{aa}=0\)。若 (M\ge3\)，(32) 的第二项已被 (2^{M+1}\) 整除，故实系数条件恰为 (X\in\mathscr R_{F,M}\)，得到 (10)。若 (M=2\)，实系数条件是
\[
\delta(X)+(\mu\bmod2)\rho(Y)=0.
\]
分别得到 (12)、(13)。

精度 (2\) 的一切矩阵类 (I+2Z\) 都被共轭固定，因为 \(\sigma(Z)-Z\in2M_d(\mathcal O_K)\)。所以此时固定点数就等于总数。对 (M\ge3\)，由 (10) 得到 (14)。公式 (8)、(9)、(16)—(18) 也随之成立。

在精度 (M+1\ge3\)，固定类的虚系数都是 (2^M\theta Y\)，约化到精度 (M\) 后消失。用 (10) 和普通约化结论，固定 \(\mathscr R\) 的像就是 \(\mathscr R_{F,M}\)；用 (7) 也得到固定 \(\mathscr C\) 的同一个像。分别计算纤维：
\[
2^t\cdot2^t=2^{2t},\qquad 2^s\cdot2^s=2^{2s}.
\]
这证明约化表的后两行。

真正固定的整矩阵恰是基域整矩阵，故真正固定提升的条件是属于 \(\mathscr R_{F,M}\)。相容固定序列的逆极限存在，且其正交方程、分块方程及固定条件都由完备性保持。因此相容序列也只能给出真正固定解。反过来，一个基域真正解的所有约化给出这样的序列，证明第二部分最后的等价断言。

### 7. 下降界的证明

由可行性判准，题目第三部分既然给出了扩域真正解，就必有基域真正解。

若 (M\ge3\)，公式 (10) 说明给定类模 (2^{M-1}\) 与某个基域真正解一致。若 (M=2\)，所有真正解都模 (2\) 为单位矩阵，故同样得到 (N=M-1\)。

若 (t=0\)，(29) 的每个因子都是 (G_1(\mathcal O_L)=\{1,-1\}\)，所以全部扩域真正解已经在基域。这证明 (21)，从而 (N=M\)。

对于个别给定解，存在精度 (M\) 的基域下降当然要求其虚系数被 (2^M\) 整除。反过来，若此条件成立，它的矩阵类为一个基域类，而 (15) 保证该类在 \(\mathscr R_{F,M}\) 中。这证明 (20)。

## 五、反例、严格性与统一的最优性构造

以下例子也说明，以上“可能不提升”“不一定下降”等区别并非形式上的。

### 1. 扩域不能修复的不可行输入

当 (r\ge2\) 时，在两个不同块中各选一个坐标 (a,b\)。在该二维坐标平面上令
\[
A_1=\begin{pmatrix}1&2\\2&0\end{pmatrix},\qquad
A_2=\begin{pmatrix}0&-2\\-2&1\end{pmatrix}=I-A_1,
\]
其他坐标上保持标准投影；其他 (A_j\) 也保持标准投影。它们对称、相互交换，且模 (2\) 为规定投影。但相应两个 (e_i\) 都为 (1\)，所以三个域上均无真正解，亦无模 (8\) 解。

模 (4\) 却有解：在该平面取
\[
\bar U=\begin{pmatrix}1&-2\\2&1\end{pmatrix}\pmod4,
\]
其余坐标取单位矩阵即可。这个构造适用于任意至少两个块的块秩。若 (r=1\)，判准自动成立，当然不会出现这种不可行性。

### 2. 近似解不一定真正可提升

取 (A_i=E_i\)。对任意 (M\ge3\)，在任一坐标取对角元 (1+2^{M-1}\)，其他部分取单位矩阵。所得类属于三个域上的 \(\mathscr C_{L,M}\)，但其该列长度减 (1\) 为
\[
2^M+2^{2M-2},
\]
不被 (2^{M+1}\) 整除。因此它不属于 \(\mathscr R_{L,M}\)，也不在下一层近似解的约化像中。这是所有精度的统一构造。

在 (M=2\) 的基域情形，若某块秩至少为 (2\)，可在该块取
\[
\begin{pmatrix}1&2\\2&1\end{pmatrix}\pmod4.
\]
列长度为 (5\)，故不可真正提升。若所有块秩均为 (1\) 且输入可行，基域的 \(\mathscr C_{F,2}=\mathscr R_{F,2}\)，这正是不存在此类反例的情形。

在任一个扩域，精度 (2\) 时即使只有一维，也可取对角元 (1+2\theta_\mu\)。它的平方模 (4\) 为 (1\)，但模 (8\) 的障碍为
\[
\theta_\mu+\mu\in\mathcal O_\mu/2\mathcal O_\mu,
\]
该元素在两个扩张中都非零，因此不可真正提升。

对固定 \(\mathscr C\) 与基域 \(\mathscr C\) 的严格差异，在任意精度可取
\[
I+2^{M-1}\theta_\mu E_{aa}\pmod{2^M}.
\]
它固定且属于 \(\mathscr C_{K_\mu,M}(E)\)，却不来自基域，也不能提升为真正解，因为其最高位虚系数有非零对角。这同时说明固定 \(\mathscr C\) 的约化不必满射。

### 3. 下降界在所有精度上的最优性

假设某块秩至少为 (2\)，仍取 (A_i=E_i\)。只在该块的一个二维平面上做以下旋转，其余坐标取单位矩阵：
\[
R(z)=\frac1{1+z^2}
\begin{pmatrix}1-z^2&-2z\\2z&1-z^2\end{pmatrix}.           \tag{33}
\]
只要所列分母为单位，直接相乘可验 (R(z)^{\mathsf T}R(z)=I\)。

对所有 (M\ge3\)，统一取
\[
z=2^{M-2}\theta_\mu.
\]
分母 (1+\mu2^{2M-4}\) 是奇数，矩阵属于 \(\mathscr S_{K_\mu}(E)\)。其非对角虚系数恰为
\[
\pm\frac{2^{M-1}}{1+\mu2^{2M-4}},
\]
是 (2^{M-1}\) 乘一个奇单位。因此
\[
\sigma(R(z))\equiv R(z)\pmod{2^M},
\]
但矩阵类模 (2^M\) 不来自基域。它不可能在精度 (M\) 下降，也不可能是相容固定类序列的该层分量。

在 (M=2,\mu=2\) 时取 (z=\theta_2\)，分母为 (3\)，同样的结论成立。

在 (M=2,\mu=-1\) 时取 (z=1+\theta_{-1}\)。此时 (33) 的对角和左下角分别为
\[
\frac{-3-4\theta_{-1}}5,
\qquad
\frac{6-2\theta_{-1}}5.
\]
矩阵模 (2\) 为单位矩阵，共轭差被 (4\) 整除，但左下角的虚系数不被 (4\) 整除。因此同样不能精确下降到模 (4\)。而且其模 (4\) 的实系数部分是
\[
\begin{pmatrix}1&2\\2&1\end{pmatrix},
\]
正好展示了公式 (13) 中 (X\) 可能不在 \(\mathscr R_{F,2}\) 的现象。

这些例子对每种允许出现非平凡旋转的块秩都适用，并覆盖全部 (M\ge2\)，证明了 (19) 的最优性，也展示了固定 \(\mathscr R\) 的约化在 (t>0\) 时并不满射。相反，所有块秩为 (1\) 时已有 (21) 的精确下降，不存在这样的反例。
