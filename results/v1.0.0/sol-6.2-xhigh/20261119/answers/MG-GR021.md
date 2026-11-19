令
\[
e=\sum_{i=1}^r\binom{n_i}{2},\qquad
q_L=|\mathcal O_L/2\mathcal O_L|=
\begin{cases}
2&L=F,\\
4&L=K_{-1},K_2.
\end{cases}
\]
对每块定义
\[
\kappa_i=\sum_{\substack{a\in I_i\\ b\notin I_i}}
\frac{(A_i)_{ba}}2\pmod2,\qquad
\chi=
\begin{cases}
1&\text{所有 }\kappa_i=0,\\
0&\text{至少一个 }\kappa_i\ne0.
\end{cases}
\]
分子都是偶数，所以 \(\chi\) 可由 \(A_i\bmod4\) 计算。三个域上的 \(\mathscr S_L(A)\) 都恰在 \(\chi=1\) 时非空。

## 1. 同时分块、计数与提升判据

有限集合的基数为
\[
\boxed{
\begin{aligned}
|\mathscr R_{L,M}(A)|&=\chi\,2^r q_L^{(M-1)e},\\
|\mathscr C_{L,2}(A)|&=q_L^{d+e},\\
|\mathscr C_{L,M}(A)|&=\chi\,2^r q_L^{(M-1)e+d}\qquad(M\ge3).
\end{aligned}}
\]
因此 \(\mathscr C_{L,2}(A)\) 总是非空。其余两类的空集条件都是 \(\chi=0\)。

给定 \(\bar U\in\mathscr C_{L,M}(A)\)，任选整数矩阵代表元 \(\widetilde U\)。可提升判据是
\[
\boxed{\quad
\bar U\in\mathscr R_{L,M}(A)
\iff
(\widetilde U^{\mathsf T}\widetilde U-I_d)_{aa}
\equiv0\pmod{2^{M+1}\mathcal O_L}\quad\text{对所有 }a.
\quad} \tag{1}
\]
一个列向量改变 \(2^M z\) 时，其平方长度的改变量属于 \(2^{M+1}\mathcal O_L\)，所以此检验与代表元无关。

### 构造共同分块

取 \(f(t)=3t^2-2t^3\)。多项式 \(f(t)-t\) 被 \(t(t-1)\) 整除，而 \(f(t)^2-f(t)\) 被 \(t^2(t-1)^2\) 整除。因 \(A_i^2-A_i\equiv0\pmod2\)，迭代 \(f\) 时幂等误差的 \(2\)-进精度至少逐次翻倍，相邻两项之差也趋于零。于是迭代收敛到对称幂等矩阵 \(P_i\)，满足
\[
P_i\equiv E_i\pmod2,\qquad P_i\equiv f(A_i)\pmod4.
\]
这些 \(P_i\) 两两交换，并与所有 \(A_j\) 交换。对于 \(i\ne j\)，\(P_iP_j\) 是模 \(2\) 为零的幂等矩阵。这样的矩阵等于自身的任意正整数次幂，故为零。于是 \(\sum_i P_i\) 幂等，且其补幂等矩阵模 \(2\) 为零，故 \(\sum_iP_i=I_d\)。

把各 \(P_i\) 的 \(I_i\) 列依次拼接，得到一个模 \(2\) 为 \(I_d\) 的可逆矩阵。这些列给出各 \(\operatorname{im}P_i\) 的基。再将每组列乘以其 \(I_i\) 行子矩阵的逆，得到基矩阵 \(T_i\)，其 \(I_i\) 行为 \(I_{n_i}\)，其余行为 \(2B_i\)。令 \(T=[T_1\ \cdots\ T_r]\)。由 \(P_i\) 的对称性及 \(P_iP_j=0\)，
\[
T\equiv I_d\pmod2,\qquad
T^{\mathsf T}T=\operatorname{diag}(H_1,\ldots,H_r),\qquad
H_i=I_{n_i}+4D_i,\quad D_i=B_i^{\mathsf T}B_i. \tag{2}
\]
写 \(A_i=E_i+2J_i\)，则 \(f(A_i)\equiv E_i+2(E_iJ_i+J_iE_i)\pmod4\)。因此 \(B_i\bmod2\) 的 \((b,a)\) 项就是 \((A_i)_{ba}/2\bmod2\)，其中 \(a\in I_i,\ b\notin I_i\)。特别地，
\[
\sum_{a=1}^{n_i}(D_i)_{aa}\equiv\kappa_i\pmod2. \tag{3}
\]

在整数环上以及模 \(2^M\) 的商环上，满足正交和同时分块条件的 \(U\) 都有唯一形式
\[
U=T\operatorname{diag}(X_1,\ldots,X_r),\qquad
X_i\equiv I_{n_i}\pmod2,\qquad X_i^{\mathsf T}H_iX_i=I_{n_i}, \tag{4}
\]
其中等式在所讨论的环中成立。事实上，正交性给出 \(U^{\mathsf T}=U^{-1}\)。若各 \(U^{-1}A_jU\) 分块，则各 \(U^{-1}P_iU\) 也分块，因为 \(P_i\) 是多项式迭代的极限，在每个有限精度上迭代最终稳定。其各块是模 \(2\) 为零或单位阵的幂等矩阵，故 \(U^{-1}P_iU=E_i\)。这里的幂等论证在有限商环上同样成立，因为 \(2\) 的幂最终为零。于是 \(T^{-1}U\) 分块。反过来，形式 (4) 给出 \(U^{-1}P_iU=E_i\)，而 \(A_j\) 与 \(P_i\) 交换，故 \(U^{-1}A_jU\) 分块。

### 单块方程与逐层提升

暂取一块，写 \(n=n_i\)、\(H=I_n+4D\)、\(X=I_n+2Y\)。令 \(G=X^{\mathsf T}HX-I_n\)，并定义
\[
\begin{aligned}
\Phi_{ab}(Y)&=G_{ab}/2
 =Y_{ab}+Y_{ba}+2(Y^{\mathsf T}Y+X^{\mathsf T}DX)_{ab} &&(a<b),\\
\Phi_{aa}(Y)&=G_{aa}/4
 =Y_{aa}+(Y^{\mathsf T}Y+X^{\mathsf T}DX)_{aa}.
\end{aligned} \tag{5}
\]
当 \(k\ge1\) 时，将 \(Y\) 改为 \(Y+2^k Z\)，在模 \(2^{k+1}\) 下，\(\Phi_{ab}\) 的改变量为 \(2^k(Z_{ab}+Z_{ba})\)，\(\Phi_{aa}\) 的改变量为 \(2^kZ_{aa}\)。因此，只要 \(\Phi(Y)\equiv0\pmod{2^k}\)，就有恰好 \(q_L^{\binom n2}\) 个模 \(2^{k+1}\) 的提升使所有 \(\Phi\) 继续为零。连续提升得到整数环中的真解，因为 \(\mathcal O_L\) 是有限自由 \(\mathbb Z_2\)-模，关于 \(2\)-进拓扑完备。

模 \(2^M\) 的 \(X\) 对应模 \(2^{M-1}\) 的 \(Y\)。有限正交方程要求非对角 \(\Phi_{ab}\) 模 \(2^{M-1}\) 为零，而对角 \(\Phi_{aa}\) 模 \(2^{M-2}\) 为零。由上面的提升论证，此类来自真解的充要条件是所有 \(\Phi\) 模 \(2^{M-1}\) 为零。这也证明了 (1)。

现在计算 \(\Phi\equiv0\pmod2\) 的解数。记 \(s_a=D_{aa}\bmod2\)。在基域上，\(Y\bmod2\) 须对称，对角项任意，非对角项满足
\[
\sum_{b\ne a}Y_{ba}=s_a\quad\text{于 }\mathbb F_2.
\]
每个无序对 \(\{a,b\}\) 的变量向第 \(a,b\) 个坐标各贡献一次。这一线性映射的像为坐标和为零的向量空间，秩为 \(n-1\)。例如，连接某一固定坐标和其余坐标的 \(n-1\) 个无序对给出一组像的基，\(n=1\) 时秩为零。

在扩域上，\(\mathcal O_L/2\mathcal O_L=\mathbb F_2[\epsilon]/(\epsilon^2)\)，其中 \(\epsilon=\theta_2\bmod2\) 或 \(\epsilon=1+\theta_{-1}\bmod2\)。写 \(Y=Y_0+\epsilon Y_1\)。两部分均须对称，\(Y_0\) 满足上述基域方程，而 \(Y_1\) 的对角线须为零，非对角项任意。这由 \((x+\epsilon y)^2=x\) 直接得到。

所以单块有解恰在 \(\sum_a s_a=0\) 时，且此时模 \(2\) 的解数为 \(2q_L^{\binom n2}\)。结合 (3) 和逐层提升，得到可行性判准及 \(\mathscr R_{L,M}\) 的基数。对 \(\mathscr C_{L,2}\)，只要求 \(Y\bmod2\) 对称，每块有 \(q_L^{n+\binom n2}\) 种。对 \(\mathscr C_{L,M+1}\)，约化到精度 \(M\) 时，所有 \(\Phi\) 都须模 \(2^{M-1}\) 为零。在这样的类上，下一层只新增非对角方程，每块有 \(q_L^{n+\binom n2}\) 种提升。这给出其余的计数。

## 2. 固定矩阵类、轨道与约化

记 \(\mathcal H\) 为 \(\mathbb F_2\) 上按 \(I_i\) 分块的对称矩阵空间，记 \(\mathcal H_0\) 为其中对角线为零的子空间。两者的维数分别为 \(d+e\) 和 \(e\)。令
\[
\delta_{\mu,M}=
\begin{cases}
1&(\mu,M)=(-1,2),\\
0&\text{其余情形}.
\end{cases}
\]
固定点集的具体矩阵类如下，式中 \(Z\) 可用任意整数代表元计算，且每个参数对给出不同的类。
\[
\boxed{
\begin{aligned}
\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}
 &=\left\{\bar V+2^{M-1}\theta_\mu Z:
     \bar V\in\mathscr C_{F,M}(A),\ Z\in\mathcal H\right\},\\
\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}
 &=\left\{\bar V+2^{M-1}(\theta_\mu+\delta_{\mu,M})Z:
     \bar V\in\mathscr R_{F,M}(A),\ Z\in\mathcal H_0\right\}.
\end{aligned}} \tag{6}
\]
两式中基域集合都恰对应 \(Z=0\)。对 \(\mathscr C\)，只要集合非空，这一包含便是严格的。对 \(\mathscr R\)，严格包含恰发生在 \(\chi=1\) 且 \(e>0\) 时。

为证明 (6)，固定类的每个条目都可唯一写成 \(a+2^{M-1}\theta_\mu b\)，其中 \(a\bmod2^M\) 是基域系数，\(b\bmod2\) 是二元系数。这是因为 \(\sigma_\mu(a+c\theta_\mu)-(a+c\theta_\mu)=-2c\theta_\mu\)，而 \(1,\theta_\mu\) 是整数环的 \(\mathbb Z_2\)-基。由于 \(T\) 在基域上，在 (4) 中可逐块写成 \(X=X_0+2^{M-1}\theta_\mu Z\)。模 \(2^M\) 的 Gram 方程要求 \(X_0^{\mathsf T}HX_0=I\) 及 \(Z+Z^{\mathsf T}=0\bmod 2\)，因为 \(X_0,H\equiv I\pmod2\)，且二次修正项含因子 \(2^{2M-2}\)。这给出固定 \(\mathscr C\) 的公式。

对固定 \(\mathscr R\)，还要检验对角项模 \(2^{M+1}\)。第 \(a\) 个对角项相对 \(X_0^{\mathsf T}HX_0-I\) 的改变量是
\[
2^M\theta_\mu (X_0^{\mathsf T}HZ)_{aa}
  +2^{2M-2}\mu (Z^{\mathsf T}HZ)_{aa}.
\]
比较 \(\theta_\mu\) 系数可得 \(Z_{aa}=0\bmod2\)。比较基域系数时，第二项只在 \((\mu,M)=(-1,2)\) 有贡献。在该情形，它模 \(8\) 等于 \(4\sum_b Z_{ba}^2\)，恰等于将 \(X_0\) 换成 \(X_0+2Z\) 后的对角改变量。故此时 \(X_0+2Z\) 须是基域可提升类，其余情形则要求 \(X_0\) 是基域可提升类。拼回整矩阵时，由 \(T\equiv I\pmod2\)，乘 \(T\) 不改变形如 \(2^{M-1}Z\) 的修正项。这证明了 (6)。

若考虑取基域系数的投影，固定 \(\mathscr C\) 投到整个 \(\mathscr C_{F,M}\)，每个纤维大小为 \(2^{d+e}\)。固定 \(\mathscr R\) 在 \(\delta_{\mu,M}=0\) 时投到 \(\mathscr R_{F,M}\)，每个纤维大小为 \(2^e\)。在 \((\mu,M)=(-1,2)\) 且 \(\chi=1\) 时，它投到整个 \(\mathscr C_{F,2}\)，每个纤维大小为 \(2^{e-d+r}\)。最后一个结论来自逐块选择 \(Z\) 来修正基域系数的对角缺差。缺差向量的坐标和为零，修正映射正是上文秩为 \(n_i-1\) 的无序对映射。

固定点数和 \(\langle\sigma_\mu\rangle\) 轨道数为
\[
\begin{array}{c|c|c}
\text{集合}&\text{固定点数}&\text{轨道数}\\ \hline
\mathscr R_{K_\mu,M}
 &\chi\,2^{r+Me}&\chi\,2^{r+Me-1}(1+2^{(M-2)e})\\
\mathscr C_{K_\mu,2}
 &4^{d+e}&4^{d+e}\\
\mathscr C_{K_\mu,M}\ (M\ge3)
 &\chi\,2^{r+Me+2d}&\chi\,2^{r+Me+2d-1}(1+2^{(M-2)e})
\end{array}
\]
固定点数由 (6) 得到。每个非固定轨道恰有两个元素，故轨道数等于总数与固定点数之和的一半。

### 约化像、纤维与相容序列

下表各行均指从精度 \(M+1\) 到精度 \(M\) 的约化。像为空时没有非空纤维。
\[
\begin{array}{c|c|c}
\text{源}&\text{像}&\text{每个非空纤维的大小}\\ \hline
\mathscr R_{L,M+1}&\mathscr R_{L,M}&q_L^e\\
\mathscr C_{L,M+1}&\mathscr R_{L,M}&q_L^{d+e}\\
\mathscr R_{K_\mu,M+1}^{\sigma_\mu}&\mathscr R_{F,M}&2^{2e}\\
\mathscr C_{K_\mu,M+1}^{\sigma_\mu}&\mathscr R_{F,M}&2^{2(d+e)}
\end{array} \tag{7}
\]
前两行来自 (5) 的逐层提升。后两行中，(6) 里精度 \(M+1\) 的修正项在精度 \(M\) 消失。基域部分按前两行约化，而源层的 \(Z\) 分别有 \(2^e\) 或 \(2^{d+e}\) 种选择，故得所列纤维大小。

对固定 \(\mathscr R\) 或固定 \(\mathscr C\) 中任一精度 \(M\) 的类，下列三个条件等价。

- 该类属于 \(\mathscr R_{F,M}(A)\)。
- 该类能提升为一个 \(\sigma_\mu\)-固定的真解。
- 该类能作为相应固定点集的一条逐层相容序列在精度 \(M\) 的分量。

第一项给出一个基域真解，其逐层约化给出后两项。固定的真解逐条目属于 \(\mathbb Z_2\)，所以第二项推出第一项。第三项给出一个固定的上一精度类，故由 (7) 也推出第一项。

## 3. 最优下降精度

所求最大整数为
\[
\boxed{
N=
\begin{cases}
M&\text{每个 }n_i=1,\\
M-1&\text{至少一个 }n_i\ge2.
\end{cases}}
\]
事实上，给定题设中的 \(U\)，令 \(\bar U=U\bmod2^M\)。由 (6)，它与某个 \(\bar V\in\mathscr R_{F,M}(A)\) 模 \(2^{M-1}\) 相同，取 \(\bar V\) 的基域真提升 \(W\) 即可。对于这个给定的 \(U\)，能取 \(N=M\) 的充要条件是 (6) 中的 \(Z=0\)。等价地，将 \(U\) 逐项写为 \(a+b\theta_\mu\)，所有 \(b\) 都须属于 \(2^M\mathbb Z_2\)，或者写成
\[
\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}.
\]
当所有块秩都为一时，\(\mathcal H_0=0\)。在这种块秩下，真解本身也全部下降。若有扩域真解 \(U\)，由可行性判准可取基域真解 \(W_0\)。于是 \(W_0^{-1}U\) 是分块正交矩阵，每块为平方等于 \(1\) 的标量，故每块为 \(1\) 或 \(-1\)。

### 最优性及各类失败的实例

**任意精度的下降反例。** 若某块秩至少为二，取 \(A_i=E_i\)，在该块选两个坐标。给定任意 \(M\ge2\)，置
\[
t=
\begin{cases}
2^{M-1}(1+\theta_{-1})&\mu=-1,\\
2^{M-1}\theta_2&\mu=2.
\end{cases}
\]
两种情形都有 \(t^2\in 2^{2M-1}\mathcal O_\mu\)。取 \(a=1+4z\) 使 \(a^2+t^2=1\)，即令 \(z+2z^2=-t^2/8\)。这个方程模 \(2\) 唯一确定 \(z\)，每次把 \(z\) 改动 \(2^k w\) 时，左侧模 \(2^{k+1}\) 的改变量为 \(2^k w\)，故能逐层解出。又因 \(1+2z\) 可逆，\(z(1+2z)=-t^2/8\) 给出 \(a-1\in2^{2M-2}\mathcal O_\mu\)。

在所选平面上令 \(U\) 为
\[
\begin{pmatrix}a&-t\\t&a\end{pmatrix}
\]
并在其余坐标上取恒等。它是真解，且模 \(2^M\) 固定，因为 \(a\equiv1\pmod{2^M}\)，而 \(\sigma_\mu(t)-t=-2^M\theta_\mu\)。但 \(t\) 的 \(\theta_\mu\) 系数为 \(2^{M-1}\)，故它在精度 \(M\) 没有基域真提升，也无法进入逐层相容的固定序列。这证明界的最优性。在 \((\mu,M)=(-1,2)\) 时，此例基域系数在所选平面上为 \(\begin{psmallmatrix}1&-2\\2&1\end{psmallmatrix}\bmod4\)，其 Gram 矩阵为 \(5I_2\)，说明该系数类属于 \(\mathscr C_{F,2}\) 却无法提升。把同一构造的 \(t,a\) 取自 \(M=2\)，再观察任意精度 \(M\ge3\)，则 \(\sigma_\mu(t)-t=-4\theta_\mu\) 在该精度非零，给出两元素轨道。

**可行性失败。** 当 \(r\ge2\) 时，从两个不同块各选一个坐标 \(a,b\)。令 \(Q\) 在该平面上为 \(\begin{psmallmatrix}1&-2\\2&1\end{psmallmatrix}\)，其余坐标上为恒等，取 \(A_i=QE_iQ^{-1}\)。因 \(Q^{\mathsf T}Q\) 为对角矩阵，这些 \(A_i\) 对称，且两两交换、模 \(2\) 为 \(E_i\)。涉及的两块列跨块项分别含 \(2/5\) 和 \(-2/5\)，因此两块的 \(\kappa_i\) 都为 \(1\)。三个域上均无真解，也无精度 \(M\ge3\) 的有限解，但 \(Q\bmod4\) 是精度 \(2\) 的有限解。当 \(r=1\) 时，\(\kappa_1=0\) 恒成立。

**有限正交条件成立但无法提升。** 取 \(A_i=E_i\)。在任意扩域和任意精度 \(M\ge2\)，将恒等矩阵的一个对角元换成 \(1+2^{M-1}\theta_\mu\)。所得类固定且属于 \(\mathscr C_{K_\mu,M}\)，但其平方长度误差的 \(\theta_\mu\) 系数恰为 \(2^M\)，由 (1) 无法提升。在基域上，\(M\ge3\) 时可用对角元 \(1+2^{M-1}\)，其平方长度误差模 \(2^{M+1}\) 为 \(2^M\)。在基域的 \(M=2\) 层，若有块秩至少为二，可在该块使用上述 Gram 矩阵为 \(5I_2\) 的平面矩阵。若各块秩均为一且 \(\chi=1\)，这层的基域有限类全部可提升。