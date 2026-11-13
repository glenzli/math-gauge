# 同时分块与二次扩张上的下降

固定正整数 \(r,n_1,\ldots,n_r\)，令 \(d=\sum_i n_i\)。将标准坐标依次分成区间 \(I_1,\ldots,I_r\)，其中 \(|I_i|=n_i\)，令 \(E_i\) 为坐标子空间 \(\mathbb Z_2^{I_i}\) 上的标准投影。给定
\[
A_i\in M_d(\mathbb Z_2),\qquad A_i^{\mathsf T}=A_i,
\qquad A_iA_j=A_jA_i,
\qquad A_i\equiv E_i\pmod2.
\]
不假设 \(A_i\) 幂等或 \(\sum_iA_i=I_d\)。

令 \(F=\mathbb Q_2\)，并对 \(\mu\in\{-1,2\}\) 置
\[
K_\mu=\mathbb Q_2(\theta_\mu),\qquad \theta_\mu^2=\mu,
\qquad \mathcal O_\mu=\mathbb Z_2[\theta_\mu],
\qquad \sigma_\mu(\theta_\mu)=-\theta_\mu.
\]
对 \(L\in\{F,K_{-1},K_2\}\)，以 \(\mathcal O_L\) 表示整数环，定义
\[
\mathscr S_L(A)=\left\{U\in\operatorname{GL}_d(\mathcal O_L):
U\equiv I_d\pmod{2\mathcal O_L},\quad U^{\mathsf T}U=I_d,
\quad[U^{\mathsf T}A_iU,E_j]=0\ (\forall i,j)\right\}.
\]
对每个整数 \(M\ge2\)，定义
\[
\mathscr R_{L,M}(A)=\{U\bmod2^M\mathcal O_L:U\in\mathscr S_L(A)\},
\]
\[
\mathscr C_{L,M}(A)=\left\{\bar U\in\operatorname{GL}_d(\mathcal O_L/2^M\mathcal O_L):
\bar U\equiv I_d\pmod{2\mathcal O_L},\quad
\bar U^{\mathsf T}\bar U=I_d,
\quad[\bar U^{\mathsf T}A_i\bar U,E_j]=0\ (\forall i,j)\right\}.
\]
\(\sigma_\mu\) 逐条目作用于 \(K_\mu\) 上的这些集合。基域上的有限集合经自然包含视为扩域上的矩阵类。

给出下列目标的完整解答与证明。

1. 对全部允许的输入与参数，给出 \(\mathscr S_L(A)\) 的明确可行性判准，以及 \(\mathscr R_{L,M}(A)\)、\(\mathscr C_{L,M}(A)\) 的闭式精确基数和空集条件。可行性判准须可由 \(A_i\bmod4\) 有限计算；对 \(\bar U\in\mathscr C_{L,M}(A)\)，还须给出其属于 \(\mathscr R_{L,M}(A)\) 的可核验必要充分条件。

2. 确定 \(\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\)、\(\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\) 的具体矩阵类，给出它们与基域上相应集合的精确关系、固定点数及 \(\langle\sigma_\mu\rangle\) 轨道数。对 \(\mathscr R,\mathscr C\) 及各自的固定点集，确定从精度 \(M+1\) 到 \(M\) 的约化像与全部非空纤维大小；同时刻画固定矩阵类中，哪些能提升为 \(\sigma_\mu\)-固定的真正解，哪些能作为一条逐层相容的固定矩阵类序列在精度 \(M\) 的分量。

3. 对固定的块秩、\(\mu\) 和 \(M\ge2\)，求满足下述性质的最大整数 \(N\in\{0,\ldots,M\}\)：对每个合法 \(A\) 和每个满足
   \[
   U\in\mathscr S_{K_\mu}(A),\qquad
   \sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}
   \]
   的 \(U\)，存在 \(W\in\mathscr S_F(A)\) 使
   \[
   U\equiv W\pmod{2^N\mathcal O_\mu}.
   \]
   对给定的这样的 \(A,U\)，另给出能取 \(N=M\) 的必要充分条件。证明所得界的最优性；若某种块秩允许精确下降，也须确定。所有否定结论均须给出实际例子，涉及任意精度的界须有相应的统一构造。

可援引标准局部域定理，但须写明所用形式与适用条件。不要求 Lean；接受任何完整、有效的证明路线。
