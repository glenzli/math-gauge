# 参考形式化与论证

取 $A,B$ 为交换环 $R$ 的理想，$q:R\to R/B$ 为商映射。理想像保持乘法：一边由乘积生成元 $q(a)q(a')=q(aa')$ 得到，另一边把像理想中的元素写成有限线性组合，再展开乘积。归纳得
\[
(q(A))^r=q(A^r).
\]
同时 $q(K)=0$ 当且仅当 $K\subseteq\ker q=B$。因此
\[
(q(A))^r=0\quad\Longleftrightarrow\quad A^r\subseteq B.
\]
代入 $A=I,B=I^{n+1},r=n+1$，由自身包含得到 $J_n^{n+1}=0$。这里没有假设 $I$ 在原环中幂零。

若 $m\le n$，理想乘法给出 $I^{n+1}\subseteq I^{m+1}$，故商同态 $\rho_{m,n}$ 良定。由商映射的满射性及 $\rho_{m,n}q_n=q_m$，理想像复合满足
\[
\rho_{m,n}(q_n(I))=(\rho_{m,n}q_n)(I)=q_m(I).
\]
对 $x\in R$，两复合同态均把 $q_n(x)$ 送至 $q_l(x)$；$q_n$ 满射，故同态相等。

以上论证允许零环、$I=0$、$I=R$ 和 $n=0$。当 $n=0$ 时 $Q_0=R/I$ 且 $J_0=0$。没有使用 Noether 性、有限生成性、素性或 $R$ 为整环。

形式化见 formal/Reference.lean。`residual_power_zero_iff` 是作者选择的辅助桥梁，候选不必采用这一声明或路线；最终三个目标均须覆盖。
