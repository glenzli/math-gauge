对每个 \(x\in H\)，构造将是

\[
Px:=\lim_{F}P_Fx,
\]

其中极限按有限子集的包含关系取，且在范数下成立。关键是利用投影的变分不等式，把有限问题的最优值之差转化为投影点之间的距离估计。

先说明所需的投影事实。若 \(D\subseteq H\) 非空、闭且凸，则每个 \(x\in H\) 在 \(D\) 中有唯一最近点 \(p\)。事实上，令

\[
a=\inf_{z\in D}\|x-z\|,
\]

并取 \(\|x-z_n\|\to a\) 的序列 \(z_n\in D\)。由凸性，\((z_n+z_m)/2\in D\)；平行四边形恒等式因此给出

\[
\begin{aligned}
\|z_n-z_m\|^2
&=2\|x-z_n\|^2+2\|x-z_m\|^2
 -4\left\|x-\frac{z_n+z_m}{2}\right\|^2\\
&\le 2(\|x-z_n\|^2-a^2)+2(\|x-z_m\|^2-a^2).
\end{aligned}
\]

所以 \((z_n)\) 是 Cauchy 序列，其极限 \(p\) 属于 \(D\) 且满足 \(\|x-p\|=a\)。同一恒等式表明最近点唯一。

此外，对任意 \(z\in D\) 和 \(0<t\le1\)，点 \(p+t(z-p)\) 属于 \(D\)。由 \(p\) 的最优性，

\[
0\le \|x-p-t(z-p)\|^2-\|x-p\|^2
=-2t\langle x-p,z-p\rangle+t^2\|z-p\|^2.
\]

除以 \(t\) 并令 \(t\downarrow0\)，得到

\[
\langle x-p,z-p\rangle\le0.
\]

等价地，

\[
\boxed{\quad
\|x-z\|^2\ge \|x-p\|^2+\|z-p\|^2
\qquad(z\in D).
\quad} \tag{1}
\]

现在固定 \(x\in H\)，记

\[
p_F=P_Fx,\qquad s_F=\|x-p_F\|^2.
\]

假设保证每个 \(C_F\) 非空；它又是闭凸集，因此 \(p_F\) 确实存在且唯一。若 \(F\subseteq G\)，则 \(C_G\subseteq C_F\)，从而 \(s_F\le s_G\)。另一方面，由假设中的 \(z_F\)，

\[
s_F\le \|x-z_F\|^2\le(\|x\|+B)^2.
\]

因此有限的实数

\[
s_x:=\sup_{F\subseteq I,\;F\text{ 有限}}s_F
\]

存在。

对于 \(F\subseteq G\)，因 \(p_G\in C_F\)，将 (1) 用于 \(D=C_F\)、\(p=p_F\)、\(z=p_G\)，可得

\[
\|p_G-p_F\|^2\le s_G-s_F. \tag{2}
\]

这说明 \((p_F)_F\) 是范数 Cauchy 网。具体地，给定 \(\varepsilon>0\)，取有限集 \(F_0\) 使

\[
s_x-s_{F_0}<\frac{\varepsilon^2}{4}.
\]

若 \(F,G\supseteq F_0\)，令 \(K=F\cup G\)。由 (2) 及 \(s_F,s_G\ge s_{F_0}\)，

\[
\|p_F-p_G\|
\le \|p_F-p_K\|+\|p_K-p_G\|
\le 2\sqrt{s_x-s_{F_0}}<\varepsilon.
\]

Hilbert 空间的完备性于是给出范数极限 \(p=\lim_Fp_F\)。这里对网的完备性也可直接验证：取递增的有限集 \(F_n\)，使相应尾部的直径小于 \(1/n\)；序列 \(p_{F_n}\) 的极限就是整个网的极限。

对每个 \(i\in I\)，当 \(F\supseteq\{i\}\) 时都有 \(p_F\in C_i\)。由 \(C_i\) 的闭性，\(p\in C_i\)，所以 \(p\in C\)。又因为递增网 \((s_F)\) 收敛到其上确界，

\[
\|x-p\|^2=\lim_F s_F=s_x.
\]

任取 \(z\in C\)，由于 \(z\in C_F\) 对所有有限 \(F\) 都成立，

\[
s_F\le\|x-z\|^2,
\qquad\text{故}\qquad
\|x-p\|^2=s_x\le\|x-z\|^2.
\]

因此 \(p\) 是 \(x\) 在 \(C\) 上的最近点。集合 \(C\) 是非空闭凸集，故该最近点唯一。定义 \(Px=p\)，便同时得到所需的范数收敛

\[
\boxed{\quad P_Fx\longrightarrow Px.\quad}
\]

有限问题还给出全局最优值及恢复误差估计：

\[
\boxed{\quad
\|x-Px\|^2
=\sup_{F\text{ 有限}}\|x-P_Fx\|^2,
\qquad
\|x-Px\|
=\sup_{F\text{ 有限}}\|x-P_Fx\|.
\quad}
\]

确实，由 \(Px\in C_F\) 和 (1)，每个有限 \(F\) 都满足

\[
\boxed{\quad
\|P_Fx-Px\|^2
\le \|x-Px\|^2-\|x-P_Fx\|^2.
\quad} \tag{3}
\]

特别地，取 \(x=0\) 可知 \(\|P0\|\le B\)，所以原来的统一有界条件还保证 \(C\) 中存在范数不超过 \(B\) 的点。

最后证明非扩张性。对固定的有限 \(F\)，令 \(p=P_Fx\)、\(q=P_Fy\)。投影的变分不等式分别给出

\[
\langle x-p,q-p\rangle\le0,
\qquad
\langle y-q,p-q\rangle\le0.
\]

相加整理后，

\[
\|p-q\|^2\le\langle x-y,p-q\rangle.
\]

令 \(F\) 沿有限子集网趋于极限，得到更强的不等式

\[
\|Px-Py\|^2\le\langle x-y,Px-Py\rangle.
\]

再由 Cauchy–Schwarz 不等式，若 \(Px\ne Py\) 则可除以 \(\|Px-Py\|\)；相等时结论显然。因此

\[
\boxed{\quad \|Px-Py\|\le\|x-y\|\qquad(x,y\in H).\quad}
\]