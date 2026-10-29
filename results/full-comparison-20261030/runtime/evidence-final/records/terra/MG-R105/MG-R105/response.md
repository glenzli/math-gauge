记
\[
T:Q\longrightarrow H,\qquad T(q(x))=Ax.
\]
若 \(q(x)=q(x')\)，则 \(x-x'\in\ker A\)，故 \(Ax=Ax'\)，所以 \(T\) 定义良好。它是单射，并满足
\[
\|q(x)\|_A=\|Tq(x)\|_H.
\]
因此 \(\|\cdot\|_A\) 是 \(Q\) 上的范数，且 \(T\) 是线性等距映射。

令
\[
C=\overline{A(E)}\subseteq H.
\]
这是 \(H\) 的闭线性子空间，因而是完备空间。可以取
\[
\widehat Q=C,\qquad
\iota:Q\to C,\quad \iota(q(x))=Ax,
\]
并令 \(J:C\to H\) 为包含映射。此时 \(\iota\) 线性等距，像 \(A(E)\) 在 \(C\) 中稠密，故 \((\widehat Q,\iota)\) 是所求的完备化；同时
\[
J\iota q=A,\qquad J(\widehat Q)=\overline{A(E)}.
\]

对**任意固定的完备化** \((\widehat Q,\iota)\)，也可直接构造满足要求的 \(J\)。给定 \(u\in\widehat Q\)，取 \(\xi_n\in Q\) 使 \(\iota\xi_n\to u\)，定义
\[
Ju=\lim_{n\to\infty}T\xi_n.
\]
由于
\[
\|T\xi_n-T\xi_m\|_H
=\|\iota\xi_n-\iota\xi_m\|_{\widehat Q},
\]
右侧极限存在；同一等式也说明它与逼近序列的选择无关。由此得到线性等距映射 \(J\)，且 \(J\iota q=A\)。

这个 \(J\) 的像包含 \(A(E)\)，并且作为完备空间 \(\widehat Q\) 的等距像，它在 \(H\) 中是闭集；另一方面，构造中的极限都属于 \(C\)。因此
\[
\boxed{J(\widehat Q)=C=\overline{A(E)}}.
\]
若另有线性等距映射 \(J'\) 满足 \(J'\iota q=A\)，则 \(J'\) 与 \(J\) 在稠密子空间 \(\iota(Q)\) 上相同。两者连续，故在整个 \(\widehat Q\) 上相同。这证明了固定完备化时的唯一性。

现在固定 \(y\in H\)，令 \(d=\inf_{v\in C}\|y-v\|_H\)。取 \(v_n\in C\) 使
\[
\|y-v_n\|_H^2\le d^2+\frac1n.
\]
由平行四边形恒等式及 \((v_n+v_m)/2\in C\)，
\[
\begin{aligned}
\|v_n-v_m\|_H^2
&=2\|y-v_n\|_H^2+2\|y-v_m\|_H^2
 -4\left\|y-\frac{v_n+v_m}{2}\right\|_H^2\\
&\le \frac2n+\frac2m.
\end{aligned}
\]
因此 \(v_n\) 收敛于某个 \(v\in C\)，且 \(\|y-v\|_H=d\)。对任意 \(w\in C\) 和 \(t\in\mathbb R\)，极小性给出
\[
0\le \|y-(v+tw)\|_H^2-\|y-v\|_H^2
=t^2\|w\|_H^2-2t\langle y-v,w\rangle,
\]
所以 \(y-v\perp C\)。反过来，若 \(v\in C\) 且 \(y-v\perp C\)，则对每个 \(w\in C\)，
\[
\|y-w\|_H^2=\|y-v\|_H^2+\|v-w\|_H^2.
\]
故 \(v\) 是唯一极小点。记它为 \(P_Cy\)；它由以下条件唯一确定：
\[
P_Cy\in C,\qquad y-P_Cy\in C^\perp.
\]

由这个刻画，线性组合的正交分解仍是正交分解，因此 \(P_C\) 是线性的。勾股定理又给出
\[
\|P_Cy\|_H\le \|y\|_H.
\]
于是所求的恢复映射为
\[
\boxed{R(y)=J^{-1}(P_Cy)}.
\]
它是唯一极小点，线性，且对所有 \(y,z\in H\)，
\[
\|R(y)-R(z)\|_{\widehat Q}
=\|P_C(y-z)\|_H\le \|y-z\|_H,
\]
即 \(R\) 是 \(1\)-Lipschitz 映射。

由于 \(A(E)\) 在 \(C\) 中稠密，取 \(a_n\in A(E)\) 使 \(a_n\to P_Cy\) 即得
\[
\boxed{
\min_{u\in\widehat Q}\|y-Ju\|_H
=\|y-P_Cy\|_H
=\inf_{x\in E}\|y-Ax\|_H.
}
\]

最后，对每个 \(x\in E\)，正交分解给出
\[
\|y-Ax\|_H^2
=\|y-P_Cy\|_H^2+\|P_Cy-Ax\|_H^2.
\]
因此，原空间中的极小点存在当且仅当
\[
\boxed{
P_Cy\in A(E)
\quad\Longleftrightarrow\quad
R(y)\in\iota(Q)
\quad\Longleftrightarrow\quad
y\in A(E)+A(E)^\perp.
}
\]
其中最后一个等价关系用到了 \(A(E)^\perp=C^\perp\)。

当上述条件成立时，任选 \(x_0\in E\) 满足 \(Ax_0=P_Cy\)，则全部极小点恰为
\[
\boxed{M_y=x_0+\ker A.}
\]
特别地，所有 \(y\in H\) 都在原空间中有极小点，当且仅当 \(A(E)\) 是闭的。