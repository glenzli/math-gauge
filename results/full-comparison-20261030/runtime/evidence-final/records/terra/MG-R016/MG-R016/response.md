题设不足以推出整体分裂。即使 \(B=R\)，而且每个素点上的右逆都是唯一的，也可能不存在整体右逆。

取任一域 \(k\)，令

\[
R=\{(a_n)_{n\ge1}\in k^{\mathbb N}:\text{序列最终为常数}\},
\qquad
I=\{(a_n)\in R:\text{只有有限项非零}\}.
\]

令 \(A=I\)、\(B=R\)、\(C=R/I\)，并取自然短正合列

\[
0\longrightarrow I\longrightarrow R\xrightarrow{q}R/I\longrightarrow0.
\]

这里 \(B\) 是秩一自由模，\(C\) 由 \(\bar 1=1+I\) 生成；取序列的最终值还给出环同构 \(R/I\cong k\)。

对任意素理想 \(\mathfrak p\)，有两种情形：

- 若 \(I\not\subseteq\mathfrak p\)，则 \(I_{\mathfrak p}=R_{\mathfrak p}\)，所以 \(C_{\mathfrak p}=0\)。此时 \(q_{\mathfrak p}\) 有唯一的右逆，即从零模出发的映射。
- 若 \(I\subseteq\mathfrak p\)，对任意 \(x\in I\)，记其有限支集为 \(S\)，并令 \(e_S\) 是在 \(S\) 上取值 \(1\)、其余位置取值 \(0\) 的序列。于是 \(e_S\in I\subseteq\mathfrak p\)，故 \(1-e_S\notin\mathfrak p\)，而 \((1-e_S)x=0\)。这说明 \(x/1=0\)，从而 \(I_{\mathfrak p}=0\)。因此
  \[
  q_{\mathfrak p}:R_{\mathfrak p}\longrightarrow C_{\mathfrak p}
  \]
  是同构，也有唯一的右逆。

但 \(q\) 没有整体右逆。否则，设 \(b=s(\bar 1)\)，则 \(q(b)=\bar 1\)。对于只在第 \(n\) 项取值 \(1\) 的序列 \(e_n\)，有 \(e_n\in I\)，所以

\[
e_n b=s(e_n\bar 1)=0.
\]

这迫使 \(b\) 的第 \(n\) 项为零。对所有 \(n\) 都如此，故 \(b=0\)，与 \(q(b)=\bar 1\ne0\) 矛盾。

下面可以精确刻画何时存在整体分裂，以及存在时的全部自由度。取 \(C\) 的生成元 \(c\)，令

\[
I=\operatorname{Ann}_R(c),\qquad
\pi:R\longrightarrow C,\quad r\longmapsto rc.
\]

于是 \(C\cong R/I\)。在 \(B\) 自由的条件下，

\[
\boxed{\quad q\text{ 有整体右逆}
\ \Longleftrightarrow\
I=eR\text{ 对某个幂等元 }e\in R\text{ 成立。}\quad}
\]

证明必要性：若 \(s\) 是 \(q\) 的右逆，由于 \(B\) 自由，存在 \(t:B\to R\) 使 \(\pi t=q\)。令 \(\sigma=ts\)、\(u=\sigma(c)\)，则 \(\pi(u)=c\)，因此 \(e=1-u\in I\)。对每个 \(x\in I\)，

\[
xu=\sigma(xc)=0,\qquad x=x(1-u)=xe.
\]

故 \(I=eR\)；又因 \(e\in I\)，有 \(eu=0\)，所以 \(e^2=e\)。

反过来，若 \(I=eR\) 且 \(e^2=e\)，任选 \(b_0\in B\) 使 \(q(b_0)=c\)，则

\[
s_0(rc)=r(1-e)b_0
\]

是良定义的：改变 \(r\) 的代表元只会增加 \(I(1-e)=0\) 中的元素；并且 \(q s_0=I_C\)。

此时所有整体右逆恰好为

\[
s_a(rc)=r\bigl((1-e)b_0+\iota(a)\bigr),
\qquad a\in(1-e)A.
\]

等价地，整体右逆一旦存在，就构成以 \(\operatorname{Hom}_R(C,A)\) 为平移模的仿射空间；这里

\[
\operatorname{Hom}_R(C,A)
\cong \{a\in A:Ia=0\}
=(1-e)A.
\]

任取其中一个右逆 \(s\)，所求的相容同构及其逆显式为

\[
\begin{aligned}
\Phi_s:A\oplus C&\longrightarrow B,
&\Phi_s(a,c')&=\iota(a)+s(c'),\\
\Phi_s^{-1}:B&\longrightarrow A\oplus C,
&\Phi_s^{-1}(b)&=
\bigl(\iota^{-1}(b-sq(b)),\,q(b)\bigr).
\end{aligned}
\]

其中 \(b-sq(b)\in\ker q=\operatorname{im}\iota\)，所以逆映射良定义。

局部条件的不足也可由上述判据看出：局部环中的幂等元只能是 \(0\) 或 \(1\)，故每个 \(q_{\mathfrak p}\) 分裂等价于

\[
I_{\mathfrak p}=0\quad\text{或}\quad I_{\mathfrak p}=R_{\mathfrak p}
\qquad\text{对每个 }\mathfrak p.
\]

这并不保证 \(I\) 由一个整体幂等元生成，前面的例子正是如此。

例如，若额外假设 \(I\) 有限生成，即 \(C\) 有限表示，则局部条件足以推出整体分裂。事实上，当 \(I\subseteq\mathfrak p\) 时，\(I_{\mathfrak p}=0\) 和有限生成性给出某个 \(t\notin\mathfrak p\) 满足 \(tI=0\)。因此没有素理想包含 \(I+\operatorname{Ann}_R(I)\)，从而该和等于 \(R\)。写 \(1=e+u\)，其中 \(e\in I\)、\(u\in\operatorname{Ann}_R(I)\)，便得到 \(e^2=e\) 且 \(I=eR\)。