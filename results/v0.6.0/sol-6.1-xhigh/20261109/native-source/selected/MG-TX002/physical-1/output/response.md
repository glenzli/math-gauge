结论成立。可以构造一个势函数，使每一步反链大小与目标平均值之差恰好等于势函数的变化。

对整数坐标定义权重
\[
w(i,j)=ab+a+b-bi-aj,
\qquad
F(A)=\sum_{(i,j)\in A}w(i,j).
\]
下面证明
\[
\boxed{F(R(A))-F(A)=ab-(a+b)|A|.}\tag{1}
\]

设 \(k=|A|\)。将反链中的点排列为
\[
A=\{(i_1,j_1),\ldots,(i_k,j_k)\},
\qquad
i_1<\cdots<i_k,\quad j_1>\cdots>j_k.
\]
再约定 \(i_0=0,\ j_{k+1}=0\)。由补集极小元的定义，
\[
R(A)=
\bigl\{(i_t+1,j_{t+1}+1):0\le t\le k\bigr\}\cap P.
\tag{2}
\]
事实上，这些落在 \(P\) 中的点互不可比、不属于 \(I(A)\)，且每个不属于 \(I(A)\) 的点都大于等于其中某一点。空反链时，公式同样给出 \(R(\varnothing)=\{(1,1)\}\)。

公式 (2) 中可能落在 \(P\) 外的点只有
\[
(1,b+1),\qquad(a+1,1),
\]
而它们的权重均为 \(0\)。因此，求权重和时可以保留全部候选点，得到
\[
\begin{aligned}
F(R(A))
&=\sum_{t=0}^{k}w(i_t+1,j_{t+1}+1)\\
&=\sum_{t=0}^{k}\bigl(ab-bi_t-aj_{t+1}\bigr)\\
&=(k+1)ab-b\sum_{t=1}^{k}i_t-a\sum_{t=1}^{k}j_t.
\end{aligned}
\]
另一方面，
\[
F(A)=k(ab+a+b)-b\sum_{t=1}^{k}i_t-a\sum_{t=1}^{k}j_t.
\]
两式相减，便得到 (1)。

最后，在任意轨道 \(O\) 上求和。由于 \(R\) 循环置换轨道中的反链，势函数的变化总和为零：
\[
0=\sum_{A\in O}\bigl(F(R(A))-F(A)\bigr)
=ab|O|-(a+b)\sum_{A\in O}|A|.
\]
故
\[
\boxed{\frac1{|O|}\sum_{A\in O}|A|=\frac{ab}{a+b}}.
\]