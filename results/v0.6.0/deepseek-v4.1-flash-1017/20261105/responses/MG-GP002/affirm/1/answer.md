KEEP

上一版 S1–S6 的全部答案与结论维持不变，尤其 S5 的否定结论不变。本轮重点断言“存在含 \(\alpha_*\) 的开区间 \(J\)、有限 \(s\ge0\) 与有限 \(C\) 使该估计对所有无理 \(\alpha\in J\) 一致成立”为假。核查依据如下，且与上一版 S5 的结论一致。

任取含 \(\alpha_*\) 的开区间 \(J\)。由有理数稠密性，取
\[
\frac pq\in J,\qquad q\ge1.
\]
设 \(s\ge0\) 与 \(C<\infty\) 任意。若 \(C\le0\)，取任一非零 \(u\in C^\infty_0(\mathbb T^2)\)，则右端非正而左端为正，估计已不可能；故设 \(C>0\)。因 \(J\) 开，存在 \(\varepsilon>0\) 使
\[
\left(\frac pq-\varepsilon,\frac pq+\varepsilon\right)\subset J.
\]
取无理数 \(\delta\)，满足
\[
0<|\delta|<\min\left\{\varepsilon,\frac1{2\pi q\,\langle(q,-p)\rangle^s C}\right\},
\]
并令
\[
\alpha=\frac pq+\delta\in J\setminus\mathbb Q.
\]
取频率 \(k=(q,-p)\ne0\) 及
\[
u(y)=e^{2\pi i(q,-p)\cdot y}.
\]
则 \(u\in C^\infty_0(\mathbb T^2)\)，且 \(\|u\|_{L^2}=1\)。同时
\[
N_\alpha u=2\pi i(\alpha q-p)u=2\pi i q\delta\,u,
\]
故
\[
\|N_\alpha u\|_{H^s}
=2\pi q|\delta|\,\langle(q,-p)\rangle^s
<\frac1C.
\]
于是
\[
C\|N_\alpha u\|_{H^s}<1=\|u\|_{L^2},
\]
与所要求的一致估计矛盾。

因此不存在题述的开区间 \(J\)、有限 \(s\ge0\) 与有限 \(C\)；S5 的判定仍为否定。上一版其余各阶段的答案无需改动。