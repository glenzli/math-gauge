# 对角呈示的完成与商拓扑

设 \(k\) 为任意域，\(R=k[t]\)，\(S=k[[t]]\)。给定任意非负整数列 \((\nu_n)_{n\ge1}\)，令

\[
A=\bigoplus_{n\ge1}Rf_n,\qquad B=\bigoplus_{n\ge1}Re_n,\qquad
\iota(f_n)=t^{\nu_n}e_n,\qquad C=B/\iota(A),
\]

并记商映射为 \(q:B\to C\)。对任意 \(R\) 模 \(M\)，定义

\[
\widehat M=\varprojlim_{m\ge1}M/t^mM,
\]

过渡映射为自然约化，典范映射记为 \(\eta_M:M\to\widehat M\)。映射 \(\iota,q\) 诱导 \(\widehat\iota,\widehat q\)。各完成上的 \(S\) 作用由第 \(m\) 层的 \(S/(t^m)\) 作用给出。置

\[
Q=\widehat B/\operatorname{im}\widehat\iota,\qquad
p:Q\longrightarrow\widehat C,\qquad
p\bigl(b+\operatorname{im}\widehat\iota\bigr)=\widehat q(b),\qquad E=\ker p.
\]

另有典范映射 \(j:C\to Q\)，由 \(j(q(b))=\eta_B(b)+\operatorname{im}\widehat\iota\) 定义。模 \(N\) 的 \(t\) 进拓扑以 \(t^mN\) 为零点邻域基；称其分离是指 \(\bigcap_{m\ge1}t^mN=0\)。

请完成以下三个整体目标，并证明全部结论。结论须适用于每一个给定的指数列；所需的充要条件直接用该指数列表述。无需 Lean。

1. 给出 \(\widehat A,\widehat B,\widehat C\) 的具体坐标模型及其与相容商记录之间的同构，写出诱导映射。确定完成列在各处的正合性、\(\operatorname{im}\widehat\iota\) 在 \(\widehat B\) 中的闭包以及 \(\widehat q\) 的每个纤维，并给出完成列短正合的充要条件。

2. 给出 \(E\) 的明确坐标模型，确定 \(j\) 的核和像、\(Q\) 中所有被某个 \(t^r\)（\(r\ge1\)）杀死的元素及 \(E\) 的 \(S\) 模挠性。判定 \(p\) 的满射性，并分别给出 \(E=0\) 与 \(p\) 存在 \(S\) 线性右逆的充要条件。

3. 对每个 \(m\ge1\)，确定由 \(p\) 诱导的 \(Q/t^mQ\to\widehat C/t^m\widehat C\)。计算 \(\bigcap_{m\ge1}t^mQ\)，确定 \(\widehat Q,\widehat E\) 及对应的典范映射，并确定 \(p\) 诱导的完成映射。最后，将 \(E\) 自身的 \(t\) 进拓扑与它从 \(Q\) 的 \(t\) 进拓扑继承的子空间拓扑作比较，确定自身拓扑的分离性及这两种拓扑相同的充要条件。
