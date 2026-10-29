# 参考论证：自由呈示的完备化与相容恢复

全称目标不成立。以下反例中两端呈示模都是实际的可数秩自由模，但完备化后的序列在中间不正合。完整验证这一反例已解决题面的全称目标。

## 原短正合列

保留任意域 $k$ 和 $R=k[t]$，取

$$A=\bigoplus_{i\ge0}Rf_i,\qquad B=\bigoplus_{i\ge0}Re_i,
\qquad\iota(f_i)=t^i e_i,$$

并令 $C=B/\iota(A)$，$q$ 为商映射。每个向量只有有限多个非零坐标，所以 $\iota$ 是良定义的 $R$ 线性映射。由于 $k[t]$ 为整环且 $t^i\ne0$，逐坐标消去 $t^i$ 可知 $\iota$ 单射。商映射满射，其核按定义为 $\iota(A)$，故原行短正合。$A,B$ 的所列基均由自然数编号。

## 完备化中的一个相容元素

对 $m\ge0$，置

$$v_m=\sum_{0\le i<m}t^i e_i\in B,\qquad
y_m=v_m+t^mB\in B/t^mB.$$

当 $n\le m$ 时，

$$v_m-v_n=\sum_{n\le i<m}t^i e_i
=t^n\sum_{n\le i<m}t^{i-n}e_i\in t^nB.$$

故 $y=(y_m)\in\widehat B$。另一方面，

$$v_m=\iota\left(\sum_{0\le i<m}f_i\right),$$

所以 $q(v_m)=0$，从而 $\widehat q(y)=0$。这里每一层代表都是有限支撑向量；没有把无限和当作 $B$ 的元素。

## 这个元素没有完备化原像

假设 $a\in\widehat A$ 满足 $\widehat\iota(a)=y$。对每个 $m\ge1$，选择有限支撑代表 $u_m\in A$ 表示 $a_m\in A/t^mA$。其相容性给出

$$u_m-u_1\in tA\qquad(m\ge1). \tag{1}$$

因而在每个坐标上，$u_m$ 与 $u_1$ 的常数项相等。映射等式则给出

$$\iota(u_m)-v_m\in t^mB. \tag{2}$$

固定任意 $i\ge0$，在 (2) 中取 $m=i+1$ 并读取第 $i$ 坐标的 $t^i$ 系数。$\iota(u_{i+1})$ 的该坐标为 $t^i(u_{i+1})_i$，而 $(v_{i+1})_i=t^i$。右侧的 $t^{i+1}$ 倍数没有 $t^i$ 项，因此

$$[(u_{i+1})_i]_{t^0}=1.$$

结合 (1)，得到 $[(u_1)_i]_{t^0}=1$ 对所有 $i\ge0$ 成立。可是 $u_1$ 是直和中的向量，只有有限多个非零坐标；在其支撑之外常数项必为零。这与域中 $0\ne1$ 矛盾。

因此 $y\in\ker\widehat q$ 而 $y\notin\operatorname{im}\widehat\iota$，完备化序列在中间不正合。这个结论不依赖于尚未讨论的右端满射性，也不把仅有逐层原像误作相容原像。

## 与题面和形式化的对应

任一 $R$ 线性映射 $f:M\to N$ 满足 $f(t^nM)\subseteq t^nN$，故确实诱导商映射；这些映射与所有自然约化交换。Lean 与题面均直接以 $n\ge0$ 的商模 $M/t^nM$ 及其相容族定义完备化，并定义原行映射诱导的完备化映射。上述矛盾全部发生在 $n\ge1$。

代码证明了原自由模上的单射与商正合、每个有限代表、所有约化等式、核见证及不存在相容原像；具体对应见 formal/COVERAGE.md。没有把所需原像或正合性存入证书字段。

完备化及其有限生成范围的公开背景见 [Stacks Project, 00MA](https://stacks.math.columbia.edu/tag/00MA)。本反例和上述系数论证独立展开，不以该背景结果作为证明前提，也未使用未公开 OET 材料。人工审定仍待进行。
