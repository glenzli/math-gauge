# 整族恢复、固定点与一致性的范围

请按 S 编号逐项作答。所有阶段均必答；给出所要求的证明、构造或分类。判断命题时，给出结论及完整证明或满足全部前提的反例。援引前项或标准定理时说明实际适用条件。无需 Lean。



## S1 紧域上的整族极限

设非空紧度量空间 X、完备度量空间 Y、I 上真滤子 F，映射 f_i:X→Y 有共同 K-Lipschitz 常数。若每个点的推前滤子 Cauchy，构造极限 f，并证明沿 F 在 X 上一致收敛及 f 为 K-Lipschitz。

## S2 恢复与固定点

在 S1 中令 Y=X，且共同常数 q<1。证明每个 f_i 和极限 f 都有唯一固定点 x_i、x_*，并证明 x_i→x_* 沿 F。给出由 sup_x d(f_i(x),f(x)) 控制固定点误差的估计。

## S3 同步复合的极限

设 X,Y 为紧度量空间、Z 完备；f_i:X→Y 共同 K-Lipschitz，g_i:Y→Z 共同 L-Lipschitz；沿同一真滤子它们分别在每点 Cauchy。证明 g_i∘f_i 在 X 上一致趋于 g∘f，并给统一误差界。

## S4 整体对象与全部恢复目标

判定下面所列目标在给定条件下是否成立。若成立，完成全部构造、分类与性质的证明；若不成立，给出满足全部给定条件的反例。

在 ZFC 中，设 $X,Y$ 为度量空间，$Y$ 完备，$D\subset X$ 稠密。设 $I$ 为集合，$\mathcal F$ 是 $I$ 上的真滤子，$K\in\mathbb R_{\geq0}$，且给定映射族 $f_i:X\to Y$ 满足
\[
d_Y(f_i(x),f_i(x'))\leq Kd_X(x,x')
\qquad(i\in I,\ x,x'\in X).
\]
对每个 $d\in D$，假设推前滤子 $(i\mapsto f_i(d))_*\mathcal F$ 在 $Y$ 中是 Cauchy 滤子。记 $\iota:X\to\widehat X$ 为度量完备化映射。

研究这些观测能否唯一确定一个 $K$-Lipschitz 映射 $F:\widehat X\to Y$，满足
\[
f_i(d)\longrightarrow F(\iota d)\quad\text{沿 }\mathcal F
\qquad(d\in D).
\]
同时构造每个 $f_i$ 到 $\widehat X$ 的唯一 $K$-Lipschitz 延拓 $\widehat f_i$，并证明它们对每个紧集 $C\subset\widehat X$ 沿 $\mathcal F$ 一致趋于 $F|_C$。

还要确定同步改变输入时的结论：对于任意 $u:I\to\widehat X$ 和 $a\in\widehat X$，若 $u\to a$ 沿 $\mathcal F$，是否有
\[
\widehat f_i(u(i))\longrightarrow F(a)\quad\text{沿 }\mathcal F?
\]

## S5 全完成域的一致性

在 S4 原条件下，判定所有延拓 f̂_i 是否必在整个 X̂ 上一致趋于 F。

## S6 全有界子集

在 S4 原条件下，令 A⊂X̂ 仅全有界，不要求 A 闭。判定 f̂_i 是否仍沿 F 在 A 上一致趋于 F|_A。
