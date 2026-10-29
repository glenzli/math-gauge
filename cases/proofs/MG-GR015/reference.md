# 自由模的商记录、完成支持与提升：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 分裂列的完成

判定：true。

映射 (a,c)↦ι(a)+s(c) 是 A⊕C→B 同构，逆为 b↦(ι^{-1}(b−sqb),qb)。它把 t^n(A⊕C) 对应到 t^nB，故每层商及相容族均分解为两因子的积。于是 B̂≅Â⊕Ĉ，完成映射是包含、投影；提升恰为 ŝ(ĉ)+ι̂(â)。若 s′−s=ιh，则所选提升差为 ι̂ĥ(ĉ)。

判准：完成分解逐层相容；全部提升及截面差。

## S2 可数自由模的完成模型

判定：construction。

答案是 R̂^{(N)}_res={ (a_i): 对每个 n，只有有限多个 i 满足 a_i mod t^n≠0 }。相容商记录在每个坐标给相容多项式余数，因此给唯一幂级数 a_i；第 n 层的有限支撑给所列条件。反之条件使第 n 层坐标余数形成 M/t^nM 的元素，逐坐标相容，构造互逆。加法的非零模 t^n 支撑包含两支撑之并，乘固定幂级数的支撑包含原支撑；故自然有 R̂ 模结构。不能把它写成无条件全积，也不是只容许有限个非零幂级数的直和。

判准：每层有限支持等价条件；两个方向及模运算。

## S3 有界对角指数

判定：true。

原 ι 单射，因为 R 为整环。C=⊕_i R/(t^{ν_i}) 且 t^MC=0，所以 Ĉ=C（从 n≥M 后商系统恒定）。任一 c 仅有限多个非零坐标，为这些坐标选次数<ν_i 的多项式给 B̂ 中提升。若 y∈ker q̂，则每个 y_i 可被 t^{ν_i} 整除，令 x_i=t^{−ν_i}y_i；对每个 n，x_i mod t^n 非零只能发生在 y_i mod t^{n+M} 非零的有限集合，故 x∈Â。反之所有这样的 ι̂x 在核中；逐坐标整环性质给单射。因此提升全体是一个所选多项式提升加 ι̂Â。ν_i=0 的商为零，M=0 同样成立。

判准：除法后的受限支持；核像等式及满射。

## S4 整体对象与全部恢复目标

判定：false。

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

判准：Test the requested completed short exact sequence for the actual t-adic completion M ↦ lim M/t^n M.；A counterexample must retain a field k, R=k[t], countably generated free A and B, and a genuine short exact original sequence.；Verify the claimed failure on the maps induced by the original row, including compatibility of any completed witness.。

## S5 原模与完成的值域

判定：false。

不满射。取坐标 a_i=t^i。对每个 n，只有 i<n 的模 t^n 坐标非零，故 S2 给完成元素，第 n 层可由 Σ_{i<n}t^ie_i 代表。但其所有坐标非零，不是 M 中有限支撑向量。典范映射单射：非零有限向量某非零坐标有有限 t 阶数，不可能在所有 t^nM 中。

判准：相容商代表；排除原模有限支持。

## S6 再次完成

判定：true。

成立。S2 坐标模型中约化模 t^n 的像正是有限支撑的 (R/t^n) 序列。核恰为 t^nM̂：若各坐标可除以 t^n，商序列在模 t^m 的非零支持包含原序列模 t^{m+n} 的支持，所以仍受限。因而 M̂/t^nM̂≅M/t^nM，且同构与约化相容。取极限得到原定义的 M̂；复合典范映射逐坐标每层均恒等，故是所求同构。

判准：核等于 t^nM̂；自然约化兼容。
