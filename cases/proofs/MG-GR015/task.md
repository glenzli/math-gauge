# 自由模的商记录、完成支持与提升

请按 S 编号逐项作答。所有阶段均必答；给出所要求的证明、构造或分类。判断命题时，给出结论及完整证明或满足全部前提的反例。援引前项或标准定理时说明实际适用条件。无需 Lean。



## S1 分裂列的完成

设 R=k[t]，0→A→B→C→0 为任意 R 模短正合列，另给 R 线性截面 s:C→B。证明完成列短正合，构造每个 ĉ∈Ĉ 的全部提升，并说明更换 s 如何改变所选提升。

## S2 可数自由模的完成模型

令 M=⊕_{i≥0}Re_i。把 M̂ 具体识别为 R̂=k[[t]] 的序列族：准确给出允许的支持条件、加法和标量作用，并证明与全部相容商记录双向互逆。

## S3 有界对角指数

取 A=⊕Rf_i、B=⊕Re_i，ι(f_i)=t^{ν_i}e_i，其中 0≤ν_i≤M 为固定整数界，C=coker ι。证明完成列短正合，并用 S2 的坐标模型写出全部提升。

## S4 整体对象与全部恢复目标

判定下面所列目标在给定条件下是否成立。若成立，完成全部构造、分类与性质的证明；若不成立，给出满足全部给定条件的反例。

设 $k$ 为域，$R=k[t]$。给定 $R$ 模的短正合列

$$0\longrightarrow A\xrightarrow{\iota}B\xrightarrow{q}C\longrightarrow0,$$

其中 $A,B$ 均为可数生成的自由 $R$ 模。

对任意 $R$ 模 $M$，定义其 $t$ 进完备化

$$\widehat M=\varprojlim_{n\ge0}M/t^nM,$$

过渡映射为自然约化。原行映射在各层诱导商模映射，因而诱导 $\widehat\iota:\widehat A\to\widehat B$ 和 $\widehat q:\widehat B\to\widehat C$。

建立自由呈示在完备化后的相容恢复理论。目标是证明

$$0\longrightarrow\widehat A\xrightarrow{\widehat\iota}\widehat B
\xrightarrow{\widehat q}\widehat C\longrightarrow0$$

仍为短正合列，并给出相容商记录的提升构造与全部提升的自由度。请完成构造和正合性论证。

## S5 原模与完成的值域

仍令 M=⊕_{i≥0}k[t]e_i。判定典范映射 M→M̂ 是否必为满射；若不是，给出在每一商层都由原模代表但不来自一个原模元素的记录。

## S6 再次完成

把 M̂ 视为 R 模，判定 M̂→lim_n M̂/t^nM̂ 是否为同构，并验证典范映射而非另选抽象同构。
