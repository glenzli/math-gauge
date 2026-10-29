# 参考论证：素点分裂的整体实现

全称目标不成立。下面使用实际的含幺交换环、循环商模和所有素理想处的通常局部化；不需要列举素理想或选择某类特殊素点。

## 环与短正合列

令

$$R=\prod_{n\in\mathbb N}\mathbb F_2,\qquad
I=\bigoplus_{n\in\mathbb N}\mathbb F_2\subset R.$$

运算逐坐标定义。$I$ 是有限支撑序列构成的理想：两个有限支撑序列的和仍有限支撑，任意序列与有限支撑序列相乘也仍有限支撑。取

$$A=I,\qquad B=R,\qquad C=R/I,$$

包含与商映射组成短正合列。$B$ 是秩一自由模；$C$ 由 $\overline1$ 生成，所以是循环模且有限生成。常值一序列不属于 $I$，故 $\overline1\ne0$。

## 每个素点处都分裂

固定任意素理想 $\mathfrak p$，记 $\varphi:R\to R_{\mathfrak p}$ 为自然映射。每个 $a\in R$ 都满足 $a^2=a$。

若 $a\notin\mathfrak p$，则 $a$ 属于局部化的分母集合，且 $a(a-1)=0$。把等式映入局部化并消去单位 $\varphi(a)$，得到 $\varphi(a)=1$。

若 $a\in\mathfrak p$，则 $1-a\notin\mathfrak p$，否则两者相加会给出 $1\in\mathfrak p$。由于 $(1-a)a=0$，在局部化中消去单位 $\varphi(1-a)$，得到 $\varphi(a)=0$。

局部化的每个元素都有分式表示 $a/s$，其中 $s\notin\mathfrak p$。上面的结论说明 $\varphi(s)=1$，所以该元素为 $\varphi(a)$，即零或一。由于 $\mathfrak p$ 为真理想，$R_{\mathfrak p}$ 非零，故它是一个域。

局部化后的 $q_{\mathfrak p}:B_{\mathfrak p}\to C_{\mathfrak p}$ 仍满射。于是它是域 $R_{\mathfrak p}$ 上向量空间之间的满射：选取 $C_{\mathfrak p}$ 的一组基，为每个基向量选取原像并线性延拓，即得到一个 $R_{\mathfrak p}$ 线性右逆。因为 $\mathfrak p$ 任意，题面的全部局部分裂条件成立。

## 不存在整体分裂

令 $e_n\in I$ 为第 $n$ 个坐标是一、其他坐标为零的序列。假设存在 $R$ 线性映射 $s:C\to R$，满足 $qs=I_C$，并置 $a=s(\overline1)$。

对每个 $n$，因 $e_n\in I$，有 $e_n\overline1=0$，故

$$e_na=e_ns(\overline1)=s(e_n\overline1)=0.$$

读取第 $n$ 坐标得到 $a_n=0$。这对所有 $n$ 成立，所以 $a=0$。但右逆条件要求 $q(a)=\overline1\ne0$，矛盾。因此没有整体分裂，也不存在题目要求的相容直和同构；若有该同构，其第二直和项的包含就是右逆。

本实例的整体分裂集合为空。一个满足全部题设的反例已经否定非空构造的全称要求；候选不必另外完成一个附加条件下的分类定理。

## 来源和验证范围

有限投射模的局部化语境参见 [Stacks Project, 00NX](https://stacks.math.columbia.edu/tag/00NX)。本稿对环、理想、所有素点处的域结构、实际局部化右逆和全局无解逐项给出证明；不调用原目标作为外部定理，也未使用未公开 OET 材料。

Lean 使用真实的 `Localization.AtPrime`、`LocalizedModule` 及商映射诱导的 `LocalizedModule.map`，不是把素点上的分裂作为未证假设。局部化模的分式构造与题面的张量构造是通常同一局部化的两种模型；形式化中的映射就是原商映射的局部化。具体覆盖及该模型对应见 formal/COVERAGE.md。人工审定仍为 pending。
