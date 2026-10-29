# 局部分裂、有限呈示与截面拼接：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 幂等理想商的截面

判定：construction。

定义 s(r̄)=r(1−e)b。若 r−r′∈eR，乘 (1−e) 后为零，故良定义；线性显然，qs(r̄)=r̄，因为 e 在商中为零。映射 (a,c)↦a+s(c) 的逆为 b′↦(b′−s(qb′),qb′)，两复合恒等，第一项在核中。

判准：良定义与右逆；双向同构。

## S2 有限生成理想的局部检验

判定：true。

局部 C_p 为有限生成投射 R_p 模，因此自由；作为循环商，它要么为零，要么秩一。非零时其湮灭理想为零，故 I_p=0；零时 I_p=R_p。因此 (I/I²)_p=0 对每个素点成立，推出 I=I²（非零模元素的湮灭理想包含于某极大理想，其局部像不为零）。取生成元 u_i，将 u_i=Σa_ij u_j，a_ij∈I；伴随矩阵给 det(1−A)I=0，写 det(1−A)=1−e，e∈I。于是 e²=e，且每个 u=eu，所以 I=eR。S1 给截面。局部有限生成投射为自由可用 Nakayama：提升剩余域的一组基给满射 R_p^r→C_p，投射使其核直和，模极大理想核零，再由有限生成和 Nakayama 得核零。

判准：局部商为零或秩一自由；有限生成幂等理想的行列式论证。

## S3 全部截面的自由度

判定：true。

任意 s−s_0 的 q 像为零，故由 ι:A→ker q 同构唯一写成 ιh，h:C→A 线性。反之 s_0+ιh 都是截面，且相加参数为 h 的加法。给 s 的同构 Φ_s(a,c)=ιa+s(c)，逆由 q 及 ι^{-1}(b−sqb) 给出；任何保持 A 包含和 C 投影的同构必由其第二因子像得到截面，因此一一对应。更换 s_0 只平移参数，没有自然指定原点。

判准：差唯一下降到 A；全部相容同构。

## S4 整体对象与全部恢复目标

判定：false。

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

判准：A refutation must give an actual commutative ring and short exact sequence with finite free B and cyclic C.；Verify that the actual localized quotient map admits a linear right inverse at every prime ideal, not only at a selected family of evaluation primes.；Prove that the original global quotient map admits no R-linear right inverse, or otherwise refute a requested universal conclusion.。

## S5 只保留幂等理想等式

判定：false。

否。取 R=∏_nF_2，I 为有限支持理想。每个元素 a 满足 a²=a，故 I=I²。若截面存在，a=s(1̄) 被每个坐标幂等 e_n 杀掉，故 a=0，而 q(a)=1̄≠0（恒 1 非有限支持），矛盾。S2 行列式证明用有限个生成元，不能对无限矩阵取同样行列式。

判准：幂等理想与非零商；排除所有截面。

## S6 给定相容的开集截面

判定：true。

成立。对每个 c∈C，s_j(c/1) 是 B 在有限主开覆盖上的相容局部截面。模的主开层条件给唯一 b∈B；定义 s(c)=b。该层条件可由有限分母消去及 Σr_j f_j^N=1 给出：先升共同幂，使各局部相等变成 B 内可核验的等式，再用该单位分解加权拼接，局部化检验两向。s(c+c′)、s(rc) 的局部值分别与 s(c)+s(c′)、rs(c) 相同，唯一性给线性；qs(c) 的局部值为 c，故 qs=id。任何另一拼接逐局部相同，唯一性给相等。关键是已经给覆盖上相容的实际映射，不必从素点截面向开邻域扩张。

判准：逐元素拼接后验证线性；不假设 Hom 局部化交换。
