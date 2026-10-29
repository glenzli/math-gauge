# 连续提升的有限拼接与积：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 有限开闭分块上的提升

判定：true。

有限离散 P 的每个点 p 任选 q 原像 y_p，所得映射自动连续。有限不交并仍紧 Hausdorff 全不连通，各分支开闭；在每个分支用给定性质得到提升，有限拼接连续，且复合逐分支等于 f。空空间的唯一映射也满足条件。

判准：逐点选择的连续性依据；有限不交并仍 profinite。

## S2 回缩与有限因子的乘积

判定：true。

给 f:P→Z，先提升 fr:Q→Z 为 h:Q→Y，取 g=hi，则 qg=fri=f。P 为题设 profinite 对象。Q×A 是由 |A| 个 Q 组成的有限开闭不交并，应用 S1；A 空时空积空间为空，结论仍成立。

判准：正确复合顺序；有限积到有限余积身份。

## S3 超滤子紧化的回缩描述

判定：construction。

βD 嵌入 {0,1}^{P(D)}，滤子及补集有限等式定义闭子集，故紧 Hausdorff，且 [A] 为开闭基。主超滤子 δ_d 稠密：非空 [A] 含主点。到紧 Hausdorff K 的任意 D 映射 h 按推前超滤子的唯一极限延拓；紧性、Hausdorff 性给存在唯一，正则性保证连续：若极限在开 O 中，取闭邻域 V⊂O，h^{-1}(V)∈u，则此基本邻域所有超滤子的极限在 V⊂O。给 q 与 f，选每个主点 f(δ_d) 的 q 原像，在 D 上形成映射并延拓为 g；qg=f 因其在稠密主点相等且 Z Hausdorff。对 P，底集恒等的延拓 ε:β|P|→P 满射，因为 εδ_p=p；若 P 有提升性质，用 id_P 提升得截面 j，于是 εj=id。反之回缩性质用 S2。空集情形所有对象和映射均唯一。

判准：紧化和连续延拓适用条件；实际截面与回缩两向。

## S4 整体对象与全部恢复目标

判定：false。

目标不成立。以下给出两个满足全部前提的相同因子，并直接构造其积上的一个连续满射，它没有连续截面。



## 因子与提升性质

令 $P$ 为 $\mathbb N$ 上所有超滤子的集合，赋 Stone 拓扑。对 $A\subseteq\mathbb N$，基本开闭集是

$$[A]=\{u:A\in u\}.$$

记 $\delta_n$ 为 $n$ 处的主超滤子。标准超滤子紧化定理给出：$P$ 紧、Hausdorff、全不连通；$\{\delta_n:n\in\mathbb N\}$ 稠密；每个从离散 $\mathbb N$ 到紧 Hausdorff 空间的映射都唯一延拓为 $P$ 上的连续映射。这些背景结果在所固定的 Mathlib 中直接以实际的 `Ultrafilter`、Stone 拓扑、稠密主点映射及连续延拓实现，不以结论证书作为输入。

具体地，超滤子由其子集成员关系嵌入 $\{0,1\}^{\mathcal P(\mathbb N)}$，滤子与补运算的有限等式给出闭子集，故紧性及 Hausdorff 性成立；$[A]$ 的补集为 $[A^c]$，给出开闭基和全不连通性。非空 $[A]$ 含某个 $\delta_n$，故主点稠密。对到紧 Hausdorff $K$ 的映射 $h$，延拓在 $u$ 处取推前超滤子 $h_*u$ 的唯一极限；紧性保证存在，Hausdorff 性保证唯一，紧 Hausdorff 正则性保证该取极限映射连续。

现在给定题中的 $q:Y\to Z$ 和 $f:P\to Z$。选择一个集合意义的右逆 $s:Z\to Y$，并将

$$n\longmapsto s(f(\delta_n))$$

连续延拓为 $g:P\to Y$。于是 $qg$ 和 $f$ 在全部主点相等，且二者都连续到 Hausdorff 空间 $Z$；由稠密性，$qg=f$。因此 $P_1=P_2=P$ 满足题设。选取的 $s$ 不需要连续，延拓只用于其在离散主点上的复合。



## 积中的开集及其闭包

置 $B=P\times P$，定义

$$D=\{(\delta_n,\delta_n):n\in\mathbb N\},\qquad
\Delta=\{(u,u):u\in P\}.$$

$\{\delta_n\}=[\{n\}]$ 为开集，所以 $D$ 是开集。Hausdorff 性使 $\Delta$ 闭，故 $\overline D\subseteq\Delta$。反向，由主点稠密及对角映射 $u\mapsto(u,u)$ 连续，每个 $(u,u)$ 都属于 $\overline D$。因此

$$\overline D=\Delta.$$

$\Delta$ 不是开集。否则对每个固定的 $u$，沿连续映射 $v\mapsto(v,u)$ 拉回 $\Delta$，得到 $\{u\}$ 开，从而 $P$ 离散。紧离散空间有限，但 $n\mapsto\delta_n$ 是从 $\mathbb N$ 到 $P$ 的单射，矛盾。



## 一个明确的无截面覆盖

令 $\{0,1\}$ 离散，并在 $B\times\{0,1\}$ 中取

$$Y=(D^c\times\{1\})\cup(\Delta\times\{0\}),\qquad
q:Y\to B,\quad q(b,e)=b.$$

$D^c$ 和 $\Delta$ 都闭，故 $Y$ 是 profinite 空间中的闭子空间，仍为 profinite。$q$ 连续且满射：$b\notin D$ 时取 $(b,1)$；$b\in D\subseteq\Delta$ 时取 $(b,0)$。

若有连续截面 $s:B\to Y$，记其第二坐标为 $c:B\to\{0,1\}$。对 $b\in D$，第一片不可能含 $s(b)$，所以 $c(b)=0$。由于 $c^{-1}(\{0\})$ 闭，

$$\Delta=\overline D\subseteq c^{-1}(\{0\}).$$

而 $Y$ 中所有第二坐标为 $0$ 的点，其第一坐标都在 $\Delta$，故反向包含也成立。于是

$$\Delta=c^{-1}(\{0\})$$

开，与前面矛盾。取题目中的 $Z=B$ 和 $f=I_B$，所要求的 $g$ 就是被排除的连续截面。这完成对原全称目标的反驳。

判准：Give a complete proof of the universal lifting target or a counterexample satisfying all stated hypotheses.；For a counterexample, verify that both factors satisfy the complete stated lifting property and that the product fails it. This may be done by an explicit continuous surjection q, continuous f and a proof of no continuous lift, or by a correctly applied exact characterization equivalent to the stated lifting property, with every factor and product hypothesis verified.。

## S5 有限像的参数映射

判定：true。

成立。有限子空间 f(P) 在 Hausdorff Z 中离散，所以每个 P_z=f^{-1}({z}) 为开闭集。为每个实际像点 z 选 y_z∈q^{-1}(z)，在 P_z 上定义常值 g=y_z；有限开闭分块保证连续且 qg=f。P 空时取空映射。因而有限像测试不足以刻画 S1 的全提升性质。

判准：有限像的离散性；开闭分块上的连续提升。

## S6 这些提升的全部自由度

判定：classification。

提升限制到 P_z 后取值于 Y_z，连续性对闭子空间成立，得到右侧族。反之逐块连续映射因 P_z 是有限开闭分块而拼成连续 g，且 qg=f，两过程互逆。若 Y_z 有限，Hausdorff 性使其离散，连续映射 P_z→Y_z 等价于标号 y∈Y_z 的开闭纤维划分：各块互不相交、并为 P_z；某块可空。反向按块取标签连续。因此既有常值提升也容许非平凡开闭细分，不把任意集合选择都叫连续。

判准：双向限制/拼接；完整开闭划分分类。
