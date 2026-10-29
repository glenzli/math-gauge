# 参考论证：两个参数空间上的连续提升

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

## 评分范围及来源

任何满足全部前提的完整反例都应得到完成判定，无须使用本反例或证明一般的射影空间分类定理。只说明积不满足某个更强条件，而未将该失败连接到题目所要求的提升，不足以完成。

射影紧 Hausdorff 空间的历史背景见 [Gleason, Projective topological spaces (1958)](https://doi.org/10.1215/ijm/1255454110)。本稿使用独立写出的主点延拓与明确两片闭覆盖论证。固定 Mathlib 的 [StoneCech 源码](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Topology/Compactification/StoneCech.lean) 提供实际超滤子紧化背景。未使用未公开 OET 材料。

作者数学自查与作者 Lean 证据分开记录；独立 AI 审核和人工审定均以 review.json 为准。未运行候选模型测评。
