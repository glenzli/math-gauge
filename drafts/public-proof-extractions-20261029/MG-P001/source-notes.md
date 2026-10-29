# 来源与独立改编边界

来源标识为 `biss-mnev-gluing`，可见性为 public。2026-10-29 核对以下一手材料，未访问未公开 OET 内容。

1. Daniel K. Biss, *The homotopy type of the matroid Grassmannian*, Annals of Mathematics 158 (2003), 929–952，DOI [10.4007/annals.2003.158.929](https://doi.org/10.4007/annals.2003.158.929)。[出版页](https://annals.math.princeton.edu/2003/158-3/p04)，[原文 PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v158-n3-p04.pdf)。核对第 2 节命题 2.6 的背景、第 4 节至第 5 节的证明组织及印刷页 947–949，特别是命题 4.5 的证明在第 948 页最后推断可缩的粘合步骤。那里研究的是有向拟阵偏序集的几何实现；开集来自删去一个子偏序集的实现，闭集来自另一个子偏序集的实现。本案例没有复原这些拟阵对象。
2. Nikolai Mnëv, *On D.K. Biss' papers …*, [arXiv:0709.1291v3](https://arxiv.org/abs/0709.1291v3)，2007-09-18，2 页，[固定版本 PDF](https://arxiv.org/pdf/0709.1291v3)。第 1 页指出两篇 Biss 论文中的同类推断：可缩开集与闭集覆盖整体，交集到闭集的包含同伦等价，并不足以推出整体可缩；圆周可由相应开、闭弧段覆盖。第 2 页讨论尝试继续归纳的障碍。这是错误定位与反例机制的来源；本稿不采纳其中个人预期作为数学结论。
3. Daniel K. Biss, *Erratum to “The homotopy type of the matroid Grassmannian”*, Annals of Mathematics 170 (2009), 493，DOI [10.4007/annals.2009.170.493](https://doi.org/10.4007/annals.2009.170.493)。[出版页](https://annals.math.princeton.edu/2009/170-1/p15)，[勘误 PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v170-n1-p15-p.pdf)，正文为 PDF 第 3 页、印刷页 493。作者确认第 948 页的上述推断有误，并说明主定理 1.1 的证明受影响，在该勘误中仍为猜想。勘误收稿 2008-11-08，出版页记载网上发表 2009-07-12。

这里的历史结论严格限于该勘误所处的时间点：**原证明存在缺口，不等于原主定理已被否定。** 本次没有调查其后所有专门研究，不能把“2009 年勘误时仍为猜想”改写为对 2026 年研究现状的完整判断。

## 保留、改变与新增

保留的机制是

$$X=O\cup C,\quad O\text{ 开且可缩},\quad C\text{ 闭},\quad O\cap C\hookrightarrow C\text{ 为同伦等价}.$$

本案例有意把原文的有向拟阵偏序集实现换成一般有限单纯复形 $K$，并把被删除的子复形缩为单个顶点 $v$。这些是独立抽象，**不是原命题 4.5 的等价转述**。题中 $B$ 保持为含 $v$ 的子复形，所有相关子空间拓扑来自 $|K|$。

新增目标是分类这一限制类中整体的所有可能同伦类型、实现全部类型，并给出局部有限数据的精确可缩判据。参考的悬挂分类、显式实现和整数无环判据并非在上述历史文献中发现的原结论；它们是本次独立推导。题面没有出现作者名、错误史、来源、真假标签、link、悬挂或待补条件。

这一抽象揭示同一粘合前提在有限组合拓扑中的实际自由度，但没有声称解决原拟阵 Grassmannian 问题。任何非可缩的实现也只反驳抽象的普遍粘合结论。

## 证明背景与证据范围

[Allen Hatcher, Algebraic Topology，作者公开 PDF](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) 提供标准工具：命题 0.16–0.17、定理 2C.5、定理 4.5 和 4.32，以及 van Kampen 与 Mayer–Vietoris。实际使用的假设在参考稿中逐项核对。参考稿给出的两生成元、两关系元无环但非可缩展示复形，是作者用于检查判据强度的独立显式见证，不归因于 Biss 或 Mnëv。

候选只接收 task.md。其余文件均为评审材料。作者数学自查、独立 AI 审查、人工批准、候选模型结果和 Lean 编译是不同证据；当前只有作者阶段材料，没有人类批准、候选运行或形式化证明。该题的经验难度未知，参考稿长度和历史来源不构成难度证据。
