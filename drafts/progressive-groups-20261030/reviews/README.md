# 独立复核证据

三份报告覆盖全部41组、246阶段，每组均由作者之外的AI完整阅读题面、参考与原始合同。所报发现已修正并复核闭环；这不是人工审定或新目标Lean编译。

- [written-a](written-a.md)：15组、90阶段。
- [written-b](written-b.md)：14组、84阶段。
- [lean-groups](lean-groups.md)：12组、72阶段，另核对所供Lean输入的类型与语义。

[绑定索引](index.json)逐组记录最终文件散列。原报告保留审查时路径和快照叙述；临时目录中的task.md/reference.md已原字节转存对应题组，审阅的contract.json保存在author-contract.json。共享runner使用的contract.json只加规范schema、kind、全项必答和母题身份包装；原数学字段逐项核对不变。GF106/GF110以报告中的final_file_sha256和amendment为最终身份，早期file_sha256只描述初审状态。

数学复核不规定唯一证明路线；有效替代论证仍须接受。题组难度和诱导效应尚未由新模型考试测量。

## 0.1.1 题面编辑

上述原始报告和索引保持原字节，覆盖0.1.0；其中旧task散列应在[历史快照](../history/0.1.0.json)中核对。当前题面移除分值、判卷提示及后序答案提示，并澄清audit书面交付；没有新增数学义务、改变参考或Lean源码。各题review.json区分原独立数学复核身份与当前编辑身份，具体前后散列及不变性见[编辑等价记录](editorial-amendment-0.1.1.json)。这不是重新完整独立数学复核、人工批准或模型试跑。
