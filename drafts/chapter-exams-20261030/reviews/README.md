# 整章考试独立复核

[最终全量复核](independent-review.md)逐项核对34+92个义务、完整来源、章末习题解、前置依赖与公开/私有判准一致性。[另一份范围复核](scope-review.md)独立检查章节数学边界；其初审散列不覆盖后来补充的清单规则。最终核心身份以independent-review.json的file_sha256为准，旧initial_file_sha256保留为历史。

[执行与判卷复核](alignment-gate.md)审核原答卷JSON抽取、完整覆盖、真实Lean审计声明、背景许可与incomplete不得通过。CH03-D07的背景复用许可已明确投影到候选清单；执行缺口和许可可见性问题均已闭环。

所有记录均为AI审核，人工状态仍pending。自动检查与背景编译不能替代目标章节完整作者Lean的逐项对齐；本批没有新模型试跑。测试结果转录与代码身份见[针对检查](../validation/targeted-runner-checks.json)。

## 0.1.1 题面编辑

上述原始报告和索引保持原字节，覆盖0.1.0；其中旧task散列应在[历史快照](../history/0.1.0.json)中核对。当前题面移除分值、判卷提示及后序答案提示，并澄清audit书面交付；没有新增数学义务、改变参考或Lean源码。各题review.json区分原独立数学复核身份与当前编辑身份，具体前后散列及不变性见[编辑等价记录](editorial-amendment-0.1.1.json)。这不是重新完整独立数学复核、人工批准或模型试跑。
