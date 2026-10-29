# 结果与版本索引

本页按实际实验范围组织材料。每次运行的题面、参考、评分、工具条件和版本独立冻结；不同批次不拼成一次实验，历史文件中的“未提交”“未试跑”等文字描述其记录时点。

当前43份新试卷是41个递进题组与两份整章题，尚无模型答卷或通过率；本页的实测成绩属于原41道单题及独立补测。新材料状态与待测问题见[项目定位](project-positioning.md)和[评测方法](evaluation-methods.md)，不沿用旧分数。

本轮[严格数学复核](../results/strict-review-20261030/README.md)属于题包审核，不是新模型实验；其中GR001的[0.1.2局部修订](../drafts/progressive-groups-20261030/reviews/strict-amendment-0.1.2.json)另保留原文件和修订身份，其余40组与两章仍为0.1.1。

## 当前完整比较

| 实验 | 题目范围 | 数学请求 | AI 审核严格完成 |
| --- | --- | ---: | --- |
| [首轮完整比较](../results/full-comparison-20261030/README.md) | 41 题，R005 为 0.3.0 | 82 | Terra 40/41；Gemini 27/41 |
| [R005 澄清版补测](../results/r005-clarified-v0.3.1-20261030/README.md) | 仅 R005 0.3.1 | 2 | Terra 1/1；Gemini 1/1 |

首轮按先 Terra 6.1 Max、后 Gemini 3.8 Flash High 的顺序执行，每题一次独立会话、相同输入、无答题工具或现场 Lean 反馈。服务端过滤、未完成数学和候选编译失败分别记录；严格分母保留全部 41 题。详见[分项及逐题报告](../results/full-comparison-20261030/comparison.md)和[结果解释](../results/full-comparison-20261030/comparison-notes.md)。

R005 旧题面没有明确竞争函数取负无穷的范围；现行版本增加扩展实值与实高度上图约定，并保留旧文件、旧答卷和旧评分。新版双方通过不能回填首轮，也不足以单凭一次样本推断成绩变化由澄清导致。

这些均为 **AI 审核的暂定比较**，题目与答卷人审待定。通过意味着全部必需义务有有效证明路线，不表示每个可分离的额外论断都正确；存在的错误旁支保留在逐题审核中。相关母题、公开来源和单次样本限制不能从总比例中消失。

## 如何检查一份成绩

1. 在完整比较表中打开题面和原始答卷，确认题号及冻结版本；当前 R005 题面不能代替首轮旧题面。
2. 查看初审、独立复核和最终裁定，核对 `response_sha256`。出题侧参考与候选自己的证明分别阅读。
3. 对生成／修复题查看候选 Lean 报告、原始源码和公理依赖。只看到作者 Lean 通过不足以确认候选交付。
4. 查看执行收据中的请求计数、型号请求与回显、工具条件和完整性。客户端成功退出不是数学通过。
5. 使用[离线复算命令](usage.md)核对汇总；两轮已完成的复算回执分别位于[首轮](../results/full-comparison-20261030/runtime/offline-recomputed/verification.json)和[补测](../results/r005-clarified-v0.3.1-20261030/offline-recomputed/verification.json)。

运行前非数学能力探测、环境失败和合成测试有各自记录，不计入上述 84 次数学请求。档案包含精确路径与时间作为历史证据；重定位由复算程序处理，不能改写原始报告。

## 历史校准

| 材料 | 当时范围与用途 |
| --- | --- |
| [原十题完整 Lean 与 Terra 校准](../results/full-lean-terra/README.md) | 0.3.0 十题基线；Terra 单次校准 10/10，与后续十题分开 |
| [0.4.0 扩展记录](../results/expansion-v0.4/README.md) | R011–R020；Terra 单次校准 10/10，含额外复核及作者形式化 |
| [成立目标六题校准](../results/true-goal-six-terra/README.md) | R101–R106；Terra 单次校准 6/6，属于独立批次 |
| [递归闭合单题旧比较](../results/recursive-operator-closure/comparison.md) | R001 原题的早期 Terra／Gemini 记录，不能代替多题比较 |
| [原十题优化验证](../results/ten-case-optimization/README.md) | 题面盲审、数学审校、输入投影及版本保留 |

历史成绩不能直接证明新版本表现。当前默认公开 suite 为 0.4.1：R005 为 0.3.1，其余原九题为 0.3.0，R011–R020 为 0.4.0；其他独立 suite 保持各自版本。完整对应见[现行与历史目录](../exercises/history.md)。

## 审核和形式化范围

现行 41 题均有完整数学参考和非作者 AI 审核。40 题有完整作者主任务 Lean 证据；P003 的参考依赖精确引用的公开几何输入，相关辅助模块已形式化，完整几何比较尚未完成 Lean 形式化。该题保留在整体分母中，覆盖子集另作分层，不以删除它来改善总成绩。

详见[逐题证据账本](../exercises/instructor-guide.md)、[候选核验合同](../protocol/candidate-lean.md)和[最终工程验收](../results/full-comparison-20261030/validation/finalization/README.md)。人工确认应另留明确记录；提交、推送或离线复算成功本身不改变审核状态。

[文档导航](README.md) · [返回首页](../README.md) · [使用与复核](usage.md)
