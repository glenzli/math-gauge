# 公开研究题集 · 0.3.0

这些题目检验模型能否保持实际条件，并完成相应证明、反例、构造或分类。正式作答只投影选中题目的 task.md；本页、来源、参考、评分、作者记录、审核及形式化材料仅供出题与评审使用。

| 题号 | 题面 | 领域 | 评审材料 |
| --- | --- | --- | --- |
| MG-R001 | [递归算子系统的闭合](MG-R001/task.md) | recursive operators | [参考](MG-R001/reference.md) · [评分](MG-R001/rubric.json) · [审核](MG-R001/review.json) · [作者记录](MG-R001/design.json) · [Lean 覆盖](MG-R001/formal/COVERAGE.md) |
| MG-R002 | [兼容线性记录的整体实现](MG-R002/task.md) | functional analysis / bidual observations | [参考](MG-R002/reference.md) · [评分](MG-R002/rubric.json) · [审核](MG-R002/review.json) · [作者记录](MG-R002/design.json) · [Lean 覆盖](MG-R002/formal/COVERAGE.md) |
| MG-R003 | [双重平均与迭代恢复](MG-R003/task.md) | functional analysis / ergodic averages and lazy iteration | [参考](MG-R003/reference.md) · [评分](MG-R003/rubric.json) · [审核](MG-R003/review.json) · [作者记录](MG-R003/design.json) · [Lean 覆盖](MG-R003/formal/COVERAGE.md) |
| MG-R004 | [复形记录的稳定消元](MG-R004/task.md) | functional analysis / Hilbert complexes | [参考](MG-R004/reference.md) · [评分](MG-R004/rubric.json) · [审核](MG-R004/review.json) · [作者记录](MG-R004/design.json) · [Lean 覆盖](MG-R004/formal/COVERAGE.md) |
| MG-R005 | [有限观测下的凸成本恢复](MG-R005/task.md) | functional analysis / convex duality | [参考](MG-R005/reference.md) · [评分](MG-R005/rubric.json) · [审核](MG-R005/review.json) · [作者记录](MG-R005/design.json) · [Lean 覆盖](MG-R005/formal/COVERAGE.md) |
| MG-R006 | [逐层可解系统的兼容提升](MG-R006/task.md) | category theory / inverse limits | [参考](MG-R006/reference.md) · [评分](MG-R006/rubric.json) · [审核](MG-R006/review.json) · [作者记录](MG-R006/design.json) · [Lean 覆盖](MG-R006/formal/COVERAGE.md) |
| MG-R007 | [对称提升的逐层相容实现](MG-R007/task.md) | representation theory / coherent equivariant splittings | [参考](MG-R007/reference.md) · [评分](MG-R007/rubric.json) · [审核](MG-R007/review.json) · [作者记录](MG-R007/design.json) · [Lean 覆盖](MG-R007/formal/COVERAGE.md) |
| MG-R008 | [逐层记录的承载与相容性分类](MG-R008/task.md) | category theory / finite-free towers and representability classification | [参考](MG-R008/reference.md) · [评分](MG-R008/rubric.json) · [审核](MG-R008/review.json) · [作者记录](MG-R008/design.json) · [Lean 覆盖](MG-R008/formal/COVERAGE.md) |
| MG-R009 | [群作用下局部记录的下降分类](MG-R009/task.md) | condensed sets / group actions and descent classification | [参考](MG-R009/reference.md) · [评分](MG-R009/rubric.json) · [审核](MG-R009/review.json) · [作者记录](MG-R009/design.json) · [Lean 覆盖](MG-R009/formal/COVERAGE.md) |
| MG-R010 | [探针记录之间的映射空间](MG-R010/task.md) | general topology / compact generation and exponential spaces | [参考](MG-R010/reference.md) · [评分](MG-R010/rubric.json) · [审核](MG-R010/review.json) · [作者记录](MG-R010/design.json) · [Lean 覆盖](MG-R010/formal/COVERAGE.md) |

## 审核与使用状态

全部题目保持 draft、human pending。数学作者与独立审核者使用 Astra Max；工程整合使用 Sol 6.1 Max。当前确切版本的数学复核、全新题面盲审、文件身份及输入投影证据见逐题 review.json 与[本轮优化验证记录](../../results/ten-case-optimization/README.md)。reference.md 与 design.json 保留经过独立审核的确切字节；其中作者阶段的待审措辞由当前 review.json 接续，不在整合时改写。

本轮完成 Terra 6.1 Max 十个新独立隔离会话，每题一份有效答卷，AI 审核 **10/10 通过**；R008、R009、R010 又经第二次数学核对。请求的型号与 max 设置被 CLI 接受，事件流未独立回显后台型号。模型答题、作者形式化和人工审定分别记录，详见 [本轮校准](../../results/full-lean-terra/README.md)。当前结果支持保留为边界基线，不能宣称对 Terra Max 已有足够区分度。

十题主目标的成立结论或完整否定反例均有实际 Lean 证明，逐题 formal/COVERAGE.md 说明对应关系及可选旁支边界；共享验证器按题隔离构建并审计全部项目声明。参考稿的作者阶段状态措辞按冻结字节保留，当前形式化与试跑状态以本页、review.json 和本轮证据为准。MG-R001 的历史 Lean 审计仍作为历史记录保存，不替代本轮扩展后的验证。

## 出题侧布局

四个不成立强目标保留为边界基线：MG-R001、MG-R002、MG-R004、MG-R006。一个满足全部前提的有效短反例足以解决对应全称目标，额外构造贡献另记。

六个主目标成立：MG-R003、MG-R005、MG-R007、MG-R008、MG-R009、MG-R010。其中 MG-R003、MG-R007、MG-R008、MG-R009、MG-R010 做了实质重设计，分别涉及迭代恢复、相容等变分裂、表示性分类、群作用下降分类和映射空间的指数结构。这些分类不进入候选输入，也不能代替逐题论证。

评分要求完成题面的实际目标，接受其他有效证明和意外结果；不要求抄齐参考稿的全部旁支、边界或附加条件升级。

[设计标准](../../protocol/research-case-design.md) · [评测协议](../../protocol/evaluation.md) · [来源](../../SOURCES.md) · [0.2 版归档](../../archive/research-v0.2/README.md) · [早期归档](../../archive/legacy-v0/README.md)
