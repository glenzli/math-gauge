# 公开研究题集 · 0.4.1

这些题目检验模型能否保持实际条件，并完成相应证明、反例、构造或分类。正式作答只投影选中题目的 task.md；本页、来源、参考、评分、作者记录、审核及形式化材料仅供出题与评审使用。

当前集合包含二十题。MG-R005 现为 0.3.1，明确竞争函数取值为 $[-\infty,+\infty]$，并以实高度上图的闭性、凸性固定语义；它仍是同一道题的修订。原十题中的其余九题保持 0.3.0，MG-R011–MG-R020 保持 0.4.0，合计另外十九题的全部材料与候选输入不变。全部统一使用 task-only 投影。

原十题基线：

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

全部题目保持 draft、human pending。原 0.3.0 十题的数学作者与独立审核者使用 Astra Max，工程整合使用 Sol 6.1 Max；该历史版本的数学复核、题面盲审、文件身份及输入投影证据见逐题历史记录与[优化验证记录](../../results/ten-case-optimization/README.md)。R005 的 0.3.1 参考、评分及 Lean 包装定理由新的[独立语义审核](MG-R005/reviews/v0.3.1-semantic.json)绑定，随后通过五模块全新构建；该审核具有源码和参考上下文，不称新题面盲审。其余十九题保留原材料。R005 的 design.json 继续作为原作者阶段记录，旧版全部题内材料和校准保存在 [0.3.0 快照](MG-R005/history/v0.3.0/snapshot.json)。

原 0.3.0 十题基线曾完成 Terra 6.1 Max 十个新独立隔离会话，每题一份有效答卷，AI 审核 **10/10 通过**；R008、R009、R010 又经第二次数学核对。请求的型号与 max 设置被 CLI 接受，事件流未独立回显后台型号。模型答题、作者形式化和人工审定分别记录，详见 [本轮校准](../../results/full-lean-terra/README.md)。该历史结果支持保留为边界基线，不能宣称对 Terra Max 已有足够区分度，也不构成 R005 0.3.1 的成绩。R005 新版的补测状态、原始答卷及评分单独记录在 [澄清版补测](../../results/r005-clarified-v0.3.1-20261030/)，不反向改写旧轮分数。

原十题主目标的成立结论或完整否定反例均有实际 Lean 证明，逐题 formal/COVERAGE.md 说明对应关系及可选旁支边界；共享验证器按题隔离构建并审计全部项目声明。未修订参考稿的作者阶段状态措辞按冻结字节保留；R005 0.3.1 的当前形式化以新 manifest、current-formal.json 与逐题审核为准，候选补测只以独立结果记录为准。MG-R001 的历史 Lean 审计仍作为历史记录保存，不替代本轮扩展后的验证。

## 出题侧布局

四个不成立强目标保留为边界基线：MG-R001、MG-R002、MG-R004、MG-R006。一个满足全部前提的有效短反例足以解决对应全称目标，额外构造贡献另记。

六个主目标成立：MG-R003、MG-R005、MG-R007、MG-R008、MG-R009、MG-R010。其中 MG-R003、MG-R007、MG-R008、MG-R009、MG-R010 做了实质重设计，分别涉及迭代恢复、相容等变分裂、表示性分类、群作用下降分类和映射空间的指数结构。这些分类不进入候选输入，也不能代替逐题论证。

评分要求完成题面的实际目标，接受其他有效证明和意外结果；不要求抄齐参考稿的全部旁支、边界或附加条件升级。

[设计标准](../../protocol/research-case-design.md) · [评测协议](../../protocol/evaluation.md) · [来源](../../SOURCES.md) · [0.2 版归档](../../archive/research-v0.2/README.md) · [早期归档](../../archive/legacy-v0/README.md)

## 新增十题 · 0.4.0

| 题号 | 题面 | 领域 | 评审材料 |
| --- | --- | --- | --- |
| MG-R011 | [无限凸约束的有限问题恢复](MG-R011/task.md) | functional analysis / Hilbert convex feasibility | [参考](MG-R011/reference.md) · [评分](MG-R011/rubric.json) · [审核](MG-R011/review.json) · [作者记录](MG-R011/design.md) · [Lean 覆盖](MG-R011/formal/COVERAGE.md) |
| MG-R012 | [循环兼容记录的凸势](MG-R012/task.md) | convex analysis / cyclic monotonicity | [参考](MG-R012/reference.md) · [评分](MG-R012/rubric.json) · [审核](MG-R012/review.json) · [作者记录](MG-R012/design.md) · [Lean 覆盖](MG-R012/formal/COVERAGE.md) |
| MG-R013 | [多项式范数记录与谱恢复](MG-R013/task.md) | functional analysis / nonnormal spectral approximation | [参考](MG-R013/reference.md) · [评分](MG-R013/rubric.json) · [审核](MG-R013/review.json) · [作者记录](MG-R013/design.md) · [Lean 覆盖](MG-R013/formal/COVERAGE.md) |
| MG-R014 | [无限方程系的坐标恢复](MG-R014/task.md) | linear algebra / infinite systems / algebraic duality | [参考](MG-R014/reference.md) · [评分](MG-R014/rubric.json) · [审核](MG-R014/review.json) · [作者记录](MG-R014/design.md) · [Lean 覆盖](MG-R014/formal/COVERAGE.md) |
| MG-R015 | [自由呈示的完备化与相容恢复](MG-R015/task.md) | commutative algebra / adic completion | [参考](MG-R015/reference.md) · [评分](MG-R015/rubric.json) · [审核](MG-R015/review.json) · [作者记录](MG-R015/design.md) · [Lean 覆盖](MG-R015/formal/COVERAGE.md) |
| MG-R016 | [素点分裂的整体实现](MG-R016/task.md) | commutative algebra / localization / module splitting | [参考](MG-R016/reference.md) · [评分](MG-R016/rubric.json) · [审核](MG-R016/review.json) · [作者记录](MG-R016/design.md) · [Lean 覆盖](MG-R016/formal/COVERAGE.md) |
| MG-R017 | [两个参数空间上的连续提升](MG-R017/task.md) | general topology / projective profinite spaces | [参考](MG-R017/reference.md) · [评分](MG-R017/rubric.json) · [审核](MG-R017/review.json) · [作者记录](MG-R017/design.json) · [Lean 覆盖](MG-R017/formal/COVERAGE.md) |
| MG-R018 | [有限观察的相容选择](MG-R018/task.md) | category theory / finite observations and the ultrafilter monad | [参考](MG-R018/reference.md) · [评分](MG-R018/rubric.json) · [审核](MG-R018/review.json) · [作者记录](MG-R018/design.json) · [Lean 覆盖](MG-R018/formal/COVERAGE.md) |
| MG-R019 | [超滤子运算与有限观测的空间实现](MG-R019/task.md) | category theory / ultrafilter algebras, topology reconstruction and profinite reflection | [参考](MG-R019/reference.md) · [评分](MG-R019/rubric.json) · [审核](MG-R019/review.json) · [作者记录](MG-R019/design.json) · [Lean 覆盖](MG-R019/formal/COVERAGE.md) |
| MG-R020 | [对称分解的整体等距比较](MG-R020/task.md) | complete discrete valuation rings / symmetric idempotent decompositions and isometries | [参考](MG-R020/reference.md) · [评分](MG-R020/rubric.json) · [审核](MG-R020/review.json) · [作者记录](MG-R020/design.json) · [Lean 覆盖](MG-R020/formal/COVERAGE.md) |

新增题的作者参考、独立 AI 审核和逐题 Lean 证据分别绑定文件散列；human 状态仍为 pending。候选试跑的状态和任何数学评分另行记录，不能从作者构建推断。

新增十题本轮各一次独立隔离运行，独立AI数学审核 **10/10 通过**，R019第二审通过；human仍pending。该结果与原十题先前10/10分属两批运行。见[本轮记录](../../results/expansion-v0.4/README.md)、[两轮比较](../../results/expansion-v0.4/comparison.md)和[候选额外贡献与边界](../../results/expansion-v0.4/CALIBRATION-NOTES.md)。请求配置与未回显的后台身份分开保存，候选补充未另做Lean形式化。
