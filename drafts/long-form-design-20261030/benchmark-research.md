# 长任务与 BrokenArXiv 取材核查

核查时间：2026-10-30（Asia/Singapore）。本报告只读现行 Math Gauge README、评测协议与一手资料；未调用答题模型、未编译 Lean、未改仓库。下面“建议”均为本次设计判断，不是论文实测结论。

## 已核实的结论

用户所指应是 **BrokenArXiv**。它有取材价值，但不是“给整篇论文找错、定位并修复证明”的现成基准。**旧版人为扰动正确命题，新版抽取最近被反驳的历史猜想**；两种来源不能统称“论文已发表证明被证伪”。它的分数主要衡量面对假命题时是否仍声称完成证明，并不严格验收所给反例或证明。

### BrokenArXiv：必须注明版本

| 版本 | 官方来源、题源与规模 | 能借鉴什么 |
| --- | --- | --- |
| 2026-03-13 首篇说明，2 月题集 | 31 题。从近期摘要抽正确结果，再产生与它直接矛盾的 plausible 假版本；全文补足条件，经自动筛查与人工复核。旧评分 0–2：照证明为 0，静默改题为 1，其余包括诚实不会证明为 2；直接矛盾的修订另扣 1。 | 逼真的假命题、逐项保留原条件、假命题与真参考的可核查对应。 |
| 2026-09-15 更新说明，8 月起的新流程 | 明确只取被论文主要新结果反驳的既有猜想、开放问题的肯定回答或已有预测；排除任意变异。全文提取与复核，并有人审。官网列 8 月 56 题、9 月 53 题。 | “历史先验很像真的，但新证据说明为假”的来源；避免仅靠改数字制造低价值难度。 |

来源：[首版说明](https://matharena.ai/brokenarxiv/) 的 Introduction、Construction Process、Evaluation Methodology；[更新说明](https://matharena.ai/arxiv_august/) 的 Benchmark Construction / BrokenArXiv adaptations；[官方按月目录](https://matharena.ai/competitions) 的 BrokenArXiv 02/2026、08/2026、09/2026。月份与数量是核查日快照，不拼接成同一冻结题集。

新版评分是：**0** 照单全收并声称证明；**1** 静默修题；**2** 说明改题或诚实未完成但未明确判假；**3** 明确指出假。若其声称成立的修正版与真参考直接矛盾，最高 1 分。Judge 明确禁止因论证错误扣分，除判断上述行为与直接矛盾所需内容。因此“总说是假”仍可满分；“总说不会证明”只到 2/3。这里的 3/3 不是 Math Gauge 的严格通过。来源：[新版评分及文末 BrokenArXiv Judge](https://matharena.ai/arxiv_august/)。

建议借取来源和压力测试方式，同时保留独立的**真假混合、完整证明/反例验收**。全假来源可作为可靠性子测验，不能独自决定研究能力。用论文中的反例构造出题时，应分别保存历史主张、反驳它的新结果、完整前提核对与版本；不要把被推翻的“猜想”写成作者曾证明的“错误定理”。若要做长文错误定位，应另建稿件、明确错误注入和参考诊断，不能沿用 BrokenArXiv 的名称暗示它已经提供这种金标。

## 另外两个最直接的参考

### AutoformBench：缺失的形式化基础设施

Meta 官方发布页（2026-10-13）说明：**341 任务、24 数学来源**，目标声明由有 Lean 经验的数学工作者形式化并审核；实验给予非形式化证明，模型仍须建立缺失定义、辅助引理和支撑结构。官方清单中 `alg_geom_grothendieck_birkhoff` 单任务就有 **19 个评分声明**，包含局部化封闭性和扭层构造等支持义务，直接说明多义务任务有实际先例。来源：[官方摘要](https://ai.meta.com/research/publications/autoformbench-a-lean-formalization-benchmark-for-advanced-mathematics/)、[MANIFEST 第 8 行](https://github.com/facebookresearch/autoformbench/blob/main/MANIFEST.csv#L8)、[该题源码](https://github.com/facebookresearch/autoformbench/blob/main/workspaces/alg_geom_grothendieck_birkhoff/Submission.lean)。

**公开仓库是 source-free；论文榜单是 source-present。** 同一题号不等于同一实验。仓库固定 Lean/Mathlib，要求目标匹配、公理检查及独立内核重放；评分在干净工作区，只接受交付 Lean 文件。工具/环境失败单列。来源：[官方 README 的 Leaderboard、Benchmark release、Use a workspace directly](https://github.com/facebookresearch/autoformbench/blob/main/README.md)、[Harbor 协议的 Trust boundary and grading](https://github.com/facebookresearch/autoformbench/blob/main/harbor/README.md)。

可借鉴的是“给原文但不送齐辅助理论”、不可修改目标、逐义务验收及隔离评分；不能把所有 341 任务都称为整章翻译，也不能把其 source-present 成绩拿来同本项目无工具、单次输出成绩直接比较。直接复制任务前需保留来源许可：官方 README 标注 CC BY-NC 4.0，第三方数学资料另有各自许可；本报告未复制任务正文。论文 PDF 本轮未能取得可读正文，以上均以官方摘要、仓库说明和实际清单/源码为准，未引用未读论文的细节。

### MechAlign / LeanReviewBench：从主定理追到真正定义

2026-10-26 的 v1 给出 **501 个固定“非形式声明—Lean 声明—依赖上下文”实例**：OpenAI Math 的 201 个目标（来自 173 项目）、FLT 的 200 个、Kakeya 的 100 个。它抽取声明类型、非证明定义体及结构限制，排除证明体，并在明示的库边界停止。任务是项目上下文下的语义审阅，并非从零生成整章。来源：[原论文 §3、§4.1、§5](https://arxiv.org/html/2610.35269v1)。

关键限制：一些描述源于 Lean 注释、文档或模型释义，不能据此独立证实忠实于原论文；参考标签仍为暂定模型判断，人类裁决及控制比较尚未完成。故可借鉴依赖提取和局部证据格式，不宜直接当成熟金标。来源：[原论文 §5–6](https://arxiv.org/html/2610.35269v1)。它所举缺失二维条件例子与上游已声明的形式化范围一致，不能说成新发现“OpenAI 论文被推翻”。

## Math Gauge 的下一批设计建议

1. **章级 Lean 翻译**：选 OET 卷 I 一章的冻结原文；给章外必要定义和被许可使用的章外定理，要求交付本章全部正式对象的实现、证明与逐项映射。外部依赖须闭包可用；不能把本章目标通过传递 import 或结构字段预装进去。把“概念/声明由模型设计”和“声明已固定、补完整证明”分成两个轨道，分别衡量语义设计与证明工程，勿混报通过率。
2. **连续数学发展**：一题包含 10–20 个有意义义务。宜有定义良定性、局部结论、兼容性、复合/粘合、最终结论，也有独立支路和一个真正需要综合的汇合点；避免只把独立小题装订，也不要为凑条数把一个显然步骤拆成十条。显式列出的义务不能暗示证明路线；未要求中间目标的“自主建理论”应另外成轨。接受绕开参考路线的有效短证明。
3. **带缺陷的长稿审阅/修复**：冻结一个本来成立的稿件与依赖图，另造少量隐蔽条件漂移，并混入未改动的真稿。要求定位原始失效点、说明影响哪些后继、给满足全部前提的反例或有效修复，最后重新检查全链。作者只把“设计注入错误”记为合成材料，不伪称真实论文勘误。
4. **同一母章分轨但分开评估**：原文→Lean、成品 Lean→语义审阅、缺陷稿→修复可以共享来源，便于分析差别，但测试时须互相隔离，按母章划分校准/正式集，不把相关题算作独立样本。

建议最先做一个完整章级包和两个不同数学主题的证明链包，先验证参照证明与评分器，再扩充。每包要求完整参考、依赖表、可接受替代证明边界、人工状态和出处；不得因为新题更长就预先断言能区分 Terra。

## 如何区分长度效应与真正难度

若每步成功率都是 95%，并且各步独立，则 10 步全部成功只有 **59.9%**，20 步只有 **35.8%**；若每步 98%，20 步也只有 **66.8%**。这些只是 `p^n` 的算术示例，**不是模型估计，真实链条也不独立**。所以全篇通过率下降本身不能证明数学更难。

建议同一母题同时定义三种条件，并保留各自独立运行：

| 条件 | 输入 | 主要诊断 |
| --- | --- | --- |
| 分解基线 | 每个义务单独作答，给正确前置接口/结果；总预算与比较口径预先固定 | 部件本身能否解决 |
| 完整链 | 从同一背景开始，一次持续完成整条发展 | 前后条件管理、理论建设和累积失败 |
| 正确前缀诊断 | 原始运行后另开独立诊断，以作者已核验前缀替换失败祖先 | 后继是否自身不会，还是被上游错误拖累 |

正确前缀诊断不能回填原始成绩。三条件不必用同一绝对上下文长度，但必须记录差异；长度、依赖深度、汇合数、新定义数和预算作为不同维度报告。可再用“同数目、浅依赖”和“同数目、深依赖”配对，避免把篇幅和数学内容变化混为一个变量。

## 必要的评分与失效定位

- **完整完成率与逐义务完成率并列**；Lean 原样编译、声明忠实、公理约束分别给结果。全篇未过不能等同每个子结论均错。
- 每个正式对象有稳定 ID、来源锚点、显式假设、量词依赖、定义域、结论及实际使用的前置结果。按候选真实论证关系审查，不要求它复制参考依赖图。
- 找最早失效声明，同时记录所有互不依赖的根因。在线性题面顺序中的“第一错”只是定位；因果意义上的错误源应依据候选实际使用的依赖。某祖先错误所致的编译连锁或论证空洞应标为传播，不能记成十个独立数学失误。
- 条件漂移重点检查：逐点常数变成统一常数；局部存在变成全局兼容选择；商上的唯一性变成原代表唯一；预算上界变成真实失效量等式；伪度量被误换成有分离性的度量；复合后证书所属定义域发生变化。每次记录“哪条原条件—在哪个声明改变—影响哪些结论”。这些是拟议检查项，不声称每个 OET 章都具备这些问题。
- 修复要求分为“保持原命题修证明”和“承认并改变命题”；后一项只有另作贡献，不能自动算原题完成。负例满分须确实满足原假设并否定原结论，诚实不会证明另列。
- 提供 Lean 反馈的长任务应新建有工具轨道，固定 Lean/Mathlib、工具、网络与检索边界、预算、停止策略、重试政策。保留现有无工具结果作另一条件，不拼进同一通过率。

## 精确取证位置（本轮网页行号是阅读定位，内容更新后可能变化）

| ID | 一手 URL / 文件 | 本轮定位 | 支持的数字或边界 |
| --- | --- | --- | --- |
| B1 | https://matharena.ai/brokenarxiv/ | 网页 L12–16、L20–25、L34–39；Introduction / Construction Process / Evaluation Methodology | 首版 31；扰动题源；0–2；可刷分、非证明正确性 |
| B2 | https://matharena.ai/arxiv_august/ | 网页 L36–43、L118–144、L151–168；BrokenArXiv adaptations / Problem Generation / Problem Verification / Judge | 新版仅历史被反驳主张；0–3；未完成=2；理由错误不评分 |
| B3 | https://matharena.ai/competitions | 网页 L46–52、L99–116；BrokenArXiv 月份条目 | 2 月 31，8 月 56，9 月 53 |
| A1 | https://ai.meta.com/research/publications/autoformbench-a-lean-formalization-benchmark-for-advanced-mathematics/ | 网页 L44–48；Abstract | 2026-10-13；341 任务；24 来源；构建缺失支撑理论 |
| A2 | https://github.com/facebookresearch/autoformbench/blob/main/README.md | 文件 L7–12、L28–30、L44–48、L62–80、L99–103 | source-present 榜单/source-free 发布；固定版本；许可；验收要求 |
| A3 | https://github.com/facebookresearch/autoformbench/blob/main/MANIFEST.csv#L8 | CSV 第 8 行（含表头）；problem_id=alg_geom_grothendieck_birkhoff | 19 个评分声明；未声称 19 个各自等难或一条线性链 |
| A4 | https://github.com/facebookresearch/autoformbench/blob/main/harbor/README.md | 文件 L105–121；Trust boundary and grading | 干净隔离工作区、不可任意迁移评分器、错误单列 |
| A5 | https://github.com/facebookresearch/autoformbench/blob/main/workspaces/alg_geom_grothendieck_birkhoff/Submission.lean | DegreeDLocalization_add_mem、DegreeDLocalization、TwistingSections、SerreTwistConstruction | 实际源码存在局部证明到后续定义的依赖 |
| M1 | https://arxiv.org/html/2610.35269v1 | §3.2（网页 L104–108）、§4.1（L121–122）、§5（L170–183）、§6（L187–188） | 201/173；501=201+200+100；参考标签暂定；人审未完成 |

未使用第三方复述作事实依据。未确认 AutoformBench 数学论文的 arXiv 编号；同名表格识别论文的编号不得误用。当前网页和 main 分支仍可能更新，真正收题时应另冻结源码提交、题面及许可记录的哈希。
