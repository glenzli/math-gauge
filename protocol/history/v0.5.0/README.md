# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 是数学推理、Lean 语义对齐与真实答卷审阅基准。它检查模型能否在实际给定的结构下完成证明、反例、构造、分类或形式化，保持假设、量词、定义域与结论强度，并留下可复核的原始答卷与审核证据。

[Benchmark 对比图](docs/results/comparison-2026-11-03/index.html) · [Gemini 综合结果](docs/gemini-combined-2026-11-03.md) · [Terra 结果页](docs/results/terra-2026-11-03/index.html) · [已发布v0.4.0](https://github.com/glenzli/math-gauge/releases/tag/v0.4.0) · [本地0.5预览指南](docs/release-consumer-README-v0.5.0.md) · [本地选题依据](docs/selection-v0.5.0.md) · [试卷目录](cases/README.md) · [真实答卷审阅](cases/answer-review/README.md) · [当前组成与审阅说明](docs/answer-review-pilot.md) · [评分结构](protocol/benchmark-scoring.md) · [维护操作](docs/usage.md) · [文档导航](docs/README.md)

## 独立任务包

当前源码为 **本地0.5.0预览**，尚未发布。默认30份任务：14份书面、5份Lean审计、5份Lean生成/修复、2章与4份真实答卷审阅；20份备选由显式清单另选。[本地任务包指南](docs/release-consumer-README-v0.5.0.md)说明30份任务/54份计划记录的操作边界，不表示已经存在0.5.0发布资产。

已发布的 [v0.4.0](https://github.com/glenzli/math-gauge/releases/tag/v0.4.0)、[命名任务包](https://github.com/glenzli/math-gauge/releases/download/v0.4.0/benchmark-v0.4.0.zip)和[原操作指南](docs/release-consumer-README-v0.4.0.md)保持原字节；它们继续绑定旧36任务/84记录配置。当前源码不能冒充该已发布版本。后续发布须从确切的干净源提交构建，构建、提交、推送和发布分别留证。

执行端只取得候选题面和白名单附件、一个操作README及可选控制工具；不需要clone仓库、安装Math Gauge或Codex。参考、评分、来源、完整评审计划、作者证据与选题理由留在评审侧；必要署名与许可保留。待审原答属于审阅题明确提供的题目材料，审阅参考仍不进入solver输入。公开数学内容可能被识别，中性包装不等于隐藏题库。

准备、检查、导出、记录与导入均不调用模型。模型只接收本题完整消息、白名单附件和允许的本分支历史；控制工具不作为解题提示。GitHub自动生成的Source code压缩包包含公开评审材料，不能替代命名候选包。分发边界见[分发合同](protocol/release-distribution.md)，历史[v0.1.0发布说明](docs/release-notes-v0.1.0.md)保留原约定。

## 当前基准

默认题集 `cases/suite.json` 为本地0.5.0的 **30份相关任务、21个数学家族**，属于公开开发基准（public development suite）：

| 类别 | 数量 | 内容 |
| --- | ---: | --- |
| `cases/proofs/` | 14 | 书面证明、反例、构造与分类 |
| `cases/lean-audit/` | 5 | 已给 Lean 源码的语义审计 |
| `cases/lean-construction/` | 5 | Lean 生成与修复 |
| `cases/chapters/` | 2 | OET 卷 I 第 2/3 章的完整形式化 |
| `cases/answer-review/` | 4 | 审阅完整原题与真实原答，判断正确性、完整性及缺陷影响 |

当前默认含26份数学交付和4份相关审阅。旧数学成员有126个递进阶段及两章34/92项义务，共252项；新GR021–023的15项书面证明判准另列，不当作新增独立阶段、Lean义务或数学家族。五对Lean审计/构造交付共享家族，4份审阅与母题相关，同母题审阅先聚合。

[20份备选](cases/reserve/README.md)由 `cases/reserve-suite.json` 明确指定：原11个物理备选目录保持原样，另外9份分别引用7个proofs、1个Lean审计、1个Lean修复的原路径。原43份数学卷完整保留，加3份同族加强稿为46份数学卷；连同4份审阅共50条任务记录。[选题说明](docs/selection-v0.5.0.md)列出取舍及未被新题涵盖的旧义务。整章提供含证明原文，审阅题提供真实原答，结果按各自条件解释。

这五类按**交付方式**划分：书面题须给论证或反例；审计题须判断源码是否证明了题面原命题；生成/修复题须交完整源码与逐项对应；整章题须覆盖整章定义、命题及习题义务；审阅题只审阅给定答卷，不要求重新完成母题或提交新Lean。此外，[按考察重点选卷](cases/by-focus.md)列出九个交叉标签：假设与作用域、量词与常数、定义域与提升、结论强度、存在与取到、构造与自然性、证明依赖、Lean语义、完整工程交付。标签附有具体阶段依据，不能重复计为九套独立题或再次加权。

题面、完整参考、逐项判准、来源和 AI 审核材料已经准备。参考答案继续公开，便于透明复核；它们是评审侧出题材料，不属于 solver 题包。现有公开内容与 Git 历史均保留，因此本题集不宣称是未公开留出集。全部题目仍为 **draft / human pending**；`draft` 是待人工审定的生命周期状态。作者 Lean 证据仍只覆盖原43份完整目标、372项义务和470个已真实编译模块；新3份书面题及其15项判准没有作者Lean证据，不继承母题覆盖。MG-GP003 的 S5 已完成任意域上的核心转移几何与原典范单位比较。见[作者证据账本](verification/author/README.md)。作者证明、AI 复核、编译和人工批准分别记录。

## 最新综合结果

当前只保留一个结果入口，路径中的2026-11-03继续使用：[Benchmark对比页](docs/results/comparison-2026-11-03/index.html) · [文字表](docs/benchmark-comparison-2026-11-03.md) · [Terra机器结果](docs/results/terra-2026-11-03/result.json) · [Gemini机器结果](docs/results/gemini-2026-11-03/result.json)。本地0.5.0聚合读取这些路径的冻结机器结果；图表与文字按同一版本刷新。精确分数以机器结果的版本、覆盖和审核快照为准，这里不沿用旧版本总分表。

当前公开计划30份任务/21个家族/54份记录；加入3份私有探索为33份任务/24个家族/57份记录。每模型复用相容原记录、原审核与原数学分，加入3份同输入映射的原生初答：既有矩阵答及两题新实考。后两题本轮共4次原生调用，合并计分本身0调用；选题与合并发生在观察结果之后，不是全任务同步重新考试。原答、旧审核和已发布0.4.0资产不改写，AI审核与人审待办分别记录。

[Terra报告](docs/terra-combined-2026-11-03.md) · [Gemini报告](docs/gemini-combined-2026-11-03.md) · [审阅专图](docs/results/comparison-2026-11-03/answer-review.png) · [审阅评分](protocol/answer-review-scoring.md)。四份审阅的母题和六题重复/自查面板成员不变；严格通过仅辅助，整章义务不是独立题数，后续答卷不替代首次。

## 分项与总分

本地0.5.0公开基准30份任务关联21个数学家族，有五个能力方向；加入3份私有研究探索后为33份任务、24个家族、六方向。每份任务只取首次独立答卷，按其冻结合同归一化；同母题的审阅先聚合。**综合分 = 75%能力分 + 5%重复作答稳定性 + 10%无反馈自查 + 10%立场干扰下的自查。**

| 能力方向 | 公开版权重 | 合并探索后权重 |
| --- | ---: | ---: |
| 书面推理 | 22.5% | 22.5% |
| Lean语义审计 | 22.5% | 18% |
| Lean生成与修复 | 22.5% | 18% |
| 整章形式化 | 22.5% | 18% |
| 研究探索 | — | 13.5% |
| 真实答卷审阅 | 10% | 10% |

审阅每题100分由核心判断60、依据与影响30、补充完整性10构成；重大误判率单列，严格通过仅作辅助诊断。AR纳入、判准及权重是在观察结果后调整，8份既有审阅答卷统一重评，属于方法变更与重算，不是新的AR考试。当前整体另包含三份新题的原生初答；原始执行、答卷与旧审核保留，已发布版本不改。

作答稳定性与自查仍固定选择6题，当前0.3多轮合同使用A1/A2两次独立作答，neutral、支持与怀疑三个分支各一次后续。公开全计划54份记录，合并探索后57份：30或33份A1、6份额外A2、6份无反馈自查、12份立场自查。重复检查两次严格完成，自查看重点数学正确性；能力仍仅取A1。旧A3/R2保留但退出新版默认，按既有A1/A2/R1重算，不重新调用模型。审阅与探索不进入该面板，缺测保留固定分母与区间。

[综合评分标准](protocol/benchmark-scoring.md) · [审阅评分合同](protocol/answer-review-scoring.md) · [组合报告合同](protocol/composite-development-report.md)。九项考察重点仅作交叉诊断，不能重复计入总分。

## 准备与核验

需要 Python 3.10+，共享 runner 无第三方运行依赖。在仓库根目录执行：

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case MG-GR002 --out runs/gr002
python3 -m math_gauge prepare --case MG-C002 --out runs/chapter02
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
```

每次输出目录须是新的。`validate` 检查合同与身份，`prepare` 导出候选材料；两者均不调用模型。实际消息由 `candidate_message(request)` 构造，完整传递题面及白名单附件。参考、评分、来源、真假、审核和作者证明留在评审侧；实际运行隔离另按[协议](protocol/isolated-cli-runs.md)核验。

外部同结构题库可重复传入 `--suite`，无需搬入本仓库。组合清单、自定义 profile、计划/题包导出与历史答卷复用的实际命令见[外部题库组合入口](protocol/composite-development-report.md#外部同结构题库入口)；合并成员不自动决定评分权重。

[真实答卷审阅](cases/answer-review/README.md)已进入默认题集，也可用 `cases/answer-review-suite.json` 单独选择。4份任务保留完整原题与真实原答，仅要求审阅；参考、既有评分和作者模型名留在评审侧。现有8份候选审阅答卷按新规重评，使用同一runner，不另设私有运行器。[正式说明](docs/answer-review-pilot.md)

## 外部 harness 与评审

外部平台按包内 README 完成准备、取题、记录和打包，交回一个 `answers.zip`；执行端无需取得完整评审计划。评审端用 `benchmark-import --input answers.zip --plan ... --out ...` 统一检查并导入，继续使用共享的审核与报告入口。维护接口与历史交换格式见[外部 harness 合同](protocol/external-harness.md)和[维护操作](docs/usage.md)。

| 边界 | 软件与操作者各自负责什么 |
| --- | --- |
| 材料和历史 | 工具检查固定输入、完整消息、父节点、原始答卷、顺序及第一次可读回答锁定。 |
| 独立性和无检索 | harness须实际隔离上下文、文件、记忆、工具状态及搜索能力；目录分开或一句提示不能证明隔离。 |
| 模型和预算 | harness须正确映射实际provider参数、落实超时和输出限制并保留调用记录；型号标签与文件散列不认证后端。 |
| 结论 | 导入不判数学；原样Lean编译、语义对齐、来源审核和人审分别完成。 |

另一个 Codex 可以担任控制器，使用其环境真正支持的候选模型；读过全包的控制器不能兼作答题者，也不能把自己的聊天、记忆或控制材料继承给solver。不支持所选模型派发或所需隔离时，应保留未执行状态。包内指南给出相同流程的启动说明，不依赖本聊天或某个GPT型号。

默认无工具条件保持原样；也可事前显式选择[本地工具、禁止外部搜索的条件](docs/release-consumer-README-v0.5.0.md)，允许本地工具反馈，禁止联网检索/外部搜索及工具联网。它只声明权限，不增加使用工具或Lean的提示、义务或最低用量，原题交付要求不变。独立初答与各分支继续隔离，不接收评审反馈；不同条件分别报告。导入成功只证明材料可接入，正式比较仍需独立核验运行来源、数学审核和适用的 Lean 门槛。

题材来自公开 OET、公开数学资料与独立构造。来源、版本、署名与许可见 [SOURCES.md](SOURCES.md)。公开题可能进入训练数据，本项目不声称它们对模型必然未见。历史版本与实验由 Git 保存，恢复入口见[仓库地图](docs/repository-map.md)。

仓库采用 [MIT 许可证](LICENSE)；第三方材料保留各自的许可和署名。
