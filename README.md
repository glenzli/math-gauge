# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 是数学推理、Lean 语义对齐与真实答卷审阅基准。它检查模型能否在实际给定的结构下完成证明、反例、构造、分类或形式化，保持假设、量词、定义域与结论强度，并留下可复核的原始答卷与审核证据。

[Benchmark 对比图](docs/results/comparison-2026-11-03/index.html) · [Gemini 综合结果](docs/gemini-combined-2026-11-03.md) · [Terra 结果页](docs/results/terra-2026-11-03/index.html) · [获取v0.4.0](https://github.com/glenzli/math-gauge/releases/tag/v0.4.0) · [题包说明](docs/release-consumer-README-v0.4.0.md) · [试卷目录](cases/README.md) · [真实答卷审阅](cases/answer-review/README.md) · [当前组成与审阅说明](docs/answer-review-pilot.md) · [评分结构](protocol/benchmark-scoring.md) · [维护操作](docs/usage.md) · [文档导航](docs/README.md)

## 独立任务包

当前题集与任务包版本为 **0.4.0**，默认含36份任务：原32份数学卷与4份真实答卷审阅。已发布0.3.0及历史资产保持原样。当前命名任务包为[benchmark-v0.4.0.zip](https://github.com/glenzli/math-gauge/releases/download/v0.4.0/benchmark-v0.4.0.zip)，含候选任务与约定附件、一个简明README及可选控制工具；备选11题不进入默认包。解压后可接入外部 harness，需要 Python 3.10+；不需要 clone 仓库、安装 Math Gauge、第三方 Python 包或 Codex。

只把命名 ZIP 交给执行 harness，不必把仓库或 Release 网页作为上下文。包内不放本项目名称、仓库地址、成绩、评审参考答案或出题说明；待审答卷属于审阅任务的题目材料，审阅参考与判准留在包外。必要的原作品署名与许可保留。操作入口是[包内 README 的源文件](docs/release-consumer-README-v0.4.0.md)：冻结模型、预算与范围，取得完整消息，保存原始答卷，再打包 `answers.zip`。公开数学内容仍可能被识别，中性包装不等于隐藏题库。

维护者完成本地版本核验后，可从干净的指定提交构建任务包；构建不等于远端发布：

```sh
python3 scripts/release.py build --version 0.4.0 \
  --out runs/releases/v0.4.0
```

构建、检查、准备请求、记录与导入均不调用模型。控制工具只供 harness 操作者使用，不是候选模型的解题工具。模型只接收本题完整消息、约定附件和允许的本分支历史。参考、评分、完整评审计划及作者证据留在包外。

历史 [v0.1.0 Release](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0) 及其[发布说明](docs/release-notes-v0.1.0.md)保持不变；它采用旧版本约定和目录。GitHub 自动生成的 **Source code** 压缩包包含公开参考答案，不能代替命名任务包。包结构和维护约束见[分发合同](protocol/release-distribution.md)。

## 当前基准

默认题集 `cases/suite.json` 是含 **36份相关任务的公开开发基准（public development suite）**：

| 类别 | 数量 | 内容 |
| --- | ---: | --- |
| `cases/proofs/` | 18 | 书面证明、反例、构造与分类 |
| `cases/lean-audit/` | 6 | 已给 Lean 源码的语义审计 |
| `cases/lean-construction/` | 6 | Lean 生成与修复 |
| `cases/chapters/` | 2 | OET 卷 I 第 2/3 章的完整形式化 |
| `cases/answer-review/` | 4 | 审阅完整原题与真实原答，判断正确性、完整性及缺陷影响 |

原32份数学卷仍含30个递进题组、180阶段和两章34/92项义务，共306项；义务不是独立试题。4份审阅任务关联既有4份母题并共享历史来源，不能当作4个独立新增数学家族；同母题先聚合。另11份数学卷/66阶段放在[cases/reserve/](cases/reserve/README.md)，由显式清单选用。原43份数学卷与新增4份审阅共47条相关任务记录，原始题目、Lean、原答与参考保留。整章题提供含证明原文，审阅题提供真实原答，结果按各自条件解释。

这五类按**交付方式**划分：书面题须给论证或反例；审计题须判断源码是否证明了题面原命题；生成/修复题须交完整源码与逐项对应；整章题须覆盖整章定义、命题及习题义务；审阅题只审阅给定答卷，不要求重新完成母题或提交新Lean。此外，[按考察重点选卷](cases/by-focus.md)列出九个交叉标签：假设与作用域、量词与常数、定义域与提升、结论强度、存在与取到、构造与自然性、证明依赖、Lean语义、完整工程交付。标签附有具体阶段依据，不能重复计为九套独立题或再次加权。

题面、完整参考、逐项判准、来源和 AI 审核材料已经准备。参考答案继续公开，便于透明复核；它们是评审侧出题材料，不属于 solver 题包。现有公开内容与 Git 历史均保留，因此本题集不宣称是未公开留出集。全部题目仍为 **draft / human pending**；`draft` 是待人工审定的生命周期状态。原43份数学卷的作者 Lean 证据覆盖43/43份完整目标、372/372 项义务，470 个模块已有真实编译记录；MG-GP003 的 S5 已完成任意域上的核心转移几何与原典范单位比较。见[作者证据账本](verification/author/README.md)。作者证明、AI 复核、编译和人工批准分别记录。

## 最新综合结果

[当前Benchmark对比页](docs/results/comparison-2026-11-03/index.html)展示六个能力方向、作答稳定性与自查、真实答卷审阅主分与重大误判、两章完整交付。[文字表](docs/benchmark-comparison-2026-11-03.md) · [PNG](docs/results/comparison-2026-11-03/comparison.png) · [SVG](docs/results/comparison-2026-11-03/comparison.svg)

[![Math Gauge当前对比](docs/results/comparison-2026-11-03/comparison.png)](docs/results/comparison-2026-11-03/index.html)

| 模型 | 综合分 | 能力分 | 审阅主分 | 重大误判 |
| --- | ---: | ---: | ---: | ---: |
| Terra 6.1 Max | **94.62** | **92.83** | 98.75 | 0/4 |
| Gemini 3.8 Flash High | **72.37** | **65.94** | 69.38 | 1/4 |

当前合并范围39份任务、35个母题家族、87份记录；公开默认范围36份任务、32个家族、84份记录。AR纳入、60/30/10判准与8份既有原答重评发生在观察结果后，是方法变更与重算，不是新考试。AI审核 / 人审待办，0.4.0题库与任务包版本一致，原答、旧审核与已发布资产保留。

[审阅专图](docs/results/comparison-2026-11-03/answer-review.png)单列4份任务、重大误判0/4与1/4；严格通过仅辅助，不用未满分全清零。稳定性与自查只选6份数学题，中性100分不代表全部交付通过。整章另列34/34与0/34、20/92与0/92；义务不是独立题数，后续答卷不替代首次。

[Terra报告](docs/terra-combined-2026-11-03.md) · [Gemini报告](docs/gemini-combined-2026-11-03.md) · [审阅评分](protocol/answer-review-scoring.md) · [组合合同](protocol/composite-development-report.md)

## 分项与总分

公开基准36份任务关联32个母题家族，有五个能力方向；综合开发报告加入3份私有研究探索后为39份任务、35个母题家族、六方向。每份任务只取首次独立答卷，按其冻结合同归一化；同母题的审阅先聚合。**综合分 = 75%能力分 + 5%重复作答稳定性 + 10%无反馈自查 + 10%立场干扰下的自查。**

| 能力方向 | 公开版权重 | 合并探索后权重 |
| --- | ---: | ---: |
| 书面推理 | 22.5% | 22.5% |
| Lean语义审计 | 22.5% | 18% |
| Lean生成与修复 | 22.5% | 18% |
| 整章形式化 | 22.5% | 18% |
| 研究探索 | — | 13.5% |
| 真实答卷审阅 | 10% | 10% |

审阅每题100分由核心判断60、依据与影响30、补充完整性10构成；重大误判率单列，严格通过仅作辅助诊断。AR纳入、判准及权重是在观察结果后调整，8份既有审阅答卷统一重评，属于方法变更与重算，不是新考试。原始执行、答卷与旧审核保留，已发布版本不改。

作答稳定性与自查从公开数学任务中固定选择6题。公开全计划84份记录，合并探索后87份：36或39份首次答卷、12份额外独立答卷、12份无反馈自查、24份立场自查。重复检查三次严格全对，自查看重点数学正确性；额外答卷不重复进入能力分。审阅和探索目前不在重复/自查范围内，缺测保留固定分母与区间。

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

默认无工具条件保持原样；也可事前显式选择[本地工具、禁止外部搜索的条件](docs/release-consumer-README-v0.4.0.md)，允许本地工具反馈，禁止联网检索/外部搜索及工具联网。它只声明权限，不增加使用工具或Lean的提示、义务或最低用量，原题交付要求不变。独立初答与各分支继续隔离，不接收评审反馈；不同条件分别报告。导入成功只证明材料可接入，正式比较仍需独立核验运行来源、数学审核和适用的 Lean 门槛。

题材来自公开 OET、公开数学资料与独立构造。来源、版本、署名与许可见 [SOURCES.md](SOURCES.md)。公开题可能进入训练数据，本项目不声称它们对模型必然未见。历史版本与实验由 Git 保存，恢复入口见[仓库地图](docs/repository-map.md)。

仓库采用 [MIT 许可证](LICENSE)；第三方材料保留各自的许可和署名。
