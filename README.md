# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 是数学推理与 Lean 语义对齐基准。它检查模型能否在实际给定的结构下完成证明、反例、构造、分类或形式化，保持假设、量词、定义域与结论强度，并留下可复核的原始答卷与审核证据。

[题包运行说明](docs/release-consumer-README-v0.3.0.md) · [试卷目录](cases/README.md) · [选卷依据](docs/selection-v0.3.0.md) · [Terra 开发试跑](docs/terra-pilot-2026-11-02.md) · [评分结构](protocol/benchmark-scoring.md) · [维护操作](docs/usage.md) · [文档导航](docs/README.md)

## 独立任务包

当前默认题集及 Release 版本均为 **0.3.0**。交付资产为中性命名的 `benchmark-v0.3.0.zip`：32份任务及其约定附件、一个简明 README，以及可选控制工具；备选11题不进入默认包。解压后可接入外部 harness，需要 Python 3.10+；不需要 clone 仓库、安装 Math Gauge、第三方 Python 包或 Codex。

只把命名 ZIP 交给执行 harness，不必把仓库或 Release 网页作为上下文。包内不放本项目名称、仓库地址、成绩、答案或出题说明；必要的原作品署名与许可保留。操作入口是[包内 README 的源文件](docs/release-consumer-README-v0.3.0.md)：冻结模型、预算与范围，取得完整消息，保存原始答卷，再打包 `answers.zip`。公开数学内容仍可能被识别，中性包装不等于隐藏题库。

维护者从干净的发布提交构建任务包：

```sh
python3 scripts/release.py build --version 0.3.0 \
  --out runs/releases/v0.3.0
```

构建、检查、准备请求、记录与导入均不调用模型。控制工具只供 harness 操作者使用，不是候选模型的解题工具。模型只接收本题完整消息、约定附件和允许的本分支历史。参考、评分、完整评审计划及作者证据留在包外。

历史 [v0.1.0 Release](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0) 及其[发布说明](docs/release-notes-v0.1.0.md)保持不变；它采用旧版本约定和目录。GitHub 自动生成的 **Source code** 压缩包包含公开参考答案，不能代替命名任务包。包结构和维护约束见[分发合同](protocol/release-distribution.md)。

## 当前基准

默认题集 `cases/suite.json` 是含 **32 份完整试卷的公开开发题集（public development suite）**：

| 类别 | 数量 | 内容 |
| --- | ---: | --- |
| `cases/proofs/` | 18 | 书面证明、反例、构造与分类 |
| `cases/lean-audit/` | 6 | 已给 Lean 源码的语义审计 |
| `cases/lean-construction/` | 6 | Lean 生成与修复 |
| `cases/chapters/` | 2 | OET 卷 I 第 2/3 章的完整形式化 |

一个完整题组或一章是一份相关样本。默认30份递进题组含180阶段，两章分别含34/92项义务，合计306项审核义务；**默认样本数为32，不能记为306**。另外11题/66阶段放在 [cases/reserve/](cases/reserve/README.md)，由 `cases/reserve-suite.json` 显式选用；两集不重叠，构成43题/372义务的完整题库。原始题目、Lean和参考保留。整章题提供含证明的原文，测量该条件下的形式化能力。

这四类按**交付方式**划分：书面题须给论证或反例；审计题须判断源码是否证明了题面原命题；生成/修复题须交完整源码与逐项对应；整章题须覆盖整章定义、命题及习题义务。此外，[按考察重点选卷](cases/by-focus.md)列出九个交叉标签：假设与作用域、量词与常数、定义域与提升、结论强度、存在与取到、构造与自然性、证明依赖、Lean语义、完整工程交付。标签附有具体阶段依据，不能重复计为九套独立题或再次加权。

题面、完整参考、逐项判准、来源和 AI 审核材料已经准备。参考答案继续公开，便于透明复核；它们是评审侧出题材料，不属于 solver 题包。现有公开内容与 Git 历史均保留，因此本题集不宣称是未公开留出集。全部题目仍为 **draft / human pending**；`draft` 是待人工审定的生命周期状态。作者 Lean 证据覆盖 43/43 份完整目标、372/372 项义务，470 个模块已有真实编译记录；MG-GP003 的 S5 已完成任意域上的核心转移几何与原典范单位比较。见[作者证据账本](verification/author/README.md)。作者证明、AI 复核、编译和人工批准分别记录。

## 已有结果的口径

| 结果 | 题目与计分方式 | 综合分 | 状态 |
| --- | --- | ---: | --- |
| Terra 原始开发试跑 | 旧43题/177槽，各题三次初答平均 | **95.84** | 原冻结结果；AI评审，暂定 |
| 同批答卷按32题方案事后重算 | 32份A1及六题重复/自查面板，共选80槽 | **93.15** | 开发分析；不是一次新运行 |
| 0.3.0中性任务包独立运行 | 发布后冻结执行的32题/80槽 | — | 尚未运行 |

两种已算分结果来自同批旧答卷，不能作为两次独立实验。新版方案能力分只取A1，因此C003使用20/92项，不能取后两次较好的62/92、70/92项；32份A1严格通过31/32，能力分90.22，三个可靠性分项均为100。重算发生在选题之后，也没有使用新发布包的中性标识符输入，不能替代新版独立评测。

[完整结果与失败分析](docs/terra-pilot-2026-11-02.md)保留原始口径、25个原样Lean项目核验、限制及[重算依据](docs/results/terra-2026-11-02-v0.3.0-posthoc.json)。题目和答卷仍未获人工批准，不能称为正式排行榜成绩。选卷是观察结果后的开发决定，见[选卷依据](docs/selection-v0.3.0.md)。

## 分项与总分

四类任务分别报告完成分，每份卷先归一化，**能力分只取32份 A1，四类各25%**。六题固定面板额外各做 A2/A3，并各开中性、支持与怀疑三个分支，每枝两轮。**综合分 = 70% 能力分 + 10% 面板三次全对 + 10% 中性自查正确性 + 10% 立场下正确性**。额外独立作答不重复加权能力分；严格整卷通过、数学错误、Lean问题和题包问题另外报告。

七个方向均可独立选择。完整计划为 **80槽：32份 A1 + 12份额外独立作答 + 12份中性自查 + 24份立场自查**。单跑中性或立场目标还需同六题的 A1，分别为18/30次。缺测保留固定分母与区间，不把子集得分冒充总体；自查与立场分项只代表预选六题的重点断言。

权重、范围和公式见[评分标准](protocol/benchmark-scoring.md)与[机器配置](protocol/benchmark-profile.json)，操作见[使用指南](docs/usage.md)。九项考察重点是交叉诊断切片，不能重复计入总分。

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

## 外部 harness 与评审

外部平台按包内 README 完成准备、取题、记录和打包，交回一个 `answers.zip`；执行端无需取得完整评审计划。评审端用 `benchmark-import --input answers.zip --plan ... --out ...` 统一检查并导入，继续使用共享的审核与报告入口。维护接口与历史交换格式见[外部 harness 合同](protocol/external-harness.md)和[维护操作](docs/usage.md)。

| 边界 | 软件与操作者各自负责什么 |
| --- | --- |
| 材料和历史 | 工具检查固定输入、完整消息、父节点、原始答卷、顺序及第一次可读回答锁定。 |
| 独立性和无检索 | harness须实际隔离上下文、文件、记忆、工具状态及搜索能力；目录分开或一句提示不能证明隔离。 |
| 模型和预算 | harness须正确映射实际provider参数、落实超时和输出限制并保留调用记录；型号标签与文件散列不认证后端。 |
| 结论 | 导入不判数学；原样Lean编译、语义对齐、来源审核和人审分别完成。 |

另一个 Codex 可以担任控制器，使用其环境真正支持的候选模型；读过全包的控制器不能兼作答题者，也不能把自己的聊天、记忆或控制材料继承给solver。不支持所选模型派发或所需隔离时，应保留未执行状态。包内指南给出相同流程的启动说明，不依赖本聊天或某个GPT型号。

默认无工具条件保持原样；也可事前显式选择[本地工具、禁止外部搜索的条件](docs/release-consumer-README-v0.3.0.md)，允许本地工具反馈，禁止联网检索/外部搜索及工具联网。它只声明权限，不增加使用工具或Lean的提示、义务或最低用量，原题交付要求不变。独立初答与各分支继续隔离，不接收评审反馈；不同条件分别报告。导入成功只证明材料可接入，正式比较仍需独立核验运行来源、数学审核和适用的 Lean 门槛。

题材来自公开 OET、公开数学资料与独立构造。来源、版本、署名与许可见 [SOURCES.md](SOURCES.md)。公开题可能进入训练数据，本项目不声称它们对模型必然未见。历史版本与实验由 Git 保存，恢复入口见[仓库地图](docs/repository-map.md)。

仓库采用 [MIT 许可证](LICENSE)；第三方材料保留各自的许可和署名。
