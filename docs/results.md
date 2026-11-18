# 当前完整结果

Benchmark **1.0.0**已封版。当前采用聚合 **0.9.0**／MC **0.3.0**／SMC **0.2.0**，提交来源组件 **0.1.0**；RMC为默认主分。

39道初答（公25／私14）、35个数学家族，另有固定三轮Lean自查。书面35／Lean35／研究30，始终按完整100分报告，未测项保留未知范围。

| 模型 | Harness | MC | RMC（主分） | SMC | 主动／强收／总题数 |
|---|---|---:|---:|---:|---:|
| [Astra 6 (max)](../site/models/astra-6-max/index.html) | Codex CLI | 94.32 | 94.32 | 89.17 | 39／0／39 |
| [Sol 6.1 (max)](../site/models/sol-6.1-max/index.html) | Codex CLI | 94.32 | 94.22 | 89.17 | 39／0／39 |
| [Sol 6.2 (max)](../site/models/sol-6.2-max/index.html) | Codex CLI | 93.21 | 93.21 | 89.17 | 39／0／39 |
| [Claude Opus 5.5 (max)](../site/models/claude-opus-5.5-max/index.html) | Claude Code | 93.76 | 91.44 | 59.42 | 39／0／39 |
| [Astra 6 (xhigh)](../site/models/astra-6-xhigh/index.html) | Codex CLI | 91.45 | 90.45 | 79.17 | 39／0／39 |
| [Dot Underlying (2026-11-08)](../site/models/dot-underlying-model-20261108/index.html) | Dot native harness¹ | 91.66 | 90.23 | 78.00 | 39／0／39 |
| [Claude Sonnet 5.5 (max)](../site/models/claude-sonnet-5.5-max/index.html) | Claude Code | 91.95 | 88.20 | 55.42 | 39／0／39 |
| [Sol 6.1 (xhigh)](../site/models/sol-6.1-xhigh/index.html) | Codex CLI | 90.12 | 87.96 | 68.00 | 39／0／39 |
| [Terra 6.1 (max)](../site/models/terra-6.1-max/index.html) | Codex CLI | 82.62 | 80.85 | 65.67 | 39／0／39 |
| [Gemini 4 Carbon (medium)](../site/models/gemini-4-carbon-medium/index.html) | AGY CLI⁴ | 91.78 | 79.74 | 64.50 | 38／1／39 |
| [Terra 6.1 (xhigh)](../site/models/terra-6.1-xhigh/index.html) | Codex CLI | 79.71 | 78.50 | 63.00 | 39／0／39 |
| [Gemini 4 Hydrogen (xhigh)](../site/models/gemini-4-hydrogen-xhigh/index.html) | AGY CLI⁴ | 87.80 | 76.81 | 47.92 | 39／0／39 |
| [Gemini 4 Carbon (high)](../site/models/gemini-4-carbon-high/index.html) | AGY CLI⁴ | 88.51 | 74.78 | 32.83 | 38／1／39 |
| [Kimi 3.1 Pro (max)](../site/models/kimi-3.1-pro-max/index.html) | Claude Code | 75.28 | 70.41 | 43.67 | 38／0／39 |
| [Gemini 4 Argon (high)](../site/models/gemini-4-argon/index.html) | AGY CLI⁴ | 86.33 | 70.24 | 37.92 | 38／1／39 |
| [DeepSeek v4.1 Flash (max)](../site/models/deepseek-v4.1-flash-1017/index.html) | Codex CLI² | 76.71 | 64.23 | 25.83 | 37／1／39 |
| [Gemini 3.8 Flash (high)](../site/models/gemini-3.8-flash-high/index.html) | AGY CLI⁴ | 59.94 | 39.77 | 13.75 | 38／1／39 |
| [GLM 5.3 (max)](../site/models/glm-5.3-max/index.html) | Claude Code³ | 41.48 | 27.34 | 14.08 | 21／5／39 |

排序先看所选口径；显示到两位小数仍同分时，依次用其余的RMC、SMC、MC降序比较。三项全同，再按有来源的初答测试时间升序；日期未知放后，同日按已知启动时刻比较；时刻缺失的排在该日已知时刻后，其余完全相同则保持稳定顺序。新批次用已记录的首次派题时刻，其余用留档公开初答中最早已记录的启动时间；这只是展示顺序，不新增评分，也不从档号或提交时间推测测试日期。

主动交卷与强收有内容互斥；强收表示留有可审核数学内容，MC可以为0。三轮自查另列，执行状态与完整区间见模型档案。后续测试完成结算并选定留档后再上榜。

⁴ AGY CLI留档中发现较严重的回传与终态处理缺陷，可能丢失模型回复或空等至超时。此类故障允许额外重跑，实际调用次数可能超过通常3次；已核实的末尾空等从展示耗时扣除，原始记录保留。正常交卷后不因数学错误重跑。

## Sol 6.2 Max · 2026-11-18

本轮为1.0.0题库的全新测试，39份正常初答及三轮正常自查均已审核。MC/RMC为93.2083，SMC为89.1667。相较Sol 6.1 Max，MC下降1.1111、RMC下降1.0111、SMC持平；主要差异是公开命题拓展TX001保留正确基础证明，但未完成上一版答卷中已有的尖锐性拓展。另有一份私有手稿消除了旧答独立附带错误的扣分。其余37题及整段自查的评分一致，不能据这两题推断普遍提升或下滑。

内容可靠率100.00%、完整目标达成率90.92%；五份手稿的主动额外成果已按共同边界审核，观察结果不计入主分。实际43次物理请求含1次已证实的控制器误拦截；该次不占有效模型次数，选定42次交付均为首次有效作答。请求gpt-6.2-sol/max，CLI版本0.169.0-alpha.11.1，后端标签未回显。全部允许本地工具，禁止联网检索和工具联网。

39份初答的原生执行耗时中位数约8.19分钟，三轮自查另计；实际批次跨度约4小时47分，包含并行、暂停与控制器恢复，不作为模型纯推理速度。原生用量完整保留；按已核实的Sol 6.2 Standard公开单价折算，采用42份答卷的API参考成本约$17.35，沿用原榜口径，不表示实际订阅扣费。AI审核、编译证据与人工批准继续分开。

## 本次方法调整

每题采用首次正常交卷，随后停止，不为数学错误重跑。有正常交卷时，三种评分只审核实际交付的正文及明确提交的工程；未随答复交付的更大封存工程不补入。

没有正常交卷时，MC可以审核本条件内最后一次有效尝试在截止前已存在的原始数学正文或完整工程文件。来源、截止与数学内容须分别核实；不能修补源码、拼尝试、把数值脚本当作证明或从思考日志拼出答案。RMC与SMC为0。未测研究题继续保留潜在得分和扣分范围。

既有初答按已有原件完成提交分类和来源复核；另有具名C003补充测试，三轮来源单独登记。原0.8.0政策、原记录和六视图按散列另存；原答、原评与题目保留原字节。规则见[提交来源规范](../protocol/submission-scoring.md)。

## 来源复核要点

- Terra Max按实际正常答卷采用C003初答18/92及三轮0→0→33；诊断分仍独立审核。旧74/92等额外封存工程不补入正常交卷。
- Gemini 3.8的HCH02正常返回原模块未通过内核，按0/40；错误核验保证另行扣罚。其C003无正常交卷轮次的截止原工程仅可计MC，正常轮次只审实际返回。
- DeepSeek的GR023截止正文保留有效MC；没有正常交卷，RMC与SMC为0。
- GLM的39份初答来源审核完成，三项末次缺档已由2026-11-11补充材料复核销项，原分数不变；三轮自查未执行，继续保留未知。[补充复核记录](../results/v0.6.0/glm-5.3-max/20261110/review-completion.json)。
- Argon采用20261111完整记录：37份原CLI正常交卷，另接纳1份因harness回传故障而恢复的HCH02原答；C003仍无正常交卷；另从新订阅封卷工程完成C003固定三轮补充自查，以正常最终回复及完整工程交付。首答和规则重试条件各绑定自身实际尝试，不交叉借用工程。

## 内容可靠率与完整目标

两率使用共同697个承诺单元与149个完整成果目标。内容可靠率检查实际断言的正确性和论证支持；目标达成率验收完整独立成果，保留类别、家族和变体权重。正常答卷来源发生更正时另行复核，原审核仍保留。定义、目标和权重没有增加。

| 模型 | 已审内容可靠率 | 已确认目标达成率 |
|---|---:|---:|
| [Astra 6 (max)](../site/models/astra-6-max/index.html) | 100.00% | 90.92% |
| [Sol 6.1 (max)](../site/models/sol-6.1-max/index.html) | 99.90% | 90.92% |
| [Sol 6.2 (max)](../site/models/sol-6.2-max/index.html) | 100.00% | 90.92% |
| [Claude Opus 5.5 (max)](../site/models/claude-opus-5.5-max/index.html) | 94.22% | 85.84% |
| [Astra 6 (xhigh)](../site/models/astra-6-xhigh/index.html) | 98.68% | 87.36% |
| [Dot Underlying (2026-11-08)](../site/models/dot-underlying-model-20261108/index.html) | 99.65% | 85.29% |
| [Claude Sonnet 5.5 (max)](../site/models/claude-sonnet-5.5-max/index.html) | 90.83% | 83.38% |
| [Sol 6.1 (xhigh)](../site/models/sol-6.1-xhigh/index.html) | 98.93% | 82.61% |
| [Terra 6.1 (max)](../site/models/terra-6.1-max/index.html) | 97.93% | 72.51% |
| [Gemini 4 Carbon (medium)](../site/models/gemini-4-carbon-medium/index.html) | 93.59% | 83.60% |
| [Terra 6.1 (xhigh)](../site/models/terra-6.1-xhigh/index.html) | 99.80% | 69.67% |
| [Gemini 4 Hydrogen (xhigh)](../site/models/gemini-4-hydrogen-xhigh/index.html) | 90.53% | 78.42% |
| [Gemini 4 Carbon (high)](../site/models/gemini-4-carbon-high/index.html) | 88.92% | 84.24% |
| [Kimi 3.1 Pro (max)](../site/models/kimi-3.1-pro-max/index.html) | 91.14% | 68.03% |
| [Gemini 4 Argon (high)](../site/models/gemini-4-argon/index.html) | 83.13% | 69.78% |
| [DeepSeek v4.1 Flash (max)](../site/models/deepseek-v4.1-flash-1017/index.html) | 76.64% | 57.36% |
| [Gemini 3.8 Flash (high)](../site/models/gemini-3.8-flash-high/index.html) | 65.28% | 38.79% |
| [GLM 5.3 (max)](../site/models/glm-5.3-max/index.html) | 69.48% | 32.44% |

Carbon Medium内容可靠率93.5938864629%、完整目标达成率83.60%；697项断言与149项完整目标均已判定。本次只更新最后强收手稿的来源与相应成果判断，其余38题及固定三轮自查不改判，断言／目标契约与权重不变。

[两率规则](../protocol/content-rates.md) · [主动额外成果观察](manuscript-observations.md)。额外成果仅描述原任务未要求的独立成果组数，不进入主分或两率；既有模型的数学判断和组数不变，Hydrogen新增核实11组。

## 记录与复算

模型详情展示大类、子类、公开逐题结果、固定自查轨迹、完整原答和来源。所有图表读取共享评分器，排序和指标显示设置只影响页面。耗时表位于能力榜单底部，解释见[时间记录](answer-timings.md)。

所有正式任务允许本地工具及预置公共依赖，禁止联网检索与工具联网；实际工具使用和harness版本按来源批次记录。纯系统故障凭证据排除；最大输出耗尽消耗有效尝试；正常数学错误不再重试。

当前结果采用AI审核，并有部分人工抽审。既有全审记录由Sol 6.1 Max完成，Astra 6 Max／Dot抽审核对；Carbon保留本轮AI审核来源。[审核说明](review-process.md)。

[当前排行榜](../site/index.html) · [评分规范](../protocol/benchmark-scoring.md) · [完整档案](../results/README.md)

1.0.0通过[源绑定兼容记录](../releases/v1.0.0/compatibility.json)复用既有答卷及当前判分。原答、原评、六种成绩视图和实际运行版本保持不变；新版本不代表重新运行。评分组件的独立版本号沿用原值。

HCH02恢复原答的更正于2026-11-13按用户确认计入，原判分标准和benchmark1.0.0不变。该原答代码块原样编译失败，核验承诺按Flash同题标准扣罚；C003补测前的总分为MC77.00／RMC60.91／SMC37.92。原始ERROR、原记录及旧成绩保留，见[更正说明](harness-corrections.md)。

Gemini 4 Hydrogen（xhigh）使用AGY CLI1.5.7订阅完成39道初答与三轮固定自查。整章形式化首答及三轮均核实92/92；R1、R2诊断不准确，自查SMC不通过。三大类RMC贡献为书面25.30/35、Lean33.33/35、研究18.18/30；所有评分使用同一批规则选定答卷。本次没有新增人工数学批准。

Argon于2026-11-14通过AGY CLI1.5.9订阅完成三轮整章工程补充自查。初答封卷与三轮工程均核实92／92，无回退；R2虚述未提供的全空间接口，R3大量声明与章节定位失实。按原70／30规则，三轮100／95／85，自查计9.33／10，整段SMC不通过；当前总分MC86.33／RMC70.24／SMC37.92。原39个初答、HCH02更正及正常交卷38／39保持不变。见[补充条件与统一准入](c003-sealed-continuation.md)。

Flash于2026-11-15（新加坡时间）通过AGY CLI1.5.9订阅完整补跑三轮。父工程与三轮均核实74／92，新增修复与回退均为0；R1只整理已有定理别名、映射和未导入草稿，R2／R3的Lean源码及对齐表相同。编译与公理检查通过，但18项语义缺口仍在。三轮均诊断0／30并误报完整，各扣20分，自查分项MC0／RMC−2／SMC0（满分10），当前总分MC59.94／RMC39.77／SMC13.75。原39份初答与旧报告保持，详见[三轮结果](../results/v0.6.0/gemini-3.8-flash-high/20261105/supplements/c003-20261114/README.md)。


## Carbon整轮运行与来源说明

一项私有手稿题在三次有效尝试后仍无正常交卷，现仅按最后一次截止时封存的完整原稿评审MC，RMC／SMC为0。三项总分为91.78／79.74／64.50；未改规则、未合并前轮内容。 原采用尝试与旧评审保留，新增审核单独绑定原稿及截止记录。

[Carbon Medium模型详情](../site/models/gemini-4-carbon-medium/index.html)与[公开来源选择说明](../results/v0.6.0/gemini-4-carbon-medium/20261115/source-selection-disclosure.json)保留采用边界。当前MC91.78／RMC79.74／SMC64.50，38份正常交卷、1项强收有内容，无空白初答。2026-11-15新加坡时间01:00后额外补测C003，累计物理第7次／有效第6次正常交卷；实际初答及三轮KEEP均AI核验92／92，诊断准确、无回退，整条轨迹Strict通过。此前五次有效失败及物理第6次原ERROR均保留；物理第6次已证明是本地控制器误拒原生上下文压缩，单独排除，不计模型尝试。初答用时116分23.8秒，三轮合计34分30.1秒；首次口径及其余38题保持。

包含High、Medium与环境排查的旧批次及排查从2026-11-11 17:01:45 UTC延续至2026-11-14约14:30 UTC，随后本次C003补测于2026-11-14约21:17 UTC结束，跨越两天以上；旧Medium批次窗口约47小时40分，此后另行补测C003。两者表示不同范围的经过时间，均包含等待与运行中断。AGY/GCP期间频繁断流、超时与HTTP429；这些记录影响未交卷的归因。Argon与Carbon的已审复杂题同时暴露出严重推理错误及完成问题。最初的High批次未形成可用的成套答卷；2026-11-15续跑已完成结算。

本次来源采用包含用户观察后明确接纳的额外补试；原物理次数、有效次数与此前失败均保留，第4／5次没有改写成通常三次以内的重试资格。正常交卷锁定来源，不因数学错误重跑，不挑最高分、不跨尝试拼卷。AI评审、人工待审与原比较资格分别保留；用户接纳来源不构成人工数学批准。

当前API参考总额为$56.9869815：唯一无回执的内部请求经Infra Sentinel核对后，按用户确认以0补记费用；安全审核辅助调用不计入。原生用量缺失状态保持，原答卷保留题源版本0.6.0身份，通过独立的来源兼容记录接入当前benchmark1.0.0；本次整理与接入不再调用候选模型。


Carbon High 的 2026-11-15 续跑现已结算：39道初答中38份正常交卷、1项强收有内容、0项无可审核正文；MC／RMC／SMC为88.51/74.78/32.83。先测非Lean题，再测Lean题，最后接续C003及固定三轮自查；成功试跑直接留作正式答卷。AGY1.5.9后继原生请求的HIGH／MEDIUM档位按原请求保留；已确证的本地控制或认证TLS故障单独留证，不消耗有效尝试；无法确证为纯系统故障的断流保留原计次，作答超时和输出耗尽计次。逐题数学判断、三轮状态及实际条件见[模型详情](../site/models/gemini-4-carbon-high/index.html)和[来源说明](../results/v0.6.0/gemini-4-carbon-high/20261115/source-selection-disclosure.json)。

Carbon High 的完整历史补充见[尝试与重试统计](execution-attempts.md)：共62条任务尝试记录，其中51次有效、11项系统排除；42个规定槽外额外20条，包含9次有效重试。旧异常表的7条为早期时间截点的部分样本，保留原值和原归因。该补充不改变答卷来源、任何分数或原生执行记录。

本批High保留共同697项断言和149项完整目标合同；三种分数、两率、时间与费用均绑定同一批规则选定来源。采用尝试API参考$73.52，42份采用交付的原生用量均已对齐；其他重试与安全审核辅助调用另存，不计入该参考总额。
