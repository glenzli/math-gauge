# 总成本参考

成本是运行观察，不进入 MC、RMC、SMC 或题型权重。当前组件为0.1.0，当前题包为1.0.0；费用来源保留原0.6.0记录身份。页面只展示每个模型的总成本，原始 token 和逐题核对材料留在私有来源中。

## 采用哪些作答

每道题只计当前留档采用的一次作答。有正常交卷时，使用对应答卷的实际调用；全部未交卷时，使用按评测规则最终采用的强制交卷、超时或失败尝试。经确认的云端／API故障后被废弃的尝试、其余重试、被替换的运行、兼容性探测、协调和评审调用均不计入。C003 的三个固定自查轮次各计一次。

一次作答中的工具往返可能产生多次内部 API 请求，它们属于同一次作答，全部合计。原生用量、封卷副本和导入副本须去重。没有实际执行的轮次与执行过但缺少用量的轮次分别记录；缺日志不代表零消耗。

终态累计用量只计一次，不再叠加逐步用量。执行过但缺少回执的生成保留其未知状态；没有明确的来源确认时，费用列为已知小计 `≥`。具名的费用口径确认可采用最终累计回执计算参考总额，原始缺口和确认依据分别留档，不补造 token 或实际账单。

Argon 的参考总额为 **$33.84**，已含两次未交卷：40项形式化约$4.92、整章形式化$7.0545898，其余37题约$21.86。2026-11-12按原生会话身份核对 Infra Sentinel，当前采用的39次作答用量全部一致。整章题75段有回执的生成与终态累计完全一致；按用户确认采用该累计作为参考费用，三次失败流重试不另补估，不再标 `≥`。三次流中断的原始记录与未知用量继续保留，未作 GCP 实际账单对账。

**Dot Underlying (2026-11-08)** 使用订阅附赠的独立额度。用户确认本次额度充足、没有额外付费，因此记 **$0 额外费用**，订阅费不作逐题分摊。日期固定本次观察的身份，后续后端或额度政策变化另行记录。底层模型SKU与 token 用量仍为未知，不据此设置零 token 或推断 API 单价。

DeepSeek 两道未交卷题的327次实际调用已补回。统一按官方峰价折算并保留实测缓存优惠，当前采用作答的 API 参考总额为 **$6.41**。按用户核实的云端记录，无实际模型调用的断流没有额外用量；被废弃重跑、操作主线程和未采用的新整章题不进入本榜成本，已计过的答卷仅作交叉核对。

这一口径衡量采用答卷的资源代价。它不表示实验过程中所有尝试的实际总开销。

## 价格与用量

币种为美元。Dot采用上述具名测试日费用，其余模型使用公开 API 标准价格，计入可核实的缓存优惠。OpenAI 采用标准短上下文价格作统一参考；逐次内部请求的长上下文分档、Fast/Ultrafast 服务费和订阅分摊没有完整证据时，不倒推为实际账单。

Claude Code 明确标为 `list` 的原生标价成本，与其用量和逐模型成本相互核对。Kimi、GLM 等自定义模型的 `costBasis: unknown` 美元字段不直接采用，须根据实际记录的模型及官方价格重算。

归一化保留客户端差异：Codex 的缓存属于输入子集；AGY 原生普通输入与缓存输入分开；Claude Code 的普通输入、缓存读取和缓存写入分开。推理 token 已包含在相应输出计数中，不重复相加。缓存和必要价格项缺失时保持未知。

DeepSeek 主榜统一采用官方峰价：输入未命中、缓存命中和输出分别为每百万 token $0.30、$0.006、$1.20，缓存命中量按实际记录计算。这与 [Artificial Analysis 当前该型号展示的费率](https://artificialanalysis.ai/models/deepseek-v4-1-flash-1017/)一致，避免运行时段影响成本比较。原按运行时段峰谷混合折算的$4.30保留在来源记录中。

价格来源：[OpenAI](https://developers.openai.com/api/docs/pricing)、[Google Gemini](https://ai.google.dev/gemini-api/docs/pricing)、[Google Cloud](https://cloud.google.com/gemini-enterprise-agent-platform/generative-ai/pricing)、[Claude](https://platform.claude.com/docs/en/about-claude/pricing)、[Kimi](https://platform.kimi.ai/)、[GLM](https://docs.z.ai/guides/overview/pricing)、[DeepSeek](https://api-docs.deepseek.com/quick_start/pricing/)。折算不含无法核实的代理加价、税费、赠金或订阅权益。

## 来源核对

- 用量齐全或经来源绑定确认采用最终累计回执：发布采用作答的 API 参考总额。原始生成缺口单独保留。
- 测试日费用已独立确认：按该日使用费用发布总额；未知 token 与后端身份保持未知。
- Terra Max：四个历史用量缺口已通过原始调度输出与原生账本唯一匹配补齐，42个成本位置均有真实用量，参考总额为 **$10.96**，不再标 `≈`。
- Gemini 3.8 Flash：余下四项通过恢复的会话编号、调度时间及原生账本请求散列精确对应，用量覆盖42/42，API参考总额为 **$23.41**，不再标 `≈`。
- Kimi、GLM：按用户确认的调用方留存记录折算，参考总额为 **$29.85／$40.88**。原先的在途和断流用量估算退出当前总额；原来源与估算过程保留。
- 仍缺用量的其他模型：只发布已知小计 `≥`，不列成本名次。
- 没有可用价格或用量：显示空值，不记作免费。

此前估算过程及其敏感性范围保留在私有来源材料中。当前总额采用已核实原生用量、具名确认的累计回执、调用方留存记录或测试日费用，来源与提取过程均保留供核查。

2026-11-12的Kimi／GLM云端包包含1532条唯一调用记录。按会话及原始尝试号核对后，只计当前采用的81次作答（Kimi42、GLM39；GLM三轮自查未运行），采用904条记录，排除其余628条。22个原缺口位置的267条原始用量字段与台账逐项一致，缓存已包含在API输入中，不重复相加。

用户确认该包来自调用方并已按时间、模型逐项核对：没有对应调用方记录就不额外补估。本次按原字段折算为 **Kimi $29.853496／GLM $40.87734396**；其中Kimi的7条ERROR记录仍按其留存输入字段计入，参考费用为$0.366596。输出0、错误状态与已生成内容均按来源原样保留；此处的零字段不认证底层物理生成量为0。该具名确认只适用于本批调用方留存口径，不改变其他来源的缺失规则，也不构成实际账单对账。

## 前沿图

默认横轴为总成本，纵轴为 RMC；成本与耗时均使用从0开始的线性刻度，坐标距离按实际金额或分钟数成比例显示。可切换到耗时横轴或 MC、SMC，标题与坐标说明随选择更新。所有模型使用相同大小的点：实心表示39道初答均正常交卷；正常交卷不足39题的一律为空心，强制收取的数学内容不算正常交卷。此标记在成本／耗时和MC／RMC／SMC切换时保持一致，不按得分或审核覆盖判断。悬浮或键盘聚焦可查看数值及正常交卷数。

典型耗时直接使用[现有耗时参考](answer-timings.md)的五道日常题加权均值，不使用并行批次的墙钟跨度。数学成绩来自共享评分器的当前采用答卷，不重新配权。

Pareto 前沿保留无法同时在更低资源消耗和更高成绩上被另一个模型超过的点；至少一项严格更好才构成支配。成本前沿只用费用已核对且成绩已测完的模型确定，估算与成本下限点仅作观察。零费用直接位于线性坐标原点。耗时前沿使用同一组五题的已记录加权耗时与完整成绩，不受成本是否齐全影响。未测完的成绩不参与两种实线前沿。

## 来源与复算

`math_gauge/costs.py` 负责计数归一化、费用算术、来源字节校验和安全公开投影；`scripts/collect_cost_reference.py` 读取既有资料，不调用模型。私有成本记录保留42个位置的采用依据、原始用量提取及缺口；公开投影只包含模型总额、状态、匿名覆盖和来源散列。

成本通过 `record_binding` 关联每个模型的原始留档记录，并逐位置绑定采用尝试和答卷散列。原始 token、缓存字段、计费约定、价格表及来源均保留在同一成本记录中，可按相同来源重新计算总额。

私有证据采用内容散列归档：字节相同的文件只保存一份，`evidence-archive.json` 列出整理前每个路径及其对应 SHA 对象。原 ZIP、调用台账、提取结果、来源确认和原成本记录都保留原字节，每个原文件均可从清单恢复。旧阶段目录由整理前的 Git 检查点保存，工作目录只保留当前选择。公开端保留匿名费用投影。

`scripts/compact_cost_evidence.py` 只调整证据位置，逐项检查用量、价格、采用身份、覆盖状态及模型总额保持一致。共享采集器的 `--check` 同时核对完整对象清单、当前答卷绑定和公开投影。复算补充文件引用同一份已绑定的模型成本记录，避免再复制模型用量和证据树；原提取版本仍在散列对象中留存。

主榜由 `scripts/render_results_site.py` 接入独立成本面板。原答、原评、现有成绩、发布题包和既有费用账本均不因这项观察而改写。

## English summary

The cost panel reports one retained attempt per task, or the last retained failed attempt when none delivered. Prescribed self-check rounds are included once; other retries and evaluator calls are excluded. Internal API requests within an included attempt are summed.

Dot Underlying (2026-11-08) used a separate allowance included with the subscription. The user confirmed that this allowance covered the tests without additional payment, so its additional cost is $0; the subscription is not amortized per task. Its backend SKU and token usage remain unknown. Other values use USD API reference prices with verified cache discounts. Argon's $33.84 includes both nondeliveries (about $11.98). All 39 selected native totals match Infra Sentinel; its C003 final cumulative receipt equals the sum of 75 reported generation steps. The user selected that reported usage as the reference-cost scope, without imputing the three failed stream retries. Their original usage gaps remain retained; this is not GCP invoice reconciliation. Source-bound cost resolutions preserve the original counters and their coverage. DeepSeek's 327 recovered calls from its two selected nondeliveries are included. Its benchmark total uses uniform official peak rates with measured cache discounts, giving $6.41; the former time-of-day calculation of $4.30 remains in the source record. Terra Max's four historical gaps are now closed by unique original-dispatch/native-ledger matching: all 42 cost slots have actual usage, giving a $10.96 reference total without an approximation mark. Gemini 3.8 Flash now also has actual usage for all 42 cost slots: the remaining four calls were recovered by exact native receipt hashes using restored conversation IDs and submission times, giving an API reference total of $23.41 without an approximation mark. Kimi and GLM use the user-confirmed API caller ledger: 904 records are bound to 81 retained attempts, while the other 628 records are excluded. Repricing the recorded fields yields $29.853496 and $40.87734396. Kimi includes $0.366596 from the input fields of seven ERROR records. The caller scope replaces prior imputation; absent records and recorded zero-output fields do not receive generated-token estimates. Original native evidence, statuses and prior estimates remain retained. This source-specific confirmation is not an invoice reconciliation or a general missing-log exemption. All plot points have equal size. Solid points mean all 39 initial tasks have normal final submissions. Fewer than 39 is always hollow; forcibly collected content does not count. This marker stays unchanged across cost/time axes and MC/RMC/SMC modes, independently of score or review coverage. Tooltips and accessible labels include the normal-submission count. Cost and time use linear axes starting at zero, so distances reflect actual dollar amounts or minutes. The cost frontier requires verified costs and completed evaluations; the time frontier uses recorded five-task weighted time independently of cost coverage. Raw usage and private task identifiers stay private.
