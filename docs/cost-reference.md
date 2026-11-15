# 总成本参考

成本是运行观察，不进入 MC、RMC、SMC 或题型权重。当前组件为0.1.0，当前题包为1.0.0；各批来源保留实际0.6.0或1.0.0身份，不因接入当前榜单而改写执行版本。页面展示模型总额或已知小计，原始 token 和逐题核对材料留在私有来源中。

## 采用哪些作答

每道题只计当前留档采用的一次作答。有正常交卷时，使用对应答卷的实际调用；全部未交卷时，使用按评测规则最终采用的强制交卷、超时或失败尝试。经确认的云端／API故障后被废弃的尝试、其余重试、被替换的运行、兼容性探测、协调和评审调用均不计入。C003 的三个固定自查轮次各计一次。

一次作答中的工具往返可能产生多次内部 API 请求，它们属于同一次作答，全部合计。原生用量、封卷副本和导入副本须去重。没有实际执行的轮次与执行过但缺少用量的轮次分别记录；缺日志不代表零消耗。

终态累计用量只计一次，不再叠加逐步用量。执行过但缺少回执的生成保留其未知状态；没有明确的来源确认时，费用列为已知小计 `≥`。具名的费用口径确认可采用最终累计回执计算参考总额，原始缺口和确认依据分别留档，不补造 token 或实际账单。

Argon原选定39道初答的参考小计为 **$33.84**，已含两次未交卷：40项形式化约$4.92、整章形式化$7.0545898，其余37题约$21.86。2026-11-12按原生会话身份核对 Infra Sentinel，当前采用的39次作答用量全部一致。整章题75段有回执的生成与终态累计完全一致；按用户确认采用该累计作为参考费用，三次失败流重试不另补估，不再标 `≥`。三次流中断的原始记录与未知用量继续保留，未作 GCP 实际账单对账。

**Dot Underlying (2026-11-08)** 使用订阅附赠的独立额度。用户确认本次额度充足、没有额外付费，因此记 **$0 额外费用**，订阅费不作逐题分摊。日期固定本次观察的身份，后续后端或额度政策变化另行记录。底层模型SKU与 token 用量仍为未知，不据此设置零 token 或推断 API 单价。

DeepSeek 两道未交卷题的327次实际调用已补回。统一按官方峰价折算并保留实测缓存优惠，当前采用作答的 API 参考总额为 **$6.41**。按用户核实的云端记录，无实际模型调用的断流没有额外用量；被废弃重跑、操作主线程和未采用的新整章题不进入本榜成本，已计过的答卷仅作交叉核对。

这一口径衡量采用答卷的资源代价。它不表示实验过程中所有尝试的实际总开销。

## 价格与用量

币种为美元。Dot采用上述具名测试日费用，有可核实单价的模型使用公开 API 标准价格，计入可核实的缓存优惠。OpenAI 采用标准短上下文价格作统一参考；逐次内部请求的长上下文分档、Fast/Ultrafast 服务费和订阅分摊没有完整证据时，不倒推为实际账单。

Argon采用测试时有效的公开Standard限时五折价：每百万token普通输入$2、缓存命中$0.10、输出（含思考）$10；加上新三轮自查后，当前合计 **$37.74**。[Google官方定价](https://aistudio.google.com/docs/pricing#gemini-4-argon)注明优惠截至2026年11月30日，12月1日起分别为$4／$0.20／$20；相同用量届时折算约$75.48。当前榜单保留本次价格快照。[Artificial Analysis的Argon页面](https://artificialanalysis.ai/models/gemini-4-argon)在2026年11月14日同样采用$2输入、$10输出和95%缓存折扣。

Argon于2026-11-14通过订阅补测C003三轮，原生用量按上述快照折算为$3.9060102，主榜仍采用原39道初答，加三轮为$37.7417155。新失败起点仅用于接续，不作为第二份初答计入主榜；起点加三轮的补充测试额外参考消耗为$9.9117267，独立留档。订阅实付不作逐题分摊。

Gemini 3.8 Flash于2026-11-15（新加坡时间）通过AGY订阅补跑C003三轮。当前参考总额为 **$22.49**：保留原39道初答$20.644864275，将旧三轮$2.762847075替换为新三轮$1.847472825，精确合计$22.4923371。三次非数学环境检查与一次已证实配置故障另记$0.107847825，不计入采用的42份交付。原$23.40771135费用快照保留，原初答计时不变；详见[补测费用来源](../results/v0.6.0/gemini-3.8-flash-high/20261105/supplements/c003-20261114/cost-source.json)。

Gemini 4 Hydrogen（xhigh）通过AGY CLI1.5.7的consumer订阅运行，42份采用答卷的原生累计用量全部留存，含三轮固定自查。[官方Standard API价格](https://aistudio.google.com/docs/pricing#gemini-4-hydrogen)为每百万token普通输入$1.50、缓存命中$0.075、输出（含思考）$7.50，参考总额 **$51.63**；xhigh是同一型号的[思考档位](https://aistudio.google.com/docs/thinking)。该型号[只支持隐式缓存](https://aistudio.google.com/docs/caching)，没有适用的显式缓存写入或存储费用；原生未提供的写入计数仍保留为空。普通输入与缓存读取分别计价，思考量已包含在输出中。此值是统一API参考成本，订阅实际账单不作逐题分摊。

Carbon Medium采用作答的API参考总额为 **$56.99**。未正常交卷的私有手稿题已切换为最后有效第三次尝试：原生ERROR终态报告输入318,981、输出166,842、缓存读取1,141,933 token，思考69,811已包含在输出中；该次参考费用$2.4205753。总额只计38份正常初答、这一次未交卷及三轮固定自查。最后内部生成43未有独立终态用量，未补造token或推断云端账单；采用原生累计回执的参考口径。前轮、安全审核辅助调用与其余重试不计入，原始用量与旧费用均保留。

Claude Code 明确标为 `list` 的原生标价成本，与其用量和逐模型成本相互核对。Kimi、GLM 等自定义模型的 `costBasis: unknown` 美元字段不直接采用，须根据实际记录的模型及官方价格重算。

归一化保留客户端差异：Codex 的缓存属于输入子集；AGY 原生普通输入与缓存输入分开；Claude Code 的普通输入、缓存读取和缓存写入分开。推理 token 已包含在相应输出计数中，不重复相加。缓存和必要价格项缺失时保持未知。

DeepSeek 主榜统一采用官方峰价：输入未命中、缓存命中和输出分别为每百万 token $0.30、$0.006、$1.20，缓存命中量按实际记录计算。这与 [Artificial Analysis 当前该型号展示的费率](https://artificialanalysis.ai/models/deepseek-v4-1-flash-1017/)一致，避免运行时段影响成本比较。原按运行时段峰谷混合折算的$4.30保留在来源记录中。

价格来源：[OpenAI](https://developers.openai.com/api/docs/pricing)、[Google Gemini](https://aistudio.google.com/docs/pricing)、[Google Cloud](https://cloud.google.com/gemini-enterprise-agent-platform/generative-ai/pricing)、[Claude](https://platform.claude.com/docs/en/about-claude/pricing)、[Kimi](https://platform.kimi.ai/)、[GLM](https://docs.z.ai/guides/overview/pricing)、[DeepSeek](https://api-docs.deepseek.com/quick_start/pricing/)。折算不含无法核实的代理加价、税费、赠金或订阅权益。

## 来源核对

- 用量齐全或经来源绑定确认采用最终累计回执：发布采用作答的 API 参考总额。原始生成缺口单独保留。
- 测试日费用已独立确认：按该日使用费用发布总额；未知 token 与后端身份保持未知。
- Terra Max：四个历史用量缺口已通过原始调度输出与原生账本唯一匹配补齐，42个成本位置均有真实用量，参考总额为 **$10.96**，不再标 `≈`。
- Gemini 3.8 Flash：余下四项通过恢复的会话编号、调度时间及原生账本请求散列精确对应，原42份用量覆盖完整，旧API参考总额为 **$23.41**，不再标 `≈`。采用新三轮自查后，当前为 **$22.49**，来源另绑且没有重复加总。
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

Gemini 3.8 Flash's current reference total is **$22.49** after adopting the three new AGY subscription self-checks. The unchanged 39 A1 slots cost $20.644864275; the new rounds replace the old $2.762847075 with $1.847472825, totaling $22.4923371. Three environment checks and one excluded configuration failure add $0.107847825 to workflow records only. The original $23.40771135 snapshot and A1 clocks remain retained.

The cost panel reports one retained attempt per task, or the last retained failed attempt when none delivered. Prescribed self-check rounds are included once; other retries and evaluator calls are excluded. Internal API requests within an included attempt are summed.

Carbon Medium's selected-attempt API reference total is **$56.99**. The failed manuscript slot now uses its final effective third attempt: native ERROR reported318,981input,166,842output and1,141,933cache-read tokens;69,811thinking tokens are already included in output. That attempt contributes$2.4205753. The total counts38normal A1 finals, this one failed attempt and three fixed rounds. Logical generation43 has no separate terminal usage; no missing tokens or cloud invoice charge are inferred. Earlier retries and auxiliary safety calls are excluded; original counters and earlier costs remain retained.

Gemini 4 Hydrogen's 42 retained receipts, including the three fixed self-check rounds, yield **$51.63** at official Standard API rates: $1.50 ordinary input, $0.075 cache hits and $7.50 output including thinking per million tokens. Its xhigh setting uses the same model tariff. Implicit-only caching makes explicit cache writes and storage inapplicable; unavailable native write counters remain null. Argon's **$37.74**, including the three new self-check rounds, uses the published introductory rates through November 30, 2026 ($2 / $0.10 / $10); the same usage at the announced December rates would cost about $75.48. Artificial Analysis currently uses the same introductory rates. These are API reference costs, not an allocation of subscription fees.

Dot Underlying (2026-11-08) used a separate allowance included with the subscription. The user confirmed that this allowance covered the tests without additional payment, so its additional cost is $0; the subscription is not amortized per task. Its backend SKU and token usage remain unknown. Other values use USD API reference prices with verified cache discounts. Argon's original39-A1 subtotal of$33.84 includes both nondeliveries (about $11.98). All 39 selected native totals match Infra Sentinel; its C003 final cumulative receipt equals the sum of 75 reported generation steps. The user selected that reported usage as the reference-cost scope, without imputing the three failed stream retries. Their original usage gaps remain retained; this is not GCP invoice reconciliation. Source-bound cost resolutions preserve the original counters and their coverage. DeepSeek's 327 recovered calls from its two selected nondeliveries are included. Its benchmark total uses uniform official peak rates with measured cache discounts, giving $6.41; the former time-of-day calculation of $4.30 remains in the source record. Terra Max's four historical gaps are now closed by unique original-dispatch/native-ledger matching: all 42 cost slots have actual usage, giving a $10.96 reference total without an approximation mark. Gemini 3.8 Flash has actual usage for all original 42 cost slots: the remaining four calls were recovered by exact native receipt hashes using restored conversation IDs and submission times, giving the retained historical total of $23.41 without an approximation mark. Replacing its three self-check rounds yields the current $22.49 total described above. Kimi and GLM use the user-confirmed API caller ledger: 904 records are bound to 81 retained attempts, while the other 628 records are excluded. Repricing the recorded fields yields $29.853496 and $40.87734396. Kimi includes $0.366596 from the input fields of seven ERROR records. The caller scope replaces prior imputation; absent records and recorded zero-output fields do not receive generated-token estimates. Original native evidence, statuses and prior estimates remain retained. This source-specific confirmation is not an invoice reconciliation or a general missing-log exemption. All plot points have equal size. Solid points mean all 39 initial tasks have normal final submissions. Fewer than 39 is always hollow; forcibly collected content does not count. This marker stays unchanged across cost/time axes and MC/RMC/SMC modes, independently of score or review coverage. Tooltips and accessible labels include the normal-submission count. Cost and time use linear axes starting at zero, so distances reflect actual dollar amounts or minutes. The cost frontier requires verified costs and completed evaluations; the time frontier uses recorded five-task weighted time independently of cost coverage. Raw usage and private task identifiers stay private.

The three subscription self-check rounds add $3.9060102 at the frozen API reference tariff, giving $37.7417155 for the retained39 A1 answers plus3 rounds. The new failed seed is used only as a self-check starting point, not charged as a second main-benchmark A1. Seed plus three rounds cost $9.9117267 in additional study calls; this is reported separately, not treated as subscription invoicing.


## Carbon High · 2026-11-15

采用的39道初答及固定三轮自查按原生首次终态边界留档，42份采用交付的原生用量均已对齐。API参考总额为 **$73.52**，仅含本条件各槽采用尝试的候选原生累计用量；未交卷采用最后有效尝试。普通输入与缓存读取分别计价，思考量已包含在输出中；其他物理重试及安全审核辅助调用另存，不计入该参考总额。该API价格折算不等同于实际订阅账单。见[逐槽公开摘要](../results/v0.6.0/gemini-4-carbon-high/20261115/cost-reference.json)与[模型详情](../site/models/gemini-4-carbon-high/index.html)。

The 2026-11-15 Carbon High selected-attempt API reference is **$73.52**, with complete native usage for all 42 selected deliveries. It counts candidate-native cumulative usage once per selected slot, with cache and thinking counted once. Other physical retries and auxiliary safety calls are retained separately and excluded from this total. The API-price reference is distinct from an actual subscription invoice.
