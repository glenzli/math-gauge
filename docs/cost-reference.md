# 总成本参考

应用户要求，当前 1.2.0／1.3.0 的 Dot (261125) 按已付订阅内的本轮 **$0 额外费用**计入当前费用比较。该数字不是底层推理成本或订阅费；用量、底层模型 SKU 和原生 API 价格仍未知。历史配置的留档计价不变。[补采来源](../results/dot-native-timings/v0.1.0/dot-20261125/evidence-replacement-v1/index.json)。

In current editions 1.2.0 and 1.3.0, the user counts Dot (261125) as **$0 additional cost for this run under the existing subscription**. This is not the inference cost or subscription price; token usage, backend SKU and native API pricing remain unknown. Historical cost observations are unchanged. [Replacement source](../results/dot-native-timings/v0.1.0/dot-20261125/evidence-replacement-v1/index.json).

## 1.3 独立开放研究

当前候选成本在既有首答、自查及采用续答的完整费用上，加上独立开放研究三轮的有效开销。原生日志中的跨轮累计计数先按事件链核对并去重，不把每轮累计总数相加，也不按题目占分或品味／能力权重折算费用。费率沿用已冻结的 API 参考价；它是用量折算，不代表订阅账单或已认证后台 SKU。已测十个 GPT 配置新增费用合计 $25.4450848。未测项保留总额未知及已有成本下限。

2026-11-24 外部五配置再新增 **$35.512417696**：Opus Max $11.2651446、Opus xHigh $14.4660992、Sonnet Max $6.9469012、Kimi Max $2.5847068、DeepSeek Max $0.249565896。Claude/Kimi 的三次用量快照属于同一 session 累计，最终累计只计一次；Kimi 按原用量和既有单价重算，不采用计价依据不明的原生估额。DeepSeek 已确认无效的系统运行不进入该增量。原包与逐轮差分保留在私有侧，公开端仅提供[外部资源聚合](../protocol/mathematical-taste/v1.3.0/external-resources.json)。这五配置与原十配置的资源来源分别绑定。

The five external configurations add **$35.512417696** at the retained 1.2 API reference rates. Final cumulative session usage is counted once, including effective internal retries; confirmed invalid system runs are excluded. This is a usage-based reference, not a subscription invoice. The external resource component remains separate from the original ten-configuration source.

Carbon medium 新增独立研究的40条唯一响应已核回 **12,160,567 tokens**（含缓存），按既有费率计入 **$6.8454724**；与既有测试合计，当前费用参考为 **$88.724143**\*（页面显示 **$88.72**\*）。按用户选择，以已记录用量统计，首轮三段未返回用量的中断尾部不另补估。**\* Carbon：费用按已记录用量统计，少量中断用量可能未计入。** 原始未知用量保留，不补零，累计快照不重复相加；原生诊断、控制器排查和评审开销不计候选成本。[本次资源聚合](../protocol/mathematical-taste/v1.3.0/native-additions/gemini-4-carbon-medium-resources.json)与[费用口径选择](../protocol/mathematical-taste/v1.3.0/native-additions/gemini-4-carbon-medium-cost-selection.json)分别留存。

Carbon medium’s new research trajectory adds **$6.8454724** for **12,160,567 tokens**, including cache reads, at the retained API reference tariff. The user-selected recorded-usage reference totals **$88.724143**\*, displayed as **$88.72**\*. **\* Carbon: costs use recorded usage; a small amount of interrupted usage may be uncounted.** The three unreported R1 tail generations are not imputed; original unknown usage remains unknown, and cumulative usage is counted once. Diagnostic and evaluator calls remain separate.

评审与候选开销分开：当前评审缺少足以核实费用的原生用量，评审成本标为未知，不填零。公开资源投影只保存按配置的合计、覆盖和不透明来源哈希，原生证据与私有题目留在评审端。

耗时继续使用同一组共有公开题和单列整章形式化，不纳入独立开放研究。成本／耗时—成绩图使用当前版本成绩，未知完整分保留已确认值与区间，资源或成绩不齐不进入完整 Pareto 前沿。纵轴下界按当前所选口径最低有效分向下取到 20 的整数倍，上界 100；刻度直接标示实际范围，原始分数与前沿计算不变。

DeepSeek的26道采纳中性续答按原留存峰价新增 **$8.45211162**，与基础测试合计 **$14.86493916**。逐请求记录核对出非缓存输入4,069,652、缓存输入645,731,070、输出2,797,358 tokens，总计652,598,080；原input包含cache，未重复相加。26个有效作答内部共3,843次上游请求，全部纳入同一次作答的完整开销；两条原生工具参数JSON错误的响应保留用量，没有按502状态码直接排除为系统故障。该费用是API参考额，后台SKU未独立认证。

Astra 6.2 xHigh（2026-11-20）采用39份初答、三轮固定自查和9份中性续答。按已留存Astra 6.2 Standard短上下文费率对51次有效尝试的完整原生用量各计一次，基础参考费用$63.7598564，续答$13.9851176，合计 **$77.744974**，共46,604,269 tokens。20%权重只用于数学成绩，续答资源全额计入。两次已确认容量／网络系统故障及独立预检不计有效用量、费用或时间；这两次缺少终态用量不使有效费用变成未知。原53次物理调用报告与原生失败记录保留，实际内部HTTP请求数仍未知。该值为统一API参考价，未冒充实际账单或已认证后端SKU。

Astra 6.2 xHigh counts the full observed usage of 51 effective attempts once:42 base deliveries cost $63.7598564 and nine revisions cost $13.9851176, giving an API reference total of **$77.744974** for 46,604,269 tokens. Confirmed capacity/network system failures and the independent canary stay outside effective usage, cost and timing statistics. Their missing terminal counters do not make effective cost unknown. Original physical-request reports remain retained; internal HTTP-call counts and the backend SKU remain unknown. The 20% weighting applies only to scores.

Claude Opus5.5 xHigh（2026-11-19）采用39份初答与三轮固定自查，全部有原生累计用量：**47,305,953 tokens，list参考总额$104.18**。输入、缓存读取、缓存写入与输出分别保留，thinking已含在输出中，不重复叠加。R1首次纯系统断流的1,728,015 tokens／$2.3699428另留原记录，不计采用交付；其余模型成本条目保持原字节。

成本是运行观察，不进入 MC、RMC、SMC 或题型权重。当前组件为0.1.0，当前题包为1.0.0；各批来源保留实际0.6.0或1.0.0身份，不因接入当前榜单而改写执行版本。页面展示模型总额或已知小计，原始 token 和逐题核对材料留在私有来源中。

Sol 6.2 Max的42份采用答卷均有原生用量，按已核实的[官方Sol 6.2 Standard价格](https://developers.openai.com/api/docs/models/gpt-6.2-sol)折算，API参考总额为 **$17.35**：每百万token输入$2、缓存输入$0.10、输出$10；本批缓存写入为0。它是与旧榜一致的参考口径，不是订阅实际扣费。另一次控制器误拦截未计入采用答卷费用，原先尚未核价的资源摘要保持原字节，补充价格证据另留档。

Astra 6.2 Max的42份采用交付均有原生用量，以2026-11-19核实的[官方Standard短上下文价格](https://developers.openai.com/api/docs/models/gpt-6.2-astra)折算为 **$77.46**：每百万token输入$8、缓存读取$0.40、30分钟缓存写入$10、输出$40；本批缓存写入为0。3次纯系统中断及非数学环境探测不计入。官方对单次输入超过272K的请求另收2倍输入／缓存价、1.5倍输出价；现有终态累计计数不足以还原每次内部请求的上下文档位，因此此值明确采用短上下文统一参考价，不是实际订阅账单或逐请求完整计价。

Gemini 4 Neon (xHigh) 的60份有效交付均有完整原生用量：42份基础答卷参考费用 **$88.9622955**，18份续答 **$48.8936544**，合计 **$137.8559499**。使用留存的Standard API参考价：每百万token非缓存输入$3、缓存输入$0.15、输出$15；thinking已在输出内，不重复计入。13次确认的纯系统中断仅留重试历史，不进入该总额。它不是订阅账单，后端SKU仍未独立认证。[本轮资源](../results/continuation-resources/v0.1.0/gemini-4-neon-xhigh-20261122.json)

Gemini4 Neon (xHigh) has complete native usage for all60 effective deliveries:42 base answers cost **$88.9622955** and18 adopted revisions **$48.8936544**, totaling **$137.8559499** at the retained Standard API reference tariff ($3 uncached input / $0.15 cached input / $15 output per million tokens). Thinking is already included in output. Thirteen confirmed system interruptions remain in retry history only. This is not a subscription invoice or independent backend-SKU verification.

## 采用哪些作答

每道题只计当前留档采用的一次作答。有正常交卷时，使用对应答卷的实际调用；全部未交卷时，使用按评测规则最终采用的强制交卷、超时或失败尝试。经确认的云端／API故障后被废弃的尝试、其余重试、被替换的运行、兼容性探测、协调和评审调用均不计入。C003 的三个固定自查轮次各计一次。

1.2.0在首答和规定自查成本上加计采纳续答的有效开销，复用的试答每份计一次。确认的系统故障单列重试。Astra 6 Max的恢复续答有用量回执，剔除其前一次容量故障后，累计 API 参考成本为 **$102.77**。[1.2.0说明](neutral-revision.md)

本次Claude／Kimi中性续答完整用量均已入库。新增API参考成本分别为Opus Max $41.78、Opus xHigh $23.87、Sonnet Max $24.99、Kimi Max $4.27；与各自首答及三轮自查合计约为$207.80、$128.05、$176.02、$34.13。三份Claude原生list金额逐条与留存费率核对一致。Kimi的19条原生金额均标为`costBasis=unknown`，并数值吻合另一套fallback费率，故保留原金额但不采用；改用实际输入、缓存写入和输出计数及已有Kimi Standard费率计算。该值是API等价参考，不是订阅实际扣费，基础测试的估计标记继续保留。

一次作答中的工具往返可能产生多次内部 API 请求，它们属于同一次作答，全部合计。原生用量、封卷副本和导入副本须去重。没有实际执行的轮次与执行过但缺少用量的轮次分别记录；缺日志不代表零消耗。

终态累计用量只计一次，不再叠加逐步用量。执行过但缺少回执的生成保留其未知状态；没有明确的来源确认时，费用列为已知小计 `≥`。具名的费用口径确认可采用最终累计回执计算参考总额，原始缺口和确认依据分别留档，不补造 token 或实际账单。

Argon原选定39道初答的参考小计为 **$33.84**，已含两次未交卷：40项形式化约$4.92、整章形式化$7.0545898，其余37题约$21.86。2026-11-12按原生会话身份核对 Infra Sentinel，当前采用的39次作答用量全部一致。整章题75段有回执的生成与终态累计完全一致；按用户确认采用该累计作为参考费用，三次失败流重试不另补估，不再标 `≥`。三次流中断的原始记录与未知用量继续保留，未作 GCP 实际账单对账。

**Dot (261108)** 使用订阅附赠的独立额度。用户确认本次额度充足、没有额外付费，因此记 **$0 额外费用**，订阅费不作逐题分摊。日期固定本次观察的身份，后续后端或额度政策变化另行记录。底层模型SKU与 token 用量仍为未知，不据此设置零 token 或推断 API 单价。

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

默认横轴为总成本，纵轴为 SMC。成本与耗时均使用从0开始的线性刻度，坐标距离按实际金额或分钟数成比例显示。可切换到耗时横轴或 RMC、MC，标题与坐标说明随选择更新。所有模型使用相同大小的点：实心表示39道初答均正常交卷；正常交卷不足39题的一律为空心，强制收取的数学内容不算正常交卷。此标记在成本／耗时和MC／RMC／SMC切换时保持一致，不按得分或审核覆盖判断。悬浮或键盘聚焦可查看数值及正常交卷数。

耗时横轴取本版本耗时参考的日常题加权均值。1.2.0使用12道共有计时的公开非 Lean 题，含这些题的有效续答耗时。1.0.0和1.1.0保留五题样本。数学成绩来自共享评分器的当前采用答卷。[耗时参考](answer-timings.md)

Pareto 前沿保留无法同时在更低资源消耗和更高成绩上被另一个模型超过的点，至少一项严格更好才构成支配。成本前沿使用已核对费用与完整成绩，估算与成本下限点仅作观察。零费用位于线性坐标原点。耗时前沿使用共有样本的加权耗时与完整成绩。两种前沿均以粗虚线标示。

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

Dot (261108) used a separate allowance included with the subscription. The user confirmed that this allowance covered the tests without additional payment, so its additional cost is $0; the subscription is not amortized per task. Its backend SKU and token usage remain unknown. Other values use USD API reference prices with verified cache discounts. Argon's original39-A1 subtotal of$33.84 includes both nondeliveries (about $11.98). All 39 selected native totals match Infra Sentinel; its C003 final cumulative receipt equals the sum of 75 reported generation steps. The user selected that reported usage as the reference-cost scope, without imputing the three failed stream retries. Their original usage gaps remain retained; this is not GCP invoice reconciliation. Source-bound cost resolutions preserve the original counters and their coverage. DeepSeek's 327 recovered calls from its two selected nondeliveries are included. Its benchmark total uses uniform official peak rates with measured cache discounts, giving $6.41; the former time-of-day calculation of $4.30 remains in the source record. Terra Max's four historical gaps are now closed by unique original-dispatch/native-ledger matching: all 42 cost slots have actual usage, giving a $10.96 reference total without an approximation mark. Gemini 3.8 Flash has actual usage for all original 42 cost slots: the remaining four calls were recovered by exact native receipt hashes using restored conversation IDs and submission times, giving the retained historical total of $23.41 without an approximation mark. Replacing its three self-check rounds yields the current $22.49 total described above. Kimi and GLM use the user-confirmed API caller ledger: 904 records are bound to 81 retained attempts, while the other 628 records are excluded. Repricing the recorded fields yields $29.853496 and $40.87734396. Kimi includes $0.366596 from the input fields of seven ERROR records. The caller scope replaces prior imputation; absent records and recorded zero-output fields do not receive generated-token estimates. Original native evidence, statuses and prior estimates remain retained. This source-specific confirmation is not an invoice reconciliation or a general missing-log exemption. All plot points have equal size. Solid points mean all 39 initial tasks have normal final submissions. Fewer than 39 is always hollow; forcibly collected content does not count. This marker stays unchanged across cost/time axes and MC/RMC/SMC modes, independently of score or review coverage. Tooltips and accessible labels include the normal-submission count. Cost and time use linear axes starting at zero, so distances reflect actual dollar amounts or minutes. The cost frontier requires verified costs and completed evaluations; the time frontier uses recorded five-task weighted time independently of cost coverage. Raw usage and private task identifiers stay private.

The three subscription self-check rounds add $3.9060102 at the frozen API reference tariff, giving $37.7417155 for the retained39 A1 answers plus3 rounds. The new failed seed is used only as a self-check starting point, not charged as a second main-benchmark A1. Seed plus three rounds cost $9.9117267 in additional study calls; this is reported separately, not treated as subscription invoicing.


## Carbon High · 2026-11-15

采用的39道初答及固定三轮自查按原生首次终态边界留档，42份采用交付的原生用量均已对齐。API参考总额为 **$73.52**，仅含本条件各槽采用尝试的候选原生累计用量；未交卷采用最后有效尝试。普通输入与缓存读取分别计价，思考量已包含在输出中；其他物理重试及安全审核辅助调用另存，不计入该参考总额。该API价格折算不等同于实际订阅账单。见[逐槽公开摘要](../results/v0.6.0/gemini-4-carbon-high/20261115/cost-reference.json)与[模型详情](../site/models/gemini-4-carbon-high/index.html)。

The 2026-11-15 Carbon High selected-attempt API reference is **$73.52**, with complete native usage for all 42 selected deliveries. It counts candidate-native cumulative usage once per selected slot, with cache and thinking counted once. Other physical retries and auxiliary safety calls are retained separately and excluded from this total. The API-price reference is distinct from an actual subscription invoice.
