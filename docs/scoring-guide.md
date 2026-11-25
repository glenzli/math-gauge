# 规则与评分索引 · 1.3.0

这里说明当前榜单每个条目的含义、分母和详细标准。题目与评分来源分别版本化：已发布的1.0.0基础题包仍是39题，1.2.0增加选定失分题的中性续答，1.3.0加入一道独立开放研究题。旧题、原答、原评和已发布资产不随新版展示改写。当前新增判断为AI审核，人工数学审核仍待完成。

## 题目、交付与权重

基础部分为25道公开题、14道私有题，共35个数学家族；同一整章Lean题再接三轮自查。独立开放研究是一道另行登记的私有任务，在同一研究会话交三稿。因此1.3.0为40个逻辑任务、36个家族、45次固定交付（39＋3＋3）；各模型选中的一次性中性续答另计。三稿不是三道独立初答，变体也不各占一个家族。

| 类别 | 1.3总分权重 | 子类与原比例 | 详细标准 |
|---|---:|---|---|
| 书面证明 | 30 | 书面论证／论证审阅＝25∶10 | [基础评分](../protocol/benchmark-scoring.md) · [论证审阅](../protocol/answer-review-scoring.md) |
| Lean | 30 | 语义审计／初答形式化／对齐自查＝10∶15∶10 | [工程与自查公式](../protocol/benchmark-scoring.md) · [工程交付](harness-guide.md) |
| 辅助研究 | 30 | 背景核查、想法手稿化、命题拓展各10 | [背景核查](../protocol/background-check-scoring.md) · [手稿量规](../protocol/manuscript-completion-policy.json) · [命题拓展](../protocol/theorem-extension-scoring.md) |
| 独立开放研究 | 10 | 同一三稿轨迹的数学品味T、研究能力C，按2∶1汇合 | [完整研究规则](open-research-v130.md) |

相关变体先在家族内合并，再平均固定家族，最后使用子类权重。1.3保留原书面和Lean的子类比例：书面两项分别占150/7与60/7分；Lean三项分别占60/7、90/7与60/7分。页面小数仅供阅读，计算使用原始精度。1.2及之前的来源权重仍为35／35／30。

令W、L、R分别是书面、Lean、辅助研究的类别百分制分数。对每个评分口径m，先计算

$$
Q_m=\frac{2T_m+C_m}{3},\qquad
S_m=\max\{0,\;0.30W_m+0.30L_m+0.30R_m+0.10Q_m\}.
$$

不能把原35分贡献直接当作W，不能将画像再加回S，也不把三稿或T／C重复计权。公式和来源验证由[共享实现](../math_gauge/scoring.py)及独立研究采用组件执行，网页读取其结果。

1.3 的原17配置继续绑定原基底；新增 Carbon medium 单独绑定其真实1.2父数据、三稿和审核，不刷新旧采用散列。显式来源选择及校验见[版本基底说明](edition-baseline-selection.md)。

## 三种分数与严格完成

| 分数 | 计什么 | 不同任务的验收单位 |
|---|---|---|
| MC，Mathematical Capability | 已核实的有效数学成果，包括未完成任务中的独立进展 | 依原任务判准核实正向贡献；错误结论及依赖它的内容无分 |
| RMC，Reliable Mathematical Capability | 有效成果扣除已确认错误所造成的损失 | 保留具体错误根、范围、扣分和旧罚的去重关系 |
| SMC，Strict Mathematical Completion | 经严格验收的交付 | 基础题整题二值；Lean自查整条三轮轨迹；新独立研究采用严格净信用 |

基础题的严格通过要求全部实质目标、必要分支和表示桥成立，没有“达到95分即可通过”的门槛。四道形式化任务审初答工程，不能用后续修复回填；整章92项少一项即初答严格不通过。Lean自查则要求三轮均交付且诊断完整准确、无误报完整或回退，最后92项核实完成，满足整条轨迹才获得该项严格信用。

基础承诺审核将普通错误按5%／10%／20%分级，同根去重后一般封顶20%，手稿类封顶50%；已确认核心错误放行、错误否决或虚假核验使该任务RMC最高为0。诚实未完成不另加错误罚。一个私有手稿家族有单独冻结的可删除附带错误判准，不能推广到其他题。见[承诺扣罚](../protocol/claim-penalties.md)、[MC规范](../protocol/capability-scoring.md)及任务自己的量规。

独立开放研究不套用基础题的整题二值SMC：T的正向预算为价值60、结构与条件20、自审取舍20；C按预设研究范围分五块，每块最多20分，分别审核覆盖和深度。RMC保留原稿中已确认的错误根。SMC将同一份MC信用与已有扣分归属到实际成果，只保留通过严格检查部分的净RMC信用；全部通过时保留实际RMC，不能自动得100。通过4/5项不自动等于80分，已剔除错误不再重复扣罚。未定检查保留固定区间。不同路线及严格负结果可获得信用，不能由评审补写缺失证明。详见[研究能力、价值与严格信用](open-research-v130.md#分数与两层聚合)。

## 各题型检查什么

| 子类 | 核心检查 | 分母及边界 |
|---|---|---|
| 书面论证 | 证明、反例或合法条件化结论；假设、量词、定义域、强度和回到原表示的桥 | 公8＋私4，12家族；逐题判准不同，不能只按证明长度给分 |
| 论证审阅 | 核心判断60、证据及影响30、补充完整性10 | 4个父家族；同父变体先聚合，错误否决正确论证也会失分 |
| Lean语义审计 | 给定文本、声明和证明的语义对应，包括条件、量词、范围及覆盖 | 4题／2家族；编译成功不等于语义对齐，操作者不预修题中错配 |
| 初答形式化 | 原字节编译、公理、真实声明、逐项义务与源码对应 | 8／20／40项先合为CH2家族，再与92项CH3等权；不按义务数量给家族加权 |
| 对齐自查 | 实际修复或保持70、准确诊断30，并处理回退与误报完整 | 固定三轮；RMC逐轮计算后平均，SMC验整段轨迹，不选最好稿、不取并集 |
| 背景核查 | 发现材料中实际错误或缺条件，给出有据修正及后果；正确背景不应误报 | 公2＋私2，4家族；R/3为部分信用，错误背书强制R0，SMC验全部实质要求 |
| 想法手稿化 | 忠实明确对象和结论，闭合证明、依赖与边界，形成可检验手稿 | 公1＋私4，5等权家族；严谨完成定向目标可满分，不额外要求独创理论 |
| 命题拓展 | 原题B与实际研究增量R分别判断；更强结论、弱条件、统一结构或严格障碍 | 公2＋私4，6等权家族；RMC=(R−D)/3，D(B0/B1/B2)=2/1/0；MC=R/3；SMC要求B2/R3 |
| 独立开放研究 | R1、R2的主线与成果，以及R3对实际成果的核查、修正和取舍 | 同一会话三稿；题分T∶C=2∶1，固定10分，不将同一成果重复计数 |

命题拓展中的R1/R2/R3是研究增量档位；独立开放研究中的R1/R2/R3是稿件轮次，两者不是同一个量。背景核查与手稿化也不因模型说出熟悉术语而互换类别。原题、具体判准与成功边界从[公开目录](../cases/README.md)进入；私有逐题标准留在私库。

## 作答、续答与缺证据

每题独立初答可并行；同一C003工程的三轮自查以及独立研究的三稿必须顺序承接。候选仅接收题面、明确提供的材料和自己的允许历史。正式测试均允许本地工具与预置公共依赖，禁止外部检索和工具联网；模型服务、认证连接另记。新书面及中性续答通常2700秒，其他七道Lean任务5400秒，C003每轮10800秒；原生、broker、外层预算与历史实际条件分别冻结。[统一运行指南](harness-guide.md) · [独立研究执行](independent-research-execution.md) · [原生采用](independent-research-native.md) · [外部回交](independent-research-external.md)

采用规则内第一次正常交卷，随后不因数学错误重考。没有正常final时，MC只能审核选定最后有效尝试中截止前已存在且独立核实的原成果；RMC／SMC为0。不能拿更大的未交工作区补正常final，也不能修源码、拼接不同尝试或把隐藏思考拼成答案。新三稿任务的后轮按其实际封卷接续条件执行；失败和阻断分别记录。Carbon medium 此次经用户明确选入首轮实际截止稿，另以[独立来源组件](../protocol/mathematical-taste/v1.3.0/selected-delivery-admission.md)审核三稿；强制收卷本身不判数学零分，原生失败状态和额外时间保留。此选择不追改其他配置或基础题的交卷规则。[提交来源](../protocol/submission-scoring.md) · [重跑](../protocol/nonlogical-retries.md) · [正式记录](../protocol/result-record.md)

中性续答只选非Lean首答中任一未满分的整题，三个模式都按80%首答＋20%一次续答折算，退步也保留。免测题必须首答三项都满；未运行续答不继承原分。该层属于1.2基底，1.3重新投影类别权重。页面保留的“续答增量”是**1.2的35／35／30框架相对1.1的增量**，不是新1.3总分差。续答自身三项满分率以全部入选题为分母，使用未取整的三个分数，失败交付也在分母内；不同模型的失分集合不同，不是同题排名。[完整续答协议](../protocol/neutral-revision.md)

已知0、无正常交付、未运行与缺原始证据分别记录。已确认贡献按完整100分展示；完整总分未知时保留exact=null及上下界，不能将已知部分归一到100。新研究未测也不借用旧手稿或其他模型的表现。交付率只计正常final，数学对错另判；1.3的45次交付率、首答39题的正常交卷数与完整目标达成率是不同指标。

## 数学画像十轴

各轴0–100，不相加为总分，也不按雷达面积排名。1.3使用已采用续答阶段；1.2保留首答／含续答切换，1.1保留原七轴，1.0不增加画像。雷达选模不筛掉表格或逐轴排名中的其他合格模型。覆盖单位随轴单独显示。

| 轴 | 当前含义与来源 | 详细说明 |
|---|---|---|
| 论证能力 | 必需核心、全部分支、推理和表示桥；按原35家族及已采用续答评审 | [原画像](../protocol/mathematical-profile.md) · [续答画像](mathematical-profile-revision.md) |
| 问题忠实度 | 保留实际对象、条件、量词、范围和目标，换表示需有已交付桥梁 | [原画像标准](../protocol/mathematical-profile.md) |
| 数学审辨力 | 80%基底审辨＋20%新题品味RMC | [1.3画像公式](open-research-v130.md#独立能力轴) |
| 数学深度 | 28个给定问题家族，按机制、桥接、条件与统一结构独立评0–4档；固定机会权重合计69 | [两轴分工、档位与权重](../protocol/profile-structure.md) |
| 成果闭合度 | 已成立成果的证明、依赖、范围和表示桥是否闭合；保留基底评审 | [续答画像](mathematical-profile-revision.md) |
| 严格完成度 | 直接读取当前1.3正式总榜SMC，不再次80／20折算 | [当前画像公式](open-research-v130.md#独立能力轴) |
| 开放研究能力 | 五道手稿与一次独立研究共6个机会，分别验收目标、机制、范围与成果闭合；机会因子1／2／1／2／2／3 | [两轴分工、档位与权重](../protocol/profile-structure.md) |
| 形式化能力 | 原Lean整体SMC的35分映射到100：语义审计10、初答工程15、完整三轮自查10 | [完整标准](../protocol/formalization-profile.md)；覆盖3个子类，1.3的30分主榜权重不重配此轴 |
| 数学品味 | 80%新题品味SMC净信用＋20%六个旧命题拓展家族的严格品味评审 | [品味与旧题复核](open-research-v130.md#独立能力轴) |
| 研究主动性 | 27个原题首答机会＋三稿整体1个域外机会，共28个等权0–4档 | [共同机会标准](../protocol/research-initiative.md) · [逐配置汇总](research-initiative.md) |

开放研究能力的必要核心未证、被推翻或范围漂移未桥接时，最高2档；3档只允许无需新机制的明确局部缺口，4档须交付完整可用的所需核心。数学深度另看原题的结构：完整的重要局部机制、桥接与条件可支持3档，主要统一核心成立才能到4档。两轴对实际采用续答按题使用80%首答／20%续答；独立研究只用规定末稿，固定权重不因未知而缩减。[完整量规](../protocol/profile-structure.md)

形式化轴直接采用SMC，不由其他模型的工程、MC或后续修复补满。主动性只记额外且有数学依据的探究，必做证明和例行工具不算；一个完整独立研究单元或严谨障碍即可得4，不要求文献首创。旧E档及原混合保留为来源，不能直接换算新主动性。

## 辅助指标、资源与故障

| 条目 | 分母或比较范围 | 完整文件 |
|---|---|---|
| 内容可靠率 | 规则选定首答中实际数学承诺；不能仅由主分推算 | [两率标准](../protocol/content-rates.md) |
| 完整目标达成率 | 共同、独立可用的完整目标；必须证明、范围和必要桥都成立，辅助步骤不另算成果 | [两率标准](../protocol/content-rates.md) |
| 主动额外成果 | 原五个手稿家族首答中已核实、非必做的独立成果组；同机制合并，不设满分或越多越好 | [额外成果观察](manuscript-observations.md) |
| RG／DG分差 | RG=RMC−MC，DG=SMC−MC；零差不代表能力强 | [分差说明](#分差与排序) |
| 续答自身满分率 | 所有入选续答题；自身未取整MC、RMC、SMC均满才计入分子 | [续答协议](../protocol/neutral-revision.md) |
| 参考费用 | 规则选中的有效首答、自查、续答、研究开销；同次接续分段去重，计分权重不折扣费用 | [计价与估计](cost-reference.md) · [续答资源](neutral-revision.md) |
| 作答耗时 | 当前共同公开非Lean样本的类别加权均值和不加权中位数；整章形式化单列 | [计时标准](answer-timings.md) |
| 成本／耗时—成绩图 | 资源越低、成绩越高越好；完整前沿要求成绩与资源均齐全 | [前沿、点形和来源](cost-reference.md) |
| 尝试与重试 | 物理请求、有效尝试、系统排除分别计；内部API往返不是新的外层任务尝试 | [尝试统计](execution-attempts.md) |
| 历史异常 | 服务端、上下文、原生运行器三类可重叠，总数取并集；不是可直接比较的故障率 | [异常来源与排除](execution-anomalies.md) |

两率和额外成果仍是首答诊断，不能宣称描述了全部续答或三稿研究。前沿的实心点只表示39/39原初答正常交卷，空心表示更少或未知；它不等于45次完整交付或数学满分。已证实测试脚本、环境配置、断电、主动停止和订阅额度耗尽不计为模型异常；模型与原生harness自身问题照原证据保留。异常表星号表示历史运行记录未完全恢复，区别于已退役的“未测完模型”标记。

成本只算规则选择的交卷、强收或截止尝试，已废弃重跑和确认的纯系统失败不混入显示成本；原物理历史仍留存。同一有效机会的前缀和续作计一次完整用量，不重复累计上下文快照，thought若已在output内不再相加。参考API价不是订阅账单；估计标≈、只有可核实小计时保留其下界。日常耗时不包含新独立研究，纵轴成绩仍可为1.3，需同时读轴标签和样本范围。全部精确算术使用共享产物。

## 分差与排序

RG=RMC−MC描述可靠性损失，DG=SMC−MC描述严格完成相对可用成果的落差；两者是诊断量，不是新benchmark。主榜仍看所选的SMC／RMC／MC，分差小不表示原能力高。分差榜按所选差值离0的距离排序，保留原符号；其选择不改变总榜或分类的排序。

总榜和各分类可独立选择排序口径。先比较所选分数，再按SMC、RMC、MC的顺序比较其余两项；三分均结算且在公布精度相同的配置共享竞赛名次。未知排在已知值之后，已知0不当作空白。并列或非名次列表按厂商、系列、型号与已知effort归组；测试日期保留为来源信息。URL分别保存这些选择。[版本和界面规则](edition-views.md)

## English

Edition1.3.0 retains the sealed39 source tasks and their35 mathematical families, the three prescribed Lean self-checks and adopted neutral revisions. It adds one private, three-manuscript independent-research task:40 logical tasks,36 families and45 fixed deliveries. Model-specific neutral revisions are additional. The1.0.0 released distribution and original answers/reviews remain unchanged.

For each score mode, written proof, Lean and supporting research contribute30 points each; independent research contributes10. Let W, L and R be the original category percentages, not their old35/35/30 contribution points. The new task is Q=(2T+C)/3 and the overall score is max(0,0.30W+0.30L+0.30R+0.10Q). Family/variant relationships and original within-category ratios stay fixed. Profile axes do not add a second score contribution.

MC credits independently verified valid mathematics; RMC accounts for supported error roots. Source-task SMC is whole-task acceptance, with the entire three-round Lean self-check judged as one trajectory. The new research task instead uses strict net credit: T has a60/20/20 positive-credit budget and C five20-point direction budgets; original errors are allocated once, and SMC retains only passed checks’ remaining RMC credit. Passing all checks preserves the actual RMC rather than automatically awarding100; passing four of five is not automatically80. Unknown evidence retains fixed bounds.

Written arguments assess the complete requested claim and representation bridges. Argument review uses core judgment60, evidence/impact30 and supplementary completeness10. Semantic audit checks actual meaning; compilation alone is insufficient. Initial engineering groups the8/20/40 variants into one family and the92-obligation task into another; later repairs never backfill the first delivery. Self-check RMC scores real repair/maintenance70 and accurate diagnosis30 over the fixed three rounds; Strict requires every delivery and diagnosis, no false completion/regression and a verified complete final project. Background checks require supported correction without misrejecting a correct premise. Manuscripts must faithfully close the requested definitions, proofs and boundaries. Theorem extension keeps baseline B separate from research grade R: RMC=(R−D)/3 with D=2/1/0 for B0/B1/B2, MC=R/3 and Strict=B2/R3. The extension grades R1–R3 are distinct from manuscript-round names.

Use the first rule-eligible normal final. A wrong normal answer is not retryable. Without a normal final, only independently verified original cutoff work in the selected effective attempt can earn MC; RMC and SMC are zero. No hidden-thought reconstruction, source repair or cross-attempt union is allowed. Independent first answers may run in parallel; each Lean/research trajectory is sequential in its own context. Local tools/preinstalled public dependencies are allowed; external retrieval and tool networking are not. Native, broker and outer budgets retain their actual source identities. See the linked execution, submission and retry contracts.

Selected non-Lean loss tasks use80% original and20% one neutral revision in every mode, including regressions. All-three-full originals are exempt. Continuation deltas retained on1.3 pages are gains in the1.2 baseline35/35/30 frame, not automatically1.3 overall-score gains. A continuation’s full-score rate uses all selected tasks, including failed deliveries, and requires all three own unrounded scores to be full. Different loss sets are not matched-task rankings. Known zero, failed delivery, unrun and missing-source uncertainty remain distinct; measured coverage is never scaled up to100.

The ten-axis profile uses the adopted-revision stage in1.3. Reasoning, fidelity and closure retain their source-bound family judgments. Discernment blends80% baseline with20% new T_RMC; depth and open-research capability blend their respective baseline with C_RMC. Strict completion copies official1.3 SMC directly. Formalization maps the original full Lean SMC35-point group to100, preserving audits10, initial engineering15 and the complete self-check trajectory10. Taste blends80% new T_SMC with20% strict taste reviews over six legacy extension families. Initiative independently averages28 equal0–4 opportunities:27 original A1 development tasks and one extra-scope opportunity across the research trajectory. Required work/routine tools do not count; one rigorous, independently useful result or obstruction may earn4. Old E labels are not converted into the new initiative grade. Coverage units differ by axis; axes and radar area are not an overall rank.

Content reliability, complete-goal attainment and manuscript-surplus observations remain first-answer diagnostics. Normal delivery rate is distinct from mathematical completion. Cost counts selected effective work, including continuations/research in full, with same-attempt segments and usage snapshots deduplicated. Abandoned/system-only retries and evaluator work stay separate. Estimates are marked≈; API-equivalent cost is not a subscription bill. Timing uses common public non-Lean tasks, with whole-chapter formalization separate; new research is excluded from that daily timing axis. Solid Pareto points mean39/39 normal A1 finals, independent of mathematics or45-delivery coverage. Historical anomaly totals are unions of overlapping service/context/native-harness events and exclude evidenced tester/environment/quota causes; an incomplete-record star does not mean an unfinished-model filter.

Detailed component documents and source-backed score outputs linked above define each item. Private task inventory, original manuscripts, exact review reasons and operational evidence stay private. Source-contract checks, Lean compilation, AI mathematical review, human approval and verified model identity are separate findings; current new AI judgments retain human-review-pending status.
