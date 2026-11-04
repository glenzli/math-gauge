# 外部 harness 交换合同

外部 harness 使用自己的模型接入和隔离环境，与仓库内运行共享同一题目、消息、数学、审核和评分合同。候选可来自任何平台，但执行端必须具备相应的真实模型派发与隔离能力，包内没有平台适配器。当前源码为本地0.6.0草稿 / human pending，尚未发布：默认26份公开相关任务、18个数学家族，另31份reserve须显式选择，全bank保留57条任务。默认含14份书面论证、4份历史Lean语义审计、4份大Lean形式化和4份真实答卷审阅；范围以[suite](../cases/suite.json)和[profile](benchmark-profile.json)为准。公开参考和Git历史保留透明复核；历史中间版本的公开可得状态尚未核实，不称隐藏留出集。

当前本地准备与补考使用[0.6.0指南](../docs/release-consumer-README-v0.6.0.md)和[仓库操作](../docs/usage.md)中的v1目录导出、检查及显式bundle导入，不存在已发布的0.6.0中性ZIP。已发布[v0.4.0](https://github.com/glenzli/math-gauge/releases/tag/v0.4.0)的单README流程仍以[同版本原指南](../docs/release-consumer-README-v0.4.0.md)为准；[v0.3.0指南](../docs/release-consumer-README-v0.3.0.md)、[历史v0.1.0发布](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0)及其[旧操作说明](../docs/release-consumer-README.md)保持各自身份。本页记录实现边界、机械字段与兼容合同，不另设操作者流程。

## 材料与访问者

| 材料 | 内容 | 访问者 |
| --- | --- | --- |
| 候选输入 | 完整题面、可选统一指令、显式白名单附件，以及本轮允许的历史 | 当前作答模型 |
| 控制材料 | 选定槽位及顺序、依赖、固定后续消息、冻结调用条件和原始尝试 | harness操作者 |
| 评审材料 | 完整主计划/profile、参考、rubric、预期真假、选择理由、审批及作者证据 | 评审端 |

候选消息沿用共享 `candidate_message(request)`，题面及附件全文都必须传递；题号、分类、来源和调度元数据不能扩展成提示。清单、README、工具和原始提交只供控制端使用。仅生成白名单目录不等于实际进程隔离；文件、网络、工具与跨题历史仍须按[隔离合同](isolated-cli-runs.md)核实。

controller 可以由另一个 Codex 操作，但不能把已阅读全包、指南或其他题的 controller 上下文直接用于作答，也不能用继承全部聊天的 fork 充当新 solver。候选只接收精确请求、冻结参数和该条件允许的工具反馈；额外项目说明、用户记忆、插件、检索、旧会话及其他运行状态不能注入候选。具体后端是否支持角色、历史、工具白名单及文件隔离，须由执行端实际核实，不能由启动提示承诺。没有可靠的模型派发或隔离能力时，只保留已准备材料、限制及缺测，不换模型代跑或伪造调用。可直接复制的 controller 启动文本集中在包内 README，不另发候选系统提示。

整章题约定的含证明原文、跨章Lean定义，以及故意语义失配的审计源码都是合法输入，不能以隐藏答案为由删除或修复。中性发行格式采用显式 `task-inputs.candidate-projection/v1`，仅改指定Lean附件的namespace/end前缀、义务表schema及署名中的特定非数学文字。0.3.0/0.4.0原指南中的30份Lean附件、2份义务表和2份署名是各自冻结包的历史投影计数，不能沿用为当前数量；当前所选输入、原始或已声明投影字节及数量均从实际导出manifest核对。原数学正文、定义、公理、证明体、任务义务及原LICENSE不变；作者、作品、DOI和CC BY归属保留。原仓库文件不改写，原字节编译证据不自动覆盖新投影字节。作者完成的本题Lean、评审材料以及私有题、答案、判据和逐题结果不进入公开任务包。公开与私有题集复用同一实现，不在私有数据中复制runner。

## 不可变数据与运行

当前0.6.0源码支持 `benchmark-plan`、`benchmark-export`、`benchmark-export-check` 和 `benchmark-import` 的只读准备/核验流程；这些命令不调用候选模型。8份Lean新A1可按initial-acquisition profile选择 `lean-audit` 与 `lean-formalization`；四written面板的外部目录导出使用标准目标 `repeat`、`neutral`、`stance`，预先冻结实际新补GP001/GP002的10槽白名单，其余槽保持未执行。`written-new-panel`是评审侧 `select_slots` 分组，当前外部导出不支持该目标。完整步骤及v1 partial回传见[本地指南](../docs/release-consumer-README-v0.6.0.md)。

以下中性v2数据集条款描述已发布v0.4.0及各自同版本历史包，不表示0.6.0已有相同发行能力。v0.4.0命名ZIP为`benchmark-v0.4.0.zip`，采用单根目录：单个README、`cases/<case-id>/task.md`、约定附件、`tools/benchmark.py`、机器清单和许可；不复制request、candidate-message或第二份控制指南。包内不放仓库URL、源码路径、完整源码身份或项目品牌，保留许可与作品署名。题号和公开数学内容仍可能被溯源，不宣称来源匿名。新发布版本与suite版本一致，schema和工具实现版本仍独立管理；历史v0.1.0保留其原编号约定。具体打包、当前限制和源码身份合同见[任务分发合同](release-distribution.md)。

不可变数据集不选模型和预算。准备命令在新目录复制原样数据，绑定runtime和事前选定目标；候选参数必须含明确请求模型，预算必须包含正的 `timeout_seconds`，`fresh_context`必须为true。`output_tokens` 若提供须为正整数且由实际传输支持并执行；仅在传输不支持输出上限时才可省略，此时表示平台默认策略及未知实际限制，须在 `adapter_identity` 和操作者冻结说明中明确记录。不得发送被忽略的上限字段或声称其已生效。运行清单的 `selected_slot_ids` 是实际执行顺序，`execution` 是允许传递的冻结参数；更换条件必须新建运行。

允许的生成参数仅为 `model`、`reasoning_effort`、`temperature`、`top_p`、`seed`、`max_output_tokens`、`max_completion_tokens`。它们是交换字段白名单，不是对所有 provider 的支持声明；`budget.output_tokens` 被投影为 `max_output_tokens`。外部适配器如需使用平台原生字段，必须在执行前冻结明确的语义映射，保存规范请求与实际发送请求，核实值和预算约束一致；不支持的设置不能静默忽略或通过解题提示代替。工具能力映射同样不能扩大权限。必需条件无法表示或执行时，保留不兼容状态。凭据不进入runtime或交付包。

历史中性紧凑控制器标记 `benchmark.release-controller/v3`，使用 `benchmark.release-dataset/v2`、`benchmark.harness-run/v2` 和 `benchmark.harness-submission/v2`；各类槽数由该版本manifest中的显式slots决定，不把旧30题/54槽配置当作当前默认。0.6.0标准计划为26个A1、4个书面A2及12个书面R1，共42槽；合并3份私有探索后29个A1、21家族、45槽。数据集绑定显式投影后的基础评审计划；运行绑定 `dataset_sha256`、`run_sha256`、`runtime_sha256`。包内provenance只留不透明来源承诺、投影版本和候选路径/散列。包外 `evaluator-plan.json` 保存完整基础计划、原始/投影输入映射、完整源码身份和期望的精确数据集身份，导入先核对此身份，再结合运行runtime重建相同计划；自洽重哈希的陌生题包也须拒绝。执行端无须取得该文件，也无权手写评审字段。

中性工具由同一共享portable实现确定性生成，仅改变协议命名空间和工具自有品牌文字。安装侧需要同一中性校验时，从受信本地源码生成并载入其实现，绝不执行下载或返回ZIP中的helper。评审端从原始suite按已声明投影重建候选请求及消息散列。导入保留实际中性请求、完整messages、原始答卷和返回ZIP；内部共享记录仅将传输schema规范化，尝试另标 `request_normalization` 与 `source_projected_request_sha256`，实际请求仍保留在`external_source`及原始快照。不得把内部规范化副本冒称为平台实际发送内容，不逆写候选答卷的命名空间。

原始记录由 `math_gauge/harness_answers.py` 管理，移位后可运行的标准库工具由 `harness.py` 导出。工具构造精确请求并将该请求文件登记为不可变记录；答卷记录必须引用该请求。它不代发平台请求，登记本身不证明实际送达内容、后端或隔离真实。

## 独立上下文、历史与失败

每个计划内初答使用全新上下文与独立工作区。0.6.0默认26题做A1；仅GR002、GR014、GP001、GP002四份书面题另做A2，其neutral/affirm/deny分支从各自锁定A1独立展开，各一轮，只包含原题、该A1和本分支固定R1消息。8份Lean能力任务、AR和探索只用A1。旧计划的A3/R2按各自原始计划保留与解析，不进入当前标准42/45槽。工具只从已保存的原始父答卷取历史，拒绝其他初答、其他分支和缺少可读祖先的续答；不使用摘要、改写或KEEP合成正文替换原始历史。前次工具日志保留为执行证据，不另行注入后续消息。可逐轮新建solver并重放精确消息；专属会话续用必须证明没有额外历史。不得加入评审者的正确性或编译反馈，独立轮和分支不共享工具状态或文件。

KEEP继承紧邻父节点的完整交付，当前轮说明另审；FULL重新交付全题答案及约定源码，不使用部分修改摘要。runtime省略 `execution_track` 时，默认无候选工具上下文精确保留。中性包显式选择 `benchmark.local-tools-no-search/v1` 时，只开放 `exec_command`、`write_stdin`、`apply_patch`，`tool_network_access=false`、`search_allowed=false`、`local_tool_feedback_allowed=true`，且仍为 `external_correctness_feedback=false`。禁止联网检索/外部搜索及工具联网，允许本地题面和预置公共依赖中的内容/API查找；本地工具输出（含本地编译反馈）可见，评审反馈不可见。该声明不增加使用工具或Lean的提示、义务或最低用量，原题Lean要求不变，题目与各自冻结的历史安排不变；当前0.6.0按四written面板安排标准42/45槽。两种执行条件分别标记，不混合成绩。操作者的传输、保存和调度工具不是候选解题工具；实际工具联网、文件边界和固定依赖另须核实。仓库内和历史包保留原 `math-gauge.*` 轨道标识，不改写既有运行。

本地工具条件须由harness封存A1结束的候选文件快照，并从同一快照为三条分支分别克隆独立工作区；历史双轮R2只继承本分支R1后的快照，当前不安排R2。controller日志、配置及凭据不进入候选快照。每个额外独立初答从各自干净初始状态开始，不能继承A1文件。只读公共依赖可共用，候选可写缓存、持久进程、shell会话和生成文件不可跨独立轮/分支共享。没有可读答卷的允许重试也须保留工具日志及失败快照，重试从该槽位调用前的相同快照开始。包内工具不实现进程/文件快照隔离。默认无工具条件不通过工作文件额外传递历史。

禁止候选外部搜索同时涵盖搜索工具、浏览器、MCP/插件及shell等通路，不能只关闭一种工具。候选本地工具不能联网安装依赖或访问外部服务；controller向候选平台发送请求所需的服务网络另行限制。网络策略和可读文件边界必须按实际进程与工具核实，不能把“工作目录独立”或一条禁止指令当作deny-read/隔离证据。

题面与附件按导出清单声明的原始或版本化候选投影字节绑定。后续固定提示的权限末句由同一个共享函数在运行时投影：默认条件逐字保留；本地工具条件只把“本轮不能调用工具或查询外部资料。”替换成“本轮不得访问网络或进行联网检索。”，保留其余数学、立场和KEEP/FULL字节，不增补使用Lean的建议。数据集和基础计划的 `content_sha256` 始终归属原始提示；实际历史及请求散列归属投影后的文本。中性本地工具上下文冻结 `followup_prompt_projection="benchmark.followup-permission-projection/v1"`，槽记录的 `prompt_sha256` 为实际提示散列，另存 `source_prompt_sha256` 与 `prompt_projection_version`，检查时从原始材料重算两者。未知版本、非预期末句或散列不符均拒绝，不在不可变数据集中覆写内容。

未带上述投影版本的旧八字段本地工具上下文不被隐式升级，应使用对应封存源码和控制器复核。默认四字段无工具上下文保持兼容；新本地工具运行须重新冻结，不能在旧运行中更改请求、收据或提示。

0.6.0是观察后的开发组合。两模型各18个标准新槽由8份Lean新A1及GP001/GP002各完整5槽构成；相容的原written/AR答卷和GR002/GR014五槽包按原生成身份复用，保存每源真实system、参数、工具条件、内外预算和未知项，不能称同步fresh新考。同case条件不得漂移。新8份Lean每轮native、broker和外层墙钟均5400秒；书面后续保留原case预算，不能从旧outer预算推断实际模型时长。MG-C003的92项对齐专项另接正式A1，固定3次中性追问、每轮5400秒，独立归档、不入标准42/45槽或权重，也不替代A1；操作续接不能自动成为正式fresh A1。

所有实际尝试按原顺序保存：完整请求、原始响应、标准错误、实际状态及已知的用量和附属平台记录。usage只含非负数值字段，累计预算使用已知的total_tokens；设置max_total_tokens时，达到阈值或用量未知即停止后续请求，单个在途请求可能超过阈值，不构成硬费用上限。原始平台JSON对象及嵌套字段保存在metadata。字段未知时保持未知，不用请求回显作为后端身份核验，不把导入或保存时间写成生成时间。Lean代码保留在原始答卷，提取源码、真实编译和语义审核分别绑定，导入不修复源码。

平台实际发送请求、完整响应/流事件、候选工具调用与输出、参数映射、进程/权限配置和文件快照绑定均由外部harness采集；`request` / `record` 不会自动抓取这些证据。每槽每次的 `metadata` 对象可保留原始JSON及日志的无损文本或字节编码，日志路径/散列不能代替原文件。归档工具只收已绑定的原始文件，不能向collection目录任意添文件；完整本地原始材料另须保留。认证秘密及登录状态不入包。

仅没有可读答卷的暂时传输失败或超时可在冻结上限内重试；第一份可读答卷立即锁定。“可读”仅指有效UTF-8且非全空白，不等于成功终态或完整交卷。v5只在核实并接纳成功终态后派生后续；尚无成功接纳的原始非ok状态保留raw及status并阻断依赖轮，数学审核为unresolved/no-delivery，不能记数学0。原生终态及具名派生接纳见[终态证据说明](native-terminal-evidence.md)；派生记录不覆盖旧raw/gate，也不自动提升正式资格。数学错误、拒答、交付不全和有可读文本的超时不能换答。每槽最多两次尝试，`retry.max_attempts`只能为2。`wait_seconds`在0至60秒内冻结；`retryable_exit_codes`默认为`[75]`，但包内记录工具不休眠、不终止超时调用，也不自动把外部退出码转换为状态；这些由实际适配器按冻结规则落实并保存证据。

失败不删除，显式skip保留未执行原因；缺少可读且已接纳成功终态父节点的后续槽位保留阻塞。请求必须按选定顺序执行，前槽尚未记录时不发下一槽；当前工具只支持单run串行，不能预取后并行调用或拆分同一run来绕过累计预算。不同模型的独立run可分别隔离运行。超时和输出上限由harness实际执行，累计次数/token规则只约束已披露的尝试；工具不能证明外部未发生其他调用。停在中途也保留所有未执行槽位。

新大Lean运行还须事前冻结[到时封卷规则](deadline-submission.md)：首次终态或截止即停止，首轮与操作续接分开归档和审核；观察后补收工程的诊断不替代标准A1。书面题和审计不新增工程交付义务。

## 单个返回包与统一导入

当前0.6.0的v1 partial回传使用导出的 `submission-template.json`，按[本地指南](../docs/release-consumer-README-v0.6.0.md)以 `benchmark-import --bundle BUNDLE --input SUBMISSION_JSON --plan PLAN --out NEW_RUN` 显式绑定原bundle。以下单返回ZIP约定适用于已有中性v2交换；不能假定v1目录包也含 `tools/benchmark.py` 或使用相同简化入口。

中性v2打包工具从原始记录生成 `answers.zip`，机械字段和散列由实现填写。外部真实调用必须显式声明origin及实际调用总数；默认fixture、真实调用数0，replay保留复放标签。打包不改变原始答卷或补齐缺测。

返回ZIP根目录为：

```text
answers.json                   绑定、文件清单及所有选定槽位状态
run/                           原样冻结运行及不可变数据集
submission/submission.json     绑定该运行的v2提交
submission/<raw-files>         原始响应、错误、用量和附属记录
```

评审入口 `benchmark-import --input answers.zip --plan TRUSTED_PLAN --out NEW_RUN` 统一进行安全读取、材料核验和共享运行导入；无需另传bundle或执行ZIP内程序。归档入口拒绝绝对路径、路径越界、重复/非普通成员及不受清单绑定的内容，按可信本地suite和计划核对数据、runtime、历史、原始字节、父节点、顺序、重试与预算。失败不能留下可被当作完成结果的输出运行。

`harness_import.py`拥有归档读取及共享外部导入；CLI只分派参数。归档内容不能替换可信评审计划或本地runner实现。原始提交和来源标签保存在可复查快照，之后check/review/collect/report继续验证同一绑定。

导入仅证明材料可接入；它不调用模型、不编译Lean、不裁定数学和外部来源。下一步使用共享 `benchmark-review-template`、实际审核、`benchmark-review`、`benchmark-collect` 和 `benchmark-report`。数学/交付审核、候选Lean原样核验、人审和来源核验彼此独立，不能用作者编译或AI审核替代。

通用外部来源保留 `external_import`，不会伪装成runner现场调用或把导入重标为一次真实模型生成。现有[正式运行证据](execution-evidence.md)绑定本地调用及隔离材料；新外部环境须验证对应来源合同，不能仅凭声明、散列、UUID、时间或勾选取得资格。未核实时保留原因及暂定分析标签，`formal_score`保持相应空值。

当前完成分只取A1并先按家族聚合；公开能力权重22.5/22.5/45/10，合并探索后22.5/18/36/13.5/10，综合75/5/10/10，读取冻结profile及[组合政策](composition-policy-v0.6.0.json)。报告继续采用完整固定分母，逐项保留未运行、失败、未决及覆盖，不能把提交子集重新归一化为总体成绩。fixture只描述软件验收，不能报告模型能力。报告同时说明公开开发集身份、模型请求、可核实来源、工具预算、数学和Lean审核、人审及正式资格。

## 历史格式兼容

当前仓库 `benchmark-export` 的v1目录交换和历史发布的v2运行交换继续复用同一导入与审核实现。v1包包含controller、模板及展开后的候选请求，完整计划另存独立evaluator目录；v1提交绑定 `bundle_sha256`、`plan_sha256`、`runtime_sha256`。历史发布v2则将不可变payload和runtime运行分开，绑定数据集/运行/runtime，评审端从原发布配置恢复基础计划。

v1 JSON提交通过 `benchmark-import --bundle BUNDLE --input SUBMISSION_JSON --plan PLAN --out NEW_RUN` 导入；当前0.6.0 partial补考仍使用这一显式绑定接口。已发布中性v2包的单README流程不要求操作者手写散列或祖先答案映射。历史细节见[v0.1.0原指南](../docs/release-consumer-README.md)与[v0.4.0原指南](../docs/release-consumer-README-v0.4.0.md)，当前仓库直接导出见[维护操作](../docs/usage.md)。
