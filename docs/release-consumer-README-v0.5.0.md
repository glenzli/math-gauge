# Benchmark 0.5.0 · 本地预览

本指南为尚未发布的本地预览，不表示已有正式下载资产。含30份完整任务，完整计划54份记录。需要 Python 3.10+；无需安装第三方包。`tools/benchmark.py` 只负责检查、准备、构造请求、记录与打包，不调用模型。模型可来自任何平台，但 harness 必须实际支持所选模型、参数及隔离条件。

待审答卷属于审阅任务的题目材料，随该题完整消息和附件提供；审阅参考答案、判准与既有成绩不在包内。

只有本 README 是操作说明。`README.md`、`manifest.json`、`tools/` 和运行配置只给 controller；solver 仅接收 `request` 生成的完整 `messages`、冻结参数及允许的本分支工具反馈。不要把整个题包目录或控制说明交给 solver。

## 给 controller 的启动文本

替换占位内容后，可复制给独立 controller；这段文本不发给 solver。

```text
你只负责调度和留证，不解题或评卷。
题包：<绝对路径>；新输出目录：<题包外的绝对路径>
候选平台/模型：<实际provider、模型ID和设置>
runtime：<配置绝对路径>；target：<事前选定的目标>
按本README检查、prepare，再按selected_slot_ids串行request、调用、record、pack。
你已读过控制说明，不能自己作solver，也不能用继承本聊天的fork作solver。
每个A1/A2采用全新上下文和独立工作区，不带全局记忆、项目规则、
其他题/答卷、控制信息或评审反馈。复核仅重放工具生成的本分支完整历史。
落实候选文件、工具和网络隔离；候选禁止外部检索，控制器的平台传输另计。
保存全部真实请求、完整响应/事件、原始答卷、工具日志、失败和已知用量。
第一份可读答卷立即锁定，不按答案质量重抽；只按冻结规则重试。
不能可靠派发指定模型或落实隔离时，停于prepared/missing，记录限制，不伪造结果。
结束时交回answers.zip及完成/缺测/失败说明。
```

新聊天或禁止指令本身不证明隔离。harness 必须限制候选可读文件和实际工具，禁用会注入候选的旧会话、用户记忆、项目规则、检索和插件。没有等价能力时停止相应执行，不静默换模型或放宽条件。

## 1. 检查并冻结运行

以下命令在解压目录执行。所有输出使用新路径，不覆盖旧记录。如取得 `SHA256SUMS`，先在 ZIP 目录执行 `shasum -a 256 -c SHA256SUMS`。

```sh
python3 tools/benchmark.py check
```

在包旁创建 `../runtime.json`，替换为实际选择；数字仅演示格式，不是推荐预算。

```json
{
  "model_label": "实际模型与设置",
  "adapter_identity": {"provider": "实际平台", "kind": "external-harness"},
  "candidate_parameters": {"model": "实际模型ID"},
  "budget": {"timeout_seconds": 120, "output_tokens": 16000},
  "fresh_context": true
}
```

上述字段除 `budget.output_tokens` 外必填。仅当传输不支持输出上限时可省略该字段；在 `adapter_identity` 记录使用平台默认输出策略、实际限制未知。不能发送会被平台忽略的上限或声称其已生效。

生成参数只接受 `model`、`reasoning_effort`、`temperature`、`top_p`、`seed`、`max_output_tokens`、`max_completion_tokens`。这不是平台支持声明；只填写实际支持的参数。`budget.output_tokens` 投影为请求的 `max_output_tokens`。harness 须事前冻结到平台原生字段的等价映射，同时保留规范请求与实际发送请求；所需设置不能忠实表达时停止。可用 `budget.case_parameters` 按题号事前覆盖参数；可选 `system_prompt` 也须事前冻结，不加入解题提示或控制流程。

默认不给候选工具。如事前选择本地工具、禁止外部搜索条件，在 runtime 增加：

```json
{"execution_track": "benchmark.local-tools-no-search/v1"}
```

该条件只允许 `exec_command`、`write_stdin`、`apply_patch`，或事前记录的等价能力；允许本地文件/API查找与工具反馈，包括本地编译反馈。禁止候选通过任何工具联网或外部检索，依赖须事前准备；controller 发送模型请求所需的服务网络另行限制。权限不增加使用工具或 Lean 的提示、义务或最低用量，按原题要求交付。两种条件分开运行。后续提示只按冻结权限投影末句，不改数学或 KEEP/FULL 要求。

```sh
python3 tools/benchmark.py prepare --runtime ../runtime.json \
  --target all --out ../run-model
```

`all` 为54份计划记录：30份A1，预选六题各一份额外A2，再从各自A1开neutral、affirm、deny三条分支，每条一次后续。可选 `core`（全部A1）、`repeat`（六题A1/A2）、`neutral`、`stance` 或五类 `proofs`、`lean-audit`、`lean-construction`、`chapters`、`answer-review`；可重复传 `--target`，所需父节点自动包含。实际顺序见 `../run-model/manifest.json` 的 `selected_slot_ids`。换模型、预算或条件须另建run。

| 条件 | 工具实际支持的边界 |
| --- | --- |
| 顺序 | 单run串行；前槽尚未记录时拒绝下一槽，没有并行调度模式 |
| 超时/输出上限 | 只冻结配置；harness实际执行并保留终止前全部输出 |
| 重试 | 每槽最多两次；仅无可读正文的暂时失败/超时可重试；harness执行等待及状态映射 |
| 累计次数 | 可选 `budget.max_transport_attempts`，达到后停止新请求 |
| 累计token | 可选 `budget.max_total_tokens`，达到或usage未知后停止；单个在途请求仍可能越限，不是硬费用上限 |

## 2. 发出完整请求，记录每次返回

完整计划的首槽示例：

```sh
mkdir -p ../requests ../raw
python3 tools/benchmark.py request --run ../run-model --responses ../answers-model \
  --slot 'MG-C002:A1' --out ../requests/c002-a1.json
```

把生成的完整 `messages` 和冻结参数忠实传给平台，不只发 `task.md`，不增补建议。工具保留构造请求，harness 另外保存实际传输。将完整原始答卷保存为 `../raw/c002-a1.md` 后记录：

```sh
python3 tools/benchmark.py record --run ../run-model --responses ../answers-model \
  --slot 'MG-C002:A1' --request ../requests/c002-a1.json \
  --response ../raw/c002-a1.md --status ok
```

原字节保留解释、拒答、未完成部分和全部代码块。仅在本题明确要求时，按题面文件名交付完整Lean源码；审阅题只按其题面审阅所给材料。记录前不修复候选原答。可加 `--stderr 文件`、`--usage 文件`、`--metadata 文件`、`--exit-code 数值`。usage只含实际已知的非负数值，累计用量用 `total_tokens`；未知保持未知，不填0。

每次用 metadata JSON 对象保留实际请求、完整平台响应/事件、工具日志、参数映射、启动配置和文件快照绑定，可用无损文本/字节编码。路径与散列不会自动把外部日志装入包，原始文件仍须保存。记录工具不会自动采集这些证据；不要只留最后成功事件，不包含凭据或登录状态。

失败也记录：status为 `ok`、`transient_error`、`timeout`、`permanent_error` 或 `budget_exhausted`。无响应引用空文件，超时已有文本全部保留。有效UTF-8且非全空白就是可读答卷，立即锁定；数学错误、拒答、截断或格式不全不能重抽。仅首份无可读答卷的暂时失败/超时可重试，使用相同请求、模型与预算及新文件名，不覆盖第一次。`retry.max_attempts`只能为2；`wait_seconds`可为0至60秒；`retryable_exit_codes`默认`[75]`。工具不休眠、不终止调用，也不按退出码自动判状态，由harness落实。

按选定顺序重复。A1/A2用独立新上下文和工作区；可共用只读公共依赖，不共享可写缓存、候选文件或shell会话。确实未执行的下一槽可以明确skip；已发生的调用必须先记录，不能用skip隐去：

```sh
python3 tools/benchmark.py skip --run ../run-model --responses ../answers-model \
  --slot 'MG-C003:A1' --reason '实际未执行原因'
```

## 3. 分支历史与交付格式

六题的 `neutral`、`affirm`、`deny` 从同一锁定A1分别展开，每条只有一次后续。工具生成完整文本历史：原题、原始A1及本分支固定提示。各分支用新上下文重放精确消息；不另加摘要、其他A2、其他分支或前次工具日志。缺少可读父答卷则保留blocked，不补造答卷。

例如顺序到达该槽时：

```sh
python3 tools/benchmark.py request --run ../run-model --responses ../answers-model \
  --slot 'MG-GR002:neutral:1' --out ../requests/gr002-neutral-1.json
```

复核首个非空行按提示写 `KEEP` 或 `FULL`。KEEP继承紧邻父节点整份交付并给核查依据；有任何修改则FULL，重新交完整答案和全部要求源码，不能只交修改摘要。仍保存原始响应，不手工合成历史。

本地工具条件下，harness封存A1候选工作文件，从同一快照分别克隆三条一次后续分支；不交叉继承其他分支文件。各分支目录、可写缓存、进程和shell会话隔离，controller日志/配置/凭据不进入候选快照。允许重试从该槽调用前相同快照重开，失败日志及快照仍保留。工具不实现这些文件/进程边界。默认无工具条件不额外传工作文件。

## 4. 打包交回

完成或停止后，N填全部实际平台调用次数，包含失败和重试。仅有真实外部调用时标 `external`：

```sh
python3 tools/benchmark.py pack --run ../run-model --responses ../answers-model \
  --out ../answers.zip --origin external --declared-external-calls N
```

离线测试省略这两个选项，保留默认fixture/0次；复放用 `--origin replay`。交回 `answers.zip`，保留本地原始证据。未执行、失败、阻塞和未知不会自动消失。

检查与接收可核对材料、冻结配置、顺序、文本历史、重试、已记录预算和原始文件；不能认证后台模型、实际时间、全部调用披露或隔离真实性。这些需真实执行与来源证据；请求标签、散列和提示词不能替代。数学审核、Lean原样核验及人工审核分别进行，打包/接收成功不表示通过。
