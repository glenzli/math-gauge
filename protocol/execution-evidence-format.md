# 运行证据交换格式 · v1

本页供适配器和运行审核者使用，配合[运行证据标准](execution-evidence.md)。原始材料由实际运行环境保存；导入器读取、冻结和核对材料，不启动候选或能力对照。模板中的 `binding` 来自原始run，必须原样保留。模板和本页的字段示例都不是已经完成的观察或审核。

## 文件清单与来源引用

单槽位提交的schema为 `math-gauge.execution-eligibility-submission/v1`，包含 `slot_id`、`binding`、`artifacts`、`observations`、`audit`。`artifacts` 中每项恰有以下五个字段：

```json
{
  "path": "raw/events.ndjson",
  "bytes": 123,
  "sha256": "REPLACE_WITH_ACTUAL_SHA256",
  "kind": "cli-events",
  "origin": "client"
}
```

路径相对于提交JSON的目录，字节数和散列从实际文件计算。这里只示范结构；不能把示例数值用作实际证据。允许的kind为 `provider-request`、`provider-metadata`、`provider-response`、`client-output`、`stderr`、`cli-events`、`invocation`、`context`、`isolation`、`ledger`、`policy`、`tool-control`、`network-probe`。origin为 `provider-return`、`request`、`client`、`os`、`operator`；模型返回信息和响应必须来自provider-return，请求必须来自request。来源声明还需具名审核核实。

观察引用使用 `{ "artifact": "raw/events.ndjson", "line": 1, "pointer": "/metadata/model" }`。pointer遵循JSON Pointer，line是从1开始的NDJSON行号；普通JSON省略line，空pointer引用完整JSON值。省略pointer时引用完整原始字节，不能同时指定line。响应文本可引用JSON字符串，其UTF-8字节必须与原始答卷一致；不补换行或清理文本。

文件名、大小、散列、来源或观察值变化会使旧收据失效。只复制显式清单内的普通文件，不递归导入状态、凭据或配置目录。原始日志如何生成、是否确为服务返回及是否披露完整，仍由运行审核负责。

## 冻结条件与逐尝试观察

计划的 `runtime.execution_requirements` 使用 `math-gauge.execution-requirements/v1`。必须有 `allowed_tools`、`internal_tools`、`denied_categories`、`read_exceptions`、`tool_control_tool`。候选工具列表等于计划的 `context_policy.tools_allowed`，本版为空；内部功能仅支持 `finish`、`manage_task`。禁止类别至少包含reference、history、prior_run、memory、global_config。读取例外由kind（literal或subpath）、绝对path和purpose构成。可选provider及model_aliases/effort_aliases只能事前声明；别名表将请求名称映射到允许观察到的名称列表。

`observations.attempts` 按原记录顺序覆盖每次传输，包括失败重试。每项的number对应原attempt，submission_state为submitted、not-submitted或unknown；模板默认unknown。已提交的尝试要求以下来源引用：

| 字段 | 引用取得的值及约束 |
| --- | --- |
| `request.messages / parameters / request_id` | 实际请求的完整消息、参数和调用身份；消息与冻结投影逐项一致 |
| `backend.provider / model / parameters / request_id` | 实际返回的服务身份、型号、有效参数及同一调用身份；不得用请求回显代替 |
| `backend.reasoning_effort` | 请求中有该字段时必须有实际观察；不从显示标签推断 |
| `response.text / request_id` | 本次原始输出与同一调用身份；精确匹配该attempt响应散列 |
| `stderr / events` | 原始错误输出和非空事件日志字节；与调用记录绑定 |
| `invocation / context / isolation` | 下述结构化观察对象 |

模型参数来自原始projected-request，包括事前逐题覆盖。未请求effort时不自行添加；已请求的输出上限、温度等须有对应有效参数证据。缺项保持未知，不按常见默认值补齐。首份可读答卷即锁定；超时或非零退出并不自动抹去已返回的文字。

可证明尚未提交的本地启动失败使用not-submitted：原attempt没有可读响应且为失败，response.text引用client来源的client-output，stderr/events/invocation仍须与原记录一致。invocation明确request_count为整数0，submitted_at/request_id为null，并给出failure_stage（startup或before-submission）及failure_reason。request/backend各引用及response.request_id为null；context/isolation可为null，不伪造尚未启动的worker或不存在的供应商回执。实际发出了请求但其服务状态未知时保留unknown，不能冒充未提交；最终锁定的可读答卷仍需完整submitted证据。

## 调用与上下文对象

submitted的invocation包含下列字段；not-submitted使用前节规定的零请求分支，不填造会话或提交时间：

- `argv`：冻结的完整适配器参数数组；`request_id`：与request/backend/response一致。
- `request_sha256`：原记录的projected_request_sha256；`response_sha256`、`stderr_sha256`：该attempt原散列；`events_sha256`：原事件日志字节散列。
- `request_count`：已提交为整数1，已证明未提交为整数0；`transport_status`、`exit_code`：与原attempt完全一致；`timeout_seconds`：冻结超时值。
- `started_at / submitted_at / finished_at`：带时区的时间，顺序正确且在runner记录的attempt区间内；`deadline_at`等于started_at加冻结超时。
- `parent_pid`：实际父进程；`session_mode`为stateful或stateless。前者有实际session_id；后者为null，并以完整显式消息、无隐藏会话为审核前提。

context包含与invocation相同的session_mode/session_id，以及 `supplied_messages_complete=true`、`hidden_session=false`、`fresh=true`、`resumed_from=null`。`history_sha256`和messages匹配原记录；ancestors等于模板binding.ancestors；excluded_context明确为 `['prior_answers', 'peer_branches', 'review_material', 'memory']`。这些声明都要指向实际记录，并接受来源完整性审核。

不同原始生成及重试不得复用会话、工作状态或请求身份。跨分片汇总也核验这一点；同一原始生成作为依赖被多次引用可以去重。

## 隔离对象

isolation按以下字段保存观察；实际角色、PID和路径需要审核者核实归属，不能用无关探测进程替代候选进程。

| 字段 | 内容与约束 |
| --- | --- |
| `policy / policy_sha256` | 实际策略的原字节引用和散列 |
| `evaluator_root / deny_roots / read_exceptions` | 原运行绝对路径、覆盖受保护材料的拒绝根及冻结的精确例外 |
| `probe_manifest` | positive绝对路径、实际适配器stdin字节sha256、negative清单。负探测含category/path/exists_before_run；本次冻结reference和rubric还须逐一提供精确路径与sha256_before_run |
| `open_probe` | [探测工具](../scripts/isolated_cli/probe.py)实际打开报告；正探测有observed_sha256，负探测确为EPERM/EACCES。文件不存在不合格 |
| `processes / pid_checks` | 实际parent及全部worker的role/pid/ppid/executable_sha256/started_at，以及每个角色/PID的存活权限报告；检查在进程生命周期内，parent在提交前核验 |
| `policy_inheritance` | parent_pid、worker_pids及verified_at，提交前确认继承边界；同一进程承载worker时显式in_process_worker=true |
| `fresh_state` | 绝对path、created_at、initial_entries为空、resumed_from为null；状态在启动前创建 |
| `tools` | 下述有效权限、事件与正反能力对照 |
| `network_probes` | network-probe来源引用列表，覆盖parent的localhost及每个worker的internet边界 |

正探测输入是runner实际发送的JSON字节，按其 `json.dumps(request, ensure_ascii=False)` 序列化规则保存；不能以只含task.md的单轮收据替代多轮完整消息。

tools中的effective_allowed/internal与冻结列表一致。calls是实际调用记录；registry和call_records必须引用本次同一个events原文件，后者的值与calls一致。registry每项为 `{name, classification, permission}`，classification为candidate/internal，permission为allowed/denied；不得把搜索工具重命名为内部功能来通过检查。

controls.denied/enabled引用两次能力对照原记录，各含相同prompt_sha256和tool、不同request_id、effective_tools、result、finished_at。禁用侧结果denied，启用侧succeeded；启用侧只多出预先声明的对照工具，均在数学请求提交前结束。真实能力对照属于单独计数、需要授权的模型请求；导入器不会代为运行。

network-probe对象含kind（live-pid-network-query或actual-connect）、role、pid、utc、target（localhost/internet）、实际address/port和denied结果。时间属于对应进程生命周期；策略查询提供正整数result_code，实际连接提供EPERM/EACCES的errno。仅有“禁网”配置或一个denied标签不足以通过。

## 账本与具名审核

observations.ledger引用包含origin_run_id、attempts、origin_manifest、peer_provenance和other_activity的原账本。attempts逐项记录全部本槽位传输的evidence_id、number、request_sha256、response_sha256、stderr_sha256、status和request_count，后者按submission_state为1、0或未知的null。origin_manifest引用原运行run.json，首次导入时须与实际原记录一致；peer_provenance以evidence_id、slot_id、slot_record_sha256、transport_attempts覆盖该记录已知的其他生成，不能漏掉已知失败或重复尝试。复用后的保留材料独立验证这些原身份。

other_activity保留相关检查、启动、对照和数学请求的id、kind、请求计数与sources引用；软件不能证明未披露的外部运行不存在。来源审核仍须判断全部尝试是否披露。

audit包含reviewer、reviewer_kind、reviewed_at、decision和checks。decision为accept/reject/unresolved。每项check包含decision（verified/rejected/unresolved）、rationale及sources引用。必须逐项审核：external_authenticity、provider_metadata_origin、process_attribution、attempt_completeness、no_answer_selection、context_completeness、tool_control_validity、read_exception_review。

通过的来源审核须为human、有实际身份与时间，并有每项相关来源依据。例如后端来源审核引用metadata/response，进程归属引用isolation/invocation，工具能力引用tool-control/events/isolation，读取例外引用policy/isolation。无关文件引用不能代替这些材料。该标签是具名审定记录，不是程序自动认证审核者身份。尚未核实的项目保留unresolved；发现不符时记reject/rejected，不为让导入通过而改写原始材料。导入、修订、历史读取与汇总命令见[使用指南](../docs/usage.md)。

明确的具名reject修订可以归档实际型号、工具等不符合要求的原始观察，并保存 `observation_errors` 诊断，撤销先前资格。文件字节、路径、来源引用、原始绑定和尝试清单仍须有效；reject不能掩盖材料篡改或错误引用。先前收据保留在历史快照中。
