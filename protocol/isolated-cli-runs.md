# 独立 CLI 运行：准备、执行与证据

本流程把一次独立答题的输入、工作状态、工具权限和证据分开核对。模型只收到冻结题面的一个用户消息；不补充条件提醒、参考答案、来源、评分、先前答卷或纠错反馈。这里的独立是可审核的工作材料与工具隔离，客户端仍需登录和模型服务联网；不是离线虚拟机。

`scripts/isolated_cli/prepare.py` 是参数化的准备与本地审计工具，**不会启动答题或提交题面推理请求**。它生成精确输入、候选 argv、macOS 策略、探测清单和记录模板；另有显式调用的 AGY 非推理型号清单预检。新 helper 的测试只验证这些合同；不把测试成功写成某台机器已完成隔离或某个模型已运行。模型运行仍须由操作者按下面的门槛启动并保存原始证据。

## 1. 选定实际 CLI，冻结题面与计划

使用调用者提供的二进制或一个明确的可执行文件名称检查身份。`inspect` 只执行 `--version`、`--help`，以及 Codex 的 `exec --help`，保存 stdout、stderr、argv 和文件散列；AGY 自动更新开关置为禁用。它不会升级工具，也不会检查付费推理。检查失败、二进制变化或缺少其余必需开关时停止。AGY目录覆盖开关即使未列于短帮助，也必须按实际二进制进行非推理预检；帮助遗漏不能证明支持或不支持。不要删掉隔离开关再试。

```sh
python3 scripts/isolated_cli/prepare.py inspect \
  --client agy --binary "$CLI_BINARY" --out "$NEW_INSPECTION_DIR"
# Codex 使用 --client codex，并显式指定准备参加本次运行的真实二进制。
```

身份检查不证明账户可用型号或最高 effort；在正式题面发送前，用该版本支持的非推理型号清单或可审查元数据确认它们并保存原始记录。缺失时记为未核实，不替换型号，不靠改模型完成预检。

复制 [config.example.json](../scripts/isolated_cli/config.example.json) 到题库外，替换全部占位路径。所有路径由调用者提供。`client` 为 `agy` 或 `codex`，`cli_identity` 指向刚保存的 `identity.json`，`run_dir` 必须不存在。准备只读取题面、CLI 二进制和非敏感配置；**不读取凭据内容**。

```sh
python3 scripts/isolated_cli/prepare.py prepare --config "$RUN_CONFIG"
```

配置中的 `deny_read_roots` 应覆盖参考材料所在项目、用户记忆、历史会话、全局规则/技能/插件、旧结果和其他临时运行。审查真实路径与符号链接后的目标，包含它们在其他数据卷或临时根中的副本；不能只列举三个已知答案文件。准备器要求至少有 `reference`、`history`、`prior_run` 三类**实际存在的文件**作为负探测，且都在拒绝范围内。文件不存在不是拒绝访问成功。可增加 memory、global_config、prior_canary 等类别。

`read_exceptions` 只用于启动所需的安装文件和精确登录文件；每项附目的。不要把包含历史的整个用户配置目录列为可读。新运行目录是策略中唯一自动排除的工作区。策略还拒绝向所列数据根写入以及连接 localhost；必要的模型服务网络保留。若代理或客户端因此不能启动，应报告不兼容，不悄悄取消限制。此模板依赖 macOS `sandbox-exec` 与 `libsandbox`；其他平台需另外实现并验证等价边界。

## 2. 新状态、登录与工具能力

`input/` 只有逐字节复制的 `task.md`。运行目录另外有空 `state/`、`work/`、`output/` 和 `runtime/`。只把计划中的 stdin 文件发送给模型，不发送 config、探测路径或运行手册。不要复用旧会话、恢复命令、共享 worker 服务或之前创建的数据区。每次诊断、能力对照和正式运行都用新目录，并在账本中关联。

原有 `HOME` 和 `CODEX_HOME` 值保持不变。不要用替换这些变量的办法假装获得新状态，也不要复制登录文件。Codex 用 `--ignore-user-config --ignore-rules --strict-config --ephemeral`，并显式禁用项目说明、记忆、插件、检索、浏览器、shell、子 agent 等；其 worker 网络设置独立于父客户端连接模型服务。所有覆盖值保存在 `runtime/codex-settings.json`。若当前版本拒绝某个设置，保存失败，停止运行。

AGY 的目录覆盖是 `--gemini_dir <新 state 目录> --app_data_dir antigravity-cli`，后者是相对名称。计划同时显式设置 `--new-project --agent text-only --model ... --effort ... --input-format stream-json --output-format stream-json`。不用旧环境变量替代目录开关。

在第 3 节的真实文件打开探测通过、登录链接就绪后，可以显式运行以下无题面预检。它在同一策略下执行目录覆盖加 `models`，stdin 关闭，记录完整 argv、退出码、stdout/stderr、运行前后新 state 中的文件名，并要求新文件确实位于所选状态目录。它会登录和联网读取型号清单；不会提交题面，也不自动确认请求型号及 effort 已被后端接受。失败只保留证据，不更换目录机制。一次预检只能运行一次；再次预检使用新运行目录。

```sh
python3 scripts/isolated_cli/prepare.py inventory-agy --run-dir "$RUN_DIR"
```

AGY 主 agent 文件放在 `work/.agents/agents/text-only.md`：正文为空，`tools: [finish]`、`mainAgent: true`、`subagent: false`。这是[官方 custom agents 文档](https://antigravity.google/docs/subagents/)所述工作区发现路径与工具白名单机制。`runtime/task-settings.json` 额外提供 strict/deny 防护模板；它**尚未自动激活**。操作者须按实际版本的配置机制应用到新状态或任务设置中，并从初始化元数据核实 strict 生效。不能把这个文件存在当成权限已应用。

strict/read_url设置本身不能证明有效工具权限，`init.tools`全局注册表也不能代替实际权限对照。正式数学运行前，在独立新状态中用同一中性非数学提示做正反能力对照：finish-only 不得完成搜索；仅为对照加入 search_web 后应能完成搜索。对照本身是模型请求，须单独获得运行授权并计数。平台内部 `manage_task` 可能保留，应如实列为内部记账；不能宣称所有工具调用为零。没有可靠的能力证明，就记录局限，不能声称闭卷条件已匹配。

AGY 如确需复用 OAuth，配置 `credential_links`，其 `source` 是调用者给出的现有文件位置，`target` 相对于新 `state/`。helper 只建立符号链接，拒绝覆盖已有文件：

```sh
python3 scripts/isolated_cli/prepare.py link-auth --run-dir "$RUN_DIR"
# 一旦进程退出，包括失败和超时：
python3 scripts/isolated_cli/prepare.py unlink-auth --run-dir "$RUN_DIR"
```

清理只删除指向预期源文件的链接。它不会删除或修改原始登录文件。Codex 保持原登录位置，只在 read_exceptions 中允许具体登录文件；不要对整个 Codex 数据区开读权限。`state/` 永远不进入证据归档。

## 3. 真正执行前，先证明进程访问边界

`runtime/outer.sb` 和计划中的 argv 都是待验证材料。先通过同一策略启动复制到新运行目录的 `runtime/probe.py`；传入 `--manifest "$RUN_DIR/runtime/probes.json" --out "$RUN_DIR/runtime/open-probe.json"`。正探测必须读到题面且散列一致；负探测必须实际打开失败并返回 EPERM/EACCES。ENOENT、其他错误或无策略时可以读到文件，都判失败。

可以从 `runtime/plan.json` 读取参数数组，用 `subprocess.run` 执行以下形状，禁止通过 shell 拼接：

```python
probe_argv = [plan["argv"][0], "-f", str(run_dir / "runtime/outer.sb"),
              python_binary, str(run_dir / "runtime/probe.py"),
              "--manifest", str(run_dir / "runtime/probes.json"),
              "--out", str(run_dir / "runtime/open-probe.json")]
```

`python_binary` 也须是策略允许的实际安装程序。探测失败时保留记录；不按错误信息宽泛放开用户目录。

接下来用计划中的**完整 argv 数组**和 cwd 启动客户端，stdin 保持 PIPE，stdout/stderr 从开始持续写入 `output/events.ndjson`、`output/stderr.txt`。环境从 helper 的 `environment(run_dir)` 构造：只保留列明的必要变量，增加任务专用 TMPDIR 与禁用自动更新开关；不要记录代理或认证变量的值。先不写 stdin。

此时识别真正的父客户端 PID 和实际模型 worker PID/可执行文件。保存父子关系及可执行文件身份，不保存可能带 token 的完整进程参数。确认新启动的服务，而非已有进程或共享会话。对实际 PID 分别运行复制的探测工具：

```sh
python3 "$RUN_DIR/runtime/probe.py" --manifest "$RUN_DIR/runtime/probes.json" \
  --pid "$PARENT_PID" --role parent --out "$RUN_DIR/runtime/parent-pid-check.json"
python3 "$RUN_DIR/runtime/probe.py" --manifest "$RUN_DIR/runtime/probes.json" \
  --pid "$WORKER_PID" --role worker --out "$RUN_DIR/runtime/worker-pid-check.json"
```

这些是对存活 PID 的 macOS 策略查询，与前面的真实文件打开探测互补。每个实际 worker 都要检查，多个 worker 另存编号文件并在执行记录中列全；如 worker 在客户端同一进程内运行，明确记录该结构与同一 PID 的证据。若 worker 只能在提交后出现，发送前必须证明外层策略约束父进程及其继承边界，worker 出现后立即核验并说明核验时间；无法证明时不把运行归入合格隔离比较。现有 helper 不自动识别 worker、不检查进程树、不发送 stdin，因此不会把某个无关探测进程当成实际客户端。

## 4. 单次提交、原始输出与完整账本

启动前在 `runtime/attempt-ledger.json` 增加记录，至少含 `id`、`kind`、`started_utc`、`request_count`、`status`、`reason` 和原始证据路径；kind 区分 inspection、inventory、startup、non_math_canary、math。发送 stdin 的瞬间增加请求数和时间，而非在答案返回后补算。任何失败、超时、诊断、能力对照、零请求启动都保留；没有数学请求的 CLI 版本/帮助检查不算数学样本。

实际 argv 与请求必须同计划逐项核对。复制 execution.template.json 为 execution.json，记录父/worker PID、argv、开始/提交/结束时间、退出码、请求数、所选及可观察到的型号/effort、原始型号与能力证据。缺失的供应商信息用 null 和说明保留，不能拿操作者标签填成后端已证实型号。计划只代表请求的配置。Codex 的 [官方 exec 文档](https://learn.chatgpt.com/docs/developer-commands#codex-exec)说明非交互执行及 JSON 事件；具体隔离开关仍以被测二进制及本次严格启动结果为准。

完成所有发送前门槛后，只进行一次：

```python
proc.stdin.write(Path(plan["stdin_file"]).read_bytes())
proc.stdin.flush()
proc.stdin.close()
```

AGY stdin 是一个 user JSON 事件，message.content 的 UTF-8 字节必须等于 input/task.md；Codex stdin 直接是 task.md 的字节。不发送 JSON 计划、手册、隐含条件提醒或 follow-up。持续保留完整原始事件与 stderr；超时终止整个新进程组，记录提交是否已发生，不复用同一目录重试。

如果在最终答案审阅前观察到不符工具调用，立即记录 `tool_mismatch_decisions`：UTC 时间、触发事件、证据路径、`answer_reviewed_at_decision: false`、`selection_based_on_answer: false`、处理分类和下一步。原数学请求保留为诊断并排除不匹配比较。修复环境后，只有既有授权与预先写下的决定允许时才能用新目录再运行；不能看答案质量决定保留哪次。

AGY 把精确原始 result 事件另存 `output/result-event.json`，`output/response.md` 是其 response 字符串的 UTF-8 字节，不添加换行；Codex 保留 CLI 写出的最终消息文件。工具调用按原始事件审核，不靠 init 注册表或助手自述。保存请求、原始输出、日志、最终答卷及实际型号元数据的散列；评分继续绑定最终答卷散列。

## 5. 审计与交付

```sh
python3 scripts/isolated_cli/prepare.py audit \
  --run-dir "$RUN_DIR" --out "$NEW_AUDIT_FILE"
```

审计检查准备文件和 CLI 是否变化、输入目录是否混入文件、标准 OS 探测记录是否覆盖原清单、凭据链接是否残留，并产生只含明确白名单的相对路径/大小/散列清单。账本允许更新，但保留其准备时散列。缺失 OS 记录报告 incomplete；输入篡改、失败或不匹配记录使本地检查失败。audit **始终不会签发隔离认证**：它不能证明人工提供的 PID 归属、所有尝试均已披露、型号元数据真实性、能力对照有效性或实际只发送一次。操作者须按原始证据补足这些结论，尤其审查编号的多个 worker 记录。

归档必须使用审查后的文件白名单，拒绝符号链接；不递归打包整个运行目录，不包含 state、凭据链接、登录文件或原始配置目录。检查输出日志是否意外含凭据；发现时先隔离原始记录、按明确规则生成可发布副本，不覆盖原证据。最终报告分别说明：准备与本地测试、真实 OS 探测、实际客户端/worker 核验、有效工具能力、模型运行、数学审核、人工审定。只有前一层完成，不得替后续层作结论。

多轮benchmark使用[运行证据接入](execution-evidence.md)把这些原始材料与具体槽位、实际请求、响应和具名来源审核关联。导入器的散列与结构校验仍不替代上述人工归属判断，也不会把单轮输入收据自动变成多轮完整历史的证明；操作者须提供对应调用的实际材料。证据导入、修订和评分命令见[使用指南](../docs/usage.md)。
