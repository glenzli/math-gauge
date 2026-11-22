# 1.3.0 独立开放研究执行

私有批次计划分别绑定十个配置、既有成绩来源和三轮固定材料。共享执行器按计划顺序逐个配置运行。每个配置启动独立的 Codex app-server stdio 进程，开一个全新的内存线程，同一线程只接收 R1、R2、R3。首轮原题、冻结正文和原图分别作为原生输入项，固定规则作为该线程的开发者指令。后两轮只下发各自原题。候选目录同时保留只读材料和可写 scratch。

每轮采用首个原生 `final_answer`，要求该轮在截止前正常完成。控制器停止可观察的工具子进程，再封存原答及终稿明确交付的本地 Markdown 文件。封印成功后才发放下一轮。缺失、越界或不安全的本地稿件引用保留原话和收集诊断，评审只使用实际交付。非正常终态、型号重路由和无法确认归因的中断保留为未裁定，暂停队列。明确在截止前没有完成的轨迹停止当前配置，并保留实际发出的请求。

## 无模型准备与本机预检

从公库运行。`RESEARCH_RUN_ROOT` 是公私源仓之外尚不存在的实际路径，可用 `/private/tmp` 下的新目录。`RESEARCH_PLAN` 指向私库的冻结批次计划，`RESEARCH_CODEX` 指向实际安装的 CLI 二进制。

```sh
python3 scripts/run_independent_research_batch.py prepare \
  --plan "$RESEARCH_PLAN" --run-root "$RESEARCH_RUN_ROOT"
python3 scripts/run_independent_research_batch.py preflight \
  --run-root "$RESEARCH_RUN_ROOT" --binary "$RESEARCH_CODEX"
python3 -m unittest discover -s tests -p 'test_independent_research_execution.py'
```

macOS 必须能运行真实 Seatbelt 进程。预检只用合成材料，检查文件实际打开、存活父进程策略、原生 `command/exec` 工具进程的独立文件与网络边界、原生模型目录和空线程配置。模型目录可以由 CLI 的内置库存提供。目录匹配和空线程配置均不确认模型服务准入、后端 SKU 或实际推理强度。目录远端刷新失败作为独立运行证据保留。

父进程沿用本机安装和认证，外层文件策略拒读用户资料、其他运行和源仓。用户的 `config.toml`、可选 `environments.toml`、个人规则目录和全局用户指令由精确路径规则拒读并返回 `ENOENT`，保持系统管理配置路径。实际 CLI 启动要求以读写模式打开已有 `installation_id`。执行器先校验其为已有、有效的 0644 UUID，只允许该文件的必要打开权限，并复核文件散列和模式。父进程认证文件和安装标识都在本地工具的否定探测中。工具清空继承环境中的代理变量、禁用工具网络，并直接探测本机监听连接被内核拒绝。每批使用当前 CLI 与网络条件的实测证据。

如本机启用了支持的回环 HTTPS 代理，预检会核对实际系统配置和监听连接，只为父进程开放该端口。原生工具也必须通过该端口的拒绝连接探测。环境变化后保留原报告，在新目录重新预检。

## 已授权执行与独立核查

`execute` 会发出实际模型请求。它要求计划、题目登记及执行器已按授权提交，并要求显式选择此次成功预检的 SHA-256。准备与预检命令不会发出 `turn/start`。

```sh
python3 scripts/run_independent_research_batch.py execute \
  --run-root "$RESEARCH_RUN_ROOT" --preflight-sha256 "$RESEARCH_PREFLIGHT_SHA256"
```

每轮控制器和请求等待上限为 2700 秒。2760 秒是进程清理外限，提交截止仍以首个原生终态和 2700 秒取早。供应商内部时限、输出令牌上限及内部物理请求数保持未知。原生转发错误、已观察用量和进程退出分别保留。批次不会自动重试或从一个不确定的中途状态续跑。

`control/dispatch-freeze.json` 记录本次公私 HEAD、预检和 CLI 身份。`control/<model-id>/execution.json` 绑定实际启动、精确请求、原始 app-server 事件、首终态、用量、进程边界和逐轮封印。`control/<model-id>/state/` 是评审读取的原稿与交付附件，`batch-summary.json` 保持原计划顺序。使用 `validate_execution(run_root, execution_ref, plan)` 验证单个已结算配置。`execution_ref` 是指向该配置 manifest 的 run 相对路径、字节数和 SHA-256。合成 fixture 保持独立来源，不能进入采用。整个运行目录只在评审侧使用。
