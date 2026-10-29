# 41题单次双模型比较

本轮运行器是 `scripts/benchmark/` 的薄调度层。题目校验、投影、请求、答卷与标准单题运行记录仍由 `math_gauge.catalog.Suite` 和 `math_gauge.execution.run` 管理。调度层不复制runner，不承担数学评分，不将本轮写成正式人工审定比较。

## 冻结与相同输入

`exercises/catalog.json` 仅供出题者组织四组共41题，不进入候选上下文。运行准备按Suite指纹使用的显式文件集合复制四个只读快照；每份快照重新调用`Suite.load`，指纹必须与源一致。引用、rubric、作者Lean及已有答卷快照均在模型拒读根内。

适配器调用共享的`candidate_message(request)`。无附件保持原题面；有附件只追加中性文件名和完整文件内容。两模型使用完全相同的消息字节。冻结表分别绑定排序JSON请求散列、候选消息散列、原suite指纹、二进制、工具配置及运行器代码。生成和修复题的输出要求来自原题面，不追加证明路线或反馈。

root另写release文件，必须含：

```json
{
  "schema": "math-gauge.comparison-release/v1",
  "released_by": "/root",
  "allow_mathematical_requests": true,
  "freeze_sha256": "运行准备给出的freeze散列",
  "catalog_sha256": "运行准备给出的catalog散列",
  "model_order": ["terra", "gemini"]
}
```

准备、启动队列和每次实际适配器调用分别检查冻结身份。未经root放行不得发送数学题。

## 工具和状态

双方均为纯文本答题，禁用浏览、搜索、文件、命令和协作能力。Codex显式禁用功能并忽略用户配置、规则、记忆和技能发现，使用新SQLite/log目录；HOME与CODEX_HOME不变。AGY采用新gemini/app-data目录，实际应用strict设置，空正文主agent只允许finish。平台内部manage_task单独记录。

复用`scripts/isolated_cli`的准备、身份检查、真实文件打开探测、活PID策略查询与登录链接清理。每题只允许自身工作目录、安装文件及精确认证路径；禁止整个用户数据、其他临时运行和数据卷。非敏感installation_id的精确写回例外沿用已验证启动机制。AGY拒绝全部loopback连接。Terra已获root明确授权，使用核验过的现有系统代理127.0.0.1:7897；macOS策略以`localhost:7897`表达该精确端口，其他loopback端口须继续通过真实拒绝探测。例外、监听程序、系统代理和公开HTTPS连通证据绑定在配置与每题receipt。不要读取、复制、归档或修改原凭据。

AGY全局二进制在首次检查后由外部从1.4.9更新为1.4.10，身份门禁阻止了旧配置发送请求。保留旧记录后，将经核验的1.4.10字节固定复制至任务临时目录，并重做身份、清单与能力对照；禁用自动更新。记录原路径、固定路径和相同散列，不推断外部升级来源。

先做无数学题的型号清单，再用单独新状态做search禁用/启用的非数学正反对照。对照单独计数和保存。不能把全局init.tools注册表当有效权限。客户端初始化声明、实际工具事件和请求的型号/档位分别记录；供应商没有独立回显的后台字段保留null。

## 队列与交付

Terra请求`gpt-6.1-terra/max`，Gemini使用本次实际inventory中Gemini3.8Flash最高可用档。每模型2并发、每题2700秒，完整Terra阶段后才开始Gemini。每题单独标准run、新会话、一次stdin；不自动重试、不替换型号、不依据答案质量选样。不购买额度或使用重置券。

配额、认证、网络、工具条件或其他执行失败停止启动后续题，保留已发生请求及仍在运行的另一题。原事件、stderr、配置、进程检查、答卷、失败和超时必须保留；未开始题不得伪造答卷。`runtime/progress.ndjson`提供机器可读完成事件，含标准run与执行证据路径，可供独立评审逐题开始。

适配器在标准case目录写`execution-assessment.json`，绑定本次run_id、精确model_label、请求、消息、答卷散列，分别记录请求次数、是否具备比较资格、请求与观察到的身份及依据。成功启动不等于数学正确。

Lean生成/修复答卷在输出冻结后由共享`verify_candidate_lean`验收。两模型均无编译反馈，不自动改写候选源码；编译、公理依赖和自然语言/Lean语义覆盖分别记录。代码围栏缺失或编译失败不由运行器补答案。

归档只用明确白名单，排除state、凭据链接和安装副本；原始输出先做凭据模式检查。各题仍human pending，单次结果只能作为本批观察。

## 命令

```sh
python3 -B scripts/benchmark/preflight.py inspect
python3 -B scripts/benchmark/preflight.py inventory
python3 -B scripts/benchmark/preflight.py canary --model terra --mode disabled
python3 -B scripts/benchmark/preflight.py canary --model terra --mode enabled
python3 -B scripts/benchmark/preflight.py canary --model gemini --mode disabled
python3 -B scripts/benchmark/preflight.py canary --model gemini --mode enabled
python3 -B scripts/benchmark/preflight.py complete
python3 -B scripts/benchmark/run_comparison.py prepare --catalog exercises/catalog.json
# shared runner与本运行器审查收口之后，绑定最终代码：
python3 -B scripts/benchmark/run_comparison.py finalize
# 只有root冻结和放行后执行：
python3 -B scripts/benchmark/run_comparison.py run --release /absolute/path/to/root-release.json
```

操作系统策略启动可能需要当前环境的执行权限；不得在权限失败后删除隔离层。失败预检保留原目录，再次预检使用显式新attempt编号。不会覆盖已有正式队列。
