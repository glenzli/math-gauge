# GCP 同上下文续接运行适配

`scripts/gcp_continuation_gateway.py` 是评测操作侧的可选传输适配器，供原生答题代理通过本机回环接口调用 GCP。它使用已验证的 `google-genai==2.34.0` 与 Vertex `v1beta1` 接口；不执行候选工具、不导入答卷、不作数学判定，也不调整计分。

源码从已经完成实际续接验证的运行实现整理而来。可提交版本将机器路径、项目、现有凭据位置、原生模型及思考级别改为显式参数，去掉临时诊断和模拟答题分支。当前已冻结的测试仍保留其原执行源码，不能追溯记成由此重构版本执行。离线测试覆盖此版本与固定 SDK 的完整续接往返；没有为此次整理增加付费模型调用。

## 运行约定

- 每个进程只服务一个实际物理尝试，证据目录必须是新的私有目录。仅监听 `127.0.0.1`，使用独立的本机凭据文件校验原生代理请求。
- SDK 的 `automaticContinuation` 在同一逻辑生成中沿用原请求及服务端检查点；不新开答题上下文、不插入继续提示、不重新发送题目来冒充原生续接。每次实际 HTTP 请求均保留原始模型上下文、系统指令、工具声明及生成设置；仅增加 SDK 的检查点及冻结的每逻辑生成输出上限。
- 不同 Base64 拼写的 `thoughtSignature` 按解码字节校验，实际请求仍发送原始字符串。SDK 合并工具容器及 protobuf `minLength` 的表示差异经过语义校验后，仍发送原生工具声明。检查点和签名不得作为可公开材料。
- 默认输出上限为每个逻辑生成 262144 token；它不是整题累计 token 上限。每个逻辑生成至多 8 个实际 HTTP 请求。原生时限与外层时限由原采集器独立冻结，回环传输的累计时钟不会因续接或工具返回重置。
- 原生 `finish()` 工具调用之后仍允许其正常最终文本生成。只有原采集器的终结封存标志、真实输出耗尽或传输失败会锁住后续候选生成；不能把 `finish()`、可读错误或传输结束当成正常交卷。
- SDK HTTP 尝试数固定为 1，适配器没有整题重试权。保留实际 HTTP 状态和原类型错误，尤其不能让后续本机 `409` 掩盖上游 `429`。是否冷却、整体重试及消耗几次有效尝试，仍由已冻结规则和明确授权决定。
- 原生工具代理、工具定义、安全审查模型与本地依赖来自原采集器。候选工具的禁止联网和评审材料隔离也由原隔离配置保证；模型服务／认证流量须另行记录。本机接口须对候选工具不可访问。

所有原始请求、SDK 块、HTTP 响应、检查点、时间和错误仅写入私有操作证据目录，不保存认证请求头或令牌值。原请求正文仍包含题目、作答历史、签名与检查点，不能进入公开仓库。只有实际原生最终答卷可作正常交付；隐藏思考、未交付工作区及跨尝试并集不得因此变成答卷。

## 使用

在专用环境安装固定 SDK，先准备原生会话 `input/task.md`、独立本机凭据文件和已有 GCP authorized-user ADC 文件。参数只传文件位置，不把密钥值放进命令行。以下名称是操作者环境变量，需由原采集器填入并冻结：

```sh
python -m pip install google-genai==2.34.0
python scripts/gcp_continuation_gateway.py \
  --out "$OPERATOR_EVIDENCE_DIR" --session "$NATIVE_SESSION_DIR" \
  --key-file "$LOOPBACK_KEY_FILE" --credential-file "$EXISTING_GCP_ADC_FILE" \
  --project "$GCP_PROJECT" --location "$GCP_LOCATION" \
  --candidate-model "$FROZEN_NATIVE_MODEL" --thinking-level "$FROZEN_THINKING_LEVEL" \
  --guard-model "$FROZEN_NATIVE_GUARD_MODEL" --deadline-seconds "$FROZEN_LIMIT_SECONDS"
```

就绪记录给出随机本机端口；原采集器据此配置原生代理的模型接口，并在本次原生尝试结束后关闭这个进程。不要将接口地址或操作目录交给候选工具。多个原生安全审查模型可重复使用 `--guard-model`，其身份必须与冻结的原生运行一致。

固定 SDK 环境中的离线检查：

```sh
python -m unittest discover -s tests -p test_gcp_continuation_gateway.py
```

测试只使用合成请求、假凭据与本地模拟传输；检验真实 SDK 的检查点往返、原文／工具／签名字节、独立逻辑生成预算、`finish()` 后的最终化、累计时限及真实 `429` 的无重试传播。默认无 Google SDK 的项目环境会跳过 SDK 集成部分，保留不依赖 SDK 的传输检查。
