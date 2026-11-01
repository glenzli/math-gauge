# Math Gauge v0.1.0 候选题包

本包可在任意外部平台独立使用。需要 Python 3.10+；不需要 clone 原仓库、安装 Math Gauge、安装第三方 Python 包或使用 Codex。控制器负责检查文件、冻结配置和构造精确请求，不调用模型。模型接入、上下文隔离及原始证据保存由你的 harness 完成。

发布版本为 **v0.1.0**，题集版本为 **0.2.0**。本次含43份公开开发试卷及177槽的完整计划；题目仍为 draft / human pending，没有候选模型结果。公开参考答案和 Git 历史仍供透明复核，独立题包不使这些题成为未公开保留集。

本 README、`payload/CONTROLLER.md`、清单、调度和运行配置均供操作者使用。候选模型只接收 `request` 构造出的完整 `messages` 与该题允许的附件，不能读取整个题包、其他题、控制说明、参考、评审材料或其他独立运行。

## 1. 校验下载与材料

从正式 [v0.1.0 Release](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0) 下载命名资产 `math-gauge-tasks-v0.1.0.zip` 和 `SHA256SUMS`，在解压前核对：

```sh
shasum -a 256 -c SHA256SUMS
unzip math-gauge-tasks-v0.1.0.zip
cd math-gauge-tasks-v0.1.0
python3 payload/controller.py check --bundle payload
```

Linux 也可用 `sha256sum -c SHA256SUMS`。GitHub 自动生成的 **Source code** 压缩包是完整源码，含公开参考和评审材料，不是候选题包。题目明确允许的含证明原文和 Lean 审计源码已作为候选附件保留。

`payload/` 是没有预选模型或预算的不可变数据集。校验通过绑定材料身份，不认证后端、隔离或人工审核。

## 2. 为所选模型创建新的运行目录

在题包外创建 `runtime.json`，用实际模型与预算替换示例：

```json
{
  "model_label": "REPLACE_WITH_REQUESTED_MODEL_AND_SETTINGS",
  "adapter_identity": {"provider": "REPLACE_WITH_BACKEND", "kind": "external-harness"},
  "candidate_parameters": {"model": "REPLACE_WITH_ACTUAL_MODEL_ID"},
  "budget": {"timeout_seconds": 120, "output_tokens": 16000, "max_transport_attempts": 354},
  "retry": {"max_attempts": 2, "wait_seconds": 0, "retryable_exit_codes": [75]},
  "fresh_context": true
}
```

预算值只演示字段，不是对完整章节的推荐。`model_label` 是显示标签，`candidate_parameters.model` 是必填的请求模型 ID；两者都不认证实际后端。`candidate_parameters` 可加入该后端实际支持的推理等参数，须在运行前冻结。可在 `budget.case_parameters` 按题号事前覆盖生成参数，例如 `{"MG-C002": {"max_output_tokens": 60000}}`；同题独立初答及复核轮使用同一覆盖。不要在 runtime、提交或证据中保存密钥。

```sh
python3 payload/controller.py freeze --bundle payload \
  --runtime /absolute/path/to/runtime.json --target all --out /absolute/path/to/new-run
python3 /absolute/path/to/new-run/controller.py check --bundle /absolute/path/to/new-run
```

输出必须是新目录。原始 `payload/` 保持不变；运行目录包含原样 `dataset/`、本次 runtime、运行身份和提交模板。换模型、预算或条件时重新从原数据集冻结另一个新目录。`--target` 默认 `all`，可重复选择事先确定的分项；缺测仍使用完整计划的固定分母。

这一步不会试调模型。控制器构造请求，不替平台执行费用、超时、文件或网络隔离。冻结散列、UUID和本地日期不证明第三方实际调用的身份、时间或独立性。

## 3. 构造初答与自查请求

在题包和运行目录外准备新的请求、回收目录，再构造初答：

```sh
python3 /absolute/path/to/new-run/controller.py request \
  --bundle /absolute/path/to/new-run --slot 'MG-GR002:A1' \
  --out /absolute/path/to/requests/gr002-a1.json
```

请求中的 `messages` 已含完整题面和附件全文。外部平台只接收这些消息与冻结 `parameters`；不补入目录、来源、分类、评分、预期真假、审核或自定义解题提示。每题 `A1`、`A2`、`A3` 使用三个全新独立上下文，保留第一份可读原始答卷。

自查需要题包指定的祖先原始文本。第一轮的 `ancestor-answers.json` 只含实际 A1：

```json
{"MG-GR002:A1": "实际 A1 的完整原始文本"}
```

```sh
python3 /absolute/path/to/new-run/controller.py request \
  --bundle /absolute/path/to/new-run --slot 'MG-GR002:neutral:1' \
  --answers /absolute/path/to/ancestor-answers.json \
  --out /absolute/path/to/requests/gr002-neutral-1.json
```

第二轮映射精确包含该 `A1` 和 `MG-GR002:neutral:1` 的原始文本，再请求 `MG-GR002:neutral:2`。保留所有空白、换行、KEEP/FULL模式行和源码块，不把合成后的完整答案替代原始历史。支持与怀疑分支各从同一锁定 A1 独立展开，不能混入另一个分支、其他初答、正确性或编译反馈。

`KEEP` 维持紧邻父节点的整份答卷，`FULL` 重新交付覆盖全题的答案和所需源码；保持请求内的固定交付格式。操作者说明见 `payload/CONTROLLER.md`，在运行目录内为 `dataset/CONTROLLER.md`。本版候选工具为空；联网、代码执行、Lean 交互工具或额外 agent 的实验需另行冻结和报告。

## 4. 保存全部尝试并返回原始提交

生成已绑定本次数据集、运行与runtime的模板：

```sh
python3 /absolute/path/to/new-run/controller.py template \
  --bundle /absolute/path/to/new-run --out /absolute/path/to/results/submission.json
```

模板默认是零调用 fixture。实际运行应改为 `origin="external"`、`fixture_only=false` 和真实 `declared_external_calls`，保持模板中的绑定散列。按冻结顺序列出已执行的槽位，每项保存精确 `projected_request` 和有序 `attempts`。每次尝试包含状态、原始响应与标准错误的相对文件路径/字节数/SHA-256、请求散列及实际可知的用量；完整字段与散列算法见 `payload/CONTROLLER.md`（运行目录内为 `dataset/CONTROLLER.md`）。

原始响应为空时也保存空文件。不改写答卷、不修 Lean、不删失败、不用导入时间替代生成时间。仅在没有可读答卷的暂时传输失败或超时后，按冻结合同重试；拒答、数学错误和交付缺失不能换答。未执行槽位保留缺测，不能把部分答卷均分称为全基准成绩。

返回完整新运行目录、`submission.json` 及其引用的全部原始文件；评审端使用同一共享runner核验、导入和审核，不需要你取得完整主计划或答案。导入不会自动确认后端来源、数学正确、人审或正式比较资格。当前外部导入保持 `external_import`，用于明确标注的暂定分析。

完整[下载与回收协议](https://github.com/glenzli/math-gauge/blob/v0.1.0/protocol/release-distribution.md)由操作者按需阅读，不作为候选提示。
