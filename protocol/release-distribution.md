# 下载题包与独立运行

本指南面向外部 harness 操作者。候选模型只读取控制器构造的完整 `messages`、题目允许的附件和本分支历史；下载说明、目录清单、运行配置与调度信息由操作者保管。

发布版本 **v0.1.0** 标记软件与交付物，题集版本 **0.2.0** 标记当前43份公开开发试卷。两者分别记录。题目仍为 draft / human pending；发布、离线测试和文件校验均不构成数学人工批准或模型能力结果。公开参考与 Git 历史仍可用于透明复核，本题集不是未公开保留集。

## 1. 下载、校验、解压

从 [v0.1.0 Release](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0) 下载两个命名资产：

- [math-gauge-tasks-v0.1.0.zip](https://github.com/glenzli/math-gauge/releases/download/v0.1.0/math-gauge-tasks-v0.1.0.zip)
- [SHA256SUMS](https://github.com/glenzli/math-gauge/releases/download/v0.1.0/SHA256SUMS)

在新的下载目录中执行：

```sh
curl -fLO https://github.com/glenzli/math-gauge/releases/download/v0.1.0/math-gauge-tasks-v0.1.0.zip
curl -fLO https://github.com/glenzli/math-gauge/releases/download/v0.1.0/SHA256SUMS
shasum -a 256 -c SHA256SUMS
unzip math-gauge-tasks-v0.1.0.zip
cd math-gauge-tasks-v0.1.0
python3 payload/controller.py check --bundle payload
```

Linux 也可用 `sha256sum -c SHA256SUMS`。校验失败时保留原下载供复核，不使用该文件开始执行。发布页自动附带的 **Source code (zip/tar.gz)** 是完整源码快照，含公开参考答案和评审材料；它不是命名候选 ZIP。外部运行端不需要 clone、安装 Math Gauge、连接 Codex 或获得原仓库。

`payload/` 包含不可变的候选材料、脱敏调度、独立 `controller.py` 与提交合同，不含完整主计划、profile、参考、rubric、预期真假、作者证据或审批记录。题目明确允许的含证明原文和 Lean 审计源码仍完整保留。压缩包根目录的 README 是操作者说明，不能并入候选提示。

## 2. 冻结所选模型与预算

需要 Python 3.10+，控制器只使用标准库。下载的题包不预选模型、不包含凭据，也没有真实运行结果。为一次试验准备 `runtime.json`；结构如下，所有 `REPLACE_` 值和预算必须按实际条件替换：

```json
{
  "model_label": "REPLACE_WITH_REQUESTED_MODEL_AND_SETTINGS",
  "adapter_identity": {"provider": "REPLACE_WITH_BACKEND", "kind": "external-harness"},
  "candidate_parameters": {"model": "REPLACE_WITH_ACTUAL_MODEL"},
  "budget": {"timeout_seconds": 120, "output_tokens": 16000, "max_transport_attempts": 354},
  "retry": {"max_attempts": 2, "wait_seconds": 0, "retryable_exit_codes": [75]},
  "fresh_context": true
}
```

120秒和16000输出 token 只演示字段，不是对整章任务的推荐。发布控制器仅接受 `model_label`、`adapter_identity`、`budget`、`candidate_parameters`、`fresh_context`、可选 `system_prompt` 与 `retry`；不接受临时添加的工具权限字段。预算必填正数 `timeout_seconds`、`output_tokens`，可选累计尝试数、累计用量与逐题参数。具体预算、参数含义、工具边界和用量证据由外部 harness 事前确定并实际实施；控制器构造请求，不替平台执行超时、隔离或费用限制。不得把请求的型号标签当作独立后端认证。runtime 不应保存密钥。

`model_label` 是报告显示标签；`candidate_parameters.model` 是必填的实际请求模型 ID，不能只填标签而遗漏请求字段。二者均不证明后端实际提供了该型号。可在 `budget.case_parameters` 按题号事前覆盖生成参数，例如 `{"MG-C002": {"max_output_tokens": 60000}}`；同题三个独立初答和对应复核轮沿用同一覆盖。未覆盖题目使用全局输出预算，不在看到答案后临时加额。

从原题包创建新的运行目录：

```sh
python3 payload/controller.py freeze --bundle payload \
  --runtime /absolute/path/to/runtime.json --target all --out /absolute/path/to/new-run
python3 /absolute/path/to/new-run/controller.py check --bundle /absolute/path/to/new-run
```

原始 `payload/` 保持不变。新目录保存原样 `dataset/`、根目录 `manifest.json`、`controller.py`、本次 runtime、运行身份、选定范围和提交模板。不同模型、预算或执行条件使用新的运行目录；不要编辑旧运行清单后继续填答卷。默认完整计划为177槽/模型；可以事前选择分项，完整计划与固定分母仍由评审端保留，缺测不重新归一化。

冻结文件的散列只绑定本地材料与配置。运行目录中的日期、UUID、型号和来源声明不证明第三方的实际执行时间、身份或隔离；外部调用仍须保存可核实的原始证据。

## 3. 构造初答与后续请求

先在题包之外创建请求和回收目录。为初答构造完整请求：

```sh
python3 /absolute/path/to/new-run/controller.py request \
  --bundle /absolute/path/to/new-run --slot 'MG-GR002:A1' \
  --out /absolute/path/to/requests/gr002-a1.json
```

将输出的完整 `messages` 和冻结生成参数原样交给平台。题面、指令及白名单附件全文已经组成初始消息；不能只发送 `task.md`，也不能添加来源、分类、评分、预期真假或自定义解题提示。`A1`、`A2`、`A3` 各用全新上下文，不能把同一对话中的三次回答当作三次独立作答。

保存实际 `A1` 原始文本后，建立 `ancestor-answers.json`，键为所需祖先槽位 ID，值为原样响应文本，例如：

```json
{"MG-GR002:A1": "这里须为实际 A1 的完整原始文本"}
```

该示意文本不是可导入答卷。构造中性第一轮：

```sh
python3 /absolute/path/to/new-run/controller.py request \
  --bundle /absolute/path/to/new-run --slot 'MG-GR002:neutral:1' \
  --answers /absolute/path/to/ancestor-answers.json \
  --out /absolute/path/to/requests/gr002-neutral-1.json
```

第二轮只在映射中提供同一 `A1` 和该分支第一轮的原始文本，再请求 `MG-GR002:neutral:2`。`affirm`、`deny` 各从同一锁定 `A1` 独立展开，互不可见。不得加入其他初答、其他分支、数学判定或编译反馈。`KEEP` 继承紧邻父节点的完整主体，`FULL` 重新交付整份答案和所需源码；不使用修改摘要替代完整交付。

当前发布为无候选工具的文本轨道。联网、代码执行、Lean 交互编译或额外 agent 属于另行冻结版本的实验，不能混报。操作者的传输、保存和调度不等于候选获得了解题工具。

## 4. 保存原始提交

用运行目录的模板创建一份新的提交文件：

```sh
python3 /absolute/path/to/new-run/controller.py template \
  --bundle /absolute/path/to/new-run --out /absolute/path/to/results/submission.json
```

模板不是完成结果。按运行清单的冻结顺序填入已执行槽位，每槽保留精确 `projected_request`、全部有序 `attempts`、原始响应和标准错误文件，以及实际可知的用量、时间、状态和后端返回信息。原始文件以相对提交目录的路径、字节数与 SHA-256 引用；响应为空也保存显式空文件。完整字段以模板和 `payload/CONTROLLER.md`（运行目录内为 `dataset/CONTROLLER.md`）为准。

实际外部运行使用 `origin="external"`、`fixture_only=false`，并填写真实 `declared_external_calls`。离线合成、复放与真实外部答卷分别标记，未知信息保持未知。只有无可读答卷的暂时传输失败或超时可以按冻结合同重试；第一份可读答卷立即锁定。拒答、数学错误、格式缺失或已经返回文本的超时不能触发换答。

不删除失败，不补写答卷，不覆盖原始 Lean。未执行与缺失槽位保留缺测，部分返回不会产生完整基准的精确成绩。将整个新运行目录及独立回收目录交给评审端，保持原始下载包以便核验。

## 5. 评审端导入

以下步骤由评审端使用同一共享 runner 执行，外部运行端无需安装。评审端保留与该发布绑定的完整主计划和题集；它们不在候选 ZIP 内。发布者从对应版本源码生成的 evaluator anchor 用于把不可变数据集与本次冻结 runtime 重建为同一评审计划，不能由外部操作者手写评审字段。

若需要恢复该计划，先在题库之外创建空的 `release-evaluator/` 目录，再在 v0.1.0 标签对应的干净源码中取得完整提交 SHA并执行：

```sh
git rev-parse HEAD
python3 scripts/release.py evaluator-plan --out /absolute/path/to/release-evaluator/plan.json \
  --source-commit FULL_SHA_FROM_PREVIOUS_COMMAND
```

`releases/v0.1.0/config.json` 固定评审计划的身份与创建时间；恢复结果绑定同一题集与发布数据集。不能用本次恢复时间伪造原始执行时间，也不能把源码检出目录交给候选进程。

```sh
python3 -m math_gauge benchmark-import --bundle /absolute/path/to/new-run \
  --input /absolute/path/to/results/submission.json \
  --plan /absolute/path/to/release-evaluator/plan.json --out runs/imported-release-run
python3 -m math_gauge benchmark-check --run runs/imported-release-run
python3 -m math_gauge benchmark-review-template --run runs/imported-release-run \
  --out runs/imported-release-review.json
```

完成真实数学审核、适用的候选 Lean 核验和来源审核后，再使用共享 `benchmark-review`、`benchmark-collect` 与 `benchmark-report`。导入不调用模型、不执行提交程序，也不确认外部来源真实。当前外部导入按既有来源合同保留 `external_import`，只可进入明确标注的暂定分析；散列、runtime 声明或审核勾选不能自动取得正式比较资格，`formal_score` 保持相应未核实状态。

未来未公开题集使用同一候选投影、分发、导入、审核和评分实现，单独冻结数据与评审材料。不得在私有题库中复制一套 runner。

[外部交换合同](external-harness.md) · [运行证据标准](execution-evidence.md) · [仓库操作指南](../docs/usage.md)
